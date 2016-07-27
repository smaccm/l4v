(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "Retyping Objects"

theory ArchRetype_H
imports
  ArchRetypeDecls_H
  ArchVSpaceDecls_H
  Hardware_H
  VCPU_H
  "../KI_Decls_H"
begin
context Arch begin global_naming ARM_HYP_H

defs deriveCap_def:
"deriveCap x0 x1\<equiv> (let c = x1 in
  if isPageTableCap c \<and> capPTMappedAddress c \<noteq> None
  then   returnOk c
  else if isPageTableCap c \<and> capPTMappedAddress c = None
  then   throw IllegalOperation
  else if isPageDirectoryCap c \<and> capPDMappedASID c \<noteq> None
  then   returnOk c
  else if isPageDirectoryCap c \<and> capPDMappedASID c = None
  then   throw IllegalOperation
  else if isPageCap c
  then   returnOk $ c \<lparr> capVPMappedAddress := Nothing \<rparr>
  else if isASIDControlCap c
  then   returnOk c
  else if isASIDPoolCap c
  then   returnOk c
  else if isVCPUCap c
  then   returnOk c
  else undefined
  )"

defs updateCapData_def:
"updateCapData arg1 arg2 cap \<equiv> ArchObjectCap cap"

defs maskCapRights_def:
"maskCapRights r x1\<equiv> (let c = x1 in
  if isPageCap c
  then   ArchObjectCap $ c \<lparr>
    capVPRights := maskVMRights (capVPRights c) r \<rparr>
  else   ArchObjectCap c
  )"

defs finaliseCap_def:
"finaliseCap x0 x1\<equiv> (let (cap, bl) = (x0, x1) in
  if isASIDPoolCap cap \<and> bl
  then let b = capASIDBase cap; ptr = capASIDPool cap
  in   (do
    deleteASIDPool b ptr;
    return NullCap
  od)
  else if isPageDirectoryCap cap \<and> bl \<and> capPDMappedASID cap \<noteq> None
  then let a = the (capPDMappedASID cap); ptr = capPDBasePtr cap
  in   (do
    deleteASID a ptr;
    return NullCap
  od)
  else if isPageTableCap cap \<and> bl \<and> capPTMappedAddress cap \<noteq> None
  then let (a, v) = the (capPTMappedAddress cap); ptr = capPTBasePtr cap
  in   (do
    unmapPageTable a v ptr;
    return NullCap
  od)
  else if isPageCap cap \<and> capVPMappedAddress cap \<noteq> None
  then let (a, v) = the (capVPMappedAddress cap); s = capVPSize cap; ptr = capVPBasePtr cap in  
           (do
              unmapPage s a v ptr;
              return NullCap
           od)
  else if isVCPUCap cap then   error []
  else   return NullCap
  )"

defs resetMemMapping_def:
"resetMemMapping x0\<equiv> (case x0 of
    (PageCap p rts sz _) \<Rightarrow>    PageCap p rts sz Nothing
  | (PageTableCap ptr _) \<Rightarrow>    PageTableCap ptr Nothing
  | (PageDirectoryCap ptr _) \<Rightarrow>    PageDirectoryCap ptr Nothing
  | cap \<Rightarrow>    cap
  )"

defs recycleCap_def:
"recycleCap is_final x1 \<equiv> (let cap = x1 in
  if isPageCap cap
  then   (do
      doMachineOp $ clearMemory (capVPBasePtr cap)
          (1 `~shiftL~` (pageBitsForSize $ capVPSize cap));
      finaliseCap cap is_final;
      return $ resetMemMapping cap
  od)
  else if isPageTableCap cap
  then let ptr = capPTBasePtr cap
  in   (do
    slots \<leftarrow> return ( [ptr, ptr + bit pteBits  .e.  ptr + bit ptBits - 1]);
    mapM_x (flip storePTE InvalidPTE) slots;
    doMachineOp $
        cleanCacheRange_PoU (VPtr $ fromPPtr ptr)
                            (VPtr $ fromPPtr ptr + (1 `~shiftL~` ptBits) - 1)
                            (addrFromPPtr ptr);
    (case capPTMappedAddress cap of
          None \<Rightarrow>   return ()
        | Some (a, v) \<Rightarrow>   (do
            mapped \<leftarrow> pageTableMapped a v ptr;
            when (mapped \<noteq> Nothing) $ invalidateTLBByASID a
        od)
        );
    finaliseCap cap is_final;
    return (if is_final then resetMemMapping cap else cap)
  od)
  else if isPageDirectoryCap cap
  then let ptr = capPDBasePtr cap
  in   (do
    pdeBits \<leftarrow> return ( objBits InvalidPDE);
    kBaseEntry \<leftarrow> return ( fromVPtr kernelBase
                        `~shiftR~` pageBitsForSize ARMSection);
    indices \<leftarrow> return ( [0  .e.  kBaseEntry - 1]);
    offsets \<leftarrow> return ( map (PPtr \<circ> flip shiftL pdeBits) indices);
    slots \<leftarrow> return ( map (\<lambda> x. x + ptr) offsets);
    mapM_x (flip storePDE InvalidPDE) slots;
    doMachineOp $
        cleanCacheRange_PoU (VPtr $ fromPPtr ptr)
                            (VPtr $ fromPPtr ptr + (1 `~shiftL~` pdBits) - 1)
                            (addrFromPPtr ptr);
    (case capPDMappedASID cap of
          None \<Rightarrow>   return ()
        | Some a \<Rightarrow>   (
            ignoreFailure $ ((doE
                pd' \<leftarrow> findPDForASID a;
                withoutFailure $ when (ptr = pd') $ invalidateTLBByASID a
            odE)
                                                                          )
        )
        );
    finaliseCap cap is_final;
    return (if is_final then resetMemMapping cap else cap)
  od)
  else if isASIDControlCap cap
  then   return ASIDControlCap
  else if isASIDPoolCap cap
  then let base = capASIDBase cap; ptr = capASIDPool cap
  in   (do
    asidTable \<leftarrow> gets (armKSASIDTable \<circ> ksArchState);
    when (asidTable (asidHighBitsOf base) = Just ptr) $ (do
        deleteASIDPool base ptr;
        setObject ptr (makeObject ::asidpool);
        asidTable \<leftarrow> gets (armKSASIDTable \<circ> ksArchState);
        asidTable' \<leftarrow> return ( asidTable aLU [(asidHighBitsOf base, Just ptr)]);
        modify (\<lambda> s. s \<lparr>
            ksArchState := (ksArchState s) \<lparr> armKSASIDTable := asidTable' \<rparr>\<rparr>)
    od);
    return cap
  od)
  else if isVCPUCap cap
  then   error []
  else undefined
  )"

defs hasRecycleRights_def:
"hasRecycleRights x0\<equiv> (case x0 of
    (PageCap _ rights _ _) \<Rightarrow>    rights = VMReadWrite
  | _ \<Rightarrow>    True
  )"

defs sameRegionAs_def:
"sameRegionAs x0 x1\<equiv> (let (a, b) = (x0, x1) in
  if isPageCap a \<and> isPageCap b
  then 
    let
        botA = capVPBasePtr a;
        botB = capVPBasePtr b;
        topA = botA + bit (pageBitsForSize $ capVPSize a) - 1;
        topB = botB + bit (pageBitsForSize $ capVPSize b) - 1
    in
    
    (botA \<le> botB) \<and> (topA \<ge> topB) \<and> (botB \<le> topB)
  else if isPageTableCap a \<and> isPageTableCap b
  then  
    capPTBasePtr a = capPTBasePtr b
  else if isPageDirectoryCap a \<and> isPageDirectoryCap b
  then  
    capPDBasePtr a = capPDBasePtr b
  else if isASIDControlCap a \<and> isASIDControlCap b
  then   True
  else if isASIDPoolCap a \<and> isASIDPoolCap b
  then  
    capASIDPool a = capASIDPool b
  else if isVCPUCap a \<and> isVCPUCap b
  then   capVCPUPtr a = capVCPUPtr b
  else   False
  )"

defs isPhysicalCap_def:
"isPhysicalCap x0\<equiv> (case x0 of
    ASIDControlCap \<Rightarrow>    False
  | _ \<Rightarrow>    True
  )"

defs sameObjectAs_def:
"sameObjectAs x0 x1\<equiv> (let (a, b) = (x0, x1) in
  if isPageCap a \<and> isPageCap b
  then let ptrA = capVPBasePtr a
  in  
    (ptrA = capVPBasePtr b) \<and> (capVPSize a = capVPSize b)
        \<and> (ptrA \<le> ptrA + bit (pageBitsForSize $ capVPSize a) - 1)
  else   sameRegionAs a b
  )"

definition
"createPageObject ptr numPages\<equiv> (do
    addrs \<leftarrow> placeNewObject ptr UserData numPages;
    doMachineOp $ initMemory (PPtr $ fromPPtr ptr) (1 `~shiftL~` (pageBits + numPages) );
    return addrs
od)"

defs createObject_def:
"createObject t regionBase arg3 \<equiv>
    let funupd = (\<lambda> f x v y. if y = x then v else f y) in
    let pointerCast = PPtr \<circ> fromPPtr in
    let mkPageCap = \<lambda> sz. PageCap (pointerCast regionBase) VMReadWrite sz Nothing
    in (case t of 
        APIObjectType v2 \<Rightarrow> 
            haskell_fail []
        | SmallPageObject \<Rightarrow>  (do
            createPageObject regionBase 0;
            modify (\<lambda> ks. ks \<lparr> gsUserPages :=
              funupd (gsUserPages ks)
                     (fromPPtr regionBase) (Just ARMSmallPage)\<rparr>);
            return $ mkPageCap ARMSmallPage
        od)
        | LargePageObject \<Rightarrow>  (do
            createPageObject regionBase 4;
            modify (\<lambda> ks. ks \<lparr> gsUserPages :=
              funupd (gsUserPages ks)
                     (fromPPtr regionBase) (Just ARMLargePage)\<rparr>);
            return $ mkPageCap ARMLargePage
        od)
        | SectionObject \<Rightarrow>  (do
            createPageObject regionBase 8;
            modify (\<lambda> ks. ks \<lparr> gsUserPages :=
              funupd (gsUserPages ks)
                     (fromPPtr regionBase) (Just ARMSection)\<rparr>);
            return $ mkPageCap ARMSection
        od)
        | SuperSectionObject \<Rightarrow>  (do
            createPageObject regionBase 12;
            modify (\<lambda> ks. ks \<lparr> gsUserPages :=
              funupd (gsUserPages ks)
                     (fromPPtr regionBase) (Just ARMSuperSection)\<rparr>);
            return $ mkPageCap ARMSuperSection
        od)
        | PageTableObject \<Rightarrow>  (do
            ptSize \<leftarrow> return ( ptBits - objBits (makeObject ::pte));
            regionSize \<leftarrow> return ( (1 `~shiftL~` ptBits));
            placeNewObject regionBase (makeObject ::pte) ptSize;
            doMachineOp $
                cleanCacheRange_PoU (VPtr $ fromPPtr regionBase)
                      (VPtr $ fromPPtr regionBase + regionSize - 1)
                      (addrFromPPtr regionBase);
            return $ PageTableCap (pointerCast regionBase) Nothing
        od)
        | PageDirectoryObject \<Rightarrow>  (do
            pdSize \<leftarrow> return ( pdBits - objBits (makeObject ::pde));
            regionSize \<leftarrow> return ( (1 `~shiftL~` pdBits));
            placeNewObject regionBase (makeObject ::pde) pdSize;
            copyGlobalMappings (pointerCast regionBase);
            doMachineOp $
                cleanCacheRange_PoU (VPtr $ fromPPtr regionBase)
                      (VPtr $ fromPPtr regionBase + regionSize - 1)
                      (addrFromPPtr regionBase);
            return $ PageDirectoryCap (pointerCast regionBase) Nothing
        od)
        | Arch.Type.VCPUObject \<Rightarrow>  (
            error []
        )
        )"

defs decodeInvocation_def:
"decodeInvocation label args capIndex slot cap extraCaps \<equiv>
    (case cap of
         VCPUCap _ \<Rightarrow>   decodeARMVCPUInvocation label args capIndex slot cap extraCaps
       | _ \<Rightarrow>   decodeARMMMUInvocation label args capIndex slot cap extraCaps
       )"

defs performInvocation_def:
"performInvocation i \<equiv>
    (let inv = i
                 in case inv of InvokeVCPU iv \<Rightarrow>  (doE
                     withoutPreemption $ performARMVCPUInvocation iv;
                     returnOk []
                 odE)
                 | _ \<Rightarrow>  performARMMMUInvocation i
                 )"

defs capUntypedPtr_def:
"capUntypedPtr x0\<equiv> (case x0 of
    (PageCap ((* PPtr *) p) _ _ _) \<Rightarrow>    PPtr p
  | (PageTableCap ((* PPtr *) p) _) \<Rightarrow>    PPtr p
  | (PageDirectoryCap ((* PPtr *) p) _) \<Rightarrow>    PPtr p
  | ASIDControlCap \<Rightarrow>    error []
  | (ASIDPoolCap ((* PPtr *) p) _) \<Rightarrow>    PPtr p
  | (VCPUCap ((* PPtr *) p)) \<Rightarrow>    PPtr p
  )"

defs capUntypedSize_def:
"capUntypedSize x0\<equiv> (case x0 of
    (PageCap _ _ sz _) \<Rightarrow>    bit (pageBitsForSize sz)
  | (PageTableCap _ _) \<Rightarrow>    bit (ptBits + pteBits)
  | (PageDirectoryCap _ _) \<Rightarrow>    bit (pdBits + pdeBits)
  | (ASIDControlCap ) \<Rightarrow>    bit (asidHighBits + 2)
  | (ASIDPoolCap _ _) \<Rightarrow>    bit (asidLowBits + 2)
  | (VCPUCap _) \<Rightarrow>    bit vcpuBits
  )"


end
end
