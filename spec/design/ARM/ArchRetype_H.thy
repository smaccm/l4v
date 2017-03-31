(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file ArchRetype_H.thy *)
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
  "../KI_Decls_H"
begin
context Arch begin global_naming ARM_H

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
  then let (a, v) = the (capVPMappedAddress cap); s = capVPSize cap; ptr = capVPBasePtr cap
  in  
           (do
              unmapPage s a v ptr;
              return NullCap
           od)
  else   return NullCap
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
        \<and> (capVPIsDevice a = capVPIsDevice b)
  else   sameRegionAs a b
  )"

defs placeNewDataObject_def:
"placeNewDataObject regionBase sz isDevice \<equiv> if isDevice
    then placeNewObject regionBase UserDataDevice sz
    else placeNewObject regionBase UserData sz"

defs createObject_def:
"createObject t regionBase arg3 isDevice \<equiv>
    let funupd = (\<lambda> f x v y. if y = x then v else f y) in
    let pointerCast = PPtr \<circ> fromPPtr in
    let mkPageCap = \<lambda> sz. PageCap isDevice (pointerCast regionBase) VMReadWrite sz Nothing
    in (case t of 
        APIObjectType v2 \<Rightarrow> 
            haskell_fail []
        | SmallPageObject \<Rightarrow>  (do
            placeNewDataObject regionBase 0 isDevice;
            modify (\<lambda> ks. ks \<lparr> gsUserPages :=
              funupd (gsUserPages ks)
                     (fromPPtr regionBase) (Just ARMSmallPage)\<rparr>);
            return $ mkPageCap ARMSmallPage
        od)
        | LargePageObject \<Rightarrow>  (do
            placeNewDataObject regionBase 4 isDevice;
            modify (\<lambda> ks. ks \<lparr> gsUserPages :=
              funupd (gsUserPages ks)
                     (fromPPtr regionBase) (Just ARMLargePage)\<rparr>);
            return $ mkPageCap ARMLargePage
        od)
        | SectionObject \<Rightarrow>  (do
            placeNewDataObject regionBase 8 isDevice;
            modify (\<lambda> ks. ks \<lparr> gsUserPages :=
              funupd (gsUserPages ks)
                     (fromPPtr regionBase) (Just ARMSection)\<rparr>);
            return $ mkPageCap ARMSection
        od)
        | SuperSectionObject \<Rightarrow>  (do
            placeNewDataObject regionBase 12 isDevice;
            modify (\<lambda> ks. ks \<lparr> gsUserPages :=
              funupd (gsUserPages ks)
                     (fromPPtr regionBase) (Just ARMSuperSection)\<rparr>);
            return $ mkPageCap ARMSuperSection
        od)
        | PageTableObject \<Rightarrow>  (do
            ptSize \<leftarrow> return ( ptBits - objBits (makeObject ::pte));
            placeNewObject regionBase (makeObject ::pte) ptSize;
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
        )"

defs decodeInvocation_def:
"decodeInvocation label args capIndex slot cap extraCaps \<equiv>
    (case cap of
         _ \<Rightarrow>   decodeARMMMUInvocation label args capIndex slot cap extraCaps
       )"

defs performInvocation_def:
"performInvocation i \<equiv>
    (case i of
                   _ \<Rightarrow>   performARMMMUInvocation i
                 )"

defs capUntypedPtr_def:
"capUntypedPtr x0\<equiv> (case x0 of
    (PageCap _ ((* PPtr *) p) _ _ _) \<Rightarrow>    PPtr p
  | (PageTableCap ((* PPtr *) p) _) \<Rightarrow>    PPtr p
  | (PageDirectoryCap ((* PPtr *) p) _) \<Rightarrow>    PPtr p
  | ASIDControlCap \<Rightarrow>    error []
  | (ASIDPoolCap ((* PPtr *) p) _) \<Rightarrow>    PPtr p
  )"

defs capUntypedSize_def:
"capUntypedSize x0\<equiv> (case x0 of
    (PageCap _ _ _ sz _) \<Rightarrow>    bit (pageBitsForSize sz)
  | (PageTableCap _ _) \<Rightarrow>    bit ptBits
  | (PageDirectoryCap _ _) \<Rightarrow>    bit pdBits
  | (ASIDControlCap ) \<Rightarrow>    bit (asidHighBits + 2)
  | (ASIDPoolCap _ _) \<Rightarrow>    bit (asidLowBits + 2)
  )"

defs prepareThreadDelete_def:
"prepareThreadDelete arg1 \<equiv> return ()"


end
end
