(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

(* 
  VSpace lookup code.
*)

theory ArchVSpace_H
imports
  "../CNode_H"
  "../KI_Decls_H"
  ArchVSpaceDecls_H
begin
context Arch begin global_naming ARM_HYP_H


defs globalsBase_def:
"globalsBase \<equiv> VPtr 0xffffc000"

defs idleThreadStart_def:
"idleThreadStart \<equiv> globalsBase + VPtr 0x100"

defs idleThreadCode_def:
"idleThreadCode \<equiv>
    [ 0xe3a00000
    , 0xeafffffc
    ]"

defs mapKernelWindow_def:
"mapKernelWindow \<equiv> error []"

defs mapKernelDevice_def:
"mapKernelDevice x0\<equiv> (case x0 of
    (addr, ptr) \<Rightarrow>    error []
  )"

defs activateGlobalVSpace_def:
"activateGlobalVSpace \<equiv> error []"

defs createITPDPTs_def:
"createITPDPTs rootCNCap vptrStart biFrameVPtr \<equiv> error []"

defs writeITPDPTs_def:
"writeITPDPTs rootCNCap pdCap \<equiv> error []"

defs createITASIDPool_def:
"createITASIDPool rootCNCap \<equiv> error []"

defs writeITASIDPool_def:
"writeITASIDPool apCap pdCap \<equiv> error []"

defs mapITPTCap_def:
"mapITPTCap pdCap ptCap \<equiv> error []"

defs mapITFrameCap_def:
"mapITFrameCap pdCap frameCap \<equiv> error []"

defs createIPCBufferFrame_def:
"createIPCBufferFrame rootCNCap vptr \<equiv> error []"

defs createBIFrame_def:
"createBIFrame rootCNCap vptr nodeId numNodes \<equiv> error []"

defs createITFrameCap_def:
"createITFrameCap pptr vptr asid large \<equiv> error []"

defs createFramesOfRegion_def:
"createFramesOfRegion rootCNCap region doMap \<equiv> error []"

defs mapGlobalsFrame_def:
"mapGlobalsFrame \<equiv> error []"

defs writeIdleCode_def:
"writeIdleCode \<equiv> error []"

defs mapKernelFrame_def:
"mapKernelFrame paddr vaddr vmrights attributes \<equiv> error []"

defs getARMGlobalPT_def:
"getARMGlobalPT \<equiv> error []"

defs createDeviceFrames_def:
"createDeviceFrames rootCNodeCap \<equiv> error []"

defs copyGlobalMappings_def:
"copyGlobalMappings newPD\<equiv> (do
    globalPT \<leftarrow> gets (armUSGlobalPT \<circ> ksArchState);
    pde \<leftarrow> return ( PageTablePDE (addrFromPPtr globalPT));
    pdSize \<leftarrow> return ( bit (pdBits));
    offset \<leftarrow> return ( pdSize - bit pdeBits);
    storePDE (newPD + offset) pde
od)"

definition
"largePagePTEOffsets \<equiv>
    let
     pts = fromIntegral pteBits
    in
                             [0, PPtr pts  .e.  PPtr (15 `~shiftL~` pteBits)] :: [PPtr PTE]"

definition
"superSectionPDEOffsets \<equiv>
    let
     pds = fromIntegral pdeBits
    in
                                [0, PPtr pds  .e.  PPtr (15 `~shiftL~` pdeBits)] :: [PPtr PDE]"

defs createMappingEntries_def:
"createMappingEntries base vptr x2 vmRights attrib pd\<equiv> (case x2 of
    ARMSmallPage \<Rightarrow>    (doE
    p \<leftarrow> lookupErrorOnFailure False $ lookupPTSlot pd vptr;
    returnOk $ Inl (SmallPagePTE_ \<lparr>
        pteFrame= base,
        pteCacheable= armPageCacheable attrib,
        pteExecuteNever= armExecuteNever attrib,
        pteRights= vmRights \<rparr>, [p])
    odE)
  | ARMLargePage \<Rightarrow>    (doE
    p \<leftarrow> lookupErrorOnFailure False $ lookupPTSlot pd vptr;
    returnOk $ Inl (LargePagePTE_ \<lparr>
        pteFrame= base,
        pteCacheable= armPageCacheable attrib,
        pteExecuteNever= armExecuteNever attrib,
        pteRights= vmRights \<rparr>, map (\<lambda> x. x + p) largePagePTEOffsets)
  odE)
  | ARMSection \<Rightarrow>    (doE
    p \<leftarrow> returnOk ( lookupPDSlot pd vptr);
    returnOk $ Inr (SectionPDE_ \<lparr>
        pdeFrame= base,
        pdeCacheable= armPageCacheable attrib,
        pdeExecuteNever= armExecuteNever attrib,
        pdeRights= vmRights \<rparr>, [p])
  odE)
  | ARMSuperSection \<Rightarrow>    (doE
    p \<leftarrow> returnOk ( lookupPDSlot pd vptr);
    returnOk $ Inr (SuperSectionPDE_ \<lparr>
        pdeFrame= base,
        pdeCacheable= armPageCacheable attrib,
        pdeExecuteNever= armExecuteNever attrib,
        pdeRights= vmRights \<rparr>, map (\<lambda> x. x + p) superSectionPDEOffsets)
  odE)
  )"

defs ensureSafeMapping_def:
"ensureSafeMapping x0\<equiv> (case x0 of
    (Inl (InvalidPTE, _)) \<Rightarrow>    returnOk ()
  | (Inl (SmallPagePTE _ _ _ _, ptSlots)) \<Rightarrow>   
    forME_x ptSlots (\<lambda> slot. (doE
        pte \<leftarrow> withoutFailure $ getObject slot;
        (case pte of
              InvalidPTE \<Rightarrow>   returnOk ()
            | SmallPagePTE _ _ _ _ \<Rightarrow>   returnOk ()
            | _ \<Rightarrow>   throw DeleteFirst
            )
    odE))
  | (Inl (LargePagePTE _ _ _ _, ptSlots)) \<Rightarrow>   
    forME_x ptSlots (\<lambda> slot. (doE
        pte \<leftarrow> withoutFailure $ getObject slot;
        (case pte of
              InvalidPTE \<Rightarrow>   returnOk ()
            | LargePagePTE _ _ _ _ \<Rightarrow>   returnOk ()
            | _ \<Rightarrow>   throw DeleteFirst
            )
    odE))
  | (Inr (InvalidPDE, _)) \<Rightarrow>    returnOk ()
  | (Inr (PageTablePDE _, _)) \<Rightarrow>   
    haskell_fail []
  | (Inr (SectionPDE _ _ _ _, pdSlots)) \<Rightarrow>   
    forME_x pdSlots (\<lambda> slot. (doE
        pde \<leftarrow> withoutFailure $ getObject slot;
        (case pde of
              InvalidPDE \<Rightarrow>   returnOk ()
            | SectionPDE _ _ _ _ \<Rightarrow>   returnOk ()
            | _ \<Rightarrow>   throw DeleteFirst
            )
    odE))
  | (Inr (SuperSectionPDE _ _ _ _, pdSlots)) \<Rightarrow>   
    forME_x pdSlots (\<lambda> slot. (doE
        pde \<leftarrow> withoutFailure $ getObject slot;
        (case pde of
              InvalidPDE \<Rightarrow>   returnOk ()
            | SuperSectionPDE _ _ _ _ \<Rightarrow>   returnOk ()
            | _ \<Rightarrow>   throw DeleteFirst
            )
    odE))
  )"

defs lookupIPCBuffer_def:
"lookupIPCBuffer isReceiver thread\<equiv> (do
    bufferPtr \<leftarrow> threadGet tcbIPCBuffer thread;
    bufferFrameSlot \<leftarrow> getThreadBufferSlot thread;
    bufferCap \<leftarrow> getSlotCap bufferFrameSlot;
    (let v33 = bufferCap in
        if isArchObjectCap v33 \<and> isPageCap (capCap v33)
        then let frame = capCap v33
        in  (do
            rights \<leftarrow> return ( capVPRights frame);
            pBits \<leftarrow> return ( pageBitsForSize $ capVPSize frame);
            if (rights = VMReadWrite \<or> Not isReceiver \<and> rights = VMReadOnly)
              then (do
                 ptr \<leftarrow> return ( capVPBasePtr frame +
                           PPtr (fromVPtr bufferPtr && mask pBits));
                 haskell_assert (ptr \<noteq> 0)
                            [];
                 return $ Just ptr
              od)
              else return Nothing
        od)
        else  return Nothing
        )
od)"

defs findPDForASID_def:
"findPDForASID asid\<equiv> (doE
    haskell_assertE (asid > 0) [];
    haskell_assertE (asid \<le> snd asidRange) [];
    asidTable \<leftarrow> withoutFailure $ gets (armKSASIDTable \<circ> ksArchState);
    poolPtr \<leftarrow> returnOk ( asidTable (asidHighBitsOf asid));
 pool \<leftarrow> liftME (inv ASIDPool) $  (case poolPtr of
          Some ptr \<Rightarrow>   withoutFailure $ getObject ptr
        | None \<Rightarrow>   throw InvalidRoot
        );
    pd \<leftarrow> returnOk ( pool (asid && mask asidLowBits));
    (case pd of
          Some ptr \<Rightarrow>   (doE
            haskell_assertE (ptr \<noteq> 0) [];
            withoutFailure $ checkPDAt ptr;
            returnOk ptr
          odE)
        | None \<Rightarrow>   throw InvalidRoot
        )
odE)"

defs findPDForASIDAssert_def:
"findPDForASIDAssert asid\<equiv> (do
    pd \<leftarrow> findPDForASID asid `~catchFailure~`
        const (haskell_fail []);
    haskell_assert (pd && mask pdBits = 0)
        [];
    checkPDAt pd;
    checkPDUniqueToASID pd asid;
    asidMap \<leftarrow> gets (armKSASIDMap \<circ> ksArchState);
    flip haskell_assert []
        $ (case asidMap asid of
              None \<Rightarrow>   True
            | Some (_, pd') \<Rightarrow>   pd = pd'
            );
    return pd
od)"

defs checkPDUniqueToASID_def:
"checkPDUniqueToASID pd asid \<equiv> checkPDASIDMapMembership pd [asid]"

defs checkPDNotInASIDMap_def:
"checkPDNotInASIDMap pd \<equiv> checkPDASIDMapMembership pd []"

defs lookupPTSlot_def:
"lookupPTSlot pd vptr\<equiv> (doE
    pdSlot \<leftarrow> returnOk ( lookupPDSlot pd vptr);
    pde \<leftarrow> withoutFailure $ getObject pdSlot;
    (case pde of
          PageTablePDE _ \<Rightarrow>   (doE
            pt \<leftarrow> returnOk ( ptrFromPAddr $ pdeTable pde);
            withoutFailure $ lookupPTSlotFromPT pt vptr
          odE)
        | _ \<Rightarrow>   throw $ MissingCapability 20
        )
odE)"

defs lookupPTSlotFromPT_def:
"lookupPTSlotFromPT pt vptr\<equiv> (do
    ptIndex \<leftarrow> return ( fromVPtr $ vptr `~shiftR~` pageBits && mask (ptBits - pteBits));
    ptSlot \<leftarrow> return ( pt + (PPtr $ ptIndex `~shiftL~` pteBits));
    checkPTAt pt;
    return ptSlot
od)"

defs lookupPDSlot_def:
"lookupPDSlot pd vptr \<equiv>
    let pdIndex = fromVPtr $ vptr `~shiftR~` (pageBits + ptBits - pteBits)
    in pd + (PPtr $ pdIndex `~shiftL~` pdeBits)"

defs handleVMFault_def:
"handleVMFault thread x1\<equiv> (case x1 of
    ARMDataAbort \<Rightarrow>    (doE
    addr \<leftarrow> withoutFailure $ doMachineOp getHDFAR;
    uaddr \<leftarrow> withoutFailure $ doMachineOp (addressTranslateS1CPR addr);
    faddr \<leftarrow> returnOk ( (uaddr && complement (mask pageBits)) ||
                (addr && mask pageBits));
    fault \<leftarrow> withoutFailure $ doMachineOp getHSR;
    throw $ ArchFault $ VMFault faddr [0, fault && 0x3ffffff]
    odE)
  | ARMPrefetchAbort \<Rightarrow>    (doE
    pc \<leftarrow> withoutFailure $ asUser thread $ getRestartPC;
    upc \<leftarrow> withoutFailure $ doMachineOp (addressTranslateS1CPR $ VPtr pc);
    faddr \<leftarrow> returnOk ( (upc && complement (mask pageBits)) ||
                (VPtr pc && mask pageBits));
    fault \<leftarrow> withoutFailure $ doMachineOp getHSR;
    throw $ ArchFault $ VMFault faddr [1, fault && 0x3ffffff]
  odE)
  )"

defs deleteASIDPool_def:
"deleteASIDPool base ptr\<equiv> (do
    haskell_assert (base && mask asidLowBits = 0)
        [];
    asidTable \<leftarrow> gets (armKSASIDTable \<circ> ksArchState);
    when (asidTable (asidHighBitsOf base) = Just ptr) $ (do
 pool \<leftarrow> liftM (inv ASIDPool) $  getObject ptr;
        forM [0  .e.  (bit asidLowBits) - 1] (\<lambda> offset. (
            when (isJust $ pool offset) $ (do
                flushSpace $ base + offset;
                invalidateASIDEntry $ base + offset
            od)
        ));
        asidTable' \<leftarrow> return ( asidTable aLU [(asidHighBitsOf base, Nothing)]);
        modify (\<lambda> s. s \<lparr>
            ksArchState := (ksArchState s) \<lparr> armKSASIDTable := asidTable' \<rparr>\<rparr>);
        tcb \<leftarrow> getCurThread;
        setVMRoot tcb
    od)
od)"

defs deleteASID_def:
"deleteASID asid pd\<equiv> (do
    asidTable \<leftarrow> gets (armKSASIDTable \<circ> ksArchState);
    (case asidTable (asidHighBitsOf asid) of
          None \<Rightarrow>   return ()
        | Some poolPtr \<Rightarrow>   (do
 pool \<leftarrow> liftM (inv ASIDPool) $  getObject poolPtr;
            when (pool (asid && mask asidLowBits) = Just pd) $ (do
                flushSpace asid;
                invalidateASIDEntry asid;
                pool' \<leftarrow> return ( pool aLU [(asid && mask asidLowBits, Nothing)]);
                setObject poolPtr $ ASIDPool pool';
                tcb \<leftarrow> getCurThread;
                setVMRoot tcb
            od)
        od)
        )
od)"

defs pageTableMapped_def:
"pageTableMapped asid vaddr pt \<equiv> catchFailure
    ((doE
        pd \<leftarrow> findPDForASID asid;
        pdSlot \<leftarrow> returnOk ( lookupPDSlot pd vaddr);
        pde \<leftarrow> withoutFailure $ getObject pdSlot;
        (case pde of
              PageTablePDE pt' \<Rightarrow>   returnOk $
                if pt' = addrFromPPtr pt then Just pd else Nothing
            | _ \<Rightarrow>   returnOk Nothing)
            
    odE)
            )
    (\<lambda> _. return Nothing)"

defs unmapPageTable_def:
"unmapPageTable asid vaddr pt\<equiv> (do
    maybePD \<leftarrow> pageTableMapped asid vaddr pt;
    (case maybePD of
          Some pd \<Rightarrow>   (do
            pdSlot \<leftarrow> return ( lookupPDSlot pd vaddr);
            storePDE pdSlot InvalidPDE;
            doMachineOp $ cleanByVA_PoU (VPtr $ fromPPtr pdSlot) (addrFromPPtr pdSlot);
            flushTable pd asid vaddr
          od)
        | None \<Rightarrow>   return ()
        )
od)"

defs unmapPage_def:
"unmapPage magnitude asid vptr ptr\<equiv> ignoreFailure $ (doE
    pd \<leftarrow> findPDForASID asid;
    (case magnitude of
          ARMSmallPage \<Rightarrow>   (doE
            p \<leftarrow> lookupPTSlot pd vptr;
            checkMappingPPtr ptr magnitude (Inl p);
            withoutFailure $ (do
                storePTE p InvalidPTE;
                doMachineOp $ cleanByVA_PoU (VPtr $ fromPPtr p) (addrFromPPtr p)
            od)
          odE)
        | ARMLargePage \<Rightarrow>   (doE
            p \<leftarrow> lookupPTSlot pd vptr;
            checkMappingPPtr ptr magnitude (Inl p);
            withoutFailure $ (do
                slots \<leftarrow> return ( map (\<lambda> x. x + p) largePagePTEOffsets);
                mapM (flip storePTE InvalidPTE) slots;
                doMachineOp $
                    cleanCacheRange_PoU (VPtr $ fromPPtr $ (head slots))
                                        (VPtr $ (fromPPtr (last slots)) + (bit pteBits - 1))
                                        (addrFromPPtr (head slots))
            od)
        odE)
        | ARMSection \<Rightarrow>   (doE
            p \<leftarrow> returnOk ( lookupPDSlot pd vptr);
            checkMappingPPtr ptr magnitude (Inr p);
            withoutFailure $ (do
                storePDE p InvalidPDE;
                doMachineOp $ cleanByVA_PoU (VPtr $ fromPPtr p) (addrFromPPtr p)
            od)
        odE)
        | ARMSuperSection \<Rightarrow>   (doE
            p \<leftarrow> returnOk ( lookupPDSlot pd vptr);
            checkMappingPPtr ptr magnitude (Inr p);
            withoutFailure $ (do
                slots \<leftarrow> return ( map (\<lambda> x. x + p) superSectionPDEOffsets);
                mapM (flip storePDE InvalidPDE) slots;
                doMachineOp $
                    cleanCacheRange_PoU (VPtr $ fromPPtr $ (head slots))
                                        (VPtr $ (fromPPtr (last slots)) + (bit pdeBits - 1))
                                        (addrFromPPtr (head slots))
            od)
        odE)
        );
    withoutFailure $ flushPage magnitude pd asid vptr
odE)"

defs checkMappingPPtr_def:
"checkMappingPPtr pptr magnitude x2\<equiv> (case x2 of
    (Inl pt) \<Rightarrow>    (doE
    pte \<leftarrow> withoutFailure $ getObject pt;
    (case (pte, magnitude) of
          (SmallPagePTE base _ _ _, ARMSmallPage) \<Rightarrow>  
            unlessE (base = addrFromPPtr pptr) $ throw InvalidRoot
        | (LargePagePTE base _ _ _, ARMLargePage) \<Rightarrow>  
            unlessE (base = addrFromPPtr pptr) $ throw InvalidRoot
        | _ \<Rightarrow>   throw InvalidRoot
        )
    odE)
  | (Inr pd) \<Rightarrow>    (doE
    pde \<leftarrow> withoutFailure $ getObject pd;
    (case (pde, magnitude) of
          (SectionPDE base _ _ _, ARMSection) \<Rightarrow>  
            unlessE (base = addrFromPPtr pptr) $ throw InvalidRoot
        | (SuperSectionPDE base _ _ _, ARMSuperSection) \<Rightarrow>  
            unlessE (base = addrFromPPtr pptr) $ throw InvalidRoot
        | _ \<Rightarrow>   throw InvalidRoot
        )
  odE)
  )"

defs armv_contextSwitch_HWASID_def:
"armv_contextSwitch_HWASID pd hwasid \<equiv> (
   writeContextIDAndPD hwasid (addrFromPPtr pd)
)"

defs armv_contextSwitch_def:
"armv_contextSwitch pd asid \<equiv> (do
   hwasid \<leftarrow> getHWASID asid;
   doMachineOp $ armv_contextSwitch_HWASID pd hwasid
od)"

defs setVMRoot_def:
"setVMRoot tcb\<equiv> (do
    threadRootSlot \<leftarrow> getThreadVSpaceRoot tcb;
    threadRoot \<leftarrow> getSlotCap threadRootSlot;
    catchFailure
        ((case threadRoot of
              ArchObjectCap (PageDirectoryCap pd (Some asid)) \<Rightarrow>   (doE
                pd' \<leftarrow> findPDForASID asid;
                whenE (pd \<noteq> pd') $ (
                    throw InvalidRoot
                );
                withoutFailure $ armv_contextSwitch pd asid
              odE)
            | _ \<Rightarrow>   throw InvalidRoot)
            )
        (\<lambda> _. (do
            (case threadRoot of
                  ArchObjectCap (PageDirectoryCap pd (Some _)) \<Rightarrow>   checkPDNotInASIDMap pd
                | _ \<Rightarrow>   return ()
                );
            doMachineOp $ setCurrentPD (addrFromPPtr 0)
        od)
                                                       )
od)"

defs setVMRootForFlush_def:
"setVMRootForFlush pd asid\<equiv> (do
    tcb \<leftarrow> getCurThread;
    threadRootSlot \<leftarrow> getThreadVSpaceRoot tcb;
    threadRoot \<leftarrow> getSlotCap threadRootSlot;
    (let v37 = threadRoot in
        if isArchObjectCap v37 \<and> isPageDirectoryCap (capCap v37) \<and> capPDMappedASID (capCap v37) \<noteq> None \<and> capPDBasePtr (capCap v37) = pd
        then let cur_pd = pd in  return False
        else  (do
            armv_contextSwitch pd asid;
            return True
        od)
        )
od)"

defs isValidVTableRoot_def:
"isValidVTableRoot x0\<equiv> (case x0 of
    (ArchObjectCap (PageDirectoryCap _ (Some _))) \<Rightarrow>    True
  | _ \<Rightarrow>    False
  )"

defs checkValidIPCBuffer_def:
"checkValidIPCBuffer vptr x1\<equiv> (case x1 of
    (ArchObjectCap (PageCap _ _ _ _)) \<Rightarrow>    (doE
    whenE (vptr && mask msgAlignBits \<noteq> 0) $ throw AlignmentError;
    returnOk ()
    odE)
  | _ \<Rightarrow>    throw IllegalOperation
  )"

defs maskVMRights_def:
"maskVMRights r m\<equiv> (case (r, capAllowRead m, capAllowWrite m) of
      (VMNoAccess, _, _) \<Rightarrow>   VMNoAccess
    | (VMReadOnly, True, _) \<Rightarrow>   VMReadOnly
    | (VMReadWrite, True, False) \<Rightarrow>   VMReadOnly
    | (VMReadWrite, True, True) \<Rightarrow>   VMReadWrite
    | _ \<Rightarrow>   VMKernelOnly
    )"

defs attribsFromWord_def:
"attribsFromWord w \<equiv> VMAttributes_ \<lparr>
    armPageCacheable= w !! 0,
    armParityEnabled= w !! 1,
    armExecuteNever= w !! 2 \<rparr>"

defs storeHWASID_def:
"storeHWASID asid hw_asid \<equiv> (do
    pd \<leftarrow> findPDForASIDAssert asid;
    asidMap \<leftarrow> gets (armKSASIDMap \<circ> ksArchState);
    asidMap' \<leftarrow> return ( asidMap aLU [(asid, Just (hw_asid, pd))]);
    modify (\<lambda> s. s \<lparr>
        ksArchState := (ksArchState s)
        \<lparr> armKSASIDMap := asidMap' \<rparr>\<rparr>);
    hwASIDMap \<leftarrow> gets (armKSHWASIDTable \<circ> ksArchState);
    hwASIDMap' \<leftarrow> return ( hwASIDMap aLU [(hw_asid, Just asid)]);
    modify (\<lambda> s. s \<lparr>
        ksArchState := (ksArchState s)
        \<lparr> armKSHWASIDTable := hwASIDMap' \<rparr>\<rparr>)
od)"

defs loadHWASID_def:
"loadHWASID asid\<equiv> (do
    asidMap \<leftarrow> gets (armKSASIDMap \<circ> ksArchState);
    findPDForASIDAssert asid;
    return $ (case asidMap asid of
          None \<Rightarrow>   Nothing
        | Some (hw_asid, _) \<Rightarrow>   Just hw_asid
        )
od)"

defs invalidateASID_def:
"invalidateASID asid\<equiv> (do
    findPDForASIDAssert asid;
    asidMap \<leftarrow> gets (armKSASIDMap \<circ> ksArchState);
    asidMap' \<leftarrow> return ( asidMap aLU [(asid, Nothing)]);
    modify (\<lambda> s. s \<lparr>
        ksArchState := (ksArchState s)
        \<lparr> armKSASIDMap := asidMap' \<rparr>\<rparr>)
od)"

defs invalidateHWASIDEntry_def:
"invalidateHWASIDEntry hwASID\<equiv> (do
    asidMap \<leftarrow> gets (armKSHWASIDTable \<circ> ksArchState);
    asidMap' \<leftarrow> return ( asidMap aLU [(hwASID, Nothing)]);
    modify (\<lambda> s. s \<lparr>
        ksArchState := (ksArchState s)
        \<lparr> armKSHWASIDTable := asidMap' \<rparr>\<rparr>)
od)"

defs invalidateASIDEntry_def:
"invalidateASIDEntry asid\<equiv> (do
    maybeHWASID \<leftarrow> loadHWASID asid;
    when (isJust maybeHWASID) $ invalidateHWASIDEntry (fromJust maybeHWASID);
    invalidateASID asid
od)"

defs findFreeHWASID_def:
"findFreeHWASID\<equiv> (do
    hwASIDTable \<leftarrow> gets (armKSHWASIDTable \<circ> ksArchState);
    nextASID \<leftarrow> gets (armKSNextASID \<circ> ksArchState);
    maybe_asid \<leftarrow> return ( find (\<lambda> a. isNothing (hwASIDTable a))
                      ([nextASID  .e.  maxBound] @ init [minBound  .e.  nextASID]));
    (case maybe_asid of
          Some hw_asid \<Rightarrow>   return hw_asid
        | None \<Rightarrow>   (do
            invalidateASID $ fromJust $ hwASIDTable nextASID;
            doMachineOp $ invalidateTLB_ASID nextASID;
            invalidateHWASIDEntry nextASID;
            new_nextASID \<leftarrow> return (
                    if nextASID = maxBound
                    then minBound
                    else nextASID + 1);
            modify (\<lambda> s. s \<lparr>
                ksArchState := (ksArchState s)
                \<lparr> armKSNextASID := new_nextASID \<rparr>\<rparr>);
            return nextASID
        od)
        )
od)"

defs getHWASID_def:
"getHWASID asid\<equiv> (do
    maybe_hw_asid \<leftarrow> loadHWASID asid;
    (case maybe_hw_asid of
          Some hw_asid \<Rightarrow>  
            return hw_asid
        | None \<Rightarrow>   (do
            new_hw_asid \<leftarrow> findFreeHWASID;
            storeHWASID asid new_hw_asid;
            return new_hw_asid
        od)
        )
od)"

defs doFlush_def:
"doFlush x0 vstart vend pstart\<equiv> (case x0 of
    Clean \<Rightarrow>   
    cleanCacheRange_RAM vstart vend pstart
  | Invalidate \<Rightarrow>   
    invalidateCacheRange_RAM vstart vend pstart
  | CleanInvalidate \<Rightarrow>   
    cleanInvalidateCacheRange_RAM vstart vend pstart
  | Unify \<Rightarrow>    (do
    cleanCacheRange_PoU vstart vend pstart;
    dsb;
    invalidateCacheRange_I vstart vend pstart;
    branchFlushRange vstart vend pstart;
    isb
  od)
  )"

defs flushPage_def:
"flushPage arg1 pd asid vptr \<equiv> (do
    haskell_assert (vptr && mask pageBits = 0)
        [];
    root_switched \<leftarrow> setVMRootForFlush pd asid;
    maybe_hw_asid \<leftarrow> loadHWASID asid;
    when (isJust maybe_hw_asid) $ (do
 hw_asid \<leftarrow> liftM the $  return ( maybe_hw_asid);
      doMachineOp $ invalidateTLB_VAASID (fromVPtr vptr || (fromIntegral $ fromHWASID hw_asid));
      when root_switched $ (do
          tcb \<leftarrow> getCurThread;
          setVMRoot tcb
      od)
    od)
od)"

defs flushTable_def:
"flushTable pd asid vptr\<equiv> (do
    haskell_assert (vptr && mask (pageBitsForSize ARMSection) = 0)
        [];
    root_switched \<leftarrow> setVMRootForFlush pd asid;
    maybe_hw_asid \<leftarrow> loadHWASID asid;
    when (isJust maybe_hw_asid) $ (do
      doMachineOp $ invalidateTLB_ASID (fromJust maybe_hw_asid);
      when root_switched $ (do
          tcb \<leftarrow> getCurThread;
          setVMRoot tcb
      od)
    od)
od)"

defs flushSpace_def:
"flushSpace asid\<equiv> (do
    maybe_hw_asid \<leftarrow> loadHWASID asid;
    doMachineOp cleanCaches_PoU;
    (case maybe_hw_asid of
          None \<Rightarrow>   return ()
        | Some hw_asid \<Rightarrow>   (
            doMachineOp $ invalidateTLB_ASID hw_asid
        )
        )
od)"

defs invalidateTLBByASID_def:
"invalidateTLBByASID asid\<equiv> (do
    maybe_hw_asid \<leftarrow> loadHWASID asid;
    (case maybe_hw_asid of
          None \<Rightarrow>   return ()
        | Some hw_asid \<Rightarrow>   (
            doMachineOp $ invalidateTLB_ASID hw_asid
        )
        )
od)"

defs labelToFlushType_def:
"labelToFlushType label\<equiv> (case invocationType label of
        ArchInvocationLabel ARMPDClean_Data \<Rightarrow>   Clean
      | ArchInvocationLabel ARMPageClean_Data \<Rightarrow>   Clean
      | ArchInvocationLabel ARMPDInvalidate_Data \<Rightarrow>   Invalidate
      | ArchInvocationLabel ARMPageInvalidate_Data \<Rightarrow>   Invalidate
      | ArchInvocationLabel ARMPDCleanInvalidate_Data \<Rightarrow>   CleanInvalidate
      | ArchInvocationLabel ARMPageCleanInvalidate_Data \<Rightarrow>   CleanInvalidate
      | ArchInvocationLabel ARMPDUnify_Instruction \<Rightarrow>   Unify
      | ArchInvocationLabel ARMPageUnify_Instruction \<Rightarrow>   Unify
      | _ \<Rightarrow>   error []
      )"

defs pageBase_def:
"pageBase vaddr magnitude\<equiv> vaddr && (complement $ mask (pageBitsForSize magnitude))"

defs resolveVAddr_def:
"resolveVAddr pd vaddr\<equiv> (do
    pdSlot \<leftarrow> return ( lookupPDSlot pd vaddr);
    pde \<leftarrow> getObject pdSlot;
    (case pde of
          SectionPDE frame v45 v46 v47 \<Rightarrow>   return $ Just (ARMSection, frame)
        | SuperSectionPDE frame v48 v49 v50 \<Rightarrow>   return $ Just (ARMSuperSection, frame)
        | PageTablePDE table \<Rightarrow>   (do
            pt \<leftarrow> return ( ptrFromPAddr table);
            pteSlot \<leftarrow> lookupPTSlotFromPT pt vaddr;
            pte \<leftarrow> getObject pteSlot;
            (case pte of
                  LargePagePTE frame v39 v40 v41 \<Rightarrow>   return $ Just (ARMLargePage, frame)
                | SmallPagePTE frame v42 v43 v44 \<Rightarrow>   return $ Just (ARMSmallPage, frame)
                | _ \<Rightarrow>   return Nothing
                )
        od)
        | _ \<Rightarrow>   return Nothing
        )
od)"

definition
"isIOSpaceFrame arg1 \<equiv> False"

defs decodeARMMMUInvocation_def:
"decodeARMMMUInvocation label args x2 cte x4 extraCaps\<equiv> (* case removed *) undefined"

defs decodeARMPageFlush_def:
"decodeARMPageFlush label args cap\<equiv> (case (args, capVPMappedAddress cap) of
      (start#end#_, Some (asid, _)) \<Rightarrow>   (doE
        vaddr \<leftarrow> returnOk ( capVPBasePtr cap);
        pd \<leftarrow> lookupErrorOnFailure False $ findPDForASID asid;
        whenE (end \<le> start) $
            throw $ InvalidArgument 1;
        pageSize \<leftarrow> returnOk ( bit (pageBitsForSize (capVPSize cap)));
        pageBase \<leftarrow> returnOk ( addrFromPPtr $ capVPBasePtr cap);
        whenE (start \<ge> pageSize \<or> end > pageSize) $
            throw $ InvalidArgument 0;
        pstart \<leftarrow> returnOk ( pageBase + toPAddr start);
        start' \<leftarrow> returnOk ( start + fromPPtr vaddr);
        end' \<leftarrow> returnOk ( end + fromPPtr vaddr);
        returnOk $ InvokePage $ PageFlush_ \<lparr>
              pageFlushType= labelToFlushType label,
              pageFlushStart= VPtr $ start',
              pageFlushEnd= VPtr $ end' - 1,
              pageFlushPStart= pstart,
              pageFlushPD= pd,
              pageFlushASID= asid \<rparr>
      odE)
    | (_#_#_, None) \<Rightarrow>   throw IllegalOperation
    | _ \<Rightarrow>   throw TruncatedMessage
    )"

defs checkVPAlignment_def:
"checkVPAlignment sz w \<equiv>
    unlessE (w && mask (pageBitsForSize sz) = 0) $
           throw AlignmentError"

defs performARMMMUInvocation_def:
"performARMMMUInvocation i\<equiv> withoutPreemption $ (do
    (case i of
          InvokePageDirectory oper \<Rightarrow>   performPageDirectoryInvocation oper
        | InvokePageTable oper \<Rightarrow>   performPageTableInvocation oper
        | InvokePage oper \<Rightarrow>   performPageInvocation oper
        | InvokeASIDControl oper \<Rightarrow>   performASIDControlInvocation oper
        | InvokeASIDPool oper \<Rightarrow>   performASIDPoolInvocation oper
        | InvokeVCPU v52 \<Rightarrow>   haskell_fail []
        );
    return $ []
od)"

defs performPageDirectoryInvocation_def:
"performPageDirectoryInvocation x0\<equiv> (case x0 of
    (PageDirectoryFlush typ start end pstart pd asid) \<Rightarrow>   
    when (start < end) $ (do
        root_switched \<leftarrow> setVMRootForFlush pd asid;
        doMachineOp $ doFlush typ start end pstart;
        when root_switched $ (do
            tcb \<leftarrow> getCurThread;
            setVMRoot tcb
        od)
    od)
  | PageDirectoryNothing \<Rightarrow>    return ()
  )"

defs performPageTableInvocation_def:
"performPageTableInvocation x0\<equiv> (case x0 of
    (PageTableMap cap ctSlot pde pdSlot) \<Rightarrow>    (do
    updateCap ctSlot cap;
    storePDE pdSlot pde;
    doMachineOp $ cleanByVA_PoU (VPtr $ fromPPtr $ pdSlot) (addrFromPPtr pdSlot)
    od)
  | (PageTableUnmap cap ctSlot) \<Rightarrow>    (do
    (case capPTMappedAddress cap of
          Some (asid, vaddr) \<Rightarrow>   (do
            unmapPageTable asid vaddr (capPTBasePtr cap);
            ptr \<leftarrow> return ( capPTBasePtr cap);
            slots \<leftarrow> return ( [ptr, ptr + bit pteBits  .e.  ptr + bit ptBits - 1]);
            mapM_x (flip storePTE InvalidPTE) slots;
            doMachineOp $
                cleanCacheRange_PoU (VPtr $ fromPPtr $ ptr)
                                    (VPtr $ fromPPtr $ (ptr + (bit ptBits) - 1))
                                    (addrFromPPtr ptr)
          od)
        | None \<Rightarrow>   return ()
        );
 cap \<leftarrow> liftM capCap $  getSlotCap ctSlot;
    updateCap ctSlot (ArchObjectCap $
                           cap \<lparr> capPTMappedAddress := Nothing \<rparr>)
  od)
  )"

defs pteCheckIfMapped_def:
"pteCheckIfMapped slot\<equiv> (do
    pt \<leftarrow> getObject slot;
    return $ pt \<noteq> InvalidPTE
od)"

defs pdeCheckIfMapped_def:
"pdeCheckIfMapped slot\<equiv> (do
    pd \<leftarrow> getObject slot;
    return $ pd \<noteq> InvalidPDE
od)"

defs performPageInvocation_def:
"performPageInvocation x0\<equiv> (case x0 of
    (PageMap asid cap ctSlot entries) \<Rightarrow>    (do
    updateCap ctSlot cap;
    (case entries of
          Inl (pte, slots) \<Rightarrow>   (do
            tlbFlush \<leftarrow> pteCheckIfMapped (head slots);
            mapM (flip storePTE pte) slots;
            doMachineOp $
                cleanCacheRange_PoU (VPtr $ fromPPtr $ head slots)
                                    (VPtr $ (fromPPtr (last slots)) + (bit pteBits - 1))
                                    (addrFromPPtr (head slots));
            when tlbFlush $ invalidateTLBByASID asid
          od)
        | Inr (pde, slots) \<Rightarrow>   (do
            tlbFlush \<leftarrow> pdeCheckIfMapped (head slots);
            mapM (flip storePDE pde) slots;
            doMachineOp $
                cleanCacheRange_PoU (VPtr $ fromPPtr $ head slots)
                                    (VPtr $ (fromPPtr (last slots)) + (bit pdeBits - 1))
                                    (addrFromPPtr (head slots));
            when tlbFlush $ invalidateTLBByASID asid
        od)
        )
    od)
  | (PageRemap asid (Inl (pte, slots))) \<Rightarrow>    (do
    tlbFlush \<leftarrow> pteCheckIfMapped (head slots);
    mapM (flip storePTE pte) slots;
    doMachineOp $
        cleanCacheRange_PoU (VPtr $ fromPPtr $ head slots)
                            (VPtr $ (fromPPtr (last slots)) + (bit pteBits - 1))
                            (addrFromPPtr (head slots));
    when tlbFlush $ invalidateTLBByASID asid
  od)
  | (PageRemap asid (Inr (pde, slots))) \<Rightarrow>    (do
    tlbFlush \<leftarrow> pdeCheckIfMapped (head slots);
    mapM (flip storePDE pde) slots;
    doMachineOp $
        cleanCacheRange_PoU (VPtr $ fromPPtr $ head slots)
                            (VPtr $ (fromPPtr (last slots)) + (bit pdeBits - 1))
                            (addrFromPPtr (head slots));
    when tlbFlush $ invalidateTLBByASID asid
  od)
  | (PageUnmap cap ctSlot) \<Rightarrow>    (do
    (case capVPMappedAddress cap of
          Some (asid, vaddr) \<Rightarrow>   unmapPage (capVPSize cap) asid vaddr
                                    (capVPBasePtr cap)
        | None \<Rightarrow>   return ()
        );
 cap \<leftarrow> liftM capCap $  getSlotCap ctSlot;
    updateCap ctSlot (ArchObjectCap $
                           cap \<lparr> capVPMappedAddress := Nothing \<rparr>)
  od)
  | (PageFlush typ start end pstart pd asid) \<Rightarrow>   
    when (start < end) $ (do
        root_switched \<leftarrow> setVMRootForFlush pd asid;
        doMachineOp $ doFlush typ start end pstart;
        when root_switched $ (do
            tcb \<leftarrow> getCurThread;
            setVMRoot tcb
        od)
    od)
  | (PageGetAddr ptr) \<Rightarrow>    (do
    paddr \<leftarrow> return ( fromPAddr $ addrFromPPtr ptr);
    ct \<leftarrow> getCurThread;
    msgTransferred \<leftarrow> setMRs ct Nothing [paddr];
    msgInfo \<leftarrow> return $ MI_ \<lparr>
            msgLength= msgTransferred,
            msgExtraCaps= 0,
            msgCapsUnwrapped= 0,
            msgLabel= 0 \<rparr>;
    setMessageInfo ct msgInfo
  od)
  )"

defs performASIDControlInvocation_def:
"performASIDControlInvocation x0\<equiv> (case x0 of
    (MakePool frame slot parent base) \<Rightarrow>    (do
    deleteObjects frame pageBits;
    pcap \<leftarrow> getSlotCap parent;
    updateCap parent (pcap \<lparr>capFreeIndex := maxFreeIndex (capBlockSize pcap) \<rparr>);
    placeNewObject frame (makeObject ::asidpool) 0;
    poolPtr \<leftarrow> return ( PPtr $ fromPPtr frame);
    cteInsert (ArchObjectCap $ ASIDPoolCap poolPtr base) parent slot;
    haskell_assert (base && mask asidLowBits = 0)
        [];
    asidTable \<leftarrow> gets (armKSASIDTable \<circ> ksArchState);
    asidTable' \<leftarrow> return ( asidTable aLU [(asidHighBitsOf base, Just poolPtr)]);
    modify (\<lambda> s. s \<lparr>
        ksArchState := (ksArchState s) \<lparr> armKSASIDTable := asidTable' \<rparr>\<rparr>)
    od)
  )"

defs performASIDPoolInvocation_def:
"performASIDPoolInvocation x0\<equiv> (case x0 of
    (Assign asid poolPtr ctSlot) \<Rightarrow>    (do
    oldcap \<leftarrow> getSlotCap ctSlot;
 pool \<leftarrow> liftM (inv ASIDPool) $  getObject poolPtr;
 cap \<leftarrow> liftM capCap $  return ( oldcap);
    updateCap ctSlot (ArchObjectCap $ cap \<lparr> capPDMappedASID := Just asid \<rparr>);
    pool' \<leftarrow> return ( pool aLU [(asid && mask asidLowBits, Just $ capPDBasePtr cap)]);
    setObject poolPtr $ ASIDPool pool'
    od)
  )"

defs storePDE_def:
"storePDE slot pde\<equiv> (do
    setObject slot pde;
    v58 \<leftarrow>   return ( wordsFromPDE pde);
    w0 \<leftarrow> headM v58;
     v60 \<leftarrow>   tailM v58;
     w1 \<leftarrow> headM v60;
     v59 \<leftarrow> tailM v60;
    haskell_assert (v59 = []) [];
    doMachineOp $ storeWordVM (PPtr $ fromPPtr slot) w0;
    doMachineOp $ storeWordVM (PPtr $ fromPPtr slot + fromIntegral wordSize) w1
od)"

defs storePTE_def:
"storePTE slot pte\<equiv> (do
    setObject slot pte;
    v62 \<leftarrow>   return ( wordsFromPTE pte);
    w0 \<leftarrow> headM v62;
     v64 \<leftarrow>   tailM v62;
     w1 \<leftarrow> headM v64;
     v63 \<leftarrow> tailM v64;
    haskell_assert (v63 = []) [];
    doMachineOp $ storeWordVM (PPtr $ fromPPtr slot) w0;
    doMachineOp $ storeWordVM (PPtr $ fromPPtr slot + fromIntegral wordSize) w1
od)"


defs checkValidMappingSize_def:
  "checkValidMappingSize sz \<equiv> stateAssert
    (\<lambda>s. 2 ^ pageBitsForSize sz <= gsMaxObjectSize s) []"

end
end
