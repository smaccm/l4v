(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "VCPU"

theory VCPU_H
imports Hardware_H "../Structures_H"
  "../Invocations_H"
  "../TCB_H"
begin
context Arch begin global_naming ARM_HYP_H

definition
decodeVCPUSetTCB :: "arch_capability \<Rightarrow> (capability * machine_word) list \<Rightarrow> ( syscall_error , Arch.invocation ) kernel_f"
where
"decodeVCPUSetTCB x0 extraCaps\<equiv> (let cap = x0 in
  if isVCPUCap cap then   (doE
    whenE (null extraCaps) $ throw TruncatedMessage;
    tcbPtr \<leftarrow> (case fst (head extraCaps) of
          ThreadCap tcbPtr \<Rightarrow>   returnOk tcbPtr
        | _ \<Rightarrow>   throw IllegalOperation
        );
    returnOk $ InvokeVCPU $ VCPUSetTCB (capVCPUPtr cap) tcbPtr
  odE)
  else   throw IllegalOperation
  )"

definition
dissociateVCPUTCB :: "machine_word \<Rightarrow> machine_word \<Rightarrow> unit kernel"
where
"dissociateVCPUTCB vcpuPtr tcbPtr\<equiv> (do
    tcbVCPU \<leftarrow> archThreadGet atcbVCPUPtr tcbPtr;
    vcpu \<leftarrow> getObject vcpuPtr;
    vcpuTCB \<leftarrow> return ( vcpuTCBPtr vcpu);
    when (tcbVCPU \<noteq> Just vcpuPtr \<or> vcpuTCB \<noteq> Just tcbPtr) $
        haskell_fail [];
    setObject vcpuPtr $ vcpu \<lparr> vcpuTCBPtr := Nothing \<rparr>;
    archThreadSet (\<lambda> atcb. atcb \<lparr> atcbVCPUPtr := Nothing \<rparr>) tcbPtr
od)"

definition
associateVCPUTCB :: "machine_word \<Rightarrow> machine_word \<Rightarrow> unit kernel"
where
"associateVCPUTCB vcpuPtr tcbPtr\<equiv> (do
    tcbVCPU \<leftarrow> archThreadGet atcbVCPUPtr tcbPtr;
    (case tcbVCPU of
        Some ptr \<Rightarrow>   dissociateVCPUTCB ptr tcbPtr
      | _ \<Rightarrow>   return ()
      );
    vcpu \<leftarrow> getObject vcpuPtr;
    (case (vcpuTCBPtr vcpu) of
          Some ptr \<Rightarrow>   dissociateVCPUTCB vcpuPtr ptr
        | _ \<Rightarrow>   return ()
        );
    archThreadSet (\<lambda> atcb. atcb \<lparr> atcbVCPUPtr := Just vcpuPtr \<rparr>) tcbPtr;
    setObject vcpuPtr $ vcpu \<lparr> vcpuTCBPtr := Just tcbPtr \<rparr>
od)"

definition
decodeVCPUReadReg :: "machine_word list \<Rightarrow> arch_capability \<Rightarrow> ( syscall_error , Arch.invocation ) kernel_f"
where
"decodeVCPUReadReg x0 x1\<equiv> (let (ls, cap) = (x0, x1) in
  if isVCPUCap cap \<and> length ls > 0
  then let field = ls ! 0 in   (doE
    whenE (field \<noteq> 0) $ throw (InvalidArgument 1);
    returnOk $ InvokeVCPU $
        VCPUReadRegister (capVCPUPtr cap) (fromIntegral field)
  odE)
  else   throw TruncatedMessage
  )"

definition
decodeVCPUWriteReg :: "machine_word list \<Rightarrow> arch_capability \<Rightarrow> ( syscall_error , Arch.invocation ) kernel_f"
where
"decodeVCPUWriteReg x0 x1\<equiv> (let (ls, cap) = (x0, x1) in
  if isVCPUCap cap \<and> length ls > 1
  then let field = ls ! 0; val = ls ! 1
  in   (doE
    whenE (field \<noteq> 0) $ throw (InvalidArgument 1);
    returnOk $ InvokeVCPU $ VCPUWriteRegister (capVCPUPtr cap)
                (fromIntegral field) (fromIntegral val)
  odE)
  else   throw TruncatedMessage
  )"

definition
readVCPUReg :: "machine_word \<Rightarrow> hyper_reg \<Rightarrow> hyper_reg_val kernel"
where
"readVCPUReg vcpuPtr reg\<equiv> (
    if reg = 0
        then (do
            vcpu \<leftarrow> getObject vcpuPtr;
            return $ vcpuSCTLR vcpu
        od)
        else haskell_fail []
)"

definition
writeVCPUReg :: "machine_word \<Rightarrow> hyper_reg \<Rightarrow> hyper_reg_val \<Rightarrow> unit kernel"
where
"writeVCPUReg vcpuPtr reg val \<equiv>
    if reg = 0
        then (do
            vcpu \<leftarrow> getObject vcpuPtr;
            setObject vcpuPtr $ vcpu \<lparr> vcpuSCTLR := val \<rparr>
        od)
        else haskell_fail []"

definition
invokeVCPUReadReg :: "machine_word \<Rightarrow> hyper_reg \<Rightarrow> unit kernel"
where
"invokeVCPUReadReg vcpuPtr reg\<equiv> (do
    ct \<leftarrow> getCurThread;
    hsCurVCPU \<leftarrow> gets (armHSCurVCPU \<circ> ksArchState);
    (case hsCurVCPU of
          Some (vcpuPtr, _) \<Rightarrow>  
           vcpuCleanInvalidateActive
        | _ \<Rightarrow>   return ()
        );
    val \<leftarrow> readVCPUReg vcpuPtr reg;
    asUser ct $ setRegister (msgRegisters ! 0) $ fromIntegral val;
    msgInfo \<leftarrow> return ( MI_ \<lparr>
            msgLength= 1,
            msgExtraCaps= 0,
            msgCapsUnwrapped= 0,
            msgLabel= 0 \<rparr>);
    setMessageInfo ct msgInfo;
    setThreadState Running ct
od)"

definition
invokeVCPUWriteReg :: "machine_word \<Rightarrow> hyper_reg \<Rightarrow> hyper_reg_val \<Rightarrow> unit kernel"
where
"invokeVCPUWriteReg vcpuPtr reg val\<equiv> (do
    hsCurVCPU \<leftarrow> gets (armHSCurVCPU \<circ> ksArchState);
    (case hsCurVCPU of
          Some (vcpuPtr, _) \<Rightarrow>  
            vcpuCleanInvalidateActive
        | _ \<Rightarrow>   return ()
        );
    writeVCPUReg vcpuPtr reg val;
    ct \<leftarrow> getCurThread;
    setThreadState Restart ct
od)"

definition
makeVIRQ :: "machine_word \<Rightarrow> machine_word \<Rightarrow> machine_word \<Rightarrow> virq"
where
"makeVIRQ group prio irq \<equiv>
    let
     groupShift = 30;
          prioShift = 23;
          irqPending = bit 28;
          eoiirqen = bit 19
    in
    (group `~shiftL~` groupShift) || (prio `~shiftL~` prioShift) || irq ||
        irqPending || eoiirqen"

definition
decodeVCPUInjectIRQ :: "machine_word list \<Rightarrow> arch_capability \<Rightarrow> ( syscall_error , Arch.invocation ) kernel_f"
where
"decodeVCPUInjectIRQ x0 x1\<equiv> (let (ls, cap) = (x0, x1) in
  if isVCPUCap cap \<and> length ls > 1
  then let mr0 = ls ! 0; mr1 = ls ! 1
  in   (doE
    vcpuPtr \<leftarrow> returnOk ( capVCPUPtr cap);
    vid \<leftarrow> returnOk ( mr0 && 0xffff);
    priority \<leftarrow> returnOk ( (mr0 `~shiftR~` 16) && 0xff);
    group \<leftarrow> returnOk ( (mr0 `~shiftR~` 24) && 0xff);
    index \<leftarrow> returnOk ( mr1 && 0xff);
    rangeCheck vid (0::nat) ((1 `~shiftL~` 10) - 1);
    rangeCheck priority (0::nat) 31;
    rangeCheck group (0::nat) 1;
    gic_vcpu_num_list_regs \<leftarrow> withoutFailure $
        gets (armKSGICVCPUNumListRegs \<circ> ksArchState);
    rangeCheck index 0 gic_vcpu_num_list_regs;
    vcpuLR \<leftarrow> withoutFailure $ liftM (vgicLR \<circ> vcpuVGIC) $ getObject vcpuPtr;
    whenE (vcpuLR (fromIntegral index) && vgicIRQMask = vgicIRQActive) $
        throw DeleteFirst;
    virq \<leftarrow> returnOk ( makeVIRQ (fromIntegral group) (fromIntegral priority) (fromIntegral vid));
    returnOk $ InvokeVCPU $ VCPUInjectIRQ vcpuPtr (fromIntegral index) virq
  odE)
  else   throw TruncatedMessage
  )"

definition
invokeVCPUInjectIRQ :: "machine_word \<Rightarrow> nat \<Rightarrow> virq \<Rightarrow> unit kernel"
where
"invokeVCPUInjectIRQ vcpuPtr index virq\<equiv> (do
    hsCurVCPU \<leftarrow> gets (armHSCurVCPU \<circ> ksArchState);
    (case hsCurVCPU of
          Some (vcpuPtr, _) \<Rightarrow>  
            doMachineOp $ set_gic_vcpu_ctrl_lr index virq
        | _ \<Rightarrow>   (do
             vcpu \<leftarrow> getObject vcpuPtr;
             vcpuLR \<leftarrow> return ( (vgicLR \<circ> vcpuVGIC $ vcpu)  aLU  [(index, virq)]);
             setObject vcpuPtr $ vcpu \<lparr> vcpuVGIC := (vcpuVGIC vcpu) \<lparr> vgicLR := vcpuLR \<rparr>\<rparr>
        od)
        );
    ct \<leftarrow> getCurThread;
    setThreadState Restart ct
od)"

definition
performARMVCPUInvocation :: "vcpuinvocation \<Rightarrow> unit kernel"
where
"performARMVCPUInvocation x0\<equiv> (case x0 of
    (VCPUSetTCB vcpuPtr tcbPtr) \<Rightarrow>   
    associateVCPUTCB vcpuPtr tcbPtr
  | (VCPUReadRegister vcpuPtr reg) \<Rightarrow>   
    invokeVCPUReadReg vcpuPtr reg
  | (VCPUWriteRegister vcpuPtr reg val) \<Rightarrow>   
    invokeVCPUWriteReg vcpuPtr reg val
  | (VCPUInjectIRQ vcpuPtr index virq) \<Rightarrow>   
    invokeVCPUInjectIRQ vcpuPtr index virq
  )"

definition
decodeARMVCPUInvocation :: "machine_word \<Rightarrow> machine_word list \<Rightarrow> cptr \<Rightarrow> machine_word \<Rightarrow> arch_capability \<Rightarrow> (capability * machine_word) list \<Rightarrow> ( syscall_error , Arch.invocation ) kernel_f"
where
"decodeARMVCPUInvocation label args capIndex slot x4 extraCaps\<equiv> (let cap = x4 in
  if isVCPUCap cap then  
    (case invocationType label of
          ArchInvocationLabel ARMVCPUSetTCB \<Rightarrow>  
            decodeVCPUSetTCB cap extraCaps
        | ArchInvocationLabel ARMVCPUReadReg \<Rightarrow>  
            decodeVCPUReadReg args cap
        | ArchInvocationLabel ARMVCPUWriteReg \<Rightarrow>  
            decodeVCPUWriteReg args cap
        | ArchInvocationLabel ARMVCPUInjectIRQ \<Rightarrow>  
            decodeVCPUInjectIRQ args cap
        | _ \<Rightarrow>   throw IllegalOperation
        )
  else   throw IllegalOperation
  )"

definition
vcpuFinalise :: "machine_word \<Rightarrow> unit kernel"
where
"vcpuFinalise vcpuPtr\<equiv> (do
    vcpu \<leftarrow> getObject vcpuPtr;
    (case vcpuTCBPtr vcpu of
          Some tcbPtr \<Rightarrow>   dissociateVCPUTCB vcpuPtr tcbPtr
        | None \<Rightarrow>   return ()
        );
    hsCurVCPU \<leftarrow> gets (armHSCurVCPU \<circ> ksArchState);
    (case hsCurVCPU of
          Some (vcpuPtr, _) \<Rightarrow>   vcpuInvalidateActive
        | _ \<Rightarrow>   return ()
        )
od)"



end
end
