(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file VCPU_H.thy *)
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
    hsCurVCPU \<leftarrow> gets (armHSCurVCPU \<circ> ksArchState);
    (case hsCurVCPU of
          Some (curVCPU, _) \<Rightarrow>   when (curVCPU = vcpuPtr) vcpuInvalidateActive
        | _ \<Rightarrow>   return ()
        );
    archThreadSet (\<lambda> atcb. atcb \<lparr> atcbVCPUPtr := Nothing \<rparr>) tcbPtr;
    setObject vcpuPtr $ vcpu \<lparr> vcpuTCBPtr := Nothing \<rparr>;
    asUser tcbPtr $ ((do
        cpsr \<leftarrow> getRegister (Register CPSR);
        setRegister (Register CPSR) $ sanitiseRegister False (Register CPSR) cpsr
    od)
        )
od)"

definition
associateVCPUTCB :: "machine_word \<Rightarrow> machine_word \<Rightarrow> machine_word list kernel"
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
    setObject vcpuPtr $ vcpu \<lparr> vcpuTCBPtr := Just tcbPtr \<rparr>;
    return []
od)"

definition
decodeVCPUReadReg :: "machine_word list \<Rightarrow> arch_capability \<Rightarrow> ( syscall_error , Arch.invocation ) kernel_f"
where
"decodeVCPUReadReg x0 x1\<equiv> (let (ls, cap) = (x0, x1) in
  if isVCPUCap cap \<and> length ls > 0
  then let field = ls ! 0 in   (doE
    reg \<leftarrow> returnOk ( fromIntegral field);
    whenE (reg > (fromEnum (maxBound ::vcpureg))) $ throw (InvalidArgument 1);
    returnOk $ InvokeVCPU $
        VCPUReadRegister (capVCPUPtr cap) (toEnum reg)
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
    reg \<leftarrow> returnOk ( fromIntegral field);
    whenE (reg > (fromEnum (maxBound ::vcpureg))) $ throw (InvalidArgument 1);
    returnOk $ InvokeVCPU $ VCPUWriteRegister (capVCPUPtr cap)
                (toEnum reg) (fromIntegral val)
  odE)
  else   throw TruncatedMessage
  )"

definition
readVCPUReg :: "machine_word \<Rightarrow> hyper_reg \<Rightarrow> hyper_reg_val kernel"
where
"readVCPUReg vcpuPtr reg\<equiv> (do
    hsCurVCPU \<leftarrow> gets (armHSCurVCPU \<circ> ksArchState);
    (onCurVCPU, active) \<leftarrow> return $ (case hsCurVCPU of
          Some (curVCPU, a) \<Rightarrow>   (curVCPU = vcpuPtr, a)
        | _ \<Rightarrow>   (False, False)
        );
    if onCurVCPU
        then (case reg of
                   VCPURegSCTLR \<Rightarrow>   if active then doMachineOp getSCTLR
                                           else (do
                                               vcpu \<leftarrow> getObject vcpuPtr;
                                               return $ vcpuRegs vcpu reg
                                           od)
                 | VCPURegLRsvc \<Rightarrow>   doMachineOp get_lr_svc
                 | VCPURegSPsvc \<Rightarrow>   doMachineOp get_sp_svc
                 | VCPURegLRabt \<Rightarrow>   doMachineOp get_lr_abt
                 | VCPURegSPabt \<Rightarrow>   doMachineOp get_sp_abt
                 | VCPURegLRund \<Rightarrow>   doMachineOp get_lr_und
                 | VCPURegSPund \<Rightarrow>   doMachineOp get_sp_und
                 | VCPURegLRirq \<Rightarrow>   doMachineOp get_lr_irq
                 | VCPURegSPirq \<Rightarrow>   doMachineOp get_sp_irq
                 | VCPURegLRfiq \<Rightarrow>   doMachineOp get_lr_fiq
                 | VCPURegSPfiq \<Rightarrow>   doMachineOp get_sp_fiq
                 | VCPURegR8fiq \<Rightarrow>   doMachineOp get_r8_fiq
                 | VCPURegR9fiq \<Rightarrow>   doMachineOp get_r9_fiq
                 | VCPURegR10fiq \<Rightarrow>   doMachineOp get_r10_fiq
                 | VCPURegR11fiq \<Rightarrow>   doMachineOp get_r11_fiq
                 | VCPURegR12fiq \<Rightarrow>   doMachineOp get_r12_fiq
                 )
        else (do
            vcpu \<leftarrow> getObject vcpuPtr;
            return $ vcpuRegs vcpu reg
        od)
od)"

definition
writeVCPUReg :: "machine_word \<Rightarrow> hyper_reg \<Rightarrow> hyper_reg_val \<Rightarrow> unit kernel"
where
"writeVCPUReg vcpuPtr reg val\<equiv> (do
    hsCurVCPU \<leftarrow> gets (armHSCurVCPU \<circ> ksArchState);
    (onCurVCPU, active) \<leftarrow> return $ (case hsCurVCPU of
          Some (curVCPU, a) \<Rightarrow>   (curVCPU = vcpuPtr, a)
        | _ \<Rightarrow>   (False, False)
        );
    if onCurVCPU
        then (case reg of
                   VCPURegSCTLR \<Rightarrow>   if active then doMachineOp $ setSCTLR val
                                           else (do
                                               vcpu \<leftarrow> getObject vcpuPtr;
                                               setObject vcpuPtr $ vcpu \<lparr> vcpuRegs := vcpuRegs vcpu  aLU  [(reg, val)] \<rparr>
                                           od)
                 | VCPURegLRsvc \<Rightarrow>   doMachineOp $ set_lr_svc val
                 | VCPURegSPsvc \<Rightarrow>   doMachineOp $ set_sp_svc val
                 | VCPURegLRabt \<Rightarrow>   doMachineOp $ set_lr_abt val
                 | VCPURegSPabt \<Rightarrow>   doMachineOp $ set_sp_abt val
                 | VCPURegLRund \<Rightarrow>   doMachineOp $ set_lr_und val
                 | VCPURegSPund \<Rightarrow>   doMachineOp $ set_sp_und val
                 | VCPURegLRirq \<Rightarrow>   doMachineOp $ set_lr_irq val
                 | VCPURegSPirq \<Rightarrow>   doMachineOp $ set_sp_irq val
                 | VCPURegLRfiq \<Rightarrow>   doMachineOp $ set_lr_fiq val
                 | VCPURegSPfiq \<Rightarrow>   doMachineOp $ set_sp_fiq val
                 | VCPURegR8fiq \<Rightarrow>   doMachineOp $ set_r8_fiq val
                 | VCPURegR9fiq \<Rightarrow>   doMachineOp $ set_r9_fiq val
                 | VCPURegR10fiq \<Rightarrow>   doMachineOp $ set_r10_fiq val
                 | VCPURegR11fiq \<Rightarrow>   doMachineOp $ set_r11_fiq val
                 | VCPURegR12fiq \<Rightarrow>   doMachineOp $ set_r12_fiq val
                 )
        else (do
            vcpu \<leftarrow> getObject vcpuPtr;
            setObject vcpuPtr $ vcpu \<lparr> vcpuRegs := vcpuRegs vcpu  aLU  [(reg, val)] \<rparr>
        od)
od)"

definition
invokeVCPUReadReg :: "machine_word \<Rightarrow> hyper_reg \<Rightarrow> machine_word list kernel"
where
"invokeVCPUReadReg vcpuPtr reg\<equiv> (do
    ct \<leftarrow> getCurThread;
    val \<leftarrow> readVCPUReg vcpuPtr reg;
    return [val]
od)"

definition
invokeVCPUWriteReg :: "machine_word \<Rightarrow> hyper_reg \<Rightarrow> hyper_reg_val \<Rightarrow> machine_word list kernel"
where
"invokeVCPUWriteReg vcpuPtr reg val\<equiv> (do
    hsCurVCPU \<leftarrow> gets (armHSCurVCPU \<circ> ksArchState);
    writeVCPUReg vcpuPtr reg val;
    return []
od)"

definition
makeVIRQ :: "machine_word \<Rightarrow> machine_word \<Rightarrow> machine_word \<Rightarrow> virq"
where
"makeVIRQ grp prio irq \<equiv>
    let
     groupShift = 30;
          prioShift = 23;
          irqPending = bit 28;
          eoiirqen = bit 19
    in
    (grp `~shiftL~` groupShift) || (prio `~shiftL~` prioShift) || irq ||
        irqPending || eoiirqen"

definition
virqType :: "machine_word \<Rightarrow> nat"
where
"virqType virq\<equiv> fromIntegral $ (virq `~shiftR~` 28) && 3"

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
    grp \<leftarrow> returnOk ( (mr0 `~shiftR~` 24) && 0xff);
    index \<leftarrow> returnOk ( mr1 && 0xff);
    rangeCheck vid (0::nat) ((1 `~shiftL~` 10) - 1);
    rangeCheck priority (0::nat) 31;
    rangeCheck grp (0::nat) 1;
    gic_vcpu_num_list_regs \<leftarrow> withoutFailure $
        gets (armKSGICVCPUNumListRegs \<circ> ksArchState);
    rangeCheck index 0 (gic_vcpu_num_list_regs - 1);
    vcpuLR \<leftarrow> withoutFailure $ liftM (vgicLR \<circ> vcpuVGIC) $ getObject vcpuPtr;
    whenE (vcpuLR (fromIntegral index) && vgicIRQMask = vgicIRQActive) $
        throw DeleteFirst;
    virq \<leftarrow> returnOk ( makeVIRQ (fromIntegral grp) (fromIntegral priority) (fromIntegral vid));
    returnOk $ InvokeVCPU $ VCPUInjectIRQ vcpuPtr (fromIntegral index) virq
  odE)
  else   throw TruncatedMessage
  )"

definition
invokeVCPUInjectIRQ :: "machine_word \<Rightarrow> nat \<Rightarrow> virq \<Rightarrow> machine_word list kernel"
where
"invokeVCPUInjectIRQ vcpuPtr index virq\<equiv> (do
    hsCurVCPU \<leftarrow> gets (armHSCurVCPU \<circ> ksArchState);
    if (isJust hsCurVCPU \<and> fst (fromJust hsCurVCPU) = vcpuPtr)
      then
         doMachineOp $ set_gic_vcpu_ctrl_lr (fromIntegral index) virq
      else (do
          vcpu \<leftarrow> getObject vcpuPtr;
          vcpuLR \<leftarrow> return ( (vgicLR \<circ> vcpuVGIC $ vcpu)  aLU  [(index, virq)]);
          setObject vcpuPtr $ vcpu \<lparr> vcpuVGIC := (vcpuVGIC vcpu) \<lparr> vgicLR := vcpuLR \<rparr>\<rparr>
      od);
    return []
od)"

definition
performARMVCPUInvocation :: "vcpuinvocation \<Rightarrow> machine_word list kernel"
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
        )
od)"



end
end
