(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file ArchHypervisor_H.thy *)
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

theory ArchHypervisor_H
imports
  "../CNode_H"
  "../FaultHandlerDecls_H"
(*  "../KI_Decls_H"
  ArchVSpaceDecls_H *)
begin
context Arch begin global_naming ARM_HYP_H

consts'
countTrailingZeros :: "('b :: {HS_bit, finiteBit}) \<Rightarrow> nat"

defs countTrailingZeros_def:
"countTrailingZeros w \<equiv>
    length \<circ> takeWhile Not \<circ> map (testBit w) $ [0  .e.  finiteBitSize w - 1]"


definition
virqSetEOIIRQEN :: "virq \<Rightarrow> machine_word \<Rightarrow> virq"
where
"virqSetEOIIRQEN virq v \<equiv>
    (virq && complement 0x80000) || ((v `~shiftL~` 19) && 0x80000)"

definition
vgicMaintenance :: "unit kernel"
where
"vgicMaintenance \<equiv>
    let
        irqIndex = (\<lambda>  eisr0 eisr1.
            if eisr0 \<noteq> 0 then countTrailingZeros eisr0
                          else countTrailingZeros eisr1);
        badIndex = (\<lambda>  irq_idx. doMachineOp $ ((do
              virq \<leftarrow> get_gic_vcpu_ctrl_lr (fromIntegral irq_idx);
              set_gic_vcpu_ctrl_lr (fromIntegral irq_idx) $ virqSetEOIIRQEN virq 0
        od)
              ))
    in
                         (do
    ct \<leftarrow> gets ksCurThread;
    runnable \<leftarrow> isRunnable ct;
    when runnable $ (do
      eisr0 \<leftarrow> doMachineOp $ get_gic_vcpu_ctrl_eisr0;
      eisr1 \<leftarrow> doMachineOp $ get_gic_vcpu_ctrl_eisr1;
      flags \<leftarrow> doMachineOp $ get_gic_vcpu_ctrl_misr;
      vgic_misr_eoi \<leftarrow> return ( 1);
      fault \<leftarrow>
          if (flags && vgic_misr_eoi \<noteq> 0)
          then
              if (eisr0 = 0 \<and> eisr1 = 0)
                  then return $ VGICMaintenance Nothing
                  else ((do
                      irq_idx \<leftarrow> return ( irqIndex eisr0 eisr1);
                      gic_vcpu_num_list_regs \<leftarrow>
                          gets (armKSGICVCPUNumListRegs \<circ> ksArchState);
                      when (irq_idx < gic_vcpu_num_list_regs) (badIndex irq_idx);
                      return $ VGICMaintenance $ Just $ fromIntegral irq_idx
                  od)
                      )
          else return $ VGICMaintenance Nothing;
      ct \<leftarrow> getCurThread;
      handleFault ct $ ArchFault fault
    od)
                         od)"

definition
vcpuEnable :: "machine_word \<Rightarrow> unit kernel"
where
"vcpuEnable vcpuPtr\<equiv> (do
    vcpu \<leftarrow> getObject vcpuPtr;
    doMachineOp $ (do
        setSCTLR (vcpuRegs vcpu VCPURegSCTLR);
        setHCR hcrVCPU;
        isb;
        set_gic_vcpu_ctrl_hcr (vgicHCR \<circ> vcpuVGIC $ vcpu)
    od)
od)"

definition
vcpuDisable :: "(machine_word) option \<Rightarrow> unit kernel"
where
"vcpuDisable vcpuPtrOpt\<equiv> (do
    doMachineOp dsb;
    (case vcpuPtrOpt of
          Some vcpuPtr \<Rightarrow>   (do
           vcpu \<leftarrow> getObject vcpuPtr;
           hcr \<leftarrow> doMachineOp get_gic_vcpu_ctrl_hcr;
           sctlr \<leftarrow> doMachineOp getSCTLR;
           regs' \<leftarrow> return ( vcpuRegs vcpu  aLU  [(VCPURegSCTLR, sctlr)]);
           setObject vcpuPtr $ vcpu \<lparr>
                 vcpuVGIC := (vcpuVGIC vcpu) \<lparr> vgicHCR := hcr \<rparr>
               , vcpuRegs := regs'
               \<rparr>;
           doMachineOp isb
          od)
        | None \<Rightarrow>   return ()
        );
    doMachineOp $ (do
        set_gic_vcpu_ctrl_hcr 0;
        isb;
        setSCTLR sctlrDefault;
        setHCR hcrNative;
        isb
    od)
od)"

definition
vcpuSave :: "(machine_word * bool) option \<Rightarrow> unit kernel"
where
"vcpuSave x0\<equiv> (case x0 of
    (Some (vcpuPtr, active)) \<Rightarrow>    (do
    doMachineOp dsb;
    vcpu \<leftarrow> getObject vcpuPtr;
    (hcr, sctlr) \<leftarrow> if active
                        then (do
                            sctlr \<leftarrow> doMachineOp getSCTLR;
                            hcr \<leftarrow> doMachineOp get_gic_vcpu_ctrl_hcr;
                            return (sctlr, hcr)
                        od)
                        else return (vcpuSCTLR vcpu, vgicHCR \<circ> vcpuVGIC $ vcpu);
    actlr \<leftarrow> doMachineOp getACTLR;
    vmcr \<leftarrow> doMachineOp get_gic_vcpu_ctrl_vmcr;
    apr \<leftarrow> doMachineOp get_gic_vcpu_ctrl_apr;
    numListRegs \<leftarrow> gets (armKSGICVCPUNumListRegs \<circ> ksArchState);
    gicIndices \<leftarrow> return ( init [0 .e. numListRegs]);
    lrVals \<leftarrow> doMachineOp $ mapM (get_gic_vcpu_ctrl_lr \<circ> fromIntegral) gicIndices;
    vcpuLR \<leftarrow> return ( (vgicLR \<circ> vcpuVGIC $ vcpu)  aLU  zip gicIndices lrVals);
    lr_svc \<leftarrow> doMachineOp get_lr_svc;
    sp_svc \<leftarrow> doMachineOp get_sp_svc;
    lr_abt \<leftarrow> doMachineOp get_lr_abt;
    sp_abt \<leftarrow> doMachineOp get_sp_abt;
    lr_und \<leftarrow> doMachineOp get_lr_und;
    sp_und \<leftarrow> doMachineOp get_sp_und;
    lr_irq \<leftarrow> doMachineOp get_lr_irq;
    sp_irq \<leftarrow> doMachineOp get_sp_irq;
    lr_fiq \<leftarrow> doMachineOp get_lr_fiq;
    sp_fiq \<leftarrow> doMachineOp get_sp_fiq;
    r8_fiq \<leftarrow> doMachineOp get_r8_fiq;
    r9_fiq \<leftarrow> doMachineOp get_r9_fiq;
    r10_fiq \<leftarrow> doMachineOp get_r10_fiq;
    r11_fiq \<leftarrow> doMachineOp get_r11_fiq;
    r12_fiq \<leftarrow> doMachineOp get_r12_fiq;
    regs' \<leftarrow> return ( (vcpuRegs vcpu)  aLU  [(VCPURegSCTLR, sctlr)
                                   ,(VCPURegLRsvc, lr_svc)
                                   ,(VCPURegSPsvc, sp_svc)
                                   ,(VCPURegLRabt, lr_abt)
                                   ,(VCPURegSPabt, sp_abt)
                                   ,(VCPURegLRund, lr_und)
                                   ,(VCPURegSPund, sp_und)
                                   ,(VCPURegLRirq, lr_irq)
                                   ,(VCPURegSPirq, sp_irq)
                                   ,(VCPURegLRfiq, lr_fiq)
                                   ,(VCPURegSPfiq, sp_fiq)
                                   ,(VCPURegR8fiq, r8_fiq)
                                   ,(VCPURegR9fiq, r9_fiq)
                                   ,(VCPURegR10fiq, r10_fiq)
                                   ,(VCPURegR11fiq, r11_fiq)
                                   ,(VCPURegR12fiq, r12_fiq)
                                   ]);
    setObject vcpuPtr $ vcpu \<lparr>
          vcpuACTLR := actlr
        , vcpuVGIC := (vcpuVGIC vcpu) \<lparr> vgicHCR := hcr
                                     , vgicVMCR := vmcr
                                     , vgicAPR := apr
                                     , vgicLR := vcpuLR \<rparr>
        , vcpuRegs := regs'
        \<rparr>;
    doMachineOp isb
    od)
  | _ \<Rightarrow>    haskell_fail []
  )"

definition
vcpuRestore :: "machine_word \<Rightarrow> unit kernel"
where
"vcpuRestore vcpuPtr\<equiv> (do
    doMachineOp $ set_gic_vcpu_ctrl_hcr 0;
    doMachineOp $ isb;
    vcpu \<leftarrow> getObject vcpuPtr;
    vgic \<leftarrow> return ( vcpuVGIC vcpu);
    numListRegs \<leftarrow> gets (armKSGICVCPUNumListRegs \<circ> ksArchState);
    doMachineOp $ (do
        set_gic_vcpu_ctrl_vmcr (vgicVMCR vgic);
        set_gic_vcpu_ctrl_apr (vgicAPR vgic);
        mapM_x (uncurry set_gic_vcpu_ctrl_lr) (map (\<lambda> i. (fromIntegral i, (vgicLR vgic) i)) [0 .e. numListRegs]);
        set_lr_svc (vcpuRegs vcpu VCPURegLRsvc);
        set_sp_svc (vcpuRegs vcpu VCPURegSPsvc);
        set_lr_abt (vcpuRegs vcpu VCPURegLRabt);
        set_sp_abt (vcpuRegs vcpu VCPURegSPabt);
        set_lr_und (vcpuRegs vcpu VCPURegLRund);
        set_sp_und (vcpuRegs vcpu VCPURegSPund);
        set_lr_irq (vcpuRegs vcpu VCPURegLRirq);
        set_sp_irq (vcpuRegs vcpu VCPURegSPirq);
        set_lr_fiq (vcpuRegs vcpu VCPURegLRfiq);
        set_sp_fiq (vcpuRegs vcpu VCPURegSPfiq);
        set_r8_fiq (vcpuRegs vcpu VCPURegR8fiq);
        set_r9_fiq (vcpuRegs vcpu VCPURegR9fiq);
        set_r10_fiq (vcpuRegs vcpu VCPURegR10fiq);
        set_r11_fiq (vcpuRegs vcpu VCPURegR11fiq);
        set_r12_fiq (vcpuRegs vcpu VCPURegR12fiq);
        setACTLR (vcpuACTLR vcpu)
    od);
    vcpuEnable vcpuPtr
od)"

definition
vcpuInvalidateActive :: "unit kernel"
where
"vcpuInvalidateActive\<equiv> (do
    hsCurVCPU \<leftarrow> gets (armHSCurVCPU \<circ> ksArchState);
    (case hsCurVCPU of
          Some (vcpuPtr, True) \<Rightarrow>   vcpuDisable Nothing
        | _ \<Rightarrow>   return ()
        );
    modifyArchState (\<lambda> s. s \<lparr> armHSCurVCPU := Nothing \<rparr>)
od)"

definition
vcpuSwitch :: "(machine_word) option \<Rightarrow> unit kernel"
where
"vcpuSwitch x0\<equiv> (case x0 of
    None \<Rightarrow>    (do
    hsCurVCPU \<leftarrow> gets (armHSCurVCPU \<circ> ksArchState);
    (case hsCurVCPU of
          None \<Rightarrow>   return ()
        | Some (vcpuPtr, active) \<Rightarrow>   (do
            when active $ (do
                vcpuDisable (Just vcpuPtr);
                modifyArchState (\<lambda> s. s \<lparr> armHSCurVCPU := Just (vcpuPtr, False) \<rparr>)
            od);
            return ()
        od)
        )
    od)
  | (Some new) \<Rightarrow>    (do
    hsCurVCPU \<leftarrow> gets (armHSCurVCPU \<circ> ksArchState);
    (case hsCurVCPU of
          None \<Rightarrow>   (do
            vcpuRestore new;
            modifyArchState (\<lambda> s. s \<lparr> armHSCurVCPU := Just (new, True) \<rparr>)
          od)
        | Some (vcpuPtr, active) \<Rightarrow>   (
            if vcpuPtr \<noteq> new
                then (do
                    vcpuSave hsCurVCPU;
                    vcpuRestore new;
                    modifyArchState (\<lambda> s. s \<lparr> armHSCurVCPU := Just (new, True) \<rparr>)
                od)
                else (
                    when (Not active) $ (do
                        doMachineOp isb;
                        vcpuEnable new;
                        modifyArchState (\<lambda> s. s \<lparr> armHSCurVCPU := Just (new, True) \<rparr>)
                    od)
                )
        )
        )
  od)
  )"


consts'
handleHypervisorFault :: "machine_word \<Rightarrow> hyp_fault_type \<Rightarrow> unit kernel"

defs handleHypervisorFault_def:
"handleHypervisorFault thread x1\<equiv> (case x1 of
    (ARMVCPUFault hsr) \<Rightarrow>    (
    handleFault thread (ArchFault $ VCPUFault $ fromIntegral hsr)
    )
  )"


end
end
