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
(*  "../KI_Decls_H"
  ArchVSpaceDecls_H *)
begin
context Arch begin global_naming ARM_HYP_H


consts'
handleHypervisorFault :: "machine_word \<Rightarrow> hyp_fault_type \<Rightarrow> unit kernel"


defs handleHypervisorFault_def:
"handleHypervisorFault arg1 hyp \<equiv> case hyp of ARMNoHypFaults \<Rightarrow> haskell_fail []"

definition
vcpuEnable :: "machine_word \<Rightarrow> unit kernel"
where
"vcpuEnable vcpuPtr\<equiv> (do
    vcpu \<leftarrow> getObject vcpuPtr;
    doMachineOp $ (do
        setSCTLR (vcpuSCTLR vcpu);
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
           setObject vcpuPtr $ vcpu \<lparr>
                 vcpuSCTLR := sctlr
               , vcpuVGIC := (vcpuVGIC vcpu) \<lparr> vgicHCR := hcr \<rparr>
               \<rparr>
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
    gicIndices \<leftarrow> return ( [0 .e. numListRegs- 1]);
    lrVals \<leftarrow> doMachineOp $ mapM get_gic_vcpu_ctrl_lr gicIndices;
    vcpuLR \<leftarrow> return ( (vgicLR \<circ> vcpuVGIC $ vcpu)  aLU  zip gicIndices lrVals);
    setObject vcpuPtr $ vcpu \<lparr>
          vcpuSCTLR := sctlr
        , vcpuACTLR := actlr
        , vcpuVGIC := (vcpuVGIC vcpu) \<lparr> vgicHCR := hcr
                                     , vgicVMCR := vmcr
                                     , vgicAPR := apr
                                     , vgicLR := vcpuLR \<rparr>
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
    doMachineOp $ (do
        set_gic_vcpu_ctrl_vmcr (vgicVMCR vgic);
        set_gic_vcpu_ctrl_apr (vgicAPR vgic);
        mapM_x (uncurry set_gic_vcpu_ctrl_lr) (map (\<lambda> i. (i, (vgicLR vgic) i)) [0 .e. gicVCPUMaxNumLR- 1]);
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
          Some (vcpuPtr, True) \<Rightarrow>   (do
            vcpuDisable Nothing;
            modifyArchState (\<lambda> s. s \<lparr> armHSCurVCPU := Just (vcpuPtr, False) \<rparr>)
          od)
        | _ \<Rightarrow>   return ()
        )
od)"

definition
"vcpuCleanInvalidateActive\<equiv> (do
    hsCurVCPU \<leftarrow> gets (armHSCurVCPU \<circ> ksArchState);
    vcpuSave hsCurVCPU;
    vcpuInvalidateActive
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
                        modifyArchState (\<lambda> s. s \<lparr> armHSCurVCPU := Just (new, False) \<rparr>)
                    od)
                )
        )
        )
  od)
  )"



end
end
