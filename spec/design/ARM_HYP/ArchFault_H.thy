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

theory ArchFault_H
imports "../Types_H"
(*  "../KI_Decls_H"
  ArchVSpaceDecls_H *)
begin
context Arch begin global_naming ARM_HYP_H


datatype arch_fault =
    VMFault vptr "machine_word list"
  | VCPUFault machine_word
  | VGICMaintenance "machine_word list"

primrec
  vcpuHSR :: "arch_fault \<Rightarrow> machine_word"
where
  "vcpuHSR (VCPUFault v0) = v0"

primrec
  vmFaultAddress :: "arch_fault \<Rightarrow> vptr"
where
  "vmFaultAddress (VMFault v0 v1) = v0"

primrec
  vgicMaintenanceData :: "arch_fault \<Rightarrow> machine_word list"
where
  "vgicMaintenanceData (VGICMaintenance v0) = v0"

primrec
  vmFaultArchData :: "arch_fault \<Rightarrow> machine_word list"
where
  "vmFaultArchData (VMFault v0 v1) = v1"

primrec
  vcpuHSR_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> arch_fault \<Rightarrow> arch_fault"
where
  "vcpuHSR_update f (VCPUFault v0) = VCPUFault (f v0)"

primrec
  vmFaultAddress_update :: "(vptr \<Rightarrow> vptr) \<Rightarrow> arch_fault \<Rightarrow> arch_fault"
where
  "vmFaultAddress_update f (VMFault v0 v1) = VMFault (f v0) v1"

primrec
  vgicMaintenanceData_update :: "((machine_word list) \<Rightarrow> (machine_word list)) \<Rightarrow> arch_fault \<Rightarrow> arch_fault"
where
  "vgicMaintenanceData_update f (VGICMaintenance v0) = VGICMaintenance (f v0)"

primrec
  vmFaultArchData_update :: "((machine_word list) \<Rightarrow> (machine_word list)) \<Rightarrow> arch_fault \<Rightarrow> arch_fault"
where
  "vmFaultArchData_update f (VMFault v0 v1) = VMFault v0 (f v1)"

abbreviation (input)
  VMFault_trans :: "(vptr) \<Rightarrow> (machine_word list) \<Rightarrow> arch_fault" ("VMFault'_ \<lparr> vmFaultAddress= _, vmFaultArchData= _ \<rparr>")
where
  "VMFault_ \<lparr> vmFaultAddress= v0, vmFaultArchData= v1 \<rparr> == VMFault v0 v1"

abbreviation (input)
  VCPUFault_trans :: "(machine_word) \<Rightarrow> arch_fault" ("VCPUFault'_ \<lparr> vcpuHSR= _ \<rparr>")
where
  "VCPUFault_ \<lparr> vcpuHSR= v0 \<rparr> == VCPUFault v0"

abbreviation (input)
  VGICMaintenance_trans :: "(machine_word list) \<Rightarrow> arch_fault" ("VGICMaintenance'_ \<lparr> vgicMaintenanceData= _ \<rparr>")
where
  "VGICMaintenance_ \<lparr> vgicMaintenanceData= v0 \<rparr> == VGICMaintenance v0"

definition
  isVMFault :: "arch_fault \<Rightarrow> bool"
where
 "isVMFault v \<equiv> case v of
    VMFault v0 v1 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isVCPUFault :: "arch_fault \<Rightarrow> bool"
where
 "isVCPUFault v \<equiv> case v of
    VCPUFault v0 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isVGICMaintenance :: "arch_fault \<Rightarrow> bool"
where
 "isVGICMaintenance v \<equiv> case v of
    VGICMaintenance v0 \<Rightarrow> True
  | _ \<Rightarrow> False"



end
end
