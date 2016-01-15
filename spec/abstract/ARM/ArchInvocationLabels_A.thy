(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

(* FIXME ARMHYP: duplicates ArchInvocationLabels_H until Haskell update *)
chapter "Architecture-specific Invocation Labels"

theory ArchInvocationLabels_A
imports "../../../lib/Enumeration"
begin

text {*
  An enumeration of arch-specific system call labels.
*}

datatype arch_invocation_label =
    ARMPDClean_Data
  | ARMPDInvalidate_Data
  | ARMPDCleanInvalidate_Data
  | ARMPDUnify_Instruction
  | ARMPageTableMap
  | ARMPageTableUnmap
  | ARMPageMap
  | ARMPageRemap
  | ARMPageUnmap
  | ARMPageClean_Data
  | ARMPageInvalidate_Data
  | ARMPageCleanInvalidate_Data
  | ARMPageUnify_Instruction
  | ARMPageGetAddress
  | ARMASIDControlMakePool
  (* ARMHYP NEW *)
  | ARMASIDPoolAssign
  | ARMVCPUDissociate
  | ARMVCPUAssociate
  | ARMVCPUReadRegister
  | ARMVCPUWriteRegister
  | ARMIOSpaceMap
  | ARMIOSpaceUnmap

(* arch_invocation_label instance proofs *)
(*<*)
instantiation arch_invocation_label :: enum begin
definition
  enum_arch_invocation_label: "enum_class.enum \<equiv> 
    [ 
      ARMPDClean_Data,
      ARMPDInvalidate_Data,
      ARMPDCleanInvalidate_Data,
      ARMPDUnify_Instruction,
      ARMPageTableMap,
      ARMPageTableUnmap,
      ARMPageMap,
      ARMPageRemap,
      ARMPageUnmap,
      ARMPageClean_Data,
      ARMPageInvalidate_Data,
      ARMPageCleanInvalidate_Data,
      ARMPageUnify_Instruction,
      ARMPageGetAddress,
      ARMASIDControlMakePool,
      ARMASIDPoolAssign,
      ARMVCPUDissociate,
      ARMVCPUAssociate,
      ARMVCPUReadRegister,
      ARMVCPUWriteRegister,
      ARMIOSpaceMap,
      ARMIOSpaceUnmap
    ]"


definition
  "enum_class.enum_all (P :: arch_invocation_label \<Rightarrow> bool) \<longleftrightarrow> Ball UNIV P"

definition
  "enum_class.enum_ex (P :: arch_invocation_label \<Rightarrow> bool) \<longleftrightarrow> Bex UNIV P"

  instance
  apply intro_classes
   apply (safe, simp)
   apply (case_tac x)
  apply (simp_all add: enum_arch_invocation_label enum_all_arch_invocation_label_def enum_ex_arch_invocation_label_def)
  by fast+
end

instantiation arch_invocation_label :: enum_alt
begin
definition
  enum_alt_arch_invocation_label: "enum_alt \<equiv> 
    alt_from_ord (enum :: arch_invocation_label list)"
instance ..
end

instantiation arch_invocation_label :: enumeration_both
begin
instance by (intro_classes, simp add: enum_alt_arch_invocation_label)
end

(* FIXME ARMHYP: copied from other Haskell to make abstract work *)
definition
isPDFlush :: "invocation_label \<Rightarrow> bool"
where
"isPDFlush x\<equiv> (case x of
        ARMPDClean_Data \<Rightarrow>   True
      | ARMPDInvalidate_Data \<Rightarrow>   True
      | ARMPDCleanInvalidate_Data \<Rightarrow>   True
      | ARMPDUnify_Instruction \<Rightarrow>   True
      | _ \<Rightarrow>   False
      )"

definition
isPageFlush :: "invocation_label \<Rightarrow> bool"
where
"isPageFlush x\<equiv> (case x of
        ARMPageClean_Data \<Rightarrow>   True
      | ARMPageInvalidate_Data \<Rightarrow>   True
      | ARMPageCleanInvalidate_Data \<Rightarrow>   True
      | ARMPageUnify_Instruction \<Rightarrow>   True
      | _ \<Rightarrow>   False
      )"

(*>*)


end
