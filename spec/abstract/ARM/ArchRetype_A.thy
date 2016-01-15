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
Retyping and untyped invocation
*)

chapter "Retyping and Untyped Invocations"

theory ArchRetype_A
imports
  ArchVSpaceAcc_A
  ArchInvocation_A
begin

text {* This is a placeholder function. We may wish to extend the specification
  with explicitly tagging kernel data regions in memory. *}
definition
  reserve_region :: "obj_ref \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "reserve_region ptr byteLength is_kernel \<equiv> return ()"

text {* Create 4k frame objects that can be mapped into memory. These must be
cleared to prevent past contents being revealed. *}

definition
  create_word_objects :: "word32 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "create_word_objects ptr numObjects sz \<equiv>
  do
    byteLength \<leftarrow> return $ numObjects * 2 ^ sz;
    reserve_region ptr byteLength True;
    rst \<leftarrow> return (map (\<lambda> n. (ptr + (n << sz))) [0  .e.  (of_nat numObjects) - 1]);
    do_machine_op $ mapM_x (\<lambda>x. clearMemory x (2 ^ sz)) rst
 od"

text {* Initialise architecture-specific objects. *}

definition
  init_arch_objects :: "apiobject_type \<Rightarrow> obj_ref \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> obj_ref list \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "init_arch_objects new_type ptr num_objects obj_sz refs \<equiv> case new_type of
    ArchObject ARM_4K_PageObj \<Rightarrow> create_word_objects ptr num_objects 12
  | ArchObject ARM_2M_BlockObj \<Rightarrow> create_word_objects ptr num_objects 21
  | ArchObject ARM_1G_BlockObj \<Rightarrow> create_word_objects ptr num_objects 30
  | ArchObject (PageTableObj PT_L1) \<Rightarrow> do
      mapM_x copy_global_mappings refs;
      do_machine_op $ mapM_x (\<lambda>x. cleanCacheRange_PoU x (x + ((1::word32) << pt_bits) - 1) (addrFromPPtr x)) refs
  | ArchObject (PageTableObj _) \<Rightarrow>
      do_machine_op $ mapM_x (\<lambda>x. cleanCacheRange_PoU x (x + ((1::word32) << pt_bits) - 1) (addrFromPPtr x)) refs
    od
  | _ \<Rightarrow> return ()"
(* FIXME ARMHYP: the two PageTableObj init cases can be folded by using an if l = PT_L1 *)

end
