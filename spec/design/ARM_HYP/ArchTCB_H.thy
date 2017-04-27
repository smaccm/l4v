(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file ArchTCB_H.thy *)
(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory ArchTCB_H
imports "../TCBDecls_H"
begin
context Arch begin global_naming ARM_HYP_H

definition
decodeTransfer :: "word8 \<Rightarrow> ( syscall_error , copy_register_sets ) kernel_f"
where
"decodeTransfer arg1 \<equiv> returnOk ARMNoExtraRegisters"

definition
performTransfer :: "copy_register_sets \<Rightarrow> machine_word \<Rightarrow> machine_word \<Rightarrow> unit kernel"
where
"performTransfer arg1 arg2 arg3 \<equiv> return ()"

definition
sanitiseRegister :: "bool \<Rightarrow> register \<Rightarrow> machine_word \<Rightarrow> machine_word"
where
"sanitiseRegister b x1 v\<equiv> (case x1 of
    CPSR \<Rightarrow>  
  let
   v' = (v && 0xf8000000) || 0x150;
        modes = [0x10, 0x11, 0x12, 0x13, 0x17, 0x1b, 0x1f]
  in
  
  if (b \<and> ((v && 0x1f) `~elem~` modes))
      then v
      else v'
  | _ \<Rightarrow>    v
  )"

definition
archTCBSanitise :: "machine_word \<Rightarrow> bool kernel"
where
"archTCBSanitise t\<equiv> (do
   v \<leftarrow> liftM (atcbVCPUPtr \<circ> tcbArch) $ getObject t;
   return $ isJust v
od)"


definition
archThreadGet :: "(arch_tcb \<Rightarrow> 'a) \<Rightarrow> machine_word \<Rightarrow> 'a kernel"
where
"archThreadGet f tptr\<equiv> liftM (f \<circ> tcbArch) $ getObject tptr"

definition
archThreadSet :: "(arch_tcb \<Rightarrow> arch_tcb) \<Rightarrow> machine_word \<Rightarrow> unit kernel"
where
"archThreadSet f tptr\<equiv> (do
        tcb \<leftarrow> getObject tptr;
        setObject tptr $ tcb \<lparr> tcbArch := f (tcbArch tcb) \<rparr>
od)"



end
end
