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
TCB accessor functions
*)

chapter "Accessors for Threads and TCBs"

theory TcbAcc_A
imports CSpace_A
begin

context begin interpretation Arch .

requalify_consts
  in_user_frame
  as_user

end

text {* Store or load a word at an offset from an IPC buffer. *}
definition
  store_word_offs :: "obj_ref \<Rightarrow> nat \<Rightarrow> machine_word \<Rightarrow> (unit,'z::state_ext) s_monad" where
 "store_word_offs ptr offs v \<equiv>
    do s \<leftarrow> get;
       assert (in_user_frame (ptr + of_nat (offs * word_size)) s);
       do_machine_op $ storeWord (ptr + of_nat (offs * word_size)) v
    od"


(* Needed for page invocations. *)
definition
  set_message_info :: "obj_ref \<Rightarrow> message_info \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "set_message_info thread info \<equiv>
     as_user thread $ set_register msg_info_register $
                      message_info_to_data info"

end