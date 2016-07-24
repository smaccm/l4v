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
context Arch begin global_naming ARM_H

definition
decodeTransfer :: "word8 \<Rightarrow> ( syscall_error , copy_register_sets ) kernel_f"
where
"decodeTransfer arg1 \<equiv> returnOk ARMNoExtraRegisters"

definition
performTransfer :: "copy_register_sets \<Rightarrow> machine_word \<Rightarrow> machine_word \<Rightarrow> unit kernel"
where
"performTransfer arg1 arg2 arg3 \<equiv> return ()"



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

definition
asUser :: "machine_word \<Rightarrow> 'a user_monad \<Rightarrow> 'a kernel"
where
"asUser tptr f\<equiv> (do
        atcb \<leftarrow> threadGet tcbArch tptr;
        (a, uc') \<leftarrow> return ( runState f $ atcbContext atcb);
        threadSet (\<lambda> tcb. tcb \<lparr> tcbArch := atcb \<lparr> atcbContext := uc' \<rparr> \<rparr>) tptr;
        return a
od)"


end
end
