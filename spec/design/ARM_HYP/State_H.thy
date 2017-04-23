(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file State_H.thy *)
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
	Machine and kernel state.
*)

chapter "Machine State"

theory State_H
imports
  "../../../lib/HaskellLib_H"
  RegisterSet_H
  "../../machine/ARM_HYP/MachineOps"
begin
context Arch begin global_naming ARM_HYP_H

definition
  Word :: "machine_word \<Rightarrow> machine_word"
where
  Word_def[simp]:
 "Word \<equiv> id"

type_synonym register = "ARM_HYP.register"

definition
  Register :: "register \<Rightarrow> register"
where Register_def[simp]:
 "Register \<equiv> id"

type_synonym vptr = "machine_word"

definition
  VPtr :: "vptr \<Rightarrow> vptr"
where VPtr_def[simp]:
 "VPtr \<equiv> id"

definition
  fromVPtr :: "vptr \<Rightarrow> vptr"
where
  fromVPtr_def[simp]:
 "fromVPtr \<equiv> id"

definition  fromVPtr_update :: "(vptr \<Rightarrow> vptr) \<Rightarrow> vptr \<Rightarrow> vptr"
where
  fromVPtr_update_def[simp]:
 "fromVPtr_update f y \<equiv> f y"

abbreviation (input)
  VPtr_trans :: "(machine_word) \<Rightarrow> vptr" ("VPtr'_ \<lparr> fromVPtr= _ \<rparr>")
where
  "VPtr_ \<lparr> fromVPtr= v0 \<rparr> == VPtr v0"

definition
msgInfoRegister :: "register"
where
"msgInfoRegister \<equiv> Register ARM_HYP.msgInfoRegister"

definition
msgRegisters :: "register list"
where
"msgRegisters \<equiv> map Register ARM_HYP.msgRegisters"

definition
capRegister :: "register"
where
"capRegister \<equiv> Register ARM_HYP.capRegister"

definition
badgeRegister :: "register"
where
"badgeRegister \<equiv> Register ARM_HYP.badgeRegister"

definition
frameRegisters :: "register list"
where
"frameRegisters \<equiv> map Register ARM_HYP.frameRegisters"

definition
gpRegisters :: "register list"
where
"gpRegisters \<equiv> map Register ARM_HYP.gpRegisters"

definition
exceptionMessage :: "register list"
where
"exceptionMessage \<equiv> map Register ARM_HYP.exceptionMessage"

definition
syscallMessage :: "register list"
where
"syscallMessage \<equiv> map Register ARM_HYP.syscallMessage"

definition
tpidrurwRegister :: "register"
where
"tpidrurwRegister \<equiv> Register ARM_HYP.tpidrurwRegister"


definition
  PPtr :: "machine_word \<Rightarrow> machine_word"
where
  PPtr_def[simp]:
 "PPtr \<equiv> id"

definition
  fromPPtr :: "machine_word \<Rightarrow> machine_word"
where
  fromPPtr_def[simp]:
 "fromPPtr \<equiv> id"

definition
  nullPointer :: machine_word
where
 "nullPointer \<equiv> 0"

end
end