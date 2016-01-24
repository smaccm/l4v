(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "ARM Machine Types"

theory MachineTypes
imports
  "../../../lib/Enumeration"
  "../../../lib/WordSetup"
  "../../../lib/wp/NonDetMonad"
  Platform
begin

(* !!! Generated File !!! Skeleton in spec/design/m-skel/ARM/MachineTypes.thy *)

text {*
  An implementation of the machine's types, defining register set 
  and some observable machine state.
*}

section "Types"

datatype register =
    R0
  | R1
  | R2
  | R3
  | R4
  | R5
  | R6
  | R7
  | R8
  | R9
  | SL
  | FP
  | IP
  | SP
  | LR
  | LR_svc
  | FaultInstruction
  | CPSR

type_synonym machine_word = "word32"

consts
initContext :: "(register * machine_word) list"

consts
sanitiseRegister :: "register \<Rightarrow> machine_word \<Rightarrow> machine_word"

(*<*)
(* register instance proofs *)
(*<*)
instantiation register :: enum begin
definition
  enum_register: "enum_class.enum \<equiv> 
    [ 
      R0,
      R1,
      R2,
      R3,
      R4,
      R5,
      R6,
      R7,
      R8,
      R9,
      SL,
      FP,
      IP,
      SP,
      LR,
      LR_svc,
      FaultInstruction,
      CPSR
    ]"


definition
  "enum_class.enum_all (P :: register \<Rightarrow> bool) \<longleftrightarrow> Ball UNIV P"

definition
  "enum_class.enum_ex (P :: register \<Rightarrow> bool) \<longleftrightarrow> Bex UNIV P"

  instance
  apply intro_classes
   apply (safe, simp)
   apply (case_tac x)
  apply (simp_all add: enum_register enum_all_register_def enum_ex_register_def)
  by fast+
end

instantiation register :: enum_alt
begin
definition
  enum_alt_register: "enum_alt \<equiv> 
    alt_from_ord (enum :: register list)"
instance ..
end

instantiation register :: enumeration_both
begin
instance by (intro_classes, simp add: enum_alt_register)
end

(*>*)

(*>*)
definition
"capRegister \<equiv> R0"

definition
"msgInfoRegister \<equiv> R1"

definition
"msgRegisters \<equiv> [R2  .e.  R5]"

definition
"badgeRegister \<equiv> R0"

definition
"frameRegisters \<equiv> FaultInstruction # SP # CPSR # [R0, R1] @ [R8  .e.  IP]"

definition
"gpRegisters \<equiv> [R2, R3, R4, R5, R6, R7, LR]"

definition
"exceptionMessage \<equiv> [FaultInstruction, SP, CPSR]"

definition
"syscallMessage \<equiv> [R0  .e.  R7] @ [FaultInstruction, SP, LR, CPSR]"

defs initContext_def:
"initContext\<equiv> [(CPSR,0x150)]"

defs sanitiseRegister_def:
"sanitiseRegister x0 v\<equiv> (case x0 of
    CPSR \<Rightarrow>    (v && 0xf8000000) || 0x150
  | _ \<Rightarrow>    v
  )"


section "Machine State"

text {*
  Most of the machine state is left underspecified at this level.
  We know it exists, we will declare some interface functions, but
  at this level we do not have access to how this state is transformed
  or what effect it has on the machine.
*}
typedecl machine_state_rest

text {*
  The exclusive monitors state is observable in user mode.
  The type for this is the type used in the Cambridge HOL4 ARM model.
*}
type_synonym exclusive_monitors = "(word32 \<Rightarrow> bool) list \<times> (word32 \<times> nat \<Rightarrow> bool)"

text {* 
  The full machine state is the state observable by the kernel plus
  the underspecified rest above. The observable parts are the 
  interrupt controller (which IRQs are masked) and the memory of the
  machine. The latter is shadow state: kernel memory is kept in a
  separate, more abstract datatype; user memory is reflected down
  to the underlying memory of the machine.
*} 
record
  machine_state =
  irq_masks :: "irq \<Rightarrow> bool"
  irq_state :: nat
  underlying_memory :: "word32 \<Rightarrow> word8"
  exclusive_state :: exclusive_monitors
  machine_state_rest :: machine_state_rest  

consts irq_oracle :: "nat \<Rightarrow> word8"

text {*
  The machine monad is used for operations on the state defined above.
*}
type_synonym 'a machine_monad = "(machine_state, 'a) nondet_monad"

translations
  (type) "'c machine_monad" <= (type) "(machine_state, 'c) nondet_monad"

text {*
  After kernel initialisation all IRQs are masked.
*}
definition
  "init_irq_masks \<equiv> \<lambda>_. True"

text {*
  The initial contents of the user-visible memory is 0.
*}
definition
  init_underlying_memory :: "word32 \<Rightarrow> word8"
  where
  "init_underlying_memory \<equiv> \<lambda>_. 0"

text {*
  The initial exclusive state is the same constant
  that clearExMonitor defaults it to.
*}
consts default_exclusive_state :: exclusive_monitors

text {*
  We leave open the underspecified rest of the machine state in
  the initial state.
*}
definition
  init_machine_state :: machine_state where
 "init_machine_state \<equiv> \<lparr> irq_masks = init_irq_masks, 
                         irq_state = 0,
                         underlying_memory = init_underlying_memory, 
                         exclusive_state = default_exclusive_state,
                         machine_state_rest = undefined \<rparr>"


(* Machine/Hardware/ARM.lhs - hardware_asid, vmfault_type and vmpage_size *)
type_synonym hardware_asid = "word8"

definition
  HardwareASID :: "hardware_asid \<Rightarrow> hardware_asid"
where HardwareASID_def[simp]:
 "HardwareASID \<equiv> id"

definition
  fromHWASID :: "hardware_asid \<Rightarrow> hardware_asid"
where
  fromHWASID_def[simp]:
 "fromHWASID \<equiv> id"

definition  fromHWASID_update :: "(hardware_asid \<Rightarrow> hardware_asid) \<Rightarrow> hardware_asid \<Rightarrow> hardware_asid"
where
  fromHWASID_update_def[simp]:
 "fromHWASID_update f y \<equiv> f y"

abbreviation (input)
  HardwareASID_trans :: "(word8) \<Rightarrow> hardware_asid" ("HardwareASID'_ \<lparr> fromHWASID= _ \<rparr>")
where
  "HardwareASID_ \<lparr> fromHWASID= v0 \<rparr> == HardwareASID v0"

datatype pt_level =
    PT_L1
  | PT_L2
  | PT_L3

datatype vmpage_size =
    ARM_1G_Block
  | ARM_2M_Block
  | ARM_4K_Page

datatype vmfault_type =
    ARMDataAbort
  | ARMPrefetchAbort

definition
pageBits :: "nat"
where
"pageBits \<equiv> 12"

definition
pageBitsForSize :: "vmpage_size \<Rightarrow> nat"
where
"pageBitsForSize x0\<equiv> (let sz = x0 in
  case sz of
  ARM_1G_Block =>   30
  | ARM_2M_Block =>   21
  | ARM_4K_Page =>   12
  )"

definition
ptBits :: "nat"
where
"ptBits \<equiv> 12"

(* pt_level instance proofs *)
(*<*)
instantiation pt_level :: enum begin
definition
  enum_pt_level: "enum_class.enum \<equiv> 
    [ 
      PT_L1,
      PT_L2,
      PT_L3
    ]"


definition
  "enum_class.enum_all (P :: pt_level \<Rightarrow> bool) \<longleftrightarrow> Ball UNIV P"

definition
  "enum_class.enum_ex (P :: pt_level \<Rightarrow> bool) \<longleftrightarrow> Bex UNIV P"

  instance
  apply intro_classes
   apply (safe, simp)
   apply (case_tac x)
  apply (simp_all add: enum_pt_level enum_all_pt_level_def enum_ex_pt_level_def)
  by fast+
end

instantiation pt_level :: enum_alt
begin
definition
  enum_alt_pt_level: "enum_alt \<equiv> 
    alt_from_ord (enum :: pt_level list)"
instance ..
end

instantiation pt_level :: enumeration_both
begin
instance by (intro_classes, simp add: enum_alt_pt_level)
end

(*>*)

(* vmpage_size instance proofs *)
(*<*)
instantiation vmpage_size :: enum begin
definition
  enum_vmpage_size: "enum_class.enum \<equiv> 
    [ 
      ARM_1G_Block,
      ARM_2M_Block,
      ARM_4K_Page
    ]"


definition
  "enum_class.enum_all (P :: vmpage_size \<Rightarrow> bool) \<longleftrightarrow> Ball UNIV P"

definition
  "enum_class.enum_ex (P :: vmpage_size \<Rightarrow> bool) \<longleftrightarrow> Bex UNIV P"

  instance
  apply intro_classes
   apply (safe, simp)
   apply (case_tac x)
  apply (simp_all add: enum_vmpage_size enum_all_vmpage_size_def enum_ex_vmpage_size_def)
  by fast+
end

instantiation vmpage_size :: enum_alt
begin
definition
  enum_alt_vmpage_size: "enum_alt \<equiv> 
    alt_from_ord (enum :: vmpage_size list)"
instance ..
end

instantiation vmpage_size :: enumeration_both
begin
instance by (intro_classes, simp add: enum_alt_vmpage_size)
end

(*>*)


end
