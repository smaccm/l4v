(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file ArchStateData_H.thy *)
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
	Kernel state and kernel monads, imports everything that SEL4.Model needs.
*)

chapter "Architecture Specific Kernel State and Monads"

theory ArchStateData_H
imports
  Arch_Structs_B
  ArchTypes_H
  ArchStructures_H
begin
context Arch begin global_naming ARM_HYP_H

datatype kernel_state =
    ARMKernelState "asid \<Rightarrow> ((machine_word) option)" "hardware_asid \<Rightarrow> (asid option)" hardware_asid "asid \<Rightarrow> ((hardware_asid * machine_word) option)" "(machine_word * bool) option" nat machine_word "machine_word \<Rightarrow> arm_vspace_region_use"

primrec
  armKSKernelVSpace :: "kernel_state \<Rightarrow> machine_word \<Rightarrow> arm_vspace_region_use"
where
  "armKSKernelVSpace (ARMKernelState v0 v1 v2 v3 v4 v5 v6 v7) = v7"

primrec
  armKSASIDTable :: "kernel_state \<Rightarrow> asid \<Rightarrow> ((machine_word) option)"
where
  "armKSASIDTable (ARMKernelState v0 v1 v2 v3 v4 v5 v6 v7) = v0"

primrec
  armKSGICVCPUNumListRegs :: "kernel_state \<Rightarrow> nat"
where
  "armKSGICVCPUNumListRegs (ARMKernelState v0 v1 v2 v3 v4 v5 v6 v7) = v5"

primrec
  armKSHWASIDTable :: "kernel_state \<Rightarrow> hardware_asid \<Rightarrow> (asid option)"
where
  "armKSHWASIDTable (ARMKernelState v0 v1 v2 v3 v4 v5 v6 v7) = v1"

primrec
  armHSCurVCPU :: "kernel_state \<Rightarrow> (machine_word * bool) option"
where
  "armHSCurVCPU (ARMKernelState v0 v1 v2 v3 v4 v5 v6 v7) = v4"

primrec
  armUSGlobalPD :: "kernel_state \<Rightarrow> machine_word"
where
  "armUSGlobalPD (ARMKernelState v0 v1 v2 v3 v4 v5 v6 v7) = v6"

primrec
  armKSNextASID :: "kernel_state \<Rightarrow> hardware_asid"
where
  "armKSNextASID (ARMKernelState v0 v1 v2 v3 v4 v5 v6 v7) = v2"

primrec
  armKSASIDMap :: "kernel_state \<Rightarrow> asid \<Rightarrow> ((hardware_asid * machine_word) option)"
where
  "armKSASIDMap (ARMKernelState v0 v1 v2 v3 v4 v5 v6 v7) = v3"

primrec
  armKSKernelVSpace_update :: "((machine_word \<Rightarrow> arm_vspace_region_use) \<Rightarrow> (machine_word \<Rightarrow> arm_vspace_region_use)) \<Rightarrow> kernel_state \<Rightarrow> kernel_state"
where
  "armKSKernelVSpace_update f (ARMKernelState v0 v1 v2 v3 v4 v5 v6 v7) = ARMKernelState v0 v1 v2 v3 v4 v5 v6 (f v7)"

primrec
  armKSASIDTable_update :: "((asid \<Rightarrow> ((machine_word) option)) \<Rightarrow> (asid \<Rightarrow> ((machine_word) option))) \<Rightarrow> kernel_state \<Rightarrow> kernel_state"
where
  "armKSASIDTable_update f (ARMKernelState v0 v1 v2 v3 v4 v5 v6 v7) = ARMKernelState (f v0) v1 v2 v3 v4 v5 v6 v7"

primrec
  armKSGICVCPUNumListRegs_update :: "(nat \<Rightarrow> nat) \<Rightarrow> kernel_state \<Rightarrow> kernel_state"
where
  "armKSGICVCPUNumListRegs_update f (ARMKernelState v0 v1 v2 v3 v4 v5 v6 v7) = ARMKernelState v0 v1 v2 v3 v4 (f v5) v6 v7"

primrec
  armKSHWASIDTable_update :: "((hardware_asid \<Rightarrow> (asid option)) \<Rightarrow> (hardware_asid \<Rightarrow> (asid option))) \<Rightarrow> kernel_state \<Rightarrow> kernel_state"
where
  "armKSHWASIDTable_update f (ARMKernelState v0 v1 v2 v3 v4 v5 v6 v7) = ARMKernelState v0 (f v1) v2 v3 v4 v5 v6 v7"

primrec
  armHSCurVCPU_update :: "(((machine_word * bool) option) \<Rightarrow> ((machine_word * bool) option)) \<Rightarrow> kernel_state \<Rightarrow> kernel_state"
where
  "armHSCurVCPU_update f (ARMKernelState v0 v1 v2 v3 v4 v5 v6 v7) = ARMKernelState v0 v1 v2 v3 (f v4) v5 v6 v7"

primrec
  armUSGlobalPD_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> kernel_state \<Rightarrow> kernel_state"
where
  "armUSGlobalPD_update f (ARMKernelState v0 v1 v2 v3 v4 v5 v6 v7) = ARMKernelState v0 v1 v2 v3 v4 v5 (f v6) v7"

primrec
  armKSNextASID_update :: "(hardware_asid \<Rightarrow> hardware_asid) \<Rightarrow> kernel_state \<Rightarrow> kernel_state"
where
  "armKSNextASID_update f (ARMKernelState v0 v1 v2 v3 v4 v5 v6 v7) = ARMKernelState v0 v1 (f v2) v3 v4 v5 v6 v7"

primrec
  armKSASIDMap_update :: "((asid \<Rightarrow> ((hardware_asid * machine_word) option)) \<Rightarrow> (asid \<Rightarrow> ((hardware_asid * machine_word) option))) \<Rightarrow> kernel_state \<Rightarrow> kernel_state"
where
  "armKSASIDMap_update f (ARMKernelState v0 v1 v2 v3 v4 v5 v6 v7) = ARMKernelState v0 v1 v2 (f v3) v4 v5 v6 v7"

abbreviation (input)
  ARMKernelState_trans :: "(asid \<Rightarrow> ((machine_word) option)) \<Rightarrow> (hardware_asid \<Rightarrow> (asid option)) \<Rightarrow> (hardware_asid) \<Rightarrow> (asid \<Rightarrow> ((hardware_asid * machine_word) option)) \<Rightarrow> ((machine_word * bool) option) \<Rightarrow> (nat) \<Rightarrow> (machine_word) \<Rightarrow> (machine_word \<Rightarrow> arm_vspace_region_use) \<Rightarrow> kernel_state" ("ARMKernelState'_ \<lparr> armKSASIDTable= _, armKSHWASIDTable= _, armKSNextASID= _, armKSASIDMap= _, armHSCurVCPU= _, armKSGICVCPUNumListRegs= _, armUSGlobalPD= _, armKSKernelVSpace= _ \<rparr>")
where
  "ARMKernelState_ \<lparr> armKSASIDTable= v0, armKSHWASIDTable= v1, armKSNextASID= v2, armKSASIDMap= v3, armHSCurVCPU= v4, armKSGICVCPUNumListRegs= v5, armUSGlobalPD= v6, armKSKernelVSpace= v7 \<rparr> == ARMKernelState v0 v1 v2 v3 v4 v5 v6 v7"

lemma armKSKernelVSpace_armKSKernelVSpace_update [simp]:
  "armKSKernelVSpace (armKSKernelVSpace_update f v) = f (armKSKernelVSpace v)"
  by (cases v) simp

lemma armKSKernelVSpace_armKSASIDTable_update [simp]:
  "armKSKernelVSpace (armKSASIDTable_update f v) = armKSKernelVSpace v"
  by (cases v) simp

lemma armKSKernelVSpace_armKSGICVCPUNumListRegs_update [simp]:
  "armKSKernelVSpace (armKSGICVCPUNumListRegs_update f v) = armKSKernelVSpace v"
  by (cases v) simp

lemma armKSKernelVSpace_armKSHWASIDTable_update [simp]:
  "armKSKernelVSpace (armKSHWASIDTable_update f v) = armKSKernelVSpace v"
  by (cases v) simp

lemma armKSKernelVSpace_armHSCurVCPU_update [simp]:
  "armKSKernelVSpace (armHSCurVCPU_update f v) = armKSKernelVSpace v"
  by (cases v) simp

lemma armKSKernelVSpace_armUSGlobalPD_update [simp]:
  "armKSKernelVSpace (armUSGlobalPD_update f v) = armKSKernelVSpace v"
  by (cases v) simp

lemma armKSKernelVSpace_armKSNextASID_update [simp]:
  "armKSKernelVSpace (armKSNextASID_update f v) = armKSKernelVSpace v"
  by (cases v) simp

lemma armKSKernelVSpace_armKSASIDMap_update [simp]:
  "armKSKernelVSpace (armKSASIDMap_update f v) = armKSKernelVSpace v"
  by (cases v) simp

lemma armKSASIDTable_armKSKernelVSpace_update [simp]:
  "armKSASIDTable (armKSKernelVSpace_update f v) = armKSASIDTable v"
  by (cases v) simp

lemma armKSASIDTable_armKSASIDTable_update [simp]:
  "armKSASIDTable (armKSASIDTable_update f v) = f (armKSASIDTable v)"
  by (cases v) simp

lemma armKSASIDTable_armKSGICVCPUNumListRegs_update [simp]:
  "armKSASIDTable (armKSGICVCPUNumListRegs_update f v) = armKSASIDTable v"
  by (cases v) simp

lemma armKSASIDTable_armKSHWASIDTable_update [simp]:
  "armKSASIDTable (armKSHWASIDTable_update f v) = armKSASIDTable v"
  by (cases v) simp

lemma armKSASIDTable_armHSCurVCPU_update [simp]:
  "armKSASIDTable (armHSCurVCPU_update f v) = armKSASIDTable v"
  by (cases v) simp

lemma armKSASIDTable_armUSGlobalPD_update [simp]:
  "armKSASIDTable (armUSGlobalPD_update f v) = armKSASIDTable v"
  by (cases v) simp

lemma armKSASIDTable_armKSNextASID_update [simp]:
  "armKSASIDTable (armKSNextASID_update f v) = armKSASIDTable v"
  by (cases v) simp

lemma armKSASIDTable_armKSASIDMap_update [simp]:
  "armKSASIDTable (armKSASIDMap_update f v) = armKSASIDTable v"
  by (cases v) simp

lemma armKSGICVCPUNumListRegs_armKSKernelVSpace_update [simp]:
  "armKSGICVCPUNumListRegs (armKSKernelVSpace_update f v) = armKSGICVCPUNumListRegs v"
  by (cases v) simp

lemma armKSGICVCPUNumListRegs_armKSASIDTable_update [simp]:
  "armKSGICVCPUNumListRegs (armKSASIDTable_update f v) = armKSGICVCPUNumListRegs v"
  by (cases v) simp

lemma armKSGICVCPUNumListRegs_armKSGICVCPUNumListRegs_update [simp]:
  "armKSGICVCPUNumListRegs (armKSGICVCPUNumListRegs_update f v) = f (armKSGICVCPUNumListRegs v)"
  by (cases v) simp

lemma armKSGICVCPUNumListRegs_armKSHWASIDTable_update [simp]:
  "armKSGICVCPUNumListRegs (armKSHWASIDTable_update f v) = armKSGICVCPUNumListRegs v"
  by (cases v) simp

lemma armKSGICVCPUNumListRegs_armHSCurVCPU_update [simp]:
  "armKSGICVCPUNumListRegs (armHSCurVCPU_update f v) = armKSGICVCPUNumListRegs v"
  by (cases v) simp

lemma armKSGICVCPUNumListRegs_armUSGlobalPD_update [simp]:
  "armKSGICVCPUNumListRegs (armUSGlobalPD_update f v) = armKSGICVCPUNumListRegs v"
  by (cases v) simp

lemma armKSGICVCPUNumListRegs_armKSNextASID_update [simp]:
  "armKSGICVCPUNumListRegs (armKSNextASID_update f v) = armKSGICVCPUNumListRegs v"
  by (cases v) simp

lemma armKSGICVCPUNumListRegs_armKSASIDMap_update [simp]:
  "armKSGICVCPUNumListRegs (armKSASIDMap_update f v) = armKSGICVCPUNumListRegs v"
  by (cases v) simp

lemma armKSHWASIDTable_armKSKernelVSpace_update [simp]:
  "armKSHWASIDTable (armKSKernelVSpace_update f v) = armKSHWASIDTable v"
  by (cases v) simp

lemma armKSHWASIDTable_armKSASIDTable_update [simp]:
  "armKSHWASIDTable (armKSASIDTable_update f v) = armKSHWASIDTable v"
  by (cases v) simp

lemma armKSHWASIDTable_armKSGICVCPUNumListRegs_update [simp]:
  "armKSHWASIDTable (armKSGICVCPUNumListRegs_update f v) = armKSHWASIDTable v"
  by (cases v) simp

lemma armKSHWASIDTable_armKSHWASIDTable_update [simp]:
  "armKSHWASIDTable (armKSHWASIDTable_update f v) = f (armKSHWASIDTable v)"
  by (cases v) simp

lemma armKSHWASIDTable_armHSCurVCPU_update [simp]:
  "armKSHWASIDTable (armHSCurVCPU_update f v) = armKSHWASIDTable v"
  by (cases v) simp

lemma armKSHWASIDTable_armUSGlobalPD_update [simp]:
  "armKSHWASIDTable (armUSGlobalPD_update f v) = armKSHWASIDTable v"
  by (cases v) simp

lemma armKSHWASIDTable_armKSNextASID_update [simp]:
  "armKSHWASIDTable (armKSNextASID_update f v) = armKSHWASIDTable v"
  by (cases v) simp

lemma armKSHWASIDTable_armKSASIDMap_update [simp]:
  "armKSHWASIDTable (armKSASIDMap_update f v) = armKSHWASIDTable v"
  by (cases v) simp

lemma armHSCurVCPU_armKSKernelVSpace_update [simp]:
  "armHSCurVCPU (armKSKernelVSpace_update f v) = armHSCurVCPU v"
  by (cases v) simp

lemma armHSCurVCPU_armKSASIDTable_update [simp]:
  "armHSCurVCPU (armKSASIDTable_update f v) = armHSCurVCPU v"
  by (cases v) simp

lemma armHSCurVCPU_armKSGICVCPUNumListRegs_update [simp]:
  "armHSCurVCPU (armKSGICVCPUNumListRegs_update f v) = armHSCurVCPU v"
  by (cases v) simp

lemma armHSCurVCPU_armKSHWASIDTable_update [simp]:
  "armHSCurVCPU (armKSHWASIDTable_update f v) = armHSCurVCPU v"
  by (cases v) simp

lemma armHSCurVCPU_armHSCurVCPU_update [simp]:
  "armHSCurVCPU (armHSCurVCPU_update f v) = f (armHSCurVCPU v)"
  by (cases v) simp

lemma armHSCurVCPU_armUSGlobalPD_update [simp]:
  "armHSCurVCPU (armUSGlobalPD_update f v) = armHSCurVCPU v"
  by (cases v) simp

lemma armHSCurVCPU_armKSNextASID_update [simp]:
  "armHSCurVCPU (armKSNextASID_update f v) = armHSCurVCPU v"
  by (cases v) simp

lemma armHSCurVCPU_armKSASIDMap_update [simp]:
  "armHSCurVCPU (armKSASIDMap_update f v) = armHSCurVCPU v"
  by (cases v) simp

lemma armUSGlobalPD_armKSKernelVSpace_update [simp]:
  "armUSGlobalPD (armKSKernelVSpace_update f v) = armUSGlobalPD v"
  by (cases v) simp

lemma armUSGlobalPD_armKSASIDTable_update [simp]:
  "armUSGlobalPD (armKSASIDTable_update f v) = armUSGlobalPD v"
  by (cases v) simp

lemma armUSGlobalPD_armKSGICVCPUNumListRegs_update [simp]:
  "armUSGlobalPD (armKSGICVCPUNumListRegs_update f v) = armUSGlobalPD v"
  by (cases v) simp

lemma armUSGlobalPD_armKSHWASIDTable_update [simp]:
  "armUSGlobalPD (armKSHWASIDTable_update f v) = armUSGlobalPD v"
  by (cases v) simp

lemma armUSGlobalPD_armHSCurVCPU_update [simp]:
  "armUSGlobalPD (armHSCurVCPU_update f v) = armUSGlobalPD v"
  by (cases v) simp

lemma armUSGlobalPD_armUSGlobalPD_update [simp]:
  "armUSGlobalPD (armUSGlobalPD_update f v) = f (armUSGlobalPD v)"
  by (cases v) simp

lemma armUSGlobalPD_armKSNextASID_update [simp]:
  "armUSGlobalPD (armKSNextASID_update f v) = armUSGlobalPD v"
  by (cases v) simp

lemma armUSGlobalPD_armKSASIDMap_update [simp]:
  "armUSGlobalPD (armKSASIDMap_update f v) = armUSGlobalPD v"
  by (cases v) simp

lemma armKSNextASID_armKSKernelVSpace_update [simp]:
  "armKSNextASID (armKSKernelVSpace_update f v) = armKSNextASID v"
  by (cases v) simp

lemma armKSNextASID_armKSASIDTable_update [simp]:
  "armKSNextASID (armKSASIDTable_update f v) = armKSNextASID v"
  by (cases v) simp

lemma armKSNextASID_armKSGICVCPUNumListRegs_update [simp]:
  "armKSNextASID (armKSGICVCPUNumListRegs_update f v) = armKSNextASID v"
  by (cases v) simp

lemma armKSNextASID_armKSHWASIDTable_update [simp]:
  "armKSNextASID (armKSHWASIDTable_update f v) = armKSNextASID v"
  by (cases v) simp

lemma armKSNextASID_armHSCurVCPU_update [simp]:
  "armKSNextASID (armHSCurVCPU_update f v) = armKSNextASID v"
  by (cases v) simp

lemma armKSNextASID_armUSGlobalPD_update [simp]:
  "armKSNextASID (armUSGlobalPD_update f v) = armKSNextASID v"
  by (cases v) simp

lemma armKSNextASID_armKSNextASID_update [simp]:
  "armKSNextASID (armKSNextASID_update f v) = f (armKSNextASID v)"
  by (cases v) simp

lemma armKSNextASID_armKSASIDMap_update [simp]:
  "armKSNextASID (armKSASIDMap_update f v) = armKSNextASID v"
  by (cases v) simp

lemma armKSASIDMap_armKSKernelVSpace_update [simp]:
  "armKSASIDMap (armKSKernelVSpace_update f v) = armKSASIDMap v"
  by (cases v) simp

lemma armKSASIDMap_armKSASIDTable_update [simp]:
  "armKSASIDMap (armKSASIDTable_update f v) = armKSASIDMap v"
  by (cases v) simp

lemma armKSASIDMap_armKSGICVCPUNumListRegs_update [simp]:
  "armKSASIDMap (armKSGICVCPUNumListRegs_update f v) = armKSASIDMap v"
  by (cases v) simp

lemma armKSASIDMap_armKSHWASIDTable_update [simp]:
  "armKSASIDMap (armKSHWASIDTable_update f v) = armKSASIDMap v"
  by (cases v) simp

lemma armKSASIDMap_armHSCurVCPU_update [simp]:
  "armKSASIDMap (armHSCurVCPU_update f v) = armKSASIDMap v"
  by (cases v) simp

lemma armKSASIDMap_armUSGlobalPD_update [simp]:
  "armKSASIDMap (armUSGlobalPD_update f v) = armKSASIDMap v"
  by (cases v) simp

lemma armKSASIDMap_armKSNextASID_update [simp]:
  "armKSASIDMap (armKSNextASID_update f v) = armKSASIDMap v"
  by (cases v) simp

lemma armKSASIDMap_armKSASIDMap_update [simp]:
  "armKSASIDMap (armKSASIDMap_update f v) = f (armKSASIDMap v)"
  by (cases v) simp

definition
newKernelState :: "paddr \<Rightarrow> (kernel_state * paddr list)"
where
"newKernelState data_start \<equiv>
    let
        alignToBits = (\<lambda>  addr b. (((addr - 1) `~shiftR~` b) + 1) `~shiftL~` b);
        globalsFrame = data_start `~alignToBits~` pageBits;
        globalsFrameTop = globalsFrame + bit pageBits;
        frames = error [];
        state = ARMKernelState_ \<lparr>
            armKSASIDTable= funPartialArray (const Nothing) (0, (1 `~shiftL~` asidHighBits) - 1),
            armKSHWASIDTable= funArray (const Nothing),
            armKSNextASID= minBound,
            armKSASIDMap= funPartialArray (const Nothing) asidRange,
            armHSCurVCPU= Nothing,
            armKSGICVCPUNumListRegs= error [],
            armUSGlobalPD= error [],
            armKSKernelVSpace=
                (\<lambda> vref. if vref < mask 20 then ArmVSpaceKernelWindow
                                            else ArmVSpaceInvalidRegion)
            \<rparr>
    in
                                   (state, frames)"


end

end
