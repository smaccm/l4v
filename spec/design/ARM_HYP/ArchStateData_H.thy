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
    ARMKernelState machine_word "asid \<Rightarrow> ((machine_word) option)" "hardware_asid \<Rightarrow> (asid option)" hardware_asid "asid \<Rightarrow> ((hardware_asid * machine_word) option)" machine_word vcpu "machine_word \<Rightarrow> arm_vspace_region_use"

primrec
  armKSGlobalsFrame :: "kernel_state \<Rightarrow> machine_word"
where
  "armKSGlobalsFrame (ARMKernelState v0 v1 v2 v3 v4 v5 v6 v7) = v0"

primrec
  armKSASIDTable :: "kernel_state \<Rightarrow> asid \<Rightarrow> ((machine_word) option)"
where
  "armKSASIDTable (ARMKernelState v0 v1 v2 v3 v4 v5 v6 v7) = v1"

primrec
  armUSGlobalPT :: "kernel_state \<Rightarrow> machine_word"
where
  "armUSGlobalPT (ARMKernelState v0 v1 v2 v3 v4 v5 v6 v7) = v5"

primrec
  armKSHWASIDTable :: "kernel_state \<Rightarrow> hardware_asid \<Rightarrow> (asid option)"
where
  "armKSHWASIDTable (ARMKernelState v0 v1 v2 v3 v4 v5 v6 v7) = v2"

primrec
  armKSKernelVSpace :: "kernel_state \<Rightarrow> machine_word \<Rightarrow> arm_vspace_region_use"
where
  "armKSKernelVSpace (ARMKernelState v0 v1 v2 v3 v4 v5 v6 v7) = v7"

primrec
  armKSCurVCPU :: "kernel_state \<Rightarrow> vcpu"
where
  "armKSCurVCPU (ARMKernelState v0 v1 v2 v3 v4 v5 v6 v7) = v6"

primrec
  armKSNextASID :: "kernel_state \<Rightarrow> hardware_asid"
where
  "armKSNextASID (ARMKernelState v0 v1 v2 v3 v4 v5 v6 v7) = v3"

primrec
  armKSASIDMap :: "kernel_state \<Rightarrow> asid \<Rightarrow> ((hardware_asid * machine_word) option)"
where
  "armKSASIDMap (ARMKernelState v0 v1 v2 v3 v4 v5 v6 v7) = v4"

primrec
  armKSGlobalsFrame_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> kernel_state \<Rightarrow> kernel_state"
where
  "armKSGlobalsFrame_update f (ARMKernelState v0 v1 v2 v3 v4 v5 v6 v7) = ARMKernelState (f v0) v1 v2 v3 v4 v5 v6 v7"

primrec
  armKSASIDTable_update :: "((asid \<Rightarrow> ((machine_word) option)) \<Rightarrow> (asid \<Rightarrow> ((machine_word) option))) \<Rightarrow> kernel_state \<Rightarrow> kernel_state"
where
  "armKSASIDTable_update f (ARMKernelState v0 v1 v2 v3 v4 v5 v6 v7) = ARMKernelState v0 (f v1) v2 v3 v4 v5 v6 v7"

primrec
  armUSGlobalPT_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> kernel_state \<Rightarrow> kernel_state"
where
  "armUSGlobalPT_update f (ARMKernelState v0 v1 v2 v3 v4 v5 v6 v7) = ARMKernelState v0 v1 v2 v3 v4 (f v5) v6 v7"

primrec
  armKSHWASIDTable_update :: "((hardware_asid \<Rightarrow> (asid option)) \<Rightarrow> (hardware_asid \<Rightarrow> (asid option))) \<Rightarrow> kernel_state \<Rightarrow> kernel_state"
where
  "armKSHWASIDTable_update f (ARMKernelState v0 v1 v2 v3 v4 v5 v6 v7) = ARMKernelState v0 v1 (f v2) v3 v4 v5 v6 v7"

primrec
  armKSKernelVSpace_update :: "((machine_word \<Rightarrow> arm_vspace_region_use) \<Rightarrow> (machine_word \<Rightarrow> arm_vspace_region_use)) \<Rightarrow> kernel_state \<Rightarrow> kernel_state"
where
  "armKSKernelVSpace_update f (ARMKernelState v0 v1 v2 v3 v4 v5 v6 v7) = ARMKernelState v0 v1 v2 v3 v4 v5 v6 (f v7)"

primrec
  armKSCurVCPU_update :: "(vcpu \<Rightarrow> vcpu) \<Rightarrow> kernel_state \<Rightarrow> kernel_state"
where
  "armKSCurVCPU_update f (ARMKernelState v0 v1 v2 v3 v4 v5 v6 v7) = ARMKernelState v0 v1 v2 v3 v4 v5 (f v6) v7"

primrec
  armKSNextASID_update :: "(hardware_asid \<Rightarrow> hardware_asid) \<Rightarrow> kernel_state \<Rightarrow> kernel_state"
where
  "armKSNextASID_update f (ARMKernelState v0 v1 v2 v3 v4 v5 v6 v7) = ARMKernelState v0 v1 v2 (f v3) v4 v5 v6 v7"

primrec
  armKSASIDMap_update :: "((asid \<Rightarrow> ((hardware_asid * machine_word) option)) \<Rightarrow> (asid \<Rightarrow> ((hardware_asid * machine_word) option))) \<Rightarrow> kernel_state \<Rightarrow> kernel_state"
where
  "armKSASIDMap_update f (ARMKernelState v0 v1 v2 v3 v4 v5 v6 v7) = ARMKernelState v0 v1 v2 v3 (f v4) v5 v6 v7"

abbreviation (input)
  ARMKernelState_trans :: "(machine_word) \<Rightarrow> (asid \<Rightarrow> ((machine_word) option)) \<Rightarrow> (hardware_asid \<Rightarrow> (asid option)) \<Rightarrow> (hardware_asid) \<Rightarrow> (asid \<Rightarrow> ((hardware_asid * machine_word) option)) \<Rightarrow> (machine_word) \<Rightarrow> (vcpu) \<Rightarrow> (machine_word \<Rightarrow> arm_vspace_region_use) \<Rightarrow> kernel_state" ("ARMKernelState'_ \<lparr> armKSGlobalsFrame= _, armKSASIDTable= _, armKSHWASIDTable= _, armKSNextASID= _, armKSASIDMap= _, armUSGlobalPT= _, armKSCurVCPU= _, armKSKernelVSpace= _ \<rparr>")
where
  "ARMKernelState_ \<lparr> armKSGlobalsFrame= v0, armKSASIDTable= v1, armKSHWASIDTable= v2, armKSNextASID= v3, armKSASIDMap= v4, armUSGlobalPT= v5, armKSCurVCPU= v6, armKSKernelVSpace= v7 \<rparr> == ARMKernelState v0 v1 v2 v3 v4 v5 v6 v7"

lemma armKSGlobalsFrame_armKSGlobalsFrame_update [simp]:
  "armKSGlobalsFrame (armKSGlobalsFrame_update f v) = f (armKSGlobalsFrame v)"
  by (cases v) simp

lemma armKSGlobalsFrame_armKSASIDTable_update [simp]:
  "armKSGlobalsFrame (armKSASIDTable_update f v) = armKSGlobalsFrame v"
  by (cases v) simp

lemma armKSGlobalsFrame_armUSGlobalPT_update [simp]:
  "armKSGlobalsFrame (armUSGlobalPT_update f v) = armKSGlobalsFrame v"
  by (cases v) simp

lemma armKSGlobalsFrame_armKSHWASIDTable_update [simp]:
  "armKSGlobalsFrame (armKSHWASIDTable_update f v) = armKSGlobalsFrame v"
  by (cases v) simp

lemma armKSGlobalsFrame_armKSKernelVSpace_update [simp]:
  "armKSGlobalsFrame (armKSKernelVSpace_update f v) = armKSGlobalsFrame v"
  by (cases v) simp

lemma armKSGlobalsFrame_armKSCurVCPU_update [simp]:
  "armKSGlobalsFrame (armKSCurVCPU_update f v) = armKSGlobalsFrame v"
  by (cases v) simp

lemma armKSGlobalsFrame_armKSNextASID_update [simp]:
  "armKSGlobalsFrame (armKSNextASID_update f v) = armKSGlobalsFrame v"
  by (cases v) simp

lemma armKSGlobalsFrame_armKSASIDMap_update [simp]:
  "armKSGlobalsFrame (armKSASIDMap_update f v) = armKSGlobalsFrame v"
  by (cases v) simp

lemma armKSASIDTable_armKSGlobalsFrame_update [simp]:
  "armKSASIDTable (armKSGlobalsFrame_update f v) = armKSASIDTable v"
  by (cases v) simp

lemma armKSASIDTable_armKSASIDTable_update [simp]:
  "armKSASIDTable (armKSASIDTable_update f v) = f (armKSASIDTable v)"
  by (cases v) simp

lemma armKSASIDTable_armUSGlobalPT_update [simp]:
  "armKSASIDTable (armUSGlobalPT_update f v) = armKSASIDTable v"
  by (cases v) simp

lemma armKSASIDTable_armKSHWASIDTable_update [simp]:
  "armKSASIDTable (armKSHWASIDTable_update f v) = armKSASIDTable v"
  by (cases v) simp

lemma armKSASIDTable_armKSKernelVSpace_update [simp]:
  "armKSASIDTable (armKSKernelVSpace_update f v) = armKSASIDTable v"
  by (cases v) simp

lemma armKSASIDTable_armKSCurVCPU_update [simp]:
  "armKSASIDTable (armKSCurVCPU_update f v) = armKSASIDTable v"
  by (cases v) simp

lemma armKSASIDTable_armKSNextASID_update [simp]:
  "armKSASIDTable (armKSNextASID_update f v) = armKSASIDTable v"
  by (cases v) simp

lemma armKSASIDTable_armKSASIDMap_update [simp]:
  "armKSASIDTable (armKSASIDMap_update f v) = armKSASIDTable v"
  by (cases v) simp

lemma armUSGlobalPT_armKSGlobalsFrame_update [simp]:
  "armUSGlobalPT (armKSGlobalsFrame_update f v) = armUSGlobalPT v"
  by (cases v) simp

lemma armUSGlobalPT_armKSASIDTable_update [simp]:
  "armUSGlobalPT (armKSASIDTable_update f v) = armUSGlobalPT v"
  by (cases v) simp

lemma armUSGlobalPT_armUSGlobalPT_update [simp]:
  "armUSGlobalPT (armUSGlobalPT_update f v) = f (armUSGlobalPT v)"
  by (cases v) simp

lemma armUSGlobalPT_armKSHWASIDTable_update [simp]:
  "armUSGlobalPT (armKSHWASIDTable_update f v) = armUSGlobalPT v"
  by (cases v) simp

lemma armUSGlobalPT_armKSKernelVSpace_update [simp]:
  "armUSGlobalPT (armKSKernelVSpace_update f v) = armUSGlobalPT v"
  by (cases v) simp

lemma armUSGlobalPT_armKSCurVCPU_update [simp]:
  "armUSGlobalPT (armKSCurVCPU_update f v) = armUSGlobalPT v"
  by (cases v) simp

lemma armUSGlobalPT_armKSNextASID_update [simp]:
  "armUSGlobalPT (armKSNextASID_update f v) = armUSGlobalPT v"
  by (cases v) simp

lemma armUSGlobalPT_armKSASIDMap_update [simp]:
  "armUSGlobalPT (armKSASIDMap_update f v) = armUSGlobalPT v"
  by (cases v) simp

lemma armKSHWASIDTable_armKSGlobalsFrame_update [simp]:
  "armKSHWASIDTable (armKSGlobalsFrame_update f v) = armKSHWASIDTable v"
  by (cases v) simp

lemma armKSHWASIDTable_armKSASIDTable_update [simp]:
  "armKSHWASIDTable (armKSASIDTable_update f v) = armKSHWASIDTable v"
  by (cases v) simp

lemma armKSHWASIDTable_armUSGlobalPT_update [simp]:
  "armKSHWASIDTable (armUSGlobalPT_update f v) = armKSHWASIDTable v"
  by (cases v) simp

lemma armKSHWASIDTable_armKSHWASIDTable_update [simp]:
  "armKSHWASIDTable (armKSHWASIDTable_update f v) = f (armKSHWASIDTable v)"
  by (cases v) simp

lemma armKSHWASIDTable_armKSKernelVSpace_update [simp]:
  "armKSHWASIDTable (armKSKernelVSpace_update f v) = armKSHWASIDTable v"
  by (cases v) simp

lemma armKSHWASIDTable_armKSCurVCPU_update [simp]:
  "armKSHWASIDTable (armKSCurVCPU_update f v) = armKSHWASIDTable v"
  by (cases v) simp

lemma armKSHWASIDTable_armKSNextASID_update [simp]:
  "armKSHWASIDTable (armKSNextASID_update f v) = armKSHWASIDTable v"
  by (cases v) simp

lemma armKSHWASIDTable_armKSASIDMap_update [simp]:
  "armKSHWASIDTable (armKSASIDMap_update f v) = armKSHWASIDTable v"
  by (cases v) simp

lemma armKSKernelVSpace_armKSGlobalsFrame_update [simp]:
  "armKSKernelVSpace (armKSGlobalsFrame_update f v) = armKSKernelVSpace v"
  by (cases v) simp

lemma armKSKernelVSpace_armKSASIDTable_update [simp]:
  "armKSKernelVSpace (armKSASIDTable_update f v) = armKSKernelVSpace v"
  by (cases v) simp

lemma armKSKernelVSpace_armUSGlobalPT_update [simp]:
  "armKSKernelVSpace (armUSGlobalPT_update f v) = armKSKernelVSpace v"
  by (cases v) simp

lemma armKSKernelVSpace_armKSHWASIDTable_update [simp]:
  "armKSKernelVSpace (armKSHWASIDTable_update f v) = armKSKernelVSpace v"
  by (cases v) simp

lemma armKSKernelVSpace_armKSKernelVSpace_update [simp]:
  "armKSKernelVSpace (armKSKernelVSpace_update f v) = f (armKSKernelVSpace v)"
  by (cases v) simp

lemma armKSKernelVSpace_armKSCurVCPU_update [simp]:
  "armKSKernelVSpace (armKSCurVCPU_update f v) = armKSKernelVSpace v"
  by (cases v) simp

lemma armKSKernelVSpace_armKSNextASID_update [simp]:
  "armKSKernelVSpace (armKSNextASID_update f v) = armKSKernelVSpace v"
  by (cases v) simp

lemma armKSKernelVSpace_armKSASIDMap_update [simp]:
  "armKSKernelVSpace (armKSASIDMap_update f v) = armKSKernelVSpace v"
  by (cases v) simp

lemma armKSCurVCPU_armKSGlobalsFrame_update [simp]:
  "armKSCurVCPU (armKSGlobalsFrame_update f v) = armKSCurVCPU v"
  by (cases v) simp

lemma armKSCurVCPU_armKSASIDTable_update [simp]:
  "armKSCurVCPU (armKSASIDTable_update f v) = armKSCurVCPU v"
  by (cases v) simp

lemma armKSCurVCPU_armUSGlobalPT_update [simp]:
  "armKSCurVCPU (armUSGlobalPT_update f v) = armKSCurVCPU v"
  by (cases v) simp

lemma armKSCurVCPU_armKSHWASIDTable_update [simp]:
  "armKSCurVCPU (armKSHWASIDTable_update f v) = armKSCurVCPU v"
  by (cases v) simp

lemma armKSCurVCPU_armKSKernelVSpace_update [simp]:
  "armKSCurVCPU (armKSKernelVSpace_update f v) = armKSCurVCPU v"
  by (cases v) simp

lemma armKSCurVCPU_armKSCurVCPU_update [simp]:
  "armKSCurVCPU (armKSCurVCPU_update f v) = f (armKSCurVCPU v)"
  by (cases v) simp

lemma armKSCurVCPU_armKSNextASID_update [simp]:
  "armKSCurVCPU (armKSNextASID_update f v) = armKSCurVCPU v"
  by (cases v) simp

lemma armKSCurVCPU_armKSASIDMap_update [simp]:
  "armKSCurVCPU (armKSASIDMap_update f v) = armKSCurVCPU v"
  by (cases v) simp

lemma armKSNextASID_armKSGlobalsFrame_update [simp]:
  "armKSNextASID (armKSGlobalsFrame_update f v) = armKSNextASID v"
  by (cases v) simp

lemma armKSNextASID_armKSASIDTable_update [simp]:
  "armKSNextASID (armKSASIDTable_update f v) = armKSNextASID v"
  by (cases v) simp

lemma armKSNextASID_armUSGlobalPT_update [simp]:
  "armKSNextASID (armUSGlobalPT_update f v) = armKSNextASID v"
  by (cases v) simp

lemma armKSNextASID_armKSHWASIDTable_update [simp]:
  "armKSNextASID (armKSHWASIDTable_update f v) = armKSNextASID v"
  by (cases v) simp

lemma armKSNextASID_armKSKernelVSpace_update [simp]:
  "armKSNextASID (armKSKernelVSpace_update f v) = armKSNextASID v"
  by (cases v) simp

lemma armKSNextASID_armKSCurVCPU_update [simp]:
  "armKSNextASID (armKSCurVCPU_update f v) = armKSNextASID v"
  by (cases v) simp

lemma armKSNextASID_armKSNextASID_update [simp]:
  "armKSNextASID (armKSNextASID_update f v) = f (armKSNextASID v)"
  by (cases v) simp

lemma armKSNextASID_armKSASIDMap_update [simp]:
  "armKSNextASID (armKSASIDMap_update f v) = armKSNextASID v"
  by (cases v) simp

lemma armKSASIDMap_armKSGlobalsFrame_update [simp]:
  "armKSASIDMap (armKSGlobalsFrame_update f v) = armKSASIDMap v"
  by (cases v) simp

lemma armKSASIDMap_armKSASIDTable_update [simp]:
  "armKSASIDMap (armKSASIDTable_update f v) = armKSASIDMap v"
  by (cases v) simp

lemma armKSASIDMap_armUSGlobalPT_update [simp]:
  "armKSASIDMap (armUSGlobalPT_update f v) = armKSASIDMap v"
  by (cases v) simp

lemma armKSASIDMap_armKSHWASIDTable_update [simp]:
  "armKSASIDMap (armKSHWASIDTable_update f v) = armKSASIDMap v"
  by (cases v) simp

lemma armKSASIDMap_armKSKernelVSpace_update [simp]:
  "armKSASIDMap (armKSKernelVSpace_update f v) = armKSASIDMap v"
  by (cases v) simp

lemma armKSASIDMap_armKSCurVCPU_update [simp]:
  "armKSASIDMap (armKSCurVCPU_update f v) = armKSASIDMap v"
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
            armKSGlobalsFrame= ptrFromPAddr globalsFrame,
            armKSASIDTable= funPartialArray (const Nothing) (0, (1 `~shiftL~` asidHighBits) - 1),
            armKSHWASIDTable= funArray (const Nothing),
            armKSNextASID= minBound,
            armKSASIDMap= funPartialArray (const Nothing) asidRange,
            armUSGlobalPT= error [],
            armKSCurVCPU= error [],
            armKSKernelVSpace=
                (\<lambda> vref. if vref < mask 20 then ArmVSpaceKernelWindow
                                            else ArmVSpaceInvalidRegion)
            \<rparr>
    in
                                   (state, frames)"


end

end
