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
context Arch begin global_naming ARM_H

datatype kernel_state =
    ARMKernelState machine_word "asid \<Rightarrow> ((machine_word) option)" "hardware_asid \<Rightarrow> (asid option)" hardware_asid "asid \<Rightarrow> ((hardware_asid * machine_word) option)" machine_word "(machine_word * bool) option" nat "machine_word \<Rightarrow> arm_vspace_region_use"

primrec
  armKSGlobalsFrame :: "kernel_state \<Rightarrow> machine_word"
where
  "armKSGlobalsFrame (ARMKernelState v0 v1 v2 v3 v4 v5 v6 v7) = v0"

primrec
  armKSASIDTable :: "kernel_state \<Rightarrow> asid \<Rightarrow> ((machine_word) option)"
where
  "armKSASIDTable (ARMKernelState v0 v1 v2 v3 v4 v5 v6 v7) = v1"

primrec
  armKSGlobalPD :: "kernel_state \<Rightarrow> machine_word"
where
  "armKSGlobalPD (ARMKernelState v0 v1 v2 v3 v4 v5 v6 v7) = v5"

primrec
  armKSHWASIDTable :: "kernel_state \<Rightarrow> hardware_asid \<Rightarrow> (asid option)"
where
  "armKSHWASIDTable (ARMKernelState v0 v1 v2 v3 v4 v5 v6 v7) = v2"

primrec
  armKSKernelVSpace :: "kernel_state \<Rightarrow> machine_word \<Rightarrow> arm_vspace_region_use"
where
  "armKSKernelVSpace (ARMKernelState v0 v1 v2 v3 v4 v5 v6 v7) = v7"

primrec
  armHSCurVCPU :: "kernel_state \<Rightarrow> (machine_word * bool) option"
where
  "armHSCurVCPU (ARMKernelState v0 v1 v2 v3 v4 v5 v6 v7 v8) = v6"

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
  armKSGlobalPD_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> kernel_state \<Rightarrow> kernel_state"
where
  "armKSGlobalPD_update f (ARMKernelState v0 v1 v2 v3 v4 v5 v6 v7) = ARMKernelState v0 v1 v2 v3 v4 (f v5) v6 v7"

primrec
  armKSHWASIDTable_update :: "((hardware_asid \<Rightarrow> (asid option)) \<Rightarrow> (hardware_asid \<Rightarrow> (asid option))) \<Rightarrow> kernel_state \<Rightarrow> kernel_state"
where
  "armKSHWASIDTable_update f (ARMKernelState v0 v1 v2 v3 v4 v5 v6 v7) = ARMKernelState v0 v1 (f v2) v3 v4 v5 v6 v7"

primrec
  armKSKernelVSpace_update :: "((machine_word \<Rightarrow> arm_vspace_region_use) \<Rightarrow> (machine_word \<Rightarrow> arm_vspace_region_use)) \<Rightarrow> kernel_state \<Rightarrow> kernel_state"
where
  "armKSKernelVSpace_update f (ARMKernelState v0 v1 v2 v3 v4 v5 v6 v7) = ARMKernelState v0 v1 v2 v3 v4 v5 v6 (f v7)"

primrec
  armHSCurVCPU_update :: "(((machine_word * bool) option) \<Rightarrow> ((machine_word * bool) option)) \<Rightarrow> kernel_state \<Rightarrow> kernel_state"
where
  "armHSCurVCPU_update f (ARMKernelState v0 v1 v2 v3 v4 v5 v6 v7 v8) = ARMKernelState v0 v1 v2 v3 v4 v5 (f v6) v7 v8"

primrec
  armKSNextASID_update :: "(hardware_asid \<Rightarrow> hardware_asid) \<Rightarrow> kernel_state \<Rightarrow> kernel_state"
where
  "armKSNextASID_update f (ARMKernelState v0 v1 v2 v3 v4 v5 v6 v7) = ARMKernelState v0 v1 v2 (f v3) v4 v5 v6 v7"

primrec
  armKSASIDMap_update :: "((asid \<Rightarrow> ((hardware_asid * machine_word) option)) \<Rightarrow> (asid \<Rightarrow> ((hardware_asid * machine_word) option))) \<Rightarrow> kernel_state \<Rightarrow> kernel_state"
where
  "armKSASIDMap_update f (ARMKernelState v0 v1 v2 v3 v4 v5 v6 v7) = ARMKernelState v0 v1 v2 v3 (f v4) v5 v6 v7"

abbreviation (input)
  ARMKernelState_trans :: "(machine_word) \<Rightarrow> (asid \<Rightarrow> ((machine_word) option)) \<Rightarrow> (hardware_asid \<Rightarrow> (asid option)) \<Rightarrow> (hardware_asid) \<Rightarrow> (asid \<Rightarrow> ((hardware_asid * machine_word) option)) \<Rightarrow> (machine_word) \<Rightarrow> ((machine_word * bool) option) \<Rightarrow> (nat) \<Rightarrow> (machine_word \<Rightarrow> arm_vspace_region_use) \<Rightarrow> kernel_state" ("ARMKernelState'_ \<lparr> armKSGlobalsFrame= _, armKSASIDTable= _, armKSHWASIDTable= _, armKSNextASID= _, armKSASIDMap= _, armUSGlobalPT= _, armHSCurVCPU= _, armKSGICVCPUNumListRegs= _, armKSKernelVSpace= _ \<rparr>")
where
  "ARMKernelState_ \<lparr> armKSGlobalsFrame= v0, armKSASIDTable= v1, armKSHWASIDTable= v2, armKSNextASID= v3, armKSASIDMap= v4, armUSGlobalPT= v5, armHSCurVCPU= v6, armKSGICVCPUNumListRegs= v7, armKSKernelVSpace= v8 \<rparr> == ARMKernelState v0 v1 v2 v3 v4 v5 v6 v7 v8"

lemma armKSGlobalsFrame_armKSGlobalsFrame_update [simp]:
  "armKSGlobalsFrame (armKSGlobalsFrame_update f v) = f (armKSGlobalsFrame v)"
  by (cases v) simp

lemma armKSGlobalsFrame_armKSASIDTable_update [simp]:
  "armKSGlobalsFrame (armKSASIDTable_update f v) = armKSGlobalsFrame v"
  by (cases v) simp

lemma armKSGlobalsFrame_armKSGlobalPD_update [simp]:
  "armKSGlobalsFrame (armKSGlobalPD_update f v) = armKSGlobalsFrame v"
  by (cases v) simp

lemma armKSGlobalsFrame_armKSHWASIDTable_update [simp]:
  "armKSGlobalsFrame (armKSHWASIDTable_update f v) = armKSGlobalsFrame v"
  by (cases v) simp

lemma armKSGlobalsFrame_armKSKernelVSpace_update [simp]:
  "armKSGlobalsFrame (armKSKernelVSpace_update f v) = armKSGlobalsFrame v"
  by (cases v) simp

lemma armKSGlobalsFrame_armHSCurVCPU_update [simp]:
  "armKSGlobalsFrame (armHSCurVCPU_update f v) = armKSGlobalsFrame v"
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

lemma armKSASIDTable_armKSGlobalPD_update [simp]:
  "armKSASIDTable (armKSGlobalPD_update f v) = armKSASIDTable v"
  by (cases v) simp

lemma armKSASIDTable_armKSHWASIDTable_update [simp]:
  "armKSASIDTable (armKSHWASIDTable_update f v) = armKSASIDTable v"
  by (cases v) simp

lemma armKSASIDTable_armKSKernelVSpace_update [simp]:
  "armKSASIDTable (armKSKernelVSpace_update f v) = armKSASIDTable v"
  by (cases v) simp

lemma armKSASIDTable_armHSCurVCPU_update [simp]:
  "armKSASIDTable (armHSCurVCPU_update f v) = armKSASIDTable v"
  by (cases v) simp

lemma armKSASIDTable_armKSNextASID_update [simp]:
  "armKSASIDTable (armKSNextASID_update f v) = armKSASIDTable v"
  by (cases v) simp

lemma armKSASIDTable_armKSASIDMap_update [simp]:
  "armKSASIDTable (armKSASIDMap_update f v) = armKSASIDTable v"
  by (cases v) simp

lemma armKSGlobalPD_armKSGlobalsFrame_update [simp]:
  "armKSGlobalPD (armKSGlobalsFrame_update f v) = armKSGlobalPD v"
  by (cases v) simp

lemma armUSGlobalPT_armHSCurVCPU_update [simp]:
  "armUSGlobalPT (armHSCurVCPU_update f v) = armUSGlobalPT v"
  by (cases v) simp

lemma armKSGlobalPD_armKSGlobalPD_update [simp]:
  "armKSGlobalPD (armKSGlobalPD_update f v) = f (armKSGlobalPD v)"
  by (cases v) simp

lemma armKSGlobalPD_armKSHWASIDTable_update [simp]:
  "armKSGlobalPD (armKSHWASIDTable_update f v) = armKSGlobalPD v"
  by (cases v) simp

lemma armKSGlobalPD_armKSKernelVSpace_update [simp]:
  "armKSGlobalPD (armKSKernelVSpace_update f v) = armKSGlobalPD v"
  by (cases v) simp

lemma armKSGlobalPD_armKSGlobalPTs_update [simp]:
  "armKSGlobalPD (armKSGlobalPTs_update f v) = armKSGlobalPD v"
  by (cases v) simp

lemma armKSGlobalPD_armKSNextASID_update [simp]:
  "armKSGlobalPD (armKSNextASID_update f v) = armKSGlobalPD v"
  by (cases v) simp

lemma armKSGICVCPUNumListRegs_armKSGICVCPUNumListRegs_update [simp]:
  "armKSGICVCPUNumListRegs (armKSGICVCPUNumListRegs_update f v) = f (armKSGICVCPUNumListRegs v)"
  by (cases v) simp

lemma armKSGICVCPUNumListRegs_armKSHWASIDTable_update [simp]:
  "armKSGICVCPUNumListRegs (armKSHWASIDTable_update f v) = armKSGICVCPUNumListRegs v"
  by (cases v) simp

lemma armKSGICVCPUNumListRegs_armKSKernelVSpace_update [simp]:
  "armKSGICVCPUNumListRegs (armKSKernelVSpace_update f v) = armKSGICVCPUNumListRegs v"
  by (cases v) simp

lemma armKSGICVCPUNumListRegs_armHSCurVCPU_update [simp]:
  "armKSGICVCPUNumListRegs (armHSCurVCPU_update f v) = armKSGICVCPUNumListRegs v"
  by (cases v) simp

lemma armKSGICVCPUNumListRegs_armKSNextASID_update [simp]:
  "armKSGICVCPUNumListRegs (armKSNextASID_update f v) = armKSGICVCPUNumListRegs v"
  by (cases v) simp

lemma armKSGICVCPUNumListRegs_armKSASIDMap_update [simp]:
  "armKSGICVCPUNumListRegs (armKSASIDMap_update f v) = armKSGICVCPUNumListRegs v"
  by (cases v) simp

lemma armKSHWASIDTable_armKSGlobalsFrame_update [simp]:
  "armKSHWASIDTable (armKSGlobalsFrame_update f v) = armKSHWASIDTable v"
  by (cases v) simp

lemma armKSHWASIDTable_armKSASIDTable_update [simp]:
  "armKSHWASIDTable (armKSASIDTable_update f v) = armKSHWASIDTable v"
  by (cases v) simp

lemma armKSHWASIDTable_armKSGlobalPD_update [simp]:
  "armKSHWASIDTable (armKSGlobalPD_update f v) = armKSHWASIDTable v"
  by (cases v) simp

lemma armKSHWASIDTable_armKSHWASIDTable_update [simp]:
  "armKSHWASIDTable (armKSHWASIDTable_update f v) = f (armKSHWASIDTable v)"
  by (cases v) simp

lemma armKSHWASIDTable_armKSKernelVSpace_update [simp]:
  "armKSHWASIDTable (armKSKernelVSpace_update f v) = armKSHWASIDTable v"
  by (cases v) simp

lemma armKSHWASIDTable_armHSCurVCPU_update [simp]:
  "armKSHWASIDTable (armHSCurVCPU_update f v) = armKSHWASIDTable v"
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

lemma armKSKernelVSpace_armKSGlobalPD_update [simp]:
  "armKSKernelVSpace (armKSGlobalPD_update f v) = armKSKernelVSpace v"
  by (cases v) simp

lemma armKSKernelVSpace_armKSHWASIDTable_update [simp]:
  "armKSKernelVSpace (armKSHWASIDTable_update f v) = armKSKernelVSpace v"
  by (cases v) simp

lemma armKSKernelVSpace_armKSKernelVSpace_update [simp]:
  "armKSKernelVSpace (armKSKernelVSpace_update f v) = f (armKSKernelVSpace v)"
  by (cases v) simp

lemma armKSKernelVSpace_armKSGlobalPTs_update [simp]:
  "armKSKernelVSpace (armKSGlobalPTs_update f v) = armKSKernelVSpace v"
lemma armKSKernelVSpace_armHSCurVCPU_update [simp]:
  "armKSKernelVSpace (armHSCurVCPU_update f v) = armKSKernelVSpace v"
  by (cases v) simp

lemma armKSKernelVSpace_armKSNextASID_update [simp]:
  "armKSKernelVSpace (armKSNextASID_update f v) = armKSKernelVSpace v"
  by (cases v) simp

lemma armKSKernelVSpace_armKSASIDMap_update [simp]:
  "armKSKernelVSpace (armKSASIDMap_update f v) = armKSKernelVSpace v"
  by (cases v) simp

lemma armHSCurVCPU_armKSGlobalsFrame_update [simp]:
  "armHSCurVCPU (armKSGlobalsFrame_update f v) = armHSCurVCPU v"
  by (cases v) simp

lemma armHSCurVCPU_armKSASIDTable_update [simp]:
  "armHSCurVCPU (armKSASIDTable_update f v) = armHSCurVCPU v"
  by (cases v) simp

lemma armHSCurVCPU_armUSGlobalPT_update [simp]:
  "armHSCurVCPU (armUSGlobalPT_update f v) = armHSCurVCPU v"
  by (cases v) simp

lemma armHSCurVCPU_armKSGICVCPUNumListRegs_update [simp]:
  "armHSCurVCPU (armKSGICVCPUNumListRegs_update f v) = armHSCurVCPU v"
  by (cases v) simp

lemma armHSCurVCPU_armKSHWASIDTable_update [simp]:
  "armHSCurVCPU (armKSHWASIDTable_update f v) = armHSCurVCPU v"
  by (cases v) simp

lemma armHSCurVCPU_armKSKernelVSpace_update [simp]:
  "armHSCurVCPU (armKSKernelVSpace_update f v) = armHSCurVCPU v"
  by (cases v) simp

lemma armHSCurVCPU_armHSCurVCPU_update [simp]:
  "armHSCurVCPU (armHSCurVCPU_update f v) = f (armHSCurVCPU v)"
  by (cases v) simp

lemma armHSCurVCPU_armKSNextASID_update [simp]:
  "armHSCurVCPU (armKSNextASID_update f v) = armHSCurVCPU v"
  by (cases v) simp

lemma armHSCurVCPU_armKSASIDMap_update [simp]:
  "armHSCurVCPU (armKSASIDMap_update f v) = armHSCurVCPU v"
  by (cases v) simp

lemma armKSNextASID_armKSGlobalsFrame_update [simp]:
  "armKSNextASID (armKSGlobalsFrame_update f v) = armKSNextASID v"
  by (cases v) simp

lemma armKSNextASID_armKSASIDTable_update [simp]:
  "armKSNextASID (armKSASIDTable_update f v) = armKSNextASID v"
  by (cases v) simp

lemma armKSNextASID_armKSGlobalPD_update [simp]:
  "armKSNextASID (armKSGlobalPD_update f v) = armKSNextASID v"
  by (cases v) simp

lemma armKSNextASID_armKSHWASIDTable_update [simp]:
  "armKSNextASID (armKSHWASIDTable_update f v) = armKSNextASID v"
  by (cases v) simp

lemma armKSNextASID_armKSKernelVSpace_update [simp]:
  "armKSNextASID (armKSKernelVSpace_update f v) = armKSNextASID v"
  by (cases v) simp

lemma armKSNextASID_armHSCurVCPU_update [simp]:
  "armKSNextASID (armHSCurVCPU_update f v) = armKSNextASID v"
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

lemma armKSASIDMap_armKSGlobalPD_update [simp]:
  "armKSASIDMap (armKSGlobalPD_update f v) = armKSASIDMap v"
  by (cases v) simp

lemma armKSASIDMap_armKSHWASIDTable_update [simp]:
  "armKSASIDMap (armKSHWASIDTable_update f v) = armKSASIDMap v"
  by (cases v) simp

lemma armKSASIDMap_armKSKernelVSpace_update [simp]:
  "armKSASIDMap (armKSKernelVSpace_update f v) = armKSASIDMap v"
  by (cases v) simp

lemma armKSASIDMap_armHSCurVCPU_update [simp]:
  "armKSASIDMap (armHSCurVCPU_update f v) = armKSASIDMap v"
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
        globalPTs = globalsFrameTop `~alignToBits~` pageBits;
        globalPTsTop = globalPTs + bit pageBits;
        globalPD = globalPTsTop `~alignToBits~` pdBits;
        globalPDTop = globalPD + bit pdBits;
        frames = globalsFrame #
            [globalPTs, globalPTs + bit pageBits  .e.  globalPTsTop - 1] @
            [globalPD, globalPD + bit pageBits  .e.  globalPDTop - 1];
        state = ARMKernelState_ \<lparr>
            armKSGlobalsFrame= ptrFromPAddr globalsFrame,
            armKSASIDTable= funPartialArray (const Nothing) (0, (1 `~shiftL~` asidHighBits) - 1),
            armKSHWASIDTable= funArray (const Nothing),
            armKSNextASID= minBound,
            armKSASIDMap= funPartialArray (const Nothing) asidRange,
            armUSGlobalPT= error [],
            armHSCurVCPU= Nothing,
            armKSGICVCPUNumListRegs= error [],
            armKSKernelVSpace=
                (\<lambda> vref. if vref < mask 20 then ArmVSpaceKernelWindow
                                            else ArmVSpaceInvalidRegion) \<rparr>
    in
                                   (state, frames)"


end

end
