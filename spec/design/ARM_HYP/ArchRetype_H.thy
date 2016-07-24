(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "Retyping Objects"

theory ArchRetype_H
imports
  ArchRetypeDecls_H
  ArchVSpaceDecls_H
  Hardware_H
  "../KI_Decls_H"
begin
context Arch begin global_naming ARM_HYP_H

defs deriveCap_def:
"deriveCap x0 x1\<equiv> (* case removed *) undefined"

defs updateCapData_def:
"updateCapData arg1 arg2 cap \<equiv> ArchObjectCap cap"

defs maskCapRights_def:
"maskCapRights r x1\<equiv> (let c = x1 in
  if isPageCap c
  then   ArchObjectCap $ c \<lparr>
    capVPRights := maskVMRights (capVPRights c) r \<rparr>
  else   ArchObjectCap c
  )"

defs finaliseCap_def:
"finaliseCap x0 x1\<equiv> (* case removed *) undefined"

defs resetMemMapping_def:
"resetMemMapping x0\<equiv> (case x0 of
    (PageCap p rts sz _) \<Rightarrow>    PageCap p rts sz Nothing
  | (PageTableCap ptr _) \<Rightarrow>    PageTableCap ptr Nothing
  | (PageDirectoryCap ptr _) \<Rightarrow>    PageDirectoryCap ptr Nothing
  | cap \<Rightarrow>    cap
  )"

defs recycleCap_def:
"recycleCap is_final x1 \<equiv> (* case removed *) undefined"

defs hasRecycleRights_def:
"hasRecycleRights x0\<equiv> (case x0 of
    (PageCap _ rights _ _) \<Rightarrow>    rights = VMReadWrite
  | _ \<Rightarrow>    True
  )"

defs sameRegionAs_def:
"sameRegionAs x0 x1\<equiv> (* case removed *) undefined"

defs isPhysicalCap_def:
"isPhysicalCap x0\<equiv> (case x0 of
    ASIDControlCap \<Rightarrow>    False
  | _ \<Rightarrow>    True
  )"

defs sameObjectAs_def:
"sameObjectAs x0 x1\<equiv> (let (a, b) = (x0, x1) in
  if isPageCap a \<and> isPageCap b
  then let ptrA = capVPBasePtr a
  in  
    (ptrA = capVPBasePtr b) \<and> (capVPSize a = capVPSize b)
        \<and> (ptrA \<le> ptrA + bit (pageBitsForSize $ capVPSize a) - 1)
  else   sameRegionAs a b
  )"

definition
"createPageObject ptr numPages\<equiv> (do
    addrs \<leftarrow> placeNewObject ptr UserData numPages;
    doMachineOp $ initMemory (PPtr $ fromPPtr ptr) (1 `~shiftL~` (pageBits + numPages) );
    return addrs
od)"

defs createObject_def:
"createObject t regionBase arg3 \<equiv>
    let funupd = (\<lambda> f x v y. if y = x then v else f y) in
    let pointerCast = PPtr \<circ> fromPPtr in
    let mkPageCap = \<lambda> sz. PageCap (pointerCast regionBase) VMReadWrite sz Nothing
    in (* case removed *) undefined"

defs decodeInvocation_def:
"decodeInvocation label args capIndex slot cap extraCaps \<equiv>
    (case cap of
         VCPUCap _ \<Rightarrow>   decodeARMVCPUInvocation label args capIndex slot cap extraCaps
       | _ \<Rightarrow>   decodeARMMMUInvocation label args capIndex slot cap extraCaps
       )"

defs performInvocation_def:
"performInvocation i \<equiv>
    (* case removed *) undefined"

defs capUntypedPtr_def:
"capUntypedPtr x0\<equiv> (case x0 of
    (PageCap ((* PPtr *) p) _ _ _) \<Rightarrow>    PPtr p
  | (PageTableCap ((* PPtr *) p) _) \<Rightarrow>    PPtr p
  | (PageDirectoryCap ((* PPtr *) p) _) \<Rightarrow>    PPtr p
  | ASIDControlCap \<Rightarrow>    error []
  | (ASIDPoolCap ((* PPtr *) p) _) \<Rightarrow>    PPtr p
  | (VCPUCap ((* PPtr *) p)) \<Rightarrow>    PPtr p
  )"

defs capUntypedSize_def:
"capUntypedSize x0\<equiv> (case x0 of
    (PageCap _ _ sz _) \<Rightarrow>    bit (pageBitsForSize sz)
  | (PageTableCap _ _) \<Rightarrow>    bit (ptBits + pteBits)
  | (PageDirectoryCap _ _) \<Rightarrow>    bit (pdBits + pdeBits)
  | (ASIDControlCap ) \<Rightarrow>    bit (asidHighBits + 2)
  | (ASIDPoolCap _ _) \<Rightarrow>    bit (asidLowBits + 2)
  | (VCPUCap _) \<Rightarrow>    bit vcpuBits
  )"


end
end
