(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory ArchStructures_H
imports
  "../../../lib/Lib"
  "../Types_H"
  Hardware_H
begin
context Arch begin global_naming ARM_HYP_H

type_synonym asid = "word32"

definition
  ASID :: "asid \<Rightarrow> asid"
where ASID_def[simp]:
 "ASID \<equiv> id"

datatype arch_capability =
    ASIDPoolCap machine_word asid
  | ASIDControlCap
  | PageCap machine_word vmrights vmpage_size "(asid * vptr) option"
  | PageTableCap machine_word "(asid * vptr) option"
  | PageDirectoryCap machine_word "asid option"
  | VCPUCap machine_word

primrec
  capVCPUPtr :: "arch_capability \<Rightarrow> machine_word"
where
  "capVCPUPtr (VCPUCap v0) = v0"

primrec
  capVPBasePtr :: "arch_capability \<Rightarrow> machine_word"
where
  "capVPBasePtr (PageCap v0 v1 v2 v3) = v0"

primrec
  capASIDPool :: "arch_capability \<Rightarrow> machine_word"
where
  "capASIDPool (ASIDPoolCap v0 v1) = v0"

primrec
  capPDBasePtr :: "arch_capability \<Rightarrow> machine_word"
where
  "capPDBasePtr (PageDirectoryCap v0 v1) = v0"

primrec
  capVPRights :: "arch_capability \<Rightarrow> vmrights"
where
  "capVPRights (PageCap v0 v1 v2 v3) = v1"

primrec
  capPTMappedAddress :: "arch_capability \<Rightarrow> (asid * vptr) option"
where
  "capPTMappedAddress (PageTableCap v0 v1) = v1"

primrec
  capPDMappedASID :: "arch_capability \<Rightarrow> asid option"
where
  "capPDMappedASID (PageDirectoryCap v0 v1) = v1"

primrec
  capASIDBase :: "arch_capability \<Rightarrow> asid"
where
  "capASIDBase (ASIDPoolCap v0 v1) = v1"

primrec
  capVPSize :: "arch_capability \<Rightarrow> vmpage_size"
where
  "capVPSize (PageCap v0 v1 v2 v3) = v2"

primrec
  capPTBasePtr :: "arch_capability \<Rightarrow> machine_word"
where
  "capPTBasePtr (PageTableCap v0 v1) = v0"

primrec
  capVPMappedAddress :: "arch_capability \<Rightarrow> (asid * vptr) option"
where
  "capVPMappedAddress (PageCap v0 v1 v2 v3) = v3"

primrec
  capVCPUPtr_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> arch_capability \<Rightarrow> arch_capability"
where
  "capVCPUPtr_update f (VCPUCap v0) = VCPUCap (f v0)"

primrec
  capVPBasePtr_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> arch_capability \<Rightarrow> arch_capability"
where
  "capVPBasePtr_update f (PageCap v0 v1 v2 v3) = PageCap (f v0) v1 v2 v3"

primrec
  capASIDPool_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> arch_capability \<Rightarrow> arch_capability"
where
  "capASIDPool_update f (ASIDPoolCap v0 v1) = ASIDPoolCap (f v0) v1"

primrec
  capPDBasePtr_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> arch_capability \<Rightarrow> arch_capability"
where
  "capPDBasePtr_update f (PageDirectoryCap v0 v1) = PageDirectoryCap (f v0) v1"

primrec
  capVPRights_update :: "(vmrights \<Rightarrow> vmrights) \<Rightarrow> arch_capability \<Rightarrow> arch_capability"
where
  "capVPRights_update f (PageCap v0 v1 v2 v3) = PageCap v0 (f v1) v2 v3"

primrec
  capPTMappedAddress_update :: "(((asid * vptr) option) \<Rightarrow> ((asid * vptr) option)) \<Rightarrow> arch_capability \<Rightarrow> arch_capability"
where
  "capPTMappedAddress_update f (PageTableCap v0 v1) = PageTableCap v0 (f v1)"

primrec
  capPDMappedASID_update :: "((asid option) \<Rightarrow> (asid option)) \<Rightarrow> arch_capability \<Rightarrow> arch_capability"
where
  "capPDMappedASID_update f (PageDirectoryCap v0 v1) = PageDirectoryCap v0 (f v1)"

primrec
  capASIDBase_update :: "(asid \<Rightarrow> asid) \<Rightarrow> arch_capability \<Rightarrow> arch_capability"
where
  "capASIDBase_update f (ASIDPoolCap v0 v1) = ASIDPoolCap v0 (f v1)"

primrec
  capVPSize_update :: "(vmpage_size \<Rightarrow> vmpage_size) \<Rightarrow> arch_capability \<Rightarrow> arch_capability"
where
  "capVPSize_update f (PageCap v0 v1 v2 v3) = PageCap v0 v1 (f v2) v3"

primrec
  capPTBasePtr_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> arch_capability \<Rightarrow> arch_capability"
where
  "capPTBasePtr_update f (PageTableCap v0 v1) = PageTableCap (f v0) v1"

primrec
  capVPMappedAddress_update :: "(((asid * vptr) option) \<Rightarrow> ((asid * vptr) option)) \<Rightarrow> arch_capability \<Rightarrow> arch_capability"
where
  "capVPMappedAddress_update f (PageCap v0 v1 v2 v3) = PageCap v0 v1 v2 (f v3)"

abbreviation (input)
  ASIDPoolCap_trans :: "(machine_word) \<Rightarrow> (asid) \<Rightarrow> arch_capability" ("ASIDPoolCap'_ \<lparr> capASIDPool= _, capASIDBase= _ \<rparr>")
where
  "ASIDPoolCap_ \<lparr> capASIDPool= v0, capASIDBase= v1 \<rparr> == ASIDPoolCap v0 v1"

abbreviation (input)
  PageCap_trans :: "(machine_word) \<Rightarrow> (vmrights) \<Rightarrow> (vmpage_size) \<Rightarrow> ((asid * vptr) option) \<Rightarrow> arch_capability" ("PageCap'_ \<lparr> capVPBasePtr= _, capVPRights= _, capVPSize= _, capVPMappedAddress= _ \<rparr>")
where
  "PageCap_ \<lparr> capVPBasePtr= v0, capVPRights= v1, capVPSize= v2, capVPMappedAddress= v3 \<rparr> == PageCap v0 v1 v2 v3"

abbreviation (input)
  PageTableCap_trans :: "(machine_word) \<Rightarrow> ((asid * vptr) option) \<Rightarrow> arch_capability" ("PageTableCap'_ \<lparr> capPTBasePtr= _, capPTMappedAddress= _ \<rparr>")
where
  "PageTableCap_ \<lparr> capPTBasePtr= v0, capPTMappedAddress= v1 \<rparr> == PageTableCap v0 v1"

abbreviation (input)
  PageDirectoryCap_trans :: "(machine_word) \<Rightarrow> (asid option) \<Rightarrow> arch_capability" ("PageDirectoryCap'_ \<lparr> capPDBasePtr= _, capPDMappedASID= _ \<rparr>")
where
  "PageDirectoryCap_ \<lparr> capPDBasePtr= v0, capPDMappedASID= v1 \<rparr> == PageDirectoryCap v0 v1"

abbreviation (input)
  VCPUCap_trans :: "(machine_word) \<Rightarrow> arch_capability" ("VCPUCap'_ \<lparr> capVCPUPtr= _ \<rparr>")
where
  "VCPUCap_ \<lparr> capVCPUPtr= v0 \<rparr> == VCPUCap v0"

definition
  isASIDPoolCap :: "arch_capability \<Rightarrow> bool"
where
 "isASIDPoolCap v \<equiv> case v of
    ASIDPoolCap v0 v1 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isASIDControlCap :: "arch_capability \<Rightarrow> bool"
where
 "isASIDControlCap v \<equiv> case v of
    ASIDControlCap \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isPageCap :: "arch_capability \<Rightarrow> bool"
where
 "isPageCap v \<equiv> case v of
    PageCap v0 v1 v2 v3 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isPageTableCap :: "arch_capability \<Rightarrow> bool"
where
 "isPageTableCap v \<equiv> case v of
    PageTableCap v0 v1 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isPageDirectoryCap :: "arch_capability \<Rightarrow> bool"
where
 "isPageDirectoryCap v \<equiv> case v of
    PageDirectoryCap v0 v1 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isVCPUCap :: "arch_capability \<Rightarrow> bool"
where
 "isVCPUCap v \<equiv> case v of
    VCPUCap v0 \<Rightarrow> True
  | _ \<Rightarrow> False"

datatype asidpool =
    ASIDPool "asid \<Rightarrow> ((machine_word) option)"

datatype vcpu =
    VCPUObj "(machine_word) option" word32 word32

primrec
  vcpuSCTLR :: "vcpu \<Rightarrow> word32"
where
  "vcpuSCTLR (VCPUObj v0 v1 v2) = v1"

primrec
  vcpuTCBPtr :: "vcpu \<Rightarrow> (machine_word) option"
where
  "vcpuTCBPtr (VCPUObj v0 v1 v2) = v0"

primrec
  vcpuACTLR :: "vcpu \<Rightarrow> word32"
where
  "vcpuACTLR (VCPUObj v0 v1 v2) = v2"

primrec
  vcpuSCTLR_update :: "(word32 \<Rightarrow> word32) \<Rightarrow> vcpu \<Rightarrow> vcpu"
where
  "vcpuSCTLR_update f (VCPUObj v0 v1 v2) = VCPUObj v0 (f v1) v2"

primrec
  vcpuTCBPtr_update :: "(((machine_word) option) \<Rightarrow> ((machine_word) option)) \<Rightarrow> vcpu \<Rightarrow> vcpu"
where
  "vcpuTCBPtr_update f (VCPUObj v0 v1 v2) = VCPUObj (f v0) v1 v2"

primrec
  vcpuACTLR_update :: "(word32 \<Rightarrow> word32) \<Rightarrow> vcpu \<Rightarrow> vcpu"
where
  "vcpuACTLR_update f (VCPUObj v0 v1 v2) = VCPUObj v0 v1 (f v2)"

abbreviation (input)
  VCPUObj_trans :: "((machine_word) option) \<Rightarrow> (word32) \<Rightarrow> (word32) \<Rightarrow> vcpu" ("VCPUObj'_ \<lparr> vcpuTCBPtr= _, vcpuSCTLR= _, vcpuACTLR= _ \<rparr>")
where
  "VCPUObj_ \<lparr> vcpuTCBPtr= v0, vcpuSCTLR= v1, vcpuACTLR= v2 \<rparr> == VCPUObj v0 v1 v2"

lemma vcpuSCTLR_vcpuSCTLR_update [simp]:
  "vcpuSCTLR (vcpuSCTLR_update f v) = f (vcpuSCTLR v)"
  by (cases v) simp

lemma vcpuSCTLR_vcpuTCBPtr_update [simp]:
  "vcpuSCTLR (vcpuTCBPtr_update f v) = vcpuSCTLR v"
  by (cases v) simp

lemma vcpuSCTLR_vcpuACTLR_update [simp]:
  "vcpuSCTLR (vcpuACTLR_update f v) = vcpuSCTLR v"
  by (cases v) simp

lemma vcpuTCBPtr_vcpuSCTLR_update [simp]:
  "vcpuTCBPtr (vcpuSCTLR_update f v) = vcpuTCBPtr v"
  by (cases v) simp

lemma vcpuTCBPtr_vcpuTCBPtr_update [simp]:
  "vcpuTCBPtr (vcpuTCBPtr_update f v) = f (vcpuTCBPtr v)"
  by (cases v) simp

lemma vcpuTCBPtr_vcpuACTLR_update [simp]:
  "vcpuTCBPtr (vcpuACTLR_update f v) = vcpuTCBPtr v"
  by (cases v) simp

lemma vcpuACTLR_vcpuSCTLR_update [simp]:
  "vcpuACTLR (vcpuSCTLR_update f v) = vcpuACTLR v"
  by (cases v) simp

lemma vcpuACTLR_vcpuTCBPtr_update [simp]:
  "vcpuACTLR (vcpuTCBPtr_update f v) = vcpuACTLR v"
  by (cases v) simp

lemma vcpuACTLR_vcpuACTLR_update [simp]:
  "vcpuACTLR (vcpuACTLR_update f v) = f (vcpuACTLR v)"
  by (cases v) simp

datatype arch_kernel_object =
    KOASIDPool asidpool
  | KOPTE pte
  | KOPDE pde
  | KOVCPU vcpu

datatype arch_tcb =
    ArchThread user_context "(machine_word) option"

primrec
  atcbVCPUPtr :: "arch_tcb \<Rightarrow> (machine_word) option"
where
  "atcbVCPUPtr (ArchThread v0 v1) = v1"

primrec
  atcbContext :: "arch_tcb \<Rightarrow> user_context"
where
  "atcbContext (ArchThread v0 v1) = v0"

primrec
  atcbVCPUPtr_update :: "(((machine_word) option) \<Rightarrow> ((machine_word) option)) \<Rightarrow> arch_tcb \<Rightarrow> arch_tcb"
where
  "atcbVCPUPtr_update f (ArchThread v0 v1) = ArchThread v0 (f v1)"

primrec
  atcbContext_update :: "(user_context \<Rightarrow> user_context) \<Rightarrow> arch_tcb \<Rightarrow> arch_tcb"
where
  "atcbContext_update f (ArchThread v0 v1) = ArchThread (f v0) v1"

abbreviation (input)
  ArchThread_trans :: "(user_context) \<Rightarrow> ((machine_word) option) \<Rightarrow> arch_tcb" ("ArchThread'_ \<lparr> atcbContext= _, atcbVCPUPtr= _ \<rparr>")
where
  "ArchThread_ \<lparr> atcbContext= v0, atcbVCPUPtr= v1 \<rparr> == ArchThread v0 v1"

lemma atcbVCPUPtr_atcbVCPUPtr_update [simp]:
  "atcbVCPUPtr (atcbVCPUPtr_update f v) = f (atcbVCPUPtr v)"
  by (cases v) simp

lemma atcbVCPUPtr_atcbContext_update [simp]:
  "atcbVCPUPtr (atcbContext_update f v) = atcbVCPUPtr v"
  by (cases v) simp

lemma atcbContext_atcbVCPUPtr_update [simp]:
  "atcbContext (atcbVCPUPtr_update f v) = atcbContext v"
  by (cases v) simp

lemma atcbContext_atcbContext_update [simp]:
  "atcbContext (atcbContext_update f v) = f (atcbContext v)"
  by (cases v) simp

consts'
archObjSize :: "arch_kernel_object \<Rightarrow> nat"

consts'
asidHighBits :: "nat"

consts'
asidLowBits :: "nat"

consts'
asidBits :: "nat"

consts'
asidRange :: "(asid * asid)"

consts'
asidHighBitsOf :: "asid \<Rightarrow> asid"

consts'
newVCPU :: "vcpu"

defs archObjSize_def:
"archObjSize a\<equiv> (case a of
                  KOASIDPool v21 \<Rightarrow>   pageBits
                | KOPTE v22 \<Rightarrow>   pteBits
                | KOPDE v23 \<Rightarrow>   pdeBits
                | KOVCPU v24 \<Rightarrow>   vcpuBits
                )"

definition
"newArchTCB \<equiv> ArchThread_ \<lparr>
    atcbContext= newContext
    ,atcbVCPUPtr= Nothing
    \<rparr>"

defs asidHighBits_def:
"asidHighBits \<equiv> 7"

defs asidLowBits_def:
"asidLowBits \<equiv> 10"

defs asidBits_def:
"asidBits \<equiv> asidHighBits + asidLowBits"

defs asidRange_def:
"asidRange\<equiv> (0, (1 `~shiftL~` asidBits) - 1)"

defs asidHighBitsOf_def:
"asidHighBitsOf asid\<equiv> (asid `~shiftR~` asidLowBits) && mask asidHighBits"

defs newVCPU_def:
"newVCPU \<equiv> error []"


datatype arch_kernel_object_type =
    PDET
  | PTET
  | VCPUT
  | ASIDPoolT

primrec
  archTypeOf :: "arch_kernel_object \<Rightarrow> arch_kernel_object_type"
where
  "archTypeOf (KOPDE e) = PDET"
| "archTypeOf (KOPTE e) = PTET"
| "archTypeOf (KOVCPU e) = VCPUT"
| "archTypeOf (KOASIDPool e) = ASIDPoolT"

end

context begin interpretation Arch .

requalify_types
  vcpu

end
end
