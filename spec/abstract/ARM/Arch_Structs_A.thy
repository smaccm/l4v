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
ARM specific data types
*)

chapter "ARM-Specific Data Types"

theory Arch_Structs_A
imports
  "../../design/$L4V_ARCH/Arch_Structs_B"
  "../ExceptionTypes_A"
  ArchVMRights_A
begin

text {*
This theory provides architecture-specific definitions and datatypes 
including architecture-specific capabilities and objects.
*}

section {* Architecture-specific virtual memory *}

text {* An ASID is simply a word. *}
type_synonym asid = "word32"

datatype vm_attribute = ParityEnabled | PageCacheable | Global | XNever
type_synonym vm_attributes = "vm_attribute set"

section {* Architecture-specific capabilities *}

text {*  The ARM kernel supports capabilities for ASID pools and an ASID controller capability,
along with capabilities for page tables, page mappings, System-MMU IO spaces, and 
virtual CPU contexts for hyper calls. *}

-- "unique device identifiers, board/vendor specific"
typedecl device_id

text {* A page can either be mapped in a normal page table or an IO space  *}
datatype mapping_root = MappedMem asid | MappedIO device_id

datatype arch_cap =
   ASIDPoolCap obj_ref asid
 | ASIDControlCap
 | PageTableCap pt_level obj_ref "(mapping_root \<times> vspace_ref) option"
 | PageCap obj_ref cap_rights vmpage_size "(mapping_root \<times> vspace_ref) option"
 | IOSpaceCap "device_id option"
 | VCPUCap obj_ref

definition
  is_page_cap :: "arch_cap \<Rightarrow> bool" where
  "is_page_cap c \<equiv> \<exists>x0 x1 x2 x3. c = PageCap x0 x1 x2 x3"

definition
  asid_high_bits :: nat where
  "asid_high_bits \<equiv> 8"
definition
  asid_low_bits :: nat where
  "asid_low_bits \<equiv> 10 :: nat"
definition
  asid_bits :: nat where
  "asid_bits \<equiv> 18 :: nat"

section {* Architecture-specific objects *}

text {* This section gives the types and auxiliary definitions for the
architecture-specific objects: a page table entry contains
either an invalid entry, a large page, or a small page mapping;
a virtual CPU object contains additional registers saved and restored
for hyper calls;
finally, an architecture-specific object is either an ASID pool, a
page table, a virtual CPU, or a data page used to model user
memory.
*}

text {*
  Translation table format descriptors, or page table entries, cf B3.6.1, pg B3-1339.

  @{text InvalidPTE} signifies unmapped or otherwise invalid entries, can be used at any level.
  @{text TablePTE} points to a next-level tabel and can be used at levels 1 and 2.
  Bits @{text "[39:12]"} of the PTE are bits @{text "[39:12]"} of the next-level page table.
  We force bits @{text "[39:32]"} to 0. Page tables are 12-bit aligned, so bits @{text "[11:0]"}
  of the output address are 0.
  @{text Block_1G_PTE} points to a 1G block of memory from a 1st-level table. We model
  stage 1 translations (32 bit input addresses), and force stage 2 translations to have
  bits @{text "[39..32]"} set to 0. The two remaining bits are bits 31 and 30 of the 
  output address (cf B3.6.1, pg 1340).
  @{text Block_2M_PTE} points to a 2M block of memory from a 2nd-level table. Similarly
  to 1G PTEs we force bits @{text "[39..32]"} set to 0. The remaining 11 bits @{text "[31:21]"}
  of the PTE are bits @{text "[31:21]"} of the output address (cf B3.6.1, pg 1340).
  @{text PagePTE} points to a 4K page of memory from a 3rd-level table. Similarly to table PTEs,
  Bits @{text "[39:12]"} of the PTE are bits @{text "[39:12]"} of the output address.
  Pages are 12-bit aligned, so bits @{text "[11:0]"} of the output address are 0.
*}
datatype pte =
   InvalidPTE
 | TablePTE "20 word" vm_attributes
 | Block_1G_PTE "2 word" vm_attributes cap_rights
 | Block_2M_PTE "11 word" vm_attributes cap_rights
 | PagePTE "20 word" vm_attributes cap_rights

definition
  is_page :: "pte \<Rightarrow> bool"
where
  "is_page pte \<equiv> case pte of PagePTE _ _ _ \<Rightarrow> True | _  \<Rightarrow> False"

definition
  is_block :: "pte \<Rightarrow> bool"
where
  "is_block pte \<equiv> case pte of Block_1G_PTE _ _ _ \<Rightarrow> True | Block_2M_PTE _ _ _ \<Rightarrow> True | _ \<Rightarrow> False"

typedecl hyper_reg -- "enumeration of additional hyper call registers"
axiomatization where hyper_reg_enum_class: "OFCLASS(hyper_reg, enum_class)"
instance hyper_reg :: enum by (rule hyper_reg_enum_class)

type_synonym hyper_reg_context = "hyper_reg \<Rightarrow> 32 word"

text {*
  ASID pools translate 10 bits, VCPUs store a potential association to a TCB as well as 
  an extended register context. Page tables have 512 entries (cf B3.6.5, pg 1348). For data pages,
  we record their size.
*}
datatype arch_kernel_obj =
   ASIDPool "10 word \<rightharpoonup> obj_ref"
 | VCPU "obj_ref option" hyper_reg_context
 | PageTable "9 word \<Rightarrow> pte"
 | DataPage vmpage_size

primrec
  arch_obj_size :: "arch_cap \<Rightarrow> nat"
where
  "arch_obj_size (ASIDPoolCap p as) = pageBits"
| "arch_obj_size ASIDControlCap = 0"
| "arch_obj_size (PageCap _ _ sz _) = pageBitsForSize sz"
| "arch_obj_size (PageTableCap _ _ _) = 12"
| "arch_obj_size (VCPUCap _) = 11"
| "arch_obj_size (IOSpaceCap _) = 0"

primrec
  arch_kobj_size :: "arch_kernel_obj \<Rightarrow> nat"
where
  "arch_kobj_size (ASIDPool _) = pageBits"
| "arch_kobj_size (PageTable _) = ptBits"
| "arch_kobj_size (VCPU _ _) = 11"
| "arch_kobj_size (DataPage sz) = pageBitsForSize sz"
(* FIXME ARMHYP: vcpu_bits? *)

primrec
  aobj_ref :: "arch_cap \<rightharpoonup> obj_ref"
where
  "aobj_ref (ASIDPoolCap p _) = Some p"
| "aobj_ref ASIDControlCap = None"
| "aobj_ref (PageCap x _ _ _) = Some x"
| "aobj_ref (PageTableCap _ x _) = Some x"
| "aobj_ref (VCPUCap x) = Some x"
| "aobj_ref (IOSpaceCap _) = None"

primrec (nonexhaustive)
  acap_rights :: "arch_cap \<Rightarrow> cap_rights"
where
 "acap_rights (PageCap x rs sz as) = rs"

definition
  acap_rights_update :: "cap_rights \<Rightarrow> arch_cap \<Rightarrow> arch_cap" where
 "acap_rights_update rs ac \<equiv> case ac of
    PageCap x rs' sz as \<Rightarrow> PageCap x (validate_vm_rights rs) sz as
  | _                   \<Rightarrow> ac"

section {* Architecture-specific object types and default objects *}

datatype
  aobject_type =
    ARM_4K_PageObj
  | ARM_2M_BlockObj
  | ARM_1G_BlockObj
  | PageTableObj pt_level
  | VCPUObj
  | ASIDPoolObj

definition
  arch_default_cap :: "aobject_type \<Rightarrow> obj_ref \<Rightarrow> nat \<Rightarrow> arch_cap" where
 "arch_default_cap tp r n \<equiv> case tp of
    ARM_4K_PageObj \<Rightarrow> PageCap r vm_read_write ARM_4K_Page None
  | ARM_2M_BlockObj \<Rightarrow> PageCap r vm_read_write ARM_2M_Block None
  | ARM_1G_BlockObj \<Rightarrow> PageCap r vm_read_write ARM_1G_Block None
  | PageTableObj l \<Rightarrow> PageTableCap l r None
  | VCPUObj \<Rightarrow> VCPUCap r
  | ASIDPoolObj \<Rightarrow> ASIDPoolCap r 0" (* unused *)

definition
  default_arch_object :: "aobject_type \<Rightarrow> nat \<Rightarrow> arch_kernel_obj" where
 "default_arch_object tp n \<equiv> case tp of
    ARM_4K_PageObj \<Rightarrow> DataPage ARM_4K_Page
  | ARM_2M_BlockObj \<Rightarrow> DataPage ARM_2M_Block
  | ARM_1G_BlockObj \<Rightarrow> DataPage ARM_1G_Block
  | PageTableObj _ \<Rightarrow> PageTable (\<lambda>x. InvalidPTE)
  | VCPUObj \<Rightarrow> VCPU None (\<lambda>x. 0)
  | ASIDPoolObj \<Rightarrow> ASIDPool (\<lambda>_. None)"

type_synonym hw_asid = word8

type_synonym arm_vspace_region_uses = "vspace_ref \<Rightarrow> arm_vspace_region_use"

section {* Architecture-specific state *}

text {* The architecture-specific state for the ARM model
consists of a reference to the globals page (@{text "arm_globals_frame"}),
the first level of the ASID table (@{text "arm_asid_table"}), a
map from hardware ASIDs to seL4 ASIDs (@{text "arm_hwasid_table"}), 
the next hardware ASID to preempt (@{text "arm_next_asid"}), the
inverse map from seL4 ASIDs to hardware ASIDs (first component of
@{text "arm_asid_map"}), and the address of the page directory and
page tables mapping the shared address space, along with a description
of this space (@{text "arm_global_pd"}, @{text "arm_global_pts"}, and 
@{text "arm_kernel_vspace"} respectively).

Hardware ASIDs are only ever associated with seL4 ASIDs that have a
currently active page directory. The second component of
@{text "arm_asid_map"} values is the address of that page directory.
*}

record arch_state =
  arm_globals_frame :: obj_ref
  arm_asid_table    :: "word8 \<rightharpoonup> obj_ref"
  arm_hwasid_table  :: "hw_asid \<rightharpoonup> asid"
  arm_next_asid     :: hw_asid
  arm_asid_map      :: "asid \<rightharpoonup> (hw_asid \<times> obj_ref)"
  arm_global_l1_pt  :: obj_ref
  arm_global_l2_pts :: "obj_ref list"
  arm_kernel_vspace :: arm_vspace_region_uses
  arm_io_space      :: "device_id \<rightharpoonup> obj_ref"

end
