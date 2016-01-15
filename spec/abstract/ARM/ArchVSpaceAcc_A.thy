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
Accessor functions for architecture specific parts of the specification. 
*)

chapter "Accessing the ARM VSpace"

theory ArchVSpaceAcc_A
imports "../KHeap_A"
begin

text {* 
  This part of the specification is fairly concrete as the machine architecture
  is visible to the user in seL4 and therefore needs to be described.
  The abstraction compared to the implementation is in the data types for 
  kernel objects. The interface which is rich in machine details remains the same.
*}

section "Encodings"

text {* The high bits of a virtual ASID. *}
definition
  asid_high_bits_of :: "asid \<Rightarrow> word8" where
  "asid_high_bits_of asid \<equiv> ucast (asid >> asid_low_bits)"


section "Kernel Heap Accessors"

text {* Manipulate ASID pools, page directories and page tables in the kernel
heap. *}
definition
  get_asid_pool :: "obj_ref \<Rightarrow> (10 word \<rightharpoonup> obj_ref,'z::state_ext) s_monad" where
  "get_asid_pool ptr \<equiv> do
     kobj \<leftarrow> get_object ptr;
     (case kobj of ArchObj (ASIDPool pool) \<Rightarrow> return pool
                 | _ \<Rightarrow> fail)
   od"

definition
  set_asid_pool :: "obj_ref \<Rightarrow> (10 word \<rightharpoonup> obj_ref) \<Rightarrow> (unit,'z::state_ext) s_monad" where
 "set_asid_pool ptr pool \<equiv> do
    v \<leftarrow> get_object ptr;
    assert (case v of ArchObj (arch_kernel_obj.ASIDPool p) \<Rightarrow> True | _ \<Rightarrow> False);
    set_object ptr (ArchObj (arch_kernel_obj.ASIDPool pool))
  od"

definition
  get_vcpu :: "obj_ref \<Rightarrow> (obj_ref option \<times> hyper_reg_context,'z::state_ext) s_monad" where
  "get_vcpu ptr \<equiv> do
     kobj \<leftarrow> get_object ptr;
     (case kobj of ArchObj (VCPU t r) \<Rightarrow> return (t,r)
                 | _ \<Rightarrow> fail)
   od"

definition
  set_vcpu :: "obj_ref \<Rightarrow> (obj_ref option \<times> hyper_reg_context) \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "set_vcpu ptr vcpu \<equiv> do
     (t,r) \<leftarrow> return vcpu;
     kobj \<leftarrow> get_object ptr;
     assert (case kobj of ArchObj (VCPU _ _) \<Rightarrow> True | _ \<Rightarrow> False);
     set_object ptr (ArchObj (VCPU t r))
   od"

definition
  get_pt :: "obj_ref \<Rightarrow> (9 word \<Rightarrow> pte,'z::state_ext) s_monad" where
  "get_pt ptr \<equiv> do
     kobj \<leftarrow> get_object ptr;
     (case kobj of ArchObj (PageTable pt) \<Rightarrow> return pt
                 | _ \<Rightarrow> fail)
   od"

definition
  set_pt :: "obj_ref \<Rightarrow> (9 word \<Rightarrow> pte) \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "set_pt ptr pt \<equiv> do
     kobj \<leftarrow> get_object ptr;
     assert (case kobj of ArchObj (PageTable _) \<Rightarrow> True | _ \<Rightarrow> False);
     set_object ptr (ArchObj (PageTable pt)) 
   od"

text {* The following function takes a pointer to a PTE in kernel memory
  and returns the actual PTE. *}
definition
  get_pte :: "obj_ref \<Rightarrow> (pte,'z::state_ext) s_monad" where
  "get_pte ptr \<equiv> do
     base \<leftarrow> return (ptr && ~~mask pt_bits);
     offset \<leftarrow> return (ptr && mask pt_bits >> 3);
     pt \<leftarrow> get_pt base;
     return $ pt (ucast offset)
   od"

definition
  store_pte :: "obj_ref \<Rightarrow> pte \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "store_pte p pte \<equiv> do
    base \<leftarrow> return (p && ~~mask pt_bits);
    offset \<leftarrow> return (p && mask pt_bits >> 2);
    pt \<leftarrow> get_pt base;
    pt' \<leftarrow> return $ pt (ucast offset := pte);
    set_pt base pt'
  od"


section "Basic Operations"

text {* The kernel window is mapped into every virtual address space from the
@{term kernel_base} pointer upwards. This function copies the mappings which
create the kernel window into a new page directory object. *}
definition
copy_global_mappings :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
"copy_global_mappings new_pt \<equiv> do
    global_pt \<leftarrow> gets (arm_global_l1_pt \<circ> arch_state);
    pte_bits \<leftarrow> return 3;
    pd_size \<leftarrow> return (1 << (pt_bits - pte_bits));
    mapM_x (\<lambda>index. do
        offset \<leftarrow> return (index << pte_bits);
        pde \<leftarrow> get_pte (global_pt + offset);
        store_pte (new_pt + offset) pde
    od) [kernel_base >> 20  .e.  pd_size - 1] 
od"

text {* Walk the page tables in software. *}

definition
  bit_slice :: "'a::len word \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a word" ("_[_:_]" [70,0,0] 71)
where
  "w[n:m] = w && mask (n + 1) && ~~ mask m"

definition level_bits :: "pt_level \<Rightarrow> nat" where
  "level_bits level \<equiv> case level of
    PT_L1 \<Rightarrow> 30
  | PT_L2 \<Rightarrow> 21
  | PT_L3 \<Rightarrow> pt_bits"

definition pt_index_of :: "pt_level \<Rightarrow> vspace_ref \<Rightarrow> 32 word" where
  "pt_index_of l va \<equiv> let m = level_bits l in
  (case l of
    PT_L1 \<Rightarrow> va[31:m]
  | PT_L2 \<Rightarrow> va[29:m]
  | PT_L3 \<Rightarrow> va[30:m]) >> m"

text {*
  Return reference to the PTE addressed by @{text vspace_ref} in
  a page table located at @{term pt}, assuming the table is at level @{term l}
*}
definition
  pte_slot :: "pt_level \<Rightarrow> obj_ref \<Rightarrow> vspace_ref \<Rightarrow> obj_ref"
where
  "pte_slot l pt va \<equiv> pt || (pt_index_of l va << 3)"

text {*
  Look up the (kernel-memory) address of the next-level page table.
  @{text pt_ref} is assumed to be a table at level @{text l}.
  Fails if the PTE is Invalid, Page, or Block.
*}
definition
  lookup_pt :: "pt_level \<Rightarrow> obj_ref \<Rightarrow> vspace_ref \<Rightarrow> (obj_ref,'z::state_ext) lf_monad" where
  "lookup_pt l pt_ref vptr = doE
    pt_slot \<leftarrow> returnOk (pte_slot l pt_ref vptr);
    pte \<leftarrow> liftE $ get_pte pt_slot;
    (case pte of
      TablePTE ptab _ \<Rightarrow> returnOk $ ptrFromPAddr (ucast ptab << pt_bits)
    | _ \<Rightarrow> throwError $ MissingCapability 20)
  odE"

text {* Look up the (kernel-memory) address of the PTE in the
  page table specified by @{text vptr}, from page table root
  @{text pt_ref}, translating up to the specified level.
  Fails if any of the translation steps are via TablePTEs. *}
fun
  lookup_pt_slot :: "pt_level \<Rightarrow> obj_ref \<Rightarrow> vspace_ref \<Rightarrow> (obj_ref,'z::state_ext) lf_monad"
where
  "lookup_pt_slot PT_L1 pt vptr =
    returnOk (pte_slot PT_L1 pt vptr)"
|
  "lookup_pt_slot PT_L2 pt vptr = doE
    pt2 \<leftarrow> lookup_pt PT_L1 pt vptr;
    returnOk $ pte_slot PT_L2 pt2 vptr
  odE"
|
  "lookup_pt_slot PT_L3 pt vptr = doE
    pt2 \<leftarrow> lookup_pt PT_L1 pt vptr;
    pt3 \<leftarrow> lookup_pt PT_L2 pt2 vptr;
    returnOk $ pte_slot PT_L3 pt3 vptr
  odE"


text {* A non-failing version of @{const lookup_pt_slot} when the pd is already known *}
definition 
  lookup_pt_slot_no_fail :: "word32 \<Rightarrow> vspace_ref \<Rightarrow> word32"
where
  "lookup_pt_slot_no_fail pt vptr \<equiv> 
     let pt_index = ((vptr >> 12) && 0xff) 
     in pt + (pt_index << 2)" 

end
