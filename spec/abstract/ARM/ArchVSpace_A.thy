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
Higher level functions for manipulating virtual address spaces
*)

chapter "ARM VSpace Functions"

theory ArchVSpace_A
imports "../Retype_A"
begin

text {* Save the set of entries that would be inserted into a page table
 to map various different sizes of frame at a given virtual address. *}
fun create_mapping_entry ::
  "paddr \<Rightarrow> vspace_ref \<Rightarrow> vmpage_size \<Rightarrow> vm_rights \<Rightarrow> vm_attributes \<Rightarrow> word32 \<Rightarrow>
  (pte \<times> obj_ref,'z::state_ext) se_monad"
where
  "create_mapping_entry base vptr ARM_4K_Page vm_rights attrib pt =
  doE
    pte_ref \<leftarrow> lookup_error_on_failure False $ lookup_pt_slot PT_L3 pt vptr;
    returnOk (PagePTE (ucast (base >> pageBitsForSize ARM_4K_Page))
                      (attrib - {Global, ParityEnabled}) vm_rights, pte_ref)
  odE"
|
  "create_mapping_entry base vptr ARM_2M_Block vm_rights attrib pt =
  doE
    pte_ref \<leftarrow> lookup_error_on_failure False $ lookup_pt_slot PT_L2 pt vptr;
    returnOk (Block_2M_PTE (ucast (base >> pageBitsForSize ARM_2M_Block))
                           (attrib - {Global, ParityEnabled}) vm_rights, pte_ref)
  odE"
|
  "create_mapping_entry base vptr ARM_1G_Block vm_rights attrib pt =
  doE
    pte_ref \<leftarrow> lookup_error_on_failure False $ lookup_pt_slot PT_L1 pt vptr;
    returnOk (Block_2M_PTE (ucast (base >> pageBitsForSize ARM_1G_Block))
                           (attrib - {Global, ParityEnabled}) vm_rights, pte_ref)
  odE"


text {* This function checks that given entries replace either
invalid entries or existing frames of the same size, but not page tables. *}
fun ensure_safe_mapping ::
  "pte \<times> word32 \<Rightarrow> (unit,'z::state_ext) se_monad"
where
"ensure_safe_mapping (InvalidPTE, _) = returnOk ()"
|
"ensure_safe_mapping (PagePTE _ _ _, slot) = doE
  pte \<leftarrow> liftE $ get_pte slot;
  (case pte of
    InvalidPTE \<Rightarrow> returnOk ()
  | PagePTE _ _ _ \<Rightarrow> returnOk ()
  | _ \<Rightarrow> throwError DeleteFirst)
odE"
|
"ensure_safe_mapping (Block_2M_PTE _ _ _, slot) = doE
  pte \<leftarrow> liftE $ get_pte slot;
  (case pte of
    InvalidPTE \<Rightarrow> returnOk ()
  | Block_2M_PTE _ _ _ \<Rightarrow> returnOk ()
  | _ \<Rightarrow> throwError DeleteFirst)
odE"
|
"ensure_safe_mapping (Block_1G_PTE _ _ _, slot) = doE
  pte \<leftarrow> liftE $ get_pte slot;
  (case pte of
    InvalidPTE \<Rightarrow> returnOk ()
  | Block_1G_PTE _ _ _ \<Rightarrow> returnOk ()
  | _ \<Rightarrow> throwError DeleteFirst)
odE"
|
"ensure_safe_mapping (TablePTE _ _, slot) = fail"

text {* Look up a thread's IPC buffer and check that the thread has the right
authority to read or (in the receiver case) write to it. *}
definition
lookup_ipc_buffer :: "bool \<Rightarrow> word32 \<Rightarrow> (word32 option,'z::state_ext) s_monad" where
"lookup_ipc_buffer is_receiver thread \<equiv> do
    buffer_ptr \<leftarrow> thread_get tcb_ipc_buffer thread;
    buffer_frame_slot \<leftarrow> return (thread, tcb_cnode_index 4);
    buffer_cap \<leftarrow> get_cap buffer_frame_slot;
    (case buffer_cap of
      ArchObjectCap (PageCap p R vms _) \<Rightarrow>
        if vm_read_write \<subseteq> R \<or> vm_read_only \<subseteq> R \<and> \<not>is_receiver
        then return $ Some $ p + (buffer_ptr && mask (pageBitsForSize vms))
        else return None
    | _ \<Rightarrow> return None)
od"

text {* Locate the page directory associated with a given virtual ASID. *}
definition
find_pt_for_asid :: "asid \<Rightarrow> (word32,'z::state_ext) lf_monad" where
"find_pt_for_asid asid \<equiv> doE
    assertE (asid > 0);
    asid_table \<leftarrow> liftE $ gets (arm_asid_table \<circ> arch_state);
    pool_ptr \<leftarrow> returnOk (asid_table (asid_high_bits_of asid));
    pool \<leftarrow> (case pool_ptr of
               Some ptr \<Rightarrow> liftE $ get_asid_pool ptr
             | None \<Rightarrow> throwError InvalidRoot);
    pt \<leftarrow> returnOk (pool (ucast asid));
    (case pt of
          Some ptr \<Rightarrow> returnOk ptr
        | None \<Rightarrow> throwError InvalidRoot)
odE"

text {* Locate the page directory and check that this process succeeds and
returns a pointer to a real page directory. *}
definition
find_pt_for_asid_assert :: "asid \<Rightarrow> (word32,'z::state_ext) s_monad" where
"find_pt_for_asid_assert asid \<equiv> do
   pt \<leftarrow> find_pt_for_asid asid <catch> K fail;
   get_pte pt;
   return pt
 od"

definition
  get_io_pt :: "device_id \<Rightarrow> (obj_ref option,'z::state_ext) s_monad"
where
  "get_io_pt dev \<equiv> gets (\<lambda>s. (arm_io_space \<circ> arch_state) s dev)"

text {* Get the root page table of a specific device *}
definition
find_pt_for_device :: "device_id \<Rightarrow> (obj_ref,'z::state_ext) lf_monad" where
"find_pt_for_device dev = doE
   opt_pt \<leftarrow> liftE $ get_io_pt dev;
   throw_opt InvalidRoot opt_pt
odE"

text {* Get the root page table of a specific mapping root (asid or device id) *}
definition
find_root_pt :: "mapping_root \<Rightarrow> (obj_ref,'z::state_ext) lf_monad" where
"find_root_pt m \<equiv> case m of
    MappedMem asid \<Rightarrow> find_pt_for_asid asid
  | MappedIO dev \<Rightarrow> find_pt_for_device dev"

text {* Format a VM fault message to be passed to a thread's supervisor after
it encounters a page fault. *}
fun
handle_vm_fault :: "word32 \<Rightarrow> vmfault_type \<Rightarrow> (unit,'z::state_ext) f_monad"
where
"handle_vm_fault thread ARMDataAbort = doE
    addr \<leftarrow> liftE $ do_machine_op getFAR;
    fault \<leftarrow> liftE $ do_machine_op getDFSR;
    throwError $ VMFault addr [0, fault && mask 14]
odE"
|
"handle_vm_fault thread ARMPrefetchAbort = doE
    pc \<leftarrow> liftE $ as_user thread $ getRestartPC;
    fault \<leftarrow> liftE $ do_machine_op getIFSR;
    throwError $ VMFault pc [1, fault && mask 14]
odE"

text {* Load the optional hardware ASID currently associated with this virtual
ASID. *}
definition
load_hw_asid :: "asid \<Rightarrow> (hardware_asid option,'z::state_ext) s_monad" where
"load_hw_asid asid \<equiv> do
    asid_map \<leftarrow> gets (arm_asid_map \<circ> arch_state);
    return $ option_map fst $ asid_map asid
od"

text {* Associate a hardware ASID with a virtual ASID. *}
definition
store_hw_asid :: "asid \<Rightarrow> hardware_asid \<Rightarrow> (unit,'z::state_ext) s_monad" where
"store_hw_asid asid hw_asid \<equiv> do
    pt \<leftarrow> find_pt_for_asid_assert asid;
    asid_map \<leftarrow> gets (arm_asid_map \<circ> arch_state);
    asid_map' \<leftarrow> return (asid_map (asid \<mapsto> (hw_asid, pt)));
    modify (\<lambda>s. s \<lparr> arch_state := (arch_state s) \<lparr> arm_asid_map := asid_map' \<rparr>\<rparr>);
    hw_asid_map \<leftarrow> gets (arm_hwasid_table \<circ> arch_state);
    hw_asid_map' \<leftarrow> return (hw_asid_map (hw_asid \<mapsto> asid));
    modify (\<lambda>s. s \<lparr> arch_state := (arch_state s) \<lparr> arm_hwasid_table := hw_asid_map' \<rparr>\<rparr>)
od"

text {* Clear all TLB mappings associated with this virtual ASID. *}
definition
invalidate_tlb_by_asid :: "asid \<Rightarrow> (unit,'z::state_ext) s_monad" where
"invalidate_tlb_by_asid asid \<equiv> do
    maybe_hw_asid \<leftarrow> load_hw_asid asid;
    (case maybe_hw_asid of
          None \<Rightarrow> return ()
        | Some hw_asid \<Rightarrow> do_machine_op $ invalidateTLB_ASID hw_asid)
od"

text {* Flush all cache and TLB entries associated with this virtual ASID. *}
definition
flush_space :: "asid \<Rightarrow> (unit,'z::state_ext) s_monad" where
"flush_space asid \<equiv> do
    maybe_hw_asid \<leftarrow> load_hw_asid asid;
    do_machine_op cleanCaches_PoU;
    (case maybe_hw_asid of
          None \<Rightarrow> return ()
        | Some hw_asid \<Rightarrow> do_machine_op $ invalidateTLB_ASID hw_asid)
od"

text {* Remove any mapping from this virtual ASID to a hardware ASID. *}
definition
invalidate_asid :: "asid \<Rightarrow> (unit,'z::state_ext) s_monad" where
"invalidate_asid asid \<equiv> do
    asid_map \<leftarrow> gets (arm_asid_map \<circ> arch_state);
    asid_map' \<leftarrow> return (asid_map (asid:= None));
    modify (\<lambda>s. s \<lparr> arch_state := (arch_state s) \<lparr> arm_asid_map := asid_map' \<rparr>\<rparr>)
od"

text {* Remove any mapping from this hardware ASID to a virtual ASID. *}
definition
invalidate_hw_asid_entry :: "hardware_asid \<Rightarrow> (unit,'z::state_ext) s_monad" where
"invalidate_hw_asid_entry hw_asid \<equiv> do
  hw_asid_map \<leftarrow> gets (arm_hwasid_table \<circ> arch_state);
  hw_asid_map' \<leftarrow> return (hw_asid_map (hw_asid:= None));
  modify (\<lambda>s. s \<lparr> arch_state := (arch_state s) \<lparr> arm_hwasid_table := hw_asid_map' \<rparr>\<rparr>)
od"

text {* Remove virtual to physical mappings in either direction involving this
virtual ASID. *}
definition
invalidate_asid_entry :: "asid \<Rightarrow> (unit,'z::state_ext) s_monad" where
"invalidate_asid_entry asid \<equiv> do
  maybe_hw_asid \<leftarrow> load_hw_asid asid;
  when (maybe_hw_asid \<noteq> None) $ invalidate_hw_asid_entry (the maybe_hw_asid);
  invalidate_asid asid
od"

text {* Locate a hardware ASID that is not in use, if necessary by reclaiming
one from another virtual ASID in a round-robin manner. *}
definition
find_free_hw_asid :: "(hardware_asid,'z::state_ext) s_monad" where
"find_free_hw_asid \<equiv> do
    hw_asid_table \<leftarrow> gets (arm_hwasid_table \<circ> arch_state);
    next_asid \<leftarrow> gets (arm_next_asid \<circ> arch_state);
    maybe_asid \<leftarrow> return (find (\<lambda>a. hw_asid_table a = None)
                    (take (length [minBound :: hardware_asid .e. maxBound])
                        ([next_asid .e. maxBound] @ [minBound .e. next_asid])));
    (case maybe_asid of
       Some hw_asid \<Rightarrow> return hw_asid
     | None \<Rightarrow>  do
            invalidate_asid $ the $ hw_asid_table next_asid;
            do_machine_op $ invalidateTLB_ASID next_asid;
            invalidate_hw_asid_entry next_asid;
            new_next_asid \<leftarrow> return (next_asid + 1);
            modify (\<lambda>s. s \<lparr> arch_state := (arch_state s) \<lparr> arm_next_asid := new_next_asid \<rparr>\<rparr>);
            return next_asid
       od)
od"

text {* Get the hardware ASID associated with a virtual ASID, assigning one if
none is already assigned. *}
definition
get_hw_asid :: "asid \<Rightarrow> (hardware_asid,'z::state_ext) s_monad" where
"get_hw_asid asid \<equiv> do
  maybe_hw_asid \<leftarrow> load_hw_asid asid;
  (case maybe_hw_asid of
    Some hw_asid \<Rightarrow> return hw_asid
  | None \<Rightarrow>  do
      new_hw_asid \<leftarrow> find_free_hw_asid;
      store_hw_asid asid new_hw_asid;
      return new_hw_asid
  od)
od"


abbreviation
  "arm_context_switch_hwasid pd hwasid \<equiv> do
              setCurrentPD $ addrFromPPtr pd;
              setHardwareASID hwasid
          od" 

definition
  arm_context_switch :: "word32 \<Rightarrow> asid \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "arm_context_switch pt asid \<equiv> do
      hwasid \<leftarrow> get_hw_asid asid;
      do_machine_op $ arm_context_switch_hwasid pt hwasid
    od"

text {* Switch into the address space of a given thread or the global address
space if none is correctly configured. *}
definition
  set_vm_root :: "word32 \<Rightarrow> (unit,'z::state_ext) s_monad" where
"set_vm_root tcb \<equiv> do
    thread_root_slot \<leftarrow> return (tcb, tcb_cnode_index 1);
    thread_root \<leftarrow> get_cap thread_root_slot;
    (case thread_root of
       ArchObjectCap (PageTableCap PT_L1 pt (Some (MappedMem asid, _))) \<Rightarrow> doE
           pt' \<leftarrow> find_pt_for_asid asid;
           whenE (pt \<noteq> pt') $ throwError InvalidRoot;
           liftE $ arm_context_switch pt asid
       odE
     | _ \<Rightarrow> throwError InvalidRoot) <catch>
    (\<lambda>_. do
       global_pt \<leftarrow> gets (arm_global_l1_pt \<circ> arch_state);
       do_machine_op $ setCurrentPD $ addrFromPPtr global_pt
    od)
od"

text {* Before deleting an ASID pool object we must deactivate all page
directories that are installed in it. *}
definition
delete_asid_pool :: "asid \<Rightarrow> word32 \<Rightarrow> (unit,'z::state_ext) s_monad" where
"delete_asid_pool base ptr \<equiv> do
  assert (base && mask asid_low_bits = 0);
  asid_table \<leftarrow> gets (arm_asid_table \<circ> arch_state);
  when (asid_table (asid_high_bits_of base) = Some ptr) $ do
    pool \<leftarrow> get_asid_pool ptr;
    mapM (\<lambda>offset. (when (pool (ucast offset) \<noteq> None) $ do
                          flush_space $ base + offset;
                          invalidate_asid_entry $ base + offset
                    od)) [0  .e.  (1 << asid_low_bits) - 1];
    asid_table' \<leftarrow> return (asid_table (asid_high_bits_of base:= None));
    modify (\<lambda>s. s \<lparr> arch_state := (arch_state s) \<lparr> arm_asid_table := asid_table' \<rparr>\<rparr>);
    tcb \<leftarrow> gets cur_thread;
    set_vm_root tcb
  od
od"

text {* When deleting a page table from an ASID pool we must deactivate it. *}
definition
delete_asid :: "asid \<Rightarrow> word32 \<Rightarrow> (unit,'z::state_ext) s_monad" where
"delete_asid asid pt \<equiv> do
  asid_table \<leftarrow> gets (arm_asid_table \<circ> arch_state);
  (case asid_table (asid_high_bits_of asid) of
    None \<Rightarrow> return ()
  | Some pool_ptr \<Rightarrow>  do
     pool \<leftarrow> get_asid_pool pool_ptr;
     when (pool (ucast asid) = Some pt) $ do
                flush_space asid;
                invalidate_asid_entry asid;
                pool' \<leftarrow> return (pool (ucast asid := None));
                set_asid_pool pool_ptr pool';
                tcb \<leftarrow> gets cur_thread;
                set_vm_root tcb
            od
    od)
od"

text {* Switch to a particular address space in order to perform a flush
operation. Assumes pt is a level 1 table. *}
definition
set_vm_root_for_flush :: "word32 \<Rightarrow> asid \<Rightarrow> (bool,'z::state_ext) s_monad" where
"set_vm_root_for_flush pt asid \<equiv> do
    tcb \<leftarrow> gets cur_thread;
    thread_root_slot \<leftarrow> return (tcb, tcb_cnode_index 1);
    thread_root \<leftarrow> get_cap thread_root_slot;
    not_is_pt \<leftarrow> (case thread_root of
                    ArchObjectCap (PageTableCap _ cur_pt (Some _)) \<Rightarrow> return (cur_pt \<noteq> pt)
                  | _ \<Rightarrow> return True);
    (if not_is_pt then do
        arm_context_switch pt asid;
        return True
    od
    else return False)
od"

text {* Encoding of a device id in a word *}
consts
  device_id_from_word :: "machine_word \<Rightarrow> device_id"
  word_from_device_id :: "device_id \<Rightarrow> machine_word"

definition
  invalidate_io_tlb_by_device :: "device_id \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "invalidate_io_tlb_by_device dev \<equiv>
    do_machine_op $ invalidateDeviceIOTLB (word_from_device_id dev)"

definition
do_flush :: "flush_type \<Rightarrow> vspace_ref \<Rightarrow> vspace_ref \<Rightarrow> paddr \<Rightarrow> unit machine_monad" where
"do_flush flush_type vstart vend pstart \<equiv>
    case flush_type of
       Clean \<Rightarrow> cleanCacheRange_RAM vstart vend pstart
     | Invalidate \<Rightarrow> invalidateCacheRange_RAM vstart vend pstart
     | CleanInvalidate \<Rightarrow> cleanInvalidateCacheRange_RAM vstart vend pstart
     | Unify \<Rightarrow> do
         cleanCacheRange_PoU vstart vend pstart;
         dsb;
         invalidateCacheRange_I vstart vend pstart;
         branchFlushRange vstart vend pstart;
         isb
     od"

text {* Flush mappings associated with a page table. *}
definition
flush_table :: "word32 \<Rightarrow> mapping_root \<Rightarrow> vspace_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
"flush_table pt m vptr \<equiv> 
  case m of
    MappedMem asid \<Rightarrow>
    do
      assert (vptr && mask (pageBitsForSize ARM_2M_Block) = 0);
      root_switched \<leftarrow> set_vm_root_for_flush pt asid;
      maybe_hw_asid \<leftarrow> load_hw_asid asid;
      when (maybe_hw_asid \<noteq> None) $ do
        hw_asid \<leftarrow> return (the maybe_hw_asid);
        do_machine_op $ invalidateTLB_ASID hw_asid;
        when root_switched $ do
          tcb \<leftarrow> gets cur_thread;
          set_vm_root tcb
        od
      od
    od
  | MappedIO device \<Rightarrow> invalidate_io_tlb_by_device device"

text {* Flush mappings associated with a given page. *}
definition
  flush_page :: "vmpage_size \<Rightarrow> word32 \<Rightarrow> mapping_root \<Rightarrow> vspace_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
"flush_page page_size pt m vptr \<equiv>
  case m of MappedMem asid \<Rightarrow>
    do
      assert (vptr && mask pageBits = 0);
      root_switched \<leftarrow> set_vm_root_for_flush pt asid;
      maybe_hw_asid \<leftarrow> load_hw_asid asid;
      when (maybe_hw_asid \<noteq> None) $ do
        hw_asid \<leftarrow> return (the maybe_hw_asid);
        do_machine_op $ invalidateTLB_VAASID (vptr || ucast hw_asid);
        when root_switched $ do
            tcb \<leftarrow> gets cur_thread;
            set_vm_root tcb
        od
      od
    od
  | MappedIO device \<Rightarrow> invalidate_io_tlb_by_device device"

text {* Return the optional previous-level page a page table is mapped in. *}
fun
  page_table_mapped :: "mapping_root \<Rightarrow> vspace_ref \<Rightarrow> pt_level \<Rightarrow> obj_ref \<Rightarrow> (obj_ref option,'z::state_ext) s_monad"
where
"page_table_mapped m vaddr PT_L1 pt = return None"
|
"page_table_mapped m vaddr l pt =
(doE
    pt1 \<leftarrow> find_root_pt m;
    pt_slot \<leftarrow> lookup_pt_slot l vaddr pt1;
    pte \<leftarrow> liftE $ get_pte pt_slot;
    case pte of
      TablePTE addr _ \<Rightarrow> returnOk $
             if addrFromPPtr pt = ucast addr << ptBits then Some pt1 else None
    | _ \<Rightarrow> returnOk None
odE <catch> (K $ return None))"

fun pred_level :: "pt_level \<Rightarrow> pt_level" where
  "pred_level PT_L2 = PT_L1" |
  "pred_level PT_L3 = PT_L2"


text {* Unmap a page table from its page directory. *}
definition
unmap_page_table :: "mapping_root \<Rightarrow> vspace_ref \<Rightarrow> pt_level \<Rightarrow> word32 \<Rightarrow> (unit,'z::state_ext) s_monad" where
"unmap_page_table m vaddr l pt \<equiv> do
    ptOpt \<leftarrow> page_table_mapped m vaddr l pt;
    case ptOpt of
      None \<Rightarrow> return ()
    | Some pt \<Rightarrow> do
        pt_slot \<leftarrow> return $ pte_slot (pred_level l) pt vaddr;
        store_pte pt_slot InvalidPTE;
        do_machine_op $ cleanByVA_PoU pt_slot (addrFromPPtr pt_slot);
        flush_table pt m vaddr
    od
od"

text {* Size of memory region corresponding to a PTE *}
fun
  vmpage_size_of_pte :: "pte \<Rightarrow> vmpage_size"
where
  "vmpage_size_of_pte (PagePTE _ _ _) = ARM_4K_Page" |
  "vmpage_size_of_pte (Block_2M_PTE _ _ _) = ARM_2M_Block" |
  "vmpage_size_of_pte (Block_1G_PTE _ _ _) = ARM_1G_Block"

text {* 32 bit physical address associated with a PTE. 0 if invalid. *}
fun
  addr_from_pte :: "pte \<Rightarrow> obj_ref"
where
  "addr_from_pte InvalidPTE = 0" |
  "addr_from_pte (TablePTE ref _) = ucast ref << ptBits" |
  "addr_from_pte (Block_1G_PTE ref _ _) = ucast ref << 30" |
  "addr_from_pte (Block_2M_PTE ref _ _) = ucast ref << 21" |
  "addr_from_pte (PagePTE ref _ _) = ucast ref << pageBits"

text {* Check that a given frame is mapped by a given mapping entry. *}
definition
  check_mapping_pptr :: "machine_word \<Rightarrow> vmpage_size \<Rightarrow> obj_ref \<Rightarrow> (bool,'z::state_ext) s_monad"
where
"check_mapping_pptr pptr pgsz pte_ref \<equiv> do
     pte \<leftarrow> get_pte pte_ref;
     return $ (is_block pte \<or> is_page pte) \<and> 
              addrFromPPtr pptr = addr_from_pte pte \<and> pgsz = vmpage_size_of_pte pte
   od"

text {* Raise an exception if a property does not hold. *}
definition
throw_on_false :: "'e \<Rightarrow> (bool,'z::state_ext) s_monad \<Rightarrow> ('e + unit,'z::state_ext) s_monad" where
"throw_on_false ex f \<equiv> doE v \<leftarrow> liftE f; unlessE v $ throwError ex odE"

text {* Each page size can only occur on a specific page table level: *}
definition
  vmpage_size_to_level :: "vmpage_size \<Rightarrow> pt_level"
where
  "vmpage_size_to_level pgsz \<equiv> case pgsz of
      ARM_4K_Page \<Rightarrow> PT_L3
    | ARM_2M_Block \<Rightarrow> PT_L2
    | ARM_1G_Block \<Rightarrow> PT_L1"

text {* Unmap a mapped page if the given mapping details are still current. *}
definition
unmap_page :: "vmpage_size \<Rightarrow> mapping_root \<Rightarrow> vspace_ref \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
"unmap_page pgsz m vptr pptr \<equiv> doE
    pt \<leftarrow> find_root_pt m;
    pte_ref \<leftarrow> lookup_pt_slot (vmpage_size_to_level pgsz) pt vptr;
    throw_on_false undefined $ check_mapping_pptr pptr pgsz pte_ref;
    liftE $ do
      store_pte pte_ref InvalidPTE;
      do_machine_op $ cleanByVA_PoU pte_ref (addrFromPPtr pte_ref);
      flush_page pgsz pt m vptr
    od
odE <catch> (K $ return ())"



text {* PageTable capabilities cannot be copied until they
have a virtual ASID and location assigned. This is because page tables
cannot have multiple current virtual ASIDs and cannot be shared
between address spaces or virtual locations. *}
definition
  arch_derive_cap :: "arch_cap \<Rightarrow> (arch_cap,'z::state_ext) se_monad"
where
  "arch_derive_cap c \<equiv> case c of
     PageTableCap _ _ (Some x) \<Rightarrow> returnOk c
   | PageTableCap _ _ None \<Rightarrow> throwError IllegalOperation
   | PageCap r R pgs x \<Rightarrow> returnOk (PageCap r R pgs None)
   | ASIDControlCap \<Rightarrow> returnOk c
   | ASIDPoolCap _ _ \<Rightarrow> returnOk c
   | IOSpaceCap _ \<Rightarrow> returnOk c
   | VCPUCap _ \<Rightarrow> returnOk c"


text {* Only IOSpaceCaps can be minted into new form. *}
definition
  arch_update_cap_data :: "data \<Rightarrow> arch_cap \<Rightarrow> arch_cap"
where
  "arch_update_cap_data data c \<equiv> case c of
     IOSpaceCap None \<Rightarrow> IOSpaceCap (Some (device_id_from_word data))
   |  _ \<Rightarrow> c"

text {* Unmap the page table associated with a device *}
definition
  unmap_device :: "device_id \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "unmap_device dev \<equiv> do
    io_space \<leftarrow> gets (arm_io_space \<circ> arch_state);
    io_space' \<leftarrow> return (io_space (dev := None));
    modify (\<lambda>s. s\<lparr>arch_state := arch_state s \<lparr>arm_io_space := io_space'\<rparr>\<rparr>);
    invalidate_io_tlb_by_device dev
  od"

text {* Unmap page table from device if provided PT is mapped there. *}
definition
  unmap_device_checked :: "device_id \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "unmap_device_checked dev pt \<equiv> do
    opt_pt \<leftarrow> get_io_pt dev;
    when (opt_pt = Some pt) $ unmap_device dev
  od"

text {* Map a page table to an empty device slot. *}
definition
  map_device :: "device_id \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "map_device dev pt_ref \<equiv> do
    modify (arch_state_update (arm_io_space_update (\<lambda>io_space. io_space (dev \<mapsto> pt_ref))));
    invalidate_io_tlb_by_device dev
  od"

text {* Invalidate appropriate TLB *}
definition
  "invalidate_tlb_by_mapping_root m \<equiv> case m of
     MappedMem asid \<Rightarrow> invalidate_tlb_by_asid asid
   | MappedIO dev \<Rightarrow> invalidate_io_tlb_by_device dev"

text {* Dissociate a VCPU from a TCB *}
definition
  dissociate_vcpu :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "dissociate_vcpu vcpu \<equiv> do
    (tcb_opt, r) \<leftarrow> get_vcpu vcpu;
    case tcb_opt of
      None \<Rightarrow> return ()
    | Some tcb \<Rightarrow> do
        thread_set (\<lambda>t. t \<lparr> tcb_vcpu := None \<rparr>) tcb;
        set_vcpu vcpu (None, r)
      od
  od"

text {* Dissociate a TCB from a VCPU *}
definition
  dissociate_tcb :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "dissociate_tcb tcb_ref \<equiv> do
    vcpu_opt \<leftarrow> thread_get tcb_vcpu tcb_ref;
    case vcpu_opt of
      None \<Rightarrow> return ()
    | Some vcpu \<Rightarrow> dissociate_vcpu vcpu
  od"

text {* Associate a VCPU with a TCB *}
definition
  associate :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "associate vcpu_ref tcb_ref \<equiv> do
    (_,r) \<leftarrow> get_vcpu vcpu_ref;
    set_vcpu vcpu_ref (Some tcb_ref, r);
    thread_set (tcb_vcpu_update $ K $ Some vcpu_ref) tcb_ref
  od"

text {* Actions that must be taken on finalisation of ARM-specific capabilities. *}
definition
  arch_finalise_cap :: "arch_cap \<Rightarrow> bool \<Rightarrow> (cap,'z::state_ext) s_monad"
where
  "arch_finalise_cap c x \<equiv> case (c, x) of
    (ASIDPoolCap ptr b, True) \<Rightarrow>  do
    delete_asid_pool b ptr;
    return NullCap
    od
  | (PageTableCap l ptr (Some (m, v)), True) \<Rightarrow> do
    if l = PT_L1 then
      (case m of
        MappedMem asid \<Rightarrow> delete_asid asid ptr
      | MappedIO dev \<Rightarrow> unmap_device_checked dev ptr)
    else unmap_page_table m v l ptr;
    return NullCap
  od
  | (PageCap ptr _ s (Some (m, v)), _) \<Rightarrow> do
     unmap_page s m v ptr;
     return NullCap
  od
  | (VCPUCap vcpu_ref, True) \<Rightarrow> do
     dissociate_vcpu vcpu_ref;
     return NullCap
  od
  | (IOSpaceCap dev_opt, True) \<Rightarrow> do
      case dev_opt of
        None \<Rightarrow> return ()
      | Some dev \<Rightarrow> unmap_device dev;
      return NullCap
  od
  | _ \<Rightarrow> return NullCap"

text {* Remove record of mappings to a page cap, page table cap or page directory cap *}

fun
  arch_reset_mem_mapping :: "arch_cap \<Rightarrow> arch_cap"
where
  "arch_reset_mem_mapping (PageCap p rts sz mp) = PageCap p rts sz None"
| "arch_reset_mem_mapping (PageTableCap l ptr mp) = PageTableCap l ptr None"
| "arch_reset_mem_mapping cap = cap"

text {* Actions that must be taken to recycle ARM-specific capabilities. *}
definition
  arch_recycle_cap :: "bool \<Rightarrow> arch_cap \<Rightarrow> (arch_cap,'z::state_ext) s_monad"
where
  "arch_recycle_cap is_final cap \<equiv> case cap of
    PageCap p _ sz _ \<Rightarrow> do
      do_machine_op $ clearMemory p (2 ^ (pageBitsForSize sz));
      arch_finalise_cap cap is_final;
      return $ arch_reset_mem_mapping cap
    od
  | PageTableCap level ptr mp \<Rightarrow> do
      pte_bits \<leftarrow> return 3;
      slots \<leftarrow> return [ptr, ptr + (1 << pte_bits) .e. ptr + (1 << ptBits) - 1];
      mapM_x (swp store_pte InvalidPTE) slots;
      do_machine_op $ cleanCacheRange_PoU ptr (ptr + (1 << ptBits) - 1) (addrFromPPtr ptr);
      case mp of 
         None \<Rightarrow> return ()
       | Some (m, v) \<Rightarrow>
           if level = PT_L1 then doE
             pt \<leftarrow> find_root_pt m;
             whenE (pt = ptr) $ liftE $ invalidate_tlb_by_mapping_root m
           odE <catch> K (return ())
           else do
             pt_opt \<leftarrow> page_table_mapped m v level ptr;
             when (pt_opt \<noteq> None) $ invalidate_tlb_by_mapping_root m
           od;
      arch_finalise_cap cap is_final;
      return (if is_final then arch_reset_mem_mapping cap else cap)
    od
  | ASIDControlCap \<Rightarrow> return ASIDControlCap
  | ASIDPoolCap ptr base \<Rightarrow> do
      asid_table \<leftarrow> gets (arm_asid_table \<circ> arch_state);
      when (asid_table (asid_high_bits_of base) = Some ptr) $ do
          delete_asid_pool base ptr;
          set_asid_pool ptr empty;
          asid_table \<leftarrow> gets (arm_asid_table \<circ> arch_state);
          asid_table' \<leftarrow> return (asid_table (asid_high_bits_of base \<mapsto> ptr));
          modify (\<lambda>s. s \<lparr> arch_state := (arch_state s) \<lparr> arm_asid_table := asid_table' \<rparr>\<rparr>)
      od;
      return cap
    od
  | IOSpaceCap dev_opt \<Rightarrow> return cap
  | VCPUCap vcpu_ref \<Rightarrow> return cap"

text {* A thread's virtual address space capability must be to a level 1 page table. *}
definition
  is_valid_vtable_root :: "cap \<Rightarrow> bool" where
  "is_valid_vtable_root c \<equiv> \<exists>r a v. c = ArchObjectCap (PageTableCap PT_L1 r (Some (MappedMem a, v)))"

text {* A thread's IPC buffer capability must be to a page that is capable of
containing the IPC buffer without the end of the buffer spilling into another
page. *}
definition
  cap_transfer_data_size :: nat where
  "cap_transfer_data_size \<equiv> 3"

definition
  msg_max_length :: nat where
 "msg_max_length \<equiv> 120"

definition
  msg_max_extra_caps :: nat where
 "msg_max_extra_caps \<equiv> 3"

definition
  msg_align_bits :: nat
  where
  "msg_align_bits \<equiv> 2 + (LEAST n. (cap_transfer_data_size + msg_max_length + msg_max_extra_caps + 2) \<le> 2 ^ n)"

lemma msg_align_bits:
  "msg_align_bits = 9"
proof -
  have "(LEAST n. (cap_transfer_data_size + msg_max_length + msg_max_extra_caps + 2) \<le> 2 ^ n) = 7"
  proof (rule Least_equality)
    show "(cap_transfer_data_size + msg_max_length + msg_max_extra_caps + 2)  \<le> 2 ^ 7"
      by (simp add: cap_transfer_data_size_def msg_max_length_def msg_max_extra_caps_def)
  next
    fix y
    assume "(cap_transfer_data_size + msg_max_length + msg_max_extra_caps + 2) \<le> 2 ^ y"
    hence "(2 :: nat) ^ 7 \<le> 2 ^ y"
      by (simp add: cap_transfer_data_size_def msg_max_length_def msg_max_extra_caps_def)
    thus "7 \<le> y"
      by (rule power_le_imp_le_exp [rotated], simp)
  qed
  thus ?thesis unfolding msg_align_bits_def by simp
qed

definition
check_valid_ipc_buffer :: "vspace_ref \<Rightarrow> cap \<Rightarrow> (unit,'z::state_ext) se_monad" where
"check_valid_ipc_buffer vptr c \<equiv> case c of
  (ArchObjectCap (PageCap _ _ magnitude _)) \<Rightarrow> doE
    whenE (\<not> is_aligned vptr msg_align_bits) $ throwError AlignmentError;
    returnOk ()
  odE
| _ \<Rightarrow> throwError IllegalOperation"

text {* On the abstract level, capability and VM rights share the same type.
  Nevertheless, a simple set intersection might lead to an invalid value like
  @{term "{AllowWrite}"}.  Hence, @{const validate_vm_rights}. *}
definition
  mask_vm_rights :: "vm_rights \<Rightarrow> cap_rights \<Rightarrow> vm_rights" where
  "mask_vm_rights V R \<equiv> validate_vm_rights (V \<inter> R)"

text {* Decode a user argument word describing the kind of VM attributes a
mapping is to have. *}
definition
attribs_from_word :: "word32 \<Rightarrow> vm_attributes" where
"attribs_from_word w \<equiv>
  let V = (if w !!0 then {PageCacheable} else {});
      V' = (if w!!1 then insert ParityEnabled V else V)
  in if w!!2 then insert XNever V' else V'"

text {* Update the mapping data saved in a page or page table capability. *}
definition
  update_map_data :: "arch_cap \<Rightarrow> (mapping_root \<times> vspace_ref) option \<Rightarrow> arch_cap" where
  "update_map_data cap m \<equiv> case cap of PageCap p R sz _ \<Rightarrow> PageCap p R sz m
                                     | PageTableCap l p _ \<Rightarrow> PageTableCap l p m"

text {* Get information about the frame of a given virtual address *}
(* FIXME ARMHYP want another pair of eyes on this; want to generalise these, not nest them *)
definition
  resolve_vaddr :: "word32 \<Rightarrow> vspace_ref \<Rightarrow> ((vmpage_size \<times> obj_ref) option, 'z::state_ext) s_monad"
where
  "resolve_vaddr root_pt va \<equiv> do
    pt_slot \<leftarrow> return $ pte_slot PT_L1 root_pt va;
    pte \<leftarrow> get_pte pt_slot;
    case pte of
      Block_1G_PTE _ _ _ \<Rightarrow> (return $ Some (ARM_1G_Block, addr_from_pte pte))
    | TablePTE _ _ \<Rightarrow> do
        pt_slot \<leftarrow> return $ pte_slot PT_L2 (addr_from_pte pte) va;
        pte \<leftarrow> get_pte pt_slot;
        case pte of
          Block_2M_PTE _ _ _ \<Rightarrow> (return $ Some (ARM_2M_Block, addr_from_pte pte))
        | TablePTE _ _ \<Rightarrow> do
            pt_slot \<leftarrow> return $ pte_slot PT_L2 (addr_from_pte pte) va;
            pte \<leftarrow> get_pte pt_slot;
            case pte of
              PagePTE _ _ _ \<Rightarrow> (return $ Some (ARM_4K_Page, addr_from_pte pte))
              | _ \<Rightarrow> return None
          od
        | _ \<Rightarrow> return None
      od
    | _ \<Rightarrow> return None
  od"

text {*
  A pointer is inside a user frame if its top bits point to a @{text DataPage}.
*}
definition
  in_user_frame :: "word32 \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" where
  "in_user_frame p s \<equiv>
   \<exists>sz. kheap s (p && ~~ mask (pageBitsForSize sz)) =
        Some (ArchObj (DataPage sz))"           

end
