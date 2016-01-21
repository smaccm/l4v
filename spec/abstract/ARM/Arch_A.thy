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
Entry point for architecture dependent definitions.
*)

chapter "Toplevel ARM Definitions"

theory Arch_A
imports "../TcbAcc_A"
begin

definition "page_bits \<equiv> pageBits"

text {* The ARM architecture does not provide any additional operations on its
interrupt controller. *}
definition
  arch_invoke_irq_control :: "arch_irq_control_invocation \<Rightarrow> (unit,'z::state_ext) p_monad" where
  "arch_invoke_irq_control aic \<equiv> fail"

text {* Switch to a thread's virtual address space context and write its IPC
buffer pointer into the globals frame. Clear the load-exclusive monitor. *}
definition
  arch_switch_to_thread :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "arch_switch_to_thread t \<equiv> do
     set_vm_root t;
     globals \<leftarrow> gets (arm_globals_frame \<circ> arch_state);
     buffer_ptr \<leftarrow> thread_get tcb_ipc_buffer t;
     do_machine_op $ storeWord globals buffer_ptr;
     do_machine_op $ clearExMonitor
   od"

text {* The idle thread does not need to be handled specially on ARM. *}
(* Clear the globals frame when switching to the idle thread. This is
    specificially to ease infoflow reasoning VER-207 *)
definition
   arch_switch_to_idle_thread :: "(unit,'z::state_ext) s_monad" where
   "arch_switch_to_idle_thread \<equiv> do
      globals \<leftarrow> gets (arm_globals_frame \<circ> arch_state);
      do_machine_op $ storeWord globals 0
    od"

definition
  arch_activate_idle_thread :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "arch_activate_idle_thread t \<equiv> return ()"

text {* The ASIDControl capability confers the authority to create a new ASID
pool object. This operation creates the new ASID pool, provides a capability
to it and connects it to the global virtual ASID table. *}
definition
perform_asid_control_invocation :: "asid_control_invocation \<Rightarrow> (unit,'z::state_ext) s_monad" where
"perform_asid_control_invocation iv \<equiv> case iv of
  MakePool frame slot parent base \<Rightarrow> do
    delete_objects frame page_bits;
    pcap \<leftarrow> get_cap parent;
    set_cap (max_free_index_update pcap) parent;
    retype_region frame 1 0 (ArchObject ASIDPoolObj);
    cap_insert (ArchObjectCap $ ASIDPoolCap frame base) parent slot;
    assert (base && mask asid_low_bits = 0);
    asid_table \<leftarrow> gets (arm_asid_table \<circ> arch_state);
    asid_table' \<leftarrow> return (asid_table (asid_high_bits_of base \<mapsto> frame));
    modify (\<lambda>s. s \<lparr>arch_state := (arch_state s) \<lparr>arm_asid_table := asid_table'\<rparr>\<rparr>)
od"

text {* The ASIDPool capability confers the authority to assign a virtual ASID
to a page directory. *}
definition
perform_asid_pool_invocation :: "asid_pool_invocation \<Rightarrow> (unit,'z::state_ext) s_monad" where
"perform_asid_pool_invocation iv \<equiv> case iv of Assign asid pool_ptr ct_slot \<Rightarrow> 
do
    pt_cap \<leftarrow> get_cap ct_slot;
    case pt_cap of
      ArchObjectCap (PageTableCap PT_L1 pt _) \<Rightarrow> do
        pool \<leftarrow> get_asid_pool pool_ptr;
        pool' \<leftarrow> return (pool (ucast asid \<mapsto> pt));
        set_cap (ArchObjectCap $ PageTableCap PT_L1 pt (Some (MappedMem asid, 0))) ct_slot;
        set_asid_pool pool_ptr pool'
      od
    | _ \<Rightarrow> fail
od"

text {* The PageDirectory capability confers the authority to flush cache entries
associated with that PD *}
definition
  perform_page_directory_invocation :: "page_directory_invocation \<Rightarrow> (unit,'z::state_ext) s_monad" 
where
  "perform_page_directory_invocation iv \<equiv> case iv of
       PageDirectoryFlush typ start end pstart pd asid \<Rightarrow> 
         when (start < end) $ do
           root_switched \<leftarrow> set_vm_root_for_flush pd asid;
           do_machine_op $ do_flush typ start end pstart;
           when root_switched $ do
             tcb \<leftarrow> gets cur_thread;
             set_vm_root tcb
           od
        od
     | PageDirectoryNothing \<Rightarrow> return ()"

definition
  pte_check_if_mapped :: "32 word \<Rightarrow> (bool, 'z::state_ext) s_monad"
where
  "pte_check_if_mapped slot \<equiv> do
     pt \<leftarrow> get_pte slot;
     return (pt \<noteq> InvalidPTE)
  od"

definition
  set_message_info :: "obj_ref \<Rightarrow> message_info \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "set_message_info thread info \<equiv>
     as_user thread $ set_register msg_info_register $
                      message_info_to_data info"


text {* The Page capability confers the authority to map, unmap and flush the
memory page. The remap system call is a convenience operation that ensures the
page is mapped in the same location as this cap was previously used to map it
in. *}
definition
perform_page_invocation :: "page_invocation \<Rightarrow> (unit,'z::state_ext) s_monad" where
"perform_page_invocation iv \<equiv> case iv of
  PageMap cap ct_slot entry m \<Rightarrow> let (pte, slot) = entry in do
    flush \<leftarrow> pte_check_if_mapped slot;
    set_cap cap ct_slot;
    store_pte slot pte;
    do_machine_op $ cleanCacheRange_PoU slot slot (addrFromPPtr slot);
    if flush then (invalidate_tlb_by_mapping_root m) else return ()
  od
| PageRemap entry m \<Rightarrow> let (pte, slot) = entry in do
    flush \<leftarrow> pte_check_if_mapped slot;
    store_pte slot pte;
    do_machine_op $ cleanCacheRange_PoU slot slot (addrFromPPtr slot);
    if flush then (invalidate_tlb_by_mapping_root m) else return ()
  od
| PageUnmap cap ct_slot \<Rightarrow> case cap of
      PageCap p R vp_size vp_mapped_addr \<Rightarrow> do
        case vp_mapped_addr of
            Some (m, vaddr) \<Rightarrow> unmap_page vp_size m vaddr p
          | None \<Rightarrow> return ();
        cap \<leftarrow> liftM the_arch_cap $ get_cap ct_slot;
        set_cap (ArchObjectCap $ update_map_data cap None) ct_slot
      od
    | _ \<Rightarrow> fail
| PageFlush typ start end pstart pd asid \<Rightarrow>
    when (start < end) $ do
      root_switched \<leftarrow> set_vm_root_for_flush pd asid;
      do_machine_op $ do_flush typ start end pstart;
      when root_switched $ do
        tcb \<leftarrow> gets cur_thread;
        set_vm_root tcb
      od
   od
| PageGetAddr ptr \<Rightarrow> do
    ct \<leftarrow> gets cur_thread;
    n_msg \<leftarrow> set_mrs ct None [addrFromPPtr ptr];
    set_message_info ct $ MI n_msg 0 0 0
  od"

text {* PageTable capabilities confer the authority to map and unmap page tables. *}
definition
perform_page_table_invocation :: "page_table_invocation \<Rightarrow> (unit,'z::state_ext) s_monad" where
"perform_page_table_invocation iv \<equiv> case iv of
    PageTableMap cap ct_slot pte pt_slot \<Rightarrow> do
      set_cap cap ct_slot;
      store_pte pt_slot pte;
      do_machine_op $ cleanByVA_PoU pt_slot (addrFromPPtr pt_slot)
    od
  | PageTableUnmap (ArchObjectCap (PageTableCap l p mapped_address)) ct_slot \<Rightarrow> do
      case mapped_address of
      Some (m_root, vaddr) \<Rightarrow> do
        unmap_page_table m_root vaddr l p;
        pte_bits \<leftarrow> return 3;
        slots \<leftarrow> return [p, p + (1 << pte_bits) .e. p + (1 << pt_bits) - 1];
        mapM_x (swp store_pte InvalidPTE) slots;
        do_machine_op $ cleanCacheRange_PoU p (p + (1 << pt_bits) - 1) (addrFromPPtr p)
      od
      | None \<Rightarrow> return ();
    cap \<leftarrow> liftM the_arch_cap $ get_cap ct_slot;
    set_cap (ArchObjectCap $ update_map_data cap None) ct_slot
  od
  | _ \<Rightarrow> fail"

definition
  vcpu_read_register :: "obj_ref \<Rightarrow> hyper_reg \<Rightarrow> (machine_word,'z::state_ext) s_monad"
where
  "vcpu_read_register vcpu reg \<equiv> do
    (_,regs) \<leftarrow> get_vcpu vcpu;
    return $ regs reg
  od"

text {*
  Some parts of some registers cannot be written by the user.
  Bits set in the mask will be preserved.
*}
consts
  register_mask :: "hyper_reg \<Rightarrow> machine_word option"

definition
  vcpu_write_register :: "obj_ref \<Rightarrow> hyper_reg \<Rightarrow> machine_word \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "vcpu_write_register vcpu reg val \<equiv>  do
    (tcb_opt,regs) \<leftarrow> get_vcpu vcpu;
    val' \<leftarrow> return (case register_mask reg of
              None \<Rightarrow> val
            | Some m \<Rightarrow> regs reg && m || val && ~~m);
    set_vcpu vcpu (tcb_opt,regs(reg := val'))
  od"

text {* VCPU objects can be associated with and dissociated from TCBs. *}
definition
perform_vcpu_invocation :: "vcpu_invocation \<Rightarrow> (machine_word list,'z::state_ext) s_monad" where
"perform_vcpu_invocation iv \<equiv> case iv of
    VCPUDissociate vcpu \<Rightarrow> do dissociate_vcpu vcpu; return [] od
  | VCPUAssociate vcpu tcb \<Rightarrow> do associate vcpu tcb; return [] od
  | VCPUReadRegister vcpu reg \<Rightarrow> do val \<leftarrow> vcpu_read_register vcpu reg; return [val] od
  | VCPUWriteRegister vcpu reg val \<Rightarrow> do vcpu_write_register vcpu reg val; return [] od"

text {* IOSpace capabilities map and unmap page tables to and from devices. *}
definition
perform_io_space_invocation :: "io_space_invocation \<Rightarrow> (unit,'z::state_ext) s_monad" where
"perform_io_space_invocation iv \<equiv> case iv of
    IOSpaceMap dev pt pt_slot \<Rightarrow> do
      set_cap (ArchObjectCap $ PageTableCap PT_L1 pt (Some (MappedIO dev, 0))) pt_slot;
      map_device dev pt
    od
  | IOSpaceUnmap dev \<Rightarrow> unmap_device dev"

text {* Top level system call despatcher for all ARM-specific system calls. *}
definition
  arch_perform_invocation :: "arch_invocation \<Rightarrow> (data list,'z::state_ext) p_monad" where
  "arch_perform_invocation i \<equiv> liftE $
    case i of
          InvokePageTable oper \<Rightarrow> do perform_page_table_invocation oper; return [] od
        | InvokePage oper \<Rightarrow> do perform_page_invocation oper; return [] od
        | InvokeASIDControl oper \<Rightarrow> do perform_asid_control_invocation oper; return [] od
        | InvokeASIDPool oper \<Rightarrow> do perform_asid_pool_invocation oper; return [] od
        | InvokeVCPU oper \<Rightarrow> perform_vcpu_invocation oper
        | InvokeIOSpace oper \<Rightarrow> do perform_io_space_invocation oper; return [] od"

end
