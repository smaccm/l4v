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
Decoding system calls
*)

chapter "Decoding Architecture-specific System Calls"

theory ArchDecode_A
imports
  "../Interrupt_A"
  "../InvocationLabels_A"
  "../../../lib/WordLib"
begin

section "Helper definitions"

text {* This definition ensures that the given pointer is aligned
to the given page size. *}

definition
  check_vp_alignment :: "vmpage_size \<Rightarrow> word32 \<Rightarrow> (unit,'z::state_ext) se_monad" where
  "check_vp_alignment sz vptr \<equiv>
     unlessE (is_aligned vptr (pageBitsForSize sz)) $
       throwError AlignmentError"

text {* This definition converts a user-supplied argument into an
invocation label, used to determine the method to invoke. 
*}

definition
  label_to_flush_type :: "invocation_label \<Rightarrow> flush_type"
where
  "label_to_flush_type label \<equiv> case label of
       ArchInvocationLabel ARMPDClean_Data \<Rightarrow> Clean
     | ArchInvocationLabel ARMPageClean_Data \<Rightarrow> Clean
     | ArchInvocationLabel ARMPDInvalidate_Data \<Rightarrow> Invalidate
     | ArchInvocationLabel ARMPageInvalidate_Data \<Rightarrow> Invalidate
     | ArchInvocationLabel ARMPDCleanInvalidate_Data \<Rightarrow> CleanInvalidate
     | ArchInvocationLabel ARMPageCleanInvalidate_Data \<Rightarrow> CleanInvalidate
     | ArchInvocationLabel ARMPDUnify_Instruction \<Rightarrow> Unify
     | ArchInvocationLabel ARMPageUnify_Instruction \<Rightarrow> Unify"

section "Architecture calls"

text {* This definition decodes architecture-specific invocations.
*}

 definition
  table_addr_from_ref :: "obj_ref \<Rightarrow> 20 word"
where
  "table_addr_from_ref r \<equiv> ucast ((addrFromPPtr r) >> ptBits)"

definition max_hyper_reg :: machine_word where
  "max_hyper_reg \<equiv> of_nat (fromEnum (maxBound::hyper_reg))"

definition
  arch_decode_invocation :: 
  "data \<Rightarrow> data list \<Rightarrow> cap_ref \<Rightarrow> cslot_ptr \<Rightarrow> arch_cap \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow> 
   (arch_invocation,'z::state_ext) se_monad"
where
"arch_decode_invocation label args x_slot cte cap extra_caps \<equiv> case cap of
  PageTableCap PT_L1 _ _ \<Rightarrow> throwError IllegalOperation
| PageTableCap level p mapped_address \<Rightarrow> 
    if invocation_type label = ArchInvocationLabel ARMPageTableMap then
    if length args > 1 \<and> length extra_caps > 0
    then let vaddr = args ! 0;
             attr = args ! 1;
             pt'_cap = fst (extra_caps ! 0)
    in doE
            whenE (mapped_address \<noteq> None) $ throwError $ InvalidCapability 0;
            (level',pt',m_root) \<leftarrow> (case pt'_cap of
                            ArchObjectCap (PageTableCap level' pt' (Some (m_root,_))) \<Rightarrow> 
                              if level' = pred_level level then
                                 returnOk (level',pt',m_root)
                              else
                                 throwError $ InvalidCapability 1
                         | _ \<Rightarrow> throwError $ InvalidCapability 1);
            whenE (vaddr \<ge> kernel_base) $ throwError $ InvalidArgument 0;
            check_pt' \<leftarrow> lookup_error_on_failure False $ find_root_pt m_root;
            whenE (check_pt' \<noteq> pt') $ throwError $ InvalidCapability 1;
            pt_slot \<leftarrow> returnOk $ pte_slot level' pt' vaddr;
            vaddr' \<leftarrow> returnOk (vaddr && ~~ mask (level_bits level));
            old_pte \<leftarrow> liftE $ get_pte pt_slot;
            unlessE (old_pte = InvalidPTE) $ throwError DeleteFirst;
            pte \<leftarrow> returnOk (TablePTE (table_addr_from_ref p)
                                      (attribs_from_word attr \<inter> {ParityEnabled}));
            returnOk $ InvokePageTable $ 
                PageTableMap
                (ArchObjectCap $ PageTableCap level p (Some (m_root, vaddr')))
                cte pte pt_slot
    odE
    else throwError TruncatedMessage
    else if invocation_type label = ArchInvocationLabel ARMPageTableUnmap
    then doE
            final \<leftarrow> liftE $ is_final_cap (ArchObjectCap cap);
            unlessE final $ throwError RevokeFirst;
            returnOk $ InvokePageTable $ PageTableUnmap (ArchObjectCap cap) cte
    odE
    else throwError IllegalOperation
| PageCap p R pgsz mapped_address \<Rightarrow>
    if invocation_type label = ArchInvocationLabel ARMPageMap then
    if length args > 2 \<and> length extra_caps > 0
    then let vaddr = args ! 0;
             rights_mask = args ! 1;
             attr = args ! 2;
             pt_cap = fst (extra_caps ! 0)
        in doE
            whenE (mapped_address \<noteq> None) $ throwError $ InvalidCapability 0;
            (pt,m_root) \<leftarrow> (case pt_cap of
                              ArchObjectCap (PageTableCap PT_L1 pt (Some (m_root,_))) \<Rightarrow> 
                                returnOk (pt,m_root)
                           | _ \<Rightarrow> throwError $ InvalidCapability 1);
            pt' \<leftarrow> lookup_error_on_failure False $ find_root_pt m_root;
            whenE (pt' \<noteq> pt) $ throwError $ InvalidCapability 1;
            vtop \<leftarrow> returnOk (vaddr + (1 << (pageBitsForSize pgsz)) - 1);
            whenE (vtop \<ge> kernel_base) $ throwError $ InvalidArgument 0;
            vm_rights \<leftarrow> returnOk (mask_vm_rights R (data_to_rights rights_mask));
            check_vp_alignment pgsz vaddr;
            entry \<leftarrow> create_mapping_entry (addrFromPPtr p)
                                            vaddr pgsz vm_rights
                                            (attribs_from_word attr) pt;
            ensure_safe_mapping entry;
            returnOk $ InvokePage $ PageMap
                (ArchObjectCap $ PageCap p R pgsz (Some (m_root, vaddr)))
                cte entry m_root
        odE
    else throwError TruncatedMessage
    else if invocation_type label = ArchInvocationLabel ARMPageRemap then
         if length args > 1 \<and> length extra_caps > 0
         then let rights_mask = args ! 0;
                  attr = args ! 1;
                  pt_cap = fst (extra_caps ! 0)
         in doE
            (pt,m_root) \<leftarrow> (case pt_cap of
                              ArchObjectCap (PageTableCap PT_L1 pt (Some (m_root, _))) \<Rightarrow> 
                                returnOk (pt,m_root)
                           | _ \<Rightarrow> throwError $ InvalidCapability 1);
            (m_root', vaddr) \<leftarrow> (case mapped_address of
                  Some m \<Rightarrow> returnOk m
                | _ \<Rightarrow> throwError $ InvalidCapability 0);
            pt' \<leftarrow> lookup_error_on_failure False $ find_root_pt m_root';
            whenE (pt' \<noteq> pt \<or> m_root' \<noteq> m_root) $ throwError $ InvalidCapability 1;  
            vm_rights \<leftarrow> returnOk (mask_vm_rights R $ data_to_rights rights_mask);
            check_vp_alignment pgsz vaddr;
            entry \<leftarrow> create_mapping_entry (addrFromPPtr p)
                                          vaddr pgsz vm_rights
                                          (attribs_from_word attr) pt;
            ensure_safe_mapping entry;
            returnOk $ InvokePage $ PageRemap entry m_root
        odE
    else  throwError TruncatedMessage
    else if invocation_type label = ArchInvocationLabel ARMPageUnmap
    then  returnOk $ InvokePage $ PageUnmap cap cte
    else if isPageFlushLabel (invocation_type label) then
        if length args > 1
        then let start = args ! 0;
                 end = args ! 1
        in doE
            (asid, vaddr) \<leftarrow> (case mapped_address of
                Some (MappedMem asid, vaddr) \<Rightarrow> returnOk (asid, vaddr)
              | _ \<Rightarrow> throwError IllegalOperation);
            pt \<leftarrow> lookup_error_on_failure False $ find_pt_for_asid asid;
            whenE (end \<le> start) $ throwError $ InvalidArgument 1;
            page_size \<leftarrow> returnOk $ 1 << pageBitsForSize pgsz;
            whenE (start \<ge> page_size \<or> end > page_size) $ throwError $ InvalidArgument 0;
            returnOk $ InvokePage $ PageFlush
                (label_to_flush_type (invocation_type label)) (start + vaddr)
                (end + vaddr - 1) (addrFromPPtr p + start) pt asid
    odE
    else throwError TruncatedMessage
    else if invocation_type label = ArchInvocationLabel ARMPageGetAddress
    then returnOk $ InvokePage $ PageGetAddr p
  else  throwError IllegalOperation
| ASIDControlCap \<Rightarrow>
    if invocation_type label = ArchInvocationLabel ARMASIDControlMakePool then
    if length args > 1 \<and> length extra_caps > 1
    then let index = args ! 0;
             depth = args ! 1;
             (untyped, parent_slot) = extra_caps ! 0;
             root = fst (extra_caps ! 1)
         in doE
            asid_table \<leftarrow> liftE $ gets (arm_asid_table \<circ> arch_state);
            free_set \<leftarrow> returnOk (- dom asid_table \<inter> {x. x \<le> 2 ^ asid_high_bits - 1});
            whenE (free_set = {}) $ throwError DeleteFirst;
            free \<leftarrow> liftE $ select_ext (\<lambda>_. free_asid_select asid_table) free_set;
            base \<leftarrow> returnOk (ucast free << asid_low_bits);
            (p,n) \<leftarrow> (case untyped of UntypedCap p n f \<Rightarrow> returnOk (p,n) 
                                    | _ \<Rightarrow> throwError $ InvalidCapability 1);
            frame \<leftarrow> (if n = pageBits
                      then doE
                        ensure_no_children parent_slot;
                        returnOk p
                      odE
                      else  throwError $ InvalidCapability 1);
            dest_slot \<leftarrow> lookup_target_slot root (to_bl index) (unat depth);
            ensure_empty dest_slot;
            returnOk $ InvokeASIDControl $ MakePool frame dest_slot parent_slot base
        odE
    else  throwError TruncatedMessage
    else  throwError IllegalOperation
| ASIDPoolCap p base \<Rightarrow>
  if invocation_type label = ArchInvocationLabel ARMASIDPoolAssign then
  if length extra_caps > 0
  then
    let (pt_cap, pt_cap_slot) = extra_caps ! 0
     in case pt_cap of
          ArchObjectCap (PageTableCap PT_L1 _ None) \<Rightarrow> doE
            asid_table \<leftarrow> liftE $ gets (arm_asid_table \<circ> arch_state);
            pool_ptr \<leftarrow> returnOk (asid_table (asid_high_bits_of base));
            whenE (pool_ptr = None) $ throwError $ FailedLookup False InvalidRoot;
            whenE (p \<noteq> the pool_ptr) $ throwError $ InvalidCapability 0;
            pool \<leftarrow> liftE $ get_asid_pool p;
            free_set \<leftarrow> returnOk 
                   (- dom pool \<inter> {x. x \<le> 2 ^ asid_low_bits - 1 \<and> ucast x + base \<noteq> 0});
            whenE (free_set = {}) $ throwError DeleteFirst;
            offset \<leftarrow> liftE $ select_ext (\<lambda>_. free_asid_pool_select pool base) free_set;
            returnOk $ InvokeASIDPool $ Assign (ucast offset + base) p pt_cap_slot
          odE
        | _ \<Rightarrow>  throwError $ InvalidCapability 1
  else  throwError TruncatedMessage
  else  throwError IllegalOperation
| VCPUCap vcpu_ref \<Rightarrow>
    if invocation_type label = ArchInvocationLabel ARMVCPUDissociate then
      returnOk $ InvokeVCPU $ VCPUDissociate vcpu_ref
    else if invocation_type label = ArchInvocationLabel ARMVCPUAssociate then
      if length extra_caps > 0 then
      let (tcb_cap, _) = extra_caps ! 0 in
      case tcb_cap of
        ThreadCap tcb_ref \<Rightarrow> doE
          (tcb_opt, _) \<leftarrow> liftE $ get_vcpu vcpu_ref;
          whenE (tcb_opt \<noteq> None) $ throwError DeleteFirst;
          vcpu_opt \<leftarrow> liftE $ thread_get tcb_vcpu tcb_ref;
          whenE (vcpu_opt \<noteq> None) $ throwError DeleteFirst;
          returnOk $ InvokeVCPU $ VCPUAssociate vcpu_ref tcb_ref
        odE
      | _ \<Rightarrow> throwError $ InvalidCapability 1
      else throwError TruncatedMessage
    else if invocation_type label = ArchInvocationLabel ARMVCPUReadRegister then
    case args of
      reg # _ \<Rightarrow> doE
        whenE (reg > max_hyper_reg) $ throwError $ RangeError 0 max_hyper_reg;
        returnOk $ InvokeVCPU $ VCPUReadRegister vcpu_ref (toEnum (unat reg))
      odE
    | _ \<Rightarrow> throwError TruncatedMessage
    else if invocation_type label = ArchInvocationLabel ARMVCPUWriteRegister then
    case args of
      reg # val # _ \<Rightarrow> doE
        whenE (reg > max_hyper_reg) $ throwError $ RangeError 0 max_hyper_reg;
        returnOk $ InvokeVCPU $ VCPUWriteRegister vcpu_ref (toEnum (unat reg)) val
      odE
    | _ \<Rightarrow> throwError TruncatedMessage
    else throwError IllegalOperation
| IOSpaceCap (Some dev) \<Rightarrow> 
    if invocation_type label = ArchInvocationLabel ARMIOSpaceMap then
      if length extra_caps > 0 then
      let (pt_cap, pt_slot) = extra_caps ! 0 in
        case pt_cap of
          ArchObjectCap (PageTableCap PT_L1 pt None) \<Rightarrow> doE
            pt_opt \<leftarrow> liftE $ get_io_pt dev;
            whenE (pt_opt \<noteq> None) $ throwError DeleteFirst;
            returnOk $ InvokeIOSpace $ IOSpaceMap dev pt pt_slot
          odE
        | _ \<Rightarrow> throwError $ InvalidCapability 1
      else throwError TruncatedMessage
    else if invocation_type label = ArchInvocationLabel ARMIOSpaceUnmap then
      returnOk $ InvokeIOSpace $ IOSpaceUnmap dev
    else throwError IllegalOperation
| IOSpaceCap _ \<Rightarrow> throwError IllegalOperation"

text "ARM does not support additional interrupt control operations"
definition
  arch_decode_irq_control ::
  "data \<Rightarrow> data list \<Rightarrow> cslot_ptr \<Rightarrow> cap list \<Rightarrow> (arch_irq_control_invocation,'z::state_ext) se_monad" where
  "arch_decode_irq_control label args src_slot cps \<equiv> throwError IllegalOperation"

definition
  arch_data_to_obj_type :: "nat \<Rightarrow> aobject_type option" where
 "arch_data_to_obj_type \<equiv>
 [ 0 \<mapsto> ARM_4K_PageObj,
   1 \<mapsto> ARM_2M_BlockObj,
   2 \<mapsto> ARM_1G_BlockObj,
   3 \<mapsto> PageTableObj PT_L3,
   4 \<mapsto> PageTableObj PT_L2,
   5 \<mapsto> PageTableObj PT_L1 ]"

end
