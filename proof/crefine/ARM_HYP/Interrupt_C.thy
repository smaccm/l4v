(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory Interrupt_C
imports CSpace_All Finalise_C
begin

context kernel_m begin

lemma invokeIRQHandler_AckIRQ_ccorres:
  "ccorres dc xfdc
       invs' (UNIV \<inter> {s. irq_' s = ucast irq}) []
     (invokeIRQHandler (AckIRQ irq)) (Call invokeIRQHandler_AckIRQ_'proc)"
  apply (cinit lift: irq_')
   apply (ctac add: maskInterrupt_ccorres)
  apply (simp add: from_bool_def false_def)
  done

lemma getIRQSlot_ccorres:
  "ccorres (op = \<circ> Ptr) irqSlot_'
          \<top> UNIV hs
      (getIRQSlot irq) 
      (\<acute>irqSlot :== CTypesDefs.ptr_add \<acute>intStateIRQNode (sint (ucast (ucast irq ::word16) :: 32 signed word)))"
  apply (rule ccorres_from_vcg[where P=\<top> and P'=UNIV])
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp: getIRQSlot_def liftM_def getInterruptState_def
                        locateSlot_conv)
  apply (simp add: simpler_gets_def bind_def return_def)
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                        cinterrupt_relation_def size_of_def
                        sint_ucast_eq_uint is_down of_int_uint_ucast
                        cte_level_bits_def mult.commute mult.left_commute ucast_nat_def
                        )
  apply (simp add:ucast_up_ucast is_up)
  done

lemma ptr_add_assertion_irq_guard:
"ccorres dc xfdc P Q hs a
     (Guard F
       \<lbrace>uint irq = 0 \<or> array_assertion \<acute>intStateIRQNode (nat (uint irq)) (hrs_htd \<acute>t_hrs)\<rbrace>
       c;;m)
  \<Longrightarrow> ccorres dc xfdc P Q hs a
            (Guard F
              \<lbrace>ptr_add_assertion \<acute>intStateIRQNode 
                (sint (ucast (irq :: 16 word)::32 signed word)) False
                (hrs_htd \<acute>t_hrs)\<rbrace> c ;; m)"
  by (simp add: ptr_add_assertion_def sint_ucast_eq_uint is_down)


lemma cte_at_irq_node':
  "invs' s \<Longrightarrow>
    cte_at' (irq_node' s + 2 ^ cte_level_bits * ucast (irq :: 10 word)) s"
  by (clarsimp simp: invs'_def valid_state'_def valid_irq_node'_def
                     cte_level_bits_def real_cte_at')

lemma invokeIRQHandler_SetIRQHandler_ccorres:
  "ccorres dc xfdc
          (invs' and sch_act_simple 
            and irq_handler_inv_valid' (SetIRQHandler irq cp slot))
          (UNIV \<inter> {s. irq_' s = ucast irq} \<inter> {s. slot_' s = Ptr slot}
                \<inter> {s. ccap_relation cp (cap_' s)}) []
      (invokeIRQHandler (SetIRQHandler irq cp slot))
      (Call invokeIRQHandler_SetIRQHandler_'proc)"
proof -
  have valid_objs_invs'_strg: "\<And>s. invs' s \<longrightarrow> valid_objs' s"
    by (clarsimp)
  show ?thesis
  apply (cinit lift: irq_' slot_' cap_')
   apply (rule ptr_add_assertion_irq_guard)
   apply (rule ccorres_move_array_assertion_irq)
   apply (simp only:)
   apply (ctac(no_vcg) add: getIRQSlot_ccorres)
     apply (rule ccorres_symb_exec_r)
       apply (ctac(no_vcg) add: cteDeleteOne_ccorres[where w="-1"])
        apply (ctac(no_vcg) add: cteInsert_ccorres)
       apply (simp add: pred_conj_def)
       apply (strengthen ntfn_badge_derived_enough_strg[unfolded o_def]
                         invs_mdb_strengthen' valid_objs_invs'_strg)
       apply (wp cteDeleteOne_other_cap[unfolded o_def])[1]
      apply vcg
     apply (rule conseqPre, vcg, clarsimp simp: rf_sr_def
        gs_set_assn_Delete_cstate_relation[unfolded o_def])
    apply (simp add: getIRQSlot_def getInterruptState_def locateSlot_conv)
    apply wp
   apply (simp add: guard_is_UNIV_def ghost_assertion_data_get_def
                    ghost_assertion_data_set_def)
  apply (clarsimp simp: cte_at_irq_node' ucast_nat_def)
  apply (clarsimp simp: invs_pspace_aligned' cte_wp_at_ctes_of badge_derived'_def
                        Collect_const_mem unat_gt_0 valid_cap_simps' ARM_HYP.maxIRQ_def)
  apply (drule word_le_nat_alt[THEN iffD1])
  apply (clarsimp simp:uint_0_iff unat_gt_0 uint_up_ucast is_up unat_def[symmetric])
  apply (drule valid_globals_ex_cte_cap_irq[where irq=irq])
  apply (auto simp add:Word.uint_up_ucast is_up unat_def[symmetric])
  done
qed

lemma invokeIRQHandler_ClearIRQHandler_ccorres:
  "ccorres dc xfdc
          (invs' and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s) and K(irq \<le> 0xFF))
          (UNIV \<inter> {s. irq_' s = ucast irq}) []
      (invokeIRQHandler (ClearIRQHandler irq))
      (Call invokeIRQHandler_ClearIRQHandler_'proc)"
  apply (cinit lift: irq_')
   apply (rule ptr_add_assertion_irq_guard)
   apply (rule ccorres_move_array_assertion_irq)
   apply (simp only: )
   apply (ctac(no_vcg) add: getIRQSlot_ccorres)
     apply (rule ccorres_symb_exec_r)
       apply (ctac add: cteDeleteOne_ccorres[where w="-1"])
      apply vcg
     apply (rule conseqPre, vcg, clarsimp simp: rf_sr_def
        gs_set_assn_Delete_cstate_relation[unfolded o_def])
    apply (simp add: getIRQSlot_def getInterruptState_def locateSlot_conv)
    apply wp
   apply (simp add: guard_is_UNIV_def ghost_assertion_data_get_def
                    ghost_assertion_data_set_def)
  apply (clarsimp simp: cte_at_irq_node' ucast_nat_def)
  apply (drule word_le_nat_alt[THEN iffD1])
  apply (auto simp add:Word.uint_up_ucast is_up unat_def[symmetric])
  done

lemma ntfn_case_can_send:
  "(case cap of NotificationCap x1 x2 x3 x4 \<Rightarrow> f x3
        | _ \<Rightarrow> v) = (if isNotificationCap cap then f (capNtfnCanSend cap)
                     else v)"
  by (cases cap, simp_all add: isCap_simps)

lemma list_length_geq_helper[simp]:
  "\<lbrakk>\<not> length args < 2\<rbrakk>
       \<Longrightarrow> \<exists>y ys. args = y # ys"
  by (frule length_ineq_not_Nil(3), simp, metis list.exhaust)

lemma decodeIRQHandlerInvocation_ccorres:
  notes if_cong[cong]
  shows
  "interpret_excaps extraCaps' = excaps_map extraCaps \<Longrightarrow>
   ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread) 
              and ct_active' and sch_act_simple
              and (excaps_in_mem extraCaps o ctes_of)
              and (\<lambda>s. \<exists>slot. cte_wp_at' (\<lambda>cte. cteCap cte = IRQHandlerCap irq) slot s)
              and (\<lambda>s. \<forall>v \<in> set extraCaps.
                             ex_cte_cap_wp_to' isCNodeCap (snd v) s))
       (UNIV
            \<inter> {s. invLabel_' s = label}  
            \<inter> {s. irq_' s = ucast irq}
            \<inter> {s. excaps_' s = extraCaps'}) []
     (decodeIRQHandlerInvocation label irq extraCaps
            >>= invocationCatch thread isBlocking isCall InvokeIRQHandler)
     (Call decodeIRQHandlerInvocation_'proc)"
  apply (cinit' lift: invLabel_' irq_' excaps_' 
           simp: decodeIRQHandlerInvocation_def invocation_eq_use_types)
   apply (rule ccorres_Cond_rhs)
    apply (simp add: returnOk_bind ccorres_invocationCatch_Inr)
    apply (rule ccorres_rhs_assoc)+
    apply (simp add: performInvocation_def bindE_assoc, simp add: liftE_bindE)
    apply (ctac(no_vcg) add: setThreadState_ccorres)
     apply (ctac(no_vcg) add: invokeIRQHandler_AckIRQ_ccorres)
      apply (simp add: liftE_alternative returnOk_liftE[symmetric])
      apply (rule ccorres_alternative2)
      apply (rule ccorres_return_CE, simp+)[1]
     apply (wp sts_invs_minor')+
   apply (rule ccorres_Cond_rhs)
    apply (rule ccorres_rhs_assoc)+
    apply csymbr
    apply csymbr
    apply (simp add: list_case_If2 split_def del: Collect_const)
    apply (rule ccorres_if_bind)
    apply (rule ccorres_if_lhs[rotated])
     apply (rule ccorres_cond_false_seq)
     apply (simp add: Let_def split_def ntfn_case_can_send
                 del: Collect_const)
     apply (rule getSlotCap_ccorres_fudge_n[where vals=extraCaps and n=0])
     apply (rule ccorres_move_c_guard_cte)
     apply (ctac(no_vcg))
       apply (rule ccorres_assert)
       apply (rule_tac P="\<lambda>s. ksCurThread s = thread"
                    in ccorres_cross_over_guard)
       apply (csymbr | rule ccorres_Guard_Seq)+
       apply (simp add: if_1_0_0 cap_get_tag_isCap del: Collect_const)
       apply (rule ccorres_Cond_rhs_Seq)
        apply (simp add: hd_conv_nth del: Collect_const)
        apply (rule ccorres_cond_true_seq)
        apply (rule ccorres_from_vcg_split_throws[where P=\<top> and P'=UNIV])
         apply vcg
        apply (rule conseqPre, vcg)
        apply (clarsimp simp: throwError_bind invocationCatch_def)
        apply (simp add: throwError_def return_def)
        apply (simp add: syscall_error_rel_def syscall_error_to_H_cases)
        apply (simp add: exception_defs)
       apply (rule ccorres_rhs_assoc)+
       apply csymbr+
       apply (subgoal_tac "(capNtfnCanSend_CL (cap_notification_cap_lift ntfnCap) = 0)
                              = (\<not> capNtfnCanSend rv)")
        apply (simp add: if_1_0_0 from_bool_0 hd_conv_nth del: Collect_const)
        apply (rule ccorres_Cond_rhs_Seq)
         apply (rule ccorres_split_throws)
          apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
          apply (rule allI, rule conseqPre, vcg)
          apply (clarsimp simp: throwError_bind invocationCatch_def)
          apply (simp add: throwError_def return_def)
          apply (simp add: syscall_error_rel_def syscall_error_to_H_cases)
          apply (simp add: exception_defs)
         apply vcg
        apply (simp add: hd_conv_nth liftE_bindE returnOk_bind
                         invocationCatch_def performInvocation_def
                         bind_assoc bind_bindE_assoc excaps_map_def
                    del: Collect_const)
        apply (ctac(no_vcg) add: setThreadState_ccorres)
         apply (ctac(no_vcg) add: invokeIRQHandler_SetIRQHandler_ccorres)
          apply (simp add: liftE_alternative returnOk_liftE[symmetric])
          apply (rule ccorres_alternative2)
          apply (rule ccorres_return_CE, simp+)[1]
         apply (wp sts_invs_minor' hoare_vcg_ex_lift
                     | simp)+
       apply (clarsimp simp: cap_get_tag_isCap[symmetric] 
                      dest!: cap_get_tag_to_H)
       apply (simp add: to_bool_def)
      apply simp
      apply (simp add: getSlotCap_def)
      apply (wp getCTE_wp)
     apply (clarsimp simp: Collect_const_mem neq_Nil_conv
                    dest!: interpret_excaps_eq)
     apply (simp add: rf_sr_ksCurThread if_1_0_0 mask_def[where n=4]
                      "StrictC'_thread_state_defs" cap_get_tag_isCap excaps_map_def
                      word_sless_def word_sle_def)
    apply (simp add: invocationCatch_def throwError_bind
                     interpret_excaps_test_null Collect_True
                     excaps_map_def
                del: Collect_const
               cong: StateSpace.state.fold_congs globals.fold_congs)
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply (rule ccorres_Cond_rhs)
    apply (simp add: invocationCatch_def performInvocation_def
                     returnOk_bind liftE_bindE bind_assoc
                     bind_bindE_assoc bind_assoc)
    apply (rule ccorres_rhs_assoc)+
    apply (ctac(no_vcg) add: setThreadState_ccorres)
     apply (ctac(no_vcg) add: invokeIRQHandler_ClearIRQHandler_ccorres)
      apply (simp add: liftE_alternative returnOk_liftE[symmetric])
      apply (rule ccorres_alternative2)
      apply (rule ccorres_return_CE, simp+)[1]
     apply (wp sts_invs_minor')+
    apply (rule ccorres_equals_throwError)
     apply (fastforce simp: invocationCatch_def throwError_bind split: invocation_label.split)
    apply (simp add: ccorres_cond_iffs cong: StateSpace.state.fold_congs globals.fold_congs)
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply simp
  apply (clarsimp simp: Collect_const_mem tcb_at_invs')
  apply (clarsimp simp: invs_queues invs_valid_objs'
                        ct_in_state'_def
                        ccap_rights_relation_def
                        mask_def[where n=4]
                        "StrictC'_thread_state_defs")
  apply (subst pred_tcb'_weakenE, assumption, fastforce)+
  apply (clarsimp simp: rf_sr_ksCurThread word_sle_def word_sless_def 
    sysargs_rel_n_def word_less_nat_alt)
  apply (clarsimp simp: cte_wp_at_ctes_of neq_Nil_conv sysargs_rel_def n_msgRegisters_def
                    excaps_map_def excaps_in_mem_def word_less_nat_alt hd_conv_nth
                    slotcap_in_mem_def valid_tcb_state'_def from_bool_def toBool_def
             dest!: interpret_excaps_eq split: bool.splits)
  apply (intro conjI impI allI)
  apply (clarsimp simp: cte_wp_at_ctes_of neq_Nil_conv sysargs_rel_def n_msgRegisters_def
                    excaps_map_def excaps_in_mem_def word_less_nat_alt hd_conv_nth
                    slotcap_in_mem_def valid_tcb_state'_def from_bool_def toBool_def
             dest!: interpret_excaps_eq split: bool.splits)+
     apply (auto dest: st_tcb_at_idle_thread' ctes_of_valid')[4]
    apply (drule ctes_of_valid')
     apply fastforce
    apply (clarsimp simp add:valid_cap_simps' ARM_HYP.maxIRQ_def)
    apply (erule order.trans,simp)
  apply (auto dest: st_tcb_at_idle_thread' ctes_of_valid')
  done

lemma mask_of_mask[simp]:
"mask (n::nat) && mask (m::nat) = mask (min m n)"
  apply (rule word_eqI)
  apply (auto simp:word_size)
  done

lemma invokeIRQControl_ccorres:
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
      (invs' and cte_at' parent and (\<lambda>_. (ucast irq) \<le> (scast Kernel_C.maxIRQ :: word32)))
      (UNIV \<inter> {s. irq_' s = ucast irq}
                  \<inter> {s. controlSlot_' s = cte_Ptr parent}
                  \<inter> {s. handlerSlot_' s = cte_Ptr slot}) []
      (performIRQControl (IssueIRQHandler irq slot parent))
      (Call invokeIRQControl_'proc)"
  apply (rule ccorres_gen_asm)
  apply (cinit lift: irq_' controlSlot_' handlerSlot_')
   apply (simp add: liftE_def bind_assoc return_returnOk)
   apply (ctac add: setIRQState_ccorres)
     apply csymbr
     apply (ctac(no_vcg) add: cteInsert_ccorres)
      apply (rule ccorres_return_CE, simp+)[1]
     apply wp+
   apply (simp add: Collect_const_mem)
   apply (vcg exspec=setIRQState_modifies)
  apply (rule conjI)
   apply (clarsimp simp: is_simple_cap'_def isCap_simps valid_cap_simps' capAligned_def)
   apply (subst ucast_le_ucast[where 'a = 16 and 'b = 32,symmetric],simp)
   apply (subst ucast_le_ucast_10_32[symmetric])
   apply (auto simp:ucast_up_ucast is_up ARM_HYP.maxIRQ_def Kernel_C.maxIRQ_def word_bits_def )[1]
  apply (clarsimp simp: Collect_const_mem ccap_relation_def cap_irq_handler_cap_lift
                        cap_to_H_def c_valid_cap_def cl_valid_cap_def
                        word_bw_assocs mask_twice Kernel_C.maxIRQ_def ucast_ucast_a
                        is_up ucast_ucast_b is_down)
  apply (subst less_mask_eq)
    apply (rule le_m1_iff_lt[THEN iffD1,THEN iffD1])
     apply simp
    apply (erule order.trans,simp)
  apply (rule word_eqI)
  apply (simp add: nth_ucast word_size)
  done

lemma unat_ucast_16_32:
  "unat (ucast (x::(16 word))::32 signed word) = unat x"
  apply (subst unat_ucast)
  apply (rule mod_less)
  apply (rule less_le_trans[OF unat_lt2p])
  apply simp
  done

lemma isIRQActive_ccorres:
  "ccorres (\<lambda>rv rv'. rv' = from_bool rv) ret__unsigned_long_'
        (\<lambda>s. irq \<le> scast Kernel_C.maxIRQ) (UNIV \<inter> {s. irq_' s = ucast irq}) []
        (isIRQActive irq) (Call isIRQActive_'proc)"
  apply (cinit lift: irq_')
   apply (simp add: getIRQState_def getInterruptState_def)
   apply (rule_tac P="irq \<le> scast Kernel_C.maxIRQ \<and> unat irq < (192::nat)" in ccorres_gen_asm)
   apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
   apply (rule allI, rule conseqPre, vcg)
   apply (clarsimp simp: simpler_gets_def word_sless_msb_less maxIRQ_def
                         word_less_nat_alt)
   apply (clarsimp simp: order_le_less_trans unat_less_helper
                         word_0_sle_from_less[OF order_less_le_trans, OF ucast_less])
   apply (clarsimp simp: rf_sr_def cstate_relation_def Kernel_C.maxIRQ_def
                         Let_def cinterrupt_relation_def)

   apply (drule spec, drule(1) mp)
   apply (case_tac "intStateIRQTable (ksInterruptState \<sigma>) irq")
     apply (simp add: from_bool_def irq_state_defs Kernel_C.maxIRQ_def
                      word_le_nat_alt)+
  done

lemma Platform_maxIRQ:
  "ARM_HYP.maxIRQ = scast Kernel_C.maxIRQ"
  by (simp add: ARM_HYP.maxIRQ_def Kernel_C.maxIRQ_def)

lemma Arch_decodeIRQControlInvocation_ccorres:
  "ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
      \<top> UNIV []
     (Arch.decodeIRQControlInvocation label args srcSlot extraCaps
        >>= invocationCatch thread isBlocking isCall (InvokeIRQControl o ArchIRQControl))
     (Call Arch_decodeIRQControlInvocation_'proc)"
  apply (cinit' simp: ARM_HYP_H.decodeIRQControlInvocation_def)
   apply (simp add: throwError_bind invocationCatch_def
              cong: StateSpace.state.fold_congs globals.fold_congs)
   apply (rule syscall_error_throwError_ccorres_n)
   apply (simp add: syscall_error_to_H_cases)
  apply simp
  done

lemma liftME_invocationCatch:
  "liftME f m >>= invocationCatch thread isBlocking isCall f'
     = m >>= invocationCatch thread isBlocking isCall (f' \<circ> f)"
  apply (simp add: liftME_def bindE_def bind_assoc)
  apply (rule bind_cong [OF refl])
  apply (simp add: lift_def throwError_bind invocationCatch_def
                   returnOk_bind
            split: sum.split)
  done

lemma maxIRQ_ucast_scast [simp]:
  "ucast (scast Kernel_C.maxIRQ :: 10 word) = scast Kernel_C.maxIRQ"
  by (clarsimp simp: Kernel_C.maxIRQ_def)

lemma decodeIRQ_arch_helper: "x \<noteq> invocation_label.IRQIssueIRQHandler \<Longrightarrow> 
         (case x of invocation_label.IRQIssueIRQHandler \<Rightarrow> f | _ \<Rightarrow> g) = g"
  by (clarsimp split: invocation_label.splits)


lemma Arch_checkIRQ_ccorres:
  "ccorres (syscall_error_rel \<currency> (\<lambda>r r'. irq \<le> scast Kernel_C.maxIRQ)) 
           (liftxf errstate id undefined ret__unsigned_long_')
   \<top> (UNIV \<inter> \<lbrace>irq = \<acute>irq___unsigned_long\<rbrace>) []
   (checkIRQ irq) (Call Arch_checkIRQ_'proc)"
  apply (cinit lift: irq___unsigned_long_' )
   apply (simp add: rangeCheck_def unlessE_def ARM_HYP.minIRQ_def checkIRQ_def
                    ucast_nat_def word_le_nat_alt[symmetric]
                    linorder_not_le[symmetric] Platform_maxIRQ
                    length_ineq_not_Nil hd_conv_nth cast_simps
               del: Collect_const cong: call_ignore_cong)
   apply (rule ccorres_Cond_rhs_Seq)
    apply (simp add: throwError_bind)
    apply (rule ccorres_from_vcg_split_throws[where P=\<top> and P'=UNIV])
     apply vcg
    apply (rule conseqPre, vcg)
    apply (clarsimp simp: throwError_def return_def
                          exception_defs syscall_error_rel_def
                          syscall_error_to_H_cases)
   apply clarsimp
   apply (rule ccorres_return_CE, simp+)
  done
  
lemma checkIRQ_ret_good:
  "\<lbrace>\<lambda>s. (irq \<le> scast Kernel_C.maxIRQ \<longrightarrow> P s) \<and> Q s\<rbrace> checkIRQ irq \<lbrace>\<lambda>rv. P\<rbrace>, \<lbrace>\<lambda>rv. Q\<rbrace>"
  apply (clarsimp simp: checkIRQ_def rangeCheck_def Platform_maxIRQ minIRQ_def)
  apply (rule hoare_pre,wp)
  by (clarsimp simp: Kernel_C.maxIRQ_def split: if_split)

lemma toEnum_of_ucast:
  "len_of TYPE('b) \<le> len_of TYPE('a) \<Longrightarrow> 
  (toEnum (unat (b::('b :: len word))):: ('a :: len word)) = of_nat (unat b)"
  apply (subst toEnum_of_nat)
   apply (rule less_le_trans[OF unat_lt2p])
   apply (simp add:power2_nat_le_eq_le)
  apply simp
  done

lemma unat_ucast_mask:
  "len_of TYPE('b) \<le> len_of TYPE('a) \<Longrightarrow> (unat (ucast (a :: ('a :: len) word) :: ('b :: len) word)) = unat (a && mask (len_of TYPE('b)))"
  apply (subst ucast_mask_drop[symmetric])
   apply (rule le_refl)
  apply (simp add:unat_ucast)
  apply (subst nat_mod_eq')
   apply (rule less_le_trans[OF word_unat_mask_lt le_refl])
   apply (simp add: word_size)
  apply simp
  done

lemma decodeIRQControlInvocation_ccorres:
  notes if_cong[cong] tl_drop_1[simp]
  shows
  "interpret_excaps extraCaps' = excaps_map extraCaps \<Longrightarrow>
   ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread) 
              and sch_act_simple and ct_active'
              and (excaps_in_mem extraCaps o ctes_of)
              and cte_wp_at' (\<lambda>cte. cteCap cte = IRQControlCap) slot
              and (\<lambda>s. \<forall>v \<in> set extraCaps. s \<turnstile>' fst v)
              and sysargs_rel args buffer)
       (UNIV
            \<inter> {s. invLabel_' s = label} \<inter> {s. srcSlot_' s = cte_Ptr slot}
            \<inter> {s. unat (length___unsigned_long_' s) = length args}
            \<inter> {s. excaps_' s = extraCaps'}
            \<inter> {s. buffer_' s = option_to_ptr buffer}) []
     (decodeIRQControlInvocation label args slot (map fst extraCaps)
            >>= invocationCatch thread isBlocking isCall InvokeIRQControl)
     (Call decodeIRQControlInvocation_'proc)"
  apply (cinit' lift: invLabel_' srcSlot_' length___unsigned_long_' excaps_' buffer_')
   apply (simp add: decodeIRQControlInvocation_def invocation_eq_use_types 
               del: Collect_const
              cong: StateSpace.state.fold_congs globals.fold_congs)
   apply (rule ccorres_Cond_rhs)
    apply (simp add: list_case_If2
                del: Collect_const cong: call_ignore_cong)
    apply (rule ccorres_rhs_assoc)+
    apply csymbr+
    apply (rule ccorres_Cond_rhs_Seq)
     apply (simp add: word_less_nat_alt if_1_0_0
                      throwError_bind invocationCatch_def)
     apply (rule ccorres_cond_true_seq)
     apply (rule syscall_error_throwError_ccorres_n)
     apply (simp add: syscall_error_to_H_cases)
    apply csymbr
    apply (rule ccorres_Cond_rhs_Seq)
     apply (simp add: interpret_excaps_test_null if_1_0_0 excaps_map_def
                      throwError_bind invocationCatch_def)
     apply (rule syscall_error_throwError_ccorres_n)
     apply (simp add: syscall_error_to_H_cases)
    apply (simp add: interpret_excaps_test_null if_1_0_0 excaps_map_def
                     word_less_nat_alt Let_def
                del: Collect_const cong: call_ignore_cong)
    apply (rule ccorres_add_return)
    apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=0 and buffer=buffer])
      apply csymbr
      apply (rule ccorres_add_return)
      apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=1 and buffer=buffer])
        apply (rule ccorres_add_return)
        apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=2 and buffer=buffer])
          apply (rule getSlotCap_ccorres_fudge_n[where vals=extraCaps and n=0])
          apply (rule ccorres_move_c_guard_cte)
          apply ctac
            apply (rule ccorres_assert2)
            apply (simp add: rangeCheck_def unlessE_def ARM_HYP.minIRQ_def
                             ucast_nat_def word_le_nat_alt[symmetric]
                             linorder_not_le[symmetric] Platform_maxIRQ
                             length_ineq_not_Nil hd_conv_nth cast_simps
                             maxIRQ_ucast_scast
                        del: Collect_const cong: call_ignore_cong)
            apply (simp add: split_def invocationCatch_use_injection_handler injection_handler_bindE
                             bindE_assoc 
                        del: Collect_const)
            apply (ctac add: ccorres_injection_handler_csum1[OF Arch_checkIRQ_ccorres])
               apply (simp add: injection_liftE)
               apply (simp add: liftE_bindE bind_assoc del: Collect_const)
               apply (ctac add: isIRQActive_ccorres)
                 apply (simp add: from_bool_0 del: Collect_const)
                 apply (rule ccorres_Cond_rhs_Seq)
                  apply (simp add: throwError_bind invocationCatch_def whenE_def
                                   injection_handler_throwError)
                  apply (rule syscall_error_throwError_ccorres_n)
                  apply (simp add: syscall_error_to_H_cases)
                 apply (simp add: split_def invocationCatch_use_injection_handler
                                  injection_handler_bindE bindE_assoc whenE_def
                                  injection_handler_returnOk
                            del: Collect_const)
                 apply (ctac add: ccorres_injection_handler_csum1
                    [OF lookupTargetSlot_ccorres, unfolded lookupTargetSlot_def])
                    apply (simp add: Collect_False split_def del: Collect_const)
                    apply csymbr
                    apply (ctac add: ccorres_injection_handler_csum1
                                       [OF ensureEmptySlot_ccorres])
                       apply (simp add: injection_handler_returnOk ccorres_invocationCatch_Inr
                                        performInvocation_def bindE_assoc)
                       apply (ctac add: setThreadState_ccorres)
                         apply (ctac(no_vcg) add: invokeIRQControl_ccorres)
                           apply (rule ccorres_alternative2)
                           apply (rule ccorres_return_CE, simp+)[1]
                          apply (rule ccorres_return_C_errorE, simp+)[1]
                         apply (wp sts_invs_minor')+
                       apply (simp add: Collect_const_mem)
                       apply (vcg exspec=setThreadState_modifies)
                      apply simp
                      apply (rule ccorres_split_throws)
                       apply (rule ccorres_return_C_errorE, simp+)[1]
                      apply vcg
                     apply simp
                     apply (wp injection_wp_E [OF refl])
                    apply (simp add: Collect_const_mem all_ex_eq_helper)
                    apply (vcg exspec=ensureEmptySlot_modifies)
                   apply simp
                   apply (rule ccorres_split_throws)
                    apply (rule ccorres_return_C_errorE, simp+)[1]
                   apply vcg
                  apply simp
                  apply (wp injection_wp_E[OF refl])
                 apply (simp add: Collect_const_mem all_ex_eq_helper)
                 apply (vcg exspec=lookupTargetSlot_modifies)
                apply simp
                apply (wp hoare_drop_imps isIRQActive_inv)
               apply (simp add: Collect_const_mem all_ex_eq_helper)
               apply (vcg exspec=isIRQActive_modifies)
              apply simp
              apply (rule ccorres_split_throws)
               apply (rule ccorres_return_C_errorE, simp+)[1]
              apply vcg
             apply simp
             apply (wp injection_wp_E[OF refl] checkIRQ_ret_good)
            apply (simp add: Collect_const_mem all_ex_eq_helper)
            apply (vcg exspec=Arch_checkIRQ_modifies)
           apply (wp hoare_vcg_const_imp_lift |wp_once hoare_drop_imps)+
          apply (simp add: Collect_const_mem all_ex_eq_helper)
          apply vcg
         apply wp
        apply (simp add: Collect_const_mem all_ex_eq_helper)
        apply (vcg exspec=getSyscallArg_modifies)
       apply simp
       apply wp
      apply (simp add: Collect_const_mem all_ex_eq_helper)
      apply (vcg exspec=getSyscallArg_modifies)
     apply simp
     apply wp
    apply (simp add: Collect_const_mem all_ex_eq_helper)
    apply (vcg exspec=getSyscallArg_modifies)
   apply (clarsimp simp: decodeIRQ_arch_helper)
   apply (simp add: liftME_invocationCatch)
   apply (rule ccorres_add_returnOk)
   apply (ctac add: Arch_decodeIRQControlInvocation_ccorres)
      apply (rule ccorres_return_CE, simp+)[1]
     apply (rule ccorres_return_C_errorE, simp+)[1]
    apply wp
   apply vcg
  apply (simp add: syscall_error_to_H_cases)
  apply (clarsimp simp: if_1_0_0 interpret_excaps_test_null excaps_map_def
                        Collect_const_mem word_sless_def word_sle_def
                        ThreadState_Restart_def unat_of_nat mask_def
                  cong: if_cong)
  apply (rule conjI)
   apply (simp add: toEnum_of_nat Kernel_C.maxIRQ_def
                    word_le_nat_alt ucast_nat_def
                    unat_ucast)
   apply (cut_tac unat_lt2p[where x="args ! 2"])
   apply clarsimp
   apply (clarsimp simp: sysargs_rel_to_n word_less_nat_alt unat_ucast)
   apply (auto,
          auto simp: ct_in_state'_def neq_Nil_conv word_bits_def
                     excaps_in_mem_def slotcap_in_mem_def
                     cte_wp_at_ctes_of numeral_eqs[symmetric]
                     valid_tcb_state'_def
              elim!: pred_tcb'_weakenE cte_wp_at_weakenE'
              dest!: st_tcb_at_idle_thread' interpret_excaps_eq)[1]
  apply (clarsimp simp: neq_Nil_conv numeral_eqs[symmetric]
                        word_sle_def word_sless_def)
  apply (drule interpret_excaps_eq[rule_format, where n=0], simp)
  apply (clarsimp simp: mask_def[where n=4] "StrictC'_thread_state_defs"
                        rf_sr_ksCurThread ccap_rights_relation_def
                        rightsFromWord_wordFromRights)
  apply (simp cong: conj_cong)

  apply (clarsimp simp add: Kernel_C.maxIRQ_def toEnum_of_nat word_le_nat_alt
                   ucast_nat_def ucast_ucast_mask mask_eq_ucast_eq unat_ucast_mask
                   less_mask_eq[unfolded word_less_nat_alt])
   
  apply (subst ucast_mask_drop)
  apply (simp add:mask_def)+
  done
end
end
