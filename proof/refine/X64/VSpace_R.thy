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
   X64 VSpace refinement
*)

theory VSpace_R
imports TcbAcc_R
begin
context Arch begin global_naming X64 (*FIXME: arch_split*)

(* FIXME x64: move *)
lemmas store_pde_typ_ats' [wp] = abs_typ_at_lifts [OF store_pde_typ_at]
lemmas store_pdpte_typ_ats' [wp] = abs_typ_at_lifts [OF store_pdpte_typ_at]
lemmas store_pte_typ_ats[wp] = store_pte_typ_ats abs_atyp_at_lifts[OF store_pte_typ_at]
lemmas store_pde_typ_ats[wp] = store_pde_typ_ats' abs_atyp_at_lifts[OF store_pde_typ_at]
lemmas store_pdpte_typ_ats[wp] = store_pdpte_typ_ats' abs_atyp_at_lifts[OF store_pdpte_typ_at]

end

context begin interpretation Arch . (*FIXME: arch_split*)

crunch_ignore (add: throw_on_false)

definition
  "vspace_at_asid' vs asid \<equiv> \<lambda>s. \<exists>ap pool.
             x64KSASIDTable (ksArchState s) (ucast (asid_high_bits_of asid)) = Some ap \<and>
             ko_at' (ASIDPool pool) ap s \<and> pool (asid && mask asid_low_bits) = Some vs \<and>
             page_map_l4_at' vs s"

defs checkPML4ASIDMapMembership_def:
  "checkPML4ASIDMapMembership pd asids
     \<equiv> stateAssert (\<lambda>s. pd \<notin> ran ((x64KSASIDMap (ksArchState s) |` (- set asids)))) []"

crunch inv[wp]:checkPDAt P

lemma findVSpaceForASID_vs_at_wp:
  "\<lbrace>\<lambda>s. \<forall>pm. (page_map_l4_at' pm s \<longrightarrow> vspace_at_asid' pm asid s) \<longrightarrow> P pm s\<rbrace>
    findVSpaceForASID asid
   \<lbrace>P\<rbrace>,-"
  apply (simp add: findVSpaceForASID_def assertE_def checkPML4At_def
             cong: option.case_cong split del: if_split)
  apply (wpsimp wp: getASID_wp)
  apply (erule allE; erule mp; clarsimp simp: vspace_at_asid'_def page_map_l4_at'_def)
  apply (case_tac ko; simp)
  apply (subst (asm) inv_f_f, rule inj_onI, simp)
  by fastforce

lemma findVSpaceForASIDAssert_vs_at_wp:
  "\<lbrace>(\<lambda>s. \<forall>pd. vspace_at_asid' pd asid  s
               \<and> pd \<notin> ran (( x64KSASIDMap (ksArchState s) |` (- {asid})))
                \<longrightarrow> P pd s)\<rbrace>
       findVSpaceForASIDAssert asid \<lbrace>P\<rbrace>"
  apply (simp add: findVSpaceForASIDAssert_def const_def
                   checkPML4At_def checkPML4UniqueToASID_def
                   checkPML4ASIDMapMembership_def)
  apply (rule hoare_pre, wp getPDE_wp findVSpaceForASID_vs_at_wp)
  apply simp
  done

crunch inv[wp]: findVSpaceForASIDAssert "P"
  (simp: const_def crunch_simps wp: loadObject_default_inv crunch_wps)

lemma pspace_relation_pml4:
  assumes p: "pspace_relation (kheap a) (ksPSpace c)"
  assumes pa: "pspace_aligned a"
  assumes pad: "pspace_aligned' c" "pspace_distinct' c"
  assumes t: "page_map_l4_at p a"
  shows "page_map_l4_at' p c"
  using assms is_aligned_pml4 [OF t pa]
  apply (clarsimp simp: obj_at_def)
  apply (drule(1) pspace_relation_absD)
  apply (clarsimp simp: a_type_def
                 split: Structures_A.kernel_object.split_asm
                        if_split_asm arch_kernel_obj.split_asm)
  apply (clarsimp simp: page_map_l4_at'_def bit_simps
                        typ_at_to_obj_at_arches)
  apply (drule_tac x="ucast y" in spec, clarsimp)
  apply (simp add: ucast_ucast_mask iffD2 [OF mask_eq_iff_w2p] word_size)
  apply (clarsimp simp add: pml4e_relation_def)
  apply (drule(2) aligned_distinct_pml4e_atI')
  apply (erule obj_at'_weakenE)
  apply simp
  done

lemma find_vspace_for_asid_eq_helper:
  "\<lbrakk> vspace_at_asid asid pm s; valid_arch_objs s;
         asid \<noteq> 0; pspace_aligned s \<rbrakk>
    \<Longrightarrow> find_vspace_for_asid asid s = returnOk pm s
             \<and> page_map_l4_at pm s \<and> is_aligned pm pml4Bits"
  apply (clarsimp simp: vspace_at_asid_def valid_arch_objs_def)
  apply (frule spec, drule mp, erule exI)
  apply (clarsimp simp: vs_asid_refs_def graph_of_def
                 elim!: vs_lookupE)
  apply (erule rtranclE)
   apply simp
  apply (clarsimp dest!: vs_lookup1D)
  apply (erule rtranclE)
   defer
   apply (drule vs_lookup1_trans_is_append')
   apply (clarsimp dest!: vs_lookup1D)
  apply (clarsimp dest!: vs_lookup1D)
  apply (drule spec, drule mp, rule exI,
         rule vs_lookupI[unfolded vs_asid_refs_def])
    apply (rule image_eqI[OF refl])
    apply (erule graph_ofI)
   apply clarsimp
   apply (rule rtrancl.intros(1))
  apply (clarsimp simp: vs_refs_def graph_of_def
                 split: Structures_A.kernel_object.splits
                        arch_kernel_obj.splits)
  apply (clarsimp simp: obj_at_def)
  apply (drule bspec, erule ranI)
  apply clarsimp
  apply (drule ucast_up_inj, simp)
  apply (simp add: find_vspace_for_asid_def bind_assoc
                   word_neq_0_conv[symmetric] liftE_bindE)
  apply (simp add: exec_gets liftE_bindE bind_assoc
                   get_asid_pool_def get_object_def)
  apply (simp add: mask_asid_low_bits_ucast_ucast)
  apply (clarsimp simp: returnOk_def get_pml4e_def
                        get_pml4_def get_object_def
                        bind_assoc)
  apply (frule(1) pspace_alignedD[where p=pm])
  apply (simp add: bit_simps)
  done

lemma find_vspace_for_asid_assert_eq:
  "\<lbrakk> vspace_at_asid asid pm s; valid_arch_objs s;
         asid \<noteq> 0; pspace_aligned s \<rbrakk>
    \<Longrightarrow> find_vspace_for_asid_assert asid s = return pm s"
  apply (drule (3) find_vspace_for_asid_eq_helper)
  apply (simp add: find_vspace_for_asid_assert_def
                   catch_def bind_assoc)
  apply (clarsimp simp: returnOk_def obj_at_def
                        a_type_def
                  cong: bind_apply_cong)
  apply (clarsimp split: Structures_A.kernel_object.splits
                         arch_kernel_obj.splits if_split_asm)
  apply (simp add: get_pml4e_def get_pml4_def get_object_def
                   bind_assoc is_aligned_neg_mask_eq
                   bit_simps)
  apply (simp add: exec_gets)
  done

lemma find_vspace_for_asid_assert_eq_ex:
  "\<lbrakk> vspace_at_asid_ex asid s; valid_arch_objs s;
         asid \<noteq> 0; pspace_aligned s \<rbrakk>
    \<Longrightarrow> (do _ \<leftarrow> find_vspace_for_asid_assert asid; return () od) s = return () s"
  apply (clarsimp simp: vspace_at_asid_ex_def)
  apply (drule (3) find_vspace_for_asid_eq_helper)
  apply (simp add: find_vspace_for_asid_assert_def
                   catch_def bind_assoc)
  apply (clarsimp simp: returnOk_def obj_at_def
                        a_type_def
                  cong: bind_apply_cong)
  apply (clarsimp split: Structures_A.kernel_object.splits
                         arch_kernel_obj.splits if_split_asm)
  apply (simp add: get_pml4e_def get_pml4_def get_object_def
                   bind_assoc is_aligned_neg_mask_eq
                   bit_simps)
  apply (simp add: exec_gets)
  done

(* FIXME x64: move to invariants *)
lemma find_vspace_for_asid_wp:
  "\<lbrace> valid_arch_objs and pspace_aligned and K (asid \<noteq> 0)
        and (\<lambda>s. \<forall>pm. vspace_at_asid asid pm s \<longrightarrow> Q pm s)
        and (\<lambda>s. (\<forall>pm. \<not> vspace_at_asid asid pm s) \<longrightarrow> E ExceptionTypes_A.lookup_failure.InvalidRoot s) \<rbrace>
    find_vspace_for_asid asid
   \<lbrace> Q \<rbrace>,\<lbrace> E \<rbrace>"
  apply (wpsimp simp: find_vspace_for_asid_def vspace_at_asid_def)
  apply (intro conjI impI allI)
    apply (erule mp; clarsimp; thin_tac "\<forall>pm. _ pm s")
    apply (erule vs_lookupE; clarsimp simp: vs_asid_refs_def graph_of_def)
    apply (drule vs_lookup1_trans_is_append)
    apply (clarsimp simp: up_ucast_inj_eq)
   apply (erule mp; clarsimp; thin_tac "\<forall>pm. _ pm s")
   apply (erule vs_lookupE; clarsimp simp: vs_asid_refs_def graph_of_def)
   apply (frule vs_lookup1_trans_is_append; clarsimp simp: up_ucast_inj_eq)
   apply (erule rtranclE; clarsimp)
   apply (frule vs_lookup1_wellformed.lookup1_is_append; clarsimp)
   apply (drule vs_lookup1_wellformed.lookup_trans_eq; clarsimp)
   apply (clarsimp simp: vs_lookup1_def vs_refs_def)
   apply (case_tac ko; clarsimp; rename_tac ako; case_tac ako; clarsimp)
   apply (clarsimp simp: graph_of_def obj_at_def mask_asid_low_bits_ucast_ucast)
  apply (drule spec; erule mp; thin_tac "_ s \<longrightarrow> _ s")
  apply (rule vs_lookupI)
   apply (fastforce simp: vs_asid_refs_def graph_of_def image_def)
  apply (rule rtrancl_into_rtrancl[rotated])
   apply (erule vs_lookup1I; fastforce simp: vs_refs_def graph_of_def image_def
                                             ucast_ucast_mask asid_low_bits_def)
  by simp

lemma valid_asid_map_inj_map:
  "\<lbrakk> valid_asid_map s; (s, s') \<in> state_relation;
        unique_table_refs (caps_of_state s);
        valid_vs_lookup s; valid_arch_objs s;
        valid_arch_state s; valid_global_objs s \<rbrakk>
        \<Longrightarrow> inj_on (x64KSASIDMap (ksArchState s'))
                   (dom (x64KSASIDMap (ksArchState s')))"
  apply (rule inj_onI)
  apply (clarsimp simp: valid_asid_map_def state_relation_def
                        arch_state_relation_def)
  apply (frule_tac c=x in subsetD, erule domI)
  apply (frule_tac c=y in subsetD, erule domI)
  apply (drule(1) bspec [rotated, OF graph_ofI])+
  apply clarsimp
  apply (erule(6) vspace_at_asid_unique)
   apply (simp add: mask_def)+
  done

lemma asidBits_asid_bits[simp]:
  "asidBits = asid_bits"
  by (simp add: asid_bits_def asidBits_def
                asidHighBits_def asid_low_bits_def)

lemma find_vspace_for_asid_assert_corres [corres]:
  assumes "asid' = asid"
  shows "corres (op =)
                (K (asid \<noteq> 0 \<and> asid \<le> mask asid_bits)
                    and pspace_aligned and pspace_distinct and valid_arch_objs and valid_asid_map
                    and vspace_at_uniq_ex asid)
                (pspace_aligned' and pspace_distinct' and no_0_obj')
                (find_vspace_for_asid_assert asid)
                (findVSpaceForASIDAssert asid')"
  using assms
  apply (simp add: find_vspace_for_asid_assert_def const_def
                   findVSpaceForASIDAssert_def liftM_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqr)
       apply (rule_tac F="is_aligned pml4 pml4Bits" in corres_gen_asm)
       apply (clarsimp simp add: is_aligned_mask[symmetric])
       apply (rule_tac P="(\<lambda>s. pml4e_at pml4 s \<and> vspace_at_uniq asid pml4 s)
                             and pspace_aligned and pspace_distinct
                             and vspace_at_asid asid pml4 and valid_asid_map"
                  and P'="pspace_aligned' and pspace_distinct'"
                  in stronger_corres_guard_imp)
         apply (rule_tac P="pml4e_at pml4 and vspace_at_uniq asid pml4
                               and valid_asid_map and vspace_at_asid asid pml4"
                  in corres_symb_exec_l)
            apply (rule_tac P'="page_map_l4_at' pml4" in corres_symb_exec_r)
               apply (simp add: checkPML4UniqueToASID_def ran_option_map
                                checkPML4ASIDMapMembership_def)
               apply (rule_tac P'="vspace_at_uniq asid pml4" in corres_stateAssert_implied)
                apply (simp add: gets_def bind_assoc[symmetric]
                                 stateAssert_def[symmetric, where L="[]"])
                apply (rule_tac P'="valid_asid_map and vspace_at_asid asid pml4"
                                 in corres_stateAssert_implied)
                 apply (rule corres_trivial, simp)
                apply (clarsimp simp: state_relation_def arch_state_relation_def
                                      valid_asid_map_def
                               split: option.split)
                apply (drule bspec, erule graph_ofI)
                apply clarsimp
                apply (drule(1) vspace_at_asid_unique2)
                apply simp
               apply (clarsimp simp: state_relation_def arch_state_relation_def
                                     vspace_at_uniq_def ran_option_map)
              apply wp+
            apply (simp add: checkPML4At_def stateAssert_def)
            apply (rule no_fail_pre, wp)
            apply simp
           apply (clarsimp simp: pml4e_at_def obj_at_def a_type_def is_aligned_neg_mask_eq)
           apply (clarsimp split: Structures_A.kernel_object.splits
                                  arch_kernel_obj.splits if_split_asm)
           apply (simp add: get_pml4e_def exs_valid_def bind_def return_def
                            get_pml4_def get_object_def simpler_gets_def)
          apply wp
          apply simp
         apply (simp add: get_pml4e_def get_pml4_def)
         apply (rule no_fail_pre)
          apply (wp get_object_wp | wpc)+
         apply (clarsimp simp: pml4e_at_def obj_at_def a_type_def is_aligned_neg_mask_eq)
         apply (clarsimp split: Structures_A.kernel_object.splits
                                arch_kernel_obj.splits if_split_asm)
        apply simp
       apply (clarsimp simp: state_relation_def)
       apply (erule(3) pspace_relation_pml4)
       apply (simp add: pml4e_at_def bit_simps
                        is_aligned_neg_mask_eq)
      apply (rule corres_split_catch [OF _ find_vspace_for_asid_corres'[OF refl]])
        apply (rule_tac P="\<bottom>" and P'="\<top>" in corres_inst)
        apply (simp add: corres_fail)
       apply (wp find_vspace_for_asid_wp)+
   apply (clarsimp simp: vspace_at_uniq_ex_def vspace_at_asid_ex_def word_neq_0_conv)
   apply (rule conjI, fastforce)
   apply (clarsimp; drule (1) vspace_at_asid_unique2)
   apply (frule find_vspace_for_asid_eq_helper; clarsimp)
   apply (frule page_map_l4_pml4e_atI[where x=0]; simp add: bit_simps)
  apply simp
  done

(* FIXME: move to Lib *)
lemma corres_add_noop_rhs2:
  "corres_underlying sr nf nf' dc P P' f (g >>= (\<lambda>_. return ()))
      \<Longrightarrow> corres_underlying sr nf nf' dc P P' f g"
  apply (simp add: corres_underlying_def)
  apply (erule ballEI)
  apply (case_tac x; rename_tac s s'; clarsimp; rename_tac rv' t')
  apply (drule_tac x="((),t')" in bspec; fastforce simp: in_bind_split in_returns)
  done

(* FIXME x64: make intro/elim rules for vspace_at_asid_ex and vspace_at_uniq_ex. *)
lemma invalidate_asid_corres [corres]:
  assumes "a' = a"
  shows "corres dc (valid_asid_map and valid_arch_objs
                        and pspace_aligned and pspace_distinct
                        and vspace_at_uniq_ex a
                        and K (a \<noteq> 0 \<and> a \<le> mask asid_bits))
                   (pspace_aligned' and pspace_distinct' and no_0_obj')
                   (invalidate_asid a) (invalidateASID' a')"
  (is "corres dc ?P ?P' ?f ?f'")
  using assms
  apply (simp add: invalidate_asid_def invalidateASID'_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_noop_rhs[where P="?P" and P'="?P'"])
      apply (rule corres_split[where P=\<top> and P'=\<top> and Q=\<top> and Q'=\<top> and r'="op =",
                               OF _ _ gets_sp gets_sp])
       apply (rule corres_modify)
       apply (simp add: state_relation_def arch_state_relation_def fun_upd_def)
      apply (clarsimp simp: state_relation_def arch_state_relation_def)
     apply (subst corres_cong[OF refl refl _ refl refl])
      apply clarsimp
      apply (rule find_vspace_for_asid_assert_eq_ex[symmetric];
             fastforce simp: vspace_at_uniq_ex_def vspace_at_asid_ex_def)
     apply (rule corres_add_noop_rhs2)
     apply corres
    by (wpsimp simp: vspace_at_asid_ex_def vspace_at_uniq_ex_def)+

lemma invalidate_asid_ext_corres:
  "corres dc
          (\<lambda>s. \<exists>pd. valid_asid_map s \<and> valid_arch_objs s
               \<and> pspace_aligned s \<and> pspace_distinct s
               \<and> vspace_at_asid a pd s \<and> vspace_at_uniq a pd s
               \<and> a \<noteq> 0 \<and> a \<le> mask asid_bits)
          (pspace_aligned' and pspace_distinct' and no_0_obj')
     (invalidate_asid a) (invalidateASID' a)"
  apply (insert invalidate_asid_corres)
  apply (clarsimp simp: corres_underlying_def)
  apply (fastforce simp: vspace_at_uniq_ex_def)
  done

(* FIXME x64: move *)
lemma no_fail_getFaultAddress[wp]: "no_fail \<top> getFaultAddress"
  by (simp add: getFaultAddress_def)

lemma hv_corres:
  "corres (fr \<oplus> dc) (tcb_at thread) (tcb_at' thread)
          (handle_vm_fault thread fault) (handleVMFault thread fault)"
  apply (simp add: X64_H.handleVMFault_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqrE)
       apply (rule corres_split_eqrE)
          apply (cases fault; simp)
         apply simp
         apply (rule user_getreg_corres[simplified get_register_eq[symmetric]])
        apply (simp, wp as_user_tcb_at)
       apply (simp, wp asUser_typ_ats)
      apply simp
      apply (rule corres_machine_op [where r="op ="])
      apply (rule corres_Id, rule refl, simp)
      apply (rule no_fail_getFaultAddress)
     apply wpsimp+
  done

crunch valid_global_objs[wp]: do_machine_op "valid_global_objs"

lemma state_relation_asid_map:
  "(s, s') \<in> state_relation \<Longrightarrow> x64KSASIDMap (ksArchState s') = x64_asid_map (arch_state s)"
  by (simp add: state_relation_def arch_state_relation_def)

(* FIXME x64: move *)
lemma no_fail_writeCR3[wp]: "no_fail \<top> (writeCR3 a b)"
  by (simp add: writeCR3_def)

lemma set_current_cr3_corres [corres]:
  "cr3_relation c c' \<Longrightarrow> corres dc \<top> \<top> (set_current_cr3 c) (setCurrentCR3 c')"
  apply (clarsimp simp add: set_current_cr3_def setCurrentCR3_def cr3_relation_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_nor)
       apply (rule corres_machine_op)
       apply (rule corres_Id, rule refl, simp)
       apply (rule no_fail_writeCR3)
      apply (rule corres_modify')
       apply (clarsimp simp: state_relation_def arch_state_relation_def cr3_relation_def)
      apply (simp add: dc_def)
     apply wpsimp+
  done

lemma get_current_cr3_corres [corres]:
  "corres cr3_relation \<top> \<top> (get_current_cr3) (getCurrentCR3)"
  apply (simp add: getCurrentCR3_def get_current_cr3_def)
  by (clarsimp simp: state_relation_def arch_state_relation_def)

lemma corres_gets_x64_asid_map [corres]:
  "corres (op =) \<top> \<top> (gets (x64_asid_map \<circ> arch_state)) (gets (x64KSASIDMap \<circ> ksArchState))"
  by (simp add: state_relation_def arch_state_relation_def)

lemma corres_modify_x64_asid_map [corres]:
  assumes "asidMap = asid_map" "a' = a" "vs = vspace"
  shows "corres dc (\<lambda>s. x64_asid_map (arch_state s) = asid_map) \<top>
                (modify (\<lambda>s. s\<lparr>arch_state := arch_state s\<lparr>x64_asid_map := asid_map(a \<mapsto> vspace)\<rparr>\<rparr>))
                (modify (\<lambda>s. s\<lparr>ksArchState := x64KSASIDMap_update (\<lambda>_. asidMap(a' \<mapsto> vs)) (ksArchState s)\<rparr>))"
  apply (rule corres_modify)
  by (simp add: assms state_relation_def arch_state_relation_def fun_upd_def)

lemma update_asid_map_corres [corres]:
  assumes "a' = a"
  shows "corres dc (K (a \<noteq> 0 \<and> a \<le> mask asid_bits) and
                         pspace_aligned and pspace_distinct and
                         valid_arch_objs and valid_asid_map and
                         vspace_at_uniq_ex a)
                   (pspace_aligned' and pspace_distinct' and no_0_obj')
                   (update_asid_map a) (updateASIDMap a')"
  using assms
  apply (simp add: update_asid_map_def updateASIDMap_def)
  by corressimp

(* FIXME x64: move to Corres_Method *)
lemma corres_rv_disj_dc: "corres_rv_disj r' r'' dc"
  unfolding corres_rv_disj_def by simp

(* FIXME x64: move to Corres_Method *)
lemma corresK_whenE (* [corresK] *):
  assumes "G \<Longrightarrow> G' \<Longrightarrow> corres_underlyingK sr nf nf' F (f \<oplus> dc) P P' a c"
  shows "corres_underlyingK sr nf nf' ((G = G') \<and> F) (f \<oplus> dc) ((\<lambda>x. G \<longrightarrow> P x)) (\<lambda>x. G' \<longrightarrow> P' x)
                            (whenE G a) (whenE G' c)"
  using assms by (cases G) (auto simp: corres_underlying_def corres_underlyingK_def
                                       whenE_def returnOk_def return_def)

lemma set_vm_root_corres [corres]:
  assumes "t' = t"
  shows "corres dc (tcb_at t and valid_arch_state and valid_objs and valid_asid_map
                      and unique_table_refs o caps_of_state and valid_vs_lookup
                      and valid_global_objs and pspace_aligned and pspace_distinct
                      and valid_arch_objs)
                   (pspace_aligned' and pspace_distinct'
                      and valid_arch_state' and tcb_at' t' and no_0_obj')
                   (set_vm_root t) (setVMRoot t')"
proof -
  have P: "corres dc \<top> \<top>
        (do global_pml4 \<leftarrow> gets (x64_global_pml4 \<circ> arch_state);
            set_current_vspace_root (X64.addrFromKPPtr global_pml4) 0
         od)
        (do globalPML4 \<leftarrow> gets (x64KSGlobalPML4 \<circ> ksArchState);
            X64_H.setCurrentVSpaceRoot (addrFromKPPtr globalPML4) 0
         od)"
    apply (simp add: X64_H.setCurrentVSpaceRoot_def set_current_vspace_root_def)
    apply (rule corres_guard_imp)
      apply (rule corres_split_eqr)
         apply (rule set_current_cr3_corres, simp add: cr3_relation_def addrFromKPPtr_def)
        apply (subst corres_gets)
        apply (clarsimp simp: state_relation_def arch_state_relation_def)
       apply (wp | simp)+
    done
  have Q: "\<And>P P'. corres dc P P'
        (throwError ExceptionTypes_A.lookup_failure.InvalidRoot <catch>
         (\<lambda>_ . do global_pml4 \<leftarrow> gets (x64_global_pml4 \<circ> arch_state);
                  set_current_vspace_root (X64.addrFromKPPtr global_pml4) 0
               od))
        (throwError Fault_H.lookup_failure.InvalidRoot <catch>
         (\<lambda>_ . do globalPML4 \<leftarrow> gets (x64KSGlobalPML4 \<circ> ksArchState);
                  setCurrentVSpaceRoot (addrFromKPPtr globalPML4) 0
               od))"
    apply (rule corres_guard_imp)
      apply (rule corres_split_catch [where f=lfr])
         apply (simp, rule P)
        apply (subst corres_throwError, simp add: lookup_failure_map_def)
       apply (wp | simp)+
    done
  show ?thesis
    unfolding set_vm_root_def setVMRoot_def getThreadVSpaceRoot_def locateSlot_conv
              catchFailure_def withoutFailure_def throw_def
    apply (rule corres_guard_imp)
      apply (rule corres_split' [where r'="op = \<circ> cte_map"])
         apply (simp add: tcbVTableSlot_def cte_map_def objBits_def cte_level_bits_def
                          objBitsKO_def tcb_cnode_index_def to_bl_1 assms)
        apply (rule_tac R="\<lambda>thread_root. valid_arch_state and valid_asid_map and
                                         valid_arch_objs and valid_vs_lookup and
                                         unique_table_refs o caps_of_state and
                                         valid_global_objs and valid_objs and
                                         pspace_aligned and pspace_distinct and
                                         cte_wp_at (op = thread_root) thread_root_slot"
                    and R'="\<lambda>thread_root. pspace_aligned' and pspace_distinct' and no_0_obj'"
                 in corres_split [OF _ getSlotCap_corres])
           apply (case_tac rv; simp add: isCap_simps Q[simplified])
           apply (rename_tac arch_cap)
           apply (case_tac arch_cap; simp add: isCap_simps Q[simplified])
           apply (rename_tac pm_ptr pm_mapped)
           apply (case_tac pm_mapped; simp add: Q[simplified])
           apply (clarsimp simp: cap_asid_def)
           apply (rule corres_guard_imp)
             apply (rule corres_split_catch [where f=lfr, OF P _ wp_post_tautE wp_post_tautE])
             apply (rule corres_split_eqrE [OF _ find_vspace_for_asid_corres[OF refl]])
               apply (rule whenE_throwError_corres; simp add: lookup_failure_map_def)
               apply (rule corres_split_norE)
                  apply (simp only: liftE_bindE)
                  apply (rule corres_split'[OF get_current_cr3_corres])
                    apply (rule corres_whenE[OF _ _ dc_simp])
                     apply (case_tac rv; case_tac rv'; clarsimp simp: cr3_relation_def)
                    apply (rule iffD2[OF corres_liftE_rel_sum, OF set_current_cr3_corres])
                    apply (simp add: cr3_relation_def)
                   apply wp
                  apply wpsimp
                 apply simp
                 apply (rule update_asid_map_corres[OF refl])
                apply wp
               apply wp
              apply (wp find_vspace_for_asid_wp)
             apply (wp hoare_drop_imps)
            apply clarsimp
            apply (frule (6) pml4_cap_vspace_at_uniq)
            apply (frule (1) cte_wp_at_valid_objs_valid_cap)
            apply (fastforce simp: valid_cap_def mask_def word_neq_0_conv vspace_at_uniq_ex_def)
           apply simp
          apply wpsimp
         apply (wpsimp wp: get_cap_wp)
        apply wp
       apply wp
      apply wp
     using tcb_at_cte_at_1 by auto
qed


lemma get_asid_pool_corres_inv':
  assumes "p' = p"
  shows "corres (\<lambda>p. (\<lambda>p'. p = p' o ucast) \<circ> inv ASIDPool)
                (asid_pool_at p) (pspace_aligned' and pspace_distinct')
                (get_asid_pool p) (getObject p')"
  apply (rule corres_rel_imp)
   apply (rule get_asid_pool_corres'[OF assms])
  apply simp
  done

(* FIXME x64: move *)
lemma no_fail_invalidateASID[wp]: "no_fail \<top> (invalidateASID a b)"
  by (simp add: invalidateASID_def)

(* FIXME x64: move *)
lemma no_fail_hwASIDInvalidate[wp]: "no_fail \<top> (hwASIDInvalidate a b)"
  by (simp add: hwASIDInvalidate_def no_fail_invalidateASID)

lemma dmo_vspace_at_uniq [wp]:
  "\<lbrace>vspace_at_uniq a pd\<rbrace> do_machine_op f \<lbrace>\<lambda>_. vspace_at_uniq a pd\<rbrace>"
  apply (simp add: do_machine_op_def split_def)
  apply wp
  apply (simp add: vspace_at_uniq_def)
  done

lemma dMo_no_0_obj'[wp]:
  "\<lbrace>no_0_obj'\<rbrace> doMachineOp f \<lbrace>\<lambda>_. no_0_obj'\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply wp
  by (simp add: no_0_obj'_def)

lemma dmo_vspace_at_uniq_ex [wp]:
  "\<lbrace>vspace_at_uniq_ex asid\<rbrace> do_machine_op f \<lbrace>\<lambda>_. vspace_at_uniq_ex asid\<rbrace>"
  apply (simp add: do_machine_op_def split_def)
  by (wpsimp simp: vspace_at_uniq_ex_def vspace_at_uniq_def vspace_at_asid_def)

lemma invalidate_asid_entry_corres:
  assumes "pm' = pm" "asid' = asid"
  shows "corres dc (valid_arch_objs and valid_asid_map
                      and K (asid \<le> mask asid_bits \<and> asid \<noteq> 0)
                      and vspace_at_asid asid pm and valid_vs_lookup
                      and unique_table_refs o caps_of_state
                      and valid_global_objs and valid_arch_state
                      and pspace_aligned and pspace_distinct)
                   (pspace_aligned' and pspace_distinct' and no_0_obj')
                   (invalidate_asid_entry asid pm) (invalidateASIDEntry asid' pm')"
  using assms
  apply (simp add: invalidate_asid_entry_def invalidateASIDEntry_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split)
       apply (rule invalidate_asid_corres[OF refl])
      apply (rule corres_machine_op)
      apply (rule corres_Id, rule refl, simp)
      apply wp
     apply (wp | clarsimp cong: if_cong)+
   apply (fastforce simp: vspace_at_uniq_ex_def intro: vspace_at_asid_uniq)
  apply simp
  done

crunch aligned'[wp]: invalidateASID' "pspace_aligned'"
crunch distinct'[wp]: invalidateASID' "pspace_distinct'"

lemma invalidateASID_cur' [wp]:
  "\<lbrace>cur_tcb'\<rbrace> invalidateASID' x \<lbrace>\<lambda>_. cur_tcb'\<rbrace>"
  by (simp add: invalidateASID'_def|wp)+

crunch aligned' [wp]: invalidateASIDEntry pspace_aligned'
crunch distinct' [wp]: invalidateASIDEntry pspace_distinct'
crunch cur' [wp]: invalidateASIDEntry cur_tcb'

lemma dMo_x64KSASIDTable_inv[wp]:
  "\<lbrace>\<lambda>s. P (x64KSASIDTable (ksArchState s))\<rbrace> doMachineOp f \<lbrace>\<lambda>_ s. P (x64KSASIDTable (ksArchState s))\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply wp
  by (clarsimp)

lemma dMo_valid_arch_state'[wp]:
  "\<lbrace>\<lambda>s. P (valid_arch_state' s)\<rbrace> doMachineOp f \<lbrace>\<lambda>_ s. P (valid_arch_state' s)\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply wp
  by (clarsimp)

lemma invalidateASID_valid_arch_state [wp]:
  "\<lbrace>valid_arch_state'\<rbrace> invalidateASIDEntry x y \<lbrace>\<lambda>_. valid_arch_state'\<rbrace>"
  apply (simp add: invalidateASID'_def invalidateASIDEntry_def hwASIDInvalidate_def)
  apply (wpsimp simp: valid_arch_state'_def doMachineOp_def split_def)
  apply (clarsimp simp: is_inv_None_upd fun_upd_def[symmetric]
                        comp_upd_simp inj_on_fun_upd_elsewhere
                        valid_asid_map'_def)
  by (auto elim!: subset_inj_on dest!: ran_del_subset)[1]

crunch no_0_obj'[wp]: deleteASID "no_0_obj'"
  (ignore: getObject simp: crunch_simps
       wp: crunch_wps getObject_inv loadObject_default_inv)

(* FIXME x64: move *)
lemma set_asid_pool_asid_map_unmap:
  "\<lbrace>valid_asid_map and ko_at (ArchObj (X64_A.ASIDPool ap)) p and
    (\<lambda>s. \<forall>asid. asid \<le> mask asid_bits \<longrightarrow>
                ucast asid = x \<longrightarrow>
                x64_asid_table (arch_state s) (asid_high_bits_of asid) = Some p \<longrightarrow>
                x64_asid_map (arch_state s) asid = None)\<rbrace>
       set_asid_pool p (ap(x := None)) \<lbrace>\<lambda>_. valid_asid_map\<rbrace>"
  using set_asid_pool_restrict_asid_map[where S="- {x}"]
  by (simp add: restrict_map_def fun_upd_def if_flip)

(* FIXME x64: move *)
lemma set_asid_pool_arch_objs_unmap_single:
  "\<lbrace>valid_arch_objs and ko_at (ArchObj (X64_A.ASIDPool ap)) p\<rbrace>
       set_asid_pool p (ap(x := None)) \<lbrace>\<lambda>_. valid_arch_objs\<rbrace>"
  using set_asid_pool_arch_objs_unmap[where S="- {x}"]
  by (simp add: restrict_map_def fun_upd_def if_flip)

(* FIXME x64: move *)
lemma invalidate_asid_entry_valid_arch_state[wp]:
  "\<lbrace>valid_arch_state\<rbrace> invalidate_asid_entry asid pm \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  apply (simp add: invalidate_asid_entry_def invalidate_asid_def)
  apply wp
   apply (simp add: do_machine_op_def split_def)
   apply wp
  by (clarsimp simp: valid_arch_state_def simp del: fun_upd_apply)

lemma valid_global_objs_asid_map_update_inv[simp]:
  "valid_global_objs s \<Longrightarrow> valid_global_objs (s\<lparr>arch_state := arch_state s \<lparr>x64_asid_map := b\<rparr>\<rparr>)"
  by (clarsimp simp: valid_global_objs_def)

crunch valid_global_objs[wp]: invalidate_asid_entry "valid_global_objs"


lemma delete_asid_corres [corres]:
  assumes "asid' = asid" "pm' = pm"
  notes set_asid_pool_simpler_def[simp del]
  shows "corres dc
          (invs and valid_etcbs and K (asid \<le> mask asid_bits \<and> asid \<noteq> 0))
          (pspace_aligned' and pspace_distinct' and no_0_obj'
              and valid_arch_state' and cur_tcb')
          (delete_asid asid pm) (deleteASID asid' pm')"
  using assms
  apply (simp add: delete_asid_def deleteASID_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split [OF _ corres_gets_asid])
      apply (case_tac "asid_table (asid_high_bits_of asid)", simp)
      apply clarsimp
      apply (rule_tac P="\<lambda>s. asid_high_bits_of asid \<in> dom (asidTable o ucast) \<longrightarrow>
                             asid_pool_at (the ((asidTable o ucast) (asid_high_bits_of asid))) s" and
                      P'="pspace_aligned' and pspace_distinct'" and
                      Q="invs and valid_etcbs and K (asid \<le> mask asid_bits \<and> asid \<noteq> 0) and
                         (\<lambda>s. x64_asid_table (arch_state s) = asidTable \<circ> ucast)" in
                      corres_split)
         prefer 2
         apply (simp add: dom_def)
         apply (rule get_asid_pool_corres_inv'[OF refl])
        apply (rule corres_when, simp add: mask_asid_low_bits_ucast_ucast)
        apply (rule corres_split [OF _ invalidate_asid_entry_corres[where pm=pm]])
            apply (rule_tac P="asid_pool_at (the (asidTable (ucast (asid_high_bits_of asid))))
                               and valid_etcbs"
                        and P'="pspace_aligned' and pspace_distinct'"
                         in corres_split)
               prefer 2
               apply (simp del: fun_upd_apply)
               apply (rule set_asid_pool_corres')
               apply (simp add: inv_def mask_asid_low_bits_ucast_ucast)
               apply (rule ext)
               apply (clarsimp simp: o_def)
              apply (rule corres_split [OF _ gct_corres])
                apply simp
                apply (rule set_vm_root_corres[OF refl])
               apply wp+
             apply (thin_tac "x = f o g" for x f g)
             apply (simp del: fun_upd_apply)
             apply (fold cur_tcb_def)
           apply (wp set_asid_pool_asid_map_unmap
                     set_asid_pool_vs_lookup_unmap'
                     set_asid_pool_arch_objs_unmap_single)+
          apply simp
            apply (fold cur_tcb'_def)
          apply (wp add: invalidate_asid_entry_invalidates | clarsimp simp: o_def)+
       apply (subgoal_tac "vspace_at_asid asid pm s")
        apply (auto simp: obj_at_def a_type_def graph_of_def
                   split: if_split_asm)[1]
       apply (simp add: vspace_at_asid_def)
       apply (rule vs_lookupI)
        apply (simp add: vs_asid_refs_def)
        apply (rule image_eqI[OF refl])
        apply (erule graph_ofI)
       apply (rule r_into_rtrancl)
       apply simp
       apply (erule vs_lookup1I [OF _ _ refl])
       apply (simp add: vs_refs_def)
       apply (rule image_eqI[rotated], erule graph_ofI)
       apply (simp add: mask_asid_low_bits_ucast_ucast)
      apply wp
      apply (simp add: o_def)
      apply (wp getASID_wp)
      apply clarsimp
      apply assumption
     apply wp+
   apply clarsimp
   apply (clarsimp simp: valid_arch_state_def valid_asid_table_def
                  dest!: invs_arch_state)
   apply blast
  apply (clarsimp simp: valid_arch_state'_def valid_asid_table'_def)
  done

lemma valid_arch_state_unmap_strg':
  "valid_arch_state' s \<longrightarrow>
   valid_arch_state' (s\<lparr>ksArchState :=
                        x64KSASIDTable_update (\<lambda>_. (x64KSASIDTable (ksArchState s))(ptr := None))
                         (ksArchState s)\<rparr>)"
  apply (simp add: valid_arch_state'_def valid_asid_table'_def)
  apply (auto simp: ran_def split: if_split_asm)
  done

crunch x64KSASIDTable_inv[wp]: invalidateASIDEntry
    "\<lambda>s. P (x64KSASIDTable (ksArchState s))"

lemma delete_asid_pool_corres:
  assumes "base' = base" "ptr' = ptr"
  shows "corres dc (invs and K (is_aligned base asid_low_bits
                                  \<and> base \<le> mask asid_bits)
                         and asid_pool_at ptr)
                   (pspace_aligned' and pspace_distinct' and no_0_obj'
                         and valid_arch_state' and cur_tcb')
                   (delete_asid_pool base ptr) (deleteASIDPool base ptr)"
  using assms
  apply (simp add: delete_asid_pool_def deleteASIDPool_def)
  apply (rule corres_assume_pre, simp add: is_aligned_mask cong: corres_weak_cong)
  apply (thin_tac P for P)+
  apply (rule corres_guard_imp)
    apply (rule corres_split [OF _ corres_gets_asid])
      apply (rule corres_when)
       apply simp
      apply (simp add: liftM_def)
      apply (rule corres_split [OF _ get_asid_pool_corres'[OF refl]])
        apply (rule corres_split)
           prefer 2
           apply (rule corres_mapM [where r=dc and r'=dc], simp, simp)
               prefer 5
               apply (rule order_refl)
              apply (rule_tac P="invs and ko_at (ArchObj (arch_kernel_obj.ASIDPool pool)) ptr
                                      and [VSRef (ucast (asid_high_bits_of base)) None] \<rhd> ptr
                                      and K (is_aligned base asid_low_bits \<and> base \<le> mask asid_bits)"
                          and P'="pspace_aligned' and pspace_distinct' and no_0_obj'"
                       in corres_guard_imp)
                apply (rule corres_when)
                 apply (clarsimp simp: ucast_ucast_low_bits)
                apply (simp add: ucast_ucast_low_bits)
                apply (rule_tac pm="the (inv ASIDPool x xa)"
                         in invalidate_asid_entry_corres[OF refl refl])
               apply (clarsimp simp: invs_def valid_state_def valid_arch_caps_def valid_pspace_def
                                     vspace_at_asid_def
                              cong: conj_cong)
               apply (rule conjI)
                apply (clarsimp simp: mask_def asid_low_bits_word_bits
                               elim!: is_alignedE)
                apply (subgoal_tac "of_nat q < (2 ^ asid_high_bits :: machine_word)")
                 apply (subst mult.commute, rule word_add_offset_less)
                     apply assumption
                    apply assumption
                   apply (simp add: asid_bits_def word_bits_def)
                  apply (erule order_less_le_trans)
                  apply (simp add: word_bits_def asid_low_bits_def asid_high_bits_def)
                 apply (simp add: asid_bits_def asid_high_bits_def asid_low_bits_def)
                apply (drule word_power_less_diff)
                 apply (drule of_nat_mono_maybe[where 'a=machine_word_len, rotated])
                  apply (simp add: word_bits_def asid_low_bits_def)
                 apply (subst word_unat_power, simp)
                apply (simp add: asid_bits_def word_bits_def)
                apply (simp add: asid_low_bits_def word_bits_def)
                apply (simp add: asid_bits_def asid_low_bits_def asid_high_bits_def)
               apply (subst conj_commute, rule context_conjI)
                apply (erule vs_lookup_trancl_step)
                apply (rule r_into_trancl)
                apply (erule vs_lookup1I)
                 apply (simp add: vs_refs_def)
                 apply (rule image_eqI[rotated])
                  apply (rule graph_ofI, simp)
                 apply (clarsimp simp: ucast_ucast_low_bits)
                 apply fastforce
                apply (simp add: add_mask_eq asid_low_bits_word_bits
                                 ucast_ucast_mask asid_low_bits_def[symmetric]
                                 asid_high_bits_of_def)
                apply (rule conjI)
                 apply (rule sym)
                 apply (simp add: is_aligned_add_helper[THEN conjunct1]
                                  mask_eq_iff_w2p asid_low_bits_def word_size)
                apply (rule_tac f="\<lambda>a. a && mask n" for n in arg_cong)
                apply (rule shiftr_eq_mask_eq)
                apply (simp add: is_aligned_add_helper is_aligned_neg_mask_eq)
               apply clarsimp
               apply (subgoal_tac "base \<le> base + xa")
                apply (simp add: valid_vs_lookup_def asid_high_bits_of_def)
                subgoal by (fastforce intro: vs_lookup_pages_vs_lookupI)
               apply (erule is_aligned_no_wrap')
               apply (simp add: asid_low_bits_word_bits)
              apply (simp add: asid_low_bits_word_bits)
             apply clarsimp
             apply ((wp|clarsimp simp: o_def)+)[3]
          apply (rule corres_split)
             prefer 2
             apply (rule corres_modify [where P=\<top> and P'=\<top>])
             apply (simp add: state_relation_def arch_state_relation_def)
             apply (rule ext)
             apply clarsimp
             apply (erule notE)
             apply (rule word_eqI)
             apply (drule_tac x1="ucast xa" in bang_eq [THEN iffD1])
             apply (erule_tac x=n in allE)
             apply (simp add: word_size nth_ucast)
            apply (rule corres_split)
               prefer 2
               apply (rule gct_corres)
              apply (simp only:)
              apply (rule set_vm_root_corres[OF refl])
             apply wp+
         apply (rule_tac R="\<lambda>_ s. rv = x64_asid_table (arch_state s)"
                  in hoare_post_add)
         apply (drule sym, simp only: )
         apply (drule sym, simp only: )
         apply (thin_tac "P" for P)+
         apply (simp only: pred_conj_def cong: conj_cong)
         apply simp
         apply (fold cur_tcb_def)
         apply (strengthen valid_arch_state_unmap_strg
                           valid_arch_objs_unmap_strg
                           valid_asid_map_unmap
                           valid_vs_lookup_unmap_strg)
         apply (simp add: valid_global_objs_arch_update)
         apply (rule hoare_vcg_conj_lift,
                (rule mapM_invalidate[where ptr=ptr, simplified])?,
                 ((wp mapM_wp' | simp)+)[1])+
        apply (rule_tac R="\<lambda>_ s. rv' = x64KSASIDTable (ksArchState s)"
                 in hoare_post_add)
        apply (simp only: pred_conj_def cong: conj_cong)
        apply simp
        apply (strengthen valid_arch_state_unmap_strg')
        apply (fold cur_tcb'_def)
        apply (wp mapM_wp')
        apply (clarsimp simp: cur_tcb'_def)
       apply (simp add: o_def pred_conj_def)
       apply wp
      apply (wp getASID_wp)+
   apply (clarsimp simp: conj_comms)
   apply (auto simp: vs_lookup_def intro: vs_asid_refsI)[1]
  apply clarsimp
  done

crunch typ_at' [wp]: findVSpaceForASID "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps getObject_inv simp: crunch_simps loadObject_default_def ignore: getObject)

crunch typ_at' [wp]: setVMRoot "\<lambda>s. P (typ_at' T p s)"
  (simp: crunch_simps)

lemmas setVMRoot_typ_ats [wp] = typ_at_lifts [OF setVMRoot_typ_at']

lemma findVSpaceForASID_inv2:
  "\<lbrace>\<lambda>s. asid \<noteq> 0 \<and> asid \<le> mask asid_bits \<longrightarrow> P s\<rbrace> findVSpaceForASID asid \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (cases "asid \<noteq> 0 \<and> asid \<le> mask asid_bits")
   apply (simp add: findVSpaceForASID_inv)
  apply (simp add: findVSpaceForASID_def assertE_def asidRange_def mask_def)
  apply clarsimp
  done

crunch no_0_obj'[wp]: flushTable "no_0_obj'"
  (ignore: getObject wp: crunch_wps simp: crunch_simps loadObject_default_inv)

lemma get_pt_sp: "\<lbrace>P\<rbrace> get_pt p \<lbrace>\<lambda>rv. P and ako_at (PageTable rv) p\<rbrace>"
  by (rule hoare_weaken_pre[OF get_pt_wp]) simp

(* FIXME x64: move to Lib *)
lemma get_mapM_x_lower:
  fixes P :: "'a option \<Rightarrow> 's \<Rightarrow> bool"
  fixes f :: "('s,'a) nondet_monad"
  fixes g :: "'a \<Rightarrow> 'b \<Rightarrow> ('s,'c) nondet_monad"
  -- "@{term g} preserves the state that @{term f} cares about"
  assumes g: "\<And>x y. \<lbrace> P (Some x) \<rbrace> g x y \<lbrace> \<lambda>_. P (Some x) \<rbrace>"
  -- "@{term P} specifies whether @{term f} either fails or returns a deterministic result"
  assumes f: "\<And>opt_x s. P opt_x s \<Longrightarrow> f s = case_option ({},True) (\<lambda>x. ({(x,s)},False)) opt_x"
  -- "Every state determines P, and therefore the behaviour of @{term f}"
  assumes x: "\<And>s. \<exists> opt_x. P opt_x s"
  -- "If @{term f} may fail, ensure there is at least one @{term f}"
  assumes y: "\<exists>s. P None s \<Longrightarrow> ys \<noteq> []"
  shows "do x \<leftarrow> f; mapM_x (g x) ys od = mapM_x (\<lambda>y. do x \<leftarrow> f; g x y od) ys"
  proof -
    have f_rv: "\<lbrace>\<top>\<rbrace> f \<lbrace>\<lambda>r. P (Some r)\<rbrace>"
      using x f
      apply (clarsimp simp: valid_def)
      apply (drule_tac x=s in meta_spec; clarsimp)
      apply (case_tac opt_x; simp)
      done
    { fix y and h :: "'a \<Rightarrow> ('s,'d) nondet_monad"
      have "do x \<leftarrow> f; _ \<leftarrow> g x y; h x od
              = do x \<leftarrow> f; _ \<leftarrow> g x y; x \<leftarrow> f; h x od"
        apply (rule ext)
        apply (subst monad_eq_split[where g="do x \<leftarrow> f; g x y; return x od"
                                      and P="\<top>" and Q="\<lambda>r. P (Some r)"
                                      and f="h" and f'="\<lambda>_. f >>= h",
                                    simplified bind_assoc, simplified])
        apply (wpsimp wp: g f_rv simp: f return_def bind_def)+
        done
    } note f_redundant = this
    show ?thesis
    proof (cases "\<exists>s. P None s")
      case True show ?thesis
        apply (cases ys; simp add: True y mapM_x_Cons bind_assoc)
        subgoal for y ys
          apply (thin_tac _)
          apply (induct ys arbitrary: y; simp add: mapM_x_Nil mapM_x_Cons bind_assoc)
          apply (subst f_redundant; simp)
          done
        done
    next
      case False
      show ?thesis using False
        apply (induct ys; simp add: mapM_x_Nil mapM_x_Cons bind_assoc)
         apply (rule ext)
         subgoal for s
           by (insert x[of s]; drule spec[of _ s]; clarsimp; case_tac opt_x;
               clarsimp simp: bind_def return_def f)
        apply (subst f_redundant; simp)
        done
    qed
  qed

(* FIXME x64: move to invariants *)
lemma get_pt_mapM_x_lower:
  assumes g: "\<And>P pt x. \<lbrace> \<lambda>s. P (kheap s pt_ptr) \<rbrace> g pt x \<lbrace> \<lambda>_ s. P (kheap s pt_ptr) \<rbrace>"
  assumes y: "ys \<noteq> []"
  notes [simp] = get_pt_def get_object_def gets_def get_def bind_def return_def
                 assert_def fail_def
  shows "do pt \<leftarrow> get_pt pt_ptr; mapM_x (g pt) ys od
          = mapM_x (\<lambda>y. get_pt pt_ptr >>= (\<lambda>pt. g pt y)) ys"
  apply (rule get_mapM_x_lower
                [where P="\<lambda>opt_pt s. case kheap s pt_ptr of
                                       Some (ArchObj (PageTable pt)) \<Rightarrow> opt_pt = Some pt
                                     | _ \<Rightarrow> opt_pt = None",
                 OF _ _ _ y])
    apply (wp g)
   apply (case_tac "kheap s pt_ptr"; simp; rename_tac ko; case_tac ko; simp;
          rename_tac ako; case_tac ako; simp)+
  done

(* FIXME x64: move to invariants *)
lemma get_pt_get_pte:
  assumes align: "is_aligned pt_ptr pt_bits"
  shows "do pt \<leftarrow> get_pt pt_ptr; f (pt i) od
            = do pte \<leftarrow> get_pte (pt_ptr + (ucast i << word_size_bits)); f pte od"
  proof -
    have i: "ucast i < (2::machine_word) ^ (pt_bits - word_size_bits)"
      by (rule less_le_trans[OF ucast_less]; simp add: bit_simps)
    have s: "ucast i << word_size_bits < (2::machine_word) ^ pt_bits"
      by (rule shiftl_less_t2n[OF i]; simp add: bit_simps)
    show ?thesis
      apply (simp add: get_pte_def is_aligned_add_helper align s)
      apply (simp add: shiftl_shiftr_id less_le_trans[OF i] bit_simps ucast_ucast_id)
      done
  qed

lemma get_pte_corres'':
  assumes "p' = p"
  shows "corres pte_relation' (pte_at p) (pspace_aligned' and pspace_distinct')
                              (get_pte p) (getObject p')"
  using assms get_pte_corres' by simp

(* FIXME: move to Lib *)
lemma zip_map_rel:
  assumes "(x,y) \<in> set (zip xs ys)" "map f xs = map g ys"
  shows "f x = g y"
  using assms by (induct xs arbitrary: x y ys; cases ys) auto

lemma flush_table_corres:
  assumes "pm' = pm" "vptr' = vptr" "pt' = pt" "asid' = asid"
  shows "corres dc (pspace_aligned and valid_objs and valid_arch_state
                      and cur_tcb and vspace_at_asid asid pm and valid_asid_map
                      and valid_arch_objs and pspace_aligned and pspace_distinct
                      and valid_vs_lookup and valid_global_objs
                      and unique_table_refs o caps_of_state and page_table_at pt
                      and K (is_aligned vptr pd_shift_bits \<and> asid \<le> mask asid_bits \<and> asid \<noteq> 0))
                   (pspace_aligned' and pspace_distinct' and no_0_obj'
                      and valid_arch_state' and cur_tcb')
                   (flush_table pm vptr pt asid)
                   (flushTable pm' vptr' pt' asid')"
  proof -
    have b: "ptTranslationBits + pageBits = pd_shift_bits"
      by (simp add: bit_simps)
    show ?thesis
      using assms
      apply (simp add: flush_table_def flushTable_def)
      apply (rule corres_assume_pre)
      apply (simp add: b is_aligned_mask[symmetric] cong: corres_weak_cong)
      apply (subst get_pt_mapM_x_lower)
        apply (solves \<open>wpsimp simp: upto_enum_def\<close>)+
      apply (subst get_pt_get_pte)
       apply (clarsimp elim!: is_aligned_pt)
      apply (thin_tac "P" for P)+
      apply (rule subst[of "0x1FF" "-1::9 word"], simp)
      apply (rule corres_mapM_x[OF _ _ _ _ subset_refl])
         apply (frule zip_map_rel[where f=ucast and g=id, simplified])
          apply (simp add: upto_enum_def bit_simps ucast_of_nat_small)
         apply (rule corres_guard_imp)
           apply (rule corres_split[OF _ get_pte_corres''])
              apply (case_tac rv; case_tac rv'; simp)
              apply (rule corres_machine_op)
              apply (subgoal_tac "ucast x = y"; simp)
              apply (rule corres_rel_imp[OF corres_underlying_trivial]; simp)
              apply (wpsimp simp: invalidateTranslationSingleASID_def)
             apply (simp add: bit_simps objBits_simps archObjSize_def)
            apply (wpsimp)+
          apply (rule page_table_pte_atI; simp add: bit_simps ucast_less[where 'b=9, simplified])
         apply simp
        apply (wpsimp wp: hoare_drop_imps)
       apply (wpsimp wp: hoare_drop_imps)
      apply (simp add: bit_simps)
      done
  qed

crunch typ_at' [wp]: flushTable "\<lambda>s. P (typ_at' T p s)"
  (simp: assertE_def when_def wp: crunch_wps ignore: getObject)

lemmas flushTable_typ_ats' [wp] = typ_at_lifts [OF flushTable_typ_at']

lemmas findVSpaceForASID_typ_ats' [wp] = typ_at_lifts [OF findVSpaceForASID_typ_at']

crunch inv [wp]: findVSpaceForASID P
  (simp: assertE_def whenE_def loadObject_default_def
   wp: crunch_wps getObject_inv ignore: getObject)

crunch aligned'[wp]: unmapPageTable, unmapPageDirectory, unmapPDPT "pspace_aligned'"
  (ignore: getObject simp: crunch_simps
       wp: crunch_wps getObject_inv loadObject_default_inv)
crunch distinct'[wp]: unmapPageTable, unmapPageDirectory, unmapPDPT "pspace_distinct'"
  (ignore: getObject simp: crunch_simps
       wp: crunch_wps getObject_inv loadObject_default_inv)


crunch no_0_obj'[wp]: storePDE, storePTE, storePDPTE, storePML4E no_0_obj'

crunch valid_arch'[wp]: storePDE, storePTE, storePDPTE, storePML4E valid_arch_state'
(ignore: setObject)

crunch cur_tcb'[wp]: storePDE, storePTE, storePDPTE, storePML4E cur_tcb'
(ignore: setObject)

lemma getCurrentCR3_inv: "\<lbrace>P\<rbrace> getCurrentCR3 \<lbrace>\<lambda>_. P\<rbrace>"
  by (simp add: getCurrentCR3_def)

lemma invalidate_local_page_structure_cache_asid_corres:
  shows
  "corres dc \<top> \<top>
     (invalidate_local_page_structure_cache_asid a b)
     (X64_H.invalidateLocalPageStructureCacheASID a b)"
  apply (simp add: invalidate_local_page_structure_cache_asid_def
                   X64_H.invalidateLocalPageStructureCacheASID_def)
  by (corressimp corres: get_current_cr3_corres set_current_cr3_corres
                        wp: get_current_cr3_inv getCurrentCR3_inv
                      simp: cr3_relation_def)

lemmas invalidatePageStructureCacheASID_corres = invalidate_local_page_structure_cache_asid_corres
                      [folded invalidatePageStructureCacheASID_def]

(* FIXME x64: move *)
lemma flush_table_pde_at[wp]: "\<lbrace>pde_at p\<rbrace> flush_table a b c d \<lbrace>\<lambda>_. pde_at p\<rbrace>"
  by (wpsimp simp: flush_table_def pde_at_def wp: flush_table_typ_at mapM_x_wp')

crunch inv[wp]: lookupPTSlot "P"
  (wp: loadObject_default_inv)

lemma unmap_page_table_corres:
  assumes "asid' = asid" "vptr' = vptr" "pt' = pt"
  notes liftE_get_pde_corres = get_pde_corres'[THEN corres_liftE_rel_sum[THEN iffD2]]
  shows "corres dc
          (invs and valid_etcbs and page_table_at pt and
           K (0 < asid \<and> is_aligned vptr pd_shift_bits \<and> vptr < pptr_base \<and> canonical_address vptr \<and> asid \<le> mask asid_bits))
          (valid_arch_state' and pspace_aligned' and pspace_distinct'
            and no_0_obj' and cur_tcb' and valid_objs')
          (unmap_page_table asid vptr pt)
          (unmapPageTable asid' vptr' pt')"
  apply (clarsimp simp: assms unmap_page_table_def unmapPageTable_def ignoreFailure_def const_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_catch[where E="\<top>\<top>" and E'="\<top>\<top>"], simp)
      apply (rule corres_split_eqrE[OF _ find_vspace_for_asid_corres[OF refl]])
        apply (rule corres_split_eqrE[OF _ lookup_pd_slot_corres])
          apply (rule corres_splitEE[OF _ liftE_get_pde_corres])
            apply (rule corres_splitEE[where r'=dc])
               prefer 2
               apply (case_tac "\<exists>addr x xa. pde = X64_A.PageTablePDE addr x xa";
                      fastforce intro!: corres_returnOkTT
                                simp: lookup_failure_map_def pde_relation_def
                                split: X64_A.pde.splits)
              apply simp
              apply (rule corres_split[OF _ flush_table_corres[OF refl refl refl refl]])
                apply (rule corres_split[OF _ store_pde_corres'])
                   apply (rule invalidatePageStructureCacheASID_corres)
                  apply simp
                 apply ((wpsimp wp: hoare_if get_pde_wp getPDE_wp)+)[8]
         apply ((wpsimp wp: lookup_pd_slot_wp hoare_vcg_all_lift_R | wp_once hoare_drop_imps)+)[2]
       apply ((wp find_vspace_for_asid_wp)+)[4]
   apply (clarsimp simp: invs_def valid_state_def valid_pspace_def valid_arch_caps_def
                         word_neq_0_conv[symmetric])
   apply (frule (3) find_vspace_for_asid_eq_helper; fastforce simp: vspace_at_asid_def)
  apply simp
  done

crunch aligned' [wp]: unmapPage pspace_aligned'
  (wp: crunch_wps simp: crunch_simps ignore: getObject)

crunch distinct' [wp]: unmapPage pspace_distinct'
  (wp: crunch_wps simp: crunch_simps ignore: getObject)

lemma corres_split_strengthen_ftE:
  "\<lbrakk> corres (ftr \<oplus> r') P P' f j;
      \<And>rv rv'. r' rv rv' \<Longrightarrow> corres (ftr' \<oplus> r) (R rv) (R' rv') (g rv) (k rv');
      \<lbrace>Q\<rbrace> f \<lbrace>R\<rbrace>,-; \<lbrace>Q'\<rbrace> j \<lbrace>R'\<rbrace>,- \<rbrakk>
    \<Longrightarrow> corres (dc \<oplus> r) (P and Q) (P' and Q') (f >>=E (\<lambda>rv. g rv)) (j >>=E (\<lambda>rv'. k rv'))"
  apply (rule_tac r'=r' in corres_splitEE)
     apply (rule corres_rel_imp, assumption)
     apply (case_tac x, auto)[1]
    apply (erule corres_rel_imp)
    apply (case_tac x, auto)[1]
   apply (simp add: validE_R_def)+
  done

lemma check_mapping_corres:
  "page_entry_map m m' \<Longrightarrow> corres (dc \<oplus> dc) \<top> \<top>
      (unlessE (check_mapping_pptr pptr m) $ throwError ExceptionTypes_A.InvalidRoot)
      (checkMappingPPtr pptr m')"
  apply (simp add: liftE_bindE check_mapping_pptr_def
                   checkMappingPPtr_def)
  apply (cases m, simp_all add: liftE_bindE)
    apply (clarsimp simp: page_entry_map_def)
    apply (case_tac x1; auto simp: unlessE_def corres_returnOk)
   apply (clarsimp simp: page_entry_map_def)
   apply (case_tac x2; auto simp: unlessE_def corres_returnOk)
  apply (clarsimp simp: page_entry_map_def)
  apply (case_tac x3; auto simp: unlessE_def corres_returnOk)
  done

crunch inv[wp]: checkMappingPPtr "P"
  (wp: crunch_wps loadObject_default_inv simp: crunch_simps)

lemma set_pt_vs_lookup [wp]:
  "\<lbrace>\<lambda>s. P (vs_lookup s)\<rbrace> set_pt p pt \<lbrace>\<lambda>x s. P (vs_lookup s)\<rbrace>"
  apply (simp add: update_object_def)
  apply (wpsimp wp: get_object_wp set_object_wp simp: a_type_simps obj_at_def)
  apply (erule rsubst [where P=P])
  by (rule order_antisym; rule vs_lookup_sub;
      clarsimp simp: obj_at_def vs_refs_def split: if_splits)

lemma store_pte_vspace_at_asid[wp]:
  "\<lbrace>vspace_at_asid asid pm\<rbrace> store_pte p pte \<lbrace>\<lambda>_. vspace_at_asid asid pm\<rbrace>"
  apply (simp only: store_pte_def vspace_at_asid_def)
  apply wp
  done

(* FIXME x64: move *)
lemma no_fail_invalidateTranslationSingleASID[wp]:
  "no_fail \<top> (invalidateTranslationSingleASID v a)"
  by (simp add: invalidateTranslationSingleASID_def)

lemmas liftE_get_pde_corres = get_pde_corres'[THEN corres_liftE_rel_sum[THEN iffD2]]
lemmas liftE_get_pte_corres = get_pte_corres'[THEN corres_liftE_rel_sum[THEN iffD2]]
lemmas liftE_get_pdpte_corres = get_pdpte_corres'[THEN corres_liftE_rel_sum[THEN iffD2]]

(* Wrap up the standard usage pattern of wp/wpc/simp into its own command: *)
method wpsimp' uses wp wp_del simp simp_del split split_del cong =
  ((determ \<open>wp add: wp del: wp_del |wpc|clarsimp simp add: simp simp del: simp_del split: split split del: split_del cong: cong\<close>)+)[1]

lemma unmap_page_corres:
  assumes "sz' = sz" "asid' = asid" "vptr' = vptr" "pptr' = pptr"
  shows "corres dc (invs and valid_etcbs and
                     K (valid_unmap sz (asid,vptr) \<and> vptr < pptr_base \<and> asid \<le> mask asid_bits
                          \<and> canonical_address vptr))
                   (valid_objs' and valid_arch_state' and pspace_aligned' and
                     pspace_distinct' and no_0_obj' and cur_tcb')
                   (unmap_page sz asid vptr pptr)
                   (unmapPage sz' asid' vptr' pptr')"
  apply (clarsimp simp: assms unmap_page_def unmapPage_def ignoreFailure_def const_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_catch[where E="\<top>\<top>" and E'="\<top>\<top>"], simp)
      apply (rule corres_split_strengthen_ftE[where ftr'=dc])
         apply (rule find_vspace_for_asid_corres[OF refl])
        apply (rule corres_splitEE)
           apply clarsimp
           apply (rule corres_machine_op, rule corres_Id, rule refl, simp)
           apply (rule no_fail_invalidateTranslationSingleASID)
          apply (rule_tac F = "vptr < pptr_base" in corres_gen_asm)
          apply (rule_tac P="\<exists>\<rhd> vspace and page_map_l4_at vspace and vspace_at_asid asid vspace
                             and (\<exists>\<rhd> vspace)
                             and valid_arch_state and valid_arch_objs
                             and equal_kernel_mappings
                             and pspace_aligned and valid_global_objs and valid_etcbs and
                             K (valid_unmap sz (asid,vptr) \<and> canonical_address vptr )" and
                          P'="pspace_aligned' and pspace_distinct'" in corres_inst)
          apply clarsimp
          apply (rename_tac vspace)
          apply (cases sz, simp_all)[1]
             apply (rule corres_guard_imp)
               apply (rule_tac F = "vptr < pptr_base" in corres_gen_asm)
               apply (rule corres_split_strengthen_ftE[OF lookup_pt_slot_corres])
                 apply simp
                 apply (rule corres_splitEE[OF _ liftE_get_pte_corres])
                   apply simp
                   apply (rule corres_split_norE[OF _ check_mapping_corres, where r=dc, simplified])
                   apply simp
                   apply (rule store_pte_corres')
                   apply (((wpsimp' wp: hoare_vcg_all_lift_R get_pte_wp getPTE_wp lookup_pt_slot_wp
                                  simp: page_entry_map_def unlessE_def is_aligned_pml4
                             split_del: if_split
                              simp_del: dc_simp)+
                           | wp_once hoare_drop_imps)+)[10]
         apply (rule corres_guard_imp)
           apply (rule corres_split_strengthen_ftE[OF lookup_pd_slot_corres])
             apply (simp del: dc_simp)
             apply (rule corres_splitEE[OF _ liftE_get_pde_corres])
               apply (rule corres_split_norE[OF _ check_mapping_corres, where r=dc, simplified])
                  apply simp
                  apply (rule store_pde_corres')
                  apply (((wpsimp' wp: hoare_vcg_all_lift_R get_pde_wp getPDE_wp lookup_pd_slot_wp
                                 simp: page_entry_map_def unlessE_def is_aligned_pml4
                            split_del: if_split
                             simp_del: dc_simp)+
                         | wp_once hoare_drop_imps)+)[10]
        apply (rule corres_guard_imp)
          apply (rule corres_split_strengthen_ftE[OF lookup_pdpt_slot_corres])
            apply (simp del: dc_simp)
            apply (rule corres_splitEE[OF _ liftE_get_pdpte_corres])
              apply (rule corres_split_norE[OF _ check_mapping_corres, where r=dc, simplified])
                 apply simp
                 apply (rule store_pdpte_corres')
                 apply (((wpsimp' wp: hoare_vcg_all_lift_R get_pdpte_wp getPDPTE_wp
                                      lookup_pdpt_slot_wp
                                simp: page_entry_map_def unlessE_def is_aligned_pml4
                           split_del: if_split
                            simp_del: dc_simp)+
                         | wp_once hoare_drop_imps)+)
   apply (rule conjI[OF disjI1], clarsimp)
   apply (clarsimp simp: invs_arch_objs invs_psp_aligned valid_unmap_def invs_arch_state
                         invs_equal_kernel_mappings)
  apply (clarsimp)
  done

definition
  "page_directory_invocation_map pdi pdi' \<equiv> case pdi of
   X64_A.PageDirectoryMap cap cte pdpte pdpt_slot pml4  \<Rightarrow>
      \<exists>cap' pdpte'. pdi' = PageDirectoryMap cap' (cte_map cte) pdpte' pdpt_slot pml4
            \<and> cap_relation cap cap' \<and> pdpte_relation' pdpte pdpte'
 | X64_A.PageDirectoryUnmap cap ptr \<Rightarrow>
      \<exists>cap'. pdi' = PageDirectoryUnmap cap' (cte_map ptr) \<and> cap_relation cap (ArchObjectCap cap')"

definition
  "page_invocation_map pgi pgi' \<equiv> case pgi of
    X64_A.PageMap c slot m vs \<Rightarrow>
      \<exists>c' m'. pgi' = PageMap c' (cte_map slot) m' vs \<and>
              cap_relation c c' \<and>
              mapping_map m m'
  | X64_A.PageRemap m a vs \<Rightarrow>
      \<exists>m'. pgi' = PageRemap m' a vs \<and> mapping_map m m'
  | X64_A.PageUnmap c ptr \<Rightarrow>
      \<exists>c'. pgi' = PageUnmap c' (cte_map ptr) \<and>
         acap_relation c c'
  | X64_A.PageGetAddr ptr \<Rightarrow>
      pgi' = PageGetAddr ptr"

lemma tl_nat_list_simp:
 "tl [a..<b] = [a + 1 ..<b]"
  by (induct b,auto)

definition
  "valid_page_inv' pgi \<equiv> case pgi of
    PageMap cap ptr m vs \<Rightarrow>
      cte_wp_at' (is_arch_update' cap) ptr and valid_slots' m and valid_cap' cap
      and K (page_entry_map_corres m)
  | PageRemap m asid vs \<Rightarrow> valid_slots' m and K (page_entry_map_corres m)
  | PageUnmap cap ptr \<Rightarrow>
      \<lambda>s. \<exists>r mt R sz d m. cap = PageCap r R mt sz d m \<and>
          cte_wp_at' (is_arch_update' (ArchObjectCap cap)) ptr s \<and>
          s \<turnstile>' (ArchObjectCap cap)
  | PageGetAddr ptr \<Rightarrow> \<top>"

crunch ctes [wp]: unmapPage "\<lambda>s. P (ctes_of s)"
  (wp: crunch_wps simp: crunch_simps ignore: getObject)

lemma updateCap_valid_slots'[wp]:
  "\<lbrace>valid_slots' x2\<rbrace> updateCap cte cte' \<lbrace>\<lambda>_ s. valid_slots' x2 s \<rbrace>"
  apply (case_tac x2, case_tac a)
    by (wpsimp simp: valid_slots'_def wp: hoare_vcg_ball_lift)+


crunch unique_table_refs[wp]: do_machine_op, store_pte, store_pde, store_pdpte "\<lambda>s. (unique_table_refs (caps_of_state s))"

lemma set_cap_vspace_at_asid [wp]:
  "\<lbrace>vspace_at_asid asid pd\<rbrace> set_cap t st \<lbrace>\<lambda>rv. vspace_at_asid asid pd\<rbrace>"
  apply (simp add: vspace_at_asid_def)
  apply wp
  done

lemma set_cap_valid_slots_inv[wp]:
  "\<lbrace>valid_slots m\<rbrace> set_cap t st \<lbrace>\<lambda>rv. valid_slots m\<rbrace>"
  apply (cases m; simp)
  apply (case_tac a; simp)
    by  (clarsimp simp: valid_slots_def, wp hoare_vcg_ball_lift set_cap.vs_lookup set_cap_typ_ats)+

lemma set_cap_same_refs_inv[wp]:
  "\<lbrace>\<lambda>s. same_refs m cap s\<rbrace> set_cap t st \<lbrace>\<lambda>rv s. same_refs m cap s\<rbrace>"
  by (cases m, (clarsimp simp: same_refs_def, wp)+)

definition
  "valid_page_map_inv cap ptr m vs \<equiv> (\<lambda>s. caps_of_state s ptr = Some cap) and same_refs m cap and
  valid_slots m and
  valid_cap cap and
  K (is_pg_cap cap \<and> empty_refs m) and
  (\<lambda>s. \<exists>sl. cte_wp_at (parent_for_refs m) sl s)"

lemma set_cap_valid_page_map_inv:
  "\<lbrace>valid_page_inv (X64_A.page_invocation.PageMap cap slot m vs)\<rbrace> set_cap cap slot \<lbrace>\<lambda>rv. valid_page_map_inv cap slot m vs\<rbrace>"
  apply (simp add: valid_page_inv_def valid_page_map_inv_def)
  apply (wp set_cap_cte_wp_at_cases hoare_vcg_ex_lift| simp)+
  apply clarsimp
  apply (rule conjI, fastforce simp: cte_wp_at_def)
  apply (rule_tac x=a in exI, rule_tac x=b in exI)
  apply (subgoal_tac "(a,b) \<noteq> slot")
   apply clarsimp
  apply (clarsimp simp: cte_wp_at_def parent_for_refs_def)
  apply (auto simp: is_pt_cap_def is_pg_cap_def is_pd_cap_def is_pdpt_cap_def split: vm_page_entry.splits)
  done

lemma message_info_to_data_eqv:
  "wordFromMessageInfo (message_info_map mi) = message_info_to_data mi"
  apply (cases mi)
  apply (simp add: wordFromMessageInfo_def
    msgLengthBits_def msgExtraCapBits_def msgMaxExtraCaps_def
    shiftL_nat)
  done

lemma message_info_from_data_eqv:
  "message_info_map (data_to_message_info rv) = messageInfoFromWord rv"
  apply (auto simp add: data_to_message_info_def messageInfoFromWord_def
    msgLengthBits_def msgExtraCapBits_def msgMaxExtraCaps_def
    shiftL_nat Let_def not_less msgMaxLength_def)
  done

lemma set_mi_corres:
 "mi' = message_info_map mi \<Longrightarrow>
  corres dc (tcb_at t) (tcb_at' t)
         (set_message_info t mi) (setMessageInfo t mi')"
  apply (simp add: setMessageInfo_def set_message_info_def)
  apply (subgoal_tac "wordFromMessageInfo (message_info_map mi) =
                      message_info_to_data mi")
   apply (simp add: user_setreg_corres msg_info_register_def
                    msgInfoRegister_def)
  apply (simp add: message_info_to_data_eqv)
  done


lemma set_mi_invs'[wp]: "\<lbrace>invs' and tcb_at' t\<rbrace> setMessageInfo t a \<lbrace>\<lambda>x. invs'\<rbrace>"
  by (simp add: setMessageInfo_def) wp

lemma set_mi_tcb' [wp]:
  "\<lbrace> tcb_at' t \<rbrace> setMessageInfo receiver msg \<lbrace>\<lambda>rv. tcb_at' t\<rbrace>"
  by (simp add: setMessageInfo_def) wp


lemma setMRs_typ_at':
  "\<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> setMRs receiver recv_buf mrs \<lbrace>\<lambda>rv s. P (typ_at' T p s)\<rbrace>"
  by (simp add: setMRs_def zipWithM_x_mapM split_def, wp crunch_wps)

lemmas setMRs_typ_at_lifts[wp] = typ_at_lifts [OF setMRs_typ_at']

lemma set_mrs_invs'[wp]:
  "\<lbrace> invs' and tcb_at' receiver \<rbrace> setMRs receiver recv_buf mrs \<lbrace>\<lambda>rv. invs' \<rbrace>"
  apply (simp add: setMRs_def)
  apply (wp dmo_invs' no_irq_mapM no_irq_storeWord crunch_wps|
         simp add: zipWithM_x_mapM split_def)+
  done

lemma perform_page_corres:
  assumes "page_invocation_map pgi pgi'"
  notes mapping_map_simps = mapping_map_def page_entry_map_def attr_mask_def attr_mask'_def page_entry_ptr_map_def
  shows "corres dc (invs and valid_etcbs and valid_page_inv pgi)
            (invs' and valid_page_inv' pgi')
            (perform_page_invocation pgi) (performPageInvocation pgi')"
proof -
  have pull_out_P:
    "\<And>P s Q c p. P s \<and> (\<forall>c. caps_of_state s p = Some c \<longrightarrow> Q s c) \<longrightarrow> (\<forall>c. caps_of_state s p = Some c \<longrightarrow> P s \<and> Q s c)"
   by blast
  show ?thesis
  using assms
  apply (cases pgi)
       apply (rename_tac cap prod entry vspace)
       apply (clarsimp simp: perform_page_invocation_def performPageInvocation_def
                             page_invocation_map_def)
       apply (rule corres_guard_imp)
         apply (rule_tac R="\<lambda>_. invs and (valid_page_map_inv cap (a,b) (aa,ba) vspace) and valid_etcbs and (\<lambda>s. caps_of_state s (a,b) = Some cap)"
           and R'="\<lambda>_. invs' and valid_slots' (ab,bb) and pspace_aligned'
           and pspace_distinct' and K (page_entry_map_corres (ab,bb))" in corres_split)
            prefer 2
            apply (erule updateCap_same_master)
           apply (simp, rule corres_gen_asm2)
           apply (case_tac aa)
             apply clarsimp
             apply (frule (1) mapping_map_pte, clarsimp)
             apply (clarsimp simp: mapping_map_simps valid_slots'_def valid_slots_def valid_page_inv_def neq_Nil_conv valid_page_map_inv_def)
            apply (rule corres_name_pre)
           apply (clarsimp simp:mapM_Cons bind_assoc split del: if_split)
           apply (rule corres_guard_imp)
             apply (rule corres_split[OF _ store_pte_corres'])
                apply (rule corres_split[where r'="op ="])
                   apply simp
                   apply (rule invalidate_local_page_structure_cache_asid_corres)
                  apply (case_tac cap; clarsimp simp add: is_pg_cap_def)
                  apply (case_tac m; clarsimp)
                  apply (rule corres_fail)
                  apply (simp add: same_refs_def)
                 apply (wpsimp simp: invs_psp_aligned)+
          apply (frule (1) mapping_map_pde, clarsimp)
          apply (clarsimp simp: mapping_map_simps valid_slots'_def valid_slots_def valid_page_inv_def neq_Nil_conv valid_page_map_inv_def)
          apply (rule corres_name_pre)
          apply (clarsimp simp:mapM_Cons bind_assoc split del: if_split)
          apply (rule corres_guard_imp)
            apply (rule corres_split[OF _ store_pde_corres'])
               apply (rule corres_split[where r'="op ="])
                  apply simp
                  apply (rule invalidate_local_page_structure_cache_asid_corres)
                 apply (case_tac cap; clarsimp simp add: is_pg_cap_def)
                 apply (case_tac m; clarsimp)
                 apply (rule corres_fail)
                 apply (simp add: same_refs_def)
                apply (wpsimp simp: invs_psp_aligned)+
         apply (frule (1) mapping_map_pdpte, clarsimp)
         apply (clarsimp simp: mapping_map_simps valid_slots'_def valid_slots_def valid_page_inv_def neq_Nil_conv valid_page_map_inv_def)
         apply (rule corres_name_pre)
         apply (clarsimp simp:mapM_Cons bind_assoc split del: if_split)
         apply (rule corres_guard_imp)
                apply (rule corres_split[OF _ store_pdpte_corres'])
              apply (rule corres_split[where r'="op ="])
                 apply simp
                 apply (rule invalidate_local_page_structure_cache_asid_corres)
                apply (case_tac cap; clarsimp simp add: is_pg_cap_def)
                apply (case_tac m; clarsimp)
                apply (rule corres_fail)
                apply (simp add: same_refs_def)
               apply (wpsimp simp: invs_psp_aligned)+
        apply (wp_trace arch_update_cap_invs_map set_cap_valid_page_map_inv)
       apply (wp arch_update_updateCap_invs)
      apply (clarsimp simp: invs_valid_objs invs_psp_aligned invs_distinct valid_page_inv_def cte_wp_at_caps_of_state is_arch_update_def is_cap_simps)
     apply (simp add: cap_master_cap_def split: cap.splits arch_cap.splits)
     apply (auto simp: cte_wp_at_ctes_of valid_page_inv'_def)[1]
       -- "PageRemap"
      apply (rename_tac asid vspace)
      apply (clarsimp simp: perform_page_invocation_def performPageInvocation_def
      page_invocation_map_def)
    apply (rule corres_name_pre)
    apply (clarsimp simp: mapM_Cons mapM_x_mapM bind_assoc valid_slots_def valid_page_inv_def
                          neq_Nil_conv valid_page_inv'_def split del: if_split)
    apply (case_tac a; simp)
      apply (frule (1) mapping_map_pte, clarsimp)
      apply (clarsimp simp: mapping_map_simps)
      apply (rule corres_guard_imp)
        apply (rule corres_split[OF _ store_pte_corres'])
           apply (rule invalidate_local_page_structure_cache_asid_corres)
          apply (wpsimp simp: invs_pspace_aligned')+
     apply (frule (1) mapping_map_pde, clarsimp)
     apply (clarsimp simp: mapping_map_simps)
     apply (rule corres_guard_imp)
       apply (rule corres_split[OF _ store_pde_corres'])
          apply (rule invalidate_local_page_structure_cache_asid_corres)
         apply (wpsimp simp: invs_pspace_aligned')+
    apply (frule (1) mapping_map_pdpte, clarsimp)
    apply (clarsimp simp: mapping_map_simps)
    apply (rule corres_guard_imp)
      apply (rule corres_split[OF _ store_pdpte_corres'])
         apply (rule invalidate_local_page_structure_cache_asid_corres)
        apply (wpsimp simp: invs_pspace_aligned')+
     -- "PageUnmap"
   apply (clarsimp simp: performPageInvocation_def perform_page_invocation_def
                         page_invocation_map_def)
   apply (rule corres_assume_pre)
   apply (clarsimp simp: valid_page_inv_def valid_page_inv'_def isCap_simps is_page_cap_def cong: option.case_cong prod.case_cong)
   apply (case_tac m)
    apply simp
    apply (rule corres_guard_imp)
      apply (rule corres_split [where r'="acap_relation"])
         prefer 2
         apply simp
         apply (rule corres_rel_imp)
          apply (rule get_cap_corres_all_rights_P[where P=is_arch_cap], rule refl)
         apply (clarsimp simp: is_cap_simps)
        apply (rule_tac F="is_page_cap cap" in corres_gen_asm)
        apply (rule updateCap_same_master)
        apply (clarsimp simp: is_page_cap_def update_map_data_def)
       apply (wp get_cap_wp getSlotCap_wp)+
     apply (clarsimp simp: cte_wp_at_caps_of_state is_arch_diminished_def)
     apply (drule (2) diminished_is_update')+
     apply (clarsimp simp: cap_rights_update_def acap_rights_update_def update_map_data_def is_cap_simps)
     apply auto[1]
    apply (auto simp: cte_wp_at_ctes_of)[1]
   apply clarsimp
   apply (rule corres_guard_imp)
     apply (rule corres_split)
        prefer 2
        apply (rule unmap_page_corres[OF refl refl refl refl])
       apply (rule corres_split [where r'=acap_relation])
          prefer 2
          apply simp
          apply (rule corres_rel_imp)
           apply (rule get_cap_corres_all_rights_P[where P=is_arch_cap], rule refl)
          apply (clarsimp simp: is_cap_simps)
         apply (rule_tac F="is_page_cap cap" in corres_gen_asm)
         apply (rule updateCap_same_master)
         apply (clarsimp simp: is_page_cap_def update_map_data_def)
        apply (wp get_cap_wp getSlotCap_wp)+
      apply (simp add: cte_wp_at_caps_of_state)
      apply (strengthen pull_out_P)+
      apply wp
     apply (simp add: cte_wp_at_ctes_of)
     apply wp
    apply (clarsimp simp: valid_unmap_def cte_wp_at_caps_of_state)
    apply (clarsimp simp: is_arch_diminished_def is_cap_simps split: cap.splits arch_cap.splits)
    apply (drule (2) diminished_is_update')+
    apply (clarsimp simp: cap_rights_update_def is_page_cap_def cap_master_cap_simps update_map_data_def acap_rights_update_def)
    apply (clarsimp simp add: valid_cap_def mask_def)
    apply auto[1]
   apply (auto simp: cte_wp_at_ctes_of)[1]
    -- "PageGetAddr"
  apply (clarsimp simp: perform_page_invocation_def performPageInvocation_def page_invocation_map_def fromPAddr_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF _ gct_corres])
      apply simp
      apply (rule corres_split[OF set_mi_corres set_mrs_corres])
         apply (simp add: message_info_map_def)
        apply clarsimp
       apply (wp)+
   apply (clarsimp simp: tcb_at_invs)
  apply (clarsimp simp: tcb_at_invs')
  done
qed

definition
  "page_table_invocation_map pti pti' \<equiv> case pti of
     X64_A.PageTableMap cap ptr pde pd_slot vspace \<Rightarrow>
    \<exists>cap' pde'. pti' = PageTableMap cap' (cte_map ptr) pde' pd_slot vspace \<and>
                cap_relation cap cap' \<and>
                pde_relation' pde pde'
   | X64_A.PageTableUnmap cap ptr \<Rightarrow>
    \<exists>cap'. pti' = PageTableUnmap cap' (cte_map ptr) \<and>
           cap_relation cap (ArchObjectCap cap')"

definition
  "valid_pti' pti \<equiv> case pti of
     PageTableMap cap slot pde pdeSlot vspace \<Rightarrow>
     cte_wp_at' (is_arch_update' cap) slot and
     valid_cap' cap and
     valid_pde' pde and K (case cap of ArchObjectCap (PageTableCap _ (Some (asid, vs))) \<Rightarrow> True | _ \<Rightarrow> False)
   | PageTableUnmap cap slot \<Rightarrow> cte_wp_at' (is_arch_update' (ArchObjectCap cap)) slot
                                 and valid_cap' (ArchObjectCap cap)
                                 and K (isPageTableCap cap)"

lemma clear_page_table_corres:
  "corres dc (pspace_aligned and page_table_at p and valid_etcbs)
             (pspace_aligned' and pspace_distinct')
    (mapM_x (swp store_pte X64_A.InvalidPTE)
       [p , p + 8 .e. p + 2 ^ ptBits - 1])
    (mapM_x (swp storePTE X64_H.InvalidPTE)
       [p , p + 8 .e. p + 2 ^ ptBits - 1])"
  apply (rule_tac F="is_aligned p ptBits" in corres_req)
   apply (clarsimp simp: obj_at_def a_type_def)
   apply (clarsimp split: Structures_A.kernel_object.split_asm if_split_asm
                          arch_kernel_obj.split_asm)
   apply (drule(1) pspace_alignedD)
   apply (simp add: bit_simps)
  apply (simp add: upto_enum_step_subtract[where x=p and y="p + 8"]
                   is_aligned_no_overflow bit_simps
                   upto_enum_step_red[where us=3, simplified]
                   mapM_x_mapM liftM_def[symmetric])
  apply (rule corres_guard_imp,
         rule_tac r'=dc and S="op ="
               and Q="\<lambda>xs s. \<forall>x \<in> set xs. pte_at x s \<and> pspace_aligned s \<and> valid_etcbs s"
               and Q'="\<lambda>xs. pspace_aligned' and pspace_distinct'"
                in corres_mapM_list_all2, simp_all)
      apply (rule corres_guard_imp, rule store_pte_corres')
        apply (simp add:pte_relation_def)+
     apply (wp hoare_vcg_const_Ball_lift | simp)+
   apply (simp add: list_all2_refl)
  apply (clarsimp simp: upto_enum_step_def)
  apply (erule page_table_pte_atI[simplified shiftl_t2n mult.commute bit_simps, simplified])
   apply (simp add: bit_simps word_less_nat_alt word_le_nat_alt unat_of_nat)
  apply simp
  done

lemma clear_page_directory_corres:
  "corres dc (pspace_aligned and page_directory_at p and valid_etcbs)
             (pspace_aligned' and pspace_distinct')
    (mapM_x (swp store_pde X64_A.InvalidPDE)
       [p , p + 8 .e. p + 2 ^ pdBits - 1])
    (mapM_x (swp storePDE X64_H.InvalidPDE)
       [p , p + 8 .e. p + 2 ^ pdBits - 1])"
  apply (rule_tac F="is_aligned p pdBits" in corres_req)
   apply (clarsimp simp: obj_at_def a_type_def)
   apply (clarsimp split: Structures_A.kernel_object.split_asm if_split_asm
                          arch_kernel_obj.split_asm)
   apply (drule(1) pspace_alignedD)
   apply (simp add: bit_simps)
  apply (simp add: upto_enum_step_subtract[where x=p and y="p + 8"]
                   is_aligned_no_overflow bit_simps
                   upto_enum_step_red[where us=3, simplified]
                   mapM_x_mapM liftM_def[symmetric])
  apply (rule corres_guard_imp,
         rule_tac r'=dc and S="op ="
               and Q="\<lambda>xs s. \<forall>x \<in> set xs. pde_at x s \<and> pspace_aligned s \<and> valid_etcbs s"
               and Q'="\<lambda>xs. pspace_aligned' and pspace_distinct'"
                in corres_mapM_list_all2, simp_all)
      apply (rule corres_guard_imp, rule store_pde_corres')
        apply (simp add:pde_relation_def)+
     apply (wp hoare_vcg_const_Ball_lift | simp)+
   apply (simp add: list_all2_refl)
  apply (clarsimp simp: upto_enum_step_def)
  apply (erule page_directory_pde_atI[simplified shiftl_t2n mult.commute bit_simps, simplified])
   apply (simp add: bit_simps word_less_nat_alt word_le_nat_alt unat_of_nat)
  apply simp
  done

lemma clear_pdpt_corres:
  "corres dc (pspace_aligned and pd_pointer_table_at p and valid_etcbs)
             (pspace_aligned' and pspace_distinct')
    (mapM_x (swp store_pdpte X64_A.InvalidPDPTE)
       [p , p + 8 .e. p + 2 ^ pdBits - 1])
    (mapM_x (swp storePDPTE X64_H.InvalidPDPTE)
       [p , p + 8 .e. p + 2 ^ pdBits - 1])"
  apply (rule_tac F="is_aligned p pdptBits" in corres_req)
   apply (clarsimp simp: obj_at_def a_type_def)
   apply (clarsimp split: Structures_A.kernel_object.split_asm if_split_asm
                          arch_kernel_obj.split_asm)
   apply (drule(1) pspace_alignedD)
   apply (simp add: bit_simps)
  apply (simp add: upto_enum_step_subtract[where x=p and y="p + 8"]
                   is_aligned_no_overflow bit_simps
                   upto_enum_step_red[where us=3, simplified]
                   mapM_x_mapM liftM_def[symmetric])
  apply (rule corres_guard_imp,
         rule_tac r'=dc and S="op ="
               and Q="\<lambda>xs s. \<forall>x \<in> set xs. pdpte_at x s \<and> pspace_aligned s \<and> valid_etcbs s"
               and Q'="\<lambda>xs. pspace_aligned' and pspace_distinct'"
                in corres_mapM_list_all2, simp_all)
      apply (rule corres_guard_imp, rule store_pdpte_corres')
        apply (simp add:pde_relation_def)+
     apply (wp hoare_vcg_const_Ball_lift | simp)+
   apply (simp add: list_all2_refl)
  apply (clarsimp simp: upto_enum_step_def)
  apply (erule pd_pointer_table_pdpte_atI[simplified shiftl_t2n mult.commute bit_simps, simplified])
   apply (simp add: bit_simps word_less_nat_alt word_le_nat_alt unat_of_nat)
  apply simp
  done

crunch typ_at'[wp]: invalidatePageStructureCacheASID, unmapPageTable, unmapPageDirectory, unmapPDPT "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps hoare_vcg_all_lift_R ignore: getObject)

lemmas unmapPageTable_typ_ats[wp] = typ_at_lifts[OF unmapPageTable_typ_at']
lemmas unmapPageDirectory_typ_ats[wp] = typ_at_lifts[OF unmapPageDirectory_typ_at']
lemmas unmapPDPT_typ_ats[wp] = typ_at_lifts[OF unmapPDPT_typ_at']

lemma perform_page_table_corres:
  "page_table_invocation_map pti pti' \<Longrightarrow>
   corres dc
          (invs and valid_etcbs and valid_pti pti)
          (invs' and valid_pti' pti')
          (perform_page_table_invocation pti)
          (performPageTableInvocation pti')"
  (is "?mp \<Longrightarrow> corres dc ?P ?P' ?f ?g")
  apply (simp add: perform_page_table_invocation_def performPageTableInvocation_def)
  apply (cases pti)
   apply (rename_tac cap slot pde pd_slot vspace)
   apply (clarsimp simp: page_table_invocation_map_def)
   apply (rule corres_name_pre)
   apply (clarsimp simp: valid_pti_def valid_pti'_def split: capability.split_asm arch_capability.split_asm)
   apply (rule corres_guard_imp)
     apply (rule corres_split [OF _ updateCap_same_master])
        prefer 2
        apply assumption
       apply (rule corres_split [OF _ store_pde_corres'])
          apply (rule corres_split[where r'="op =" and P="\<top>" and P'="\<top>"])
             apply simp
             apply (rule invalidatePageStructureCacheASID_corres)
            apply (case_tac cap; clarsimp simp add: is_pt_cap_def)
            apply (case_tac asid; clarsimp)
           apply (wpsimp wp: set_cap_typ_at)+
    apply (clarsimp simp: invs_valid_objs invs_psp_aligned invs_distinct is_arch_update_def
                          cte_wp_at_caps_of_state )
    apply (clarsimp simp: is_cap_simps cap_master_cap_simps
                   dest!: cap_master_cap_eqDs)
   apply (clarsimp simp: cte_wp_at_ctes_of valid_pti'_def)
   apply auto[1]
  apply (clarsimp simp: split:X64_H.pde.split)
  apply (rename_tac cap a b)
  apply (clarsimp simp: page_table_invocation_map_def)
  apply (rule_tac F="is_pt_cap cap" in corres_req)
   apply (clarsimp simp: valid_pti_def)
  apply (clarsimp simp: is_pt_cap_def split_def
                        bit_simps objBits_simps archObjSize_def
                  cong: option.case_cong)
  apply (simp add: case_option_If2 getSlotCap_def split del: if_split)
  apply (rule corres_guard_imp)
    apply (rule corres_split_nor)
       apply (simp add: liftM_def)
       apply (rule corres_split [OF _ get_cap_corres])
         apply (rule_tac F="is_pt_cap x" in corres_gen_asm)
         apply (rule updateCap_same_master)
         apply (clarsimp simp: is_pt_cap_def update_map_data_def)
        apply (wp get_cap_wp)+
      apply (rule corres_if[OF refl])
       apply (rule corres_split [OF _ unmap_page_table_corres[OF refl refl refl]])
         apply (rule clear_page_table_corres[simplified bit_simps bitSimps, simplified])
        apply wp+
      apply (rule corres_trivial, simp)
     apply (simp add: cte_wp_at_caps_of_state pred_conj_def
           split del: if_split)
     apply (rule hoare_lift_Pf2[where f=caps_of_state])
      apply ((wp hoare_vcg_all_lift hoare_vcg_const_imp_lift
                mapM_x_wp' | simp split del: if_split)+)
   apply (clarsimp simp: valid_pti_def cte_wp_at_caps_of_state
                         is_arch_diminished_def
                         cap_master_cap_simps
                         update_map_data_def is_cap_simps
                         cap_rights_update_def acap_rights_update_def
                  dest!: cap_master_cap_eqDs)
   apply (frule (2) diminished_is_update')
   apply (auto simp: valid_cap_def mask_def cap_master_cap_def
                     cap_rights_update_def acap_rights_update_def
              split: option.split_asm)[1]
   apply (auto simp: valid_pti'_def cte_wp_at_ctes_of bit_simps)
  done

definition
  "valid_pdi' pdi \<equiv> case pdi of
     PageDirectoryMap cap slot pdpte pdptSlot vspace \<Rightarrow>
     cte_wp_at' (is_arch_update' cap) slot and
     valid_cap' cap and
     valid_pdpte' pdpte and K (case cap of ArchObjectCap (PageDirectoryCap _ (Some (asid, vs))) \<Rightarrow> True | _ \<Rightarrow> False)
   | PageDirectoryUnmap cap slot \<Rightarrow> cte_wp_at' (is_arch_update' (ArchObjectCap cap)) slot
                                 and valid_cap' (ArchObjectCap cap)
                                 and K (isPageDirectoryCap cap)"

lemma flush_all_corres [corres]:
  assumes "vspace' = vspace" "asid' = asid"
  shows "corres dc \<top> \<top> (flush_all vspace asid) (flushAll vspace' asid')"
  apply (simp add: assms flush_all_def flushAll_def)
  apply (rule corres_rel_imp[OF _ dc_simp])
  apply (rule corres_machine_op)
  apply (rule corres_underlying_trivial[OF no_fail_invalidateASID])
  done

lemma unmap_pd_corres:
  assumes "asid' = asid" "vptr' = vptr" "pd' = pd"
  notes liftE_get_pdpte_corres = get_pdpte_corres'[THEN corres_liftE_rel_sum[THEN iffD2]]
  shows "corres dc
          (invs and valid_etcbs and page_directory_at pd and
           K (0 < asid \<and> is_aligned vptr pdpt_shift_bits \<and> vptr < pptr_base \<and> canonical_address vptr \<and> asid \<le> mask asid_bits))
          (valid_arch_state' and pspace_aligned' and pspace_distinct'
            and no_0_obj' and cur_tcb' and valid_objs')
          (unmap_pd asid vptr pd)
          (unmapPageDirectory asid' vptr' pd')"
  apply (clarsimp simp: assms unmap_pd_def unmapPageDirectory_def flushPD_def
                        invalidatePageStructureCacheASID_def
                        ignoreFailure_def const_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_catch[where E="\<top>\<top>" and E'="\<top>\<top>"], simp)
      apply (rule corres_split_eqrE[OF _ find_vspace_for_asid_corres[OF refl]])
        apply (rule corres_split_eqrE[OF _ lookup_pdpt_slot_corres])
          apply (rule corres_splitEE[OF _ liftE_get_pdpte_corres])
            apply (rule corres_splitEE[where r'=dc])
               prefer 2
               apply (case_tac "\<exists>addr x xa. pdpte = X64_A.PageDirectoryPDPTE addr x xa";
                      fastforce intro!: corres_returnOkTT
                                simp: lookup_failure_map_def pdpte_relation_def
                                split: X64_A.pdpte.splits)
              apply simp
              apply (rule corres_split_nor[OF _ flush_all_corres[OF _ refl]])
                 prefer 2
                 (* FIXME x64: change Haskell spec so that invalidateASID takes a word,
                               and unmapPageDirectory uses fromPPtr instead of addrFromPPtr *)
                 subgoal sorry
                apply (rule corres_split[OF invalidate_local_page_structure_cache_asid_corres
                                            store_pdpte_corres'])
                  apply ((wpsimp wp: get_pdpte_wp simp: pdpte_at_def)+)[8]
          apply (wpsimp wp: hoare_drop_imps)
         apply ((wp lookup_pdpt_slot_wp find_vspace_for_asid_wp)+)[6]
   apply (clarsimp simp: invs_def valid_state_def valid_pspace_def valid_arch_caps_def
                         word_neq_0_conv[symmetric])
   apply (frule (3) find_vspace_for_asid_eq_helper;
          fastforce simp: vspace_at_asid_def pdpte_at_def)
  apply simp
  done

crunch valid_objs[wp]: unmap_pd, unmap_pdpt "valid_objs"
crunch pspace_aligned[wp]: unmap_pd, unmap_pdpt "pspace_aligned"
crunch pspace_distinct[wp]: unmap_pd, unmap_pdpt "pspace_distinct"

lemma perform_page_directory_corres:
  "page_directory_invocation_map pdi pdi' \<Longrightarrow>
   corres dc
          (invs and valid_etcbs and valid_pdi pdi)
          (invs' and valid_pdi' pdi')
          (perform_page_directory_invocation pdi)
          (performPageDirectoryInvocation pdi')"
  (is "?mp \<Longrightarrow> corres dc ?P ?P' ?f ?g")
  apply (simp add: perform_page_directory_invocation_def performPageDirectoryInvocation_def)
  apply (cases pdi)
   apply (rename_tac cap slot pdpte pdpt_slot vspace)
   apply (clarsimp simp: page_directory_invocation_map_def)
   apply (rule corres_name_pre)
   apply (clarsimp simp: valid_pdi_def valid_pdi'_def split: capability.split_asm arch_capability.split_asm)
   apply (rule corres_guard_imp)
     apply (rule corres_split [OF _ updateCap_same_master])
        prefer 2
        apply assumption
       apply (rule corres_split [OF _ store_pdpte_corres'])
          apply (rule corres_split[where r'="op =" and P="\<top>" and P'="\<top>"])
             apply simp
             apply (rule invalidatePageStructureCacheASID_corres)
            apply (case_tac cap; clarsimp simp add: is_pd_cap_def)
            apply (case_tac asid; clarsimp)
           apply (wpsimp wp: set_cap_typ_at)+
    apply (clarsimp simp: invs_valid_objs invs_psp_aligned invs_distinct is_arch_update_def
                          cte_wp_at_caps_of_state )
    apply (clarsimp simp: is_cap_simps cap_master_cap_simps
                   dest!: cap_master_cap_eqDs)
   apply (clarsimp simp: cte_wp_at_ctes_of valid_pdi'_def)
   apply auto[1]
  apply (clarsimp split:X64_H.pdpte.split)
  apply (rename_tac cap a b)
  apply (clarsimp simp: page_directory_invocation_map_def)
  apply (rule_tac F="is_pd_cap cap" in corres_req)
   apply (clarsimp simp: valid_pdi_def)
  apply (clarsimp simp: is_pd_cap_def split_def
                        bit_simps objBits_simps archObjSize_def
                  cong: option.case_cong)
  apply (simp add: case_option_If2 getSlotCap_def split del: if_split)
  apply (rule corres_guard_imp)
    apply (rule corres_split_nor)
       apply (simp add: liftM_def)
       apply (rule corres_split [OF _ get_cap_corres])
         apply (rule_tac F="is_pd_cap x" in corres_gen_asm)
         apply (rule updateCap_same_master)
         apply (clarsimp simp: is_pd_cap_def update_map_data_def)
        apply (wp get_cap_wp)+
      apply (rule corres_if[OF refl])
       apply (rule corres_split [OF _ unmap_pd_corres[OF refl refl refl]])
         apply (rule clear_page_directory_corres[simplified bit_simps bitSimps, simplified])
        apply wp+
      apply (rule corres_trivial, simp)
     apply (simp add: cte_wp_at_caps_of_state pred_conj_def
           split del: if_split)
     apply (rule hoare_lift_Pf2[where f=caps_of_state])
      apply ((wp hoare_vcg_all_lift hoare_vcg_const_imp_lift
                mapM_x_wp' | simp split del: if_split)+)
   apply (clarsimp simp: valid_pdi_def cte_wp_at_caps_of_state
                         is_arch_diminished_def
                         cap_master_cap_simps
                         update_map_data_def is_cap_simps
                         cap_rights_update_def acap_rights_update_def
                  dest!: cap_master_cap_eqDs)
   apply (frule (2) diminished_is_update')
   apply (auto simp: valid_cap_def mask_def cap_master_cap_def
                     cap_rights_update_def acap_rights_update_def
                     wellformed_mapdata_def vmsz_aligned_def
              split: option.split_asm)[1]
   apply (auto simp: valid_pdi'_def cte_wp_at_ctes_of bit_simps)
  done

definition
  "valid_pdpti' pdi \<equiv> case pdi of
     PDPTMap cap slot pml4e pml4Slot vspace \<Rightarrow>
     cte_wp_at' (is_arch_update' cap) slot and
     valid_cap' cap and
     valid_pml4e' pml4e and K (case cap of ArchObjectCap (PDPointerTableCap _ (Some (asid, vs))) \<Rightarrow> True | _ \<Rightarrow> False)
   | PDPTUnmap cap slot \<Rightarrow> cte_wp_at' (is_arch_update' (ArchObjectCap cap)) slot
                                 and valid_cap' (ArchObjectCap cap)
                                 and K (isPDPointerTableCap cap)"

lemma unmap_pdpt_corres:
  assumes "asid' = asid" "vptr' = vptr" "pd' = pd"
  notes liftE_get_pml4e_corres = get_pml4e_corres'[THEN corres_liftE_rel_sum[THEN iffD2]]
  shows "corres dc
          (invs and valid_etcbs and pd_pointer_table_at pd and
           K (0 < asid \<and> is_aligned vptr pml4_shift_bits \<and> vptr < pptr_base \<and> canonical_address vptr \<and> asid \<le> mask asid_bits))
          (valid_arch_state' and pspace_aligned' and pspace_distinct'
            and no_0_obj' and cur_tcb' and valid_objs')
          (unmap_pdpt asid vptr pd)
          (unmapPDPT asid vptr pd)"
  apply (clarsimp simp: assms unmap_pdpt_def unmapPDPT_def flushPDPT_def
                        invalidatePageStructureCacheASID_def
                        ignoreFailure_def const_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_catch[where E="\<top>\<top>" and E'="\<top>\<top>"], simp)
      apply (rule corres_split_eqrE[OF _ find_vspace_for_asid_corres[OF refl]])
        apply (rule corres_splitEE[OF _ liftE_get_pml4e_corres])
          apply (rule corres_splitEE[where r'=dc])
             prefer 2
             apply (case_tac "\<exists>addr a b. rv = X64_A.PDPointerTablePML4E addr a b";
                    fastforce intro!: corres_returnOkTT
                              simp: lookup_failure_map_def pml4e_relation_def
                              split: X64_A.pml4e.splits)
            apply simp
            apply (rule corres_split_nor[OF _ flush_all_corres[OF _ refl]])
               prefer 2
               (* FIXME x64: change Haskell spec so that invalidateASID takes a word,
                             and unmapPageDirectory uses fromPPtr instead of addrFromPPtr *)
               subgoal sorry
              apply (rule store_pml4e_corres'[OF refl], simp)
             apply ((wpsimp wp: get_pml4e_wp simp: pml4e_at_def)+)[5]
        apply (wpsimp wp: hoare_drop_imps)
       apply ((wp find_vspace_for_asid_wp)+)[4]
   apply (clarsimp simp: invs_def valid_state_def valid_pspace_def valid_arch_caps_def
                         word_neq_0_conv[symmetric])
   apply (frule (3) find_vspace_for_asid_eq_helper)
   apply (rule conjI[OF page_map_l4_pml4e_at_lookupI]; simp)
   apply (clarsimp simp: obj_at_def a_type_simps lookup_pml4_slot_def)
   apply (fastforce intro!: is_aligned_add is_aligned_shiftl_self
                    elim: is_aligned_weaken simp: bit_simps)
  apply simp
  done

definition
  "pdpt_invocation_map pdpti pdpti' \<equiv> case pdpti of
   X64_A.PDPTMap cap cte pml4e pml4_slot vspace  \<Rightarrow>
      \<exists>cap' pml4e'. pdpti' = PDPTMap cap' (cte_map cte) pml4e' pml4_slot vspace
            \<and> cap_relation cap cap' \<and> pml4e_relation' pml4e pml4e'
 | X64_A.PDPTUnmap cap ptr \<Rightarrow>
      \<exists>cap'. pdpti' = PDPTUnmap cap' (cte_map ptr) \<and> cap_relation cap (ArchObjectCap cap')"

lemma perform_pdpt_corres:
  "pdpt_invocation_map pdpti pdpti' \<Longrightarrow>
   corres dc
          (invs and valid_etcbs and valid_pdpti pdpti)
          (invs' and valid_pdpti' pdpti')
          (perform_pdpt_invocation pdpti)
          (performPDPTInvocation pdpti')"
  (is "?mp \<Longrightarrow> corres dc ?P ?P' ?f ?g")
  apply (simp add: perform_pdpt_invocation_def performPDPTInvocation_def)
  apply (cases pdpti)
   apply (rename_tac cap slot pml4e pml4_slot vspace)
   apply (clarsimp simp: pdpt_invocation_map_def)
   apply (rule corres_name_pre)
   apply (clarsimp simp: valid_pdpti_def valid_pdpti'_def split: capability.split_asm arch_capability.split_asm)
   apply (rule corres_guard_imp)
     apply (rule corres_split [OF _ updateCap_same_master])
        prefer 2
        apply assumption
       apply (rule corres_split [OF _ store_pml4e_corres'])
          apply (rule corres_split[where r'="op =" and P="\<top>" and P'="\<top>"])
             apply simp
             apply (rule invalidatePageStructureCacheASID_corres)
            apply (case_tac cap; clarsimp simp add: is_pdpt_cap_def)
            apply (case_tac asid; clarsimp)
           apply (wpsimp wp: set_cap_typ_at)+
    apply (clarsimp simp: invs_valid_objs invs_psp_aligned invs_distinct is_arch_update_def
                          cte_wp_at_caps_of_state )
    apply (clarsimp simp: is_cap_simps cap_master_cap_simps
                   dest!: cap_master_cap_eqDs)
   apply (clarsimp simp: cte_wp_at_ctes_of valid_pdpti'_def)
   apply auto[1]
  apply (clarsimp split:X64_H.pml4e.split)
  apply (rename_tac cap a b)
  apply (clarsimp simp: pdpt_invocation_map_def)
  apply (rule_tac F="is_pdpt_cap cap" in corres_req)
   apply (clarsimp simp: valid_pdpti_def)
  apply (clarsimp simp: is_pdpt_cap_def split_def
                        bit_simps objBits_simps archObjSize_def
                  cong: option.case_cong)
  apply (simp add: case_option_If2 getSlotCap_def split del: if_split)
  apply (rule corres_guard_imp)
    apply (rule corres_split_nor)
       apply (simp add: liftM_def)
       apply (rule corres_split [OF _ get_cap_corres])
         apply (rule_tac F="is_pdpt_cap x" in corres_gen_asm)
         apply (rule updateCap_same_master)
         apply (clarsimp simp: is_pdpt_cap_def update_map_data_def)
        apply (wp get_cap_wp)+
      apply (rule corres_if[OF refl])
       apply (rule corres_split [OF _ unmap_pdpt_corres[OF refl refl refl]])
         apply (rule clear_pdpt_corres[simplified bit_simps bitSimps, simplified])
        apply wp+
      apply (rule corres_trivial, simp)
     apply (simp add: cte_wp_at_caps_of_state pred_conj_def
           split del: if_split)
     apply (rule hoare_lift_Pf2[where f=caps_of_state])
      apply ((wp hoare_vcg_all_lift hoare_vcg_const_imp_lift
                mapM_x_wp' | simp split del: if_split)+)
   apply (clarsimp simp: valid_pdpti_def cte_wp_at_caps_of_state
                         is_arch_diminished_def
                         cap_master_cap_simps
                         update_map_data_def is_cap_simps
                         cap_rights_update_def acap_rights_update_def
                  dest!: cap_master_cap_eqDs)
   apply (frule (2) diminished_is_update')
   apply (auto simp: valid_cap_def mask_def cap_master_cap_def
                     cap_rights_update_def acap_rights_update_def
                     wellformed_mapdata_def vmsz_aligned_def
              split: option.split_asm)[1]
   apply (auto simp: valid_pdpti'_def cte_wp_at_ctes_of bit_simps)
  done

definition
  "asid_pool_invocation_map ap \<equiv> case ap of
  asid_pool_invocation.Assign asid p slot \<Rightarrow> Assign asid p (cte_map slot)"

definition
  "isPML4Cap' cap \<equiv> \<exists>p asid. cap = (ArchObjectCap (PML4Cap p asid))"

definition
  "valid_apinv' ap \<equiv> case ap of Assign asid p slot \<Rightarrow>
  asid_pool_at' p and cte_wp_at' (isPML4Cap' o cteCap) slot and K
  (0 < asid \<and> asid \<le> 2^asid_bits - 1)"

lemma pap_corres:
  assumes "ap' = asid_pool_invocation_map ap"
  shows "corres dc (valid_objs and pspace_aligned and pspace_distinct and valid_apinv ap and valid_etcbs)
                   (pspace_aligned' and pspace_distinct' and valid_apinv' ap')
                   (perform_asid_pool_invocation ap)
                   (performASIDPoolInvocation ap')"
  proof -
    { fix rv p asid asid'
      assume "rv = cap.ArchObjectCap (arch_cap.PML4Cap p asid)"
      hence "(case rv of cap.ArchObjectCap (arch_cap.PML4Cap p asid)
                 \<Rightarrow> cap.ArchObjectCap (arch_cap.PML4Cap p asid'))
               = cap.ArchObjectCap (arch_cap.PML4Cap p asid')"
      by simp
    } note helper = this
    show ?thesis
      using assms
      apply (clarsimp simp: perform_asid_pool_invocation_def performASIDPoolInvocation_def)
      apply (cases ap, simp add: asid_pool_invocation_map_def)
      apply (rename_tac word1 word2 prod)
      apply (rule corres_guard_imp)
        apply (rule corres_split[OF _ getSlotCap_corres[OF refl] get_cap_wp getSlotCap_wp])
        apply (rule_tac F="\<exists>p asid. rv = Structures_A.ArchObjectCap (X64_A.PML4Cap p asid)"
                 in corres_gen_asm; elim exE)
        apply (simp cong: corres_weak_cong)
        apply (rule subst[OF helper], assumption)
        apply (rule corres_split[OF _ updateCap_same_master])
           unfolding store_asid_pool_entry_def
           apply (rule corres_split[where r'="\<lambda>pool pool'. pool = pool' \<circ> ucast"])
              prefer 2
              apply (simp cong: corres_weak_cong)
              apply (rule corres_rel_imp)
               apply (rule get_asid_pool_corres'[OF refl])
              apply simp
             apply (simp only: return_bind cong: corres_weak_cong)
             apply (rule set_asid_pool_corres')
             apply (rule ext; clarsimp simp: inv_def mask_asid_low_bits_ucast_ucast)
            apply (wp getASID_wp)+
          apply simp
         apply (wp set_cap_typ_at)
        apply (wpsimp wp: hoare_drop_imps)
       by (auto simp: valid_apinv_def cte_wp_at_def is_pml4_cap_def
                      is_cap_simps cap_master_cap_def obj_at_def a_type_simps
                      valid_apinv'_def cte_wp_at'_def)
  qed

lemma setCurrentCR3_obj_at [wp]:
  "\<lbrace>\<lambda>s. P (obj_at' P' t s)\<rbrace> setCurrentCR3 c \<lbrace>\<lambda>rv s. P (obj_at' P' t s)\<rbrace>"
  apply (simp add: setCurrentCR3_def)
  apply (wp doMachineOp_obj_at|wpc|simp)+
  done

lemmas getCurrentCR3_obj_at [wp]
  = getCurrentCR3_inv[of "\<lambda>s. P (obj_at' P' t s)" for P P' t]

crunch obj_at[wp]: setVMRoot "\<lambda>s. P (obj_at' P' t s)"
  (simp: crunch_simps)

crunch it[wp]: doMachineOp "\<lambda>s. P (ksIdleThread s)"
crunch arch[wp]: doMachineOp "\<lambda>s. P (ksArchState s)"
crunch irq_node'[wp]: doMachineOp "\<lambda>s. P (irq_node' s)"
crunch gsMaxObjectSize[wp]: doMachineOp "\<lambda>s. P (gsMaxObjectSize s)"
crunch ksInterruptState[wp]: doMachineOp "\<lambda>s. P (ksInterruptState s)"

lemma dmo_writeCR3_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp (writeCR3 a b) \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (wp dmo_invs' no_irq_writeCR3 no_irq)
  apply clarsimp
  apply (drule_tac P4="\<lambda>m'. underlying_memory m' p = underlying_memory m p"
         in use_valid[where P=P and Q="\<lambda>_. P" for P])
    apply (simp add: writeCR3_def machine_op_lift_def
                     machine_rest_lift_def split_def | wp)+
  done

lemma dmo_writeCR3_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace> doMachineOp (writeCR3 a addr) \<lbrace>\<lambda>rv. invs_no_cicd'\<rbrace>"
  apply (wp dmo_invs_no_cicd' no_irq_writeCR3 no_irq)
  apply clarsimp
  apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
         in use_valid)
  apply (clarsimp simp: writeCR3_def machine_op_lift_def
                        machine_rest_lift_def split_def | wp)+
  done

lemma setCurrentCR3_invs' [wp]: "\<lbrace>invs'\<rbrace> setCurrentCR3 c \<lbrace>\<lambda>rv. invs'\<rbrace>"
  unfolding setCurrentCR3_def
  apply (wpsimp wp:)
  by (clarsimp simp: invs'_def valid_state'_def valid_global_refs'_def global_refs'_def
                   valid_arch_state'_def valid_machine_state'_def ct_not_inQ_def
                   ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def)

lemma getCurrentCR3_invs' [wp]: "\<lbrace>invs'\<rbrace> getCurrentCR3 \<lbrace>\<lambda>rv. invs'\<rbrace>"
  unfolding getCurrentCR3_def
  by (wpsimp)

lemma setCurrentCR3_invs_no_cicd' [wp]: "\<lbrace>invs_no_cicd'\<rbrace> setCurrentCR3 c \<lbrace>\<lambda>rv. invs_no_cicd'\<rbrace>"
  unfolding setCurrentCR3_def
  apply (wpsimp wp:)
  by (clarsimp simp: all_invs_but_ct_idle_or_in_cur_domain'_def valid_state'_def valid_global_refs'_def global_refs'_def
                   valid_arch_state'_def valid_machine_state'_def ct_not_inQ_def
                   ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def)

lemma getCurrentCR3_invs_no_cicd' [wp]: "\<lbrace>invs_no_cicd'\<rbrace> getCurrentCR3 \<lbrace>\<lambda>rv. invs_no_cicd'\<rbrace>"
  unfolding getCurrentCR3_def
  by (wpsimp)


lemma updateASIDMap_valid_arch'[wp]:
  shows "\<lbrace>valid_arch_state'\<rbrace> updateASIDMap asid  \<lbrace>\<lambda>rv. valid_arch_state'\<rbrace>"
  apply (simp add: updateASIDMap_def)
  apply wp
   prefer 2
   apply assumption
  apply (simp add: valid_arch_state'_def comp_upd_simp fun_upd_def[symmetric])
  apply wp
   apply (simp add: findVSpaceForASIDAssert_def const_def
                    checkPML4UniqueToASID_def checkPML4ASIDMapMembership_def)
   apply wp
   apply (rule_tac Q'="\<lambda>rv s. valid_asid_map' (x64KSASIDMap (ksArchState s))
                                \<and> asid \<noteq> 0 \<and> asid \<le> mask asid_bits"
              in hoare_post_imp_R)
    apply (wp findVSpaceForASID_inv2)+
   apply (clarsimp simp: valid_asid_map'_def)
   apply (subst conj_commute, rule context_conjI)
    apply clarsimp
    apply (rule ccontr, erule notE, rule_tac a=x in ranI)
    apply (simp add: restrict_map_def)
   apply (erule(1) inj_on_fun_updI2)
  apply clarsimp
  done

lemma updateASIDMap_invs'[wp]:
  notes fun_upd_apply[simp del]
  shows "\<lbrace>invs'\<rbrace> updateASIDMap a  \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (rule hoare_add_post)
    apply (rule updateASIDMap_valid_arch')
   apply fastforce
  apply (simp add: updateASIDMap_def)
  apply (wp findVSpaceForASIDAssert_vs_at_wp)
  apply (clarsimp simp add: invs'_def valid_state'_def valid_global_refs'_def global_refs'_def
      valid_arch_state'_def valid_machine_state'_def ct_not_inQ_def
      ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def)
  done

lemma updateASIDMap_invs_no_cicd'[wp]:
  notes fun_upd_apply[simp del]
  shows "\<lbrace>invs_no_cicd'\<rbrace> updateASIDMap a  \<lbrace>\<lambda>rv. invs_no_cicd'\<rbrace>"
  apply (rule hoare_add_post)
    apply (rule updateASIDMap_valid_arch')
   apply (fastforce simp: all_invs_but_ct_idle_or_in_cur_domain'_def)
  apply (simp add: updateASIDMap_def)
  apply (wp findVSpaceForASIDAssert_vs_at_wp)
  apply (clarsimp simp add: all_invs_but_ct_idle_or_in_cur_domain'_def valid_state'_def valid_global_refs'_def global_refs'_def
      valid_arch_state'_def valid_machine_state'_def ct_not_inQ_def
      ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def)
  done

lemma setVMRoot_invs [wp]:
  "\<lbrace>invs'\<rbrace> setVMRoot p \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: setVMRoot_def getThreadVSpaceRoot_def setCurrentVSpaceRoot_def )
  apply (rule hoare_pre)
   apply (wp hoare_whenE_wp | wpcw | clarsimp cong: if_cong)+
         apply (rule_tac Q'="\<lambda>rv. invs'" in hoare_post_imp_R)
          apply (wpsimp)+
  done

lemma setVMRoot_invs_no_cicd':
  "\<lbrace>invs_no_cicd'\<rbrace> setVMRoot p \<lbrace>\<lambda>rv. invs_no_cicd'\<rbrace>"
  apply (simp add: setVMRoot_def getThreadVSpaceRoot_def setCurrentVSpaceRoot_def)
  apply (rule hoare_pre)
   apply (wp hoare_whenE_wp | wpcw | clarsimp cong: if_cong)+
         apply (rule_tac Q'="\<lambda>rv. invs_no_cicd'" in hoare_post_imp_R)
          apply (wpsimp)+
  done

crunch nosch [wp]: setVMRoot "\<lambda>s. P (ksSchedulerAction s)"
  (wp: crunch_wps getObject_inv simp: crunch_simps
       loadObject_default_def ignore: getObject)

crunch it' [wp]: findVSpaceForASID "\<lambda>s. P (ksIdleThread s)"
  (simp: crunch_simps loadObject_default_def wp: getObject_inv ignore: getObject)

crunch it' [wp]: deleteASIDPool "\<lambda>s. P (ksIdleThread s)"
  (simp: crunch_simps loadObject_default_def wp: getObject_inv mapM_wp'
   ignore: getObject)

crunch it' [wp]: lookupPTSlot "\<lambda>s. P (ksIdleThread s)"
  (simp: crunch_simps loadObject_default_def wp: getObject_inv
   ignore: getObject)

crunch it' [wp]: storePTE "\<lambda>s. P (ksIdleThread s)"
  (simp: crunch_simps updateObject_default_def wp: setObject_idle'
   ignore: setObject)

crunch it' [wp]: storePDE "\<lambda>s. P (ksIdleThread s)"
  (simp: crunch_simps updateObject_default_def wp: setObject_idle'
   ignore: setObject)

crunch it' [wp]: storePDPTE "\<lambda>s. P (ksIdleThread s)"
  (simp: crunch_simps updateObject_default_def wp: setObject_idle'
   ignore: setObject)

crunch it' [wp]: storePML4E "\<lambda>s. P (ksIdleThread s)"
  (simp: crunch_simps updateObject_default_def wp: setObject_idle'
   ignore: setObject)

crunch it' [wp]: flushTable "\<lambda>s. P (ksIdleThread s)"
  (simp: crunch_simps loadObject_default_def
   wp: setObject_idle' hoare_drop_imps mapM_x_wp'
   ignore: getObject)

crunch it' [wp]: deleteASID "\<lambda>s. P (ksIdleThread s)"
  (simp: crunch_simps loadObject_default_def updateObject_default_def
   wp: getObject_inv
   ignore: getObject setObject)

crunch typ_at' [wp]: performPageTableInvocation "\<lambda>s. P (typ_at' T p s)"
  (ignore: getObject wp: crunch_wps)

crunch typ_at' [wp]: performPageDirectoryInvocation "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps)

crunch typ_at' [wp]: performPDPTInvocation "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps)

crunch typ_at' [wp]: performPageInvocation "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps ignore: getObject)

lemma performASIDPoolInvocation_typ_at' [wp]:
  "\<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> performASIDPoolInvocation api \<lbrace>\<lambda>_ s. P (typ_at' T p s)\<rbrace>"
  by (wpsimp simp: performASIDPoolInvocation_def
               wp: getASID_wp hoare_vcg_imp_lift[where P'=\<bottom>, simplified])

lemmas performPageTableInvocation_typ_ats' [wp] =
  typ_at_lifts [OF performPageTableInvocation_typ_at']

lemmas performPageDirectoryInvocation_typ_ats' [wp] =
  typ_at_lifts [OF performPageDirectoryInvocation_typ_at']

lemmas performPDPTInvocation_typ_ats' [wp] =
  typ_at_lifts [OF performPDPTInvocation_typ_at']

lemmas performPageInvocation_typ_ats' [wp] =
  typ_at_lifts [OF performPageInvocation_typ_at']

lemmas performASIDPoolInvocation_typ_ats' [wp] =
  typ_at_lifts [OF performASIDPoolInvocation_typ_at']

lemma storePDE_pred_tcb_at' [wp]:
  "\<lbrace>pred_tcb_at' proj P t\<rbrace> storePDE p pde \<lbrace>\<lambda>_. pred_tcb_at' proj P t\<rbrace>"
  apply (simp add: storePDE_def pred_tcb_at'_def)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp add: updateObject_default_def in_monad)
  done

lemma storePTE_pred_tcb_at' [wp]:
  "\<lbrace>pred_tcb_at' proj P t\<rbrace> storePTE p pte \<lbrace>\<lambda>_. pred_tcb_at' proj P t\<rbrace>"
  apply (simp add: storePTE_def pred_tcb_at'_def)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp add: updateObject_default_def in_monad)
  done

lemma storePDPTE_pred_tcb_at' [wp]:
  "\<lbrace>pred_tcb_at' proj P t\<rbrace> storePDPTE p pte \<lbrace>\<lambda>_. pred_tcb_at' proj P t\<rbrace>"
  apply (simp add: storePDPTE_def pred_tcb_at'_def)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp add: updateObject_default_def in_monad)
  done

lemma storePML4E_pred_tcb_at' [wp]:
  "\<lbrace>pred_tcb_at' proj P t\<rbrace> storePML4E p pte \<lbrace>\<lambda>_. pred_tcb_at' proj P t\<rbrace>"
  apply (simp add: storePML4E_def pred_tcb_at'_def)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp add: updateObject_default_def in_monad)
  done

lemma setASID_pred_tcb_at' [wp]:
  "\<lbrace>pred_tcb_at' proj P t\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. pred_tcb_at' proj P t\<rbrace>"
  apply (simp add: pred_tcb_at'_def)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp add: updateObject_default_def in_monad)
  done

lemma dmo_ct[wp]:
  "\<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace> doMachineOp m \<lbrace>\<lambda>rv s. P (ksCurThread s)\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply wp
  apply clarsimp
  done

lemma storePDE_valid_mdb [wp]:
  "\<lbrace>valid_mdb'\<rbrace> storePDE p pde \<lbrace>\<lambda>rv. valid_mdb'\<rbrace>"
  by (simp add: valid_mdb'_def) wp

lemma storePDPTE_valid_mdb [wp]:
  "\<lbrace>valid_mdb'\<rbrace> storePDPTE p pde \<lbrace>\<lambda>rv. valid_mdb'\<rbrace>"
  by (simp add: valid_mdb'_def) wp

lemma storePML4E_valid_mdb [wp]:
  "\<lbrace>valid_mdb'\<rbrace> storePML4E p pde \<lbrace>\<lambda>rv. valid_mdb'\<rbrace>"
  by (simp add: valid_mdb'_def) wp

crunch nosch [wp]: storePDE, storePDPTE, storePML4E "\<lambda>s. P (ksSchedulerAction s)"
  (simp: updateObject_default_def)

crunch ksQ [wp]: storePDE, storePDPTE, storePML4E "\<lambda>s. P (ksReadyQueues s)"
  (simp: updateObject_default_def ignore: setObject)

lemma storePDE_inQ[wp]:
  "\<lbrace>\<lambda>s. P (obj_at' (inQ d p) t s)\<rbrace> storePDE ptr pde \<lbrace>\<lambda>rv s. P (obj_at' (inQ d p) t s)\<rbrace>"
  apply (simp add: obj_at'_real_def storePDE_def)
  apply (wp setObject_ko_wp_at | simp add: objBits_simps archObjSize_def)+
  apply (clarsimp simp: projectKOs obj_at'_def ko_wp_at'_def)
  done

lemma storePDPTE_inQ[wp]:
  "\<lbrace>\<lambda>s. P (obj_at' (inQ d p) t s)\<rbrace> storePDPTE ptr pde \<lbrace>\<lambda>rv s. P (obj_at' (inQ d p) t s)\<rbrace>"
  apply (simp add: obj_at'_real_def storePDPTE_def)
  apply (wp setObject_ko_wp_at | simp add: objBits_simps archObjSize_def)+
  apply (clarsimp simp: projectKOs obj_at'_def ko_wp_at'_def)
  done

lemma storePML4E_inQ[wp]:
  "\<lbrace>\<lambda>s. P (obj_at' (inQ d p) t s)\<rbrace> storePML4E ptr pde \<lbrace>\<lambda>rv s. P (obj_at' (inQ d p) t s)\<rbrace>"
  apply (simp add: obj_at'_real_def storePML4E_def)
  apply (wp setObject_ko_wp_at | simp add: objBits_simps archObjSize_def)+
  apply (clarsimp simp: projectKOs obj_at'_def ko_wp_at'_def)
  done

crunch norqL1[wp]: storePDE, storePDPTE, storePML4E "\<lambda>s. P (ksReadyQueuesL1Bitmap s)"
  (simp: updateObject_default_def ignore: setObject)

crunch norqL2[wp]: storePDE, storePDPTE, storePML4E "\<lambda>s. P (ksReadyQueuesL2Bitmap s)"
  (simp: updateObject_default_def ignore: setObject)

lemma storePDE_valid_queues [wp]:
  "\<lbrace>Invariants_H.valid_queues\<rbrace> storePDE p pde \<lbrace>\<lambda>_. Invariants_H.valid_queues\<rbrace>"
  by (wp valid_queues_lift | simp add: pred_tcb_at'_def)+

lemma storePDPTE_valid_queues [wp]:
  "\<lbrace>Invariants_H.valid_queues\<rbrace> storePDPTE p pde \<lbrace>\<lambda>_. Invariants_H.valid_queues\<rbrace>"
  by (wp valid_queues_lift | simp add: pred_tcb_at'_def)+

lemma storePML4E_valid_queues [wp]:
  "\<lbrace>Invariants_H.valid_queues\<rbrace> storePML4E p pde \<lbrace>\<lambda>_. Invariants_H.valid_queues\<rbrace>"
  by (wp valid_queues_lift | simp add: pred_tcb_at'_def)+

lemma storePDE_valid_queues' [wp]:
  "\<lbrace>valid_queues'\<rbrace> storePDE p pde \<lbrace>\<lambda>_. valid_queues'\<rbrace>"
  by (wp valid_queues_lift')

lemma storePDE_state_refs' [wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of' s)\<rbrace> storePDE p pde \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  apply (clarsimp simp: storePDE_def)
  apply (clarsimp simp: setObject_def valid_def in_monad split_def
                        updateObject_default_def projectKOs objBits_simps
                        in_magnitude_check state_refs_of'_def ps_clear_upd'
                 elim!: rsubst[where P=P] intro!: ext
             split del: if_split cong: option.case_cong if_cong)
  apply (simp split: option.split)
  done

lemma storePDE_iflive [wp]:
  "\<lbrace>if_live_then_nonz_cap'\<rbrace> storePDE p pde \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  apply (simp add: storePDE_def)
  apply (rule hoare_pre)
   apply (rule setObject_iflive' [where P=\<top>], simp)
      apply (simp add: objBits_simps archObjSize_def)
     apply (auto simp: updateObject_default_def in_monad projectKOs)
  done

lemma setObject_pde_ksInt [wp]:
  "\<lbrace>\<lambda>s. P (ksInterruptState s)\<rbrace> setObject p (pde::pde) \<lbrace>\<lambda>_. \<lambda>s. P (ksInterruptState s)\<rbrace>"
  by (wp setObject_ksInterrupt updateObject_default_inv|simp)+

lemma storePDPTE_valid_queues' [wp]:
  "\<lbrace>valid_queues'\<rbrace> storePDPTE p pdpte \<lbrace>\<lambda>_. valid_queues'\<rbrace>"
  by (wp valid_queues_lift')

lemma storePDPTE_state_refs' [wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of' s)\<rbrace> storePDPTE p pdpte \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  apply (clarsimp simp: storePDPTE_def)
  apply (clarsimp simp: setObject_def valid_def in_monad split_def
                        updateObject_default_def projectKOs objBits_simps
                        in_magnitude_check state_refs_of'_def ps_clear_upd'
                 elim!: rsubst[where P=P] intro!: ext
             split del: if_split cong: option.case_cong if_cong)
  apply (simp split: option.split)
  done

lemma storePDPTE_iflive [wp]:
  "\<lbrace>if_live_then_nonz_cap'\<rbrace> storePDPTE p pdpte \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  apply (simp add: storePDPTE_def)
  apply (rule hoare_pre)
   apply (rule setObject_iflive' [where P=\<top>], simp)
      apply (simp add: objBits_simps archObjSize_def)
     apply (auto simp: updateObject_default_def in_monad projectKOs)
  done

lemma setObject_pdpte_ksInt [wp]:
  "\<lbrace>\<lambda>s. P (ksInterruptState s)\<rbrace> setObject p (pdpte::pdpte) \<lbrace>\<lambda>_. \<lambda>s. P (ksInterruptState s)\<rbrace>"
  by (wp setObject_ksInterrupt updateObject_default_inv|simp)+

lemma storePML4E_valid_queues' [wp]:
  "\<lbrace>valid_queues'\<rbrace> storePML4E p pml4e \<lbrace>\<lambda>_. valid_queues'\<rbrace>"
  by (wp valid_queues_lift')

lemma storePML4E_state_refs' [wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of' s)\<rbrace> storePML4E p pml4e \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  apply (clarsimp simp: storePML4E_def)
  apply (clarsimp simp: setObject_def valid_def in_monad split_def
                        updateObject_default_def projectKOs objBits_simps
                        in_magnitude_check state_refs_of'_def ps_clear_upd'
                 elim!: rsubst[where P=P] intro!: ext
             split del: if_split cong: option.case_cong if_cong)
  apply (simp split: option.split)
  done

lemma storePML4E_iflive [wp]:
  "\<lbrace>if_live_then_nonz_cap'\<rbrace> storePML4E p pml4e \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  apply (simp add: storePML4E_def)
  apply (rule hoare_pre)
   apply (rule setObject_iflive' [where P=\<top>], simp)
      apply (simp add: objBits_simps archObjSize_def)
     apply (auto simp: updateObject_default_def in_monad projectKOs)
  done

lemma setObject_pml4e_ksInt [wp]:
  "\<lbrace>\<lambda>s. P (ksInterruptState s)\<rbrace> setObject p (pml4e::pml4e) \<lbrace>\<lambda>_. \<lambda>s. P (ksInterruptState s)\<rbrace>"
  by (wp setObject_ksInterrupt updateObject_default_inv|simp)+

crunch ksInterruptState [wp]: storePDE, storePDPTE, storePML4E "\<lambda>s. P (ksInterruptState s)"
  (ignore: setObject)

lemma storePDE_ifunsafe [wp]:
  "\<lbrace>if_unsafe_then_cap'\<rbrace> storePDE p pde \<lbrace>\<lambda>rv. if_unsafe_then_cap'\<rbrace>"
  apply (simp add: storePDE_def)
  apply (rule hoare_pre)
   apply (rule setObject_ifunsafe' [where P=\<top>], simp)
     apply (auto simp: updateObject_default_def in_monad projectKOs)[2]
   apply wp
  apply simp
  done

lemma storePDE_idle [wp]:
  "\<lbrace>valid_idle'\<rbrace> storePDE p pde \<lbrace>\<lambda>rv. valid_idle'\<rbrace>"
  unfolding valid_idle'_def
  by (rule hoare_lift_Pf [where f="ksIdleThread"]; wp)

lemma storePDPTE_ifunsafe [wp]:
  "\<lbrace>if_unsafe_then_cap'\<rbrace> storePDPTE p pde \<lbrace>\<lambda>rv. if_unsafe_then_cap'\<rbrace>"
  apply (simp add: storePDPTE_def)
  apply (rule hoare_pre)
   apply (rule setObject_ifunsafe' [where P=\<top>], simp)
     apply (auto simp: updateObject_default_def in_monad projectKOs)[2]
   apply wp
  apply simp
  done

lemma storePDPTE_idle [wp]:
  "\<lbrace>valid_idle'\<rbrace> storePDPTE p pde \<lbrace>\<lambda>rv. valid_idle'\<rbrace>"
  unfolding valid_idle'_def
  by (rule hoare_lift_Pf [where f="ksIdleThread"]; wp)

lemma storePML4E_ifunsafe [wp]:
  "\<lbrace>if_unsafe_then_cap'\<rbrace> storePML4E p pde \<lbrace>\<lambda>rv. if_unsafe_then_cap'\<rbrace>"
  apply (simp add: storePML4E_def)
  apply (rule hoare_pre)
   apply (rule setObject_ifunsafe' [where P=\<top>], simp)
     apply (auto simp: updateObject_default_def in_monad projectKOs)[2]
   apply wp
  apply simp
  done

lemma storePML4E_idle [wp]:
  "\<lbrace>valid_idle'\<rbrace> storePML4E p pde \<lbrace>\<lambda>rv. valid_idle'\<rbrace>"
  unfolding valid_idle'_def
  by (rule hoare_lift_Pf [where f="ksIdleThread"]; wp)

crunch arch' [wp]: storePDE, storePDPTE, storePML4E "\<lambda>s. P (ksArchState s)"
  (ignore: setObject)

crunch cur' [wp]: storePDE, storePDPTE, storePML4E "\<lambda>s. P (ksCurThread s)"
  (ignore: setObject)

lemma storePDE_irq_states' [wp]:
  "\<lbrace>valid_irq_states'\<rbrace> storePDE pde p \<lbrace>\<lambda>_. valid_irq_states'\<rbrace>"
  apply (simp add: storePDE_def)
  apply (wpsimp wp: valid_irq_states_lift' dmo_lift' no_irq_storeWord setObject_ksMachine
                    updateObject_default_inv)
  done

lemma storePDPTE_irq_states' [wp]:
  "\<lbrace>valid_irq_states'\<rbrace> storePDPTE pde p \<lbrace>\<lambda>_. valid_irq_states'\<rbrace>"
  apply (simp add: storePDPTE_def)
  apply (wpsimp wp: valid_irq_states_lift' dmo_lift' no_irq_storeWord setObject_ksMachine
                    updateObject_default_inv)
  done

lemma storePML4E_irq_states' [wp]:
  "\<lbrace>valid_irq_states'\<rbrace> storePML4E pde p \<lbrace>\<lambda>_. valid_irq_states'\<rbrace>"
  apply (simp add: storePML4E_def)
  apply (wpsimp wp: valid_irq_states_lift' dmo_lift' no_irq_storeWord setObject_ksMachine
                    updateObject_default_inv)
  done

crunch no_0_obj' [wp]: storePDE, storePDPTE, storePML4E no_0_obj'

lemma storePDE_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> storePDE p pde \<lbrace>\<lambda>_. valid_machine_state'\<rbrace>"
  apply (simp add: storePDE_def valid_machine_state'_def pointerInUserData_def
                   pointerInDeviceData_def)
  apply (wp setObject_typ_at_inv setObject_ksMachine updateObject_default_inv
            hoare_vcg_all_lift hoare_vcg_disj_lift | simp)+
  done

lemma storePDPTE_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> storePDPTE p pde \<lbrace>\<lambda>_. valid_machine_state'\<rbrace>"
  apply (simp add: storePDPTE_def valid_machine_state'_def pointerInUserData_def
                   pointerInDeviceData_def)
  apply (wp setObject_typ_at_inv setObject_ksMachine updateObject_default_inv
            hoare_vcg_all_lift hoare_vcg_disj_lift | simp)+
  done

lemma storePML4E_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> storePML4E p pde \<lbrace>\<lambda>_. valid_machine_state'\<rbrace>"
  apply (simp add: storePML4E_def valid_machine_state'_def pointerInUserData_def
                   pointerInDeviceData_def)
  apply (wp setObject_typ_at_inv setObject_ksMachine updateObject_default_inv
            hoare_vcg_all_lift hoare_vcg_disj_lift | simp)+
  done

crunch pspace_domain_valid[wp]: storePDE, storePDPTE, storePML4E "pspace_domain_valid"

lemma storePDE_ct_not_inQ[wp]:
  "\<lbrace>ct_not_inQ\<rbrace> storePDE p pde \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  apply (rule ct_not_inQ_lift [OF storePDE_nosch])
  apply (simp add: storePDE_def)
  apply (rule hoare_weaken_pre)
   apply (wps setObject_PDE_ct)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp: updateObject_default_def in_monad)+
  done

lemma setObject_pde_cur_domain[wp]:
  "\<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace> setObject t (v::pde) \<lbrace>\<lambda>rv s. P (ksCurDomain s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma setObject_pde_ksDomSchedule[wp]:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace> setObject t (v::pde) \<lbrace>\<lambda>rv s. P (ksDomSchedule s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma storePDE_cur_domain[wp]:
  "\<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace> storePDE p pde \<lbrace>\<lambda>rv s. P (ksCurDomain s)\<rbrace>"
by (simp add: storePDE_def) wp

lemma storePDE_ksDomSchedule[wp]:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace> storePDE p pde \<lbrace>\<lambda>rv s. P (ksDomSchedule s)\<rbrace>"
by (simp add: storePDE_def) wp

lemma storePDE_tcb_obj_at'[wp]:
  "\<lbrace>obj_at' (P::tcb \<Rightarrow> bool) t\<rbrace> storePDE p pde \<lbrace>\<lambda>_. obj_at' P t\<rbrace>"
  apply (simp add: storePDE_def)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp add: updateObject_default_def in_monad)
  done

lemma storePDE_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t\<rbrace> storePDE p pde \<lbrace>\<lambda>_. tcb_in_cur_domain' t\<rbrace>"
  by (wp tcb_in_cur_domain'_lift)

lemma storePDE_ct_idle_or_in_cur_domain'[wp]:
  "\<lbrace>ct_idle_or_in_cur_domain'\<rbrace> storePDE p pde \<lbrace>\<lambda>_. ct_idle_or_in_cur_domain'\<rbrace>"
  by (wp ct_idle_or_in_cur_domain'_lift hoare_vcg_disj_lift)

lemma setObject_pte_ksDomScheduleIdx [wp]:
  "\<lbrace>\<lambda>s. P (ksDomScheduleIdx s)\<rbrace> setObject p (pte::pte) \<lbrace>\<lambda>_. \<lambda>s. P (ksDomScheduleIdx s)\<rbrace>"
  by (wp updateObject_default_inv|simp add:setObject_def | wpc)+

lemma setObject_pde_ksDomScheduleIdx [wp]:
  "\<lbrace>\<lambda>s. P (ksDomScheduleIdx s)\<rbrace> setObject p (pde::pde) \<lbrace>\<lambda>_. \<lambda>s. P (ksDomScheduleIdx s)\<rbrace>"
  by (wp updateObject_default_inv|simp add:setObject_def | wpc)+

lemma storePDPTE_ct_not_inQ[wp]:
  "\<lbrace>ct_not_inQ\<rbrace> storePDPTE p pdpte \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  apply (rule ct_not_inQ_lift [OF storePDPTE_nosch])
  apply (simp add: storePDPTE_def)
  apply (rule hoare_weaken_pre)
   apply (wps setObject_PDPTE_ct)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp: updateObject_default_def in_monad)+
  done

lemma setObject_pdpte_cur_domain[wp]:
  "\<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace> setObject t (v::pdpte) \<lbrace>\<lambda>rv s. P (ksCurDomain s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma setObject_pdpte_ksDomSchedule[wp]:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace> setObject t (v::pdpte) \<lbrace>\<lambda>rv s. P (ksDomSchedule s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma storePDPTE_cur_domain[wp]:
  "\<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace> storePDPTE p pdpte \<lbrace>\<lambda>rv s. P (ksCurDomain s)\<rbrace>"
by (simp add: storePDPTE_def) wp

lemma storePDPTE_ksDomSchedule[wp]:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace> storePDPTE p pdpte \<lbrace>\<lambda>rv s. P (ksDomSchedule s)\<rbrace>"
by (simp add: storePDPTE_def) wp

lemma storePDPTE_tcb_obj_at'[wp]:
  "\<lbrace>obj_at' (P::tcb \<Rightarrow> bool) t\<rbrace> storePDPTE p pdpte \<lbrace>\<lambda>_. obj_at' P t\<rbrace>"
  apply (simp add: storePDPTE_def)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp add: updateObject_default_def in_monad)
  done

lemma storePDPTE_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t\<rbrace> storePDPTE p pdpte \<lbrace>\<lambda>_. tcb_in_cur_domain' t\<rbrace>"
  by (wp tcb_in_cur_domain'_lift)

lemma storePDPTE_ct_idle_or_in_cur_domain'[wp]:
  "\<lbrace>ct_idle_or_in_cur_domain'\<rbrace> storePDPTE p pdpte \<lbrace>\<lambda>_. ct_idle_or_in_cur_domain'\<rbrace>"
  by (wp ct_idle_or_in_cur_domain'_lift hoare_vcg_disj_lift)

lemma setObject_pdpte_ksDomScheduleIdx [wp]:
  "\<lbrace>\<lambda>s. P (ksDomScheduleIdx s)\<rbrace> setObject p (pdpte::pdpte) \<lbrace>\<lambda>_. \<lambda>s. P (ksDomScheduleIdx s)\<rbrace>"
  by (wp updateObject_default_inv|simp add:setObject_def | wpc)+

lemma storePML4E_ct_not_inQ[wp]:
  "\<lbrace>ct_not_inQ\<rbrace> storePML4E p pml4e \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  apply (rule ct_not_inQ_lift [OF storePML4E_nosch])
  apply (simp add: storePML4E_def)
  apply (rule hoare_weaken_pre)
   apply (wps setObject_PML4E_ct)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp: updateObject_default_def in_monad)+
  done

lemma setObject_pml4e_cur_domain[wp]:
  "\<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace> setObject t (v::pml4e) \<lbrace>\<lambda>rv s. P (ksCurDomain s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma setObject_pml4e_ksDomSchedule[wp]:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace> setObject t (v::pml4e) \<lbrace>\<lambda>rv s. P (ksDomSchedule s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma storePML4E_cur_domain[wp]:
  "\<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace> storePML4E p pml4e \<lbrace>\<lambda>rv s. P (ksCurDomain s)\<rbrace>"
by (simp add: storePML4E_def) wp

lemma storePML4E_ksDomSchedule[wp]:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace> storePML4E p pml4e \<lbrace>\<lambda>rv s. P (ksDomSchedule s)\<rbrace>"
by (simp add: storePML4E_def) wp

lemma storePML4E_tcb_obj_at'[wp]:
  "\<lbrace>obj_at' (P::tcb \<Rightarrow> bool) t\<rbrace> storePML4E p pml4e \<lbrace>\<lambda>_. obj_at' P t\<rbrace>"
  apply (simp add: storePML4E_def)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp add: updateObject_default_def in_monad)
  done

lemma storePML4E_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t\<rbrace> storePML4E p pml4e \<lbrace>\<lambda>_. tcb_in_cur_domain' t\<rbrace>"
  by (wp tcb_in_cur_domain'_lift)

lemma storePML4E_ct_idle_or_in_cur_domain'[wp]:
  "\<lbrace>ct_idle_or_in_cur_domain'\<rbrace> storePML4E p pml4e \<lbrace>\<lambda>_. ct_idle_or_in_cur_domain'\<rbrace>"
  by (wp ct_idle_or_in_cur_domain'_lift hoare_vcg_disj_lift)

lemma setObject_pml4e_ksDomScheduleIdx [wp]:
  "\<lbrace>\<lambda>s. P (ksDomScheduleIdx s)\<rbrace> setObject p (pml4e::pml4e) \<lbrace>\<lambda>_. \<lambda>s. P (ksDomScheduleIdx s)\<rbrace>"
  by (wp updateObject_default_inv|simp add:setObject_def | wpc)+

crunch ksDomScheduleIdx[wp]: storePTE, storePDE, storePDPTE, storePML4E "\<lambda>s. P (ksDomScheduleIdx s)"
(ignore: getObject setObject)

crunch gsMaxObjectSize[wp]: storePTE, storePDE, storePDPTE, storePML4E "\<lambda>s. P (gsMaxObjectSize s)"
(ignore: getObject setObject wp: setObject_ksPSpace_only updateObject_default_inv)

crunch gsUntypedZeroRanges[wp]: storePTE, storePDE, storePDPTE, storePML4E "\<lambda>s. P (gsUntypedZeroRanges s)"
(ignore: getObject setObject wp: setObject_ksPSpace_only updateObject_default_inv)

lemma storePDE_invs[wp]:
  "\<lbrace>invs' and valid_pde' pde\<rbrace>
      storePDE p pde
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def valid_pspace'_def)
  apply (rule hoare_pre)
   apply (wp sch_act_wf_lift valid_global_refs_lift'
             irqs_masked_lift
             valid_arch_state_lift' valid_irq_node_lift
             cur_tcb_lift valid_irq_handlers_lift''
             untyped_ranges_zero_lift
           | simp add: cteCaps_of_def o_def)+
  apply clarsimp
  done

lemma storePDPTE_invs[wp]:
  "\<lbrace>invs' and valid_pdpte' pde\<rbrace>
      storePDPTE p pde
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def valid_pspace'_def)
  apply (rule hoare_pre)
   apply (wp sch_act_wf_lift valid_global_refs_lift'
             irqs_masked_lift
             valid_arch_state_lift' valid_irq_node_lift
             cur_tcb_lift valid_irq_handlers_lift''
             untyped_ranges_zero_lift
           | simp add: cteCaps_of_def o_def)+
  apply clarsimp
  done

lemma storePML4E_invs[wp]:
  "\<lbrace>invs' and valid_pml4e' pde\<rbrace>
      storePML4E p pde
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def valid_pspace'_def)
  apply (rule hoare_pre)
   apply (wp sch_act_wf_lift valid_global_refs_lift'
             irqs_masked_lift
             valid_arch_state_lift' valid_irq_node_lift
             cur_tcb_lift valid_irq_handlers_lift''
             untyped_ranges_zero_lift
           | simp add: cteCaps_of_def o_def)+
  apply clarsimp
  done

lemma storePTE_valid_mdb [wp]:
  "\<lbrace>valid_mdb'\<rbrace> storePTE p pte \<lbrace>\<lambda>rv. valid_mdb'\<rbrace>"
  by (simp add: valid_mdb'_def) wp

crunch nosch [wp]: storePTE "\<lambda>s. P (ksSchedulerAction s)"
  (simp: updateObject_default_def)

crunch ksQ [wp]: storePTE "\<lambda>s. P (ksReadyQueues s)"
  (simp: updateObject_default_def ignore: setObject)

lemma storePTE_inQ[wp]:
  "\<lbrace>\<lambda>s. P (obj_at' (inQ d p) t s)\<rbrace> storePTE ptr pde \<lbrace>\<lambda>rv s. P (obj_at' (inQ d p) t s)\<rbrace>"
  apply (simp add: obj_at'_real_def storePTE_def)
  apply (wp setObject_ko_wp_at | simp add: objBits_simps archObjSize_def)+
  apply (clarsimp simp: projectKOs obj_at'_def ko_wp_at'_def)
  done

crunch norqL1[wp]: storePTE "\<lambda>s. P (ksReadyQueuesL1Bitmap s)"
  (simp: updateObject_default_def ignore: setObject)

crunch norqL2[wp]: storePTE "\<lambda>s. P (ksReadyQueuesL2Bitmap s)"
  (simp: updateObject_default_def ignore: setObject)

lemma storePTE_valid_queues [wp]:
  "\<lbrace>Invariants_H.valid_queues\<rbrace> storePTE p pde \<lbrace>\<lambda>_. Invariants_H.valid_queues\<rbrace>"
  by (wp valid_queues_lift | simp add: pred_tcb_at'_def)+

lemma storePTE_valid_queues' [wp]:
  "\<lbrace>valid_queues'\<rbrace> storePTE p pde \<lbrace>\<lambda>_. valid_queues'\<rbrace>"
  by (wp valid_queues_lift')

lemma storePTE_iflive [wp]:
  "\<lbrace>if_live_then_nonz_cap'\<rbrace> storePTE p pte \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  apply (simp add: storePTE_def)
  apply (rule hoare_pre)
   apply (rule setObject_iflive' [where P=\<top>], simp)
      apply (simp add: objBits_simps archObjSize_def)
     apply (auto simp: updateObject_default_def in_monad projectKOs)
  done

lemma setObject_pte_ksInt [wp]:
  "\<lbrace>\<lambda>s. P (ksInterruptState s)\<rbrace> setObject p (pte::pte) \<lbrace>\<lambda>_. \<lambda>s. P (ksInterruptState s)\<rbrace>"
  by (wp setObject_ksInterrupt updateObject_default_inv|simp)+

crunch ksInt' [wp]: storePTE "\<lambda>s. P (ksInterruptState s)"
  (ignore: setObject)

lemma storePTE_ifunsafe [wp]:
  "\<lbrace>if_unsafe_then_cap'\<rbrace> storePTE p pte \<lbrace>\<lambda>rv. if_unsafe_then_cap'\<rbrace>"
  apply (simp add: storePTE_def)
  apply (rule hoare_pre)
   apply (rule setObject_ifunsafe' [where P=\<top>], simp)
     apply (auto simp: updateObject_default_def in_monad projectKOs)[2]
   apply wp
  apply simp
  done

lemma storePTE_idle [wp]:
  "\<lbrace>valid_idle'\<rbrace> storePTE p pte \<lbrace>\<lambda>rv. valid_idle'\<rbrace>"
  unfolding valid_idle'_def
  by (rule hoare_lift_Pf [where f="ksIdleThread"]; wp)

crunch arch' [wp]: storePTE "\<lambda>s. P (ksArchState s)"
  (ignore: setObject)

crunch cur' [wp]: storePTE "\<lambda>s. P (ksCurThread s)"
  (ignore: setObject)

lemma storePTE_irq_states' [wp]:
  "\<lbrace>valid_irq_states'\<rbrace> storePTE pte p \<lbrace>\<lambda>_. valid_irq_states'\<rbrace>"
  apply (simp add: storePTE_def)
  apply (wpsimp wp: valid_irq_states_lift' dmo_lift' no_irq_storeWord setObject_ksMachine
                    updateObject_default_inv)
  done

lemma storePTE_valid_objs [wp]:
  "\<lbrace>valid_objs' and valid_pte' pte\<rbrace> storePTE p pte \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (simp add: storePTE_def doMachineOp_def split_def)
  apply (rule hoare_pre)
   apply (wp hoare_drop_imps|wpc|simp)+
   apply (rule setObject_valid_objs')
   prefer 2
   apply assumption
  apply (clarsimp simp: updateObject_default_def in_monad)
  apply (clarsimp simp: valid_obj'_def)
  done

crunch no_0_obj' [wp]: storePTE no_0_obj'

lemma storePTE_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> storePTE p pde \<lbrace>\<lambda>_. valid_machine_state'\<rbrace>"
  apply (simp add: storePTE_def valid_machine_state'_def pointerInUserData_def
                   pointerInDeviceData_def)
  apply (wp setObject_typ_at_inv setObject_ksMachine updateObject_default_inv
            hoare_vcg_all_lift hoare_vcg_disj_lift | simp)+
  done

crunch pspace_domain_valid[wp]: storePTE "pspace_domain_valid"

lemma storePTE_ct_not_inQ[wp]:
  "\<lbrace>ct_not_inQ\<rbrace> storePTE p pte \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  apply (rule ct_not_inQ_lift [OF storePTE_nosch])
  apply (simp add: storePTE_def)
  apply (rule hoare_weaken_pre)
   apply (wps setObject_pte_ct)
  apply (rule obj_at_setObject2)
   apply (clarsimp simp: updateObject_default_def in_monad)+
  done

lemma setObject_pte_cur_domain[wp]:
  "\<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace> setObject t (v::pte) \<lbrace>\<lambda>rv s. P (ksCurDomain s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma setObject_pte_ksDomSchedule[wp]:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace> setObject t (v::pte) \<lbrace>\<lambda>rv s. P (ksDomSchedule s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma storePTE_cur_domain[wp]:
  "\<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace> storePTE p pde \<lbrace>\<lambda>rv s. P (ksCurDomain s)\<rbrace>"
  by (simp add: storePTE_def) wp

lemma storePTE_ksDomSchedule[wp]:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace> storePTE p pde \<lbrace>\<lambda>rv s. P (ksDomSchedule s)\<rbrace>"
  by (simp add: storePTE_def) wp


lemma storePTE_tcb_obj_at'[wp]:
  "\<lbrace>obj_at' (P::tcb \<Rightarrow> bool) t\<rbrace> storePTE p pte \<lbrace>\<lambda>_. obj_at' P t\<rbrace>"
  apply (simp add: storePTE_def)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp add: updateObject_default_def in_monad)
  done

lemma storePTE_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t\<rbrace> storePTE p pte \<lbrace>\<lambda>_. tcb_in_cur_domain' t\<rbrace>"
  by (wp tcb_in_cur_domain'_lift)

lemma storePTE_ct_idle_or_in_cur_domain'[wp]:
  "\<lbrace>ct_idle_or_in_cur_domain'\<rbrace> storePTE p pte \<lbrace>\<lambda>_. ct_idle_or_in_cur_domain'\<rbrace>"
  by (wp ct_idle_or_in_cur_domain'_lift hoare_vcg_disj_lift)

lemma storePTE_invs [wp]:
  "\<lbrace>invs' and valid_pte' pte\<rbrace> storePTE p pte \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def valid_pspace'_def)
  apply (rule hoare_pre)
   apply (wp sch_act_wf_lift valid_global_refs_lift' irqs_masked_lift
             valid_arch_state_lift' valid_irq_node_lift
             cur_tcb_lift valid_irq_handlers_lift''
             untyped_ranges_zero_lift
           | simp add: cteCaps_of_def o_def)+
  apply clarsimp
  done

lemma setASIDPool_valid_objs [wp]:
  "\<lbrace>valid_objs' and valid_asid_pool' ap\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (rule hoare_pre)
   apply (rule setObject_valid_objs')
   prefer 2
   apply assumption
  apply (clarsimp simp: updateObject_default_def in_monad)
  apply (clarsimp simp: valid_obj'_def)
  done

lemma setASIDPool_valid_mdb [wp]:
  "\<lbrace>valid_mdb'\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv. valid_mdb'\<rbrace>"
  by (simp add: valid_mdb'_def) wp

lemma setASIDPool_nosch [wp]:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  by (wp setObject_nosch updateObject_default_inv|simp)+

lemma setASIDPool_ksQ [wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueues s)\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv s. P (ksReadyQueues s)\<rbrace>"
  by (wp setObject_qs updateObject_default_inv|simp)+

lemma setASIDPool_inQ[wp]:
  "\<lbrace>\<lambda>s. P (obj_at' (inQ d p) t s)\<rbrace>
     setObject ptr (ap::asidpool)
   \<lbrace>\<lambda>rv s. P (obj_at' (inQ d p) t s)\<rbrace>"
  apply (simp add: obj_at'_real_def)
  apply (wp setObject_ko_wp_at
            | simp add: objBits_simps archObjSize_def)+
   apply (simp add: pageBits_def)
  apply (clarsimp simp: obj_at'_def ko_wp_at'_def projectKOs)
  done

lemma setASIDPool_qsL1 [wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueuesL1Bitmap s)\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv s. P (ksReadyQueuesL1Bitmap s)\<rbrace>"
  by (wp setObject_qs updateObject_default_inv|simp)+

lemma setASIDPool_qsL2 [wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueuesL2Bitmap s)\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv s. P (ksReadyQueuesL2Bitmap s)\<rbrace>"
  by (wp setObject_qs updateObject_default_inv|simp)+

lemma setASIDPool_valid_queues [wp]:
  "\<lbrace>Invariants_H.valid_queues\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. Invariants_H.valid_queues\<rbrace>"
  by (wp valid_queues_lift | simp add: pred_tcb_at'_def)+

lemma setASIDPool_valid_queues' [wp]:
  "\<lbrace>valid_queues'\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. valid_queues'\<rbrace>"
  by (wp valid_queues_lift')

lemma setASIDPool_state_refs' [wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of' s)\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  apply (clarsimp simp: setObject_def valid_def in_monad split_def
                        updateObject_default_def projectKOs objBits_simps
                        in_magnitude_check state_refs_of'_def ps_clear_upd'
                 elim!: rsubst[where P=P] intro!: ext
             split del: if_split cong: option.case_cong if_cong)
  apply (simp split: option.split)
  done

lemma setASIDPool_iflive [wp]:
  "\<lbrace>if_live_then_nonz_cap'\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  apply (rule hoare_pre)
   apply (rule setObject_iflive' [where P=\<top>], simp)
      apply (simp add: objBits_simps archObjSize_def)
     apply (auto simp: updateObject_default_def in_monad projectKOs pageBits_def)
  done

lemma setASIDPool_ksInt [wp]:
  "\<lbrace>\<lambda>s. P (ksInterruptState s)\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. \<lambda>s. P (ksInterruptState s)\<rbrace>"
  by (wp setObject_ksInterrupt updateObject_default_inv|simp)+

lemma setASIDPool_ifunsafe [wp]:
  "\<lbrace>if_unsafe_then_cap'\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv. if_unsafe_then_cap'\<rbrace>"
  apply (rule hoare_pre)
   apply (rule setObject_ifunsafe' [where P=\<top>], simp)
     apply (auto simp: updateObject_default_def in_monad projectKOs)[2]
   apply wp
  apply simp
  done

lemma setASIDPool_it' [wp]:
  "\<lbrace>\<lambda>s. P (ksIdleThread s)\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. \<lambda>s. P (ksIdleThread s)\<rbrace>"
  by (wp setObject_it updateObject_default_inv|simp)+

lemma setASIDPool_idle [wp]:
  "\<lbrace>valid_idle'\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv. valid_idle'\<rbrace>"
  unfolding valid_idle'_def
  by (rule hoare_lift_Pf [where f="ksIdleThread"]; wp)

lemma setASIDPool_irq_states' [wp]:
  "\<lbrace>valid_irq_states'\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. valid_irq_states'\<rbrace>"
  apply (rule hoare_pre)
   apply (rule hoare_use_eq [where f=ksInterruptState, OF setObject_ksInterrupt])
    apply (simp, rule updateObject_default_inv)
   apply (rule hoare_use_eq [where f=ksMachineState, OF setObject_ksMachine])
    apply (simp, rule updateObject_default_inv)
   apply wp
  apply assumption
  done


lemma setASIDPool_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. valid_machine_state'\<rbrace>"
  apply (simp add: valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def)
  apply (wp setObject_typ_at_inv setObject_ksMachine updateObject_default_inv
            hoare_vcg_all_lift hoare_vcg_disj_lift | simp)+
  done

lemma setASIDPool_ct_not_inQ[wp]:
  "\<lbrace>ct_not_inQ\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  apply (rule ct_not_inQ_lift [OF setObject_nosch])
   apply (simp add: updateObject_default_def | wp)+
  apply (rule hoare_weaken_pre)
   apply (wps setObject_ASID_ct)
  apply (rule obj_at_setObject2)
   apply (clarsimp simp: updateObject_default_def in_monad)+
  done

lemma setObject_asidpool_cur'[wp]:
  "\<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv s. P (ksCurThread s)\<rbrace>"
  apply (simp add: setObject_def)
  apply (wp | wpc | simp add: updateObject_default_def)+
  done

lemma setObject_asidpool_cur_domain[wp]:
  "\<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv s. P (ksCurDomain s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma setObject_asidpool_ksDomSchedule[wp]:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv s. P (ksDomSchedule s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma setObject_tcb_obj_at'[wp]:
  "\<lbrace>obj_at' (P::tcb \<Rightarrow> bool) t\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. obj_at' P t\<rbrace>"
  apply (rule obj_at_setObject2)
  apply (clarsimp simp add: updateObject_default_def in_monad)
  done

lemma setObject_asidpool_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. tcb_in_cur_domain' t\<rbrace>"
  by (wp tcb_in_cur_domain'_lift)

lemma setObject_asidpool_ct_idle_or_in_cur_domain'[wp]:
  "\<lbrace>ct_idle_or_in_cur_domain'\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. ct_idle_or_in_cur_domain'\<rbrace>"
  apply (rule ct_idle_or_in_cur_domain'_lift)
      apply (wp hoare_vcg_disj_lift)+
  done

lemma setObject_ap_ksDomScheduleIdx [wp]:
  "\<lbrace>\<lambda>s. P (ksDomScheduleIdx s)\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. \<lambda>s. P (ksDomScheduleIdx s)\<rbrace>"
  by (wp updateObject_default_inv|simp add:setObject_def | wpc)+

lemma setASIDPool_invs [wp]:
  "\<lbrace>invs' and valid_asid_pool' ap\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def valid_pspace'_def)
  apply (rule hoare_pre)
   apply (wp sch_act_wf_lift valid_global_refs_lift' irqs_masked_lift
             valid_arch_state_lift' valid_irq_node_lift
             cur_tcb_lift valid_irq_handlers_lift''
             untyped_ranges_zero_lift
             updateObject_default_inv
           | simp add: cteCaps_of_def
           | rule setObject_ksPSpace_only)+
  apply (clarsimp simp add: setObject_def o_def)
  done

crunch cte_wp_at'[wp]: unmapPageTable "\<lambda>s. P (cte_wp_at' P' p s)"
  (wp: crunch_wps simp: crunch_simps ignore: getObject setObject)

crunch cte_wp_at'[wp]: unmapPageDirectory "\<lambda>s. P (cte_wp_at' P' p s)"
  (wp: crunch_wps simp: crunch_simps ignore: getObject setObject)

crunch cte_wp_at'[wp]: unmapPDPT "\<lambda>s. P (cte_wp_at' P' p s)"
  (wp: crunch_wps simp: crunch_simps ignore: getObject setObject)

lemmas storePDE_Invalid_invs = storePDE_invs[where pde=InvalidPDE, simplified]
lemmas storePDPTE_Invalid_invs = storePDPTE_invs[where pde=InvalidPDPTE, simplified]
lemmas storePML4E_Invalid_invs = storePML4E_invs[where pde=InvalidPML4E, simplified]

lemma dmo_writeCR3_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp (writeCR3 a b) \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (wp dmo_invs' no_irq_writeCR3 no_irq)
  apply clarsimp
  apply (drule_tac P4="\<lambda>m'. underlying_memory m' p = underlying_memory m p"
         in use_valid[where P=P and Q="\<lambda>_. P" for P])
    apply (simp add: writeCR3_def machine_op_lift_def
                     machine_rest_lift_def split_def | wp)+
  done

(* FIXME x64: move*)
lemma no_irq_invalidateTranslationSingleASID[wp]:
  "no_irq (invalidateTranslationSingleASID a b)"
  by (simp add: invalidateTranslationSingleASID_def)

lemma dmo_invalidateTranslationSingleASID_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp (invalidateTranslationSingleASID a b) \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (wp dmo_invs' no_irq_invalidateTranslationSingleASID no_irq)
  apply clarsimp
  apply (drule_tac P4="\<lambda>m'. underlying_memory m' p = underlying_memory m p"
         in use_valid[where P=P and Q="\<lambda>_. P" for P])
    apply (simp add: invalidateTranslationSingleASID_def machine_op_lift_def
                     machine_rest_lift_def split_def | wp)+
  done

lemma dmo_invalidateASID_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp (invalidateASID a b) \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (wp dmo_invs' no_irq_invalidateASID no_irq)
  apply clarsimp
  apply (drule_tac P4="\<lambda>m'. underlying_memory m' p = underlying_memory m p"
         in use_valid[where P=P and Q="\<lambda>_. P" for P])
    apply (simp add: invalidateASID_def machine_op_lift_def
                     machine_rest_lift_def split_def | wp)+
  done

lemma x64KSCurrentCR3_update_inv[simp]:
  "invs' s \<Longrightarrow> invs' (s\<lparr>ksArchState := x64KSCurrentCR3_update (\<lambda>_. c) (ksArchState s)\<rparr>)"
  by (clarsimp simp: invs'_def valid_state'_def valid_global_refs'_def global_refs'_def
                        valid_arch_state'_def valid_machine_state'_def ct_not_inQ_def
                        ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def)

crunch invs'[wp]: unmapPageTable, unmapPageDirectory, unmapPDPT "invs'"
  (ignore: getObject setObject storePDE storePDPTE storePML4E doMachineOp
       wp: storePDE_Invalid_invs storePDPTE_Invalid_invs storePML4E_Invalid_invs mapM_wp'
           crunch_wps
     simp: crunch_simps)

lemma perform_pti_invs [wp]:
  "\<lbrace>invs' and valid_pti' pti\<rbrace> performPageTableInvocation pti \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (clarsimp simp: performPageTableInvocation_def getSlotCap_def
                 split: page_table_invocation.splits)
  apply (intro conjI allI impI)
   apply (rule hoare_pre)
    apply (wp arch_update_updateCap_invs getCTE_wp
              hoare_vcg_ex_lift  mapM_x_wp'
                | wpc | simp add: o_def
                | (simp only: imp_conv_disj, rule hoare_vcg_disj_lift))+
   apply (clarsimp simp: valid_pti'_def cte_wp_at_ctes_of
                         is_arch_update'_def isCap_simps valid_cap'_def
                         capAligned_def)
  apply (rule hoare_pre)
   apply (wpsimp wp: arch_update_updateCap_invs valid_pde_lift' hoare_vcg_all_lift hoare_vcg_ex_lift
             | wp_once hoare_drop_imps)+
  apply (clarsimp simp: cte_wp_at_ctes_of valid_pti'_def)
  done

lemma perform_pdi_invs [wp]:
  "\<lbrace>invs' and valid_pdi' pdi\<rbrace> performPageDirectoryInvocation pdi \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (clarsimp simp: performPageDirectoryInvocation_def getSlotCap_def
                 split: page_directory_invocation.splits)
  apply (intro conjI allI impI)
   apply (rule hoare_pre)
    apply (wp arch_update_updateCap_invs getCTE_wp
              hoare_vcg_ex_lift  mapM_x_wp'
                | wpc | simp add: o_def
                | (simp only: imp_conv_disj, rule hoare_vcg_disj_lift))+
   apply (clarsimp simp: valid_pdi'_def cte_wp_at_ctes_of
                         is_arch_update'_def isCap_simps valid_cap'_def
                         capAligned_def)
  apply (rule hoare_pre)
   apply (wpsimp wp: arch_update_updateCap_invs valid_pdpte_lift' hoare_vcg_all_lift hoare_vcg_ex_lift
             | wp_once hoare_drop_imps)+
  apply (clarsimp simp: cte_wp_at_ctes_of valid_pdi'_def)
  done

lemma perform_pdpti_invs [wp]:
  "\<lbrace>invs' and valid_pdpti' pdpti\<rbrace> performPDPTInvocation pdpti \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (clarsimp simp: performPDPTInvocation_def getSlotCap_def
                 split: pdptinvocation.splits)
  apply (intro conjI allI impI)
   apply (rule hoare_pre)
    apply (wp arch_update_updateCap_invs getCTE_wp
              hoare_vcg_ex_lift  mapM_x_wp'
                | wpc | simp add: o_def
                | (simp only: imp_conv_disj, rule hoare_vcg_disj_lift))+
   apply (clarsimp simp: valid_pdpti'_def cte_wp_at_ctes_of
                         is_arch_update'_def isCap_simps valid_cap'_def
                         capAligned_def)
  apply (rule hoare_pre)
   apply (wpsimp wp: arch_update_updateCap_invs hoare_vcg_all_lift hoare_vcg_ex_lift
             | wp_once hoare_drop_imps)+
  apply (clarsimp simp: cte_wp_at_ctes_of valid_pdpti'_def)
  done

lemma mapM_x_storePTE_invs:
  "\<lbrace>invs' and valid_pte' pte\<rbrace> mapM_x (swp storePTE pte) ps \<lbrace>\<lambda>xa. invs'\<rbrace>"
  apply (rule hoare_post_imp)
   prefer 2
   apply (rule mapM_x_wp')
   apply simp
   apply (wp valid_pte_lift')
    apply simp+
  done

lemma mapM_x_storePDE_invs:
  "\<lbrace>invs' and valid_pde' pde \<rbrace>
         mapM_x (swp storePDE pde) ps \<lbrace>\<lambda>xa. invs'\<rbrace>"
  apply (rule hoare_post_imp)
   prefer 2
   apply (rule mapM_x_wp[OF _ subset_refl])
   apply simp
   apply (wp valid_pde_lift')
    apply simp+
  done

lemma mapM_storePTE_invs:
  "\<lbrace>invs' and valid_pte' pte\<rbrace> mapM (swp storePTE pte) ps \<lbrace>\<lambda>xa. invs'\<rbrace>"
  apply (rule hoare_post_imp)
   prefer 2
   apply (rule mapM_wp')
   apply simp
   apply (wp valid_pte_lift')
    apply simp+
  done

lemma mapM_storePDE_invs:
  "\<lbrace>invs' and valid_pde' pde
       and K (\<forall>p \<in> set ps. valid_pde_mapping' (p && mask pdBits) pde)\<rbrace>
       mapM (swp storePDE pde) ps \<lbrace>\<lambda>xa. invs'\<rbrace>"
  apply (rule hoare_post_imp)
   prefer 2
   apply (rule mapM_wp')
   apply simp
   apply (wp valid_pde_lift')
    apply simp+
  done

crunch cte_wp_at': unmapPage "\<lambda>s. P (cte_wp_at' P' p s)"
  (wp: crunch_wps simp: crunch_simps ignore: getObject)

lemmas unmapPage_typ_ats [wp] = typ_at_lifts [OF unmapPage_typ_at']

crunch inv: lookupPTSlot P
  (wp: crunch_wps simp: crunch_simps ignore: getObject)

lemma unmapPage_invs' [wp]:
  "\<lbrace>invs'\<rbrace> unmapPage sz asid vptr pptr \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: unmapPage_def)
  apply (rule hoare_pre)
   apply (wp lookupPTSlot_inv
             mapM_storePTE_invs mapM_storePDE_invs
             hoare_vcg_const_imp_lift
         |wpc
         |simp)+
  done

crunch invs'[wp]: pteCheckIfMapped, pdeCheckIfMapped "invs'"
  (ignore: getObject)

crunch valid_pte'[wp]: pteCheckIfMapped, pdeCheckIfMapped "valid_pte' pte"
  (ignore: getObject)

crunch valid_pde'[wp]: pteCheckIfMapped, pdeCheckIfMapped "valid_pde' pde"
  (ignore: getObject)

lemma perform_pt_invs [wp]:
  notes no_irq[wp]
  shows
  "\<lbrace>invs' and valid_page_inv' pt\<rbrace> performPageInvocation pt \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: performPageInvocation_def)
  apply (cases pt)
     apply clarsimp
     apply ((wpsimp wp: hoare_vcg_all_lift hoare_vcg_ex_lift hoare_vcg_const_imp_lift
                       arch_update_updateCap_invs unmapPage_cte_wp_at' getSlotCap_wp
                  simp: valid_page_inv'_def valid_slots'_def is_arch_update'_def
                 split: vmpage_entry.splits
             | (auto simp: is_arch_update'_def)[1])+)[3]
  apply (wp arch_update_updateCap_invs unmapPage_cte_wp_at' getSlotCap_wp|wpc| clarsimp)+
   apply (rename_tac acap word a b)
   apply (rule_tac Q="\<lambda>_. invs' and cte_wp_at' (\<lambda>cte. \<exists>r R mt sz d m. cteCap cte =
                                       ArchObjectCap (PageCap r R mt sz d m)) word"
               in hoare_strengthen_post)
    apply (wp unmapPage_cte_wp_at')
   apply (clarsimp simp: cte_wp_at_ctes_of)
   apply (case_tac cte)
   apply clarsimp
   apply (frule ctes_of_valid_cap')
    apply (auto simp: valid_page_inv'_def valid_slots'_def cte_wp_at_ctes_of)[1]
   apply (simp add: is_arch_update'_def isCap_simps)
   apply (simp add: valid_cap'_def capAligned_def)
  apply (clarsimp simp: cte_wp_at_ctes_of valid_page_inv'_def)
  apply (simp add: is_arch_update'_def isCap_simps)
  apply (case_tac cte)
  apply clarsimp+
  apply (frule ctes_of_valid_cap')
   apply (auto simp: valid_page_inv'_def valid_slots'_def cte_wp_at_ctes_of)[1]
  apply (simp add: valid_cap'_def capAligned_def)
  done

lemma ucast_ucast_le_low_bits [simp]:
  "ucast (ucast x :: 9 word) \<le> (2 ^ asid_low_bits - 1 :: machine_word)"
  apply (rule word_less_sub_1)
  apply (rule order_less_le_trans)
   apply (rule ucast_less)
   apply simp
  apply (simp add: asid_low_bits_def)
  done

lemma setObject_cte_obj_at_ap':
  shows
  "\<lbrace>\<lambda>s. P' (obj_at' (P :: asidpool \<Rightarrow> bool) p s)\<rbrace>
  setObject c (cte::cte)
  \<lbrace>\<lambda>_ s. P' (obj_at' P p s)\<rbrace>"
  apply (clarsimp simp: setObject_def in_monad split_def
                        valid_def lookupAround2_char1
                        obj_at'_def ps_clear_upd' projectKOs
             split del: if_split)
  apply (clarsimp elim!: rsubst[where P=P'])
  apply (clarsimp simp: updateObject_cte in_monad objBits_simps
                        tcbCTableSlot_def tcbVTableSlot_def
                        typeError_def
                 split: if_split_asm
                        Structures_H.kernel_object.split_asm)
  done

lemma updateCap_ko_at_ap_inv'[wp]:
  "\<lbrace>\<lambda>s. P (ko_at' (ko::asidpool) p s )\<rbrace> updateCap a b \<lbrace>\<lambda>rv s. P ( ko_at' ko p s)\<rbrace>"
  by (wpsimp simp: updateCap_def setCTE_def wp: setObject_cte_obj_at_ap')

lemma perform_aci_invs [wp]:
  "\<lbrace>invs' and valid_apinv' api\<rbrace> performASIDPoolInvocation api \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (clarsimp simp: performASIDPoolInvocation_def split: asidpool_invocation.splits)
  apply (wp arch_update_updateCap_invs getASID_wp getSlotCap_wp hoare_vcg_all_lift
            hoare_vcg_imp_lift
          | simp add: o_def)+
  apply (clarsimp simp: valid_apinv'_def cte_wp_at_ctes_of)
  apply (case_tac cte)
  apply (clarsimp split: if_splits)
  apply (drule ctes_of_valid_cap', fastforce)
  apply (clarsimp simp: isPML4Cap'_def valid_cap'_def capAligned_def is_arch_update'_def isCap_simps)
  apply (drule ko_at_valid_objs', fastforce, clarsimp simp: projectKOs)
  apply (clarsimp simp: valid_obj'_def ran_def mask_asid_low_bits_ucast_ucast
                 split: if_split_asm)
  apply (case_tac x, clarsimp simp: inv_def)
  apply (clarsimp simp: page_map_l4_at'_def, drule_tac x=0 in spec)
  apply (auto simp: bit_simps )
  done

lemma capMaster_isPML4Cap':
  "capMasterCap cap' = capMasterCap cap \<Longrightarrow> isPML4Cap' cap' = isPML4Cap' cap"
  by (simp add: capMasterCap_def isPML4Cap'_def split: capability.splits arch_capability.splits)

lemma isPML4Cap'_PML4 :
  "isPML4Cap' (ArchObjectCap (PML4Cap r m))"
  by (simp add: isPML4Cap'_def)


lemma diminished_valid':
  "diminished' cap cap' \<Longrightarrow> valid_cap' cap = valid_cap' cap'"
  apply (clarsimp simp add: diminished'_def)
  apply (rule ext)
  apply (simp add: maskCapRights_def Let_def split del: if_split)
  done

lemma diminished_isPML4Cap':
  "diminished' cap cap' \<Longrightarrow> isPML4Cap' cap' = isPML4Cap' cap"
  by (blast dest: diminished_capMaster capMaster_isPML4Cap')

end

lemma cteCaps_of_ctes_of_lift:
  "(\<And>P. \<lbrace>\<lambda>s. P (ctes_of s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ctes_of s)\<rbrace>) \<Longrightarrow> \<lbrace>\<lambda>s. P (cteCaps_of s) \<rbrace> f \<lbrace>\<lambda>_ s. P (cteCaps_of s)\<rbrace>"
  unfolding cteCaps_of_def .

end
