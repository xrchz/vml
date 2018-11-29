(*
  Definitions and proofs of correctness for flatLang dead code elimination.

  General sptree lemmas, definitions of reachability in a num_set num_map,
  and proofs of semantic preservation for flat_elim.
*)

open preamble sptreeTheory flatLangTheory flat_elimTheory
     flatSemTheory flatPropsTheory

val _ = new_theory "flat_elimProof";

val grammar_ancestry =
  ["flat_elim", "flatSem", "flatLang", "flatProps",
    "misc", "ffi", "sptree"];

val _ = set_grammar_ancestry grammar_ancestry;

(* BEGIN TODO: move to sptreeTheory *)

val mk_BN_thm = prove(
  ``!t1 t2. mk_BN t1 t2 =
            if isEmpty t1 /\ isEmpty t2 then LN else BN t1 t2``,
  REPEAT Cases >> EVAL_TAC);

val mk_BS_thm = prove(
  ``!t1 t2. mk_BS t1 x t2 =
            if isEmpty t1 /\ isEmpty t2 then LS x else BS t1 x t2``,
  REPEAT Cases >> EVAL_TAC);

val oddevenlemma = prove(
  ``2n * y + 1 <> 2 * x + 2``,
  disch_then (mp_tac o AP_TERM ``EVEN``) >>
  simp[EVEN_ADD, EVEN_MULT]);

Theorem size_domain
    `∀ t . size t = CARD (domain t)`
    (Induct_on `t`
    >- rw[size_def, domain_def]
    >- rw[size_def, domain_def]
    >> rw[pred_setTheory.CARD_UNION_EQN, pred_setTheory.CARD_INJ_IMAGE]
    >| [
    `IMAGE (λn. 2 * n + 2) (domain t) ∩ IMAGE (λn. 2 * n + 1) (domain t') = {}`
        by (rw[GSYM pred_setTheory.DISJOINT_DEF, pred_setTheory.IN_DISJOINT]
        >> Cases_on `ODD x`
        >> fs[ODD_EXISTS, ADD1, oddevenlemma]
           )
        >> simp[] ,
    `(({0} ∩ IMAGE (λn. 2 * n + 2) (domain t)) = {}) /\
     (({0} UNION (IMAGE (\n. 2 * n + 2) (domain t)))
          INTER (IMAGE (\n. 2 * n + 1) (domain t')) = {})`
    by (rw[GSYM pred_setTheory.DISJOINT_DEF, pred_setTheory.IN_DISJOINT]
        >> Cases_on `ODD x`
        >> fs[ODD_EXISTS, ADD1, oddevenlemma]
           )
        >> simp[]
    ]
);

Theorem num_set_domain_eq
    `∀ t1 t2:num_set . wf t1 ∧ wf t2 ⇒
        (domain t1 = domain t2 ⇔ t1 = t2)`
    (rw[] >> EQ_TAC >> rw[spt_eq_thm] >> fs[EXTENSION, domain_lookup] >>
    pop_assum (qspec_then `n` mp_tac) >> strip_tac >>
    Cases_on `lookup n t1` >> fs[] >> Cases_on `lookup n t2` >> fs[]
);

Theorem union_num_set_sym
    `∀ t1:num_set t2 . union t1 t2 = union t2 t1`
    (Induct >> fs[union_def] >> rw[] >> CASE_TAC >> fs[union_def]
);

Theorem mk_wf_union
    `∀ t1 t2 . mk_wf (union t1 t2) = union (mk_wf t1) (mk_wf t2)`
    (rw[] >> `wf(union (mk_wf t1) (mk_wf t2)) ∧ wf(mk_wf (union t1 t2))` by
        metis_tac[wf_mk_wf, wf_union] >>
    rw[spt_eq_thm] >> fs[lookup_union, lookup_mk_wf]
);

Theorem domain_difference
    `∀ t1 t2 . domain (difference t1 t2) = (domain t1) DIFF (domain t2)`
    (simp[pred_setTheory.EXTENSION, domain_lookup, lookup_difference] >>
    rw [] >> Cases_on `lookup x t1`
    >- fs[]
    >> fs[] >> Cases_on `lookup x t2`
        >- rw[] >- rw[]
);

Theorem difference_sub
    `(difference a b = LN) ⇒ (domain a ⊆ domain b)`
    (rw[] >>
    `(domain (difference a b) = {})` by rw[domain_def] >>
    fs[EXTENSION, domain_difference, SUBSET_DEF] >>
    metis_tac[]
);

Theorem wf_difference
    `∀ t1 t2 . (wf t1 ∧ wf t2) ⇒ wf (difference t1 t2)`
    (Induct >> rw[difference_def, wf_def] >> CASE_TAC >> fs[wf_def]
    >> rw[wf_def, wf_mk_BN, wf_mk_BS]
);

Theorem delete_fail
    `∀ n t . (wf t) ⇒ (n ∉  domain t ⇔ (delete n t = t))`
    (simp[domain_lookup] >>
    recInduct lookup_ind >>
    rw[lookup_def, wf_def, delete_def, mk_BN_thm, mk_BS_thm]
);

Theorem size_delete
    `∀ n t . (size (delete n t) =
        if (lookup n t = NONE) then (size t) else (size t - 1))`
    (rw[size_def] >>
    fs[lookup_NONE_domain] >>
    TRY (qpat_assum `n NOTIN d` (qspecl_then [] mp_tac)) >>
    rfs[delete_fail, size_def] >>
    fs[lookup_NONE_domain] >>
    fs[size_domain] >>
    fs[lookup_NONE_domain] >>
    fs[size_domain]
);

Theorem lookup_zero
  `∀ n t x. (lookup n t = SOME x) ==> (size t <> 0)`
   (recInduct lookup_ind
   \\ rw[lookup_def]
);

Theorem empty_sub
    `isEmpty(difference a b) ∧ (subspt b a) ==> (domain a = domain b)`
    (fs[subspt_def] >>
    rw[] >>
    imp_res_tac difference_sub >>
    metis_tac[GSYM SUBSET_DEF, SUBSET_ANTISYM]
);

Theorem subspt_delete
    `∀ a b x . subspt a b ⇒ subspt (delete x a) b`
    (rw[subspt_def, lookup_delete]
);

Theorem inter_union_empty
    `∀ a b c . isEmpty (inter (union a b) c)
  ⇔ isEmpty (inter a c) ∧ isEmpty (inter b c)`
    (rw[] >> EQ_TAC >> rw[] >>
    `wf (inter (union a b) c) ∧ wf (inter a c)` by metis_tac[wf_inter] >>
    fs[domain_empty] >> fs[EXTENSION] >> rw[] >>
    pop_assum (qspec_then `x` mp_tac) >> fs[domain_lookup] >>
    rw[] >> fs[lookup_inter, lookup_union] >>
    TRY(first_x_assum (qspec_then `x` mp_tac)) >> rw[] >>
    fs[lookup_inter, lookup_union] >> EVERY_CASE_TAC >> fs[]
);

Theorem inter_insert_empty
    `∀ n t1 t2 . isEmpty (inter (insert n () t1) t2)
  ⇒ n ∉ domain t2 ∧ isEmpty(inter t1 t2)`
    (rw[] >>
    `∀ k . lookup k (inter (insert n () t1) t2) = NONE` by fs[lookup_def]
    >- (fs[domain_lookup] >> rw[] >> fs[lookup_inter] >>
        pop_assum (qspec_then `n` mp_tac) >>
        rw[] >> fs[] >> EVERY_CASE_TAC >> fs[])
    >- (`wf (inter t1 t2)` by metis_tac[wf_inter] >> fs[domain_empty] >>
        fs[EXTENSION] >> rw[] >>
        pop_assum (qspec_then `x` mp_tac) >> rw[] >>
        first_x_assum (qspec_then `x` mp_tac) >> rw[] >>
        fs[domain_lookup, lookup_inter, lookup_insert] >>
        Cases_on `x = n` >> fs[] >>
        Cases_on `lookup n t2` >> fs[] >> CASE_TAC)
);

Theorem fromList2_value
    `∀ e l t n . MEM e l ⇔  ∃ n . lookup n (fromList2 l) = SOME e`
    (rw[lookup_fromList2] >> rw[lookup_fromList] >> fs[MEM_EL] >>
    EQ_TAC >> rw[]
    >- (qexists_tac `n * 2` >> fs[] >> once_rewrite_tac [MULT_COMM] >>
        rw[EVEN_DOUBLE, MULT_DIV])
    >- (qexists_tac `n DIV 2` >> fs[])
);

Theorem wf_spt_fold_tree
    `∀ tree : num_set num_map y : num_set.
        wf tree ∧ (∀ n x . (lookup n tree = SOME x) ⇒ wf x) ∧ wf y
      ⇒ wf(spt_fold union y tree)`
    (Induct >> rw[] >> fs[spt_fold_def]
    >- (fs[wf_def] >> metis_tac[lookup_def, wf_union])
    >> `wf(spt_fold union y tree)` by (
            last_x_assum match_mp_tac >>
            fs[] >> rw[]
            >- fs[wf_def]
            >> last_x_assum match_mp_tac >>
               qexists_tac `2 * n + 2` >>
               fs[lookup_def] >> fs[EVEN_DOUBLE, EVEN_ADD] >>
               once_rewrite_tac[MULT_COMM] >> fs[DIV_MULT])
    >> (last_x_assum match_mp_tac >> fs[] >> rw[]
        >-  fs[wf_def]
        >- (last_x_assum match_mp_tac >>
            qexists_tac `2 * n + 1` >> fs[lookup_def, EVEN_DOUBLE, EVEN_ADD] >>
            once_rewrite_tac[MULT_COMM] >> fs[MULT_DIV])
        >>  `wf a` by (last_x_assum match_mp_tac >>
                qexists_tac `0` >> fs[lookup_def]) >>
            fs[wf_union])
);

Theorem lookup_spt_fold_union
    `∀ tree : num_set num_map y : num_set n : num .
        lookup n (spt_fold union y tree) = SOME ()
      ⇒ lookup n y = SOME () ∨
        ∃ n1 s . lookup n1 tree = SOME s ∧ lookup n s = SOME ()`
    (Induct >> rw[]
    >-  fs[spt_fold_def]
    >-  (fs[spt_fold_def, lookup_union] >> EVERY_CASE_TAC >>
        fs[] >>
        DISJ2_TAC >>
        qexists_tac `0` >> qexists_tac `a` >> fs[lookup_def])
    >- (
        fs[spt_fold_def] >>
        res_tac
        >- (
            res_tac >> fs[]
            >- (
               DISJ2_TAC >>
               fs[lookup_def] >>
               qexists_tac `n1 * 2 + 2` >> qexists_tac `s` >>
               fs[EVEN_DOUBLE, EVEN_ADD] >>
               once_rewrite_tac[MULT_COMM] >>
               fs[DIV_MULT]
               )
            >- (
               DISJ2_TAC >>
               fs[lookup_def] >>
               qexists_tac `n1' * 2 + 2` >> qexists_tac `s'` >>
               fs[EVEN_DOUBLE, EVEN_ADD] >>
               once_rewrite_tac[MULT_COMM] >>
               fs[DIV_MULT]
               )
            )
        >- (
            res_tac >> fs[] >>
            DISJ2_TAC >>
            fs[lookup_def] >>
            qexists_tac `2 * n1 + 1` >> qexists_tac `s` >>
            fs[EVEN_DOUBLE, EVEN_ADD] >>
            once_rewrite_tac[MULT_COMM] >>
            fs[MULT_DIV]
            )
        )
    >- (
        fs[spt_fold_def] >>
        res_tac
        >- (
            fs[lookup_union] >>
            EVERY_CASE_TAC
            >- (
                res_tac >> fs[]
                >- (
                   DISJ2_TAC >>
                   fs[lookup_def] >>
                   qexists_tac `n1 * 2 + 2` >> qexists_tac `s` >>
                   fs[EVEN_DOUBLE, EVEN_ADD] >>
                   once_rewrite_tac[MULT_COMM] >>
                   fs[DIV_MULT]
                   )
                >- (
                   DISJ2_TAC >>
                   fs[lookup_def] >>
                   qexists_tac `n1' * 2 + 2` >> qexists_tac `s'` >>
                   fs[EVEN_DOUBLE, EVEN_ADD] >>
                   once_rewrite_tac[MULT_COMM] >>
                   fs[DIV_MULT]
                   )
                )
            >- (
                DISJ2_TAC >>
                qexists_tac `0` >> qexists_tac `a` >>
                fs[lookup_def]
                )
            )
        >- (
            DISJ2_TAC >>
            fs[lookup_def] >>
            qexists_tac `2 * n1 + 1` >> qexists_tac `s` >>
            fs[EVEN_DOUBLE, EVEN_ADD] >>
            once_rewrite_tac[MULT_COMM] >>
            fs[MULT_DIV]
            )
    )
);

Theorem lookup_spt_fold_union_STRONG
    `∀ tree : num_set num_map y : num_set n : num .
        lookup n (spt_fold union y tree) = SOME ()
      <=> lookup n y = SOME () ∨
        ∃ n1 s . lookup n1 tree = SOME s ∧ lookup n s = SOME ()`
    (Induct >> rw[] >> EQ_TAC >> fs[lookup_spt_fold_union] >> rw[] >>
    fs[spt_fold_def, lookup_def, lookup_union]
    >- (EVERY_CASE_TAC >> fs[])
    >- (EVERY_CASE_TAC >> fs[]
        >- (DISJ1_TAC >> DISJ2_TAC >>
            qexists_tac `(n1 - 1) DIV 2` >> qexists_tac `s` >> fs[])
        >- (DISJ2_TAC >>
            qexists_tac `(n1 - 1) DIV 2` >> qexists_tac `s` >> fs[])
        )
    >- (EVERY_CASE_TAC >> fs[])
    >- (EVERY_CASE_TAC >> fs[]
        >- (rw[] >> fs[NOT_NONE_SOME])
        >- (DISJ1_TAC >> DISJ2_TAC >>
            qexists_tac `(n1 - 1) DIV 2` >> qexists_tac `s` >> fs[])
        >- (DISJ2_TAC >>
            qexists_tac `(n1 - 1) DIV 2` >> qexists_tac `s` >> fs[])
        )
);

Theorem subspt_domain_spt_fold_union
    `∀ t1 : num_set num_map t2 y : num_set .
        subspt t1 t2
      ⇒ domain (spt_fold union y t1) ⊆ domain (spt_fold union y t2)`
    (rw[SUBSET_DEF] >> fs[domain_lookup] >>
    qspecl_then [`t1`, `y`] mp_tac lookup_spt_fold_union_STRONG >>
    qspecl_then [`t2`, `y`] mp_tac lookup_spt_fold_union_STRONG >>
    ntac 2 strip_tac >> res_tac
    >- metis_tac[]
    >> ntac 2 (first_x_assum kall_tac) >>
       `lookup n1 t2 = SOME s` by fs[subspt_def, domain_lookup] >>
       metis_tac[]
);

Theorem domain_spt_fold_union
    `∀ tree : num_set num_map y : num_set .
        (∀ k v . lookup k tree = SOME v ⇒ domain v ⊆ domain tree)
      ⇒ domain (spt_fold union y tree) ⊆ domain y ∪ domain tree`
    (rw[] >> qspec_then `tree` mp_tac lookup_spt_fold_union >>
    rw[] >> fs[SUBSET_DEF, domain_lookup] >> rw[] >> res_tac >> fs[] >>
    metis_tac[]
);

Theorem domain_spt_fold_union_LN
    `∀ tree : num_set num_map  .
        (∀ k v . lookup k tree = SOME v ⇒ domain v ⊆ domain tree)
      ⇔ domain (spt_fold union LN tree) ⊆ domain tree`
    (rw[] >> EQ_TAC >> rw[]
    >- (drule domain_spt_fold_union >>
        strip_tac >> first_x_assum (qspec_then `LN` mp_tac) >> fs[])
    >- (qspec_then `tree` mp_tac lookup_spt_fold_union_STRONG >>
        rw[] >> fs[SUBSET_DEF, domain_lookup, lookup_def] >> rw[] >>
        metis_tac[])
);

(* END TODO *)

(*****************************************************************************)



(**************************** ANALYSIS LEMMAS *****************************)

Theorem is_pure_EVERY_aconv
    `∀ es . EVERY (λ a . is_pure a) es = EVERY is_pure es`
    (Induct >> fs[]
);

Theorem wf_find_loc_wf_find_locL
    `(∀ e locs . find_loc  e = locs ⇒ wf locs) ∧
    (∀ l locs . find_locL l = locs ⇒ wf locs)`
    (ho_match_mp_tac find_loc_ind >> rw[find_loc_def, wf_union] >> rw[wf_def] >>
    Cases_on `dest_GlobalVarInit op` >> fs[wf_insert]
);

Theorem wf_find_locL
    `∀ l . wf(find_locL l)`
    (metis_tac[wf_find_loc_wf_find_locL]
);

Theorem wf_find_loc
    `∀ e . wf(find_loc e)`
    (metis_tac[wf_find_loc_wf_find_locL]
);

Theorem wf_find_lookups_wf_find_lookupsL
    `(∀ e lookups . find_lookups e = lookups ⇒ wf lookups) ∧
    (∀ l lookups . find_lookupsL l = lookups ⇒ wf lookups)`
    (ho_match_mp_tac find_lookups_ind >>
    rw[find_lookups_def, wf_union] >> rw[wf_def] >>
    Cases_on `dest_GlobalVarLookup op` >> fs[wf_insert]
);

Theorem wf_find_lookupsL
    `∀ l . wf(find_lookupsL l)`
    (metis_tac[wf_find_lookups_wf_find_lookupsL]
);

Theorem wf_find_lookups
    `∀ e . wf(find_lookups e)`
    (metis_tac[wf_find_lookups_wf_find_lookupsL]
);

Theorem find_lookupsL_MEM
    `∀ e es . MEM e es ⇒ domain (find_lookups e) ⊆ domain (find_lookupsL es)`
    (Induct_on `es` >> rw[] >> fs[find_lookups_def, domain_union] >>
    res_tac >> fs[SUBSET_DEF]
);

Theorem find_lookupsL_APPEND
    `∀ l1 l2 . find_lookupsL (l1 ++ l2) =
        union (find_lookupsL l1) (find_lookupsL l2)`
    (Induct >> fs[find_lookups_def] >> fs[union_assoc]
);

Theorem find_lookupsL_REVERSE
    `∀ l . find_lookupsL l = find_lookupsL (REVERSE l)`
    (Induct >> fs[find_lookups_def] >>
    fs[find_lookupsL_APPEND, find_lookups_def, union_num_set_sym]
);

Theorem find_loc_EVERY_isEmpty
    `∀ l reachable:num_set .
        EVERY (λ e . isEmpty (inter (find_loc e) reachable)) l
      ⇔ isEmpty (inter (find_locL l) reachable)`
    (Induct >- fs[Once find_loc_def, inter_def]
    >> fs[EVERY_DEF] >> rw[] >> EQ_TAC >> rw[] >>
       qpat_x_assum `isEmpty _` mp_tac >> simp[Once find_loc_def] >>
       fs[inter_union_empty]
);

Theorem wf_analyse_exp
    `∀ e roots tree . analyse_exp e = (roots, tree) ⇒ (wf roots) ∧ (wf tree)`
    (simp[analyse_exp_def] >> rw[] >>
    metis_tac[
        wf_def, wf_map, wf_union, wf_find_loc, wf_find_lookups_wf_find_lookupsL]
);

Theorem analyse_exp_domain
    `∀ e roots tree . analyse_exp e = (roots, tree)
  ⇒ (domain roots ⊆ domain tree)`
    (simp[analyse_exp_def] >> rw[] >> rw[domain_def, domain_map]
);




(**************************** ELIMINATION LEMMAS *****************************)

Theorem keep_Dlet
    `∀ (reachable:num_set) h . ¬ keep reachable h ⇒ ∃ x . h = Dlet x`
   (Cases_on `h` >> rw[keep_def]
);

Theorem num_set_tree_union_empty
    `∀ t1 t2 . isEmpty(num_set_tree_union t1 t2) ⇔ isEmpty t1 ∧ isEmpty t2`
    (Induct >> rw[num_set_tree_union_def] >> CASE_TAC >>
    rw[num_set_tree_union_def]
);

Theorem wf_num_set_tree_union
    `∀ t1 t2 result . wf t1 ∧ wf t2 ∧ num_set_tree_union t1 t2 = result
  ⇒ wf result`
    (Induct >> rw[num_set_tree_union_def, wf_def] >> rw[wf_def] >>
    TRY(CASE_TAC) >>
    rw[wf_def] >>
    TRY(metis_tac[wf_def, num_set_tree_union_empty])
);

Theorem domain_num_set_tree_union
    `∀ t1 t2 . domain (num_set_tree_union t1 t2) = domain t1 ∪ domain t2`
    (Induct >> rw[num_set_tree_union_def, domain_def] >> CASE_TAC >>
    rw[domain_def, domain_union] >> rw[UNION_ASSOC] >> rw[UNION_COMM] >>
    rw[UNION_ASSOC] >> rw[UNION_COMM] >>
    metis_tac[UNION_ASSOC, UNION_COMM, UNION_IDEMPOT]
);

Theorem num_set_tree_union_sym
    `∀ (t1 : num_set num_map) t2 .
        num_set_tree_union t1 t2 = num_set_tree_union t2 t1`
    (Induct >> rw[num_set_tree_union_def] >>
    Cases_on `t2` >> fs[num_set_tree_union_def] >>
    fs[union_num_set_sym]
);

Theorem lookup_domain_num_set_tree_union
    `∀ n (t1:num_set num_map) t2 x . lookup n t1 = SOME x
  ⇒ ∃ y . lookup n (num_set_tree_union t1 t2) = SOME y ∧ domain x ⊆ domain y`
    (Induct_on `t1` >> rw[]
    >- fs[lookup_def]
    >- (fs[lookup_def, num_set_tree_union_def] >> CASE_TAC >>
        fs[lookup_def, domain_union])
    >- (fs[lookup_def, num_set_tree_union_def] >> CASE_TAC >>
        fs[lookup_def, domain_union] >> Cases_on `EVEN n` >> fs[])
    >- (fs[lookup_def, num_set_tree_union_def] >> CASE_TAC >>
        fs[lookup_def, domain_union] >>
        Cases_on `n = 0` >> fs[domain_union] >> Cases_on `EVEN n` >> fs[])
);

Theorem lookup_NONE_num_set_tree_union
    `∀ n (t1:num_set num_map) t2 . lookup n t1 = NONE
    ⇒ lookup n (num_set_tree_union t1 t2) = lookup n t2`
    (Induct_on `t1` >> rw[] >> fs[lookup_def, num_set_tree_union_def] >>
    Cases_on `t2` >> fs[lookup_def] >> Cases_on `n = 0` >> fs[] >>
    Cases_on `EVEN n` >> fs[]
);

Theorem lookup_SOME_SOME_num_set_tree_union
    `∀ n (t1:num_set num_map) x1 t2 x2 .
    lookup n t1 = SOME x1 ∧ lookup n t2 = SOME x2
  ⇒ lookup n (num_set_tree_union t1 t2) = SOME (union x1 x2)`
    (Induct_on `t1` >> rw[] >> fs[lookup_def, num_set_tree_union_def] >>
    Cases_on `t2` >> fs[lookup_def] >>
    Cases_on `EVEN n` >> fs[] >>
    Cases_on `n = 0` >> fs[]
);

Theorem lookup_num_set_tree_union
    `∀ (t1 : num_set num_map) t2 n .
        lookup n (num_set_tree_union t1 t2) = case (lookup n t1) of
            | NONE => lookup n t2
            | SOME s1 => case (lookup n t2) of
                | NONE => SOME s1
                | SOME s2 => SOME (union s1 s2)`
    (rw[] >> Cases_on `lookup n t1` >> fs[]
    >-  fs[lookup_NONE_num_set_tree_union]
    >- (Cases_on `lookup n t2` >> fs[]
        >- (fs[lookup_NONE_num_set_tree_union, num_set_tree_union_sym] >>
            imp_res_tac lookup_NONE_num_set_tree_union >>
            pop_assum (qspec_then `t1` mp_tac) >> rw[] >>
            fs[num_set_tree_union_sym])
        >-  fs[lookup_SOME_SOME_num_set_tree_union])
);

Theorem wf_code_analysis_union
    `∀ r3 r2 r1 t1 t2 t3. wf r1 ∧ wf r2
        ∧ code_analysis_union (r1, t1) (r2, t2) = (r3, t3) ⇒  wf r3`
    (rw[code_analysis_union_def] >> rw[wf_union]
);

Theorem wf_code_analysis_union_strong
    `∀ r3:num_set r2 r1 (t1:num_set num_map) t2 t3.
        wf r1 ∧ wf r2 ∧ wf t1 ∧ wf t2 ∧
        code_analysis_union (r1, t1) (r2, t2) = (r3, t3) ⇒  wf r3 ∧ wf t3`
    (rw[code_analysis_union_def] >> rw[wf_union] >>
    imp_res_tac wf_num_set_tree_union >> fs[]
);

Theorem domain_code_analysis_union
    `∀ r1:num_set r2 r3 (t1:num_set num_map) t2 t3 .
    domain r1 ⊆ domain t1 ∧ domain r2 ⊆ domain t2 ∧
    code_analysis_union (r1, t1) (r2, t2) = (r3, t3) ⇒ domain r3 ⊆ domain t3`
    (rw[code_analysis_union_def] >> rw[domain_union] >>
    rw[domain_num_set_tree_union] >> fs[SUBSET_DEF]
);

Theorem wf_code_analysis_union
    `∀ r3 r2 r1 t1 t2 t3. wf r1 ∧ wf r2
        ∧ code_analysis_union (r1, t1) (r2, t2) = (r3, t3) ⇒  wf r3`
    (rw[code_analysis_union_def] >> rw[wf_union]
);

Theorem wf_code_analysis_union_strong
    `∀ r3:num_set r2 r1 (t1:num_set num_map) t2 t3.
        wf r1 ∧ wf r2 ∧ wf t1 ∧ wf t2 ∧
        code_analysis_union (r1, t1) (r2, t2) = (r3, t3) ⇒  wf r3 ∧ wf t3`
    (rw[code_analysis_union_def] >> rw[wf_union] >>
    imp_res_tac wf_num_set_tree_union >> fs[]
);

Theorem domain_code_analysis_union
    `∀ r1:num_set r2 r3 (t1:num_set num_map) t2 t3 .
    domain r1 ⊆ domain t1 ∧ domain r2 ⊆ domain t2 ∧
    code_analysis_union (r1, t1) (r2, t2) = (r3, t3) ⇒ domain r3 ⊆ domain t3`
    (rw[code_analysis_union_def] >> rw[domain_union] >>
    rw[domain_num_set_tree_union] >> fs[SUBSET_DEF]
);

Theorem analyse_code_thm
    `∀ code root tree . analyse_code code = (root, tree)
    ⇒ (wf root) ∧ (domain root ⊆ domain tree)`
    (Induct
    >-(rw[analyse_code_def] >> rw[wf_def])
    >> Cases_on `h` >> simp[analyse_code_def] >> Cases_on `analyse_exp e` >>
       Cases_on `analyse_code code` >>
       first_x_assum (qspecl_then [`q'`, `r'`] mp_tac) >> simp[] >>
       qspecl_then [`e`, `q`, `r`] mp_tac wf_analyse_exp >> simp[] >> rw[]
       >- imp_res_tac wf_code_analysis_union
       >> qspecl_then [`e`, `q`, `r`] mp_tac analyse_exp_domain >> rw[] >>
          imp_res_tac domain_code_analysis_union
);



(**************************** REACHABILITY LEMMAS *****************************)

Theorem subspt_superdomain
    `∀ t1 a t2 . subspt (superdomain t1) (superdomain (BS t1 a t2)) ∧
                 subspt (superdomain t2) (superdomain (BS t1 a t2)) ∧
                 subspt a (superdomain (BS t1 a t2)) ∧
                 subspt (superdomain t1) (superdomain (BN t1 t2)) ∧
                 subspt (superdomain t2) (superdomain (BN t1 t2))`
    (rw[subspt_domain, superdomain_def, domain_union, SUBSET_DEF]
);

Theorem superdomain_thm
    `∀ x y (tree:num_set num_map) . lookup x tree = SOME y
  ⇒ domain y ⊆ domain (superdomain tree)`
    (Induct_on `tree` >- rw[lookup_def]
    >- rw[lookup_def, superdomain_def, foldi_def, domain_map]
    >> rw[] >> fs[lookup_def] >> Cases_on `EVEN x` >> res_tac >>
       qspecl_then [`tree`, `a`, `tree'`] mp_tac subspt_superdomain >>
       Cases_on `x = 0` >> fs[subspt_domain] >> metis_tac[SUBSET_TRANS]
);

Theorem superdomain_inverse_thm
    `∀ n tree . n ∈ domain (superdomain tree)
    ⇒ ∃ k aSet . lookup k tree = SOME aSet ∧ n ∈ domain aSet`
    (Induct_on `tree` >> rw[superdomain_def] >>
    fs[lookup_def, domain_union] >> res_tac
    >- (qexists_tac `2 * k + 2` >> fs[EVEN_DOUBLE, EVEN_ADD] >>
        once_rewrite_tac[MULT_COMM] >> fs[DIV_MULT])
    >- (qexists_tac `2 * k + 1` >> fs[EVEN_DOUBLE, EVEN_ADD] >>
        once_rewrite_tac[MULT_COMM] >> fs[MULT_DIV])
    >- (qexists_tac `2 * k + 2` >> fs[EVEN_DOUBLE, EVEN_ADD] >>
        once_rewrite_tac[MULT_COMM] >> fs[DIV_MULT])
    >- (qexists_tac `0` >> fs[])
    >- (qexists_tac `2 * k + 1` >> fs[EVEN_DOUBLE, EVEN_ADD] >>
        once_rewrite_tac[MULT_COMM] >> fs[MULT_DIV])
);

Theorem superdomain_not_in_thm
    `∀ n tree . n ∉ domain (superdomain tree)
  ⇒ ∀ k aSet . lookup k tree = SOME aSet ⇒ n ∉ domain aSet`
    (Induct_on `tree` >> rw[superdomain_def] >> fs[lookup_def, domain_union] >>
    res_tac >> Cases_on `k = 0` >> Cases_on `EVEN k` >> fs[] >> metis_tac[]
);

val wf_set_tree_def = Define `
    wf_set_tree tree ⇔
        (∀ x  y . (lookup x tree = SOME y) ⇒ domain y ⊆ domain tree) ∧
        (∀ n x . lookup n tree = SOME x ⇒ wf x) ∧
        wf tree
`

Theorem mk_wf_set_tree_domain
    `∀ tree . domain tree ⊆ domain (mk_wf_set_tree tree)`
    (Induct >>
    rw[mk_wf_set_tree_def, domain_map, domain_mk_wf, domain_union, SUBSET_DEF]
);

Theorem mk_wf_set_tree_thm
    `∀ x tree . x = mk_wf_set_tree tree ⇒ wf_set_tree x`
    (rw[mk_wf_set_tree_def, wf_set_tree_def] >> fs[lookup_map] >>
    rw[domain_map, domain_union] >> fs[lookup_union] >>
    Cases_on `lookup x' tree` >> fs[] >- fs[lookup_map] >> rw[] >>
    qspecl_then [`x'`, `x`, `tree`] mp_tac superdomain_thm >> rw[SUBSET_DEF]
);

Theorem lookup_mk_wf_set_tree
    `∀ n tree x . lookup n tree = SOME x
  ⇒ ∃ y . lookup n (mk_wf_set_tree tree) = SOME y ∧ domain x = domain y`
    (rw[mk_wf_set_tree_def] >> rw[lookup_map] >> rw[lookup_union]
);

Theorem lookup_domain_mk_wf_set_tree
    `∀ n t x y . lookup n (mk_wf_set_tree t) = SOME x ⇒
        lookup n t = SOME y ⇒ domain y = domain x`
    (rw[mk_wf_set_tree_def] >> fs[lookup_map, lookup_union] >>
    metis_tac[domain_mk_wf]
);

Theorem wf_close_spt
    `∀ reachable seen tree. (wf reachable) ∧ (wf seen) ∧ (wf tree) ∧
        (∀ n x . (lookup n tree = SOME x) ⇒ wf x)
  ⇒ wf (close_spt reachable seen tree)`
    (recInduct close_spt_ind >> rw[] >>
    once_rewrite_tac [close_spt_def] >> rw[] >>
    fs[] >>
    last_x_assum match_mp_tac >>
    reverse(rw[]) >> fs[wf_union, wf_difference]
    >-  metis_tac[]
    >>  match_mp_tac wf_union >>
        fs[] >>
        match_mp_tac wf_spt_fold_tree >>
        fs[wf_def] >>
        fs[lookup_inter] >>
        rw[] >> EVERY_CASE_TAC >> fs[] >> rveq >>
        metis_tac[]
);



(**************************** OTHER LEMMAS *****************************)

Theorem domain_superdomain_num_set_tree_union
    `∀ t1 t2 . domain (superdomain t1)
        ⊆ domain (superdomain (num_set_tree_union t1 t2))`
    (fs[SUBSET_DEF] >> rw[] >> imp_res_tac superdomain_inverse_thm >>
    imp_res_tac lookup_domain_num_set_tree_union >>
    pop_assum (qspec_then `t2` mp_tac) >>
    rw[] >> imp_res_tac superdomain_thm >> metis_tac[SUBSET_DEF]
);

Theorem domain_superdomain_num_set_tree_union_STRONG
    `∀ t1 t2 . domain (superdomain t1) ∪ domain (superdomain t2) =
        domain (superdomain (num_set_tree_union t1 t2))`
    (fs[EXTENSION] >> rw[] >> EQ_TAC >> rw[]
    >- metis_tac[domain_superdomain_num_set_tree_union,
                 SUBSET_DEF, num_set_tree_union_sym]
    >- metis_tac[domain_superdomain_num_set_tree_union,
                 SUBSET_DEF, num_set_tree_union_sym]
    >- (imp_res_tac superdomain_inverse_thm >> fs[lookup_num_set_tree_union] >>
        EVERY_CASE_TAC >> fs[]
        >- (disj1_tac >> imp_res_tac superdomain_thm >> fs[SUBSET_DEF])
        >- (disj2_tac >> imp_res_tac superdomain_thm >> fs[SUBSET_DEF])
        >- (rveq >> imp_res_tac superdomain_thm >>
            fs[SUBSET_DEF, domain_union])
       )
);

Theorem mk_wf_set_tree_num_set_tree_union
    `∀ t1 t2 . mk_wf_set_tree (num_set_tree_union t1 t2) =
        num_set_tree_union (mk_wf_set_tree t1) (mk_wf_set_tree t2)`
    (rw[] >>
    `wf (mk_wf_set_tree (num_set_tree_union t1 t2))`
        by metis_tac[mk_wf_set_tree_thm, wf_set_tree_def] >>
    `wf (num_set_tree_union (mk_wf_set_tree t1) (mk_wf_set_tree t2))` by
        metis_tac[mk_wf_set_tree_thm, wf_set_tree_def,
                  wf_num_set_tree_union] >>
    rw[spt_eq_thm] >> simp[mk_wf_set_tree_def] >> fs[lookup_map] >>
    fs[lookup_union] >> fs[lookup_map] >>
    fs[lookup_num_set_tree_union] >> fs[lookup_map] >>
    fs[lookup_union] >> fs[lookup_map] >>
    fs[OPTION_MAP_COMPOSE, mk_wf_def] >> Cases_on `lookup n t1` >>
    Cases_on `lookup n t2` >> fs[] >>
    EVERY_CASE_TAC >> fs[mk_wf_def, union_def] >>
    fs[lookup_NONE_domain, GSYM domain_lookup] >>
    qspecl_then [`t1`, `t2`] mp_tac
        domain_superdomain_num_set_tree_union_STRONG >>
    strip_tac >> fs[EXTENSION]
    >-  metis_tac[]
    >- (qsuff_tac `n ∈ domain (superdomain (num_set_tree_union t1 t2))`
        >- rw[domain_lookup]
        >> imp_res_tac domain_lookup >> metis_tac[])
    >- (qsuff_tac `n ∈ domain (superdomain (num_set_tree_union t1 t2))`
        >- rw[domain_lookup]
        >> imp_res_tac domain_lookup >> metis_tac[])
    >- (qsuff_tac `n ∈ domain (superdomain (num_set_tree_union t1 t2))`
        >- rw[domain_lookup]
        >> imp_res_tac domain_lookup >> metis_tac[])
    >-  metis_tac[mk_wf_union]
);



(************************** ADJACENCY/REACHABILITY ***************************)

val is_adjacent_def = Define `
    is_adjacent tree x y =
    ∃ aSetx aSety.
        ( lookup x tree = SOME aSetx ) ∧ ( lookup y aSetx = SOME () ) ∧
        ( lookup y tree = SOME aSety )
`;

Theorem adjacent_domain
    `∀ tree x y . is_adjacent tree x y ⇒ x ∈ domain tree ∧ y ∈ domain tree`
    (rw[is_adjacent_def] >> rw[domain_lookup]
);

val is_reachable_def = Define `
    is_reachable tree = RTC (is_adjacent tree)
`;

Theorem reachable_domain
    `∀ tree x y . is_reachable tree x y
  ⇒ (x = y ∨ (x ∈ domain tree ∧ y ∈ domain tree))`
    (simp[is_reachable_def] >> strip_tac >> ho_match_mp_tac RTC_INDUCT_RIGHT1 >>
    metis_tac[adjacent_domain]
);

Theorem rtc_is_adjacent
    `s ⊆ t ∧ (∀ k . k ∈ t ⇒ ∀ n . (is_adjacent fullTree k n ⇒ n ∈ t)) ⇒
    ∀ x y . RTC(is_adjacent fullTree) x y ⇒ x ∈ s ⇒ y ∈ t`
    (strip_tac >>
    ho_match_mp_tac RTC_INDUCT_RIGHT1 >>
    fs[SUBSET_DEF] >>
    metis_tac []
);

Theorem is_adjacent_num_set_tree_union
    `∀ t1 t2 n m .
        is_adjacent t1 n m ⇒ is_adjacent (num_set_tree_union t1 t2) n m`
    (rw[is_adjacent_def] >> imp_res_tac lookup_domain_num_set_tree_union >>
    first_x_assum (qspec_then `t2` mp_tac) >> rw[] >>
    first_x_assum (qspec_then `t2` mp_tac) >> rw[] >>
    fs[SUBSET_DEF, domain_lookup]
);

Theorem is_adjacent_wf_set_tree_num_set_tree_union
    `∀ t1 t2 n m .
        is_adjacent (mk_wf_set_tree t1) n m
        ⇒ is_adjacent (mk_wf_set_tree (num_set_tree_union t1 t2)) n m`
    (rw[is_adjacent_def] >> fs[mk_wf_set_tree_def] >> fs[lookup_map] >>
    fs[lookup_union] >> fs[lookup_map] >> fs[PULL_EXISTS] >>
    fs[lookup_num_set_tree_union] >>
    Cases_on `lookup n t1` >> fs[] >> Cases_on `lookup n t2` >> fs[] >>
    rveq >> fs[lookup_def, mk_wf_def, lookup_union] >>
    EVERY_CASE_TAC >> fs[] >>
    qspecl_then [`t1`, `t2`] mp_tac domain_superdomain_num_set_tree_union >>
    rw[SUBSET_DEF, domain_lookup]
);

Theorem is_reachable_wf_set_tree_num_set_tree_union
    `∀ t1 t2 n m .
        is_reachable (mk_wf_set_tree t1) n m
      ⇒ is_reachable (mk_wf_set_tree (num_set_tree_union t1 t2)) n m`
    (simp[is_reachable_def] >> strip_tac >> strip_tac >>
    ho_match_mp_tac RTC_INDUCT_RIGHT1 >> rw[] >>
    simp[Once RTC_CASES2] >> disj2_tac >> qexists_tac `m` >> fs[] >>
    imp_res_tac is_adjacent_wf_set_tree_num_set_tree_union >> fs[]
);



(************************** DEFINITIONS ***************************)

Theorem exp_size_map_snd
    `∀ vvs . v3_size (MAP SND vvs) ≤ v1_size vvs`
    (Induct >> rw[v_size_def] >>
    Cases_on `v3_size (MAP SND vvs) = v1_size vvs` >>
    `v_size (SND h) ≤ v2_size h` by (Cases_on `h` >> rw[v_size_def]) >> rw[]
);

val find_v_globals_def = tDefine "find_v_globals" `
    (find_v_globals (Conv _ vl) = (find_v_globalsL vl):num_set) ∧
    (find_v_globals (Closure vvs _ e) =
        union (find_v_globalsL (MAP SND vvs)) (find_lookups e)) ∧
    (find_v_globals (Recclosure vvs vves _) =
        union (find_v_globalsL (MAP SND vvs))
            (find_lookupsL (MAP (SND o SND) vves))) ∧
    (find_v_globals (Vectorv vl) = find_v_globalsL vl) ∧
    (find_v_globals _ = LN) ∧
    (find_v_globalsL [] = LN) ∧
    (find_v_globalsL (h::t) = union (find_v_globals h) (find_v_globalsL t))
`
(
    WF_REL_TAC `measure (λ e . case e of
            | INL x => v_size x
            | INR y => v3_size y)` >>
    rw[v_size_def] >> qspec_then `vvs` mp_tac v_size_map_snd >>
    Cases_on `v3_size(MAP SND vvs) = v1_size vvs` >> rw[]
);

val find_v_globals_ind = theorem "find_v_globals_ind";

Theorem find_v_globalsL_APPEND
    `∀ l1 l2 . find_v_globalsL (l1 ++ l2) =
        union (find_v_globalsL l1) (find_v_globalsL l2)`
    (Induct >> fs[find_v_globals_def] >> fs[union_assoc]
);

Theorem find_v_globalsL_REVERSE
    `∀ l . find_v_globalsL l = find_v_globalsL (REVERSE l)`
    (Induct >> fs[find_v_globals_def] >>
    fs[find_v_globalsL_APPEND, union_num_set_sym, find_v_globals_def]
);

Theorem find_v_globalsL_MEM
    `∀ k v vs . MEM (k, v) vs
  ⇒ domain (find_v_globals v) ⊆ domain (find_v_globalsL (MAP SND vs))`
    (Induct_on `vs` >> rw[] >> fs[find_v_globals_def, domain_union] >>
    res_tac >> fs[SUBSET_DEF]
);

Theorem find_v_globalsL_EL
    `∀ n vs . n < LENGTH vs ⇒
    domain (find_v_globals (EL n vs)) ⊆ domain(find_v_globalsL vs)`
    (Induct >> fs[EL] >> rw[] >> Cases_on `vs` >>
    fs[find_v_globals_def, domain_union] >>
    Cases_on `n = 0` >> fs[] >>  fs[EXTENSION, SUBSET_DEF]
);

Theorem find_v_globals_MAP_Recclosure
    `∀ (funs:(tvarN,tvarN # flatLang$exp) alist) v l .
        domain (find_v_globalsL (MAP (λ (f,x,e). Recclosure v l f) funs)) ⊆
            domain (find_v_globalsL (MAP SND v)) ∪
            domain (find_lookupsL (MAP (SND o SND) l))`
    (Induct >> fs[find_v_globals_def] >> rw[domain_union] >>
    PairCases_on `h` >> fs[find_v_globals_def, domain_union]
);

Theorem find_v_globalsL_REPLICATE
    `∀ n v vs . domain (find_v_globalsL (REPLICATE n v)) ⊆
        domain (find_v_globals v)`
    (Induct >> fs[REPLICATE, find_v_globals_def, domain_union]
);

Theorem find_v_globalsL_LUPDATE
    `∀ n vs (reachable:num_set) v . n < LENGTH vs ∧
    domain (find_v_globalsL vs) ⊆ domain reachable ∧
    domain (find_v_globals v) ⊆ domain reachable
  ⇒ domain (find_v_globalsL (LUPDATE v n vs)) ⊆ domain reachable`
    (Induct_on `vs` >> rw[] >> Cases_on `n` >> fs[LUPDATE_def] >>
    fs[find_v_globals_def, domain_union]
);

Theorem find_v_globals_v_to_list
    `∀ x reachable xs .
        domain (find_v_globals x) ⊆ domain reachable ∧ v_to_list x = SOME xs
    ⇒ domain (find_v_globalsL xs) ⊆ domain reachable`
    (recInduct v_to_list_ind >>
    fs[v_to_list_def, find_v_globals_def, domain_union] >> rw[] >>
    Cases_on `v_to_list v2` >> fs[] >> rveq >>
    fs[find_v_globals_def, domain_union] >> metis_tac[]
);

Theorem find_v_globals_list_to_v
    `∀ xs reachable x .
        domain (find_v_globalsL xs) ⊆ domain reachable ∧ list_to_v xs = x
    ⇒ domain (find_v_globals x) ⊆ domain reachable`
    (Induct >> fs[list_to_v_def, find_v_globals_def, domain_union]
);

val find_refs_globals_def = Define `
    (find_refs_globals (Refv a::t) =
        union (find_v_globals a) (find_refs_globals t)) ∧
    (find_refs_globals (Varray l::t) =
        union (find_v_globalsL l) (find_refs_globals t)) ∧
    (find_refs_globals (_::t) = find_refs_globals t) ∧
    (find_refs_globals [] = LN)
`

val find_refs_globals_ind = theorem "find_refs_globals_ind";

Theorem find_refs_globals_EL
    `∀ n l . n < LENGTH l ⇒
        (∀ a . EL n l = Refv a
            ⇒ domain (find_v_globals a) ⊆ domain (find_refs_globals l)) ∧
        (∀ vs . EL n l = Varray vs
            ⇒ domain (find_v_globalsL vs) ⊆ domain (find_refs_globals l))`
    (Induct >> rw[]
    >- (Cases_on `l` >> fs[find_refs_globals_def, domain_union])
    >- (Cases_on `l` >> fs[find_refs_globals_def, domain_union])
    >> fs[EL] >> first_x_assum (qspec_then `TL l` mp_tac) >> rw[] >>
       `n < LENGTH (TL l)` by fs[LENGTH_TL] >> fs[] >>
       Cases_on `l` >> fs[] >>
       Cases_on `h` >> fs[find_refs_globals_def, domain_union, SUBSET_DEF]
);

Theorem find_refs_globals_MEM
    `∀ refs reachable:num_set .
        domain (find_refs_globals refs) ⊆ domain reachable
      ⇒ (∀ a . MEM (Refv a) refs
            ⇒ domain (find_v_globals a) ⊆ domain reachable) ∧
        (∀ vs . MEM (Varray vs) refs
            ⇒ domain (find_v_globalsL vs) ⊆ domain reachable)`
    (Induct >> rw[] >> fs[find_refs_globals_def, domain_union] >>
    Cases_on `h` >> fs[find_refs_globals_def, domain_union]
);

Theorem find_refs_globals_LUPDATE
    `∀ reachable:num_set refs n .
        n < LENGTH refs ∧ domain (find_refs_globals refs) ⊆ domain reachable
      ⇒
        (∀ a . domain (find_v_globals a) ⊆ domain reachable
            ⇒ domain (find_refs_globals (LUPDATE (Refv a) n refs))
                ⊆ domain reachable) ∧
    (∀ vs . domain (find_v_globalsL vs) ⊆ domain reachable
        ⇒ domain (find_refs_globals (LUPDATE (Varray vs) n  refs))
            ⊆ domain reachable) ∧
    (∀ ws. domain (find_refs_globals (LUPDATE (W8array ws) n refs))
        ⊆ domain reachable)`
    (Induct_on `refs` >> rw[] >> Cases_on `h` >>
    fs[find_refs_globals_def, domain_union] >>
    Cases_on `n = 0` >> fs[LUPDATE_def, find_refs_globals_def, domain_union] >>
    fs[domain_union, LUPDATE_def] >> Cases_on `n` >> fs[] >>
    fs[LUPDATE_def, find_refs_globals_def, domain_union]
);

Theorem find_refs_globals_APPEND
    `∀ refs new . find_refs_globals (refs ++ new) =
        union (find_refs_globals refs) (find_refs_globals new)`
    (Induct >> rw[] >> fs[find_refs_globals_def] >>
    Cases_on `h` >> fs[find_refs_globals_def] >> fs[union_assoc]

);

val find_env_globals_def = Define `
    find_env_globals env = find_v_globalsL (MAP SND env.v)
`

val find_result_globals_def = Define `
    (find_result_globals (SOME (Rraise v)) = find_v_globals v) ∧
    (find_result_globals _ = LN)
`

val find_result_globals_ind = theorem "find_result_globals_ind";

val find_sem_prim_res_globals_def = Define `
    (find_sem_prim_res_globals (Rerr e :
        (flatSem$v list, flatSem$v) semanticPrimitives$result) =
        find_result_globals (SOME e)) ∧
    (find_sem_prim_res_globals (Rval e) = find_v_globalsL e)
`

(* s = state, t = removed state *)
val globals_rel_def = Define `
    globals_rel
        (reachable : num_set) (s : 'a flatSem$state) (t : 'a flatSem$state) ⇔
        LENGTH s.globals = LENGTH t.globals ∧
        (∀ n . n ∈ domain reachable ∧ n < LENGTH t.globals
        ⇒ EL n s.globals = EL n t.globals) ∧
        (∀ n x . n < LENGTH t.globals ∧ EL n t.globals = SOME x
            ⇒ EL n s.globals = SOME x) ∧
        (∀ n . n < LENGTH t.globals ∧ EL n s.globals = NONE
            ⇒ EL n t.globals = NONE) ∧
        (∀ n x . n ∈ domain reachable ∧ n < LENGTH t.globals ∧
            EL n t.globals = SOME x
          ⇒ domain (find_v_globals x) ⊆ domain reachable)
`

Theorem globals_rel_trans
    `∀ reachable s1 s2 s3 .
        globals_rel reachable s1 s2 ∧ globals_rel reachable s2 s3
        ⇒ globals_rel reachable s1 s3`
    (rw[globals_rel_def]
);

val decs_closed_def = Define `
    decs_closed (reachable : num_set) decs ⇔  ∀ r t . analyse_code decs = (r,t)
    ⇒ domain r ⊆ domain reachable ∧
      (∀ n m . n ∈ domain reachable ∧ is_reachable (mk_wf_set_tree t) n m
      ⇒ m ∈ domain reachable)
`

Theorem decs_closed_reduce
    `∀ reachable h t . decs_closed reachable (h::t) ⇒ decs_closed reachable t`
    (fs[decs_closed_def] >> rw[] >> Cases_on `h` >> fs[analyse_code_def]
    >- (Cases_on `analyse_exp e` >> fs[code_analysis_union_def, domain_union])
    >- (Cases_on `analyse_exp e` >> fs[code_analysis_union_def, domain_union] >>
        first_x_assum drule >> rw[] >> pop_assum match_mp_tac >>
        assume_tac is_reachable_wf_set_tree_num_set_tree_union >> fs[] >>
        fs[Once num_set_tree_union_sym])
    >> metis_tac[]
);

Theorem decs_closed_reduce_HD
    `∀ reachable h t .
        decs_closed reachable (h::t) ⇒ decs_closed reachable [h]`
    (fs[decs_closed_def] >> rw[] >> Cases_on `h` >> fs[analyse_code_def] >>
    Cases_on `analyse_exp e` >>
    fs[code_analysis_union_def, domain_union] >> rveq >> fs[domain_def]
    >- (Cases_on `analyse_code t` >> fs[code_analysis_union_def, domain_union])
    >- (fs[Once num_set_tree_union_sym, num_set_tree_union_def] >>
        Cases_on `analyse_code t` >>
        fs[code_analysis_union_def, domain_union] >>
        imp_res_tac is_reachable_wf_set_tree_num_set_tree_union >>
        pop_assum (qspec_then `r` mp_tac) >> strip_tac >> res_tac)
    >- (fs[EVAL ``mk_wf_set_tree LN``] >>
        imp_res_tac reachable_domain >> fs[domain_def])
    >- (fs[EVAL ``mk_wf_set_tree LN``] >>
        imp_res_tac reachable_domain >> fs[domain_def])
);

(* s = state, t = removed state *)
val flat_state_rel_def = Define `
    flat_state_rel reachable s t ⇔ s.clock = t.clock ∧ s.refs = t.refs ∧
    s.ffi = t.ffi ∧ globals_rel reachable s t ∧
    domain (find_refs_globals s.refs) ⊆ domain reachable
`

Theorem flat_state_rel_trans
    `∀ reachable s1 s2 s3 . flat_state_rel reachable s1 s2 ∧
        flat_state_rel reachable s2 s3
    ⇒ flat_state_rel reachable s1 s3`
    (rw[flat_state_rel_def, globals_rel_def]
);

(**************************** FLATLANG LEMMAS *****************************)

Theorem pmatch_Match_reachable
    `(∀ env refs p v l a reachable:num_set . pmatch env refs p v l = Match a ∧
        domain (find_v_globalsL (MAP SND env.v)) ⊆ domain reachable ∧
        domain (find_v_globals v) ⊆ domain reachable ∧
        domain (find_v_globalsL (MAP SND l)) ⊆ domain reachable ∧
        domain (find_refs_globals refs) ⊆ domain reachable
    ⇒ domain (find_v_globalsL (MAP SND a)) ⊆ domain reachable)
  ∧
    (∀ env refs p vs l a reachable:num_set .
        pmatch_list env refs p vs l = Match a ∧
        domain (find_v_globalsL (MAP SND env.v)) ⊆ domain reachable ∧
        domain (find_v_globalsL vs) ⊆ domain reachable ∧
        domain (find_v_globalsL (MAP SND l)) ⊆ domain reachable ∧
        domain (find_refs_globals refs) ⊆ domain reachable
    ⇒ domain (find_v_globalsL (MAP SND a)) ⊆ domain reachable)`
    (ho_match_mp_tac pmatch_ind >> rw[pmatch_def] >>
    fs[find_v_globals_def, domain_union]
    >- (Cases_on `store_lookup lnum refs` >> fs[] >> Cases_on `x` >> fs[] >>
        fs[semanticPrimitivesTheory.store_lookup_def] >>
        first_x_assum (qspec_then `reachable` match_mp_tac) >> rw[] >>
        imp_res_tac find_refs_globals_EL >> metis_tac[SUBSET_TRANS])
    >- (Cases_on `pmatch env refs p v l` >> fs[domain_union])
);


Theorem find_v_globals_list_to_v_APPEND
    `∀ xs reachable ys .
        domain (find_v_globalsL xs) ⊆ domain reachable ∧
        domain(find_v_globalsL ys) ⊆ domain reachable
    ⇒ domain (find_v_globals (list_to_v (xs ++ ys))) ⊆ domain reachable`
    (Induct >> fs[list_to_v_def, find_v_globals_def, domain_union] >>
    metis_tac[find_v_globals_list_to_v]
);

Theorem find_v_globals_Unitv[simp]
  `find_v_globals (Unitv cc) = LN`
  (EVAL_TAC);

Theorem do_app_SOME_flat_state_rel
    `∀ reachable state removed_state op l new_state result new_removed_state.
        flat_state_rel reachable state removed_state ∧ op ≠ Opapp ∧
        domain(find_v_globalsL l) ⊆ domain reachable ∧
        domain (find_lookups (App tra op [])) ⊆ domain reachable
          ⇒ do_app cc state op l = SOME (new_state, result) ∧
            result ≠ Rerr (Rabort Rtype_error)
            ⇒ ∃ new_removed_state .
                flat_state_rel reachable new_state new_removed_state ∧
                do_app cc removed_state op l =
                    SOME (new_removed_state, result) ∧
                domain (find_sem_prim_res_globals (list_result result)) ⊆
                    domain reachable`

    (rw[] >> qpat_x_assum `flat_state_rel _ _ _` mp_tac >>
    simp[Once flat_state_rel_def] >> strip_tac >>
    `∃ this_case . this_case op` by (qexists_tac `K T` >> simp[]) >>
    reverse (Cases_on `op`) >> fs[]
    >- (fs[do_app_def] >> Cases_on `l` >> fs[find_v_globals_def] >>
        rveq >> fs[flat_state_rel_def] >>
        fs[find_lookups_def, dest_GlobalVarLookup_def] >>
        fs[find_sem_prim_res_globals_def] >>
        Cases_on `EL n new_state.globals` >> fs[] >> res_tac >>
        Cases_on `EL n removed_state.globals` >> fs[find_v_globals_def] >>
        fs[globals_rel_def] >> res_tac >> fs[] >> rveq >> metis_tac[])
    >- (fs[do_app_def] >> Cases_on `l` >> fs[find_v_globals_def] >>
        Cases_on `t` >> fs[] >>
        rveq >> fs[flat_state_rel_def, globals_rel_def] >> rfs[] >>
        fs[EL_LUPDATE] >> rw[] >>
        fs[find_sem_prim_res_globals_def, find_v_globals_def] >>
        metis_tac[]) >>
    fs[do_app_cases] >> rveq >> fs[] >> rw[] >>
    fs[find_sem_prim_res_globals_def, find_v_globals_def,
        find_result_globals_def] >>
    fs[semanticPrimitivesTheory.store_assign_def,
       semanticPrimitivesTheory.store_v_same_type_def, subscript_exn_v_def] >>
    fs[semanticPrimitivesTheory.store_alloc_def,
       semanticPrimitivesTheory.store_lookup_def,
       chr_exn_v_def, Boolv_def, div_exn_v_def] >>
    fs[flat_state_rel_def, find_v_globals_def,
       domain_union, find_refs_globals_def] >> rveq >> rfs[globals_rel_def]
    (* 21 subgoals *)
    >- (rw[] >> Cases_on `n' < LENGTH removed_state.globals` >> rveq >> fs[]
        >- fs[EL_APPEND1] >- fs[EL_APPEND2] >- fs[EL_APPEND1] >- fs[EL_APPEND2]
        >- metis_tac[EL_APPEND1]
        >- (fs[EL_APPEND2] >>
            `n' - LENGTH removed_state.globals < n` by fs[] >>
            metis_tac[EL_REPLICATE])
        >- (fs[EL_APPEND1] >> metis_tac[])
        >- (fs[EL_APPEND2] >>
            `n' - LENGTH removed_state.globals < n` by fs[] >>
            fs[EL_REPLICATE]))
    >-  metis_tac[find_refs_globals_LUPDATE]
    >-  metis_tac[find_v_globals_v_to_list, find_v_globals_list_to_v_APPEND]
    >- (qsuff_tac
        `domain (find_v_globalsL (LUPDATE v'''''' (Num (ABS i''''''')) vs))
            ⊆ domain reachable`
        >-  metis_tac[find_refs_globals_LUPDATE]
        >>  match_mp_tac find_v_globalsL_LUPDATE >> fs[] >>
            imp_res_tac EL_MEM >> rfs[] >>
            fs[find_refs_globals_def] >> metis_tac[find_refs_globals_MEM])
    >- (qexists_tac `removed_state` >> fs[] >> fs[])
    >- (imp_res_tac find_refs_globals_EL >>
        `domain (find_v_globals (EL (Num (ABS i'''''')) vs))
            ⊆ domain (find_v_globalsL vs)` by
            (match_mp_tac find_v_globalsL_EL >> decide_tac) >>
             metis_tac[SUBSET_TRANS])
    >- (qexists_tac `removed_state` >> fs[] >> fs[])
    >- (rw[] >- metis_tac[] >>
        fs[find_refs_globals_APPEND, domain_union, find_refs_globals_def] >>
        metis_tac[find_v_globalsL_REPLICATE, SUBSET_DEF])
    >- (`Num (ABS i''''') < LENGTH vs'` by fs[] >>
        metis_tac[find_v_globalsL_EL, SUBSET_DEF])
    >- (qexists_tac `removed_state` >> fs[] >> fs[])
    >- (metis_tac[find_v_globals_v_to_list, SUBSET_DEF])
    >- (qexists_tac `removed_state` >> fs[] >> fs[])
    >- (rw[] >> metis_tac[find_refs_globals_LUPDATE])
    >- (rw[] >> metis_tac[find_refs_globals_LUPDATE])
    >- (rw[] >> metis_tac[find_refs_globals_LUPDATE])
    >- (qexists_tac `removed_state` >> fs[] >> fs[])
    >- (qexists_tac `removed_state` >> fs[] >> fs[])
    >- (fs[find_refs_globals_APPEND, domain_union, find_refs_globals_def] >>
        metis_tac[])
    >- (metis_tac[find_refs_globals_EL, SUBSET_DEF])
    >- (rw[] >>
        fs[find_refs_globals_APPEND, find_refs_globals_def,
           find_v_globals_def, domain_union] >> res_tac)
    >- (rw[] >> metis_tac[find_refs_globals_LUPDATE])
);



(**************************** MAIN LEMMAS *****************************)

Theorem close_spt_thm
    `∀ reachable seen tree closure (roots : num set) .
        (wf reachable) ∧ (wf seen) ∧ (wf_set_tree tree) ∧
        (close_spt reachable seen tree = closure) ∧
        (subspt reachable seen) ∧
        (roots ⊆ domain (seen)) ∧
        (domain seen ⊆ domain tree) ∧
        (∀ k . k ∈ domain (seen)
            ⇒ (∃ n . (n ∈ roots) ∧ (is_reachable tree n k))) ∧
        (∀ k . k ∈ domain (reachable)
            ⇒ (∀ a . (is_adjacent tree k a) ⇒ a ∈ domain (seen)))
      ⇒ (domain closure = {a | ∃ n . (is_reachable tree n a) ∧ (n ∈ roots)})`
    (recInduct close_spt_ind >> rw[] >>
    once_rewrite_tac [close_spt_def] >> simp[] >> fs[wf_set_tree_def] >>
    IF_CASES_TAC
    >- (
        imp_res_tac inter_eq_LN  >>
        imp_res_tac subspt_domain >>
        fs[SUBSET_DEF, EXTENSION, IN_DISJOINT, domain_difference] >>
        `domain reachable = domain seen` by (
            fs[EXTENSION] >> rw[] >> EQ_TAC >> fs[] >> metis_tac[]) >>
        imp_res_tac num_set_domain_eq >>
        fs[] >> rveq >> rw[] >> EQ_TAC >> rw[]
        >- (qpat_x_assum `∀ k . k ∈ domain seen ⇒ _` (qspec_then `x` mp_tac) >>
            reverse(impl_tac) >> rw[] >> metis_tac[])
        >> (imp_res_tac reachable_domain >> rveq >> fs[] >>
            res_tac >>
            qspecl_then [`domain reachable`, `domain reachable`, `tree`] mp_tac
                (rtc_is_adjacent |> GEN_ALL) >>
            strip_tac >> fs[] >>
            fs[is_reachable_def] >>
            res_tac)
        )
    >- (
        fs[] >>
        first_x_assum match_mp_tac >>
        fs[wf_union, wf_difference, subspt_domain, domain_union] >>
        fs[SUBSET_DEF] >>
        rw[] >> fs[]
        >- (
            match_mp_tac wf_union >>
            fs[] >>
            match_mp_tac wf_spt_fold_tree >>
            fs[wf_inter, wf_def] >>
            fs[lookup_inter] >>
            rw[] >> EVERY_CASE_TAC >> fs[] >>
            rveq >>
            fs[subspt_lookup] >>
            res_tac >>
            metis_tac[]
            )
        >-  metis_tac[]
        >-  metis_tac[]
        >- (
            qspecl_then [`tree`, `LN`] mp_tac domain_spt_fold_union >>
            fs[domain_def] >>
            impl_tac
            >- (rw[] >> res_tac >> fs[SUBSET_DEF])
            >- (rw[] >>
                qspecl_then
                    [`inter tree (difference seen reachable)`, `tree`, `LN`]
                    mp_tac subspt_domain_spt_fold_union >>
                rw[] >> fs[SUBSET_DEF] >>
                first_x_assum mp_tac >> impl_tac >> fs[] >>
                fs[subspt_alt, lookup_inter, domain_difference] >> rw[] >>
                EVERY_CASE_TAC >> fs[])
            )
        >- (
            fs[domain_lookup] >>
            imp_res_tac lookup_spt_fold_union >>
            fs[lookup_def] >>
            fs[lookup_inter] >>
            EVERY_CASE_TAC >> fs[] >>
            rveq >>
            fs[lookup_difference] >> EVERY_CASE_TAC >> fs[] >>
            res_tac >>
            qexists_tac `v'` >> fs[]
            )
        >- (
            fs[domain_lookup] >>
            imp_res_tac lookup_spt_fold_union >>
            fs[lookup_def] >>
            fs[lookup_inter] >>
            EVERY_CASE_TAC >> fs[] >>
            rveq >>
            fs[lookup_difference] >> EVERY_CASE_TAC >> fs[] >>
            res_tac >>
            qexists_tac `n` >> fs[] >>
            fs[is_reachable_def] >>
            simp[Once RTC_CASES2] >>
            DISJ2_TAC >>
            qexists_tac `n1` >> fs[] >>
            fs[is_adjacent_def]
            )
        >-  metis_tac[]
        >- (
            Cases_on `a ∈ domain seen` >> fs[] >>
            Cases_on `a ∈ domain reachable` >> rfs[]
            >-  metis_tac[]
            >>  `a ∈ domain tree` by fs[is_adjacent_def, domain_lookup] >>
                `k ∈ domain tree` by fs[is_adjacent_def, domain_lookup] >>
                `k ∈ domain (inter tree (difference seen reachable))` by
                    fs[domain_inter, domain_difference] >>
                fs[is_adjacent_def] >>
                fs[domain_lookup] >>
                qspecl_then
                    [`inter tree (difference seen reachable)`, `LN`, `a`]
                    mp_tac (GSYM lookup_spt_fold_union_STRONG) >>
                fs[lookup_def] >> strip_tac >>
                fs[lookup_inter] >> EVERY_CASE_TAC >> fs[] >>
                rveq >> fs[] >>
                fs[EQ_IMP_THM] >>
                first_x_assum match_mp_tac >>
                fs[lookup_difference] >>
                qexists_tac `k` >> fs[]
            )
    )
);

val closure_spt_lemma =
    close_spt_thm |> Q.SPECL [`LN`, `start:num_set`, `tree`]
        |> SIMP_RULE std_ss [
            GSYM closure_spt_def, wf_def, wf_insert,
            subspt_def, domain_def, NOT_IN_EMPTY,
            domain_insert, SUBSET_DEF
           ]
        |> Q.SPECL[`domain (start:num_set)`]
        |> SIMP_RULE std_ss [
                ConseqConvTheory.AND_CLAUSES_XX,
                ConseqConvTheory.IMP_CLAUSES_XX,
                IN_SING, Once is_reachable_def, RTC_REFL, AND_CLAUSES
           ] |> GEN_ALL
;

Theorem closure_spt_thm
    `∀ tree start . wf start ∧ (wf_set_tree tree) ∧
    (domain start ⊆ domain tree)
  ⇒ domain (closure_spt start tree) =
        {a | ∃ n . is_reachable tree n a ∧ n ∈ domain start}`
    (rw[] >> assume_tac closure_spt_lemma >> rw[] >> fs[wf_set_tree_def] >>
    first_x_assum match_mp_tac >> reverse(rw[]) >> res_tac >> fs[SUBSET_DEF] >>
    qexists_tac `k` >> fs[]
);

Theorem analysis_reachable_thm
   `∀ (compiled : dec list) start tree t .
        ((start, t) = analyse_code compiled) ∧
        (tree = mk_wf_set_tree t)
    ⇒ domain (closure_spt start tree) =
        {a | ∃ n . is_reachable tree n a ∧ n ∈ domain start}`
    (rw[] >> qspecl_then [`mk_wf_set_tree t`, `start`] mp_tac closure_spt_thm >>
    rw[] >> `wf_set_tree(mk_wf_set_tree t)` by metis_tac[mk_wf_set_tree_thm] >>
    qspecl_then [`compiled`, `start`, `t`] mp_tac analyse_code_thm >>
    qspec_then `t` mp_tac mk_wf_set_tree_domain >> rw[] >>
    metis_tac[SUBSET_TRANS]
);

(******** EVALUATE MUTUAL INDUCTION ********)

Theorem evaluate_sing_keep_flat_state_rel_eq_lemma
    `(∀ env (state:'a flatSem$state) exprL new_state
        result reachable:num_set removed_state .
        flatSem$evaluate env state exprL = (new_state, result) ∧
        domain (find_lookupsL exprL) ⊆ domain reachable ∧
        env.exh_pat ∧
        flat_state_rel reachable state removed_state ∧
        domain (find_env_globals env) ⊆ domain reachable ∧
        result ≠ Rerr (Rabort Rtype_error)
    ⇒ ∃ new_removed_state .
        evaluate env removed_state exprL = (new_removed_state, result) ∧
        flat_state_rel reachable new_state new_removed_state ∧
        domain (find_sem_prim_res_globals result) ⊆ domain reachable)
   ∧
    (∀ env (state:'a flatSem$state) v patExp_list err_v new_state result
        reachable:num_set removed_state .
        evaluate_match env state v patExp_list err_v = (new_state, result) ∧
        domain (find_lookupsL (MAP SND patExp_list)) ⊆ domain reachable ∧
        env.exh_pat ∧
        domain (find_v_globals v) ⊆ domain reachable ∧
        flat_state_rel reachable state removed_state ∧
        domain (find_env_globals env) ⊆ domain reachable ∧
        result ≠ Rerr (Rabort Rtype_error)
    ⇒ ∃ new_removed_state .
        evaluate_match env removed_state v patExp_list err_v =
            (new_removed_state, result) ∧
        flat_state_rel reachable new_state new_removed_state ∧
        domain (find_sem_prim_res_globals result) ⊆ domain reachable)`
        (ho_match_mp_tac evaluate_ind >> rpt CONJ_TAC >> rpt GEN_TAC >> strip_tac
        (* EVALUATE CASES *)
            (* EMPTY LIST CASE *)
        >- (fs[evaluate_def] >> rveq >>
            fs[find_sem_prim_res_globals_def, find_v_globals_def])
            (* NON_EMPTY, NON-SINGLETON LIST CASE *)
        >- (rpt gen_tac >> strip_tac >>
            qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
            simp[evaluate_def] >> Cases_on `evaluate env state' [e1]` >>
            fs[find_lookups_def, domain_union] >>
            first_x_assum (
                qspecl_then [`reachable`, `removed_state`] mp_tac) >> fs[] >>
            strip_tac >> Cases_on `r` >> rw[] >> rfs[] >>
            Cases_on `evaluate env q (e2::es)` >> fs[] >>
            first_x_assum (
                qspecl_then [`reachable`, `new_removed_state`] mp_tac) >>
            fs[] >>
            reverse(Cases_on `r` >> fs[]) >- (rw[] >> fs[])
            >- (strip_tac >> rw[] >>
                fs[find_sem_prim_res_globals_def,
                    find_v_globals_def, domain_union] >>
                imp_res_tac evaluate_sing >> rveq >> rveq >>
                fs[find_v_globals_def]))
        (* SINGLETON LIST CASES *)
            (* Lit *)
        >- (fs[evaluate_def] >> rveq >> fs[] >>
            fs[find_sem_prim_res_globals_def, find_v_globals_def])
            (* Raise *)
        >- (rpt gen_tac >> strip_tac >> fs[find_lookups_def] >>
            qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
            simp[evaluate_def] >>
            Cases_on `evaluate env state' [e]` >> fs[] >> strip_tac >>
            first_x_assum (
                qspecl_then [`reachable`, `removed_state`] mp_tac) >> fs[] >>
            strip_tac >>
            `r ≠ Rerr (Rabort Rtype_error)` by (
                CCONTR_TAC >> Cases_on `r` >> fs[]) >>
            fs[] >> Cases_on `r` >> fs[] >> rveq >> fs[] >>
            fs[find_sem_prim_res_globals_def,
                find_v_globals_def, find_result_globals_def] >>
            imp_res_tac evaluate_sing >> rveq >> rveq >> fs[find_v_globals_def])
            (* Handle *)
        >- (rpt gen_tac >> strip_tac >>
            qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
            simp[evaluate_def] >>
            Cases_on `evaluate env state' [e]` >> fs[] >>
            fs[find_lookups_def, domain_union] >>
            first_x_assum (
                qspecl_then [`reachable`, `removed_state`] mp_tac) >> fs[] >>
            strip_tac >>
            Cases_on `r` >> rw[] >> rfs[] >>
            Cases_on `e'` >> rw[] >> rfs[] >> rveq >> rfs[] >>
            first_x_assum (
                qspecl_then [`reachable`, `removed_state`] match_mp_tac) >>
            fs[find_sem_prim_res_globals_def, find_result_globals_def])
            (* Con NONE *)
        >- (rpt gen_tac >> strip_tac >>
            qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
            simp[evaluate_def] >> fs[find_lookups_def] >>
            Cases_on `env.check_ctor` >> fs[] >>
            Cases_on `evaluate env state' (REVERSE es)` >> fs[] >>
            first_x_assum (
                qspecl_then [`reachable`, `removed_state`] mp_tac) >>
            simp[Once find_lookupsL_REVERSE] >> fs[] >>
            strip_tac >> Cases_on `r` >> rw[] >> rfs[] >>
            fs[find_sem_prim_res_globals_def, find_v_globals_def] >>
            simp[Once find_v_globalsL_REVERSE])
            (* Con SOME *)
        >- (rpt gen_tac >> strip_tac >>
            qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
            simp[evaluate_def] >> fs[find_lookups_def] >>
            Cases_on `evaluate env state' (REVERSE es)` >> fs[] >>
            Cases_on `env.check_ctor ∧ (cn, LENGTH es) ∉ env.c` >> fs[] >>
            first_x_assum (
                qspecl_then [`reachable`, `removed_state`] mp_tac) >>
            simp[Once find_lookupsL_REVERSE] >> fs[] >>
            strip_tac >> Cases_on `r` >> rw[] >> rfs[] >>
            fs[find_sem_prim_res_globals_def, find_v_globals_def] >>
            simp[Once find_v_globalsL_REVERSE])
            (* Var_local *)
        >- (qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
            simp[evaluate_def] >> strip_tac >> rveq >> fs[find_lookups_def] >>
            Cases_on `ALOOKUP env.v n` >>
            fs[find_sem_prim_res_globals_def, find_v_globals_def] >>
            imp_res_tac ALOOKUP_MEM >> imp_res_tac find_v_globalsL_MEM >>
            fs[find_env_globals_def] >> fs[SUBSET_DEF])
            (* Fun *)
        >- (qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
            simp[evaluate_def] >> strip_tac >> rveq >>
            fs[find_sem_prim_res_globals_def,
                find_env_globals_def, find_v_globals_def] >>
            fs[domain_union, find_lookups_def])
            (* App *)
        >- (
            rpt gen_tac >> strip_tac >>
            qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
            simp[evaluate_def] >> fs[find_lookups_def] >>
            Cases_on `evaluate env state' (REVERSE es)` >> fs[] >>
            first_x_assum (
                qspecl_then [`reachable`, `removed_state`] mp_tac) >>
            simp[Once find_lookupsL_REVERSE] >> fs[] >>
            strip_tac >> fs[] >>
            `domain (find_lookupsL es) ⊆ domain reachable` by (
                Cases_on `op` >> fs[dest_GlobalVarLookup_def] >>
                fs[domain_insert]) >>
            fs[] >>
            Cases_on `r` >> fs[] >> strip_tac >> rveq >> fs[] >> rfs[] >>
            Cases_on `op = Opapp` >> fs[]
            >- (Cases_on `do_opapp (REVERSE a)` >> fs[] >>
                Cases_on `x` >> fs[] >>
                Cases_on `q.clock = 0` >> fs[]
                >- (rveq >>
                    qpat_x_assum
                        `flat_state_rel reachable new_state _` mp_tac >>
                    simp[Once flat_state_rel_def] >> strip_tac >> rveq >>
                    fs[flat_state_rel_def,
                        find_sem_prim_res_globals_def, find_result_globals_def])
                >- (first_x_assum (qspecl_then
                        [`reachable`, `dec_clock new_removed_state`] mp_tac) >>
                    fs[] >>
                    qpat_x_assum `flat_state_rel reachable q _` mp_tac >>
                    simp[Once flat_state_rel_def] >>
                    strip_tac >> strip_tac >>
                    qpat_x_assum `_ ⇒ _` match_mp_tac  >>
                    fs[flat_state_rel_def, globals_rel_def,
                        dec_clock_def, find_env_globals_def] >> rfs[] >> rveq >>
                    fs[do_opapp_def] >> EVERY_CASE_TAC >> fs[] >> rveq >>
                    fs[find_sem_prim_res_globals_def] >>
                    fs[SWAP_REVERSE_SYM, find_v_globals_def, domain_union] >>
                    rw[]
                    >- (fs[semanticPrimitivesPropsTheory.find_recfun_ALOOKUP] >>
                        imp_res_tac ALOOKUP_MEM >>
                        `MEM r (MAP (SND o SND) l0)` by (
                            fs[MEM_MAP] >> qexists_tac `(s,q'',r)` >> fs[]) >>
                        imp_res_tac find_lookupsL_MEM >> rw[] >>
                        metis_tac[SUBSET_TRANS])
                    >- (fs[build_rec_env_def] >> fs[FOLDR_CONS_triple] >>
                        fs[find_v_globalsL_APPEND, domain_union] >>
                        fs[MAP_MAP_o] >>
                        `MAP (SND o (λ (f,x,e). (f, Recclosure l l0 f))) l0 =
                        MAP (λ (f,x,e). (Recclosure l l0 f)) l0` by
                            (rw[MAP_EQ_f] >> PairCases_on `e` >> fs[]) >>
                        fs[] >>
                        `domain (find_v_globalsL (MAP (λ(f,x,e).
                            Recclosure l l0 f) l0)) ⊆
                            domain(find_v_globalsL (MAP SND l)) ∪
                        domain (find_lookupsL (MAP (SND o SND) l0))` by
                            metis_tac[find_v_globals_MAP_Recclosure] >>
                        fs[SUBSET_DEF, EXTENSION] >> metis_tac[])
                    >- (fs[semanticPrimitivesPropsTheory.find_recfun_ALOOKUP] >>
                        imp_res_tac ALOOKUP_MEM >>
                        `MEM r (MAP (SND o SND) l0)` by (fs[MEM_MAP] >>
                        qexists_tac `(s,q'',r)` >> fs[]) >>
                        imp_res_tac find_lookupsL_MEM >> rw[] >>
                        metis_tac[SUBSET_TRANS])
                    >- (fs[build_rec_env_def] >> fs[FOLDR_CONS_triple] >>
                        fs[find_v_globalsL_APPEND, domain_union] >>
                        fs[MAP_MAP_o] >>
                        `MAP (SND o (λ (f,x,e). (f, Recclosure l l0 f))) l0 =
                        MAP (λ (f,x,e). (Recclosure l l0 f)) l0` by (
                            rw[MAP_EQ_f] >> PairCases_on `e` >> fs[]) >> fs[] >>
                        `domain (find_v_globalsL
                            (MAP (λ(f,x,e). Recclosure l l0 f) l0)) ⊆
                            domain(find_v_globalsL (MAP SND l)) ∪
                        domain (find_lookupsL (MAP (SND o SND) l0))` by
                            metis_tac[find_v_globals_MAP_Recclosure] >>
                        fs[SUBSET_DEF, EXTENSION] >> metis_tac[]))
                )
            >- (Cases_on `do_app env.check_ctor q op (REVERSE a)` >> fs[] >>
                PairCases_on `x` >> fs[] >> rveq >>
                drule (GEN_ALL do_app_SOME_flat_state_rel) >>
                fs[find_lookups_def] >> disch_then drule >> strip_tac >>
                pop_assum (qspecl_then [
                    `env.check_ctor`, `REVERSE a`, `new_state`, `x1`] mp_tac) >>
                    simp[Once find_v_globalsL_REVERSE] >>
                fs[] >> strip_tac >>
                `domain (case dest_GlobalVarLookup op of
                    NONE => LN | SOME n => insert n () LN) ⊆ domain reachable`
                        by (Cases_on `dest_GlobalVarLookup op` >> fs[]) >>
                            fs[find_sem_prim_res_globals_def] >> rfs[]))
            (* If *)
        >- (rpt gen_tac >> strip_tac >>
            qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
            simp[evaluate_def] >> fs[find_lookups_def, domain_union] >>
            Cases_on `evaluate env state' [e1]` >> fs[] >>
            first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
            fs[] >>
            strip_tac >> strip_tac >> fs[] >>
            `r ≠ Rerr(Rabort Rtype_error)` by
                (CCONTR_TAC >> Cases_on `r` >> fs[]) >>
            fs[] >>
            Cases_on `r` >> fs[] >>
            Cases_on `do_if (HD a) e2 e3` >> fs[] >>
            fs[do_if_def] >> EVERY_CASE_TAC >> fs[])
            (* Mat *)
        >- (rpt gen_tac >> strip_tac >>
            qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
            simp[evaluate_def] >> fs[find_lookups_def, domain_union] >>
            Cases_on `evaluate env state' [e]` >> fs[] >>
            first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
            fs[] >>
            strip_tac >> strip_tac >>
            `r ≠ Rerr(Rabort Rtype_error)` by
                (CCONTR_TAC >> Cases_on `r` >> fs[]) >> fs[] >>
            Cases_on `r` >> fs[] >>
            first_x_assum (qspecl_then [`reachable`, `new_removed_state`]
                match_mp_tac) >> fs[] >>
            fs[find_sem_prim_res_globals_def] >>
            imp_res_tac evaluate_sing >> rveq >> fs[] >> rveq >>
            fs[find_v_globals_def])
            (* Let *)
        >- (rpt gen_tac >> strip_tac >>
            qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
            simp[evaluate_def] >> fs[find_lookups_def, domain_union] >>
            Cases_on `evaluate env state' [e1]` >> fs[] >>
            first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
            fs[] >>
            strip_tac >> strip_tac >>
            `r ≠ Rerr(Rabort Rtype_error)` by
                (CCONTR_TAC >> Cases_on `r` >> fs[]) >> fs[] >>
            Cases_on `r` >> fs[] >>
            first_x_assum (qspecl_then [`reachable`, `new_removed_state`]
                match_mp_tac) >> fs[] >>
            fs[find_env_globals_def, libTheory.opt_bind_def] >>
            Cases_on `n` >> fs[] >>
            fs[find_v_globals_def, domain_union] >>
            fs[find_sem_prim_res_globals_def] >> imp_res_tac evaluate_sing >>
            rveq >> fs[] >> rveq >> fs[find_v_globals_def])
            (* Letrec *)
        >- (rpt gen_tac >> strip_tac >>
            qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
            simp[evaluate_def] >> fs[find_lookups_def, domain_union] >>
            Cases_on `ALL_DISTINCT (MAP FST funs)` >> fs[] >>
            strip_tac >> fs[] >>
            first_x_assum (qspecl_then [`reachable`, `removed_state`]
                match_mp_tac) >> fs[] >>
            fs[find_env_globals_def, build_rec_env_def] >>
            fs[FOLDR_CONS_triple] >> fs[find_v_globalsL_APPEND, domain_union] >>
            fs[MAP_MAP_o] >>
            `MAP (SND o (λ (f,x,e). (f, Recclosure env.v funs f))) funs =
                MAP (λ (f,x,e). (Recclosure env.v funs f)) funs` by
                    (rw[MAP_EQ_f] >> PairCases_on `e'` >> fs[]) >>
            `domain (find_v_globalsL (MAP (SND o (λ(f,x,e).
                (f, Recclosure env.v funs f))) funs)) ⊆
                domain (find_v_globalsL (MAP SND env.v)) ∪
                domain (find_lookupsL (MAP (SND o SND) funs))` by
                    metis_tac[find_v_globals_MAP_Recclosure] >>
            fs[SUBSET_DEF] >> metis_tac[])
        (* EVALUATE_MATCH CASES *)
            (* EMPTY LIST CASE *)
        >- (fs[evaluate_def])
            (* NON-EMPTY LIST CASE *)
        >- (rpt gen_tac >> strip_tac >>
            qpat_x_assum `evaluate_match _ _ _ _ _ =  _` mp_tac >>
            simp[evaluate_def] >> fs[find_lookups_def, domain_union] >>
            Cases_on `ALL_DISTINCT (pat_bindings p [])` >> fs[] >>
            strip_tac >>
            `state'.refs = removed_state.refs` by fs[flat_state_rel_def] >>
            fs[] >>
            Cases_on `pmatch env removed_state.refs p v []` >> fs[] >>
            first_x_assum (qspecl_then [`reachable`, `removed_state`]
                match_mp_tac) >> fs[] >>
            fs[find_env_globals_def, find_v_globalsL_APPEND, domain_union] >>
            drule (CONJUNCT1 pmatch_Match_reachable) >> disch_then drule >>
            disch_then match_mp_tac >> fs[find_v_globals_def] >> rw[] >>
            fs[flat_state_rel_def])
);

(******** EVALUATE SPECIALISATION ********)

Theorem evaluate_sing_keep_flat_state_rel_eq
    `∀ env (state:'a flatSem$state) exprL new_state result expr
        reachable removed_state .
        flatSem$evaluate (env with v := []) state exprL = (new_state, result) ∧
        exprL = [expr] ∧
        keep reachable (Dlet expr) ∧ env.exh_pat ∧
        domain(find_lookups expr) ⊆ domain reachable ∧
        flat_state_rel reachable state removed_state ∧
        domain (find_env_globals env) ⊆ domain reachable ∧
        result ≠ Rerr (Rabort Rtype_error)
    ⇒ ∃ new_removed_state .
        evaluate (env with v := []) removed_state exprL
            = (new_removed_state, result) ∧
        flat_state_rel reachable new_state new_removed_state`
        (rpt gen_tac >> strip_tac >> fs[keep_def] >> rveq >>
        drule (CONJUNCT1 evaluate_sing_keep_flat_state_rel_eq_lemma) >> fs[] >>
        strip_tac >> pop_assum (qspecl_then [`reachable`, `removed_state`]
            mp_tac) >> fs[] >>
        impl_tac >> fs[] >>
        simp[find_env_globals_def, find_v_globals_def, Once find_lookups_def] >>
        simp[EVAL ``find_lookupsL []``] >> rw[] >> fs[]
);

(******** EVALUATE_DEC ********)

Theorem evaluate_dec_flat_state_rel
    `∀ env (state:'a flatSem$state) dec new_state new_ctors result
        reachable removed_state .
        evaluate_dec env state dec = (new_state, new_ctors, result) ∧
        env.exh_pat ∧
        decs_closed reachable [dec] ∧
        flat_state_rel reachable state removed_state ∧ keep reachable dec ∧
        result ≠ SOME (Rabort Rtype_error) ∧
        domain (find_env_globals env) ⊆ domain reachable
    ⇒ ∃ new_removed_state .
        evaluate_dec env removed_state dec =
            (new_removed_state, new_ctors, result) ∧
        flat_state_rel reachable new_state new_removed_state`
        (rw[] >> qpat_x_assum `evaluate_dec _ _ _ = _` mp_tac >>
        reverse(Induct_on `dec`) >> fs[evaluate_dec_def] >> strip_tac >>
        strip_tac >>
        fs[keep_def]
        >- (reverse(Cases_on `env.check_ctor`) >> fs[is_fresh_exn_def] >>
            rw[] >> fs[find_result_globals_def])
        >- (reverse(Cases_on `env.check_ctor`) >> fs[is_fresh_exn_def] >>
            rw[] >> fs[find_result_globals_def]) >>
        strip_tac >> strip_tac >>
        assume_tac evaluate_sing_keep_flat_state_rel_eq >> fs[] >>
        Cases_on `evaluate (env with v := []) state' [e]` >> fs[] >>
        first_x_assum (qspecl_then [`env`, `state'`, `q`, `r`, `e`,
            `reachable`, `removed_state`] mp_tac) >> strip_tac >>
        fs[keep_def] >> rfs[] >> fs[] >>
        `domain (find_lookups e) ⊆ domain reachable` by (
            fs[decs_closed_def] >> fs[analyse_code_def] >>
            fs[analyse_exp_def] >>
            reverse(Cases_on `is_pure e`) >> fs[]
            >- (fs[code_analysis_union_def] >> fs[domain_union]) >>
            reverse(Cases_on `is_hidden e`) >> fs[] >>
            fs[code_analysis_union_def, domain_union] >>
            fs[Once num_set_tree_union_sym, num_set_tree_union_def] >>
            simp[SUBSET_DEF] >>
            rw[] >> first_x_assum match_mp_tac >>
            fs[spt_eq_thm, wf_inter, wf_def] >> fs[lookup_inter_alt] >>
            fs[lookup_def] >> Cases_on `lookup n (find_loc e)` >> fs[] >>
            fs[domain_lookup] >>
            asm_exists_tac >> fs[] >> fs[is_reachable_def] >>
            match_mp_tac RTC_SINGLE >> fs[is_adjacent_def] >>
            `(lookup n (map (K (find_lookups e)) (find_loc e))) =
                SOME (find_lookups e)` by fs[lookup_map] >>
            imp_res_tac lookup_mk_wf_set_tree >> fs[] >>
            `wf_set_tree (mk_wf_set_tree
                (map (K (find_lookups e)) (find_loc e)))`
                by metis_tac[mk_wf_set_tree_thm] >>
            fs[wf_set_tree_def] >> res_tac >> `y = find_lookups e`
                by metis_tac[wf_find_lookups, num_set_domain_eq] >>
            rveq >> fs[] >> fs[SUBSET_DEF, domain_lookup]) >>
        fs[] >> `r ≠ Rerr (Rabort Rtype_error)` by
            (CCONTR_TAC >> Cases_on `r` >> fs[]) >> fs[] >>
        qpat_x_assum `_ = (_,_,_) ` mp_tac >> fs[] >>
        EVERY_CASE_TAC >> fs[] >> rw[] >>
        fs[find_result_globals_def, find_sem_prim_res_globals_def]
);




(********************** CASE: *NOT* keep reachable h ***********************)

(******** EVALUATE MUTUAL INDUCTION ********)

Theorem evaluate_flat_state_rel_lemma
    `(∀ env (state:'a flatSem$state) exprL new_state result
        reachable removed_state .
        flatSem$evaluate env state exprL = (new_state, result) ∧
        EVERY is_pure exprL ∧
        EVERY (λ e. isEmpty (inter (find_loc e) reachable)) exprL ∧
        env.exh_pat ∧
        flat_state_rel reachable state removed_state ∧
        result ≠ Rerr (Rabort Rtype_error)
    ⇒ flat_state_rel reachable new_state removed_state ∧
        ∃ values : flatSem$v list . result = Rval values)
   ∧
    (∀ env (state:'a flatSem$state) v patExp_list err_v new_state result
        reachable removed_state .
        evaluate_match env state v patExp_list err_v = (new_state, result) ∧
        EVERY is_pure (MAP SND patExp_list) ∧
        EVERY (λ e. isEmpty (inter (find_loc e) reachable))
            (MAP SND patExp_list) ∧
        env.exh_pat ∧
        flat_state_rel reachable state removed_state ∧
        result ≠ Rerr (Rabort Rtype_error)
    ⇒ flat_state_rel reachable new_state removed_state ∧
        ∃ values : flatSem$v list . result = Rval values)`
    (ho_match_mp_tac evaluate_ind >> rpt CONJ_TAC >> rpt GEN_TAC >> strip_tac
    (* EVALUATE_DECS_CASES *)
    >- (
        (* EMPTY LIST CASE *)
        fs[evaluate_def] >> rveq >> fs[find_v_globals_def]
        )
    >- (
        (* NON-EMPTY, NON-SINGLETON LIST CASE *)
        rpt gen_tac >> strip_tac >>
        qpat_assum `flat_state_rel _ _ _` mp_tac >>
        SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >>
        fs[evaluate_def] >>
        Cases_on `evaluate env state' [e1]` >> fs[] >>
        Cases_on `r` >> fs[]
        >- (Cases_on `evaluate env q (e2 :: es)` >> fs[] >>
            first_x_assum drule >> disch_then drule >>
            fs[] >> Cases_on `r` >> fs[]
            >- (first_x_assum (qspecl_then [`reachable`, `removed_state`]
                    mp_tac) >> fs[] >>
                rw[] >> fs[find_v_globals_def, domain_union] >>
                `LENGTH a = 1` by (imp_res_tac evaluate_sing >> fs[]) >>
                Cases_on `a` >> fs[find_v_globals_def, domain_union])
            >- (first_x_assum (qspecl_then [`reachable`, `removed_state`]
                    mp_tac) >>
                fs[] >> rw[] >> fs[] >> qpat_x_assum `EXISTS _ _` mp_tac >>
                once_rewrite_tac [GSYM NOT_EVERY] >> strip_tac))
        >- (first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
            fs[] >>
            rw[] >> fs[])
        )
        (* SINGLETON LIST CASES *)
    >- (
        (* Lit *)
        fs[evaluate_def] >> rveq >> fs[find_v_globals_def]
        )
    >- (
        (* Raise *)
        rpt gen_tac >> strip_tac >> qpat_assum `flat_state_rel _ _ _` mp_tac >>
        SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >>
        fs[evaluate_def] >> Cases_on `evaluate env state' [e]` >> fs[] >>
        Cases_on `r` >> fs[] >>
        first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
        fs[is_pure_def]
        )
    >- (
        (* Handle *)
        rpt gen_tac >> strip_tac >> qpat_assum `flat_state_rel _ _ _` mp_tac >>
        SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >>
        fs[evaluate_def] >>
        Cases_on `evaluate env state' [e]` >> fs[] >>
        Cases_on `r` >> fs[]
        >- (rveq >>
            first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
            fs[is_pure_def] >> strip_tac >>
            qpat_x_assum `isEmpty _` mp_tac >>
            simp[Once find_loc_def] >>
            strip_tac >>
            qpat_x_assum `isEmpty _ ⇒ _` match_mp_tac >> fs[] >>
            imp_res_tac inter_union_empty)
        >- (fs[is_pure_def] >>
            qpat_x_assum `isEmpty _` mp_tac >> simp[Once find_loc_def] >>
            strip_tac >>
            `isEmpty(inter (find_locL (MAP SND patExp_list)) reachable) ∧
            isEmpty (inter (find_loc e) reachable)` by
                metis_tac[inter_union_empty] >>
            first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
            fs[] >> strip_tac >> fs[])
        )
    >- (
        (* Con NONE *)
        rpt gen_tac >> strip_tac >> qpat_assum `flat_state_rel _ _ _` mp_tac >>
        SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >>
        reverse(Cases_on `env.check_ctor`) >> fs[] >> fs[evaluate_def] >>
        Cases_on `evaluate env state' (REVERSE es)` >> fs[] >>
        Cases_on `r` >> fs[]
        >- (first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
            fs[] >>
            strip_tac >> rveq >>
            fs[is_pure_def, find_v_globals_def] >> fs[EVERY_REVERSE] >>
            simp[Once find_v_globalsL_REVERSE] >> fs[is_pure_EVERY_aconv] >>
            rfs[] >>
            qpat_x_assum `isEmpty _` mp_tac >> simp[Once find_loc_def] >>
            strip_tac >>
            fs[find_loc_EVERY_isEmpty])
        >- (first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
            fs[] >>
            rveq >> fs[is_pure_def] >> fs[EVERY_REVERSE, is_pure_EVERY_aconv] >>
            once_rewrite_tac [(GSYM NOT_EXISTS)] >>
            once_rewrite_tac [GSYM NOT_EVERY] >> fs[] >>
            qpat_x_assum `isEmpty _` mp_tac >> simp[Once find_loc_def] >>
            fs[find_loc_EVERY_isEmpty])
        )
    >- (
        (* Con SOME *)
        rpt gen_tac >> strip_tac >> qpat_assum `flat_state_rel _ _ _` mp_tac >>
        SIMP_TAC std_ss [Once flat_state_rel_def] >>
        strip_tac >> fs[evaluate_def] >>
        Cases_on `env.check_ctor ∧ (cn, LENGTH es) ∉ env.c` >> fs[] >> fs[] >>
        Cases_on `evaluate env state' (REVERSE es)` >> fs[] >> Cases_on `r` >>
        fs[] >>
        fs[is_pure_def, is_pure_EVERY_aconv, EVERY_REVERSE] >> rveq >>
        fs[find_loc_EVERY_isEmpty] >>
        qpat_x_assum `isEmpty _` mp_tac >> simp[Once find_loc_def] >>
        strip_tac >>
        first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
        fs[EVERY_REVERSE, is_pure_EVERY_aconv] >>
        once_rewrite_tac [(GSYM NOT_EXISTS)] >>
        once_rewrite_tac [GSYM NOT_EVERY] >> fs[find_loc_EVERY_isEmpty]
        )
    >- (
        (* Var_local *)
        fs[evaluate_def] >> Cases_on `ALOOKUP env.v n` >> fs[] >>
        rveq >> fs[] >>
        fs[find_v_globals_def, find_env_globals_def] >>
        imp_res_tac ALOOKUP_MEM >>
        imp_res_tac find_v_globalsL_MEM >> imp_res_tac SUBSET_TRANS
        )
    >- (
        (* Fun *)
        qpat_assum `flat_state_rel _ _ _` mp_tac >>
        SIMP_TAC std_ss [Once flat_state_rel_def] >>
        strip_tac >> fs[evaluate_def] >>
        rveq >>
        fs[find_v_globals_def, domain_union,
            find_env_globals_def, is_pure_def] >>
        fs[find_loc_def]
        )
    >- (
        (* App *)
        rpt gen_tac >> strip_tac >> qpat_assum `flat_state_rel _ _ _` mp_tac >>
        SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >>
        fs[evaluate_def] >>
        Cases_on `evaluate env state' (REVERSE es)` >> fs[] >>
        fs[is_pure_def] >> qpat_x_assum `isEmpty _` mp_tac >>
        simp[Once find_loc_def] >>
        strip_tac >> fs[] >> fs[EVERY_REVERSE] >> fs[find_loc_EVERY_isEmpty] >>
        Cases_on `r` >> fs[]
        >- (Cases_on `op = Opapp` >> fs[is_pure_def, dest_GlobalVarInit_def] >>
            first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
            strip_tac >>
            Cases_on `op` >>
            fs[is_pure_def, dest_GlobalVarInit_def, do_app_def] >>
            fs[is_pure_EVERY_aconv] >> imp_res_tac inter_insert_empty >>
            EVERY_CASE_TAC >> fs[] >> rveq >> fs[] >>
            fs[find_v_globals_def, flat_state_rel_def] >> rw[] >>
            fs[] >> rfs[] >>
            fs[globals_rel_def] >>
            fs[LUPDATE_SEM] >>
            reverse(rw[]) >- metis_tac[] >>
            Cases_on `n = n'` >> fs[] >>
            qpat_x_assum `∀ n . _ ∧ _ ⇒ _` match_mp_tac >>
            fs[EL_LUPDATE])
        >- (rveq >> fs[] >>
            first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
            fs[] >>
            once_rewrite_tac [(GSYM NOT_EXISTS)] >>
            once_rewrite_tac [GSYM NOT_EVERY] >> fs[] >>
            Cases_on `op` >>
            fs[is_pure_def, is_pure_EVERY_aconv, dest_GlobalVarInit_def] >>
            imp_res_tac inter_insert_empty)
        )
    >- (
        (* If *)
        rpt gen_tac >> strip_tac >> qpat_assum `flat_state_rel _ _ _` mp_tac >>
        SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >>
        fs[evaluate_def] >> Cases_on `evaluate env state' [e1]` >> fs[] >>
        fs[is_pure_def] >>
        qpat_x_assum `isEmpty _` mp_tac >> simp[Once find_loc_def] >>
        strip_tac >>
        `isEmpty (inter (find_loc e1) reachable) ∧
            isEmpty (inter (find_loc e2) reachable) ∧
            isEmpty (inter (find_loc e3) reachable)` by
                metis_tac[inter_union_empty] >>
        Cases_on `r` >> fs[]
        >- (fs[do_if_def, Boolv_def] >> Cases_on `HD a` >> fs[] >>
            EVERY_CASE_TAC >> fs[] >>
            rveq >> first_x_assum (qspecl_then [`reachable`, `removed_state`]
                mp_tac) >> fs[] >>
            first_x_assum (qspecl_then [`reachable`, `removed_state`]
                mp_tac) >> fs[])
        >- (rveq >> first_x_assum (qspecl_then [`reachable`, `removed_state`]
            mp_tac) >> fs[])
        )
    >- (
        (* Mat *)
        rpt gen_tac >> strip_tac >> qpat_assum `flat_state_rel _ _ _` mp_tac >>
        SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >>
        fs[evaluate_def] >>
        Cases_on `evaluate env state' [e]` >> fs[] >> fs[is_pure_def] >>
        qpat_x_assum `isEmpty _` mp_tac >> simp[Once find_loc_def] >>
        strip_tac >>
        `isEmpty (inter (find_locL (MAP SND patExp_list)) reachable) ∧
            isEmpty (inter (find_loc e) reachable)` by
                metis_tac[inter_union_empty] >>
        first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
        fs[] >>
        strip_tac >> Cases_on `r` >> fs[] >>
        first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
        fs[] >>
        strip_tac >> fs[is_pure_EVERY_aconv, find_loc_EVERY_isEmpty] >> rfs[] >>
        imp_res_tac evaluate_sing >> rveq >> fs[find_v_globals_def]
        )
    >- (
        (* Let *)
        rpt gen_tac >> strip_tac >> qpat_assum `flat_state_rel _ _ _` mp_tac >>
        SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >>
        fs[evaluate_def] >>
        Cases_on `evaluate env state' [e1]` >> fs[is_pure_def] >>
        fs[is_pure_def] >> qpat_x_assum `isEmpty _ ` mp_tac >>
        simp[Once find_loc_def] >>
        strip_tac >> imp_res_tac inter_union_empty >>
        Cases_on `r` >> fs[]
        >- (first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
            fs[] >>
            first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
            fs[] >>
            strip_tac >> strip_tac >>
            fs[find_env_globals_def] >>
            qpat_x_assum `domain _ ⊆ domain _ ⇒ _` match_mp_tac >>
            fs[libTheory.opt_bind_def] >>
            Cases_on `n` >> fs[] >>
            fs[find_v_globals_def, domain_union] >>
            imp_res_tac evaluate_sing >> rveq >> fs[find_v_globals_def])
        >- (rveq >> fs[] >>
            first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
            fs[])
        )
    >- (
        (* Letrec *)
        rpt gen_tac >> strip_tac >> qpat_assum `flat_state_rel _ _ _` mp_tac >>
        SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >>
        fs[evaluate_def] >> Cases_on `ALL_DISTINCT (MAP FST funs)` >> fs[] >>
        first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
        fs[] >>
        strip_tac >> fs[is_pure_def] >> rfs[] >>
        qpat_x_assum `isEmpty _` mp_tac >> simp[Once find_loc_def] >>
        strip_tac >>
        `isEmpty (inter (find_locL (MAP (SND o SND) funs)) reachable) ∧
            isEmpty (inter (find_loc e) reachable)` by
                metis_tac[inter_union_empty] >>
        fs[] >> qpat_x_assum `domain _ ⊆ domain _ ⇒ _` match_mp_tac >>
        fs[find_env_globals_def, build_rec_env_def] >> fs[FOLDR_CONS_triple] >>
        fs[find_v_globalsL_APPEND, domain_union] >> fs[MAP_MAP_o] >>
        `MAP (SND o (λ (f,x,e). (f, Recclosure env.v funs f))) funs =
            MAP (λ (f,x,e). (Recclosure env.v funs f)) funs` by
                (rw[MAP_EQ_f] >> PairCases_on `e'` >> fs[]) >>
        fs[]
        )
    (* EVALUATE_MATCH CASES *)
    >- (
        (* EMPTY LIST CASE *)
        fs[evaluate_def]
        )
    >- (
        (* NON-EMPTY LIST CASE *)
        rpt gen_tac >> strip_tac >> qpat_assum `flat_state_rel _ _ _` mp_tac >>
        SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >>
        fs[evaluate_def] >> Cases_on `ALL_DISTINCT (pat_bindings p [])` >>
        fs[] >>
        Cases_on `pmatch env removed_state.refs p v []` >> fs[] >>
        first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
        fs[] >>
        impl_tac >> fs[] >>
        fs[find_env_globals_def, find_v_globalsL_APPEND, domain_union] >>
        drule (CONJUNCT1 pmatch_Match_reachable) >> disch_then drule >>
        disch_then match_mp_tac >>
        fs[find_v_globals_def] >> rw[] >> metis_tac[]
        )
);

(******** EVALUATE SPECIALISATION ********)


Theorem evaluate_sing_notKeep_flat_state_rel
    `∀ env (state:'a flatSem$state) exprL new_state result expr
        reachable removed_state .
        flatSem$evaluate (env with v := []) state exprL = (new_state, result) ∧
        exprL = [expr] ∧
        ¬keep reachable (Dlet expr) ∧ env.exh_pat ∧
        flat_state_rel reachable state removed_state ∧
        domain (find_env_globals env) ⊆ domain reachable ∧
        result ≠ Rerr (Rabort Rtype_error)
    ⇒ flat_state_rel reachable new_state removed_state ∧
        ∃ value : flatSem$v . result = Rval [value]`
    (rpt gen_tac >> strip_tac >> fs[keep_def] >> rveq >>
    drule (CONJUNCT1 evaluate_flat_state_rel_lemma) >> fs[] >>
    disch_then drule >> disch_then drule >> fs[] >>
    rw[] >> imp_res_tac evaluate_sing >> fs[] >> fs[find_v_globals_def]
);



(******************************* MAIN PROOFS ******************************)

Theorem flat_decs_removal_lemma
    `∀ env (state:'a flatSem$state) decs new_state new_ctors result
        reachable removed_decs removed_state .
        evaluate_decs env state decs = (new_state, new_ctors, result) ∧
        result ≠ SOME (Rabort Rtype_error) ∧ env.exh_pat ∧
        remove_unreachable reachable decs = removed_decs ∧
        flat_state_rel reachable state removed_state ∧
        domain (find_env_globals env) ⊆ domain reachable ∧
        decs_closed reachable decs
    ⇒ ∃ new_removed_state .
        new_removed_state.ffi = new_state.ffi /\
        evaluate_decs env removed_state removed_decs =
            (new_removed_state, new_ctors, result)`
    (Induct_on `decs`
    >- (rw[evaluate_decs_def, remove_unreachable_def] >>
        fs[evaluate_decs_def, find_result_globals_def, flat_state_rel_def])
    >>  fs[evaluate_decs_def, remove_unreachable_def] >> rw[] >>
        qpat_assum `flat_state_rel _ _ _` mp_tac >>
        SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac
        >- (fs[evaluate_decs_def] >>
            `∃ r . evaluate_dec env state' h = r` by simp[] >>
            PairCases_on `r` >> fs[] >> `r2 ≠ SOME (Rabort Rtype_error)` by
                (CCONTR_TAC >> fs[]) >>
            drule evaluate_dec_flat_state_rel >> rpt (disch_then drule) >>
            rw[] >> fs[] >>
            pop_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
            fs[] >>
            `decs_closed reachable [h]` by imp_res_tac decs_closed_reduce_HD >>
            fs[] >>
            reverse(Cases_on `r2` >> fs[] >> rw[] >> rveq >> EVERY_CASE_TAC)
            >- fs[flat_state_rel_def] >>
            fs[] >> first_x_assum drule >> fs[] >> rveq >> strip_tac >>
            pop_assum (qspecl_then [`reachable`, `new_removed_state`] mp_tac) >>
            fs[] >>
            reverse(impl_tac) >- rw[] >> fs[find_env_globals_def] >>
            imp_res_tac decs_closed_reduce)
        >>  reverse(EVERY_CASE_TAC) >> fs[] >> rveq >>
            rename1 `_ _ decs = (n_state, ctors, res)` >>
            imp_res_tac keep_Dlet >> rveq >>
            fs[Once evaluate_dec_def] >> EVERY_CASE_TAC >> fs[] >>
            rveq >> rw[UNION_EMPTY] >>
            `env with c updated_by $UNION {} = env` by
                fs[environment_component_equality] >> fs[]
            >- (drule evaluate_sing_notKeep_flat_state_rel >> fs[] >>
                strip_tac >>
                pop_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
                strip_tac >> fs[])
            >>  first_x_assum match_mp_tac >> fs[] >> asm_exists_tac >> fs[] >>
                imp_res_tac decs_closed_reduce >> fs[] >>
                drule evaluate_sing_notKeep_flat_state_rel >> fs[]
);

Theorem flat_removal_thm
    `∀ exh_pat check_ctor ffi k decs new_state new_ctors result roots tree
        reachable removed_decs .
        evaluate_decs (initial_env exh_pat check_ctor)
            (initial_state ffi k) decs = (new_state, new_ctors, result) ∧
        result ≠ SOME (Rabort Rtype_error) ∧ exh_pat ∧
        (roots, tree) = analyse_code decs ∧
        reachable = closure_spt roots (mk_wf_set_tree tree) ∧
        remove_unreachable reachable decs = removed_decs
    ⇒ ∃ s .
        s.ffi = new_state.ffi /\
        evaluate_decs (initial_env exh_pat check_ctor) (initial_state ffi k)
            removed_decs = (s, new_ctors, result)`
    (rpt strip_tac >> drule flat_decs_removal_lemma >>
    rpt (disch_then drule) >> strip_tac >>
    pop_assum (qspecl_then
        [`reachable`, `removed_decs`, `initial_state ffi k`] mp_tac) >> fs[] >>
    reverse(impl_tac) >- (rw[] >> fs[])
    >>  qspecl_then [`decs`, `roots`, `mk_wf_set_tree tree`, `tree`]
            mp_tac analysis_reachable_thm >>
        impl_tac >> rw[initial_env_def, initial_state_def]
        >- (fs[flat_state_rel_def, globals_rel_def] >>
            fs[find_refs_globals_def])
        >- (fs[find_env_globals_def, find_v_globals_def])
        >- (fs[decs_closed_def] >> rw[] >> `(r,t) = (roots, tree)` by
            metis_tac[] >> fs[] >> rveq
            >- (rw[SUBSET_DEF] >> qexists_tac `x` >> fs[is_reachable_def])
            >- (qexists_tac `n'` >> fs[is_reachable_def] >>
                metis_tac[transitive_RTC, transitive_def]))
);

Theorem flat_remove_eval_sim
  `eval_sim ffi T T ds1 T T (remove_flat_prog ds1)
                            (\d1 d2. d2 = remove_flat_prog d1) F`
  (rw [eval_sim_def] \\ qexists_tac `0` \\ fs [remove_flat_prog_def]
  \\ pairarg_tac \\ fs []
  \\ drule flat_removal_thm \\ rw [] \\ fs []);

val flat_remove_semantics = save_thm ("flat_remove_semantics",
  MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] IMP_semantics_eq)
           flat_remove_eval_sim |> SIMP_RULE (srw_ss()) []);

(* syntactic results *)

val elist_globals_filter = Q.prove (
  `elist_globals (MAP dest_Dlet (FILTER is_Dlet ds)) = {||}
   ==>
   elist_globals (MAP dest_Dlet (FILTER is_Dlet (FILTER P ds))) = {||}`,
  Induct_on `ds` \\ rw [] \\ fs [SUB_BAG_UNION]);

val esgc_free_filter = Q.prove (
  `EVERY esgc_free (MAP dest_Dlet (FILTER is_Dlet ds))
   ==>
   EVERY esgc_free (MAP dest_Dlet (FILTER is_Dlet (FILTER P ds)))`,
  Induct_on `ds` \\ rw []);

val elist_globals_filter_SUB_BAG = Q.prove (
  `elist_globals (MAP dest_Dlet (FILTER is_Dlet (FILTER P ds))) <=
   elist_globals (MAP dest_Dlet (FILTER is_Dlet ds))`,
  Induct_on `ds` \\ rw [] \\ fs [SUB_BAG_UNION]);

Theorem remove_flat_prog_elist_globals_eq_empty
  `elist_globals (MAP dest_Dlet (FILTER is_Dlet ds)) = {||}
   ==>
   elist_globals (MAP dest_Dlet (FILTER is_Dlet (remove_flat_prog ds))) = {||}`
  (simp [remove_flat_prog_def, remove_unreachable_def, UNCURRY]
  \\ metis_tac [elist_globals_filter]);

Theorem remove_flat_prog_esgc_free
  `EVERY esgc_free (MAP dest_Dlet (FILTER is_Dlet ds))
   ==>
   EVERY esgc_free (MAP dest_Dlet (FILTER is_Dlet (remove_flat_prog ds)))`
  (simp [remove_flat_prog_def, remove_unreachable_def, UNCURRY]
  \\ metis_tac [esgc_free_filter]);

Theorem remove_flat_prog_sub_bag
  `elist_globals (MAP dest_Dlet (FILTER is_Dlet (remove_flat_prog ds))) <=
   elist_globals (MAP dest_Dlet (FILTER is_Dlet ds))`
  (simp [remove_flat_prog_def, remove_unreachable_def, UNCURRY]
  \\ metis_tac [elist_globals_filter_SUB_BAG]);

Theorem remove_flat_prog_distinct_globals
  `BAG_ALL_DISTINCT (elist_globals (MAP dest_Dlet (FILTER is_Dlet ds)))
   ==>
   BAG_ALL_DISTINCT (elist_globals
     (MAP dest_Dlet (FILTER is_Dlet (remove_flat_prog ds))))`
  (metis_tac [remove_flat_prog_sub_bag, BAG_ALL_DISTINCT_SUB_BAG]);


val _ = export_theory();
