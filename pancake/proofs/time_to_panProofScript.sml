(*
  Correctness proof for --
*)

open preamble
     timeSemTheory panSemTheory
     timePropsTheory panPropsTheory
     pan_commonPropsTheory time_to_panTheory
     ffiTimeTheory


val _ = new_theory "time_to_panProof";

val _ = set_grammar_ancestry
        ["timeSem", "panSem", "ffiTime",
         "pan_commonProps", "timeProps",
         "time_to_pan"];

Definition equiv_val_def:
  equiv_val fm xs v <=>
    v = MAP (ValWord o n2w o THE o (FLOOKUP fm)) xs
End


Definition valid_clks_def:
  valid_clks clks tclks wt <=>
    EVERY (λck. MEM ck clks) tclks ∧
    EVERY (λck. MEM ck clks) (MAP SND wt)
End


Definition resetClksVals_def:
  resetClksVals fm xs ys  =
    MAP
    (ValWord o n2w o THE o
     (FLOOKUP (resetClocks fm ys))) xs
End


Definition retVal_def:
  retVal s clks tclks wt dest =
    Struct [
        Struct (resetClksVals s.clocks clks tclks);
        ValWord (case wt of [] => 1w | _ => 0w);
        ValWord (case wt of [] => 0w
                         | _ => n2w (THE (calculate_wtime s tclks wt)));
        ValLabel (toString dest)]
End


Definition maxClksSize_def:
  maxClksSize clks ⇔
    SUM (MAP (size_of_shape o shape_of) clks) ≤ 29
End


Definition clock_bound_def:
  clock_bound fm clks (m:num) ⇔
    EVERY
      (λck. ∃n. FLOOKUP fm ck = SOME n ∧
                n < m) clks
End

Definition time_range_def:
  time_range wt (m:num) ⇔
    EVERY (λ(t,c). t < m) wt
End


Definition restore_from_def:
  (restore_from t lc [] = lc) ∧
  (restore_from t lc (v::vs) =
   restore_from t (res_var lc (v, FLOOKUP t.locals v)) vs)
End

Definition emptyVals_def:
  emptyVals n = REPLICATE n (ValWord 0w)
End

Definition constVals_def:
  constVals n v = REPLICATE n v
End


Definition minOption_def:
  (minOption (x:'a word) NONE = x) ∧
  (minOption x (SOME (y:num)) =
    if x <₊ n2w y then x else n2w y)
End


Definition well_behaved_ffi_def:
  well_behaved_ffi ffi_name s nffi nbytes bytes n (m:num) <=>
  explode ffi_name ≠ "" /\ n < m /\
  read_bytearray ffiBufferAddr n
                 (mem_load_byte s.memory s.memaddrs s.be) =
  SOME bytes /\
  s.ffi.oracle (explode ffi_name) s.ffi.ffi_state [] bytes =
  Oracle_return nffi nbytes /\
  LENGTH nbytes = LENGTH bytes
End


Definition ffi_return_state_def:
  ffi_return_state s ffi_name bytes nbytes nffi =
  s with
    <|memory := write_bytearray 4000w nbytes s.memory s.memaddrs s.be;
      ffi :=
      s.ffi with
       <|ffi_state := nffi;
         io_events :=
         s.ffi.io_events ++
          [IO_event (explode ffi_name) [] (ZIP (bytes,nbytes))]|> |>
End


Definition nffi_state_def:
  nffi_state s nffi (n:num) bytes nbytes =
    s.ffi with
     <|ffi_state := nffi;
       io_events :=
       s.ffi.io_events ++
        [IO_event (toString n) [] (ZIP (bytes,nbytes))]|>
End

Theorem eval_empty_const_eq_empty_vals:
  ∀s n.
    OPT_MMAP (λe. eval s e) (emptyConsts n) =
    SOME (emptyVals n)
Proof
  rw [] >>
  fs [opt_mmap_eq_some] >>
  fs [MAP_EQ_EVERY2] >>
  fs [emptyConsts_def, emptyVals_def] >>
  fs [LIST_REL_EL_EQN] >>
  rw [] >>
  ‘EL n' (REPLICATE n ((Const 0w):'a panLang$exp)) = Const 0w’ by (
    match_mp_tac EL_REPLICATE >>
    fs []) >>
  ‘EL n' (REPLICATE n (ValWord 0w)) = ValWord 0w’ by (
    match_mp_tac EL_REPLICATE >>
    fs []) >>
  fs [eval_def]
QED

Theorem opt_mmap_resetTermClocks_eq_resetClksVals:
  ∀t clkvals s clks tclks.
    EVERY (λck. ck IN FDOM s.clocks) clks ∧
    FLOOKUP t.locals «clks» = SOME (Struct clkvals) ∧
    equiv_val s.clocks clks clkvals ⇒
    OPT_MMAP (λa. eval t a)
             (resetTermClocks «clks» clks tclks) =
    SOME (resetClksVals s.clocks clks tclks)
Proof
  rpt gen_tac >>
  strip_tac >>
  fs [opt_mmap_eq_some] >>
  fs [MAP_EQ_EVERY2] >>
  conj_tac
  >- fs [resetTermClocks_def, resetClksVals_def] >>
  fs [LIST_REL_EL_EQN] >>
  conj_tac
  >- fs [resetTermClocks_def, resetClksVals_def] >>
  rw [] >>
  fs [resetTermClocks_def] >>
  TOP_CASE_TAC
  >- (
    ‘EL n (resetClksVals s.clocks clks tclks) = ValWord 0w’ by (
    fs [resetClksVals_def] >>
    qmatch_goalsub_abbrev_tac ‘MAP ff _’ >>
    ‘EL n (MAP ff clks) = ff (EL n clks)’ by (
      match_mp_tac EL_MAP >>
      fs []) >>
    fs [Abbr ‘ff’] >>
    drule reset_clks_mem_flookup_zero >>
    disch_then (qspec_then ‘s.clocks’ mp_tac) >>
    fs []) >>
   fs [eval_def]) >>
  fs [equiv_val_def] >> rveq >> fs [] >>
  fs [EVERY_MEM] >>
  last_x_assum (qspec_then ‘EL n clks’ mp_tac) >>
  impl_tac
  >- (match_mp_tac EL_MEM >> fs []) >>
  strip_tac >>
  fs [FDOM_FLOOKUP] >>
  ‘EL n (resetClksVals s.clocks clks tclks) = ValWord (n2w v)’ by (
    fs [resetClksVals_def] >>
    qmatch_goalsub_abbrev_tac ‘MAP ff _’ >>
    ‘EL n (MAP ff clks) = ff (EL n clks)’ by (
      match_mp_tac EL_MAP >>
      fs []) >>
    fs [Abbr ‘ff’] >>
    drule reset_clks_not_mem_flookup_same >>
    fs []) >>
  fs [] >>
  fs [eval_def] >>
  qmatch_goalsub_abbrev_tac ‘MAP ff _’ >>
  ‘EL n (MAP ff clks) = ff (EL n clks)’ by (
    match_mp_tac EL_MAP >>
    fs []) >>
  fs [Abbr ‘ff’]
QED


Theorem maxClksSize_reset_clks_eq:
  ∀s clks (clkvals:α v list) tclks.
    EVERY (λck. ck IN FDOM s.clocks) clks ∧
    equiv_val s.clocks clks clkvals ∧
    maxClksSize clkvals  ⇒
    maxClksSize ((resetClksVals s.clocks clks tclks):α v list)
Proof
  rw [] >>
  fs [resetClksVals_def] >>
  fs [equiv_val_def] >> rveq >> fs [] >>
  fs [maxClksSize_def] >>
  fs [MAP_MAP_o] >>
  fs [SUM_MAP_FOLDL] >>
  qmatch_asmsub_abbrev_tac ‘FOLDL ff _ _’ >>
  qmatch_goalsub_abbrev_tac ‘FOLDL gg _ _’ >>
  ‘FOLDL ff 0 clks = FOLDL gg 0 clks ’ by (
    match_mp_tac FOLDL_CONG >>
    fs [Abbr ‘ff’, Abbr ‘gg’] >> rw [shape_of_def]) >>
  fs []
QED


Theorem calculate_wait_times_eq:
  ∀t vname clkvals s clks wt.
    FLOOKUP t.locals vname = SOME (Struct clkvals) ∧
    EVERY (λck. ck IN FDOM s.clocks) clks ∧
    equiv_val s.clocks clks clkvals ∧
    EVERY (λck. MEM ck clks) (MAP SND wt) ∧
    EVERY (λ(t,c). ∃v. FLOOKUP s.clocks c = SOME v ∧ v ≤ t) wt ⇒
    OPT_MMAP (λe. eval t e)
        (waitTimes (MAP FST wt)
         (MAP (λn. Field n (Var vname)) (indicesOf clks (MAP SND wt)))) =
    SOME (MAP (ValWord ∘ n2w ∘ THE ∘ evalDiff s) wt)
Proof
  rw [] >>
  fs [opt_mmap_eq_some] >>
  fs [MAP_EQ_EVERY2] >>
  rw [waitTimes_def, indicesOf_def, LIST_REL_EL_EQN] >>
  ‘SND (EL n wt) ∈ FDOM s.clocks’ by (
    fs [EVERY_MEM] >>
    first_x_assum (qspec_then ‘SND (EL n wt)’ mp_tac) >>
    impl_tac
    >- (
      drule EL_MEM >>
      fs [MEM_MAP] >>
      metis_tac []) >>
    strip_tac >>
    last_x_assum drule >>
    fs []) >>
  qmatch_goalsub_abbrev_tac ‘MAP2 ff xs ys’ >>
  ‘EL n (MAP2 ff xs ys) =
   ff (EL n xs) (EL n ys)’ by (
    match_mp_tac EL_MAP2 >>
    fs [Abbr ‘xs’, Abbr ‘ys’]) >>
  fs [] >>
  pop_assum kall_tac >>
  fs [Abbr ‘xs’] >>
  ‘EL n (MAP FST wt) = FST (EL n wt)’ by (
    match_mp_tac EL_MAP >>
    fs []) >>
  fs [] >>
  pop_assum kall_tac >>
  fs [Abbr ‘ys’] >>
  fs [MAP_MAP_o] >>
  qmatch_goalsub_abbrev_tac ‘EL n (MAP gg _)’ >>
  ‘EL n (MAP gg wt) = gg (EL n wt)’ by (
    match_mp_tac EL_MAP >>
    fs []) >>
  fs [] >>
  pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac ‘MAP hh _’ >>
  ‘EL n (MAP hh wt) = hh (EL n wt)’ by (
    match_mp_tac EL_MAP >>
    fs []) >>
  fs [] >>
  pop_assum kall_tac >>
  fs [Abbr ‘gg’, Abbr ‘ff’, Abbr ‘hh’] >>
  cases_on ‘EL n wt’ >> fs [] >>
  fs [evalDiff_def, evalExpr_def, EVERY_EL] >>
  fs [FDOM_FLOOKUP] >>
  fs [minusT_def] >>
  fs [eval_def, OPT_MMAP_def] >>
  fs [eval_def] >>
  ‘findi r clks < LENGTH clkvals’ by (
    fs [equiv_val_def] >>
    match_mp_tac MEM_findi >>
    res_tac >> fs [] >>
    rfs [] >>
    ‘EL n (MAP SND wt) = SND (EL n wt)’ by (
      match_mp_tac EL_MAP >>
      fs []) >>
    rfs [] >> rveq >> fs []) >>
  fs [] >>
  rfs [equiv_val_def] >>
  qmatch_goalsub_abbrev_tac ‘EL m (MAP ff _)’ >>
  ‘EL m (MAP ff clks) = ff (EL m clks)’ by (
    match_mp_tac EL_MAP >>
    fs []) >>
  fs [Abbr ‘ff’, Abbr ‘m’] >>
  pop_assum kall_tac >>
  last_x_assum drule >>
  strip_tac >> fs [] >>
  ‘EL (findi r clks) clks = r’ by (
    match_mp_tac EL_findi >>
    res_tac >> fs [] >>
    rfs [] >>
    ‘EL n (MAP SND wt) = SND (EL n wt)’ by (
      match_mp_tac EL_MAP >>
      fs []) >>
    rfs [] >> rveq >> fs []) >>
  fs [wordLangTheory.word_op_def] >>
  first_x_assum drule >>
  fs [] >>
  strip_tac >>
  ‘n2w (q − v):'a word = n2w q − n2w v’ suffices_by fs [] >>
  match_mp_tac n2w_sub >> rveq >> fs [] >> rveq >> rfs [] >>
  first_x_assum drule >>
  fs []
QED


Theorem eval_term_clkvals_equiv_reset_clkvals:
  ∀s io io' cnds tclks dest wt s' clks.
    evalTerm s io
             (Tm io' cnds tclks dest wt) s' ⇒
    equiv_val s'.clocks clks (resetClksVals s.clocks clks tclks)
Proof
  rw [] >>
  fs [evalTerm_cases] >>
  rveq >> fs [] >>
  fs [equiv_val_def] >>
  fs [resetClksVals_def]
QED


Theorem evaluate_minop_eq:
  ∀es s vname n ns res t.
    FLOOKUP s.locals vname = SOME (ValWord (n2w n)) ∧
    (∀n. n < LENGTH es ⇒ ~MEM vname (var_exp (EL n es))) ∧
    MAP (eval s) es = MAP (SOME ∘ ValWord ∘ (n2w:num -> α word)) ns ∧
    n < dimword (:α) ∧
    EVERY (λn. n < dimword (:α)) ns ∧
    evaluate (minOp vname es,s) = (res,t) ⇒
    res = NONE ∧
    t = s with locals:= s.locals |+
                         (vname,
                          ValWord (minOption (n2w n) (list_min_option ns)))
Proof
  Induct >>
  rpt gen_tac >>
  strip_tac >> fs []
  >- (
    fs [minOp_def, evaluate_def] >> rveq >>
    fs [minOption_def, list_min_option_def] >>
    cases_on ‘s’ >>
    fs [state_fn_updates] >>
    match_mp_tac EQ_SYM >>
    match_mp_tac FUPDATE_ELIM >>
    fs [FLOOKUP_DEF]) >>
  cases_on ‘ns’ >> fs [] >>
  fs [minOp_def] >>
  fs [evaluate_def] >>
  pairarg_tac >> fs [] >>
  fs [eval_def] >>
  rfs [] >>
  fs [asmTheory.word_cmp_def] >>
  cases_on ‘(n2w h'):'a word <₊ n2w n’ >>
  fs []
  >- (
    fs [evaluate_def] >>
    rfs [] >>
    fs [is_valid_value_def] >>
    rfs [] >>
    fs [panSemTheory.shape_of_def] >>
    rveq >> fs [] >>
    qmatch_asmsub_abbrev_tac ‘evaluate (_, stNew)’ >>
    last_x_assum
    (qspecl_then
     [‘stNew’, ‘vname’, ‘h'’, ‘t'’, ‘res’, ‘t’] mp_tac) >>
    fs [Abbr ‘stNew’] >>
    fs [FLOOKUP_UPDATE] >>
    impl_tac
    >- (
      reverse conj_tac
      >- (
        fs [MAP_EQ_EVERY2] >>
        fs [LIST_REL_EL_EQN] >>
        rw [] >>
        match_mp_tac update_locals_not_vars_eval_eq >>
        last_x_assum (qspec_then ‘SUC n'’ mp_tac) >>
        fs []) >>
      rw [] >> fs [] >>
      last_x_assum (qspec_then ‘SUC n'’ mp_tac) >>
      fs []) >>
    strip_tac >>
    fs [list_min_option_def] >>
    cases_on ‘list_min_option t'’ >> fs []
    >- (
    fs [minOption_def] >>
    ‘~(n2w n <₊ n2w h')’ by (
      fs [WORD_NOT_LOWER] >>
      gs [WORD_LOWER_OR_EQ]) >>
    fs []) >>
    drule list_min_option_some_mem >>
    strip_tac >>
    fs [EVERY_MEM] >>
    first_x_assum (qspec_then ‘x’ mp_tac) >>
    fs [] >>
    strip_tac >>
    cases_on ‘h' < x’ >> fs []
    >- (
    fs [minOption_def] >>
     ‘~(n2w n <₊ n2w h')’ by (
      fs [WORD_NOT_LOWER] >>
      gs [WORD_LOWER_OR_EQ]) >>
     fs [] >>
    qsuff_tac ‘(n2w h'):'a word <₊ n2w x’ >- fs [] >>
    fs [word_lo_n2w]) >>
    fs [minOption_def] >>
    ‘~((n2w h'):'a word <₊ n2w x)’ by (
      fs [WORD_NOT_LOWER, NOT_LESS, word_ls_n2w]) >>
    fs [] >>
    ‘~((n2w n):'a word <₊ n2w x)’ by (
      fs [WORD_NOT_LOWER] >>
      fs [NOT_LESS] >>
      ‘h' < n’ by gs [word_lo_n2w] >>
      ‘x < n’ by gs [] >>
      gs [word_ls_n2w]) >>
    fs []) >>
  fs [evaluate_def] >>
  rfs [] >> rveq >>
  last_x_assum
  (qspecl_then
   [‘s’, ‘vname’, ‘n’, ‘t'’, ‘res’, ‘t’] mp_tac) >>
  fs [] >>
  impl_tac
  >- (
    rw [] >>
    last_x_assum (qspec_then ‘SUC n'’ mp_tac) >>
    fs []) >>
  strip_tac >>
  fs [] >>
  fs [list_min_option_def] >>
  cases_on ‘list_min_option t'’ >> fs []
  >- (
    fs [minOption_def] >>
    fs [WORD_NOT_LOWER] >>
    gs [WORD_LOWER_OR_EQ]) >>
  fs [minOption_def] >>
  every_case_tac >> fs [WORD_NOT_LOWER]
  >- (
    qsuff_tac ‘h' = n’ >- fs [] >>
    qsuff_tac ‘h' ≤ n ∧ n ≤ h'’ >- fs [] >>
    gs [word_ls_n2w]) >> (
  drule list_min_option_some_mem >>
  strip_tac >>
  fs [EVERY_MEM] >>
  first_x_assum (qspec_then ‘x’ mp_tac) >>
  impl_tac >- fs [] >>
  strip_tac >>
  gs [word_ls_n2w])
QED


Theorem evaluate_min_exp_eq:
  ∀es s vname v ns res t.
    FLOOKUP s.locals vname = SOME (ValWord v) ∧
    (∀n. n < LENGTH es ⇒ ~MEM vname (var_exp (EL n es))) ∧
    MAP (eval s) es = MAP (SOME ∘ ValWord ∘ (n2w:num -> α word)) ns ∧
    EVERY (λn. n < dimword (:α)) ns ∧
    evaluate (minExp vname es,s) = (res,t) ⇒
    res = NONE ∧
    (es = [] ⇒ t = s) ∧
    (es ≠ [] ⇒
     t = s with locals :=
         s.locals |+
          (vname, ValWord ((n2w:num -> α word) (THE (list_min_option ns)))))
Proof
  rpt gen_tac >>
  strip_tac >>
  cases_on ‘es’ >> fs []
  >- (
    fs [minExp_def] >>
    fs [evaluate_def]) >>
  cases_on ‘ns’ >> fs [] >>
  fs [minExp_def] >>
  fs [evaluate_def] >>
  pairarg_tac >> fs [] >>
  rfs [] >>
  fs [is_valid_value_def] >>
  rfs [] >>
  fs [panSemTheory.shape_of_def] >> rveq >> fs [] >>
  qmatch_asmsub_abbrev_tac ‘evaluate (_,stInit)’ >>
  ‘FLOOKUP stInit.locals vname = SOME (ValWord (n2w h'))’ by (
    fs [Abbr ‘stInit’] >>
    fs [FLOOKUP_UPDATE]) >>
  last_x_assum mp_tac >>
  drule evaluate_minop_eq >>
  disch_then (qspecl_then [‘t'’, ‘t''’, ‘res’, ‘t’] mp_tac) >>
  fs [] >>
  impl_tac
  >- (
    conj_tac
    >- (
      rw [] >>
      last_x_assum (qspec_then ‘SUC n’ mp_tac) >>
      fs []) >>
    fs [Abbr ‘stInit’] >>
    fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
    rw [] >>
    match_mp_tac update_locals_not_vars_eval_eq >>
    last_x_assum (qspec_then ‘SUC n’ mp_tac) >>
    fs []) >>
  rpt strip_tac >> fs [] >>
  fs [list_min_option_def] >>
  cases_on ‘list_min_option t''’ >> fs [] >>
  fs [Abbr ‘stInit’, minOption_def] >>
  drule list_min_option_some_mem >>
  strip_tac >>
  fs [EVERY_MEM] >>
  first_x_assum (qspec_then ‘x’ mp_tac) >>
  fs [] >>
  strip_tac >>
  every_case_tac
  >- (
    fs [NOT_LESS] >>
    qsuff_tac ‘h' < x’ >- fs [] >>
    gs [word_lo_n2w]) >>
  fs [WORD_NOT_LOWER] >>
  gs [word_ls_n2w]
QED


Theorem every_conj_spec:
  ∀fm xs w.
    EVERY
    (λck. ∃n. FLOOKUP fm ck = SOME n ∧
              n < dimword (:α)) xs ⇒
    EVERY (λck. ck IN FDOM fm) xs
Proof
  rw [] >>
  fs [EVERY_MEM] >>
  rw [] >>
  last_x_assum drule >>
  strip_tac >> fs [FDOM_FLOOKUP]
QED


Theorem shape_of_resetClksVals_eq:
  ∀fm (clks:mlstring list) (tclks:mlstring list) (clkvals:'a v list).
    EVERY (λv. ∃w. v = ValWord w) clkvals /\
    LENGTH clks = LENGTH clkvals ⇒
    MAP ((λa. size_of_shape a) ∘ (λa. shape_of a))
        ((resetClksVals fm clks tclks):'a v list) =
    MAP ((λa. size_of_shape a) ∘ (λa. shape_of a)) clkvals
Proof
  rw [] >>
  fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
  fs [resetClksVals_def] >>
  rw [] >> fs [] >>
  qmatch_goalsub_abbrev_tac ‘MAP f _’ >>
  ‘EL n (MAP f clks) = f (EL n clks)’ by (
    match_mp_tac EL_MAP >>
    fs []) >>
  fs [Abbr ‘f’] >>
  pop_assum kall_tac >>
  fs [EVERY_MEM] >>
  drule EL_MEM >>
  strip_tac >>
  last_x_assum drule >>
  strip_tac >> fs [] >>
  fs [panSemTheory.shape_of_def]
QED

Theorem comp_input_term_correct:
  ∀s n cnds tclks dest wt s' t (clkvals:'a v list) clks.
    evalTerm s (SOME n)
             (Tm (Input n) cnds tclks dest wt) s' ∧
    FLOOKUP t.locals «clks» = SOME (Struct clkvals) ∧
    maxClksSize clkvals ∧
    clock_bound s.clocks clks (dimword (:'a)) ∧
    time_range wt (dimword (:'a)) ∧
    equiv_val s.clocks clks clkvals ∧
    valid_clks clks tclks wt ∧
    toString dest IN FDOM t.code ⇒
      evaluate (compTerm clks (Tm (Input n) cnds tclks dest wt), t) =
      (SOME (Return (retVal s clks tclks wt dest)),
       t with locals :=
       restore_from t FEMPTY [«waitTimes»; «newClks»; «wakeUpAt»; «waitSet»])
Proof
  rpt gen_tac >>
  strip_tac >>
  fs [clock_bound_def, time_range_def] >>
  drule every_conj_spec >>
  strip_tac >>
  drule eval_term_clkvals_equiv_reset_clkvals >>
  disch_then (qspec_then ‘clks’ assume_tac) >>
  fs [evalTerm_cases] >>
  rveq >> fs [] >>
  fs [compTerm_def] >>
  cases_on ‘wt’
  >- ( (* wait set is disabled *)
   fs [panLangTheory.decs_def] >>
   fs [evaluate_def] >>
   fs [eval_def] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >> rveq >>
   rfs [] >> fs [] >>
   qmatch_asmsub_abbrev_tac ‘OPT_MMAP (λa. eval stInit a) _’ >>
   ‘OPT_MMAP (λa. eval stInit a)
      (resetTermClocks «clks» clks tclks) =
    SOME (resetClksVals s.clocks clks tclks)’ by (
     match_mp_tac opt_mmap_resetTermClocks_eq_resetClksVals >>
     qexists_tac ‘clkvals’ >> rfs [] >>
     fs [Abbr ‘stInit’] >>
     rfs [FLOOKUP_UPDATE]) >>
   fs [] >>
   pop_assum kall_tac >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   fs [emptyConsts_def] >>
   fs [OPT_MMAP_def] >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   fs [panLangTheory.nested_seq_def] >>
   fs [evaluate_def] >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   fs [eval_def] >>
   fs [indicesOf_def, waitTimes_def, minExp_def] >>
   pop_assum mp_tac >>
   rewrite_tac [OPT_MMAP_def] >>
   strip_tac >>
   fs [is_valid_value_def] >>
   fs [FLOOKUP_UPDATE, FDOM_FLOOKUP] >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   fs [evaluate_def] >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   qmatch_asmsub_abbrev_tac ‘OPT_MMAP (λa. eval stReset a) _’ >>
   fs [OPT_MMAP_def] >>
   fs [eval_def] >>
   fs [Abbr ‘stReset’, FLOOKUP_UPDATE, FDOM_FLOOKUP] >>
   rfs [] >>
   fs [panSemTheory.shape_of_def, panLangTheory.size_of_shape_def] >>
   fs [GSYM FDOM_FLOOKUP] >>
   drule maxClksSize_reset_clks_eq >>
   disch_then (qspecl_then [‘clkvals’, ‘tclks’] mp_tac) >>
   fs [] >> strip_tac >>
   fs [maxClksSize_def, MAP_MAP_o, ETA_AX] >>
   pop_assum kall_tac >>
   rveq >> fs [] >> rfs [] >> rveq >> fs [] >>
   fs [empty_locals_def, retVal_def] >>
   fs [restore_from_def]) >>
  (* some maintenance to replace h::t' to wt *)
  qmatch_goalsub_abbrev_tac ‘emptyConsts (LENGTH wt)’ >>
  ‘(case wt of [] => Const 1w | v2::v3 => Const 0w) =
   (Const 0w): 'a panLang$exp’ by fs [Abbr ‘wt’] >>
  fs [] >>
  pop_assum kall_tac >>
  fs [panLangTheory.decs_def] >>
  fs [evaluate_def] >>
  fs [eval_def] >>
  pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >> rveq >>
  rfs [] >> fs [] >>
  qmatch_asmsub_abbrev_tac ‘OPT_MMAP (λa. eval stInit a) _’ >>
  ‘OPT_MMAP (λa. eval stInit a)
   (resetTermClocks «clks» clks tclks) =
   SOME (resetClksVals s.clocks clks tclks)’ by (
    match_mp_tac opt_mmap_resetTermClocks_eq_resetClksVals >>
    qexists_tac ‘clkvals’ >> rfs [] >>
    fs [Abbr ‘stInit’] >>
    rfs [FLOOKUP_UPDATE]) >>
  fs [] >>
  pop_assum kall_tac >>
  pairarg_tac >> fs [] >> rveq >> rfs [] >>
  fs [eval_empty_const_eq_empty_vals] >>
  pairarg_tac >> fs [] >> rveq >> rfs [] >>
  fs [panLangTheory.nested_seq_def] >>
  fs [evaluate_def] >>
  pairarg_tac >> fs [] >> rveq >> rfs [] >>
  qmatch_asmsub_abbrev_tac ‘eval stReset _’ >>
  fs [eval_def] >>
  (* waitimes eq eval diffs *)
  ‘OPT_MMAP (λa. eval stReset a)
   (waitTimes (MAP FST wt)
    (MAP (λn. Field n (Var «newClks» ))
     (indicesOf clks (MAP SND wt)))) =
   SOME (MAP ((λw. ValWord w) ∘ n2w ∘ THE ∘ evalDiff
              (s with clocks := resetClocks s.clocks tclks)) wt)’ by (
    match_mp_tac calculate_wait_times_eq >>
    qexists_tac ‘resetClksVals s.clocks clks tclks’ >>
    rfs [Abbr ‘stReset’] >>
    rewrite_tac [FLOOKUP_UPDATE] >>
    fs [] >>
    fs [equiv_val_def] >>
    last_x_assum assume_tac >>
    drule fdom_reset_clks_eq_clks >>
    strip_tac >>
    rfs [valid_clks_def] >>
    fs [EVERY_MEM] >>
    rw [] >>
    last_x_assum (qspec_then ‘e’ mp_tac) >>
    fs [] >>
    cases_on ‘e’ >> fs [] >>
    strip_tac >>
    fs [] >>
    match_mp_tac flookup_reset_clks_leq >>
    fs []) >>
  fs [] >>
  pop_assum kall_tac >>
  qmatch_asmsub_abbrev_tac ‘is_valid_value tt _ wtval’ >>
  ‘is_valid_value tt «waitTimes» wtval’ by (
    fs [Abbr ‘tt’, Abbr ‘wtval’] >>
    fs [is_valid_value_def] >>
    fs [FLOOKUP_UPDATE] >>
    fs [panSemTheory.shape_of_def] >>
    fs [emptyVals_def, emptyConsts_def] >>
    fs [MAP_MAP_o, GSYM MAP_K_REPLICATE, MAP_EQ_f] >>
    rw [] >>
    fs [shape_of_def]) >>
  fs [] >>
  pairarg_tac >> fs [] >> rveq >> fs [] >>
  qmatch_asmsub_abbrev_tac ‘evaluate (minExp _ es, stWait)’ >>
  ‘FLOOKUP stWait.locals «wakeUpAt» = SOME (ValWord 0w)’ by
    fs [Abbr ‘stWait’, FLOOKUP_UPDATE] >>
  drule evaluate_min_exp_eq >>
  disch_then (
    qspecl_then [
        ‘es’,
        ‘MAP (THE o evalDiff (s with clocks := resetClocks s.clocks tclks)) wt’,
        ‘res''’, ‘s1'’] mp_tac) >>
  impl_tac
  >- (
   rfs [] >>
   conj_tac
   >- (
    rw [] >>
    fs [Abbr ‘es’] >>
    fs [panLangTheory.var_exp_def]) >>
   conj_tac
   >- (
    fs [Abbr ‘stWait’, Abbr ‘es’] >>
    fs [Abbr ‘wtval’] >>
    fs [MAP_MAP_o] >>
    fs [MAPi_enumerate_MAP] >>
    fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
    fs [LENGTH_enumerate] >>
    rw [] >>
    pairarg_tac >> fs [] >>
    ‘EL n (enumerate 0 wt) = (n+0,EL n wt)’ by (
      match_mp_tac EL_enumerate >>
      fs []) >>
    fs [] >>
    pop_assum kall_tac >>
    fs [eval_def] >>
    fs [FLOOKUP_UPDATE] >>
    rveq >> rfs [] >>
    qmatch_goalsub_abbrev_tac ‘MAP ff _’ >>
    ‘EL i (MAP ff wt) = ff (EL i wt)’ by (
      match_mp_tac EL_MAP >>
      fs []) >>
    fs [Abbr ‘ff’]) >>
   fs [EVERY_MAP, EVERY_MEM] >>
   gen_tac >>
   strip_tac >>
   cases_on ‘x’ >>
   fs [evalDiff_def, evalExpr_def] >>
   cases_on ‘MEM r tclks’
   >- (
    drule reset_clks_mem_flookup_zero >>
    disch_then (qspec_then ‘s.clocks’ assume_tac) >>
    fs [] >>
    fs [minusT_def] >>
    first_x_assum (qspec_then ‘(q,r)’ mp_tac) >>
    fs []) >>
   rfs [valid_clks_def] >>
   rfs [EVERY_MEM] >>
   ‘MEM r clks’ by (
     ‘MEM r (MAP SND wt)’ by (
       fs [MEM_MAP] >>
       qexists_tac ‘(q,r)’ >> fs []) >>
     res_tac >> gs []) >>
   res_tac >> rfs [] >>
   drule reset_clks_not_mem_flookup_same >>
   disch_then (qspec_then ‘tclks’ mp_tac) >>
   rfs [] >>
   strip_tac >>
   fs [minusT_def] >>
   last_x_assum (qspec_then ‘(q,r)’ mp_tac) >>
   fs [] >>
   strip_tac >>
   last_x_assum (qspec_then ‘(q,r)’ mp_tac) >>
   gs []) >>
  strip_tac >> fs [] >>
  ‘es ≠ []’ by fs [Abbr ‘wt’, Abbr ‘es’] >>
  fs [] >>
  pairarg_tac >> fs [] >> rveq >> rfs [] >>
  unabbrev_all_tac >> fs [] >> rveq >> rfs [] >>
  fs [OPT_MMAP_def, eval_def, FLOOKUP_UPDATE] >>
  rfs [FDOM_FLOOKUP] >>
  rfs [] >>
  fs [panLangTheory.size_of_shape_def, panSemTheory.shape_of_def] >>
  fs [MAP_MAP_o] >>
  qmatch_asmsub_abbrev_tac ‘SUM ss’ >>
  ‘ss =
   MAP ((λa. size_of_shape a) ∘ (λa. shape_of a)) clkvals’ by (
    fs [Abbr ‘ss’] >>
    match_mp_tac shape_of_resetClksVals_eq >>
    rfs [equiv_val_def] >>
    fs [EVERY_MEM] >>
    rw [] >>
    fs [MEM_MAP]) >>
  rfs [maxClksSize_def] >>
  qmatch_asmsub_abbrev_tac ‘ss = tt’ >>
  ‘SUM ss + 3 ≤ 32’ by fs [ETA_AX] >>
  fs [] >>
  pop_assum kall_tac >>
  fs [empty_locals_def] >>
  rveq >> fs [] >> rveq >> rfs [] >>
  fs [restore_from_def] >>
  fs [retVal_def] >>
  fs [calculate_wtime_def]
QED


Theorem ffi_eval_state_thm:
  !ffi_name s (res:'a result option) t nffi nbytes bytes.
    evaluate
    (ExtCall ffi_name «ptr1» «len1» «ptr2» «len2»,s) = (res,t)∧
    well_behaved_ffi ffi_name s nffi nbytes bytes
     (w2n (ffiBufferSize:'a word)) (dimword (:α))  /\
    FLOOKUP s.locals «ptr1» = SOME (ValWord 0w) ∧
    FLOOKUP s.locals «len1» = SOME (ValWord 0w) ∧
    FLOOKUP s.locals «ptr2» = SOME (ValWord ffiBufferAddr) ∧
    FLOOKUP s.locals «len2» = SOME (ValWord ffiBufferSize) ==>
    res = NONE ∧ t = ffi_return_state s ffi_name bytes nbytes nffi
Proof
  rpt gen_tac >>
  strip_tac >>
  fs [well_behaved_ffi_def] >>
  gs [evaluate_def] >>
  gs [read_bytearray_def] >>
  gs [read_bytearray_def, ffiBufferAddr_def] >>
  dxrule LESS_MOD >>
  strip_tac >> rfs [] >>
  pop_assum kall_tac >>
  rfs [ffiTheory.call_FFI_def] >>
  rveq >> fs [] >>
  gs [ffi_return_state_def]
QED


Theorem comp_output_term_correct:
  ∀s out cnds tclks dest wt s' t (clkvals:'a v list) clks
   ffi_name nffi nbytes bytes.
    evalTerm s NONE
             (Tm (Output out) cnds tclks dest wt) s' ∧
    FLOOKUP t.locals «clks» = SOME (Struct clkvals) ∧
    maxClksSize clkvals ∧
    clock_bound s.clocks clks (dimword (:'a)) ∧
    time_range wt (dimword (:'a)) ∧
    equiv_val s.clocks clks clkvals ∧
    valid_clks clks tclks wt ∧
    toString dest IN FDOM t.code ∧
    well_behaved_ffi (strlit (toString out)) t nffi nbytes bytes
      (w2n (ffiBufferSize:'a word)) (dimword (:α)) ⇒
      evaluate (compTerm clks (Tm (Output out) cnds tclks dest wt), t) =
      (SOME (Return (retVal s clks tclks wt dest)),
       t with
       <|locals :=
         restore_from t FEMPTY [«len2»; «ptr2»; «len1»; «ptr1»;
                                «waitTimes»; «newClks»; «wakeUpAt»; «waitSet»];
         memory := write_bytearray 4000w nbytes t.memory t.memaddrs t.be;
         ffi := nffi_state t nffi out bytes nbytes|>)
Proof
  rpt gen_tac >>
  strip_tac >>
  fs [clock_bound_def, time_range_def] >>
  drule every_conj_spec >>
  strip_tac >>
  drule eval_term_clkvals_equiv_reset_clkvals >>
  disch_then (qspec_then ‘clks’ assume_tac) >>
  fs [evalTerm_cases] >>
  rveq >> fs [] >>
  fs [compTerm_def] >>
  cases_on ‘wt’
  >- ( (* wait set is disabled *)
   fs [panLangTheory.decs_def] >>
   fs [evaluate_def, eval_def] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >> rveq >>
   rfs [] >> fs [] >>
   qmatch_asmsub_abbrev_tac ‘OPT_MMAP (λa. eval stInit a) _’ >>
   ‘OPT_MMAP (λa. eval stInit a)
      (resetTermClocks «clks» clks tclks) =
    SOME (resetClksVals s.clocks clks tclks)’ by (
     match_mp_tac opt_mmap_resetTermClocks_eq_resetClksVals >>
     qexists_tac ‘clkvals’ >> rfs [] >>
     fs [Abbr ‘stInit’] >>
     rfs [FLOOKUP_UPDATE]) >>
   fs [] >>
   pop_assum kall_tac >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   fs [emptyConsts_def] >>
   fs [OPT_MMAP_def] >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   fs [panLangTheory.nested_seq_def] >>
   fs [Once evaluate_def] >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   fs [Once evaluate_def] >>
   fs [eval_def] >>
   fs [indicesOf_def, waitTimes_def, minExp_def] >>
   pop_assum mp_tac >>
   rewrite_tac [OPT_MMAP_def] >>
   strip_tac >>
   fs [is_valid_value_def] >>
   fs [FLOOKUP_UPDATE, FDOM_FLOOKUP] >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   fs [Once evaluate_def] >> rveq >> fs [] >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   fs [Once evaluate_def] >> rveq >> fs [] >>
   fs [eval_def] >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   fs [Once evaluate_def] >> rveq >> fs [] >>
   fs [eval_def] >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   fs [Once evaluate_def] >> rveq >> fs [] >>
   fs [eval_def] >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   fs [Once evaluate_def] >> rveq >> fs [] >>
   fs [eval_def] >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   fs [Once evaluate_def] >> rveq >> fs [] >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   drule ffi_eval_state_thm >>
   disch_then (qspecl_then
               [‘nffi’, ‘nbytes’, ‘bytes’] mp_tac) >>
   impl_tac
   >- (
    fs [FLOOKUP_UPDATE] >>
    fs [well_behaved_ffi_def]) >>
   strip_tac >> fs [] >> rveq >> fs [] >>
   pop_assum kall_tac >>
   fs [ffi_return_state_def] >>
   fs [evaluate_def] >>
   fs [eval_def] >>
   qmatch_asmsub_abbrev_tac ‘OPT_MMAP (λa. eval stReset a) _’ >>
   fs [OPT_MMAP_def] >>
   fs [eval_def] >>
   fs [Abbr ‘stReset’, FLOOKUP_UPDATE, FDOM_FLOOKUP] >>
   rfs [] >>
   fs [panSemTheory.shape_of_def, panLangTheory.size_of_shape_def] >>
   fs [GSYM FDOM_FLOOKUP] >>
   drule maxClksSize_reset_clks_eq >>
   disch_then (qspecl_then [‘clkvals’, ‘tclks’] mp_tac) >>
   fs [] >> strip_tac >>
   fs [maxClksSize_def, MAP_MAP_o, ETA_AX] >>
   pop_assum kall_tac >>
   rveq >> fs [] >> rfs [] >> rveq >> fs [] >>
   fs [empty_locals_def, retVal_def] >>
   fs [nffi_state_def, restore_from_def]) >>
  (* some maintenance to replace h::t' to wt *)
  qmatch_goalsub_abbrev_tac ‘emptyConsts (LENGTH wt)’ >>
  ‘(case wt of [] => Const 1w | v2::v3 => Const 0w) =
   (Const 0w): 'a panLang$exp’ by fs [Abbr ‘wt’] >>
  fs [] >>
  pop_assum kall_tac >>
  fs [panLangTheory.decs_def] >>
  fs [Once evaluate_def] >> rveq >> fs [] >>
  fs [eval_def] >>
  pairarg_tac >> fs [] >> rveq >> rfs [] >>
  fs [Once evaluate_def] >> rveq >> fs [] >>
  fs [eval_def] >>
  pairarg_tac >> fs [] >> rveq >> rfs [] >>
  fs [Once evaluate_def] >> rveq >> fs [] >>
  fs [eval_def] >>
  rfs [] >> fs [] >>
  qmatch_asmsub_abbrev_tac ‘OPT_MMAP (λa. eval stInit a) _’ >>
  ‘OPT_MMAP (λa. eval stInit a)
   (resetTermClocks «clks» clks tclks) =
   SOME (resetClksVals s.clocks clks tclks)’ by (
    match_mp_tac opt_mmap_resetTermClocks_eq_resetClksVals >>
    qexists_tac ‘clkvals’ >> rfs [] >>
    fs [Abbr ‘stInit’] >>
    rfs [FLOOKUP_UPDATE]) >>
  fs [] >>
  pop_assum kall_tac >>
  pairarg_tac >> fs [] >> rveq >> rfs [] >>
  fs [Once evaluate_def] >> rveq >> fs [] >>
  fs [eval_def] >>
  fs [eval_empty_const_eq_empty_vals] >>
  pairarg_tac >> fs [] >> rveq >> rfs [] >>
  fs [panLangTheory.nested_seq_def] >>
  fs [Once evaluate_def] >> rveq >> fs [] >>
  fs [eval_def] >>
  pairarg_tac >> fs [] >> rveq >> rfs [] >>
  fs [Once evaluate_def] >> rveq >> fs [] >>
  qmatch_asmsub_abbrev_tac ‘eval stReset _’ >>
  fs [eval_def] >>
  (* waitimes eq eval diffs *)
  ‘OPT_MMAP (λa. eval stReset a)
   (waitTimes (MAP FST wt)
    (MAP (λn. Field n (Var «newClks» ))
     (indicesOf clks (MAP SND wt)))) =
   SOME (MAP ((λw. ValWord w) ∘ n2w ∘ THE ∘ evalDiff
              (s with clocks := resetClocks s.clocks tclks)) wt)’ by (
    match_mp_tac calculate_wait_times_eq >>
    qexists_tac ‘resetClksVals s.clocks clks tclks’ >>
    rfs [Abbr ‘stReset’] >>
    rewrite_tac [FLOOKUP_UPDATE] >>
    fs [] >>
    fs [equiv_val_def] >>
    last_x_assum assume_tac >>
    drule fdom_reset_clks_eq_clks >>
    strip_tac >>
    rfs [valid_clks_def] >>
    fs [EVERY_MEM] >>
    rw [] >>
    last_x_assum (qspec_then ‘e’ mp_tac) >>
    fs [] >>
    cases_on ‘e’ >> fs [] >>
    strip_tac >>
    fs [] >>
    match_mp_tac flookup_reset_clks_leq >>
    fs []) >>
  fs [] >>
  pop_assum kall_tac >>
  qmatch_asmsub_abbrev_tac ‘is_valid_value tt _ wtval’ >>
  ‘is_valid_value tt «waitTimes» wtval’ by (
    fs [Abbr ‘tt’, Abbr ‘wtval’] >>
    fs [is_valid_value_def] >>
    fs [FLOOKUP_UPDATE] >>
    fs [panSemTheory.shape_of_def] >>
    fs [emptyVals_def, emptyConsts_def] >>
    fs [MAP_MAP_o, GSYM MAP_K_REPLICATE, MAP_EQ_f] >>
    rw [] >>
    fs [shape_of_def]) >>
  fs [] >>
  pairarg_tac >> fs [] >> rveq >> fs [] >>
  qmatch_asmsub_abbrev_tac ‘evaluate (minExp _ es, stWait)’ >>
  ‘FLOOKUP stWait.locals «wakeUpAt» = SOME (ValWord 0w)’ by
    fs [Abbr ‘stWait’, FLOOKUP_UPDATE] >>
  drule evaluate_min_exp_eq >>
  disch_then (
    qspecl_then [
        ‘es’,
        ‘MAP (THE ∘ evalDiff (s with clocks := resetClocks s.clocks tclks)) wt’,
        ‘res''’, ‘s1'’] mp_tac) >>
  impl_tac
  >- (
   rfs [] >>
   conj_tac
   >- (
    rw [] >>
    fs [Abbr ‘es’] >>
    fs [panLangTheory.var_exp_def]) >>
   conj_tac
   >- (
    fs [Abbr ‘stWait’, Abbr ‘es’] >>
    fs [Abbr ‘wtval’] >>
    fs [MAP_MAP_o] >>
    fs [MAPi_enumerate_MAP] >>
    fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
    fs [LENGTH_enumerate] >>
    rw [] >>
    pairarg_tac >> fs [] >>
    ‘EL n (enumerate 0 wt) = (n+0,EL n wt)’ by (
      match_mp_tac EL_enumerate >>
      fs []) >>
    fs [] >>
    pop_assum kall_tac >>
    fs [eval_def] >>
    fs [FLOOKUP_UPDATE] >>
    rveq >> rfs [] >>
    qmatch_goalsub_abbrev_tac ‘MAP ff _’ >>
    ‘EL i (MAP ff wt) = ff (EL i wt)’ by (
      match_mp_tac EL_MAP >>
      fs []) >>
    fs [Abbr ‘ff’]) >>
   fs [EVERY_MAP, EVERY_MEM] >>
   gen_tac >>
   strip_tac >>
   cases_on ‘x’ >>
   fs [evalDiff_def, evalExpr_def] >>
   cases_on ‘MEM r tclks’
   >- (
    drule reset_clks_mem_flookup_zero >>
    disch_then (qspec_then ‘s.clocks’ assume_tac) >>
    fs [] >>
    fs [minusT_def] >>
    first_x_assum (qspec_then ‘(q,r)’ mp_tac) >>
    fs []) >>
   rfs [valid_clks_def] >>
   rfs [EVERY_MEM] >>
   ‘MEM r clks’ by (
     ‘MEM r (MAP SND wt)’ by (
       fs [MEM_MAP] >>
       qexists_tac ‘(q,r)’ >> fs []) >>
     res_tac >> gs []) >>
   res_tac >> rfs [] >>
   drule reset_clks_not_mem_flookup_same >>
   disch_then (qspec_then ‘tclks’ mp_tac) >>
   rfs [] >>
   strip_tac >>
   fs [minusT_def] >>
   last_x_assum (qspec_then ‘(q,r)’ mp_tac) >>
   fs [] >>
   strip_tac  >>
   last_x_assum (qspec_then ‘(q,r)’ mp_tac) >>
   fs []) >>
  strip_tac >> fs [] >>
  ‘es ≠ []’ by fs [Abbr ‘wt’, Abbr ‘es’] >>
  fs [] >> rveq >> rfs [] >>
  fs [Once evaluate_def] >> rveq >> fs [] >>
  pairarg_tac >> fs [] >> rveq >> rfs [] >>
  fs [Once evaluate_def] >> rveq >> fs [] >>
  fs [eval_def] >>
  pairarg_tac >> fs [] >> rveq >> rfs [] >>
  fs [Once evaluate_def] >> rveq >> fs [] >>
  fs [eval_def] >>
  pairarg_tac >> fs [] >> rveq >> rfs [] >>
  fs [Once evaluate_def] >> rveq >> fs [] >>
  fs [eval_def] >>
  pairarg_tac >> fs [] >> rveq >> rfs [] >>
  fs [Once evaluate_def] >> rveq >> fs [] >>
  fs [eval_def] >>
  pairarg_tac >> fs [] >> rveq >> rfs [] >>
  fs [Once evaluate_def] >> rveq >> fs [] >>
  pairarg_tac >> fs [] >> rveq >> rfs [] >>
  unabbrev_all_tac >> fs [] >> rveq >> rfs [] >>
  drule ffi_eval_state_thm >>
  disch_then (qspecl_then
              [‘nffi’, ‘nbytes’, ‘bytes’] mp_tac) >>
  impl_tac
  >- (
  fs [FLOOKUP_UPDATE] >>
  fs [well_behaved_ffi_def]) >>
  strip_tac >> fs [] >> rveq >> fs [] >>
  pop_assum kall_tac >>
  fs [ffi_return_state_def] >>
  fs [evaluate_def] >>
  fs [eval_def] >>
  qmatch_asmsub_abbrev_tac ‘OPT_MMAP (λa. eval stReset a) _’ >>
  fs [OPT_MMAP_def] >>
  fs [eval_def] >>
  fs [Abbr ‘stReset’, FLOOKUP_UPDATE, FDOM_FLOOKUP] >>
  rfs [] >>
  fs [panLangTheory.size_of_shape_def, panSemTheory.shape_of_def] >>
  fs [MAP_MAP_o] >>
  qmatch_asmsub_abbrev_tac ‘SUM ss’ >>
  ‘ss =
   MAP ((λa. size_of_shape a) ∘ (λa. shape_of a)) clkvals’ by (
    fs [Abbr ‘ss’] >>
    match_mp_tac shape_of_resetClksVals_eq >>
    rfs [equiv_val_def] >>
    fs [EVERY_MEM] >>
    rw [] >>
    fs [MEM_MAP]) >>
  rfs [maxClksSize_def] >>
  qmatch_asmsub_abbrev_tac ‘ss = tt’ >>
  ‘SUM ss + 3 ≤ 32’ by fs [ETA_AX] >>
  fs [] >>
  pop_assum kall_tac >>
  fs [empty_locals_def] >>
  rveq >> fs [] >> rveq >> rfs [] >>
  fs [restore_from_def] >>
  fs [retVal_def] >>
  fs [calculate_wtime_def] >>
  fs [nffi_state_def]
QED


Theorem comp_term_correct:
  ∀s io ioAct cnds tclks dest wt s' t (clkvals:'a v list) clks.
    evalTerm s io
             (Tm ioAct cnds tclks dest wt) s' ∧
    FLOOKUP t.locals «clks» = SOME (Struct clkvals) ∧
    maxClksSize clkvals ∧
    clock_bound s.clocks clks (dimword (:'a)) ∧
    time_range wt (dimword (:'a)) ∧
    equiv_val s.clocks clks clkvals ∧
    valid_clks clks tclks wt ∧
    toString dest IN FDOM t.code ⇒
    case (io,ioAct) of
     | (SOME _,Input n) =>
         evaluate (compTerm clks (Tm (Input n) cnds tclks dest wt), t) =
         (SOME (Return (retVal s clks tclks wt dest)),
          (* we can throw away the locals *)
          t with locals :=
          restore_from t FEMPTY [«waitTimes»; «newClks»; «wakeUpAt»; «waitSet»])
     | (NONE, Output out) =>
         (∀nffi nbytes bytes.
            well_behaved_ffi (strlit (toString out)) t nffi nbytes bytes
              (w2n (ffiBufferSize:'a word)) (dimword (:α)) ⇒
            evaluate (compTerm clks (Tm (Output out) cnds tclks dest wt), t) =
            (SOME (Return (retVal s clks tclks wt dest)),
             t with
               <|locals :=
                 restore_from t FEMPTY [«len2»; «ptr2»; «len1»; «ptr1»;
                                        «waitTimes»; «newClks»; «wakeUpAt»; «waitSet»];
                 memory := write_bytearray 4000w nbytes t.memory t.memaddrs t.be;
                 ffi := nffi_state t nffi out bytes nbytes|>))
     | (_,_) => F
Proof
  rw [] >>
  cases_on ‘ioAct’ >>
  cases_on ‘io’ >>
  fs [] >>
  TRY (fs[evalTerm_cases] >> NO_TAC)
  >- (
    drule eval_term_inpput_ios_same >>
    strip_tac >> rveq >>
    imp_res_tac comp_input_term_correct) >>
  imp_res_tac comp_output_term_correct
QED


Theorem comp_exp_correct:
  ∀s e n clks t:('a,'b)panSem$state clkvals.
    evalExpr s e = SOME n ∧
    EVERY (λck. MEM ck clks) (exprClks [] e) ∧
    FLOOKUP t.locals «clks» = SOME (Struct clkvals) ∧
    equiv_val s.clocks clks clkvals ⇒
    eval t (compExp clks «clks» e) = SOME (ValWord (n2w n))
Proof
  ho_match_mp_tac evalExpr_ind >>
  rpt gen_tac >>
  strip_tac >>
  rpt gen_tac >>
  strip_tac >>
  cases_on ‘e’ >> fs []
  >- (
    fs [evalExpr_def] >>
    fs [compExp_def] >>
    fs [eval_def])
  >- (
    fs [evalExpr_def, timeLangTheory.exprClks_def] >>
    fs [compExp_def] >>
    fs [equiv_val_def] >> rveq >> gs [] >>
    fs [eval_def] >>
    ‘findi m clks < LENGTH clks’ by (
      match_mp_tac MEM_findi >>
      gs []) >>
    fs [] >>
    qmatch_goalsub_abbrev_tac ‘EL nn (MAP ff _)’ >>
    ‘EL nn (MAP ff clks) = ff (EL nn clks)’ by (
      match_mp_tac EL_MAP >>
      fs []) >>
    fs [Abbr ‘ff’, Abbr ‘nn’] >>
    pop_assum kall_tac >>
    ‘EL (findi m clks) clks = m’ by (
      match_mp_tac EL_findi >>
      gs []) >>
    fs []) >>
  qpat_x_assum ‘evalExpr _ _ = _’ mp_tac >>
  rewrite_tac [Once evalExpr_def] >>
  fs [] >>
  TOP_CASE_TAC >> fs [] >>
  TOP_CASE_TAC >> fs [] >>
  strip_tac >>
  qpat_x_assum ‘EVERY _ (exprClks [] _)’ mp_tac >>
  once_rewrite_tac [timeLangTheory.exprClks_def] >>
  fs [] >>
  strip_tac >>
  ‘EVERY (λck. MEM ck clks) (exprClks [] e0) ∧
   EVERY (λck. MEM ck clks) (exprClks [] e')’ by (
    drule exprClks_accumulates >>
    fs [] >>
    strip_tac >>
    fs [EVERY_MEM] >>
    rw [] >>
    fs [] >>
    drule exprClks_sublist_accum >>
    fs []) >>
  fs [] >>
  last_x_assum drule >>
  last_x_assum drule >>
  fs [] >>
  disch_then (qspecl_then [‘t’, ‘clkvals’] assume_tac) >>
  disch_then (qspecl_then [‘t’, ‘clkvals’] assume_tac) >>
  gs [] >>
  rewrite_tac [compExp_def] >>
  fs [eval_def] >>
  gs [OPT_MMAP_def] >>
  fs [wordLangTheory.word_op_def] >>
  match_mp_tac EQ_SYM >>
  rewrite_tac [Once evalExpr_def] >>
  fs [minusT_def] >>
  rveq >> gs [] >>
  drule n2w_sub >>
  fs []
QED


Definition code_installed_def:
  code_installed code prog <=>
  ∀loc tms.
    MEM (loc,tms) prog ⇒
    let clks = clksOf prog;
        n = LENGTH clks
    in
      FLOOKUP code (toString loc) =
      SOME ([(«clks», genShape n)],
            compTerms clks «clks» tms)
End


Definition ffi_vars_def:
  ffi_vars fm  ⇔
  FLOOKUP fm «ptr1» = SOME (ValWord 0w) ∧
  FLOOKUP fm «len1» = SOME (ValWord 0w) ∧
  FLOOKUP fm «ptr2» = SOME (ValWord ffiBufferAddr) ∧
  FLOOKUP fm «len2» = SOME (ValWord ffiBufferSize)
End


Definition time_vars_def:
  time_vars fm ⇔
  (∃st. FLOOKUP fm «sysTime»  = SOME (ValWord st)) ∧
  (∃wt. FLOOKUP fm «wakeUpAt» = SOME (ValWord wt)) ∧
  (∃io. FLOOKUP fm «isInput»  = SOME (ValWord io))
End


(* for easier reasoning *)
Definition clkvals_rel_def:
  clkvals_rel fm xs ys (n:num) ⇔
    MAP (λ(x,y). y + THE (FLOOKUP fm x)) (ZIP (xs,ys)) =
    MAP (λx. n) ys ∧
    EVERY (\x. THE (FLOOKUP fm x) <= n) xs
End


(*
Definition clkvals_rel_def:
  clkvals_rel fm xs ys (n:num) ⇔
    (MAP2 (λx y. THE (FLOOKUP fm x) + y) xs ys =
     REPLICATE (LENGTH ys) n) ∧
    EVERY (\x. THE (FLOOKUP fm x) <= n) xs
End
*)

Definition clocks_rel_def:
  clocks_rel sclocks tlocals clks stime ⇔
  ∃ns.
    FLOOKUP tlocals «clks» =
    SOME (Struct (MAP (ValWord o n2w) ns)) ∧
    LENGTH clks = LENGTH ns ∧
    clkvals_rel sclocks clks ns stime
End


Definition active_low_def:
  (active_low NONE = 1w) ∧
  (active_low (SOME _) = 0w)
End


Definition add_time_def:
  (add_time t NONE     = SOME (ValWord 0w)) ∧
  (add_time t (SOME n) = SOME (ValWord (t + n2w n)))
End

(*
Definition equiv_labels_def:
  equiv_labels fm v sloc ⇔
    FLOOKUP fm v = SOME (ValLabel (toString sloc))
End


Definition equiv_flags_def:
  equiv_flags fm v n ⇔
    FLOOKUP fm v = SOME (ValWord (active_low n))
End
*)

Definition equivs_def:
  equivs fm loc wt ⇔
  FLOOKUP fm «loc» = SOME (ValLabel (toString loc)) ∧
  FLOOKUP fm «waitSet» = SOME (ValWord (active_low wt))
End

(*
Definition equivs_def:
  equivs fm loc wt io ⇔
    equiv_labels fm «loc» loc ∧
    equiv_flags  fm «waitSet» wt ∧
    equiv_flags  fm «isInput» io
End
*)

Definition time_seq_def:
  time_seq (f:num -> num # bool) m ⇔
  (∀n. ∃d. FST (f (SUC n)) = FST (f n) + d) ∧
  (∀n. FST (f n) < m)
End


Definition mem_config_def:
  mem_config (mem:'a word -> 'a word_lab) (adrs:('a word) set) be ⇔
    (∃bytes. read_bytearray
             (ffiBufferAddr:'a word)
             (w2n (ffiBufferSize:'a word))
             (mem_load_byte mem adrs be) = SOME bytes) ∧
    ffiBufferAddr ∈ adrs ∧
    ffiBufferAddr + bytes_in_word ∈ adrs
End


Definition state_rel_def:
  state_rel clks s (t:('a,time_input) panSem$state) ⇔
    equivs t.locals s.location s.waitTime ∧
    ffi_vars t.locals ∧  time_vars t.locals ∧
    mem_config t.memory t.memaddrs t.be ∧
    dimindex (:α) DIV 8 + 1 <  dimword (:α) ∧
    LENGTH clks ≤ 29 ∧
    clock_bound s.clocks clks (dimword (:'a)) ∧
    let
      ffi = t.ffi.ffi_state;
      io_events = t.ffi.io_events;
      (tm,io_flg) = ffi 0
    in
      t.ffi = build_ffi ffi io_events ∧
      time_seq ffi (dimword (:'a)) ∧
      clocks_rel s.clocks t.locals clks tm
End

Definition mem_call_ffi_def:
  mem_call_ffi mem adrs be bytes ffi  =
  write_bytearray (ffiBufferAddr:'a word)
                  (k2mw (LENGTH bytes − 1) (FST (ffi (0:num))) ++
                   [if SND (ffi 0) then 0w:word8 else 1w])
                  mem adrs be
End


Definition ffi_call_ffi_def:
  ffi_call_ffi ffi bytes  =
    ffi with
        <|ffi_state := next_ffi ffi.ffi_state;
          io_events := ffi.io_events ++
          [IO_event "get_ffi" []
           (ZIP
            (bytes,
             k2mw (LENGTH bytes − 1) (FST (ffi.ffi_state (0:num))) ++
                  [if SND (ffi.ffi_state 0) then 0w:word8 else 1w]))]|>

End


Definition nexts_ffi_def:
  nexts_ffi m (f:num -> (num # bool)) =
  λn. f (n+m)
End

Theorem state_rel_imp_time_seq_ffi:
  ∀cks s t.
    state_rel cks s (t:('a,time_input) panSem$state) ⇒
    time_seq t.ffi.ffi_state (dimword (:'a))
Proof
  rw [state_rel_def] >>
  pairarg_tac >> gs []
QED


Theorem state_rel_imp_ffi_vars:
  ∀cks s t.
    state_rel cks s (t:('a,time_input) panSem$state) ⇒
    ffi_vars t.locals
Proof
  rw [state_rel_def]
QED


Theorem time_seq_mono:
  ∀m n f a.
    n ≤ m ∧
    time_seq f a ⇒
    FST (f n) ≤ FST (f m)
Proof
  Induct >>
  rw [] >>
  fs [time_seq_def] >>
  fs [LE] >>
  last_x_assum (qspecl_then [‘n’, ‘f’, ‘a’] mp_tac) >>
  impl_tac
  >- gs [] >>
  strip_tac >>
  ‘FST (f m) ≤ FST (f (SUC m))’ suffices_by gs [] >>
  last_x_assum (qspec_then ‘m’ mp_tac) >>
  gs []
QED



Theorem step_delay_eval_wait_not_zero:
  !t.
    FLOOKUP t.locals «isInput» = SOME (ValWord 1w) ∧
    FLOOKUP t.locals «waitSet» = SOME (ValWord 1w) ∧
    (?tm. FLOOKUP t.locals «sysTime» = SOME (ValWord tm)) ∧
    (?tm. FLOOKUP t.locals «wakeUpAt» = SOME (ValWord tm)) ==>
    ?w.
      eval t wait = SOME (ValWord w) ∧
      w ≠ 0w
Proof
  rw [] >>
  fs [wait_def, eval_def, OPT_MMAP_def] >>
  gs [wordLangTheory.word_op_def] >>
  TOP_CASE_TAC >>
  fs []
QED


Theorem step_wait_delay_eval_wait_not_zero:
  !(t:('a,'b) panSem$state).
    FLOOKUP t.locals «isInput» = SOME (ValWord 1w) ∧
    (∃w. FLOOKUP t.locals «waitSet» = SOME (ValWord 0w)) ∧
    (?tm. FLOOKUP t.locals «sysTime» = SOME (ValWord (n2w tm)) ∧
          ?wt. FLOOKUP t.locals «wakeUpAt» = SOME (ValWord (n2w wt)) ∧
               tm < wt ∧
               wt < dimword (:α) ∧
               tm < dimword (:α)) ==>
    ?w.
      eval t wait = SOME (ValWord w) ∧
      w ≠ 0w
Proof
  rw [] >>
  fs [wait_def] >>
  fs [eval_def, OPT_MMAP_def] >>
  gs [active_low_def,
      wordLangTheory.word_op_def] >>
  TOP_CASE_TAC >>
  fs [] >>
  fs [asmTheory.word_cmp_def] >>
  fs [addressTheory.WORD_CMP_NORMALISE] >>
  fs [word_ls_n2w] >>
  ‘wt MOD dimword (:α) = wt’ by (
    match_mp_tac LESS_MOD >> fs []) >>
  ‘tm MOD dimword (:α) = tm’ by (
    match_mp_tac LESS_MOD >> fs []) >>
  fs []
QED


Theorem state_rel_imp_mem_config:
  ∀clks io s t.
    state_rel clks s t ==>
    mem_config t.memory t.memaddrs t.be
Proof
  rw [state_rel_def]
QED


Theorem state_rel_imp_systime_defined:
  ∀clks io s t.
    state_rel clks s t ==>
    ∃tm. FLOOKUP t.locals «sysTime» = SOME (ValWord tm)
Proof
  rw [state_rel_def, time_vars_def] >>
  pairarg_tac >> fs []
QED


Theorem evaluate_ext_call:
  ∀(t :('a, time_input) panSem$state) res t' bytes.
    evaluate (ExtCall «get_ffi» «ptr1» «len1» «ptr2» «len2» ,t) = (res,t') ∧
    read_bytearray ffiBufferAddr (w2n (ffiBufferSize:α word))
                   (mem_load_byte t.memory t.memaddrs t.be) = SOME bytes ∧
    t.ffi = build_ffi t.ffi.ffi_state t.ffi.io_events ∧
    ffi_vars t.locals ∧
    dimindex (:α) DIV 8 + 1 <  dimword (:α) ⇒
    res = NONE ∧
    t' =
    t with
      <|memory :=
        mem_call_ffi t.memory t.memaddrs t.be bytes t.ffi.ffi_state;
        ffi := ffi_call_ffi t.ffi bytes|>
Proof
  rpt gen_tac >>
  strip_tac >>
  fs [evaluate_def, ffi_vars_def, read_bytearray_def] >>
  gs [build_ffi_def, ffiTheory.call_FFI_def] >>
  gs [ffiTheory.ffi_state_component_equality] >>
  fs [ntime_input_def] >>
  fs [multiwordTheory.LENGTH_k2mw] >>
  drule read_bytearray_LENGTH >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac ‘LENGTH _ = a’ >>
  ‘a = dimindex (:α) DIV 8 + 1’ by (
    fs [Abbr ‘a’] >>
    fs [ffiBufferSize_def, bytes_in_word_def,
        GSYM n2w_SUC]) >>
  gs [mem_call_ffi_def, ffi_call_ffi_def]
QED


Theorem evaluate_assign_load:
  ∀dst trgt (t :('a, time_input) panSem$state) res t' adr tm w.
    evaluate (Assign dst (Load One (Var trgt)),t) = (res,t') ∧
    FLOOKUP t.locals trgt = SOME (ValWord adr) ∧
    FLOOKUP t.locals dst = SOME (ValWord tm) ∧
    t.memory adr = Word w ∧
    adr ∈ t.memaddrs ⇒
      res = NONE ∧
      t' = t with locals :=
           t.locals |+
            (dst, ValWord w)
Proof
  rpt gen_tac >>
  strip_tac >>
  gs [evaluate_def, eval_def] >>
  gs [mem_load_def] >>
  gs [is_valid_value_def, shape_of_def]
QED


Theorem evaluate_assign_load_next_address:
  ∀dst trgt (t :('a, time_input) panSem$state) res t' adr tm w.
    evaluate (Assign dst
              (Load One (Op Add [Var trgt ; Const bytes_in_word])),t) = (res,t') ∧
    FLOOKUP t.locals trgt = SOME (ValWord adr) ∧
    FLOOKUP t.locals dst = SOME (ValWord tm) ∧
    t.memory (adr + bytes_in_word) = Word w ∧
    adr + bytes_in_word ∈ t.memaddrs ⇒
      res = NONE ∧
      t' = t with locals :=
           t.locals |+
            (dst, ValWord w)
Proof
  rpt gen_tac >>
  strip_tac >>
  gs [evaluate_def, eval_def, OPT_MMAP_def] >>
  gs [mem_load_def, wordLangTheory.word_op_def] >>
  gs [is_valid_value_def, shape_of_def]
QED

Theorem time_seq_add_holds:
  ∀f m p.
    time_seq f m ⇒
    time_seq (λn. f (p + n)) m
Proof
  rw [time_seq_def] >>
  fs [] >>
  last_x_assum (qspec_then ‘p + n’ assume_tac) >>
  fs [ADD_SUC]
QED


Definition delay_rep_def:
  delay_rep m (d:num) (seq:time_input) cycles ⇔
    FST (seq cycles) = d + FST (seq 0) ∧
    FST (seq cycles) < m ∧
    ∀i. i < cycles ⇒ ¬SND (seq i)
End


Definition wakeup_rel_def:
  (wakeup_rel fm m NONE (seq:time_input) cycles = T) ∧
  (wakeup_rel fm m (SOME wt) seq cycles =
    ∃st.
      FLOOKUP fm «wakeUpAt» = SOME (ValWord (n2w (wt + st))) ∧
      wt + st < m ∧
      st ≤ FST (seq 0) ∧
      FST (seq cycles) < wt + st)
End


Theorem step_delay:
  !cycles prog d s s' w (t:('a,time_input) panSem$state) ck_extra.
    step prog (LDelay d) s s' ∧
    state_rel (clksOf prog) s t ∧
    code_installed t.code prog ∧
    delay_rep (dimword (:α)) d (t.ffi.ffi_state) cycles ∧
    wakeup_rel t.locals (dimword (:α)) s.waitTime (t.ffi.ffi_state) cycles ∧
    FLOOKUP t.locals «isInput» = SOME (ValWord 1w) ∧
    FLOOKUP t.locals «sysTime» =
    SOME (ValWord (n2w (FST (t.ffi.ffi_state 0)))) ==>
    ?ck t'.
      evaluate (wait_input_time_limit, t with clock := t.clock + ck) =
      evaluate (wait_input_time_limit, t' with clock := t'.clock + ck_extra) ∧
      code_installed t'.code prog ∧
      state_rel (clksOf prog) s' t' ∧
      t'.ffi.ffi_state = nexts_ffi cycles (t.ffi.ffi_state) ∧
      t'.ffi.oracle = t.ffi.oracle ∧
      FLOOKUP t'.locals «wakeUpAt» = FLOOKUP t.locals «wakeUpAt» ∧
      FLOOKUP t'.locals «isInput» = SOME (ValWord 1w) ∧
      FLOOKUP t'.locals «sysTime»  =
      SOME (ValWord (n2w (FST (t.ffi.ffi_state (cycles - 1)))))
Proof
  Induct_on ‘cycles’ >>
  fs []
  >- (
    rw [] >>
    fs [delay_rep_def] >>
    ‘d = 0’ by fs [] >>
    fs [] >>
    pop_assum kall_tac >>
    fs [step_cases] >>
    fs [delay_clocks_def, mkState_def] >>
    rveq >> gs [] >>
    fs [fmap_to_alist_eq_fm] >>
    qexists_tac ‘ck_extra’ >> fs [] >>
    qexists_tac ‘t’ >> fs [] >>
    gs [state_rel_def, nexts_ffi_def, GSYM ETA_AX]) >>
  rw [] >>
  ‘∃sd. sd ≤ d ∧
        delay_rep (dimword (:α)) sd t.ffi.ffi_state cycles’ by (
    fs [delay_rep_def] >>
    imp_res_tac state_rel_imp_time_seq_ffi >>
    ‘FST (t.ffi.ffi_state 0) ≤ FST (t.ffi.ffi_state cycles)’ by (
      match_mp_tac time_seq_mono >>
      qexists_tac ‘(dimword (:α))’ >>
      fs []) >>
    fs [time_seq_def] >>
    first_x_assum (qspec_then ‘cycles’ mp_tac) >>
    first_x_assum (qspec_then ‘cycles’ mp_tac) >>
    strip_tac >> strip_tac >>
    gs [] >>
    qexists_tac ‘d - d'’ >>
    gs [] >>
    qexists_tac ‘st’ >> fs []) >>
  qpat_x_assum ‘step _ _ _ _’ mp_tac >>
  rewrite_tac [step_cases] >>
  strip_tac >>
  fs [] >> rveq
  >- (
    ‘step prog (LDelay sd) s
     (mkState (delay_clocks s.clocks sd) s.location NONE NONE)’ by (
      gs [mkState_def] >>
      fs [step_cases, mkState_def]) >>
    last_x_assum drule >>
    (* ck_extra *)
    disch_then (qspecl_then [‘t’, ‘ck_extra + 1’] mp_tac) >>
    impl_tac >- gs [mkState_def, wakeup_rel_def] >>
    strip_tac >> fs [] >>
    ‘(mkState (delay_clocks s.clocks d) s.location NONE NONE).ioAction =
     NONE’ by fs [mkState_def] >>
    fs [] >>
    pop_assum kall_tac >>
    ‘(mkState (delay_clocks s.clocks sd) s.location NONE NONE).ioAction =
     NONE’ by fs [mkState_def] >>
    fs [] >>
    pop_assum kall_tac >>
    qexists_tac ‘ck’ >>
    fs [] >>
    fs [wait_input_time_limit_def] >>
    rewrite_tac [Once evaluate_def] >>

    drule step_delay_eval_wait_not_zero >>
    impl_tac
    >- (
      gs [state_rel_def, mkState_def, equivs_def, time_vars_def, active_low_def] >>
      pairarg_tac >> gs []) >>
    strip_tac >>
    gs [eval_upd_clock_eq] >>
    (* evaluating the function *)
    pairarg_tac >> fs [] >>
    pop_assum mp_tac >>
    fs [dec_clock_def] >>
    ‘state_rel (clksOf prog)
     (mkState (delay_clocks s.clocks sd) s.location NONE NONE)
     (t' with clock := ck_extra + t'.clock)’ by gs [state_rel_def] >>
    qpat_x_assum ‘state_rel _ _ t'’ kall_tac >>

    rewrite_tac [Once check_input_time_def] >>
    fs [panLangTheory.nested_seq_def] >>
    rewrite_tac [Once evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    drule state_rel_imp_mem_config >>
    rewrite_tac [Once mem_config_def] >>
    strip_tac >>
    drule evaluate_ext_call >>
    disch_then drule >>
    impl_tac
    >- (
      gs [state_rel_def] >>
      pairarg_tac >> gs []) >>
    strip_tac >> gs [] >>
    pop_assum kall_tac >>
    pop_assum kall_tac >>
    drule state_rel_imp_ffi_vars >>
    strip_tac >>
    pop_assum mp_tac >>
    rewrite_tac [Once ffi_vars_def] >>
    strip_tac >>
    drule state_rel_imp_systime_defined >>
    strip_tac >>
    (* reading systime *)
    rewrite_tac [Once evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    qmatch_asmsub_abbrev_tac ‘evaluate (Assign «sysTime» _, nt)’ >>
    ‘nt.memory ffiBufferAddr = Word (n2w (FST(t'.ffi.ffi_state 0)))’ by (
      fs [Abbr ‘nt’] >>
      fs [mem_call_ffi_def] >>
      drule read_bytearray_LENGTH >>
      strip_tac >> fs [] >>
      fs [ffiBufferSize_def] >>
      cheat) >>
    drule evaluate_assign_load >>
    gs [] >>
    disch_then (qspecl_then
                [‘ffiBufferAddr’, ‘tm’,
                 ‘n2w (FST (t'.ffi.ffi_state 0))’] mp_tac) >>
    impl_tac
    >- (
      gs [Abbr ‘nt’] >>
      fs [state_rel_def]) >>
    strip_tac >> fs [] >>
    pop_assum kall_tac >>
    pop_assum kall_tac >>
    (* reading input *)
    rewrite_tac [Once evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    qmatch_asmsub_abbrev_tac ‘evaluate (Assign «isInput» _, nnt)’ >>
    ‘nnt.memory (ffiBufferAddr +  bytes_in_word) =
     Word (if SND (t'.ffi.ffi_state 0) then 0w else 1w)’ by cheat >>
    gs [] >>
    drule evaluate_assign_load_next_address >>
    gs [] >>
    disch_then (qspecl_then
                [‘ffiBufferAddr’, ‘1w’,
                 ‘1w’] mp_tac) >>
    impl_tac
    >- (
      gs [Abbr ‘nnt’,Abbr ‘nt’, active_low_def] >>
      gs [state_rel_def, FLOOKUP_UPDATE] >>
      gs [delay_rep_def, nexts_ffi_def]) >>
    strip_tac >>
    gs [] >>
    pop_assum kall_tac >>
    pop_assum kall_tac >>
    rewrite_tac [Once evaluate_def] >>
    fs [] >>
    strip_tac >> fs [] >>
    rveq >> gs [] >>
    fs [Abbr ‘nnt’, Abbr ‘nt’] >>
    qmatch_goalsub_abbrev_tac ‘evaluate (_, nt)’ >>
    qexists_tac ‘nt with clock := t'.clock’ >>
    fs [] >>
    gs [Abbr ‘nt’] >>
    reverse conj_tac
    >- (
      fs [ffi_call_ffi_def] >>
      fs [nexts_ffi_def, next_ffi_def, FLOOKUP_UPDATE] >>
      fs [ADD1]) >>
    (* proving state rel *)
    gs [state_rel_def, mkState_def] >>
    conj_tac
    (* equivs *)
    >- gs [equivs_def, FLOOKUP_UPDATE, active_low_def] >>
    conj_tac
    >- gs [ffi_vars_def, FLOOKUP_UPDATE] >>
    conj_tac
    >- gs [time_vars_def, FLOOKUP_UPDATE] >>
    conj_tac
    >- (
      gs [mem_config_def, mem_call_ffi_def] >>
      cheat) >>
    conj_tac
    >- (
      (* clock_bound *)
      qpat_x_assum ‘clock_bound s.clocks _ _’ assume_tac >>
      gs [clock_bound_def] >>
      fs [EVERY_MEM] >>
      rw [] >>
      first_x_assum drule >>
      strip_tac >>
      fs [] >>
      fs [delay_clocks_def] >>
      qexists_tac ‘d+n’ >>
      gs [] >>
      conj_tac
      >- (
        match_mp_tac mem_to_flookup >>
        ‘MAP FST (MAP (λ(x,y). (x,d + y)) (fmap_to_alist s.clocks)) =
         MAP FST (fmap_to_alist s.clocks)’ by fs [map_fst] >>
        fs [ALL_DISTINCT_fmap_to_alist_keys] >>
        fs [MEM_MAP] >>
        qexists_tac ‘(ck',n)’ >>
        fs []) >>
      gs [delay_rep_def] >>
      qpat_x_assum ‘_ (t.ffi.ffi_state 0)’ assume_tac >>
      pairarg_tac >> fs [] >>
      fs [clocks_rel_def, clkvals_rel_def] >>
      gs [EVERY_MEM] >>
      first_x_assum (qspec_then ‘ck'’ assume_tac) >>
      gs []) >>
    pairarg_tac >> gs [] >>
    conj_tac
    >- (
      fs [ffi_call_ffi_def, build_ffi_def] >>
      fs [ffiTheory.ffi_state_component_equality] >>
      last_x_assum assume_tac >>
      pairarg_tac >>
      fs []) >>
    conj_tac
    >- (
      (* time_seq holds *)
      gs [ffi_call_ffi_def,
          nexts_ffi_def, next_ffi_def] >>
      qpat_x_assum ‘_ (t.ffi.ffi_state 0)’ mp_tac >>
      pairarg_tac >> gs [] >>
      strip_tac >>
      drule time_seq_add_holds >>
      disch_then (qspec_then ‘cycles + 1’ mp_tac) >>
      fs [])  >>
    qpat_x_assum ‘_ (nexts_ffi _ _ _)’ assume_tac >>
    pairarg_tac >> fs [] >>
    fs [nexts_ffi_def] >>
    gs [clocks_rel_def, FLOOKUP_UPDATE] >>
    qexists_tac ‘ns’ >>
    fs [] >>
    fs [clkvals_rel_def] >>
    conj_tac
    >- (
      fs [MAP_EQ_EVERY2] >>
      fs [LIST_REL_EL_EQN] >>
      rw [] >>
      pairarg_tac >> fs [] >>
      last_x_assum drule >>
      fs [] >>
      strip_tac >>
      (* shortcut *)
      ‘∃xn. FLOOKUP s.clocks x = SOME xn’ by (
        drule EL_ZIP >>
        disch_then (qspec_then ‘n’ mp_tac) >>
        gs [] >>
        strip_tac >>
        gs [clock_bound_def] >>
        imp_res_tac every_conj_spec >>
        fs [EVERY_MEM] >>
        fs [MEM_EL] >>
        first_x_assum (qspec_then ‘x’ mp_tac) >>
        fs [] >>
        impl_tac >- metis_tac [] >>
        gs [FDOM_FLOOKUP]) >>
      fs [delay_clocks_def] >>
      ‘FLOOKUP (FEMPTY |++ MAP (λ(x,y). (x,d + y)) (fmap_to_alist s.clocks))
       x = SOME (d + xn)’ by (
        match_mp_tac mem_to_flookup >>
        ‘MAP FST (MAP (λ(x,y). (x,d + y)) (fmap_to_alist s.clocks)) =
         MAP FST (fmap_to_alist s.clocks)’ by fs [map_fst] >>
        fs [ALL_DISTINCT_fmap_to_alist_keys] >>
        fs [MEM_MAP] >>
        qexists_tac ‘(x,xn)’ >>
        fs []) >>
      fs [] >>
      ‘FLOOKUP (FEMPTY |++ MAP (λ(x,y). (x,sd + y)) (fmap_to_alist s.clocks))
       x = SOME (sd + xn)’ by (
        match_mp_tac mem_to_flookup >>
        ‘MAP FST (MAP (λ(x,y). (x,sd + y)) (fmap_to_alist s.clocks)) =
         MAP FST (fmap_to_alist s.clocks)’ by fs [map_fst] >>
        fs [ALL_DISTINCT_fmap_to_alist_keys] >>
        fs [MEM_MAP] >>
        qexists_tac ‘(x,xn)’ >>
        fs []) >>
      fs [] >>
      fs [ffi_call_ffi_def, next_ffi_def] >>
      qpat_x_assum ‘delay_rep _ d _ _’ assume_tac >>
      qpat_x_assum ‘delay_rep _ sd _ _’ assume_tac >>
      qpat_x_assum ‘sd ≤ d’ assume_tac >>
      gs [delay_rep_def] >>
      gs [ADD1]) >>
    (* repetition *)
    fs [EVERY_MEM] >>
    rw [] >>
    first_x_assum (qspec_then ‘x’ assume_tac) >>
    gs [] >>
    ‘∃xn. FLOOKUP s.clocks x = SOME xn’ by (
      gs [clock_bound_def] >>
      gs [EVERY_MEM] >>
      rw [] >> gs [] >>
      last_x_assum (qspec_then ‘x’ assume_tac) >>
      gs []) >>
    fs [delay_clocks_def] >>
    ‘FLOOKUP (FEMPTY |++ MAP (λ(x,y). (x,d + y)) (fmap_to_alist s.clocks))
     x = SOME (d + xn)’ by (
      match_mp_tac mem_to_flookup >>
      ‘MAP FST (MAP (λ(x,y). (x,d + y)) (fmap_to_alist s.clocks)) =
       MAP FST (fmap_to_alist s.clocks)’ by fs [map_fst] >>
      fs [ALL_DISTINCT_fmap_to_alist_keys] >>
      fs [MEM_MAP] >>
      qexists_tac ‘(x,xn)’ >>
      fs []) >>
    fs [] >>
    ‘FLOOKUP (FEMPTY |++ MAP (λ(x,y). (x,sd + y)) (fmap_to_alist s.clocks))
     x = SOME (sd + xn)’ by (
      match_mp_tac mem_to_flookup >>
      ‘MAP FST (MAP (λ(x,y). (x,sd + y)) (fmap_to_alist s.clocks)) =
       MAP FST (fmap_to_alist s.clocks)’ by fs [map_fst] >>
      fs [ALL_DISTINCT_fmap_to_alist_keys] >>
      fs [MEM_MAP] >>
      qexists_tac ‘(x,xn)’ >>
      fs []) >>
    fs [] >>
    fs [ffi_call_ffi_def, next_ffi_def] >>
    qpat_x_assum ‘delay_rep _ d _ _’ assume_tac >>
    qpat_x_assum ‘delay_rep _ sd _ _’ assume_tac >>
    qpat_x_assum ‘sd ≤ d’ assume_tac >>
    gs [delay_rep_def] >>
    gs [ADD1]) >>
  ‘step prog (LDelay sd) s
   (mkState (delay_clocks s.clocks sd) s.location NONE (SOME (w - sd)))’ by (
    gs [mkState_def] >>
    fs [step_cases, mkState_def]) >>
  last_x_assum drule >>
  (* ck_extra *)
  disch_then (qspecl_then [‘t’, ‘ck_extra + 1’] mp_tac) >>
  impl_tac
  >- (
    gs [mkState_def, wakeup_rel_def] >>
    cheat) >>
  strip_tac >> fs [] >>
  ‘(mkState (delay_clocks s.clocks d) s.location NONE (SOME (w - d))).ioAction =
   NONE’ by fs [mkState_def] >>
  fs [] >>
  pop_assum kall_tac >>
  ‘(mkState (delay_clocks s.clocks sd) s.location NONE (SOME (w - sd))).ioAction =
   NONE’ by fs [mkState_def] >>
  fs [] >>
  pop_assum kall_tac >>
  qexists_tac ‘ck’ >>
  fs [] >>
  fs [wait_input_time_limit_def] >>
  rewrite_tac [Once evaluate_def] >>
  drule step_wait_delay_eval_wait_not_zero >>
  impl_tac
  >- (
    conj_tac
    >- gs [state_rel_def, mkState_def, equivs_def, active_low_def] >>
    gs [] >>
    gs [wakeup_rel_def, delay_rep_def] >>
    ‘(st + w) MOD dimword (:α) = st + w’ by (
      match_mp_tac  LESS_MOD >>
      fs []) >>
    qexists_tac ‘FST (t.ffi.ffi_state (cycles − 1))’ >>
    fs [] >>
    gs [] >>
    rveq >> gs [] >>
    qexists_tac ‘st + w’ >>
    rveq >> gs [] >>
    fs [state_rel_def] >>
    qpat_x_assum ‘_ (t.ffi.ffi_state 0)’ assume_tac >>

    pairarg_tac >> fs [] >>
    gs [time_seq_def, nexts_ffi_def] >>
    (* could be neater *)
    cases_on ‘cycles = 0’
    >- gs [] >>
    first_x_assum (qspec_then ‘cycles − 1’ assume_tac) >>
    gs [SUB_LEFT_SUC] >>
    cases_on ‘cycles = 1’ >>
    fs [] >>
    ‘~(cycles ≤ 1)’ by gs [] >>
    fs []) >>
  strip_tac >>
  gs [eval_upd_clock_eq] >>
  (* evaluating the function *)
  pairarg_tac >> fs [] >>
  pop_assum mp_tac >>
  fs [dec_clock_def] >>
  ‘state_rel (clksOf prog)
   (mkState (delay_clocks s.clocks sd) s.location NONE (SOME (w − sd)))
   (t' with clock := ck_extra + t'.clock)’ by gs [state_rel_def] >>
  qpat_x_assum ‘state_rel _ _ t'’ kall_tac >>

  rewrite_tac [Once check_input_time_def] >>
  fs [panLangTheory.nested_seq_def] >>
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  drule state_rel_imp_mem_config >>
  rewrite_tac [Once mem_config_def] >>
  strip_tac >>
  drule evaluate_ext_call >>
  disch_then drule >>
  impl_tac
  >- (
    gs [state_rel_def] >>
    pairarg_tac >> gs []) >>
  strip_tac >> gs [] >>
  pop_assum kall_tac >>
  pop_assum kall_tac >>
  drule state_rel_imp_ffi_vars >>
  strip_tac >>
  pop_assum mp_tac >>
  rewrite_tac [Once ffi_vars_def] >>
  strip_tac >>
  drule state_rel_imp_systime_defined >>
  strip_tac >>
  (* reading systime *)
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  qmatch_asmsub_abbrev_tac ‘evaluate (Assign «sysTime» _, nt)’ >>
  ‘nt.memory ffiBufferAddr = Word (n2w (FST(t'.ffi.ffi_state 0)))’ by (
    fs [Abbr ‘nt’] >>
    fs [mem_call_ffi_def] >>
    drule read_bytearray_LENGTH >>
    strip_tac >> fs [] >>
    fs [ffiBufferSize_def] >>
    cheat) >>
  drule evaluate_assign_load >>
  gs [] >>
  disch_then (qspecl_then
              [‘ffiBufferAddr’, ‘tm’,
               ‘n2w (FST (t'.ffi.ffi_state 0))’] mp_tac) >>
  impl_tac
  >- (
    gs [Abbr ‘nt’] >>
    fs [state_rel_def]) >>
  strip_tac >> fs [] >>
  pop_assum kall_tac >>
  pop_assum kall_tac >>
  (* reading input *)
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  qmatch_asmsub_abbrev_tac ‘evaluate (Assign «isInput» _, nnt)’ >>
  ‘nnt.memory (ffiBufferAddr +  bytes_in_word) =
   Word (if SND (t'.ffi.ffi_state 0) then 0w else 1w)’ by cheat >>
  gs [] >>
  drule evaluate_assign_load_next_address >>
  gs [] >>
  disch_then (qspecl_then
              [‘ffiBufferAddr’, ‘1w’,
               ‘1w’] mp_tac) >>
  impl_tac
  >- (
    gs [Abbr ‘nnt’,Abbr ‘nt’, active_low_def] >>
    gs [state_rel_def, FLOOKUP_UPDATE] >>
    gs [delay_rep_def, nexts_ffi_def]) >>
  strip_tac >>
  gs [] >>
  pop_assum kall_tac >>
  pop_assum kall_tac >>
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  strip_tac >> fs [] >>
  rveq >> gs [] >>
  fs [Abbr ‘nnt’, Abbr ‘nt’] >>
  qmatch_goalsub_abbrev_tac ‘evaluate (_, nt)’ >>
  qexists_tac ‘nt with clock := t'.clock’ >>
  fs [] >>
  gs [Abbr ‘nt’] >>
  reverse conj_tac
  >- (
    fs [ffi_call_ffi_def] >>
    fs [nexts_ffi_def, next_ffi_def] >>
    fs [FLOOKUP_UPDATE] >>
    gs [ADD1]) >>
  (* proving state rel *)
  gs [state_rel_def, mkState_def] >>
  conj_tac
  (* equivs *)
  >- gs [equivs_def, FLOOKUP_UPDATE, active_low_def] >>
  conj_tac
  >- gs [ffi_vars_def, FLOOKUP_UPDATE] >>
  conj_tac
  >- gs [time_vars_def, FLOOKUP_UPDATE] >>
  conj_tac
  >- (
    gs [mem_config_def, mem_call_ffi_def] >>
    cheat) >>
  conj_tac
  >- (
    (* clock_bound *)
    qpat_x_assum ‘clock_bound s.clocks _ _’ assume_tac >>
    gs [clock_bound_def] >>
    fs [EVERY_MEM] >>
    rw [] >>
    first_x_assum drule >>
    strip_tac >>
    fs [] >>
    fs [delay_clocks_def] >>
    qexists_tac ‘d+n’ >>
    gs [] >>
    conj_tac
    >- (
      match_mp_tac mem_to_flookup >>
      ‘MAP FST (MAP (λ(x,y). (x,d + y)) (fmap_to_alist s.clocks)) =
       MAP FST (fmap_to_alist s.clocks)’ by fs [map_fst] >>
      fs [ALL_DISTINCT_fmap_to_alist_keys] >>
      fs [MEM_MAP] >>
      qexists_tac ‘(ck',n)’ >>
      fs []) >>
    gs [delay_rep_def] >>
    last_x_assum assume_tac >>
    pairarg_tac >> fs [] >>
    fs [clocks_rel_def, clkvals_rel_def] >>
    gs [EVERY_MEM] >>
    first_x_assum (qspec_then ‘ck'’ assume_tac) >>
    gs []) >>
  pairarg_tac >> gs [] >>
  conj_tac
  >- (
    fs [ffi_call_ffi_def, build_ffi_def] >>
    fs [ffiTheory.ffi_state_component_equality] >>
    last_x_assum assume_tac >>
    pairarg_tac >>
    fs []) >>
  conj_tac
  >- (
    (* time_seq holds *)
    gs [ffi_call_ffi_def,
        nexts_ffi_def, next_ffi_def] >>
    last_x_assum mp_tac >>
    pairarg_tac >> gs [] >>
    strip_tac >>
    drule time_seq_add_holds >>
    disch_then (qspec_then ‘cycles + 1’ mp_tac) >>
    fs [])  >>
  qpat_x_assum ‘_ (nexts_ffi _ _ _)’ assume_tac >>
  pairarg_tac >> fs [] >>
  fs [nexts_ffi_def] >>
  gs [clocks_rel_def, FLOOKUP_UPDATE] >>
  qexists_tac ‘ns’ >>
  fs [] >>
  fs [clkvals_rel_def] >>
  conj_tac
  >- (
    fs [MAP_EQ_EVERY2] >>
    fs [LIST_REL_EL_EQN] >>
    rw [] >>
    pairarg_tac >> fs [] >>
    last_x_assum drule >>
    fs [] >>
    strip_tac >>
    (* shortcut *)
    ‘∃xn. FLOOKUP s.clocks x = SOME xn’ by (
      drule EL_ZIP >>
      disch_then (qspec_then ‘n’ mp_tac) >>
      gs [] >>
      strip_tac >>
      gs [clock_bound_def] >>
      imp_res_tac every_conj_spec >>
      fs [EVERY_MEM] >>
      fs [MEM_EL] >>
      first_x_assum (qspec_then ‘x’ mp_tac) >>
      fs [] >>
      impl_tac >- metis_tac [] >>
      gs [FDOM_FLOOKUP]) >>
    fs [delay_clocks_def] >>
    ‘FLOOKUP (FEMPTY |++ MAP (λ(x,y). (x,d + y)) (fmap_to_alist s.clocks))
     x = SOME (d + xn)’ by (
      match_mp_tac mem_to_flookup >>
      ‘MAP FST (MAP (λ(x,y). (x,d + y)) (fmap_to_alist s.clocks)) =
       MAP FST (fmap_to_alist s.clocks)’ by fs [map_fst] >>
      fs [ALL_DISTINCT_fmap_to_alist_keys] >>
      fs [MEM_MAP] >>
      qexists_tac ‘(x,xn)’ >>
      fs []) >>
    fs [] >>
    ‘FLOOKUP (FEMPTY |++ MAP (λ(x,y). (x,sd + y)) (fmap_to_alist s.clocks))
     x = SOME (sd + xn)’ by (
      match_mp_tac mem_to_flookup >>
      ‘MAP FST (MAP (λ(x,y). (x,sd + y)) (fmap_to_alist s.clocks)) =
       MAP FST (fmap_to_alist s.clocks)’ by fs [map_fst] >>
      fs [ALL_DISTINCT_fmap_to_alist_keys] >>
      fs [MEM_MAP] >>
      qexists_tac ‘(x,xn)’ >>
      fs []) >>
    fs [] >>
    fs [ffi_call_ffi_def, next_ffi_def] >>
    qpat_x_assum ‘delay_rep _ d _ _’ assume_tac >>
    qpat_x_assum ‘delay_rep _ sd _ _’ assume_tac >>
    qpat_x_assum ‘sd ≤ d’ assume_tac >>
    gs [delay_rep_def] >>
    gs [ADD1]) >>
  (* repetition *)
  fs [EVERY_MEM] >>
  rw [] >>
  first_x_assum (qspec_then ‘x’ assume_tac) >>
  gs [] >>
  ‘∃xn. FLOOKUP s.clocks x = SOME xn’ by (
    gs [clock_bound_def] >>
    gs [EVERY_MEM] >>
    rw [] >> gs [] >>
    last_x_assum (qspec_then ‘x’ assume_tac) >>
    gs []) >>
  fs [delay_clocks_def] >>
  ‘FLOOKUP (FEMPTY |++ MAP (λ(x,y). (x,d + y)) (fmap_to_alist s.clocks))
   x = SOME (d + xn)’ by (
    match_mp_tac mem_to_flookup >>
    ‘MAP FST (MAP (λ(x,y). (x,d + y)) (fmap_to_alist s.clocks)) =
     MAP FST (fmap_to_alist s.clocks)’ by fs [map_fst] >>
    fs [ALL_DISTINCT_fmap_to_alist_keys] >>
    fs [MEM_MAP] >>
    qexists_tac ‘(x,xn)’ >>
    fs []) >>
  fs [] >>
  ‘FLOOKUP (FEMPTY |++ MAP (λ(x,y). (x,sd + y)) (fmap_to_alist s.clocks))
   x = SOME (sd + xn)’ by (
    match_mp_tac mem_to_flookup >>
    ‘MAP FST (MAP (λ(x,y). (x,sd + y)) (fmap_to_alist s.clocks)) =
     MAP FST (fmap_to_alist s.clocks)’ by fs [map_fst] >>
    fs [ALL_DISTINCT_fmap_to_alist_keys] >>
    fs [MEM_MAP] >>
    qexists_tac ‘(x,xn)’ >>
    fs []) >>
  fs [] >>
  fs [ffi_call_ffi_def, next_ffi_def] >>
  qpat_x_assum ‘delay_rep _ d _ _’ assume_tac >>
  qpat_x_assum ‘delay_rep _ sd _ _’ assume_tac >>
  qpat_x_assum ‘sd ≤ d’ assume_tac >>
  gs [delay_rep_def] >>
  gs [ADD1]
QED


val _ = export_theory();
