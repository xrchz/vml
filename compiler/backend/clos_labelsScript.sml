(*
  Replaces calls to unknown functions with constant type errors.
*)
open preamble closLangTheory;

val _ = new_theory "clos_labels";
val _ = set_grammar_ancestry ["closLang","misc","backend_common"];

val remove_dests_def = tDefine "remove_dests" `
  (remove_dests (ds: unit fntree) [] = []) /\
  (remove_dests ds ((x:closLang$exp)::y::xs) =
     HD (remove_dests ds [x]) :: remove_dests ds (y::xs)) /\
  (remove_dests ds [Var t v] = [Var t v]) /\
  (remove_dests ds [If t x1 x2 x3] =
     [If t (HD (remove_dests ds [x1]))
           (HD (remove_dests ds [x2]))
           (HD (remove_dests ds [x3]))]) /\
  (remove_dests ds [Let t xs x2] =
     let xs = remove_dests ds xs in
     let x2 = HD (remove_dests ds [x2]) in
       [Let t xs x2]) /\
  (remove_dests ds [Raise t x1] =
     [Raise t (HD (remove_dests ds [x1]))]) /\
  (remove_dests ds [Handle t x1 x2] =
     [Handle t (HD (remove_dests ds [x1]))
              (HD (remove_dests ds [x2]))]) /\
  (remove_dests ds [Op t op xs] =
     [Op t op (remove_dests ds xs)]) /\
  (remove_dests ds [Tick t x] = [Tick t (HD (remove_dests ds [x]))]) /\
  (remove_dests ds [Call t ticks dest xs] =
   if IS_SOME (fntree_lookup dest ds) then
    [Call t ticks dest (remove_dests ds xs)]
   else [Op t (if NULL xs then El else String "") (remove_dests ds xs)]) /\
  (remove_dests ds [App t NONE x1 xs] =
  [App t NONE (HD (remove_dests ds [x1])) (remove_dests ds xs)]) /\
  (remove_dests ds [App t (SOME dest) x1 xs] =
  if IS_SOME (fntree_lookup dest ds) then
    [App t (SOME dest) (HD (remove_dests ds [x1])) (remove_dests ds xs)]
  else
    if NULL xs then [Let t [Op t El []] (HD (remove_dests ds [x1]))]
    else [Op t (String"") (remove_dests ds xs ++ remove_dests ds [x1])]) /\
  (remove_dests ds [Letrec t fn_opt vs fns x1] =
     let m = LENGTH fns in
     let new_fns =
       MAP (\(num_args, x).
         (num_args, HD (remove_dests ds [x]))) fns in
     [Letrec t fn_opt vs new_fns (HD (remove_dests ds [x1]))]) /\
  (remove_dests ds [Fn t fn_opt vs num_args x1] =
    [Fn t fn_opt vs num_args (HD (remove_dests ds [x1]))])`
  (WF_REL_TAC `measure (exp3_size o SND)`
   \\ simp []
   \\ rpt strip_tac
   \\ imp_res_tac exp1_size_lemma
   \\ simp []);

val add_code_names_def = tDefine "add_code_names" `
  (add_code_names ds [] = ds) /\
  (add_code_names ds (x::y::xs) =
     let ds = add_code_names ds [x] in
       add_code_names ds (y::xs)) /\
  (add_code_names ds [Var _ v] = ds) /\
  (add_code_names ds [If _ x1 x2 x3] =
     let ds = add_code_names ds [x1] in
     let ds = add_code_names ds [x2] in
     let ds = add_code_names ds [x3] in
       ds) /\
  (add_code_names ds [Let _ xs x2] =
     let ds = add_code_names ds xs in
     let ds = add_code_names ds [x2] in
       ds) /\
  (add_code_names ds [Raise _ x1] =
     add_code_names ds [x1]) /\
  (add_code_names ds [Tick _ x1] =
     add_code_names ds [x1]) /\
  (add_code_names ds [Op _ op xs] =
     add_code_names ds xs) /\
  (add_code_names ds [App _ fn_opt x1 xs] =
     let ds = add_code_names ds [x1] in
     let ds = add_code_names ds xs in
       ds) /\
  (add_code_names ds [Fn _ fn_opt vs num_args x1] =
     let ds = add_code_names ds [x1] in
     case fn_opt of NONE => ds
       | SOME fname => fntree_insert fname () ds) /\
  (add_code_names ds [Letrec _ fn_opt vs fns x1] =
     let ds = add_code_names ds (MAP SND fns) in
     let ds = add_code_names ds [x1] in
     case fn_opt of NONE => ds
       | SOME fname => fntree_list_insert
         (GENLIST (\n. next_fname fname (2 * n)) (LENGTH fns)) ds) /\
  (add_code_names ds [Handle _ x1 x2] =
     let ds = add_code_names ds [x1] in
     let ds = add_code_names ds [x2] in
       ds) /\
  (add_code_names ds [Call _ ticks dest xs] =
     add_code_names ds xs)`
  (WF_REL_TAC `measure (exp3_size o SND)`
   \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC >>
   Induct_on `fns` >>
   srw_tac [ARITH_ss] [exp_size_def] >>
   Cases_on `h` >>
   full_simp_tac(srw_ss())[exp_size_def] >>
   decide_tac);

val compile_def = Define`
  compile prog =
    let ds = fntree_list_insert (MAP FST prog) LN in
    let ds = add_code_names ds (MAP (SND o SND) prog) in
      MAP (λ(n,args,exp). (n, args, HD(remove_dests ds [exp]))) prog`;

Theorem LENGTH_remove_dests
  `!dests xs. LENGTH (remove_dests dests xs) = LENGTH xs`
  (recInduct (fetch "-" "remove_dests_ind") \\ simp [remove_dests_def] \\ rw []);

val _ = export_theory();
