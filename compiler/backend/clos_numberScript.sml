(*
  This simple compiler phase walks the program and gives each closure
  a new unique function identifier.
*)
open preamble closLangTheory;

val _ = new_theory"clos_number";
val _ = set_grammar_ancestry ["closLang"]

val renumber_code_fnames_def = tDefine "renumber_code_fnames" `
  (renumber_code_fnames_list nm [] = (nm,[])) /\
  (renumber_code_fnames_list nm (x::xs) =
     let (nm,x) = renumber_code_fnames nm x in
     let (nm,xs) = renumber_code_fnames_list nm xs in
     (nm, x::xs)) /\
  (renumber_code_fnames nm (Var t v) = (nm,(Var t v))) /\
  (renumber_code_fnames nm (If t x1 x2 x3) =
     let (nm,x1) = renumber_code_fnames nm x1 in
     let (nm,x2) = renumber_code_fnames nm x2 in
     let (nm,x3) = renumber_code_fnames nm x3 in
       (nm,If t x1 x2 x3)) /\
  (renumber_code_fnames nm (Let t xs x2) =
     let (nm,xs) = renumber_code_fnames_list nm xs in
     let (nm,x2) = renumber_code_fnames nm x2 in
       (nm,Let t xs x2)) /\
  (renumber_code_fnames nm (Raise t x1) =
     let (nm,x1) = renumber_code_fnames nm x1 in
       (nm,Raise t x1)) /\
  (renumber_code_fnames nm (Tick t x1) =
     let (nm,x1) = renumber_code_fnames nm x1 in
       (nm,Tick t x1)) /\
  (renumber_code_fnames nm (Op t op xs) =
     let (nm,xs) = renumber_code_fnames_list nm xs in
       (nm,Op t op xs)) /\
  (renumber_code_fnames nm (App t fn_opt x1 x2) =
     let (nm,x1) = renumber_code_fnames nm x1 in
     let (nm,x2) = renumber_code_fnames_list nm x2 in
       (nm,App t NONE x1 x2)) /\
  (renumber_code_fnames nm (Fn t fn_opt vs num_args x1) =
     let (nm,x1) = renumber_code_fnames nm x1 in
       (next_fname nm 2,Fn t (SOME nm) vs num_args x1)) /\
  (renumber_code_fnames nm (Letrec t fn_opt vs fns x1) =
     let (start_nm,fns') = renumber_code_fnames_list nm (MAP SND fns) in
     let next_nm = next_fname start_nm (2 * LENGTH fns') in
     let (nm,x1) = renumber_code_fnames next_nm x1 in
       (nm,Letrec t (SOME start_nm) vs (ZIP (MAP FST fns, fns')) x1)) /\
  (renumber_code_fnames nm (Handle t x1 x2) =
     let (nm,x1) = renumber_code_fnames nm x1 in
     let (nm,x2) = renumber_code_fnames nm x2 in
       (nm,Handle t x1 x2)) /\
  (renumber_code_fnames nm (Call t ticks dest xs) =
     let (nm,xs) = renumber_code_fnames_list nm xs in
       (nm,Op t Add xs)) (* this case cannot occur *)`
 (WF_REL_TAC `inv_image $< (λx. case x of INL p => exp3_size (SND p) | INR p => exp_size (SND p))` >>
 rw [] >>
 TRY decide_tac >>
 Induct_on `fns` >>
 srw_tac [ARITH_ss] [exp_size_def] >>
 Cases_on `h` >>
 rw [exp_size_def] >>
 decide_tac);

val renumber_code_fnames_ind = theorem"renumber_code_fnames_ind";

val renumber_code_fnames_ind1 = renumber_code_fnames_ind
  |> Q.SPECL [`P`, `\_ _. T`] 
  |> UNDISCH_ALL |> CONJUNCT1 |> DISCH_ALL;

Theorem renumber_code_fnames_length
  `(∀x y. LENGTH (SND (renumber_code_fnames_list x y)) = LENGTH y)`
    (ho_match_mp_tac renumber_code_fnames_ind1 >>
    simp[renumber_code_fnames_def,UNCURRY] >> rw[] >>
    METIS_TAC[PAIR,FST,SND]);

val _ = export_theory()
