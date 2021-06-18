(*
  Encoders and decoders to/from configuration types in backend.
*)
open integerTheory ml_progTheory
     astTheory semanticPrimitivesTheory
     semanticPrimitivesPropsTheory evaluatePropsTheory
     fpSemTheory mlvectorTheory mlstringTheory
     ml_translatorTheory miscTheory
     backendTheory backend_commonTheory
     num_list_enc_decTheory num_tree_enc_decTheory;
open preamble;

val _ = new_theory "backend_enc_dec";

(* automation *)

val enc_dec_mapping =
  ref ([(“:bool”, “bool_enc'”, “bool_dec'”),
        (“:num”,  “num_enc'”,  “num_dec'” ),
        (“:int”,  “int_enc'”,  “int_dec'” ),
        (“:char”, “chr_enc'”,  “chr_dec'” )]);

fun reg_enc_dec_only ty enc dec =
   (enc_dec_mapping := (ty,enc,dec) :: (!enc_dec_mapping));

fun reg_enc_dec enc_dec_lemma = let
  val enc_dec_lemma = SPEC_ALL enc_dec_lemma
  val enc = enc_dec_lemma |> concl |> dest_eq |> fst |> rand |> rator
  val dec = enc_dec_lemma |> concl |> dest_eq |> fst |> rator
  val ty = dest_type (type_of enc) |> snd |> hd
  val _ = reg_enc_dec_only ty enc dec
  val th = MATCH_MP imp_enc_dec_ok (GEN_ALL enc_dec_lemma)
  val e = th |> concl |> rator |> rand
  val d = th |> concl |> rand
  val e_name = enc |> dest_const |> fst |> explode |> butlast |> implode
  val d_name = dec |> dest_const |> fst |> explode |> butlast |> implode
  val e_def = mk_eq(mk_var(e_name,type_of e), e)
    |> ANTIQUOTE |> single |> Define
  val d_def = mk_eq(mk_var(d_name,type_of d), d)
    |> ANTIQUOTE |> single |> Define
  val th = th |> REWRITE_RULE [GSYM e_def,GSYM d_def]
  in save_thm(e_name ^ "_dec_ok",th) end

fun get_enc_dec_for ty =
  if can listSyntax.dest_list_type ty then
    let val ty1 = listSyntax.dest_list_type ty
        val (x,y) = get_enc_dec_for ty1
    in (“list_enc' ^x”,“list_dec' ^y”) end
  else if can (match_type “:'a option”) ty then
    let val ty1 = ty |> dest_type |> snd |> hd
        val (x,y) = get_enc_dec_for ty1
    in (“option_enc' ^x”,“option_dec' ^y”) end
  else if can (match_type “:'a # 'b”) ty then
    let val (e1,d1) = ty |> dest_type |> snd |> el 1 |> get_enc_dec_for
        val (e2,d2) = ty |> dest_type |> snd |> el 2 |> get_enc_dec_for
    in (“pair_enc' ^e1 ^e2”,“pair_dec' ^d1 ^d2”) end
  else
    let val (_,x,y) = first (fn (x,_,_) => x = ty) (!enc_dec_mapping)
    in (x,y) end handle HOL_ERR _ => failwith ("Missing type: " ^ type_to_string ty)

fun enc_dec_for ty = let
  val name = type_to_string ty |> explode |> tl |> implode
             |> String.translate (fn c => if c = #"$" then "_" else implode [c])
  val enc_name = name ^ "_enc'"
  val enc_tm = mk_var(enc_name,mk_type("fun",[ty,“:num_tree”]))
  val dec_name = name ^ "_dec'"
  val dec_tm = mk_var(dec_name,mk_type("fun",[“:num_tree”,ty]))
  val _ = reg_enc_dec_only ty enc_tm dec_tm
  val cs = TypeBase.constructors_of ty
  fun arg_types ty =
    let val (n,xs) = dest_type ty
    in if n = "fun" then hd xs :: arg_types (hd (tl xs)) else [] end
  fun build_enc_eq i c = let
    val tys = type_of c |> arg_types
    val vs = mapi (fn i => fn ty => mk_var("v" ^ int_to_string i,ty)) tys
    val l = mk_comb(enc_tm,list_mk_comb(c,vs))
    val r = mk_comb(“Tree”,numSyntax.term_of_int i)
    val ws = map (fn v => mk_comb(fst (get_enc_dec_for (type_of v)),v)) vs
    val r = mk_comb(r,listSyntax.mk_list(ws, “:num_tree”))
    in mk_eq(l,r) end
  val enc_def_tm = list_mk_conj (mapi build_enc_eq cs)
  val arg = “Tree n xs”
  val xs = arg |> rand
  val l = mk_comb(dec_tm,arg)
  val nth = nth_def |> CONJUNCT1 |> SPEC_ALL |> concl |> dest_eq |> fst |> repeat rator
  fun get_nth i = mk_comb(mk_comb(nth,numSyntax.term_of_int i),xs)
  fun make_dec_ifs i [] = fail()
    | make_dec_ifs i [c] = let
        val tys = type_of c |> arg_types
        fun arg i ty = let
          val (_,dec) = get_enc_dec_for ty
          in mk_comb(dec, get_nth i) end
        val ws = mapi arg tys
        in list_mk_comb(c,ws) end
    | make_dec_ifs i (c::cs) =
        mk_cond(mk_eq(rand (rator arg), numSyntax.term_of_int i),
                make_dec_ifs i [c],
                make_dec_ifs (i+1) cs)
  val dec_def_tm = mk_eq(l,make_dec_ifs 0 cs)
  in (enc_def_tm, dec_def_tm) end

fun define_enc_dec ty = let
  val (enc_def_tm, dec_def_tm) = enc_dec_for ty
  val enc_def = Define [ANTIQUOTE enc_def_tm] |> CONJUNCTS |> map SPEC_ALL |> LIST_CONJ
  val dec_def = Define [ANTIQUOTE dec_def_tm] |> CONJUNCTS |> map SPEC_ALL |> LIST_CONJ
  val (e,x) = enc_def |> CONJUNCTS |> hd |> concl |> dest_eq |> fst |> dest_comb
  val (d,_) = dec_def |> CONJUNCTS |> hd |> concl |> dest_eq |> fst |> dest_comb
  val x = mk_var("x",type_of x)
  val goal = mk_forall(x,mk_eq(mk_comb(d,mk_comb(e,x)),x))
  val ty_n = type_to_string ty |> explode |> tl |> implode
             |> String.translate (fn c => if c = #"$" then "_" else implode [c])
  val lemma = prove(goal,Cases \\ fs [enc_def,dec_def])
  val _ = save_thm(ty_n ^ "_enc'_thm[simp]",lemma)
  val _ = reg_enc_dec lemma
  in (enc_def,dec_def,lemma) end;

(* tra *)

val (e,d) = enc_dec_for “:tra”

Definition tra_enc'_def:
  ^e
End

Definition tra_dec'_def:
  ^d
Termination
  WF_REL_TAC `measure num_tree_size`
  \\ reverse (rw [])
  \\ rpt (pop_assum mp_tac)
  \\ rpt (goal_term (fn tm =>
            tmCases_on (rand (find_term (can (match_term “nth _ _”)) tm)) []
            \\ fs [num_tree_size_def,list_dec'_def]))
  \\ rename [‘list_dec' I xs’] \\ Cases_on ‘xs’
  \\ fs [list_dec'_def] \\ rw []
  \\ imp_res_tac MEM_num_tree_size \\ fs [num_tree_size_def]
  \\ Cases_on ‘x’ \\ gvs [list_dec'_def]
  \\ fs [num_tree_size_def]
End

Theorem tra_enc'_thm[simp]:
  tra_dec' (tra_enc' x) = x
Proof
  Induct_on ‘x’ \\ fs [tra_enc'_def,Once tra_dec'_def]
QED

val _ = reg_enc_dec tra_enc'_thm;

val res = define_enc_dec “:var_name”
val res = define_enc_dec “:word_size”
val res = define_enc_dec “:opw”
val res = define_enc_dec “:ast$shift”
val res = define_enc_dec “:fp_cmp”
val res = define_enc_dec “:fp_uop”
val res = define_enc_dec “:fp_bop”
val res = define_enc_dec “:fp_top”
val res = define_enc_dec “:closLang$op”
val res = define_enc_dec “:mlstring”

(* closLang's exp *)

val (e,d) = enc_dec_for “:closLang$exp”

Triviality MEM_exp_size:
  (∀xs x. MEM x xs ⇒ exp_size x ≤ closLang$exp3_size xs) ∧
  (∀xs x y. MEM (x,y) xs ⇒ exp_size y ≤ closLang$exp1_size xs)
Proof
  rpt conj_tac
  \\ Induct \\ fs [] \\ rw [] \\ fs [closLangTheory.exp_size_def]
  \\ res_tac \\ fs []
QED

Definition closLang_exp_enc'_def:
  ^e
Termination
  WF_REL_TAC ‘measure closLang$exp_size’ \\ rw []
  \\ imp_res_tac MEM_exp_size \\ gvs []
End

Definition closLang_exp_dec'_def:
  ^d
Termination
  WF_REL_TAC `measure num_tree_size`
  \\ reverse (rw [])
  \\ rpt (pop_assum mp_tac)
  \\ rpt (goal_term (fn tm =>
            tmCases_on (rand (find_term (can (match_term “nth _ _”)) tm)) []
            \\ fs [num_tree_size_def,list_dec'_def]))
  \\ rename [‘list_dec' I xs’] \\ Cases_on ‘xs’
  \\ fs [list_dec'_def] \\ rw []
  \\ imp_res_tac MEM_num_tree_size \\ fs [num_tree_size_def]
  \\ Cases_on ‘x’ \\ gvs [list_dec'_def]
  \\ fs [num_tree_size_def]
End

Triviality bvl_MEM_exp_size:
  (∀xs x. MEM x xs ⇒ exp_size x ≤ bvl$exp1_size xs)
Proof
  Induct \\ fs [] \\ rw [] \\ fs [bvlTheory.exp_size_def]
  \\ res_tac \\ fs []
QED

Theorem closLang_exp_enc'_thm[simp]:
  ∀x. closLang_exp_dec' (closLang_exp_enc' x) = x
Proof
  ho_match_mp_tac closLang_exp_enc'_ind \\ rw []
  \\ fs [closLang_exp_enc'_def]
  \\ once_rewrite_tac [closLang_exp_dec'_def] \\ gvs []
  \\ fs [SF ETA_ss]
  \\ match_mp_tac list_enc'_mem \\ fs [] \\ rw []
  \\ match_mp_tac pair_enc'_fst_snd
  \\ rename [‘MEM y ys’] \\ PairCases_on ‘y’ \\ gvs []
QED

val _ = reg_enc_dec closLang_exp_enc'_thm;

(* BVL's exp *)

val (e,d) = enc_dec_for “:bvl$exp”

Definition bvl_exp_enc'_def:
  ^e
Termination
  WF_REL_TAC ‘measure bvl$exp_size’ \\ rw []
  \\ imp_res_tac bvl_MEM_exp_size \\ gvs []
End

Definition bvl_exp_dec'_def:
  ^d
Termination
  WF_REL_TAC `measure num_tree_size`
  \\ reverse (rw [])
  \\ rpt (pop_assum mp_tac)
  \\ rpt (goal_term (fn tm =>
            tmCases_on (rand (find_term (can (match_term “nth _ _”)) tm)) []
            \\ fs [num_tree_size_def,list_dec'_def]))
  \\ rename [‘list_dec' I xs’] \\ Cases_on ‘xs’
  \\ fs [list_dec'_def] \\ rw []
  \\ imp_res_tac MEM_num_tree_size \\ fs [num_tree_size_def]
End

Theorem bvl_exp_enc'_thm[simp]:
  ∀x. bvl_exp_dec' (bvl_exp_enc' x) = x
Proof
  ho_match_mp_tac bvl_exp_enc'_ind \\ rw []
  \\ fs [bvl_exp_enc'_def]
  \\ once_rewrite_tac [bvl_exp_dec'_def] \\ gvs []
  \\ fs [SF ETA_ss]
  \\ match_mp_tac list_enc'_mem \\ fs []
QED

val _ = reg_enc_dec bvl_exp_enc'_thm;

(* val_approx *)

val (e,d) = enc_dec_for “:val_approx”

Definition val_approx_enc'_def:
  ^e
Termination
  WF_REL_TAC ‘measure val_approx_size’ \\ rw []
  \\ qsuff_tac ‘val_approx_size a ≤ val_approx1_size v1’ \\ fs []
  \\ pop_assum mp_tac \\ rename [‘MEM a xs’]
  \\ Induct_on ‘xs’ \\ fs [] \\ rw [clos_knownTheory.val_approx_size_def]
  \\ gvs [clos_knownTheory.val_approx_size_def]
End

Definition val_approx_dec'_def:
  ^d
Termination
  WF_REL_TAC `measure num_tree_size`
  \\ reverse (rw [])
  \\ rpt (pop_assum mp_tac)
  \\ rpt (goal_term (fn tm =>
            tmCases_on (rand (find_term (can (match_term “nth _ _”)) tm)) []
            \\ fs [num_tree_size_def,list_dec'_def]))
  \\ rename [‘list_dec' I xs’] \\ Cases_on ‘xs’
  \\ fs [list_dec'_def] \\ rw []
  \\ imp_res_tac MEM_num_tree_size \\ fs [num_tree_size_def]
End

Theorem val_approx_enc'_thm[simp]:
  ∀x. val_approx_dec' (val_approx_enc' x) = x
Proof
  ho_match_mp_tac val_approx_enc'_ind \\ rw []
  \\ fs [val_approx_enc'_def]
  \\ once_rewrite_tac [val_approx_dec'_def] \\ gvs []
  \\ fs [SF ETA_ss]
  \\ match_mp_tac list_enc'_mem \\ fs []
QED

val _ = reg_enc_dec val_approx_enc'_thm;



(*

  <| source_conf : source_to_flat$config
   ; clos_conf : clos_to_bvl$config
   ; bvl_conf : bvl_to_bvi$config
   ; data_conf : data_to_word$config
   ; word_to_word_conf : word_to_word$config
   ; word_conf : 'a word_to_stack$config
   ; stack_conf : stack_to_lab$config
   ; lab_conf : 'a lab_to_target$config
   ; tap_conf : tap_config

  source_to_flat$config =
           <| next : next_indices
            ; mod_env : environment
            ; pattern_cfg : flat_pattern$config

  where

  next_indices = <| vidx : num; tidx : num; eidx : num |>

  var_name = Glob tra num | Local tra string

  environment =
    <| c : (modN, conN, num # num option) namespace;
       v : (modN, varN, var_name) namespace; |>

  flat_pattern$config =
  <| pat_heuristic : (* pattern_matching$branch list *) unit -> num ;  (* problem! *)
    type_map : (num # num) list spt |>

  clos_to_bvl$config =
           <| next_loc : num
            ; start : num
            ; do_mti : bool
            ; known_conf : clos_known$config option
            ; do_call : bool
            ; call_state : num_set # (num, num # closLang$exp) alist
            ; max_app : num
            |>

  clos_known$config =
           <| inline_max_body_size : num
            ; inline_factor : num
            ; initial_inline_factor : num
            ; val_approx_spt : val_approx spt
            |>`;

  bvl_to_bvi$config =
           <| inline_size_limit : num (* zero disables inlining *)
            ; exp_cut : num (* huge number effectively disables exp splitting *)
            ; split_main_at_seq : bool (* split main expression at Seqs *)
            ; next_name1 : num (* there should be as many of       *)
            ; next_name2 : num (* these as bvl_to_bvi_namespaces-1 *)
            ; inlines : (num # bvl$exp) spt
            |>

  data_to_word$config = <| tag_bits : num (* in each pointer *)
            ; len_bits : num (* in each pointer *)
            ; pad_bits : num (* in each pointer *)
            ; len_size : num (* size of length field in block header *)
            ; has_div : bool (* Div available in target *)
            ; has_longdiv : bool (* LongDiv available in target *)
            ; has_fp_ops : bool (* can compile floating-point ops *)
            ; has_fp_tern : bool (* can compile FMA *)
            ; call_empty_ffi : bool (* emit (T) / omit (F) calls to FFI "" *)
            ; gc_kind : gc_kind (* GC settings *) |>

  word_to_word$config =
  <| reg_alg : num
   ; col_oracle : num -> (num num_map) option |>

  word_to_stack$config = <| bitmaps : 'a word list ;
                            stack_frame_size : num spt |>

  stack_to_lab$config =
  <| reg_names : num num_map
   ; jump : bool (* whether to compile to JumpLower or If Lower ... in stack_remove*)
   |>

  lab_to_target$config =
           <| labels : num num_map num_map
            ; pos : num
            ; asm_conf : 'a asm_config
            ; init_clock : num
            ; ffi_names : string list option
            ; hash_size : num
            |>

  asm_config =
    <| ISA            : architecture
     ; encode         : 'a asm -> word8 list
     ; big_endian     : bool
     ; code_alignment : num
     ; link_reg       : num option
     ; avoid_regs     : num list
     ; reg_count      : num
     ; fp_reg_count   : num  (* set to 0 if float not available *)
     ; two_reg_arith  : bool
     ; valid_imm      : (binop + cmp) -> 'a word -> bool
     ; addr_offset    : 'a word # 'a word
     ; byte_offset    : 'a word # 'a word
     ; jump_offset    : 'a word # 'a word
     ; cjump_offset   : 'a word # 'a word
     ; loc_offset     : 'a word # 'a word
     |>

  tap_config = Tap_Config
    (* save filename prefix *) mlstring
    (* bits which should be saved. the boolean indicates
       the presence of a '*' suffix, and matches all suffixes *)
    ((mlstring # bool) list)

*)

val _ = export_theory();
