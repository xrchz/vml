(*
  A theory about byte-level manipulation of machine words.
*)

open HolKernel boolLib bossLib dep_rewrite Parse
     arithmeticTheory rich_listTheory wordsTheory

val _ = new_theory "byte";

val _ = set_grammar_ancestry ["arithmetic", "list", "words"];

(* Get and set bytes in a word *)

val byte_index_def = Define `
  byte_index (a:'a word) is_bigendian =
    let d = dimindex (:'a) DIV 8 in
      if is_bigendian then 8 * ((d - 1) - w2n a MOD d) else 8 * (w2n a MOD d)`

val get_byte_def = Define `
  get_byte (a:'a word) (w:'a word) is_bigendian =
    (w2w (w >>> byte_index a is_bigendian)):word8`

val word_slice_alt_def = Define `
  (word_slice_alt h l (w:'a word) :'a word) = FCP i. l <= i /\ i < h /\ w ' i`

val set_byte_def = Define `
  set_byte (a:'a word) (b:word8) (w:'a word) is_bigendian =
    let i = byte_index a is_bigendian in
      (word_slice_alt (dimindex (:'a)) (i + 8) w
       || w2w b << i
       || word_slice_alt i 0 w)`;

(* Convert between lists of bytes and words *)

val bytes_in_word_def = Define `
  bytes_in_word = n2w (dimindex (:'a) DIV 8):'a word`;

val word_of_bytes_def = Define `
  (word_of_bytes be a [] = 0w) /\
  (word_of_bytes be a (b::bs) =
     set_byte a b (word_of_bytes be (a+1w) bs) be)`

val words_of_bytes_def = tDefine "words_of_bytes" `
  (words_of_bytes be [] = ([]:'a word list)) /\
  (words_of_bytes be bytes =
     let xs = TAKE (MAX 1 (w2n (bytes_in_word:'a word))) bytes in
     let ys = DROP (MAX 1 (w2n (bytes_in_word:'a word))) bytes in
       word_of_bytes be 0w xs :: words_of_bytes be ys)`
 (WF_REL_TAC `measure (LENGTH o SND)` \\ fs [])

val words_of_bytes_ind = theorem"words_of_bytes_ind";

Theorem LENGTH_words_of_bytes
  `8 ≤ dimindex(:'a) ⇒
   ∀be ls.
   (LENGTH (words_of_bytes be ls : 'a word list) =
    LENGTH ls DIV (w2n (bytes_in_word : 'a word)) +
    MIN 1 (LENGTH ls MOD (w2n (bytes_in_word : 'a word))))`
  (strip_tac
  \\ recInduct words_of_bytes_ind
  \\ `1 ≤ w2n bytes_in_word`
  by (
    simp[bytes_in_word_def,dimword_def]
    \\ DEP_REWRITE_TAC[LESS_MOD]
    \\ rw[DIV_LT_X, X_LT_DIV, X_LE_DIV]
    \\ match_mp_tac LESS_TRANS
    \\ qexists_tac`2 ** dimindex(:'a)`
    \\ simp[X_LT_EXP_X] )
  \\ simp[words_of_bytes_def]
  \\ conj_tac
  >- ( DEP_REWRITE_TAC[ZERO_DIV] \\ fs[] )
  \\ rw[ADD1]
  \\ `MAX 1 (w2n (bytes_in_word:'a word)) = w2n (bytes_in_word:'a word)`
      by rw[MAX_DEF]
  \\ fs[]
  \\ qmatch_goalsub_abbrev_tac`(m - n) DIV _`
  \\ Cases_on`m < n` \\ fs[]
  >- (
    `m - n = 0` by fs[]
    \\ simp[]
    \\ simp[LESS_DIV_EQ_ZERO]
    \\ rw[MIN_DEF]
    \\ fs[Abbr`m`] )
  \\ simp[SUB_MOD]
  \\ qspec_then`1`(mp_tac o GEN_ALL)(Q.GEN`q`DIV_SUB) \\ fs[]
  \\ disch_then kall_tac
  \\ Cases_on`m MOD n = 0` \\ fs[]
  >- (
    DEP_REWRITE_TAC[SUB_ADD]
    \\ fs[X_LE_DIV] )
  \\ `MIN 1 (m MOD n) = 1` by simp[MIN_DEF]
  \\ fs[]
  \\ `m DIV n - 1 + 1 = m DIV n` suffices_by fs[]
  \\ DEP_REWRITE_TAC[SUB_ADD]
  \\ fs[X_LE_DIV]);

Theorem words_of_bytes_append
  `0 < w2n(bytes_in_word:'a word) ⇒
   ∀l1 l2.
   (LENGTH l1 MOD w2n (bytes_in_word:'a word) = 0) ⇒
   (words_of_bytes be (l1 ++ l2) : 'a word list =
    words_of_bytes be l1 ++ words_of_bytes be l2)`
  (strip_tac
  \\ gen_tac
  \\ completeInduct_on`LENGTH l1`
  \\ rw[]
  \\ Cases_on`l1` \\ fs[]
  >- EVAL_TAC
  \\ rw[words_of_bytes_def]
  \\ fs[PULL_FORALL]
  >- (
    simp[TAKE_APPEND]
    \\ qmatch_goalsub_abbrev_tac`_ ++ xx`
    \\ `xx = []` suffices_by rw[]
    \\ simp[Abbr`xx`]
    \\ fs[ADD1]
    \\ rfs[MOD_EQ_0_DIVISOR]
    \\ Cases_on`d` \\ fs[] )
  \\ simp[DROP_APPEND]
  \\ qmatch_goalsub_abbrev_tac`_ ++ DROP n l2`
  \\ `n = 0`
  by (
    simp[Abbr`n`]
    \\ rfs[MOD_EQ_0_DIVISOR]
    \\ Cases_on`d` \\ fs[ADD1] )
  \\ simp[]
  \\ first_x_assum irule
  \\ simp[]
  \\ rfs[MOD_EQ_0_DIVISOR, ADD1]
  \\ Cases_on`d` \\ fs[MULT]
  \\ simp[MAX_DEF]
  \\ IF_CASES_TAC \\ fs[NOT_LESS]
  >- metis_tac[]
  \\ Cases_on`w2n bytes_in_word` \\ fs[] \\ rw[]
  \\ Cases_on`n''` \\ fs[]);

val bytes_to_word_def = Define `
  (bytes_to_word 0 a bs w be = w) /\
  (bytes_to_word (SUC k) a [] w be = w) /\
  (bytes_to_word (SUC k) a (b::bs) w be =
     set_byte a b (bytes_to_word k (a+1w) bs w be) be)`

Theorem word_of_bytes_bytes_to_word
  `∀be a bs k.
   LENGTH bs ≤ k ⇒
   (word_of_bytes be a bs = bytes_to_word k a bs 0w be)`
  (Induct_on`bs`
  >- (
    EVAL_TAC
    \\ Cases_on`k`
    \\ EVAL_TAC
    \\ rw[] )
  \\ rw[word_of_bytes_def]
  \\ Cases_on`k` \\ fs[]
  \\ rw[bytes_to_word_def]
  \\ AP_THM_TAC
  \\ AP_TERM_TAC
  \\ first_x_assum match_mp_tac
  \\ fs[]);

val _ = export_theory();