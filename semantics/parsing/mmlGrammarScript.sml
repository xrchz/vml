open HolKernel Parse boolLib bossLib

open TokensTheory AstTheory grammarTheory

val _ = new_theory "mmlGrammar"

val _ = Hol_datatype`
  MMLnonT = nV |
    nEbase | nEapp | nEmult | nEadd | nErel | nEcomp | nEbefore
  | nElogic | nE | nError | nLogicalOp | nLiteral | nFDecl
  | nAndFDecls | nPEs | nPE
  | nPattern | nType | nDType | nTypeList | nTypeDec | nDtypeDecls
  | nDtypeDecl | nTypeName | nTyVarList | nDconstructor | nDtypeCons
  | nStarTypes | nDecl
  | nMultOps | nAddOps | nRelOps | nCompOps | nBeforeOps
`;

val _ = type_abbrev("NT", ``:MMLnonT inf``)
val _ = overload_on("mkNT", ``INL : MMLnonT -> NT``)

val _ = overload_on ("NN", ``\nt. NT (mkNT nt)``)
val _ = overload_on ("TK", ``TOK : token -> (token,MMLnonT)symbol``)

val V_rules_def = Define`
  V_rules =
   {(mkNT nV, [TK (AlphaT s)]) | T } ∪
   {(mkNT nV, [TK (SymbolT s)]) | T } ∪
   {(mkNT nV, [TK OpT; TK (SymbolT s)]) | T }`

val mkRules_def = Define`
  mkRules n rset = IMAGE (\r. (mkNT n, r)) rset
`

val Ebase_rules_def = Define`
  Ebase_rules =
    mkRules nEbase
      ({[TK LparT; NN nE; TK RparT];
        [NN nV];
        [TK LetT; TK ValT; NN nV; TK EqualsT; NN nE; TK InT;
         NN nE; TK EndT];
        [TK LetT; TK FunT; NN nAndFDecls; TK InT; NN nE; TK EndT]} ∪
      { [TK (IntT i)] | T })
`

val binop_rule_def = Define`
  binop_rule tight loose opn = mkRules loose {
    [NN loose; NN opn; NN tight];
    [NN tight]
  }`

val Eapp_rules_def = Define`
  Eapp_rules = mkRules nEapp {
    [NN nEapp; NN nEbase];
    [NN nEbase]
  }`

val MultOps_rules_def = Define`
  MultOps_rules = mkRules nMultOps {
    [TK (AlphaT "div")];
    [TK (AlphaT "mod")];
    [TK (SymbolT "*")];
    [TK (SymbolT "/")]
  }`;

(* various left associative binary operators *)
val Emult_rules_def = Define`
  Emult_rules = binop_rule nEapp nEmult nMultOps
`;
val Eadd_rules_def = Define`
  Eadd_rules = binop_rule nEmult nEadd nAddOps
`;
val Erel_rules_def = Define`
  Erel_rules = binop_rule nEadd nErel nRelOps
`;
val Ecomp_rules_def = Define`
  Ecomp_rules = binop_rule nErel nEcomp nCompOps
`;
val Ebefore_rules_def = Define`
  Ebefore_rules = binop_rule nEcomp nEbefore nBeforeOps
`;

(* ----------------------------------------------------------------------
    Parse trees to abstract syntax
   ---------------------------------------------------------------------- *)

val _ = type_abbrev("mlptree", ``:(token, MMLnonT) parsetree``)

open monadsyntax
val _ = overload_on ("monad_bind", ``OPTION_BIND``)

val _ = computeLib.add_persistent_funs ["option.OPTION_BIND_def"]

val ptree_Op_def = Define`
  ptree_Op (Lf _) = NONE ∧
  ptree_Op (Nd nt subs) =
    case nt of
      mkNT nMultOps =>
        (case subs of
           [Lf (TK (SymbolT "*"))] => SOME "*"
         | [Lf (TK (SymbolT "/"))] => SOME "/"
         | [Lf (TK (AlphaT "mod"))] => SOME "mod"
         | [Lf (TK (AlphaT "div"))] => SOME "div"
         | _ => NONE)
    | mkNT nAddOps =>
        (case subs of
           [Lf (TK (SymbolT "+"))] => SOME "+"
         | [Lf (TK (SymbolT "-"))] => SOME "-"
         | _ => NONE)
    | _ => NONE
`;

val ptree_Expr_def = Define`
  ptree_Expr (Lf _) = NONE ∧
  ptree_Expr (Nd nt subs) =
    case nt of
      mkNT nEbase =>
        (case subs of
           [Lf (TK LparT); Nd t s; Lf (TK RparT)] => ptree_Expr (Nd t s)
         | [Lf (TK (IntT i))] => SOME (Ast_Lit (IntLit i))
         | _ => NONE)
   | mkNT nEapp =>
       (case subs of
          [t1; t2] => do
            a1 <- ptree_Expr t1;
            a2 <- ptree_Expr t2;
            SOME(Ast_App a1 a2)
          od
        | [t] => ptree_Expr t
        | _ => NONE)
   | mkNT nEmult =>
       (case subs of
          [t1; opt; t2] => do (* s will be *, /, div, or mod *)
            a1 <- ptree_Expr t1;
            a_op <- ptree_Op opt;
            a2 <- ptree_Expr t2;
            SOME(Ast_App (Ast_App (Ast_Var a_op) a1) a2)
          od
        | [t] => ptree_Expr t
        | _ => NONE)
   | _ => NONE
`;

val ast = ``Nd (mkNT nEmult) [
              Nd (mkNT nEmult) [
                Nd (mkNT nEmult) [
                  Nd (mkNT nEapp) [Nd (mkNT nEbase) [Lf (TK (IntT 3))]]
                ];
                Nd (mkNT nMultOps) [Lf (TK (SymbolT "*"))];
                Nd (mkNT nEapp) [Nd (mkNT nEbase) [Lf (TK (IntT 4))]]
              ];
              Nd (mkNT nMultOps) [Lf (TK (SymbolT "*"))];
              Nd (mkNT nEapp) [Nd (mkNT nEbase) [Lf (TK (IntT 5))]]
            ]``

val parse_result = EVAL ``ptree_Expr ^ast``;

(* would use EVAL for this too, but it fails to turn (∃i. F) into F, and can't
   be primed with that as a rewrite rule.

   Nor does

     val _ = computeLib.add_conv (existential, 1, REWR_CONV EXISTS_SIMP)

   work (can't see why)
*)
val check_results =
    time (SIMP_CONV (srw_ss())
              [valid_ptree_def, Eapp_rules_def, Ebase_rules_def,
               MultOps_rules_def, Emult_rules_def, mkRules_def,
               binop_rule_def, DISJ_IMP_THM, FORALL_AND_THM])
   ``valid_ptree <| rules := Eapp_rules ∪ Ebase_rules ∪ MultOps_rules ∪
                             Emult_rules; start := mkNT nEmult |> ^ast``

val _ = if aconv (rhs (concl check_results)) T then print "valid_ptree: OK\n"
        else raise Fail "valid_ptree: failed"

val _ = export_theory()
