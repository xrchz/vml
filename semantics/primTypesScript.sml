(*Generated by Lem from primTypes.lem.*)
open HolKernel Parse boolLib bossLib;
open lem_pervasivesTheory libTheory astTheory namespaceTheory ffiTheory semanticPrimitivesTheory evaluateTheory typeSystemTheory;

val _ = numLib.prefer_num();



val _ = new_theory "primTypes"

(*
  Definition of the primitive types that are in scope before any CakeML program
  starts. Some of them are generated by running an initial program.
*)
(*open import Pervasives*)
(*open import Ast*)
(*open import SemanticPrimitives*)
(*open import Ffi*)
(*open import Namespace*)
(*open import Lib*)
(*open import Evaluate*)

(* The ordering in the following is important. The stamps generated from the
   exceptions and types must match those in semanticPrimitives *)
(*val prim_types_program : list dec*)
val _ = Define `
 (prim_types_program=  
 ([Dexn unknown_loc "Bind" [];
   Dexn unknown_loc "Chr" [];
   Dexn unknown_loc "Div" [];
   Dexn unknown_loc "Subscript" [];
   Dtype unknown_loc [([], "bool", [("False", []); ("True", [])])];
   Dtype unknown_loc [(["'a"], "list", [("[]", []); ("::", [Atvar "'a"; Atapp [Atvar "'a"] (Short "list")]) ])] ]))`;


(*val add_to_sem_env :
  forall 'ffi. Eq 'ffi => (state 'ffi * sem_env v) -> list dec -> maybe (state 'ffi * sem_env v)*)
val _ = Define `
 (add_to_sem_env (st, env) prog=  
 ((case evaluate_decs st env prog of
    (st', Rval env') => SOME (st', extend_dec_env env' env)
  | _ => NONE
  )))`;


(*val prim_sem_env : forall 'ffi. Eq 'ffi => ffi_state 'ffi -> maybe (state 'ffi * sem_env v)*)
val _ = Define `
 (prim_sem_env ffi=  
 (add_to_sem_env
    (<| clock :=(( 0 : num)); ffi := ffi; refs := ([]); next_type_stamp :=(( 0 : num));
        next_exn_stamp :=(( 0 : num)); next_env_stamp :=(( 0 : num)); eval := default_eval_state |>,
     <| v := nsEmpty; c := nsEmpty |>)
        prim_types_program))`;


(*open import TypeSystem*)

val _ = Define `
 (prim_tenv=    
 (<| c := (alist_to_ns (REVERSE
          [("Bind", ([],[],Texn_num));
           ("Chr", ([],[],Texn_num));
           ("Div", ([],[],Texn_num));
           ("Subscript", ([],[],Texn_num));
           ("False", ([],[], Tbool_num));
           ("True", ([],[], Tbool_num));
           ("[]", (["'a"],[],Tlist_num));
           ("::", (["'a"],[Tvar "'a"; Tlist (Tvar "'a")], Tlist_num))]));
       v := nsEmpty;
       t := (alist_to_ns (REVERSE
          [
          ("array",(["'a"],Tapp [Tvar "'a"] Tarray_num));
          ("bool",([],Tapp [] Tbool_num));
          ("char",([],Tapp [] Tchar_num));
          ("exn",([],Tapp [] Texn_num));
          (* Tfn is ->, specially handled *)
          ("int",([],Tapp [] Tint_num));
          ("list",(["'a"],Tapp [Tvar "'a"] Tlist_num));
          ("ref",(["'a"],Tapp [Tvar "'a"] Tref_num));
          ("string",([],Tapp [] Tstring_num));
          ("unit",([],Tapp [] Ttup_num));
          (* pairs are specially handled *)
          ("vector",(["'a"],Tapp [Tvar "'a"] Tvector_num));
          ("word64",([],Tapp [] Tword64_num));
          ("word8",([],Tapp [] Tword8_num));
          ("word8array",([],Tapp [] Tword8array_num))]
          ))|>))`;


val _ = Define `
 (prim_type_ids=  (LIST_TO_SET (Tlist_num :: (Tbool_num :: prim_type_nums))))`;

val _ = export_theory()

