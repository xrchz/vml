(*
  A module about Arrays for the CakeML standard basis library.
*)
open preamble ml_translatorLib ml_progLib basisFunctionsLib
     Word8ArrayProgTheory

val _ = new_theory"ArrayProg"

val _ = translation_extends"Word8ArrayProg"

val () = ml_prog_update (open_module "Array");

val _ = ml_prog_update (add_dec
  ``Dtabbrev unknown_loc [strlit "'a"] (strlit "array") (Atapp [Atvar (strlit "'a")] (Short (strlit "array")))`` I);

val () = append_decs
   ``[mk_binop (strlit "array") Aalloc;
      mk_unop (strlit "arrayEmpty") AallocEmpty;
      mk_binop (strlit "sub") Asub;
      mk_unop (strlit "length") Alength;
      Dlet unknown_loc (Pvar (strlit "update"))
       (Fun (strlit "x") (Fun (strlit "y") (Fun (strlit "z")
         (App Aupdate [Var (Short (strlit "x")); Var (Short (strlit "y")); Var (Short (strlit "z"))])))) ]``;

val array_fromList = process_topdecs
  `fun fromList l =
    let fun f arr l i =
       case l of
          [] => arr
        | (h::t) => (update arr i h; f arr t (i + 1))
    in
      case l of
        [] => arrayEmpty ()
      | h::t => f (array (List.length l) h) t 1
    end`;

val _ = append_prog array_fromList;

val array_tabulate = process_topdecs
  `fun tabulate n f =
    let fun u arr x =
        if x = n then arr
        else (update arr x (f x); u arr (x + 1))
    in
      if n = 0 then
        arrayEmpty ()
      else
        u (array n (f 0)) 1
    end`;

val _ = append_prog array_tabulate;

(*val array_vector = process_topdecs
  `fun vector arr = Vector.tabulate (length arr) (fn i => sub arr i)`*)

val _ = ml_prog_update open_local_block;

val array_copy_aux = process_topdecs
  `fun copy_aux src dst di max n =
    if n = max
      then ()
    else (update dst di (sub src n); copy_aux src dst (di + 1) max (n + 1))`

val _ = append_prog array_copy_aux;

val _ = ml_prog_update open_local_in_block;

val array_copy = process_topdecs
  `fun copy src dst di =
    copy_aux src dst di (length src) 0`

val _ = append_prog array_copy;

val _ = ml_prog_update open_local_block;

val array_copyVec_aux = process_topdecs
  `fun copyVec_aux src dst di max n =
    if n = max
        then ()
    else (update dst (di + n) (Vector.sub src n); copyVec_aux src dst di max (n + 1))`

val _ = append_prog array_copyVec_aux;

val _ = ml_prog_update open_local_in_block;

val array_copyVec = process_topdecs
  `fun copyVec src dst di =
    copyVec_aux src dst di (Vector.length src) 0`

val _ = append_prog array_copyVec;

val _ = ml_prog_update open_local_block;

val array_app_aux = process_topdecs
  `fun app_aux f arr max n =
    if n = max
      then ()
    else (f (sub arr n); app_aux f arr max (n + 1))`

val _ = append_prog array_app_aux;

val _ = ml_prog_update open_local_in_block;

val array_app = process_topdecs
  `fun app f arr =
    app_aux f arr (length arr) 0`

val _ = append_prog array_app;

val _ = ml_prog_update open_local_block;

val array_appi_aux = process_topdecs
  `fun appi_aux f arr max n =
    if n = max
      then ()
    else (f n (sub arr n); app_aux f arr max (n + 1))`

val _ = append_prog array_appi_aux;

val _ = ml_prog_update open_local_in_block;

val array_appi = process_topdecs
  `fun appi f arr =
    appi_aux f arr (length arr) 0`

val _ = append_prog array_appi;

val _ = ml_prog_update open_local_block;

val array_modify_aux = process_topdecs
  `fun modify_aux f arr max n =
    if n = max
      then ()
    else (update arr n (f (sub arr n)); modify_aux f arr max (n + 1))`

val _ = append_prog array_modify_aux;

val _ = ml_prog_update open_local_in_block;

val array_modify = process_topdecs
  `fun modify f arr =
    modify_aux f arr (length arr) 0`

val _ = append_prog array_modify;

val _ = ml_prog_update open_local_block;

val array_modifyi_aux = process_topdecs
  `fun modifyi_aux f arr max n =
    if n = max
      then ()
    else (update arr n (f n (sub arr n)); modifyi_aux f arr max (n + 1))`

val _ = append_prog array_modifyi_aux;

val _ = ml_prog_update open_local_in_block;

val array_modifyi = process_topdecs
  `fun modifyi f arr =
    modifyi_aux f arr (length arr) 0`

val _ = append_prog array_modifyi;

val _ = ml_prog_update open_local_block;

val array_foldli_aux = process_topdecs
  `fun foldli_aux f init arr max n =
    if n = max
      then init
    else foldli_aux f (f n (sub arr n) init ) arr max (n + 1)`

val _ = append_prog array_foldli_aux;

val _ = ml_prog_update open_local_in_block;

val array_foldli = process_topdecs
  `fun foldli f init arr =
    foldli_aux f init arr (length arr) 0`

val _ = append_prog array_foldli;

val _ = ml_prog_update open_local_block;

val array_foldl_aux = process_topdecs
  `fun foldl_aux f init arr max n =
    if n = max
      then init
    else foldl_aux f (f (sub arr n) init ) arr max (n + 1)`

val _ = append_prog array_foldl_aux;

val _ = ml_prog_update open_local_in_block;

val array_foldl = process_topdecs
  `fun foldl f init arr =
    foldl_aux f init arr (length arr) 0`

val _ = append_prog array_foldl;

val _ = ml_prog_update open_local_block;

val array_foldri_aux = process_topdecs
  `fun foldri_aux f init arr n =
    if n = 0
      then init
    else foldri_aux f (f (n - 1) (sub arr (n - 1)) init) arr (n - 1)`

val _ = append_prog array_foldri_aux;

val _ = ml_prog_update open_local_in_block;

val array_foldri = process_topdecs
  `fun foldri f init arr =
    foldri_aux f init arr (length arr)`

val _ = append_prog array_foldri;

val _ = ml_prog_update open_local_block;

val array_foldr_aux = process_topdecs
  `fun foldr_aux f init arr n =
    if n = 0
      then init
    else foldr_aux f (f (sub arr (n - 1)) init) arr (n - 1)`

val _ = append_prog array_foldr_aux;

val _ = ml_prog_update open_local_in_block;

val array_foldr = process_topdecs
  `fun foldr f init arr =
    foldr_aux f init arr (length arr)`

val _ = append_prog array_foldr;

val _ = ml_prog_update open_local_block;

val array_find_aux = process_topdecs
  `fun find_aux f arr max n =
    if n = max
      then None
    else (if f (sub arr n)
        then Some(sub arr n)
      else find_aux f arr max (n + 1))`

val _ = append_prog array_find_aux;

val _ = ml_prog_update open_local_in_block;

val array_find = process_topdecs
  `fun find f arr =
    find_aux f arr (length arr) 0`

val _ = append_prog array_find;

val _ = ml_prog_update open_local_block;

(* Parser bug, see Issue #25 *)
val array_findi_aux =
``[(Dletrec unknown_loc
[(strlit "findi_aux", strlit "f",
 Fun (strlit "arr")
   (Fun (strlit "max")
      (Fun (strlit "n")
         (Let (SOME (strlit "a"))
            (App Opapp
               [App Opapp [Var (Short (strlit "=")); Var (Short (strlit "n"))];
                Var (Short (strlit "max"))])
            (If (Var (Short (strlit "a"))) (Con (SOME (Short (strlit "None"))) [])
               (Let (SOME (strlit "b"))
                  (App Opapp
                     [App Opapp
                        [Var (Short (strlit "sub")); Var (Short (strlit "arr"))];
                      Var (Short (strlit "n"))])
                  (Let (SOME (strlit "c"))
                     (App Opapp
                        [App Opapp
                           [Var (Short (strlit "f")); Var (Short (strlit "n"))];
                         Var (Short (strlit "b"))])
                     (If (Var (Short (strlit "c")))
                        (Let (SOME (strlit "d"))
                           (App Opapp
                              [App Opapp
                                 [Var (Short (strlit "sub"));
                                  Var (Short (strlit "arr"))];
                               Var (Short (strlit "n"))])
                           (Con (SOME (Short (strlit "Some")))
                              [Con NONE [Var (Short (strlit "n"));
                               Var (Short (strlit "d"))]]))
                        (Let (SOME (strlit "e"))
                           (App Opapp
                              [App Opapp
                                 [Var (Short (strlit "+"));
                                  Var (Short (strlit "n"))];
                               Lit (IntLit 1)])
                           (App Opapp
                              [App Opapp
                                 [App Opapp
                                    [App Opapp
                                       [Var (Short (strlit "findi_aux"));
                                        Var (Short (strlit "f"))];
                                     Var (Short (strlit "arr"))];
                                  Var (Short (strlit "max"))];
                               Var (Short (strlit "e"))]))))))))))])]``

val _ = append_prog array_findi_aux;

val _ = ml_prog_update open_local_in_block;

val array_findi = process_topdecs
  `fun findi f arr =
    findi_aux f arr (length arr) 0`

val _ = append_prog array_findi;

val _ = ml_prog_update open_local_block;

val array_exists_aux = process_topdecs
  `fun exists_aux f arr max n =
    if n = max
      then False
    else (if f (sub arr n)
      then True
    else exists_aux f arr max (n + 1))`

val _ = append_prog array_exists_aux;

val _ = ml_prog_update open_local_in_block;

val array_exists = process_topdecs
  `fun exists f arr =
    exists_aux f arr (length arr) 0`

val _ = append_prog array_exists;

val _ = ml_prog_update open_local_block;

val array_all_aux = process_topdecs
  `fun all_aux f arr max n =
    if n = max
      then True
    else (if f (sub arr n)
      then all_aux f arr max (n + 1)
    else False)`

val _ = append_prog array_all_aux;

val _ = ml_prog_update open_local_in_block;

val array_all = process_topdecs
  `fun all f arr =
    all_aux f arr (length arr) 0`

val _ = append_prog array_all;

val _ = ml_prog_update open_local_block;

val array_collate_aux = process_topdecs
  `fun collate_aux f a1 a2 max ord n =
    if n = max
      then ord
    else (if f (sub a1 n) (sub a2 n) = Equal
        then collate_aux f a1 a2 max ord (n + 1)
      else f (sub a1 n) (sub a2 n))`

val _ = append_prog array_collate_aux;

val _ = ml_prog_update open_local_in_block;

val array_collate = process_topdecs
  `fun collate f a1 a2 =
    if (length a1) < (length a2)
      then collate_aux f a1 a2 (length a1) Less 0
    else if (length a2) < (length a1)
      then collate_aux f a1 a2 (length a2) Greater 0
    else collate_aux f a1 a2 (length a2) Equal 0`

val _ = append_prog array_collate;

val _ = ml_prog_update close_local_blocks;

val _ = ml_prog_update (close_module NONE);

val _ = export_theory ()
