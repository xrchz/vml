(*
  Module about the built-in byte-array type.
*)
open preamble ml_translatorLib ml_progLib basisFunctionsLib
     Word8ProgTheory

val _ = new_theory "Word8ArrayProg";

val _ = translation_extends "Word8Prog";

val _ = ml_prog_update (add_dec
  ``Dtabbrev unknown_loc [] (strlit "byte_array") (Atapp [] (Short (strlit "word8array")))`` I);

val _ = ml_prog_update (open_module "Word8Array");

val _ = append_decs
   ``[mk_binop (strlit "array") Aw8alloc;
      mk_binop (strlit "sub") Aw8sub;
      mk_unop (strlit "length") Aw8length;
      Dlet unknown_loc (Pvar (strlit "update")) (Fun (strlit "x") (Fun (strlit "y") (Fun (strlit "z")
        (App Aw8update [Var (Short (strlit "x")); Var (Short (strlit "y")); Var (Short (strlit "z"))]))));
      Dlet unknown_loc (Pvar (strlit "copy"))
        (Fun (strlit "src") (Fun (strlit "srcoff") (Fun (strlit "len") (Fun (strlit "dst") (Fun (strlit "dstoff")
        (App CopyAw8Aw8 [Var (Short (strlit "src"));Var (Short (strlit "srcoff"));Var (Short (strlit "len"));
                         Var (Short (strlit "dst"));Var (Short (strlit "dstoff"))]))))));
      Dlet unknown_loc (Pvar (strlit "copyVec"))
        (Fun (strlit "src") (Fun (strlit "srcoff") (Fun (strlit "len") (Fun (strlit "dst") (Fun (strlit "dstoff")
        (App CopyStrAw8 [Var (Short (strlit "src"));Var (Short (strlit "srcoff"));Var (Short (strlit "len"));
                         Var (Short (strlit "dst"));Var (Short (strlit "dstoff"))]))))));
      Dlet unknown_loc (Pvar (strlit "substring"))
        (Fun (strlit "src") (Fun (strlit "srcoff") (Fun (strlit "len")
        (App CopyAw8Str [Var (Short (strlit "src"));Var (Short (strlit "srcoff"));Var (Short (strlit "len"))])))) ]``;

val _ = ml_prog_update (close_module NONE);

val _ = export_theory()
