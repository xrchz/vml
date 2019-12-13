(*
  A module about the char type for the CakeML standard basis library.
*)
open preamble ml_translatorLib ml_progLib basisFunctionsLib
     RatProgTheory

val _ = new_theory "CharProg";

val _ = translation_extends "RatProg";

(* Char module -- translated *)

val _ = ml_prog_update (open_module "Char");

val () = generate_sigs := true;

val _ = ml_prog_update (add_dec
  ``Dtabbrev unknown_loc [] "char" (Atapp [] (Short "char"))`` I);

val _ = trans "ord" stringSyntax.ord_tm;
val _ = trans "chr" stringSyntax.chr_tm;
val _ = trans "<" stringSyntax.char_lt_tm;
val _ = trans ">" stringSyntax.char_gt_tm;
val _ = trans "<=" stringSyntax.char_le_tm;
val _ = trans ">=" stringSyntax.char_ge_tm;

val _ = next_ml_names := ["isSpace"];
val res = translate stringTheory.isSpace_def;

val _ = next_ml_names := ["isUpper"];
val res = translate stringTheory.isUpper_def;

val _ = next_ml_names := ["isLower"];
val res = translate stringTheory.isLower_def;

val _ = next_ml_names := ["isDigit"];
val res = translate stringTheory.isDigit_def;

val _ = next_ml_names := ["isAlpha"];
val res = translate stringTheory.isAlpha_def;

val _ = next_ml_names := ["isAlphaNum"];
val res = translate stringTheory.isAlphaNum_def;

val sigs = module_signatures [
  "ord",
  "chr",
  "<",
  ">",
  "<=",
  ">=",
  "isSpace",
  "isUpper",
  "isLower",
  "isDigit",
  "isAlpha",
  "isAlphaNum"
];

val _ = ml_prog_update (close_module (SOME sigs));

val _ = export_theory()
