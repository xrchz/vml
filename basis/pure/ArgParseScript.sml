(*
  Pure functions for parsing of command-line arguments.
*)
open preamble mlstringTheory;

val _ = new_theory "ArgParse";

(* Datatype representing each posible argument/flag/option in a
   typical command line argument list (eg: char* argv[] in C)
*)
Datatype:
  arg =
  (* Simple flags of the form -<ident> eg: -h *)
         ShortFlag mlstring
  (* Long flags of the form --<ident>+ eg: --help *)
       | LongFlag mlstring
  (* Long flags with option of the form --<ident>+=<ident>+
     eg: --arch=arm6 *)
       | OptionFlag mlstring mlstring
  (* Standalone option of the form <ident>+ eg: cake.S*)
       | Option mlstring
  (* Where <ident> is equal to the regular expression [a-zA-Z0-9.-/_]
     (or similar) *)
End

(* An arbitrary term of 'arg' to serve as ARB in some definitions *)
Definition arb_arg_def:
  arb_arg = Option (implode "")
End

(* Destructors for 'arg' terms *)

Definition destShortFlag_def:
  destShortFlag (ShortFlag flag) = flag ∧
  destShortFlag _ = (implode "")
End

Definition destOption_def:
  destOption (Option opt) = opt ∧
  destOption _ = (implode "")
End

Definition destLongFlag_def:
  destLongFlag (LongFlag flag) = flag ∧
  destLongFlag _ = (implode "")
End

Definition destOptionFlag_def:
  destOptionFlag (OptionFlag flag opt) = (flag,opt) ∧
  destOptionFlag _ = ((implode ""),(implode ""))
End

(* Auxiliary functions *)

(* Get the name of each flag and the empty string in case of an option *)
Definition getFlagName_def:
  getFlagName (ShortFlag f)    = f   ∧
  getFlagName (LongFlag f)     = f   ∧
  getFlagName (OptionFlag f _) = f ∧
  getFlagName _                = implode ""
End

(* Wheter the argument is a Flag *)
Definition isFlag_def:
  isFlag (Option _) = F ∧
  isFlag _          = T
End

(* Pretty prints values or type 'arg' *)
Definition showFlag_def:
  showFlag (ShortFlag f)     = implode "-"  ^ f ∧
  showFlag (LongFlag f)      = implode "--" ^ f ∧
  showFlag (OptionFlag f s)  = implode "--" ^ f ^ implode "=" ^ s ∧
  showFlag (Option s)        = s
End

(* Expands shortFlag(s) into single values when grouped in a single
   shortFlag (eg: '[ShortFlag "ab"]' expands to [ShortFlag "a", ShortFlag "b"])
 *)

Definition expandArgs_def:
  expandArgs l =
    let expandFlags = MAP (ShortFlag o str) o explode;
        expand = λx l.
          case x of ShortFlag x => expandFlags x ++ l
                  | _           => x :: l
    in FOLDR expand [] l
End

(* Flags description types *)
Datatype:
  flagConf = <|
    name       : mlstring; (* Long flag  ("-"  if disable) *)
    short      : char;     (* Short flag (#"-" if disable) *)
    desc       : mlstring; (* Short description used in the help msg *)
    has_option : bool;     (* Does it have and acompaning option/value? *)
    (* Continuation modifing the underlying structure
       representing the options where 'flag.cont opt x' takes
       an optional value 'opt' and a value 'x' of ''a' and
       uses these to update 'x' to represent the precense of
       the flag 'flag.name' or 'flag.short' with potentially
       some argument
     *)
    cont : mlstring option -> 'a -> 'a |>
End


Definition matchArgs_def:
  matchArg [] arg mOpt a =
    (if isFlag arg then INL (implode "Unrecognized flag: " ^ showFlag arg)
     (* TODO: Check for extra options *)
     else INR (a,F)) ∧
  matchArg (f::fs) arg mOpt a =
    let flagName = getFlagName arg;
        strEq = (λx y. case compare x y of Equal => T | _ => F);
        pArg = showFlag arg;
        (* Does the current argument match with the current flag options? *)
        matchFlag = (isFlag arg ∧ (* is the current argument a flag? *)
                     (strEq f.name flagName ∨  (* match the long name?  *)
                      strEq (str f.short) flagName)) (* match the short name? *)
    in if matchFlag
       then if f.has_option
            then case arg of
                     OptionFlag _ opt => INR (f.cont (SOME opt) a,F)
                  | _ => if IS_SOME mOpt
                         then INR (f.cont mOpt a,T)
                         else INL (implode "Missing value to: " ^ pArg)
            else case arg of
                     OptionFlag _ _ => INL (implode "Malformed flag: " ^ pArg)
                  | _               => INR (f.cont NONE a,F)
       else matchArg fs arg mOpt a
End

(* Given a configuration (`:flag list`), an initial representing value,
   and a list of parsed arguments `:arg list`, `mkArgsConf confs init args`
   folds `args` over `init` using the apropiate continuation from
   matching flags/options
*)
Definition mkArgsConf_def:
  mkArgsConf fs a [] = INR a ∧
  mkArgsConf fs a (x::xs) =
    let flagOpt = (* Tries to find and option after a flag *)
          case xs of (* Look for the tail of the argument list *)
              []      => NONE (* If empty there is no extra option *)
            | (x::xs) => if isFlag x (* is the next value a flag? *)
                         then NONE   (* There is no option then *)
                         else SOME (destOption x) (* That is your option *)
    in
    case matchArg fs x flagOpt a of
        INL m => INL m
     |  INR (b,T) => mkArgsConf fs b (DROP 1 xs)
     |  INR (b,F) => mkArgsConf fs b xs
Termination
  wf_rel_tac `measure (LENGTH o SND o SND)` >> rw [LENGTH]
End

(* Parse options *)

Definition get_short_def:
  get_short s =
   if 1 < strlen s /\ strsub s 0 = #"-" then
     SOME (ShortFlag (extract s 1 NONE))
   else
     NONE
End

Definition get_long_def:
  get_long s =
    if 2 < strlen s /\ substring s 0 2 = implode "--" then
      let rest = extract s 2 NONE;
          toks = tokens (\x. x = #"=") rest in
       (case toks of
          [x] => SOME (LongFlag x)
        | [x; y] => SOME (OptionFlag x y)
        | _ => NONE)
    else
      NONE
End

Definition is_ident_def:
  is_ident c <=>
    isAlphaNum c \/ c = #"." \/ c = #"-" \/ c = #"/" \/ c = #"_" \/ c = CHR 92
End

Definition get_option_def:
  get_option s =
    if EVERY is_ident (explode s) then
      SOME (Option s)
    else
      NONE
End

Definition parse_arg_def:
  parse_arg s =
    OPTION_CHOICE (get_long s) (OPTION_CHOICE (get_short s) (get_option s))
End

Definition parse_args_aux_def:
  parse_args_aux acc l =
    case l of
      [] => INR (REVERSE acc)
    | h::t =>
        case parse_arg h of
          NONE => INL (implode "Unrecognized option: " ^ h)
        | SOME f => parse_args_aux (f::acc) t
End

Definition parse_args_def:
  parse_args = parse_args_aux []
End

Definition parse_def:
  parse conf l =
    case parse_args l of
      INR fs => conf (expandArgs fs)
    | INL err => INL err
End

val _ = export_theory()

