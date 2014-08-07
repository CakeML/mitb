open HolKernel Parse boolLib bossLib;
open arithmeticTheory wordsTheory listTheory wordsLib lcsymtacs;
val _ = numLib.prefer_num()
(* interactive use:
app load ["arithmeticTheory", "wordsTheory", "listTheory","wordsLib","lcsymtacs"];
*)

val _ = new_theory "keccakpermutation";

(* translate from keccak_hol.sml *)

val _ = export_theory();
