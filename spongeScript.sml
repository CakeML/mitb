
(**********************************************************************)
(* Formalization of sponge function using an arbitrary permutation    *)
(**********************************************************************)

(**********************************************************************

Roughly:

 Hash msg =  Output(Absorb initial_state (Split (Pad msg)))

  - Pad adds additional bits (specified by Keccak) to
    extend msg so the result can be split into blocks

  - Split splits a message into a list of blocks

  - Absorb applies the sponge algorithm, starting from initial_state

  - Outputs extracts the digest from the state resulting from absorbing

More precisely, the algorithm is parametrised over a permutation f,
used for absorbing, and (r,c,n) where r is the "bitrate" (i.e. block
size), c is the "capacity" (a parameter used by the sponge algorithm)
and n is the digest length. The definition of Hash is thus actually:

 Hash (r,c,n) f initial_state msg =
  Output n (Absorb f c initial_state (Split r (Pad r msg)))

The initial_state consists entirely of zeros.

***********************************************************************)

(* Load stuff below when running interactively *)

(*
app load ["rich_listTheory","intLib","Cooper"];
open HolKernel Parse boolLib bossLib
     listTheory rich_listTheory
     arithmeticTheory Arith numLib computeLib
     Cooper;

intLib.deprecate_int();
*)


(* Hide stuff above and expose stuff below when compiling *)
open HolKernel Parse boolLib bossLib
     listTheory rich_listTheory
     arithmeticTheory Arith numLib computeLib
     wordsLib
     Cooper;
open lcsymtacs;
open wordsTheory;

val _ = intLib.deprecate_int();

(**********************************************************************)
(* Start new theory MITB_SPEC                                         *)
(**********************************************************************)

val _ = new_theory "sponge";

(*
Bit sizes:
 digest   (n): 224
 capacity (c): 448
 bitrate  (r): 1152 (block and key size)
 width    (b): 1600 (SHA-3 state size = r+c)
*)

(*
Started using wordLib for bit-strings, but switched to using lists of
Booleans because symbolic execution was simpler. Might switch back to
wordsLib later.
*)

(*
List of zeros (represented as Fs) of a given size
*)

val _ = type_abbrev("bits", ``:bool list``);

val Zeros_def =
 Define
  `(Zeros 0 = [])
   /\
   (Zeros(SUC n) = F :: Zeros n)`;

val WORD_TO_BITS_def=
  Define
  ` WORD_TO_BITS (w:'l word) =
  let
    bitstring_without_zeros =  MAP (\e.if e=1 then T else F) (word_to_bin_list w)
  in
    ( Zeros (dimindex(:'l) - (LENGTH bitstring_without_zeros) )) ++
    bitstring_without_zeros`;

val BITS_TO_WORD_def=
  Define
  ` BITS_TO_WORD =
      word_from_bin_list o ( MAP (\e.if e then 1 else 0))`;

(*
Sanity checks
*)
val LengthZeros =
 store_thm
  ("LengthZeros",
   ``!n. LENGTH(Zeros n) = n``,
   Induct
    THEN RW_TAC list_ss [Zeros_def]);

val ZerosOneToOne =
 store_thm
  ("ZerosOneToOne",
   ``!m n. (Zeros m = Zeros n) = (m = n)``,
   Induct
    THEN Induct
    THEN RW_TAC list_ss [Zeros_def]);

(*
PadZeros r msg computes the smallest number n such that the length of
(msg ++ [T] ++ Zeros n ++ [T]) is a multiple of r, i.e.:

 LENGTH(msg ++ [T] ++ Zeros n ++ [T]) MOD r = 0

The theorem names LeastPad, proved below, verifies that PadZeros
has this property:

 LeastPad
 |- !r msg.
     2 < r
     ==>
     (LENGTH (msg ++ [T] ++ Zeros (PadZeros r msg) ++ [T]) MOD r = 0)
     /\
     !n. (LENGTH (msg ++ [T] ++ Zeros n ++ [T]) MOD r = 0)
         ==>
         PadZeros r msg <= n

Robert's definition of PadZeros is used below. This is:

 |- PadZeros r msg = (r - ((LENGTH msg + 2) MOD r)) MOD r

The theorem PadZerosLemma, proved below, verifies an alterntive
definition:

 PadZerosLemma
 |- !msg r.
     1 < r
     ==>
     (PadZeros r msg =
       if (LENGTH msg MOD r = r - 1 )
        then r - 1
        else r - LENGTH msg MOD r - 2)

*)
val PadZeros_def =
 Define
  `PadZeros r msg = (r - ((LENGTH msg + 2) MOD r)) MOD r`;

(*
Pad r msg adds Keccak padding to msg. The theorem LengthPadDivides
proved below verifies:

 LengthPadDivides
 |- !r msg. 2 < r ==> (LENGTH(Pad r msg) MOD r = 0)
*)
val Pad_def =
 Define
  `Pad r msg = msg ++ [T] ++ Zeros(PadZeros r msg) ++ [T]`;

(*
Various lemmas needed to prove LeastPad, PadZerosLemma and
LengthPadDivides.

The HOL4 proofs could probably be made much shorter and more elegant
(I just mechanically blundered through them)
*)

val LengthPadLemma1 =
 prove
  (``!r msg n.
      (2 < r) /\ (LENGTH msg = n * r)
      ==>
      (LENGTH(Pad r msg) = (n + 1) * r)``,
   RW_TAC list_ss [Pad_def,PadZeros_def,LengthZeros,MOD_TIMES]);

val MOD_SUB_MOD =
 prove
  (``!m n r. 0 < r /\ 0 < n MOD r ==> ((r - n MOD r) MOD r = r - n MOD r)``,
   RW_TAC arith_ss []);

val MULT_ADD_MOD =
 prove
  (``!n p r. p < r ==> ((n * r + p) MOD r = p)``,
   RW_TAC arith_ss[]
    THEN `0 < r` by DECIDE_TAC
    THEN PROVE_TAC[MOD_TIMES,ADD_SYM,LESS_MOD]);

val LengthPadLemma2 =
 prove
  (``!r msg n p.
      (0 < p) /\ (p + 2 < r) /\ (LENGTH msg = n * r + p)
      ==>
      (LENGTH(Pad r msg) = (n + 1) * r)``,
   RW_TAC list_ss [Pad_def,PadZeros_def,LengthZeros,MOD_TIMES]
    THEN `0 < p + 2` by DECIDE_TAC
    THEN `p + (n * r + 2) = n * r + (p + 2)` by PROVE_TAC[ADD_SYM,ADD_ASSOC]
    THEN `0 < (n * r + (p + 2)) MOD r` by PROVE_TAC[MULT_ADD_MOD]
    THEN `p < r` by DECIDE_TAC
    THEN `0 < r` by DECIDE_TAC
    THEN RW_TAC std_ss [MOD_SUB_MOD,MULT_ADD_MOD]
    THEN DECIDE_TAC);

val LengthPadLemma3 =
 prove
  (``!r msg n.
      (2 < r) /\ (LENGTH msg = n * r + (r - 2))
      ==>
      (LENGTH(Pad r msg) = (n + 1) * r)``,
   RW_TAC list_ss [Pad_def,PadZeros_def,LengthZeros,MOD_TIMES]
    THEN `r + n * r = (n + 1) * r` by DECIDE_TAC
    THEN `0 < r` by DECIDE_TAC
    THEN RW_TAC std_ss [MOD_EQ_0]
    THEN RW_TAC arith_ss []);

val LengthPadLemma4 =
 prove
  (``!r msg n.
      (2 < r) /\ (LENGTH msg = n * r + (r - 1))
      ==>
      (LENGTH(Pad r msg) = (n + 2) * r)``,
   RW_TAC list_ss [Pad_def,PadZeros_def,LengthZeros,MOD_TIMES]
    THEN `r + (n * r + 1) = (n + 1) * r + 1`
          by PROVE_TAC[ADD_SYM,ADD_ASSOC,RIGHT_ADD_DISTRIB,MULT_LEFT_1]
    THEN RW_TAC std_ss []
    THEN `1 < r` by DECIDE_TAC
    THEN RW_TAC std_ss [MULT_ADD_MOD]
    THEN `r - 1 < r` by DECIDE_TAC
    THEN RW_TAC std_ss [LESS_MOD]
    THEN DECIDE_TAC);

val LengthPadLemma5 =
 prove
  (``!r msg n p.
      2 < r /\ p < r /\ (LENGTH msg = n * r + p)
      ==>
      (LENGTH(Pad r msg) = (n + (if p = r - 1 then 2 else 1)) * r)``,
   RW_TAC std_ss []
    THENL
     [PROVE_TAC[LengthPadLemma4],
      Cases_on `0 < p`
       THENL
        [`p + 2 < r \/ (p = r - 2) \/ (p = r - 1)`
          by PROVE_TAC
              [DECIDE
                ``2 < r /\ p < r ==> p + 2 < r \/ (p = r - 2) \/ (p = r - 1)``]
          THENL
           [PROVE_TAC[LengthPadLemma2],
            PROVE_TAC[LengthPadLemma3]],
         `p = 0` by DECIDE_TAC
          THEN RW_TAC arith_ss []
          THEN `LENGTH msg = n * r` by PROVE_TAC[ADD_0]
          THEN IMP_RES_TAC LengthPadLemma1
          THEN DECIDE_TAC]]);

val LengthPadLemma6 =
 prove
  (``!r msg.
      2 < r
      ==>
      ?n p.
       p < r
       /\
       (LENGTH msg = n*r + p)
       /\
       (LENGTH(Pad r msg) = if p = r-1 then (n+2)*r else (n+1)*r)``,
   RW_TAC std_ss []
    THEN `?n p. (LENGTH msg = n * r + p) /\ p < r`
          by PROVE_TAC[DIVISION, DECIDE ``2<r ==> 0<r``]
    THEN Q.EXISTS_TAC `n`
    THEN Q.EXISTS_TAC `p`
    THEN RW_TAC std_ss []
    THEN IMP_RES_TAC LengthPadLemma5
    THEN RW_TAC std_ss []);

(*
Pad r msg produces a strin whose length is a multiple of r
*)
val LengthPad =
 store_thm
  ("LengthPad",
   ``!r msg.
      2 < r
      ==>
      (LENGTH(Pad r msg) =
        (if (LENGTH msg MOD r) = r-1
          then ((LENGTH msg DIV r) + 2)
          else ((LENGTH msg DIV r) + 1)) * r)``,
   RW_TAC std_ss []
    THEN IMP_RES_TAC LengthPadLemma6
    THEN POP_ASSUM(STRIP_ASSUME_TAC o SPEC ``msg : bool list``)
    THEN PROVE_TAC[DIV_UNIQUE,MOD_UNIQUE]);

val LengthPadDivides =
 store_thm
  ("LengthPadDivides",
   ``!r msg. 2 < r ==> (LENGTH(Pad r msg) MOD r = 0)``,
   RW_TAC std_ss []
    THEN `0 < r` by DECIDE_TAC
    THEN RW_TAC std_ss [LengthPad,MOD_EQ_0]);

(*
More lemmas needed for proving that minimal padding added
*)
val ADD_MOD_ZERO1 =
 prove
  (``!m p r.
      0 < r /\ ((m + p) MOD r = 0)
      ==>
      ?n. p = n * r - m MOD r``,
   RW_TAC arith_ss []
    THEN `?d. m + p = d * r` by PROVE_TAC[MOD_EQ_0_DIVISOR]
    THEN `((m DIV r) * r + m MOD r + p = d * r) /\ m MOD r < r`
          by PROVE_TAC[DIVISION]
    THEN Q.EXISTS_TAC `d - (m DIV r)`
    THEN RW_TAC arith_ss [RIGHT_SUB_DISTRIB]);

val ADD_MOD_ZERO1_COR =
 prove
  (``!m p r.
      0 < r /\ 0 < p /\ ((m + p) MOD r = 0)
      ==>
      ?n. 0 < n /\ (p = n * r - m MOD r)``,
   RW_TAC std_ss []
    THEN IMP_RES_TAC ADD_MOD_ZERO1
    THEN POP_ASSUM(K ALL_TAC)
    THEN Cases_on `n=0`
    THEN RW_TAC arith_ss []
    THEN `0 < n` by DECIDE_TAC
    THEN PROVE_TAC[]);

val ADD_MOD_ZERO2 =
 prove
  (``!m p r.
      0 < r /\ (?n. 0 < n /\ (p = n * r - m MOD r))
      ==>
      ((m + p) MOD r = 0)``,
   RW_TAC arith_ss []
    THEN `(m = (m DIV r) * r + m MOD r) /\ m MOD r < r`
          by PROVE_TAC[DIVISION]
    THEN `n = SUC(PRE n)` by DECIDE_TAC
    THEN POP_ASSUM(ASSUME_TAC o SIMP_RULE arith_ss [ADD1])
    THEN POP_ASSUM(fn th => SUBST_TAC[th])
    THEN RW_TAC arith_ss [RIGHT_ADD_DISTRIB]
    THEN `(m + (r + r * PRE n) - m MOD r) = m DIV r * r + r + r * PRE n`
          by DECIDE_TAC
    THEN RW_TAC std_ss []
    THEN `m DIV r * r + r + r * PRE n = m DIV r * r + 1 * r + PRE n * r`
          by PROVE_TAC[MULT_SYM,MULT_LEFT_1]
    THEN ONCE_ASM_REWRITE_TAC[]
    THEN PROVE_TAC[MOD_EQ_0,RIGHT_ADD_DISTRIB]);

val ADD_MOD_ZERO =
 prove
  (``!m p r.
      0 < r /\ 0 < p
      ==>
     (((m + p) MOD r = 0) =
      ?n. 0 < n /\ (p = n * r - m MOD r))``,
   RW_TAC arith_ss []
    THEN EQ_TAC
    THENL
     [PROVE_TAC[ADD_MOD_ZERO1_COR],
      PROVE_TAC[ADD_MOD_ZERO2]]);

val ADD_MOD_ZERO_COR1 =
 prove
  (``!msg n r.
      0 < r
      ==>
     ((LENGTH(msg ++ [T] ++ Zeros n ++ [T]) MOD r = 0) =
      ?m. 0 < m /\ (n + 2 = m * r - LENGTH msg MOD r))``,
   RW_TAC list_ss [LengthZeros]
    THEN PROVE_TAC
          [DECIDE ``0 < n+2 /\ (m + (n + 2) = n + (m + 2))``,
           ADD_MOD_ZERO]);

val ADD_MOD_ZERO_COR2 =
 prove
  (``!msg n r.
      2 < r
      ==>
     ((LENGTH(msg ++ [T] ++ Zeros n ++ [T]) MOD r = 0) =
      ?m. (if LENGTH msg MOD r = r - 1 then 1 else 0) < m
          /\
          (n = m * r - LENGTH msg MOD r - 2))``,
   RW_TAC std_ss []
    THEN `0 < r` by DECIDE_TAC
    THEN RW_TAC std_ss [ADD_MOD_ZERO_COR1]
    THENL
     [EQ_TAC
       THENL
        [RW_TAC std_ss []
          THEN Cases_on `m = 1`
          THEN RW_TAC arith_ss []
          THEN `?m'. m = m' + 2` by COOPER_TAC
          THEN `?r'. r = r' + 3` by COOPER_TAC
          THEN FULL_SIMP_TAC arith_ss [LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB]
          THEN `n = 3 * m' + (r' + (m' * r' + 4)) - 2` by DECIDE_TAC
          THEN RW_TAC arith_ss []
          THEN Q.EXISTS_TAC `2+m'`
          THEN RW_TAC arith_ss [],
         RW_TAC std_ss []
          THEN `?m'. m = m' + 2` by COOPER_TAC
          THEN RW_TAC std_ss [RIGHT_ADD_DISTRIB]
          THEN Q.EXISTS_TAC `m'+2`
          THEN RW_TAC arith_ss []],
      `LENGTH msg MOD r < r` by PROVE_TAC[MOD_LESS]
       THEN `LENGTH msg MOD r < r-1` by DECIDE_TAC
       THEN EQ_TAC
       THEN RW_TAC std_ss []
       THEN`?m'. m = m' + 1` by COOPER_TAC
       THEN FULL_SIMP_TAC arith_ss [LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB]
       THEN Q.EXISTS_TAC `m'+1`
       THEN RW_TAC arith_ss []]);

val MOD_ADD2_EQ =
 prove
  (``!m r. 1 < r /\ (m MOD r = r - 1) ==> ((m + 2) MOD r = 1)``,
   RW_TAC arith_ss []
    THEN `0 < r` by DECIDE_TAC
    THEN `m = m DIV r * r + (r - 1)` by PROVE_TAC[DIVISION]
    THEN POP_ASSUM(fn th => SUBST_TAC[th])
    THEN `m DIV r * r + (r - 1) + 2 = m DIV r * r + (r + 1)`
          by DECIDE_TAC
    THEN RW_TAC std_ss [MOD_TIMES]
    THEN PROVE_TAC[MULT_LEFT_1,MULT_ADD_MOD]);

val MOD_ADD2_NEQ =
 prove
  (``!m r.
      1 < r /\ m MOD r <> r - 1 ==>
      ((r - (m + 2) MOD r) MOD r = r - m MOD r - 2)``,
   RW_TAC arith_ss []
    THEN `0 < r` by DECIDE_TAC
    THEN `m MOD r < r` by PROVE_TAC[MOD_LESS]
    THEN `m MOD r < r - 1` by DECIDE_TAC
    THEN `m = m DIV r * r + m MOD r` by PROVE_TAC[DIVISION]
    THEN POP_ASSUM(fn th => SUBST_TAC[th])
    THEN `m DIV r * r + m MOD r + 2 = m DIV r * r + (m MOD r + 2)` by DECIDE_TAC
    THEN RW_TAC std_ss [MOD_TIMES]
    THEN Cases_on `m MOD r + 2 = r`
    THEN RW_TAC arith_ss []);

val PadZerosLemma1 =
 prove
  (``!r msg.
      1 < r /\ (LENGTH msg MOD r = r - 1)
      ==>
      (PadZeros r msg = r - 1)``,
   RW_TAC arith_ss [PadZeros_def,MOD_ADD2_EQ]);

val PadZerosLemma2 =
 prove
  (``!r msg.
      1 < r /\ ~(LENGTH msg MOD r = r - 1)
      ==>
      (PadZeros r msg = r - LENGTH msg MOD r - 2)``,
   REWRITE_TAC[PadZeros_def,MOD_ADD2_NEQ]);

val PadZerosLemma =
 store_thm
 ("PadZerosLemma",
  ``!r msg.
     1 < r
     ==>
     (PadZeros r msg =
       if (LENGTH msg MOD r = r - 1 )
        then r - 1
        else r - LENGTH msg MOD r - 2)``,
  RW_TAC arith_ss [PadZerosLemma1,PadZerosLemma2]);

val LeastPad1 =
 prove
  (``!r msg.
      2 < r /\ (LENGTH msg MOD r = r - 1 )
      ==> (LENGTH(msg ++ [T] ++ Zeros(r - 1) ++ [T]) MOD r = 0)``,
   RW_TAC std_ss []
    THEN `0 < r` by DECIDE_TAC
    THEN `1 < r` by DECIDE_TAC
    THEN `r - 1 = PadZeros r msg` by PROVE_TAC[PadZerosLemma]
    THEN RW_TAC arith_ss [GSYM Pad_def,LengthPad]
    THEN PROVE_TAC[MOD_EQ_0,MULT_SYM]);

val LeastPad2 =
 prove
  (``!r msg.
      2 < r
      /\
      (LENGTH msg MOD r = r - 1 )
      /\
      (LENGTH(msg ++ [T] ++ Zeros n ++ [T]) MOD r = 0)
      ==>
      r - 1 <= n``,
   RW_TAC std_ss []
    THEN `?m. 1 < m /\ (n = m * r - LENGTH msg MOD r - 2)`
          by PROVE_TAC[ADD_MOD_ZERO_COR2]
    THEN `?m'. m = m' + 2` by COOPER_TAC
    THEN RW_TAC std_ss [RIGHT_ADD_DISTRIB]
    THEN DECIDE_TAC);

val LeastPad3 =
 prove
  (``!r msg.
      2 < r /\ ~(LENGTH msg MOD r = r - 1 )
      ==>
      (LENGTH(msg ++ [T] ++ Zeros(r - LENGTH msg MOD r - 2) ++ [T]) MOD r = 0)``,
   RW_TAC std_ss []
    THEN `0 < r` by DECIDE_TAC
    THEN `1 < r` by DECIDE_TAC
    THEN `r - LENGTH msg MOD r - 2 = PadZeros r msg`
          by PROVE_TAC[PadZerosLemma]
    THEN RW_TAC arith_ss [GSYM Pad_def,LengthPad]
    THEN PROVE_TAC[MOD_EQ_0,MULT_SYM]);

val LeastPad4 =
 prove
  (``!r msg.
      2 < r
      /\
      ~(LENGTH msg MOD r = r - 1 )
      /\
      (LENGTH(msg ++ [T] ++ Zeros n ++ [T]) MOD r = 0)
      ==>
      r - LENGTH msg MOD r - 2 <= n``,
   RW_TAC std_ss []
    THEN `?m. 0 < m /\ (n = m * r - LENGTH msg MOD r - 2)`
          by PROVE_TAC[ADD_MOD_ZERO_COR2]
    THEN `?m'. m = m' + 1` by COOPER_TAC
    THEN FULL_SIMP_TAC std_ss [RIGHT_ADD_DISTRIB]
    THEN DECIDE_TAC);

(*
Proof that PadZeros r msg computes the smallest number n such that the
length of (msg ++ [T] ++ Zeros n ++ [T]) is a multiple of r, i.e.:
*)
val LeastPad =
 store_thm
  ("LeastPad",
   ``!r msg.
      2 < r
      ==>
      (LENGTH(msg ++ [T] ++ Zeros(PadZeros r msg) ++ [T]) MOD r = 0)
      /\
      !n. (LENGTH(msg ++ [T] ++ Zeros n ++ [T]) MOD r = 0)
          ==>
          PadZeros r msg <= n``,
   REPEAT GEN_TAC THEN DISCH_TAC
    THEN `1 < r` by DECIDE_TAC
    THEN Cases_on `LENGTH msg MOD r = r - 1`
    THEN RW_TAC pure_ss [PadZerosLemma]
    THEN RW_TAC std_ss [LeastPad1,LeastPad2,LeastPad3,LeastPad4]
    THEN `r - 1 <= n` by PROVE_TAC[LeastPad2]
    THEN DECIDE_TAC);

(*
Split a message into blocks of a given length r, with the last block
being shorter if the r doesn't divide exactly into the block length.
*)
val Split_def =
 tDefine
  "Split"
  `Split r msg =
    if (r = 0) \/ LENGTH msg <= r
     then [msg]
     else TAKE r msg :: Split r (DROP r msg)`
  (WF_REL_TAC `measure (LENGTH o SND)`
    THEN RW_TAC list_ss [LENGTH_DROP]);


val Split_ind = (fetch "-" "Split_ind");

(*
Sanity check:

 - each block has length shorter than r;

 - if there are more than one blocks in a message,
   then all except the last have length r;

 - the concatenation of the blocks is the original message.

The first two of these are verified by the theorem:

 SplitBlockLengths
 |- !r msg.
     0 < r ==>
     LENGTH (EL (PRE (LENGTH (Split r msg))) (Split r msg)) <= r /\
     !n.
       n < PRE (LENGTH (Split r msg)) ==>
       (LENGTH (EL n (Split r msg)) = r)

and the third property by:

 FlattenSplit
 |- !r msg. 0 < r ==> (FLAT (Split r msg) = msg)

Note that EL ((LENGTH l) - 1) l = LAST l as shown by:

 listTheory.LAST_EL (THEOREM)
 |- !ls. ls <> [] ==> (LAST ls = EL (PRE (LENGTH ls)) ls)
*)

val SplitLengthsLemma1 =
 prove
  (``!r msg n.
      n < PRE(LENGTH(Split r msg))
      ==>
      (LENGTH(EL n (Split r msg)) = r)``,
   recInduct(fetch "-" "Split_ind")
    THEN RW_TAC list_ss []
    THEN RW_TAC list_ss [Once Split_def]
    THENL
     [`n < PRE (LENGTH [msg])` by PROVE_TAC[Split_def]
       THEN FULL_SIMP_TAC list_ss [],
      `n < PRE (LENGTH [msg])` by PROVE_TAC[Split_def]
       THEN FULL_SIMP_TAC list_ss [],
      Cases_on `n`
       THEN RW_TAC list_ss []
       THEN `n' < PRE (LENGTH (Split r (DROP r msg))) ==>
             (LENGTH (EL n' (Split r (DROP r msg))) = r)`
             by PROVE_TAC[]
       THEN `Split r msg = TAKE r msg::Split r (DROP r msg)`
             by PROVE_TAC[Split_def]
       THEN FULL_SIMP_TAC list_ss []]);

val SplitLengthsLemma2 =
 prove
  (``!r msg. 0 < LENGTH(Split r msg)``,
   RW_TAC list_ss [Once Split_def]);

val SplitLengthsLemma3 =
 prove
  (``!r msg.
      0 < r
      ==>
      LENGTH(EL (PRE(LENGTH(Split r msg))) (Split r msg)) <= r``,
   recInduct(fetch "-" "Split_ind")
    THEN RW_TAC list_ss []
    THEN RW_TAC list_ss [Once Split_def]
    THENL
     [`Split r msg = [msg]` by PROVE_TAC[Split_def]
        THEN RW_TAC list_ss [],
      `r <> 0` by DECIDE_TAC
       THEN `LENGTH
             (EL
               (PRE (LENGTH (Split r (DROP r msg))))
               (Split r (DROP r msg))) <= r`
             by PROVE_TAC[]
       THEN `Split r msg = TAKE r msg::Split r (DROP r msg)` by PROVE_TAC[Split_def]
       THEN `0 < (LENGTH (Split r (DROP r msg)))` by PROVE_TAC[SplitLengthsLemma2]
       THEN RW_TAC list_ss [EL_CONS]]);

val SplitBlockLengths =
 store_thm
  ("SplitBlockLengths",
   ``!r msg.
      0 < r
      ==>
      (LENGTH(EL (PRE(LENGTH(Split r msg))) (Split r msg)) <= r)
      /\
      (!n. n < PRE(LENGTH(Split r msg)) ==> (LENGTH(EL n (Split r msg)) = r))``,
   PROVE_TAC[SplitLengthsLemma1,SplitLengthsLemma3]);

val FlattenSplit =
 prove
  (``!r msg. 0 < r ==> (FLAT(Split r msg) = msg)``,
   recInduct(fetch "-" "Split_ind")
    THEN RW_TAC list_ss []
    THEN RW_TAC list_ss [Once Split_def]);

(* Sanity ckecking tests
EVAL ``Split 4 (Pad 4 [m0;m1;m2;m3;m4;m5])``;
EVAL ``Split 4 (Pad 4 [m0;m1;m2;m3;m4;m5;m6])``;
EVAL ``Split 4 (Pad 4 [m0;m1;m2;m3;m4;m5;m6;m7])``;
EVAL ``Split 4 (Pad 4 [m0;m1;m2;m3;m4;m5;m6;m7;m8])``;
EVAL ``Split 4 (Pad 4 [m0;m1;m2;m3;m4;m5;m6;m7;m8;m9;m10])``;
EVAL ``Split 4 (Pad 4 [m0;m1;m2;m3;m4;m5;m6;m7;m8;m9;m10;m11])``;
EVAL ``Split 4 (Pad 4 [m0;m1;m2;m3;m4;m5;m6;m7;m8;m9;m10;m11;m12])``;
EVAL ``Split 4 (Pad 4 [m0;m1;m2;m3;m4;m5;m6;m7;m8;m9;m10;m11;m12;m13])``;
*)

val Split_APPEND =
  store_thm
  ("Split_APPEND",
  ``!l1 l2.
  ( 0< LENGTH l1 )
  ==>
  ( 0< LENGTH l2 )
  ==>
   (Split (LENGTH l1) (l1 ++ l2) = l1::(Split (LENGTH l1) l2))
  ``,
    RW_TAC list_ss [( Once Split_def ),TAKE_LENGTH_APPEND,
                        DROP_LENGTH_APPEND]
    );

(*
Absorb f c : state -> block list -> state
*)
val Absorb_def =
 Define
  `(Absorb f s ([]:'r word list)  = s)
   /\
   (Absorb f (s: ('r+'c) word) (blk::blkl) =
     Absorb f (f(s ?? (0w: 'c word @@ blk ))) blkl)`;

(* Sanity check: relate Absorb to FOLDL *)
val Absorb_FOLDL =
 store_thm
  ("Absorb_FOLDL",
   ``Absorb (f: ('r+'c) word -> ('r+'c) word) = FOLDL (\s blk. f(s ?? ((0w: 'c word) @@ blk
   )))``,
   RW_TAC std_ss [FUN_EQ_THM]
    THEN Q.SPEC_TAC(`x`,`s0`)
    THEN Q.SPEC_TAC(`x'`,`blkl`)
    THEN Induct
    THEN RW_TAC list_ss [Absorb_def]);

(*
Extract digest from a state
*)
val Output_def =
 Define
  `Output: ('b) word -> 'n word s =
     ((dimindex(:'n)-1) >< 0) s`;

val SplittoWords_def =
  Define
  `(SplittoWords: bits -> 'r word list) bitlist  =
    (MAP BITS_TO_WORD) (Split (dimindex(:'r)) bitlist)`;

(*
Hash a message
(('r+'c)word ->('r+'c)word) -> ('r+'c)word -> bits -> 'n word )
*)
val Hash_def =
 Define
  `Hash f initial_state  msg =
    Output (Absorb f initial_state
       (SplittoWords (Pad ( dimindex(:'r) ) msg)
     : 'r word list  )
       )`;

(* Example
val (r,c,n) = (``4``,``2``,``3``);
val s = ``Zeros(r+c)``;

EVAL ``Hash (4,2,3) f ^s []``;
EVAL ``Hash (4,2,3) f ^s [m0]``;
EVAL ``Hash (4,2,3) f ^s [m0;m1]``;
EVAL ``Hash (4,2,3) f ^s [m0;m1;m2]``;
EVAL ``Hash (4,2,3) f ^s [m0;m1;m2;m3]``;
EVAL ``Hash (4,2,3) f ^s [m0;m1;m2;m3;m4]``;
EVAL ``Hash (4,2,3) f ^s [m0;m1;m2;m3;m4;m5]``;
EVAL ``Hash (4,2,3) f ^s [m0;m1;m2;m3;m4;m5;m6]``;
EVAL ``Hash (4,2,3) f ^s [m0;m1;m2;m3;m4;m5;m6;m7]``;
EVAL ``Hash (4,2,3) f ^s [m0;m1;m2;m3;m4;m5;m6;m7;m8;m9]``;
EVAL ``Hash (4,2,3) f ^s [m0;m1;m2;m3;m4;m5;m6;m7;m8;m9;m10]``;
EVAL ``Hash (4,2,3) f ^s [m0;m1;m2;m3;m4;m5;m6;m7;m8;m9;m10;m11]``;
*)

(* Some test data:
val (r,c,n) = (``4``,``2``,``3``);
val s = ``Zeros(^r+^c)``;

EVAL ``Hash (4,2,3) f ^s []``;
EVAL ``Hash (4,2,3) f ^s [m0]``;
EVAL ``Hash (4,2,3) f ^s [m0;m1]``;
EVAL ``Hash (4,2,3) f ^s [m0;m1;m2]``;
EVAL ``Hash (4,2,3) f ^s [m0;m1;m2;m3]``;
EVAL ``Hash (4,2,3) f ^s [m0;m1;m2;m3;m4]``;
EVAL ``Hash (4,2,3) f ^s [m0;m1;m2;m3;m4;m5]``;
EVAL ``Hash (4,2,3) f ^s [m0;m1;m2;m3;m4;m5;m6]``;
EVAL ``Hash (4,2,3) f ^s [m0;m1;m2;m3;m4;m5;m6;m7]``;
EVAL ``Hash (4,2,3) f ^s [m0;m1;m2;m3;m4;m5;m6;m7;m8]``;
EVAL ``Hash (4,2,3) f ^s [m0;m1;m2;m3;m4;m5;m6;m7;m8;m9]``;
EVAL ``Hash (4,2,3) f ^s [m0;m1;m2;m3;m4;m5;m6;m7;m8;m9;m10]``;
EVAL ``Hash (4,2,3) f ^s [m0;m1;m2;m3;m4;m5;m6;m7;m8;m9;m10;m11]``;
*)

val _ = export_theory();
