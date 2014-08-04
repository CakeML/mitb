(**********************************************************************)
(* Formalization of a revised version of Robert's MITB state machine  *)
(**********************************************************************)

(*

Description of MITB state:

 |----------|-----------|-----------|
 | control  | permanent | volatile  |
 |----------|-----------|-------++++|

 control: two states: Ready, Absorbing;

 permanent: 1600-bit requester storing the Keccak-f permution of an
            initial 1152-bit key padded with 448 zeros. In the HOL
            notation defined below: f(K++(Zeros 448))

 volatile:  1600-bit register storing MITB state

The initial manufacturer state:

 |---------|-----------|----------|
 | Ready   |f(K||0...0)| 0        |
 |---------|-----------|----------|

 - the control state is initially Ready;

 - the permanent memory contains the Keccak-f permution of an initial
   manufacturer-supplied 1152-bit key padded with 448 zeros. In the
   HOL notation defined below: f(K++(Zeros 448));

 - the volatile memory contains 1600-bit 0 (Zeros 1600);

Commands (inputs from user/attacker):

 - Skip : {Ready -> Ready} + {Absorbing -> Absorbing}
   State unchanged (stutter, no-op).

 - Move : {Ready->Absorbing} + {Absorbing->Ready}.
   In Ready: start to hash a new message.
   In Absorbing: abandon absorbing, set vmem to zeros.

 - Input bits len : {Ready->Ready} + {Absorbing->{Absorbing,AbsorbEnd,Ready}}.
   In Ready installs f(key++(Zeros c)) in permanent memory.
   In Absorbing inputs a block and continues absorbing if the block
   isn't the last one (indicated by len < r - where r is the bitrate,
   1152 for SHA-3). If the block being input is the last one, then
   goes into AbsorbEnd (len=r-1) or Ready (len < r-s).

State-transition diagram

                    |-----------|                |-----------|
                    |           |      Move      |           |
                    |           |<-------------->|           |
                +---|           |                |           |---+
                |   |           |                |           |   |
 Input key len  |   |  Ready    |                | Absorbing |   | Input blk len
                |   |           |  Input blk len |           |   |   (len = r)
                |-->|           |   (len < r-1)  |           |<--|
                    |           |<---------------|           |
                    |           |                |           |
                    |-----+-----|                |-----------|
                         /|\                           |
                          |                            | Input blk len
                          |                            |   (len = r-1)
                          |                           \|/
                          |                      |-----+-----|
                          |                      |           |
                          |                      |           |
                          |                      |           |
                          |                      |           |
                          |----------------------| AbsorbEnd |
                                                 |           |
                                                 |           |
                                                 |           |
                                                 |           |
                                                 |-----+-----|

The changes to Robert's original design are:

 - added Skip command that does nothing

 - old Setup state is now subsumed by Ready;

 - added addition state AbsorbEnd for len = r-1 case;

 - both key and message block are input using Input command;

 - remove the transition (Setup to Ready in old version) that allows
   the digest corresponding to a partially hashed key
   (e.g. without the padding added) to be read;

 - old commands ButtonSetup, ButtonReady roughly correspond to
   new Input, Move, respectively;

 - Move abandons absorbing, discards vmem memory and moved to Ready;

 - explicit outputs now omitted - it is assumed that in the Ready
   state the control state and digest (bottom 224 bits of volatle
   memory) are displayed.

The changes to Mike's modelling of the MITB are:

 - MITB operates on words now. The parameters (r,c,n) are now part of the
   types.
*)

open HolKernel;
open Parse;
open boolLib;
open bossLib;
open listTheory;
open rich_listTheory;
open arithmeticTheory;
open Arith;
open numLib;
open computeLib;
open wordsTheory;
open wordsLib;
open uccomTheory;
open spongeTheory;
open lcsymtacs;

(*
check later if we need this
open numposrepTheory; 
*)

(**********************************************************************)
(* Start new theory MITB                                              *)
(**********************************************************************)

val _ = new_theory "mitb";

val _ = numLib.prefer_num();

(*
Bit sizes:
 digest   (n): 224
 capacity (c): 448
 bitrate  (r): 1152 (block and key size)
 width    (b): 1600 (SHA-3 state size = r+c)
*)

val _ = type_abbrev("bits", ``:bool list``);

(*
Datatype of control states
*)
val _ = Datatype
  `control = Ready | Absorbing | AbsorbEnd`;

(*
Datatype of input commands
*)
val _ =
 Datatype
  `command = Move
           | Skip
           | Input ('r word) num`;

(*
Type abbreviation for MITB states
*)
val _ =
  (* ('c,'r) mitb_state is *)
 type_abbrev
  ("mitb_state",
   ``:control # ('r+'c) word # ('r+'c) word ``);
(*              permanent       volatile      *)

(*
Type abbreviation for MITB inputs
*)
val _ =
 type_abbrev
  ("mitb_inp",
   ``:bool # bool # 'r word # num``);
(*    skip   move   block     size     *)

(*
Type abbreviation for MITB outputs
*)
val _ =
 type_abbrev
  ("mitb_out",
   ``:bool # 'n word``);


(*
Extract components of an MITB state
*)
val cntlOf_def =
 Define
  `cntlOf((cntl,pmem,vmem): ('r, 'c) mitb_state) = cntl`;

val pmemOf_def =
 Define
  `pmemOf((cntl,pmem,vmem): ('r, 'c) mitb_state) = pmem`;

val vmemOf_def =
 Define
  `vmemOf((cntl,pmem,vmem): ('r, 'c) mitb_state) = vmem`;

(*
Type abbreviation for MITB device
Given a permutation on b=r+c words, moves from one state, via a command
to another state
*)
val _ =
 type_abbrev
 (* ('c,'r) mitb is *)
  ("mitb",
   ``: ( ('r+'c) word -> ('r+'c) word) (* permutation *)
       -> (('c,'r) mitb_state) (* prev. state *)
       -> ('r command) (* command *)
       -> (('c,'r) mitb_state) (* next state *)
      ``);

(*
Type abbreviation for MITB step-function
Given a permutation on b=r+c words, a state and an input, gives
following state and the output.
*)
val _ =
 type_abbrev
 (* ('c, 'n,'r) mitbstepfunction is *)
  ("mitbstepfunction",
``: (('r+'c) word -> ('r+'c) word)  (* permutation *)
  -> ('c, 'r) mitb_state # 'r mitb_inp
  -> ('c, 'r) mitb_state # 'n mitb_out
      ``);

(*
Zero word: Alternative name for the zero word.
REMARK: Zeros is a bool list (bitstring) defined in spongeTheory
*)
val ZERO_def =
 Define
  `ZERO = (0w: 'a word) `;

(*
We first establish some lemmas to fascilitate  relating a translation of
a padded bitstring into a word to a the translation of the same word
padded by the MITB.
*)

(*
Every element in a Zeros-bitstring is F
*)
val EL_Zeros = store_thm("EL_Zeros",
  ``∀n m. m < n ⇒ (EL m (Zeros n) = F)``,
  Induct >> simp[Zeros_def] >> Cases >> simp[] )

(*
Make rewrites for Zeros-bitstring easier.
*)
val LENGTH_Zeros = store_thm("LENGTH_Zeros",
  ``∀n. LENGTH (Zeros n) = n``,
  Induct >> simp[Zeros_def])
val _ = export_rewrites["LENGTH_Zeros"]


val zero_splitting_lemma = store_thm("zero_splitting_lemma",
``! n m . (m <= n) ==> ((Zeros n) = (Zeros m) ++ (Zeros (n-m)))``,
  Induct_on `m`
 >-
  simp[Zeros_def]
 >>
 (
  strip_tac >>
  strip_tac >>
  qpat_abbrev_tac `X = (Zeros n)` >>
  qpat_abbrev_tac `Y = (Zeros (n - (SUC m)))` >>
  PURE_REWRITE_TAC [(Once Zeros_def)] >>
  qpat_assum `!n. p` ( assume_tac o (Q.SPEC `(n-1)` )) >>
  rw [Abbr`Y`] >>
  `(n - SUC m) = (n-1) - m` by simp [] >>
  pop_assum (fn thm => rw [thm]) >>
  `m <= n-1` by simp [] >>
  pop_assum (fn thm => fs [thm]) >>
  pop_assum (fn thm => rw [SYM thm]) >>
  rw [Abbr`X`,(GSYM (CONJUNCT2 Zeros_def))] >>
  `n>0` by simp [] >>
  simp [ADD1]
  )
  );

(*
At every position, the bit in a word constructed using
word_from_bin_list concides with the value at the same position in the
original bitstring.
*)
val word_bit_word_from_bin_list = store_thm("word_bit_word_from_bin_list",
  ``∀ls b.
      EVERY ($> 2) ls ∧ b < LENGTH ls ⇒
      (word_bit b ((word_from_bin_list ls):'a word) ⇔ b < dimindex (:'a) ∧ (EL b ls = 1))``,
  rw[word_from_bin_list_def,l2w_def,word_bit_n2w] >>
  rw[GSYM numposrepTheory.num_from_bin_list_def] >>
  rw[numposrepTheory.BIT_num_from_bin_list] >>
  rw[EQ_IMP_THM] >>
  assume_tac DIMINDEX_GT_0 >>
  DECIDE_TAC);

val l2n_APPEND = store_thm("l2n_APPEND",
`` ! a c d.
l2n b (c ++ d)  = (l2n b c) + (l2n b d) * b ** (LENGTH  c) ``,
strip_tac >> Induct
>- (rw [numposrepTheory.l2n_def] >> simp [])
>>
rw [numposrepTheory.l2n_def] >>
`b** SUC(LENGTH c) = b* b ** (LENGTH c)` by cheat >>
rw [] >> simp []
);

val BITS_TO_WORD_APPEND = store_thm("BITS_TO_WORD_APPEND",
``(BITS_TO_WORD (a++b):'r word ) =
((BITS_TO_WORD a:'r word) || ((BITS_TO_WORD b)<< (LENGTH a)))``,
rw [BITS_TO_WORD_def, word_from_bin_list_def,
    l2w_def] >>
rw [l2n_APPEND] >>
rw [WORD_MUL_LSL ] >>
rw [GSYM word_add_n2w] >>
qpat_abbrev_tac `A=l2n 2 (MAP (\e. if e then 1 else 0) a)` >>
qpat_abbrev_tac `B=l2n 2 (MAP (\e. if e then 1 else 0) b)` >>
rw [word_mul_n2w] >>
cheat 
);

(*
The previous statement holds for BITS_TO_WORD, too.
REMARK: word_from_bin_list translates from num list, where BITS_TO_WORD
translates from bool list. We have chosen the latter representation in
spongeTheory, hence the "indirection".
*)
val word_bit_BITS_TO_WORD = store_thm("word_bit_BITS_TO_WORD",
  ``∀ls x. x < LENGTH ls ⇒ (word_bit x ((BITS_TO_WORD ls):'a word) ⇔ x < dimindex (:'a) ∧ EL x ls)``,
  rw[BITS_TO_WORD_def] >>
  qmatch_abbrev_tac`word_bit x (word_from_bin_list l) ⇔ y` >>
  `EVERY ($> 2) l` by (
    simp[Abbr`l`,EVERY_MAP,EVERY_MEM] >> rw[] ) >>
  fs[Abbr`l`] >> simp[word_bit_word_from_bin_list] >>
  simp[EL_MAP,Abbr`y`] >> rw[])


val l2n_Zeros_helper = prove(
``!l. l2n 2 (MAP (λe. if e then 1 else 0) (Zeros (l))) = 0``,
Induct >>
rw [numposrepTheory.l2n_def, Zeros_def]);

(* See whether this can go .. *)
(* val num_to_bool_conversion_helper = prove( *)
(* `` (($> 2) n) ==> (((λe. if e then 1 else 0) o (λe. e = 1)) n = n)``, *)
(* simp [] ); *)

val n2l_st = prove(
``! b n. b> 0 ==> EVERY ($> b) (n2l b n)``,
recInduct(fetch "numposrep" "n2l_ind") >>
rw [] >>
rw [(Once numposrepTheory.n2l_def)]  >>
assume_tac ( Q.SPECL [`n`,`b`] MOD_LESS ) >>
simp []
);

val MAP_num_to_bool_conversion = prove(
`` (EVERY ($> 2) l)
==>
(MAP ((λe. if e then 1 else 0) o (λe. e = (1:num))) l = l)``,
Induct_on `l` >>
simp [] );


val BITS_TO_WORD_WORD_TO_BITS = store_thm("BITS_TO_WORD_WORD_TO_BITS",
  `` ! (k:'r word ).
  dimindex (:'r) > 1 ==>
   (BITS_TO_WORD (WORD_TO_BITS k) = k )``,
rw [GSYM WORD_EQ,
    WORD_TO_BITS_def,
    BITS_TO_WORD_def,
    word_from_bin_list_def,
    l2w_def] >>
rw [l2n_APPEND, l2n_Zeros_helper] >>
rw [GSYM l2w_def,
    Abbr`bitstring_without_zeros`, word_to_bin_list_def,
    MAP_MAP_o] >>
rw [w2l_def] >>
qspecl_then [`2`,`w2n k`] assume_tac n2l_st >>
rw [MAP_num_to_bool_conversion,
    GSYM w2l_def,
    l2w_w2l]
);

(*
The word we use for padding. It is Zero at each position, except for the
last-position (MSB) and the position given as a parameter.
(l >< 0) w || PAD_WORD l
produces a padded word of length l from w and l.
REMARK: For l=dimindex(:'a), PAD_WORD has only the MSB set to 1, which
is useful for the definition in case l is one short to the block length.
In this case, the block needs to be followed by a 1w block.
*)
val PAD_WORD_def =
 Define
  `(PAD_WORD l):'a word = FCP i. (i=dimindex(:'a)-1) \/ (i=l)`;


(* The two following simplifications are used in padding_lemma *)
val word_bit_or  = prove (
`` (x < dimindex(:'a)) ==> ((a:'a word || b) ' x ⇔ a ' x \/ b ' x) ``,
rw [word_or_def] >>
simp [fcpTheory.FCP_BETA] );

val word_bit_T  = prove (
`` (b < dimindex(:'a) ) ==> ((01w:'a word) ' b = (b=0))``,
rw [word_index] );

(*
This Theorem shows how to construct a correct padding (w.r.t. to
PAD_WORD from spongeTheory) for words smaller than the blocklength minus
two.
*)
val padding_lemma = prove (
``
!m.
(LENGTH(m) < dimindex(:'r)-1)
==>
( 2 < dimindex(:'r))
==>
(LENGTH(m) <> 0 )
==>
(
(BITS_TO_WORD (m ++ (T::(Zeros (dimindex(:'r)-2-LENGTH (m)))++[T]))):'r word
=  (((LENGTH m)-1 -- 0 ) (BITS_TO_WORD m) || PAD_WORD (LENGTH m))
)
``,
ntac 4 strip_tac >>
qmatch_abbrev_tac`(BITS_TO_WORD ls) =  word` >>
simp[GSYM WORD_EQ] >>
rw [] >>
`x < (LENGTH ls) ` by ( simp[Abbr`ls`,LengthZeros] ) >>
simp[word_bit_BITS_TO_WORD, word_bit_def,Abbr`word`,word_bit_or,
PAD_WORD_def, fcpTheory.FCP_BETA,word_bits_def ]  >>
Cases_on `x< LENGTH(m)`
>-
  (
  simp [word_bit, word_bit_BITS_TO_WORD, Abbr`ls`,EL_APPEND1]
  )
>>
  `LENGTH(m)-1<=x` by (rw[] >> simp []) >>
  simp[word_bit, word_bit_BITS_TO_WORD, Abbr`ls`,EL_APPEND2] >>
  Cases_on`x = LENGTH(m)`>>
  simp[EL_APPEND2, EL_CONS] >>
  (* one case left *)
  Cases_on `PRE((x-LENGTH(m))) < dimindex(:'r) - (LENGTH(m) +2)`
  >-
    (
    `PRE((x-LENGTH(m))) < LENGTH(Zeros( dimindex(:'r) - (LENGTH m +2)))` by
    simp [LengthZeros] >>
    simp[EL_APPEND1, EL_APPEND2, EL_CONS, EL_Zeros]
    )
  >>
  pop_assum (fn thm => `x >= dimindex(:'r)-1` by simp [thm]) >>
  pop_assum (fn thm => `x = dimindex(:'r)-1` by simp [thm]) >>
  `(LENGTH (Zeros (dimindex ((:ς) :ς itself) − (LENGTH m + (2 :num)))))
  <= PRE((x-LENGTH(m)))` by simp [LengthZeros] >>
  pop_assum (assume_tac
  o (MATCH_MP (INST_TYPE [alpha |-> Type `:bool`] EL_APPEND2 ))) >>
  simp [PRE_SUB1,LengthZeros]
);

(*
This Theorem shows how to construct a correct padding (w.r.t. to
PAD_WORD from spongeTheory) for empty words.
*)
val full_padding_lemma = prove (
``
( 2 < dimindex(:'r))
==>
(
(BITS_TO_WORD (T::((Zeros (dimindex(:'r)-2))++[T]))):'r word
=  PAD_WORD (0)
)
``,
strip_tac >>
qmatch_abbrev_tac`(BITS_TO_WORD ls) =  word` >>
simp[GSYM WORD_EQ] >>
rw [] >>
`x < (LENGTH ls) ` by ( simp[Abbr`ls`,LengthZeros] ) >>
simp[word_bit_BITS_TO_WORD, word_bit_def,Abbr`word`,word_bit_or,
PAD_WORD_def, fcpTheory.FCP_BETA,word_bits_def,LengthZeros] >>
Cases_on `x=0`
>- simp [Abbr`ls`]
>>
`x>0` by simp[] >>
simp [ Abbr`ls`,LengthZeros ,EL_CONS]  >>
Cases_on `x< LENGTH(m)` >>
pop_assum (fn thm => `0<x` by simp [thm]) >>
Cases_on `x< dimindex(:'r)-1` >>
lrw [EL_CONS,PRE_SUB1,EL_APPEND1, EL_APPEND2,EL_Zeros,LengthZeros]  >>
`x+1-dimindex(:'r)=0` by simp [] >>
rw []
);

(* The following two lemmas show how to construct a padding for a word
that is one short to blocksize. If such a word m is padded, it takes two
blocks, the first one being: m++T, the second one being F::F::..::T.
one_short_lemma
  shows that using PAD_WORD as usual works for the first block, i.e.,
  it adds a single T at the end of the bitstring.
int_min_lemma
  shows that INT_MINw conveniently expresses the second block, which is
  independent of the word being padded.
*)

(*
TODO proof this lemma
*)

val one_short_lemma = prove (
``
(LENGTH(m) = dimindex(:'r)-1)
/\
( 2 < dimindex(:'r))
==>
(
(BITS_TO_WORD (m ++ [T]) =
 (((LENGTH m)-1 -- 0 ) (BITS_TO_WORD m) || PAD_WORD (LENGTH m) ))
)
``,
cheat
);


val int_min_lemma = prove (
  ``
  (dimindex(:'n) > 0)
  ==>
  ((BITS_TO_WORD ((Zeros (dimindex(:'n)-1))++[T])):'n word
  = INT_MINw)
  ``,
  strip_tac >>
  simp[GSYM WORD_EQ] >>
  rw[] >>
  qmatch_abbrev_tac`word_bit x (BITS_TO_WORD ls) ⇔ word_bit x INT_MINw` >>
  `x < LENGTH ls` by ( simp[Abbr`ls`] ) >>
  simp[word_bit_BITS_TO_WORD] >>
  simp[word_bit_def,word_L,Abbr`ls`] >>
  rev_full_simp_tac(srw_ss()++ARITH_ss)[] >>
  Cases_on`x = dimindex(:'n)-1`>>
  fs[]>>
  simp[EL_APPEND1,EL_APPEND2] >>
  simp[EL_Zeros]);


(*
Defines one step of MITB  with permutation function f
MITB_FUN  f : 'b mitb_state -> 'r inputs -> 'b mitb_state
*)
val MITB_FUN_def =
 Define
  `(* Skip : {Ready -> Ready} + {Absorbing -> Absorbing} *)
   (
   (MITB_FUN: ('c,'r) mitb)
     f ((cntl,pmem,vmem)) Skip
    = (cntl,pmem,vmem))
   /\
   (* Input : Ready -> Ready *)
   (MITB_FUN f (Ready,pmem,vmem) (Input key len)
    = (Ready, f((ZERO:'c word) @@ key ),ZERO))
   /\
   (* Move: {Ready -> Absorbing} *)
   (MITB_FUN f (Ready,pmem,vmem) Move
    = (Absorbing,pmem,pmem))
   /\
   (* Move: {Absorbing -> Ready} *)
   (MITB_FUN f (Absorbing,pmem,vmem) Move
    = (Ready,pmem,ZERO))
   /\
   (* Input: Absorbing -> {Absorbing,AbsorbEnd,Ready} *)
   (MITB_FUN f (Absorbing,pmem,vmem) (Input blk len)
    =
    let r=dimindex(:'r) in
      if len <= r-2 then (* More than one bit too small *)
         if len = 0 then
          (Ready,pmem,f(vmem ?? ((ZERO:'c word) @@ PAD_WORD (0):'r word)))
         else
          (Ready,pmem,
           f ( vmem ??
           (
           (ZERO:'c word) @@
           ( (len-1 -- 0 ) (blk) || PAD_WORD (len) )
           )))
      else
       if len = r-1 then  (* Exactly one-bit too small *)
       (AbsorbEnd,
        pmem,
        (* see above. Note PAD_WORD 0x10* in this case *)
        f ( vmem ??
        (
        (ZERO:'c word) @@
        ( (len-1 -- 0 ) (blk) || PAD_WORD (len) )
        )))
       else  (* Full block *)
      (Absorbing,pmem,f(vmem ?? ((ZERO: 'c word) @@ blk )))
      )
   /\
   (* Move: AbsorbEnd -> Ready} *)
   (MITB_FUN f (AbsorbEnd,pmem,vmem) Move
    = (Ready, pmem, ZERO))
   /\
   (* Input: AbsorbEnd -> Ready} *)
   (MITB_FUN  f (AbsorbEnd,pmem,vmem) (Input blk len)
    = (Ready, pmem,
    (* see above
     * f(vmem XOR (Zeros(r-1) ++ [T] ++ Zeros c)))) *)
     f(vmem ?? ( (ZERO: 'c word) @@ (INT_MINw:'r word )))
     ))
    `;

(*
Predicate to test for well-formed Keccak parameters
*)
val GoodParameters_def =
 Define
  `GoodParameters (r:num,c:num,n:num)
    ⇔ 2 < r /\ 0 < c /\ n <= r`;

(*
Functional version as in the paper
*)
val MITB_def =
 Define
  `MITB  f ((skip,move,block,size), (cntl,pmem,vmem)) =
    MITB_FUN  f
     (cntl, pmem, vmem)
     (if skip = T
       then Skip else
      if move = T
       then Move
       else
         if (size <=dimindex(:'r)) then
          Input (block: 'r word) size
         else Skip)`;

(*
We define a step function that behaves like MITB, but defines the
output, too.
Parametric in:
 f - compression function used inside MITB
 Input:
  (cnt,pmem,vmem) - current state of the MITB
  (skip,move,block,size) - input to the MITB
 Output:
  (cntl_n,pmem_n,vmem_n) - next state of the MITB
  (ready:bool, digest:bits) - output of the MITB
*)

val MITB_STEP_def =
 Define
  `MITB_STEP f ((cntl,pmem,vmem), (skip,move,block,size)) =
    let (cntl_n,pmem_n,vmem_n) = MITB  f ((skip,move,block,size), (cntl, pmem, vmem))
    in
      ((cntl_n,pmem_n,vmem_n),
      (
      (cntl_n = Ready),
      (if cntl_n = Ready then ((dimindex(:'n)-1 >< 0) vmem_n) else (ZERO:'n word )))
      )
    `;

(*
Datatype of commands to the library/protocol calling the MITB
*)
val _ =
 Datatype
  `mac_query =
            SetKey ('r word)
          | Mac bits
          | Corrupt
          `;

(*
Datatype for
- responses from the library/protocol to the adversary (real
  world)
- responses from the simulator to the environment (ideal world)
or from the S.
WasCorrupted is a notice that the environment decided to corrupt the
library/protocal or functionality
OracleResponse is the response to an Oracle Query
*)
val _ =
 Hol_datatype
  `mac_to_adv_msg =
            WasCorrupted
          | OracleResponse of 'n word
          `;
(*
Datatype for
- queries from the adversary to the library/protocol (real world)
- queries from the simulator to the functionality (ideal world)
*)
val _ =
 Datatype
  `adv_to_mac_msg =
            CorruptACK
          | OracleQuery bits
          `;

(*
State transition function for the functionality defining a perfect MAC
device for a given Hash function
parameters:
 H  -- Hash function
internal state:
 current key K, corruption status
inputs:
 queries of type query
output:
 bitstrings

REMARK: Whoever is on the adversarial interface may request Hashes with
K prepended to the input. This interface will be accessed by SIM, to be
able to  emulate a MITB

FMAC
: (bits -> 'n word) ->  (* Hash function *)
 'r word # bool ->  (* current key, corruption status *)
 ('r mac_query, γ, δ, ε, ζ, adv_to_mac_msg) Message ->
 (* Input from environment or adversary *)
 ('r word # bool) # ('n word, 'n mac_to_adv_msg) ProtoMessage
 (* output to environment or adversary *)
*)

val FMAC_def =
    Define
          `
          ( FMAC (H: bits -> 'n word) (K,F)
              (EnvtoP (SetKey k:'r mac_query)) =
              ((k,F),(Proto_toEnv (0w:'n word)))
          )
          /\
          ( FMAC H (K,F) (EnvtoP (Mac m)) =
            ((K,F),(Proto_toEnv (H (WORD_TO_BITS(K) ++ m)))))
          /\
          ( FMAC H (K,F) (EnvtoP (Corrupt)) = ((K,T),Proto_toA (WasCorrupted)))
          /\
          ( FMAC H (K,T) (AtoP (CorruptACK)) = ((K,T),Proto_toEnv 0w))
          /\
          ( FMAC H (K,T) (AtoP (OracleQuery m)) =
          ((K,T),(Proto_toA (OracleResponse (H((WORD_TO_BITS K)++m))))))
          /\
          (* When corrupted, ignore honest queries *)
          ( FMAC H (K,T) (EnvtoP q) = ((K,T),Proto_toEnv 0w))
          `;

(*
Run MITB mitbf s l

Executes a list of commands l on a initial state s, using the step
function mitbf. This function will make the definition of the protocol,
see below, easier in the future.

The output consists of the state after execution of list l and the final
output (preceeding outputs are discarded).
*)
val RunMITB_def =
 Define
  `RunMITB  mitbf s (i::il) =
  if (il=[]) then
     (mitbf (s,i))
  else
     let (s', out) = (mitbf (s,i)) in
       RunMITB  mitbf s' il
       `;

(*
PROCESS_MESSAGE_LIST: bits list -> 'r mitb_inp list
Given a list of bitstrings, PROCESS_MESSAGE_LIST produces a list of
input queries to the MITB that will leave the MITB in ready state, with
vmem set to the hash of the flattening of the input. This is used in the
protocol definition below.
*)
val PROCESS_MESSAGE_LIST_def= Define
`
  (PROCESS_MESSAGE_LIST  [] =
  ([(F,F,0w,0)]:'r mitb_inp list))
  /\
  (PROCESS_MESSAGE_LIST (hd::tl) =
      if (LENGTH hd) = dimindex(:'r)-1 then
        ([(F,F,(BITS_TO_WORD hd),(LENGTH hd));
        (F,F,0w,0)])
      else
        (if (LENGTH hd) <  dimindex(:'r)-1 then
          [ (F,F,(BITS_TO_WORD hd),(LENGTH hd)) ]
        else
          ((F,F,(BITS_TO_WORD hd),(LENGTH hd))
           :: (PROCESS_MESSAGE_LIST tl))))
  `;

(* PROCESS_MESSAGE_LIST never outputs NIL *)
val PROCESS_MESSAGE_LIST_neq_NIL = prove (
  ``!a . PROCESS_MESSAGE_LIST a <> []:'r mitb_inp list``,
          Cases  >> rw[PROCESS_MESSAGE_LIST_def]  );

(*
PROTO

stepfunction defining the protocol. When used with a "correct" MITB (described by a step function), it implements FMAC.

(In real life, this protocol corresponds to a client library that
computes hashes by splitting the message and feeding it into the MITB.
This is how honest users are supposed to use the MITB )

Parametric in:
 mitbf - step function of MITB,
Internal state:
 s - current MITB state
 T/F - corruption status
Input:
 mac_query
Output:
 bitstring
*)

val PROTO_def =
    Define
          `
          ( PROTO (mitbf : ('c,'r) mitb_state # 'r mitb_inp -> ('c,'r)
          mitb_state # 'n mitb_out) (s,F) (EnvtoP (SetKey k)) =
              let (s1,(rdy1,dig1))=mitbf (s,(T,F,(ZERO: 'r word),0)) in
                if rdy1=F then
                  (let (s2,(rdy2,dig2)) =mitbf(s1,(F,T,(ZERO:'r word),0)) in
                    let (s3,(rdy3,dig3))=
                    mitbf (s2,(F,F,k,(dimindex (:'r)))) in
                      ((s3,F),(Proto_toEnv 0w)))
                else
                    let (s2,rdy2,dig2)=mitbf(s1,(F,F,k,(dimindex (:'r)))) in
                     ((s2,F),(Proto_toEnv 0w))
              )
          /\
          ( PROTO mitbf (s,F) (EnvtoP (Mac m)) =
          (* Bring MITB into Ready state *)
           let (s0,(rdy0,dig0)) = RunMITB mitbf s [(T,F,(ZERO: 'r
           word),0)] in
           (* make sure that MITB is in Ready state *)
             let (sr,rdyr,digr) =
              ( if (rdy0=F) then
                  RunMITB mitbf (s0) [(F,T,ZERO,0)]
                else
                  (s0,rdy0,dig0)
              ) in
                let (ss,rdys,digest) = ( RunMITB
                  mitbf
                  (sr)
                  ((F,T,ZERO,0)
                  :: (PROCESS_MESSAGE_LIST (Split (dimindex(:'r)) m))))
                in
                  (* two consecutive moves to re-initialise vmem *)
                  let (sq,rdyq,digq) = RunMITB mitbf ss [(F,T,ZERO,0);
                  (F,T,ZERO,0)] in
                    ((sq,F),(Proto_toEnv digest))
          )
          /\
          ( PROTO mitbf (s,F) (EnvtoP (Corrupt)) =
                ((s,T),(Proto_toEnv 0w)))
          /\
          (* Give adversary blackbox access when corrupted, but
           *  not complete: she is not allowed to set the key.
           * TODO: would be nicer if we would check the ready state via the LED
           *
           *  *)
          (* Ignore Key-overwrite *)
          ( PROTO mitbf ((Ready,cntl,vmem),T) (AtoP (F,F,inp,len)) =
            (((Ready,cntl,vmem),T), (Proto_toA (F,ZERO)))
          )
          /\
          ( PROTO mitbf (s,T) (AtoP i) =
            let (s_next,rdy,dig) = mitbf (s,i) in
                ((s_next,T), (Proto_toA (rdy,dig))))
          /\
          (* Ignore honest queries when corrupted *)
          ( PROTO mitbf (s,T) (EnvtoP _) = ((s,T),(Proto_toEnv 0w)))
          /\
          (* Ignore adversarial queries when not corrupted *)
          ( PROTO mitbf (s,F) (AtoP _) = ((s,F),(Proto_toA ( F,0w ))) )
          /\
          (* Ignore the rest TODO : get rid of this and replace with individual
          * cases.. *)
          ( PROTO mitbf (s,cor) _ = ((s,cor),(Proto_toEnv 0w)))
                `;

(*
SIM - step-function defining the simulator.
The simulator can make queries to F, but only on the adversarial
interface. It should not alter or read F's state directly.

REMARK: We first define a step function for SIM, which is then used in a
wrapper function that instantiates the adversarial interface of F as an
oracle.
*)

val SIM_def =
  Define `
(SIM (T,Ready,(vm:'n word) ,m) (EnvtoA (T,_,_,_)) = ((T,Ready,vm,m),(Adv_toEnv
(T,vm))))
    /\
(SIM (T,Absorbing,vm,m) (EnvtoA (T,_,_,_)) =
    ((T,Absorbing,vm,m),(Adv_toEnv (F,ZERO))))
    /\
(SIM (T,AbsorbEnd,vm,m) (EnvtoA (T,_,_,_)) =
((T,AbsorbEnd,vm,m),(Adv_toEnv (F,ZERO))))
    /\
(SIM (T,Ready,vm,m) (EnvtoA (F,T,_,_)) = ((T,Absorbing,vm,[]),(Adv_toEnv
(F,ZERO ))))
    /\
(SIM (T,Absorbing,vm,m) (EnvtoA (F,T,_,_)) =
((T,Ready,ZERO ,m),(Adv_toEnv (T,ZERO ))))
    /\
(SIM (T,AbsorbEnd,vm,m) (EnvtoA (F,T,_,_)) =
((T,Ready,ZERO ,m),(Adv_toEnv (T,ZERO ))))
    /\
(SIM (T,Absorbing,(vm: 'n word),m) (EnvtoA (F,F,(inp: 'r word),inp_size)) =
 let r = dimindex(:'r) in
  (* Cases:
   *  inp_size=r) take full block
   *  inp_size=r-1 take partial block, goto AbsorbEnd
   *  inp_size<r-1 query oracle
   *  *)
   if (inp_size=r) then
    ((T,Absorbing,ZERO, (m ++ (WORD_TO_BITS inp))),(Adv_toEnv (F,ZERO)))
   else
    if (inp_size=r-1) then
      ((T,AbsorbEnd,ZERO,
      (m ++ TAKE inp_size (WORD_TO_BITS ((inp_size-1 -- 0)
      inp)))),Adv_toEnv (F,ZERO))
    else
      if inp_size<r-1 then
      (*  Send to Functionality for communication. Proceed when response is *)
      (* received, see (MARK)  *)
      (
        if inp_size = 0 then
          ((T,Absorbing,vm,[]), Adv_toP ( OracleQuery (m)))
        else
          ((T,Absorbing,vm,[]),
            (Adv_toP (
              OracleQuery (m ++
              TAKE inp_size (WORD_TO_BITS ((inp_size-1 -- 0)
              inp))))))
       )
       else (*if inp_size>r behave like Skip*)
        ((T,Absorbing,vm,m),(Adv_toEnv (F,ZERO)))
    (* ) *)
    )
    /\
(SIM (T,AbsorbEnd,vm,m) (EnvtoA (F,F,inp,inp_size)) =
  if (inp_size <= dimindex(:'r)) then
    (
    ((T,AbsorbEnd,vm,[]),(Adv_toP (
    OracleQuery ((m)))))
    )
  else (* behave like Skip *)
      ((T,AbsorbEnd,vm,m),(Adv_toEnv (F,ZERO)))
       )
    /\
(* MARK *)
(SIM (T,_,vm,m) (PtoA (OracleResponse hashvalue)) =
((T,Ready,hashvalue,[]),(Adv_toEnv (T,hashvalue))))
    /\
(* If FMAC was corrupted, change corruption state *)
(SIM (F,cntl,vm,m) (PtoA WasCorrupted) = ((T,cntl,vm,m),(Adv_toP
(CorruptACK))))
    /\
(* Ignore other queries while not corrupted *)
(SIM (F,cntl,vm,m) (EnvtoA _) = ((F,cntl,vm,m),(Adv_toEnv (F,ZERO))))
    /\
(* Ignore other queries, while corrupted, in particular:
 * query to set the key. *)
(SIM (T,cntl,vm,m) (EnvtoA _) = ((T,cntl,vm,m),(Adv_toEnv (F,ZERO))))
      `;

(* Type abbreviations for easier debugging *)
val _ =
 type_abbrev
  ("real_game_state",
   ``: (('c,'r) mitb_state # bool) # num list ``);
(*                           ^ corruption status *)


val _ = type_abbrev ("fmac_state",
   ``: ( 'r word # bool) ``);
(* corruption status ^ *)

val _ = type_abbrev ("proto_state",
   ``: (('c,'r) mitb_state # bool)``);


(* ('n,'r) real_message is *)
val _ = type_abbrev ("real_message",
    ``: ('r mac_query, 'r mitb_inp,  'n word,
     'n mitb_out , 'n mitb_out ,'r mitb_inp ) Message ``);

(* ('n,'r) ideal_message is *)
val _ = type_abbrev ("ideal_message",
    ``: ('r mac_query, 'r mitb_inp,  'n word,
     'n mitb_out , 'n mitb_out , adv_to_mac_msg ) Message ``);

(* ('n,'r) adv_message is *)
val _ = type_abbrev ("adv_message",
    ``: (
     'n mitb_out,
    'r mitb_inp
     ) AdvMessage ``);

val _ = type_abbrev ("env_message",
    ``: ('r mac_query, 'r mitb_inp  ) EnvMessage ``);

val _ = type_abbrev ("real_proto_message",
    ``: ('n word, 'n mitb_out  ) ProtoMessage ``);

val _ = type_abbrev ("ideal_proto_message",
    ``: ('n word, 'n mac_to_adv_msg  ) ProtoMessage ``);

(*
We instantiate the real world with the protocol using the MITB, given
parameters and the compression function
*)
val MITB_GAME_def =
    Define `
     ( (MITB_GAME f):
     (('c, 'r) proto_state # num) # 'r env_message ->
     (('c, 'r) proto_state # num) # ('n word,'n mitb_out) GameOutput)
        =
       EXEC_STEP
       ((PROTO ( (MITB_STEP:('c,'n,'r) mitbstepfunction) f))
       : ('c,'r) proto_state -> ('n,'r) real_message
         -> (('c,'r) proto_state) # 'n real_proto_message)
         DUMMY_ADV
        `;

val ALMOST_IDEAL_GAME_def =
    Define `
      (ALMOST_IDEAL_GAME (h: bits -> 'n word ))
      =
      EXEC_STEP
      (FMAC h)
      SIM
      `;
(*
We define the invariant that is to be preserved after every
invocation of the real world and the ideal world with the same inputs.
*)

(* corruption status in real and ideal world correspond *)
val STATE_INVARIANT_COR_def =
    Define `
    STATE_INVARIANT_COR ((cntl,pmem,vmem),cor_r) ((k,cor_f),(cor_s,cntl_s,vm_s,m_s)) =
    ((cor_r = cor_f) /\ (cor_f = cor_s))
    `;

(*
if real game is corrupted, the cntl-state of the MITB simulated by SIM
and the actual MITB in the real game correspond.
*)
val STATE_INVARIANT_CNTL_def =
    Define `
    STATE_INVARIANT_CNTL ((cntl,pmem,vmem),cor_r)
    ((k,cor_f),(cor_s,cntl_s,vm_s,m_s))=
    ((cor_r ==> (cntl = cntl_s))
     /\
     (~cor_r ==> (cntl = Ready) /\ (cntl_s = Ready ))
     )
    `;

(*
We need a different version of SplittoWord for the invariant, as in the
case where no input has been made yet (m_s), we expect SplittoWords to
  give an empty list rather than a list consisting of a single 0-word.
*)
val SplittoWords2_def =
  Define
  `(SplittoWords2: bits -> 'r word list) bitlist =
   if bitlist = [] then []
   else SplittoWords bitlist`

(*
TODO document
*)
val STATE_INVARIANT_MEM_def =
    Define `
    STATE_INVARIANT_MEM f
    (((cntl:control),(pmem:('r+'c) word),(vmem:('r+'c)
    word)),(cor_r:bool))
    ((k: 'r word,cor_f),(cor_s,cntl_s,(vm_s:'n word ),m_s))⇔
    (cor_r ==>
        (
        (pmem = f(ZERO: 'c word @@ k))
        /\
        ((cntl = Absorbing)(*no padding case *)
         ==>
         (? n. LENGTH m_s=n * dimindex(:'r))
         /\
         (vmem = Absorb f (f(ZERO: 'c word @@ k)) ( SplittoWords2 m_s) ))
        /\
        ((cntl = AbsorbEnd)(* half padding case *)
         ==>
         (? n. (LENGTH m_s=n * dimindex(:'r) - 1) /\ ( n>0))
         /\
         (vmem = Absorb f (f(ZERO:'c word @@ k ))
         (SplittoWords (m_s ++ [T] )) ) )
        /\
        ((cntl=Ready) ==> ((Output vmem)=vm_s))
        )
     )
     /\
        (~cor_r ==>
        (
          (pmem = f(ZERO: 'c word @@ k))
          /\
          (vmem = ZERO)
          /\
          (vm_s = ZERO)
        )
        )
    `;

(* The complete invariant (will grow in the future) *)
val STATE_INVARIANT_def =
  Define `
  STATE_INVARIANT f (state_r) (state_f) ⇔
     (STATE_INVARIANT_COR (state_r) (state_f))
     /\
     (STATE_INVARIANT_CNTL (state_r) (state_f))
     /\
     (STATE_INVARIANT_MEM f (state_r) (state_f))`

val rws_invariants =
 [ STATE_INVARIANT_def, STATE_INVARIANT_COR_def,
STATE_INVARIANT_CNTL_def,STATE_INVARIANT_MEM_def ];

(* Tactics for different case splits *)
fun split_all_pairs_tac (g as (asl,w)) =
  let
    val vs = free_varsl (w::asl)
    val ps = filter (can pairSyntax.dest_prod o snd o dest_var) vs
    val qs = map (C cons nil o QUOTE o fst o dest_var) ps
  in
    map_every PairCases_on qs
  end g

fun split_all_bools_tac (g as (asl,w)) =
  let
    val vs = free_varsl (w::asl)
    val ps = filter (equal bool o snd o dest_var) vs
    val qs = map (C cons nil o QUOTE o fst o dest_var) ps
  in
    map_every Cases_on qs
  end g

fun split_all_control_tac (g as (asl,w)) =
  let
    val vs = free_varsl (w::asl)
    val ps = filter (equal ``:control`` o snd o dest_var) vs
    val qs = map (C cons nil o QUOTE o fst o dest_var) ps
  in
    map_every Cases_on qs
  end g

fun split_applied_pair_tac tm =
  let
    val (f,p) = dest_comb tm
    val (x,b) = pairSyntax.dest_pabs f
    val xs = pairSyntax.strip_pair x
    val g = list_mk_exists(xs,mk_eq(p,x))
    val th = prove(g, SIMP_TAC bool_ss [GSYM pairTheory.EXISTS_PROD])
  in
    strip_assume_tac th
  end

fun PairCases_on_tm tm (g as (asl,w)) =
let
  val vs = free_varsl(w::asl)
  val p = variant vs (mk_var("p",type_of tm))
  val eq = mk_eq(p,tm)
in
  markerLib.ABBREV_TAC eq >>
  PairCases_on([QUOTE(fst(dest_var p))]) >>
  PAT_ASSUM``Abbrev(^eq)``(ASSUME_TAC o SYM o
  PURE_REWRITE_RULE[markerTheory.Abbrev_def])
end g


val rws =
[EXEC_STEP_def,
EXEC_LIST_FULL_def,
LET_THM,ENV_WRAPPER_def,ROUTE_THREE_def,ROUTE_def,
  SIM_def,ADV_WRAPPER_def,DUMMY_ADV_def,PROTO_def,MITB_STEP_def,
  MITB_def,MITB_FUN_def,PROTO_WRAPPER_def,STATE_INVARIANT_def,FMAC_def,
  STATE_INVARIANT_COR_def, STATE_INVARIANT_CNTL_def,
  ALMOST_IDEAL_GAME_def, MITB_GAME_def,
  RunMITB_def,
  GAME_OUT_WRAPPER_def, ZERO_def
                    ];

val mitb_skip_lemma =
  prove (
  ``
    (((cntl',pmem',vmem'),(rdy,dig)) = RunMITB (MITB_STEP:('c,'n,'r) mitbstepfunction f) (cntl,pmem,vmem) [(T,b,inp,len)] )
    ==>
    ( cntl=cntl')
    /\
    ( pmem=pmem')
    /\
    ( vmem=vmem')
    /\
    (( rdy=T) ==> (cntl=Ready) )
    /\
    (( rdy=F) ==> (cntl=Absorbing) \/ (cntl=AbsorbEnd))
    ``,
split_all_pairs_tac >>
split_all_control_tac >>
fs [RunMITB_def, MITB_STEP_def, MITB_FUN_def, MITB_def] >>
fsrw_tac [ARITH_ss] [LET_THM]
);


(* This lemma is useful for simplifying terms occuring in the padding *)
val a_mult_b_mod_a_lemma = prove (
``( 0 < a) ==> ((a + b) MOD a = b MOD a)``,
rw [] >>
first_assum (ASSUME_TAC o SYM o (Q.SPECL [`a`,`b`]) o (MATCH_MP
MOD_PLUS)) >>
first_assum (ASSUME_TAC o CONJUNCT2 o (MATCH_MP DIVMOD_ID)) >>
rw []);

val n_a_mult_b_mod_a_lemma = prove (
``( 0 < a) ==> ((n * a  + b) MOD a = b MOD a)``,
Induct_on `n` >>
rw [MULT] >>
fs [] >>
`(n*a + a + b)=(a + (n*a +b))` by simp [] >>
rw [a_mult_b_mod_a_lemma]
);

(*
Rewrite system for what concerns the MACing procedure inside the
protocol
*)
val rws_macking =
  [
  LET_THM,
  MITB_STEP_def, MITB_def,MITB_FUN_def,RunMITB_def,
  PROCESS_MESSAGE_LIST_def
  ]

(*
Rewrite system for what concerns the definition of Hash. (Ideal world
behaviour)
*)
val rws_hash =
  [
  LET_THM,
  Hash_def, Output_def, Absorb_def, 
  Pad_def, Zeros_def, PadZeros_def, ZERO_def,
  a_mult_b_mod_a_lemma,
  SplittoWords_def,
  SplittoWords2_def
   ];

val rws_hash_sans_split =
  [
  LET_THM,
  Hash_def, Output_def, Absorb_def, 
  Pad_def, Zeros_def, PadZeros_def, ZERO_def,
  a_mult_b_mod_a_lemma
   ];

val non_zero_mult = prove(
``!n a . ( n <> 0)  ==> (n * a >= a)``,
Cases >> simp [] >> rw [MULT_SUC] >> simp []);

val Split_APPEND = prove(
``
! r a b n.
LENGTH a > 0 /\
LENGTH b > 0 /\
(LENGTH a = n * r)
==> (Split r (a++b) = Split r a ++ Split r b)``,
recInduct(Split_ind) >>
rw [] >>
`r<>0` by spose_not_then (fn t=> fs[t]) >>
pop_assum (fn t=> fs[t] >> assume_tac t) >>
`n<>0` by spose_not_then (fn t=> fs[t]) >>
`n*r >= r` by simp [non_zero_mult] >>
`n*r + LENGTH b > r` by simp [] >>
rw [(Once Split_def)]
>- lfs [] (*Contradictory case *)
>>
`r <= LENGTH (msg)` by simp [] >>
rw [TAKE_APPEND1] >>
Cases_on `n<=1`
>- (
  `n=1` by simp [] >>
  `r=LENGTH msg` by simp [] >>
  rw [DROP_LENGTH_APPEND,TAKE_LENGTH_APPEND] >>
  rw [(Once Split_def)]
)
>>
qpat_assum `P ==> !b n. Q` (* Invariant *)
 (fn t => first_assum
 (assume_tac o Q.SPECL [`b`, `(n-1)`] o MATCH_MP t)) >>
`n -1 <> 0` by simp[] >>
 pop_assum (assume_tac o Q.SPEC `r` o MATCH_MP non_zero_mult) >>
 `n * r > r` by simp [] >>
 `n* r -r = (n-1)*r` by simp [] >>
 res_tac >>
 rw [DROP_APPEND1] >>
 qmatch_abbrev_tac `lhs=rhs` >> qunabbrev_tac `rhs` >>
 rw [(Once Split_def)]
);

(*
This lemma shows that the MACing step in the protocol is executed
correctly, i.e., that the virtual memory after execution equals a
properly computed hash,  given that the MITB was in Absorbing state
before.

REMARK: In mac_message_in_ready_lemma, we will be able to establish that
vmem equals pmem after moving into Absorbing. Thus
(Absorb f vmem (SplittoWords (Pad ( dimindex(:'r) ) m)))
will equal Hash f .. for the truncated output, if composed right.
*)

val mac_message_in_absorbing = prove (
``! r m pmem vmem .
  (
  (r = dimindex(:'r))
  /\
  (GoodParameters (dimindex(:'r),dimindex(:'c),dimindex(:'n)))
  )
  ==>
  (
   RunMITB
       (MITB_STEP: ('c,'n,'r)mitbstepfunction  f)
       (Absorbing,pmem,vmem)
       (PROCESS_MESSAGE_LIST
       (Split (dimindex(:'r)) m))
   =
   ((Ready, pmem,
      (Absorb f vmem (SplittoWords (Pad ( dimindex(:'r) ) m)))
    ),
    (T,Hash f vmem m)
    )
    )  ``,
   recInduct(Split_ind) >>
   strip_tac >> strip_tac >>
   Cases_on `(LENGTH msg) <= dimindex(:'r)`
   >-
   (
    simp [GoodParameters_def,(Once Split_def)] >>
    (ntac 3 strip_tac) >>
    `Split (dimindex(:'r)) msg = [msg]`
      by (rw [(Once Split_def)]) >>
    `(dimindex(:'r) = LENGTH msg  )
     \/
     (LENGTH msg = dimindex(:'r)-1 )
     \/
     ((0 < LENGTH msg) /\ (LENGTH msg < dimindex(:'r)-1 ))
     \/
     (0 = LENGTH msg )` by simp []
    >- (* LENGTH msg = dimindex(:'r) *)
    (
      fsrw_tac [ARITH_ss] rws_macking >>
      ` ~(dimindex(:'r) <= dimindex(:'r) -2)` by simp [] >>
      pop_assum (fn thm => fsrw_tac[ARITH_ss] [thm]) >>
      fs rws_macking >>
      (* now cntl_t, pmem_t and vmem_t are determined *)
      fsrw_tac [ARITH_ss] (a_mult_b_mod_a_lemma::rws_hash) >>
      `! rest more . ((msg++[T])++ rest) ++ more
       = msg++ ([T]++ rest ++ more)` by rw [] >>
      pop_assum (fn thm => PURE_REWRITE_TAC [thm]) >>
      qpat_abbrev_tac `zeroblock = ([T] ++ Zeros (LENGTH msg - 2)) ++ [T]` >>
      `0 < LENGTH (msg)` by simp [] >>
      `0 < LENGTH (zeroblock)` by simp [LengthZeros,Abbr`zeroblock`] >>
      RW_TAC arith_ss  [Split_LENGTH_APPEND] >>
      pop_assum (fn thm => ALL_TAC) >>
      pop_assum (fn thm => ALL_TAC) >>
      `LENGTH (zeroblock) = LENGTH msg` by simp [LengthZeros,Abbr`zeroblock`] >>
      `LENGTH (msg ++ zeroblock) > LENGTH (msg)` by simp [] >>
      RW_TAC arith_ss  [ (Once Split_def) ] >>
      rw [DROP_LENGTH_APPEND, TAKE_LENGTH_APPEND] >>
      rw rws_hash >>
      RW_TAC arith_ss  [ (Once Split_def) ] >>
      rw rws_hash >>
      qpat_assum `dimindex(:'r) = LENGTH (msg)`
        (fn thm => assume_tac (SYM thm)) >>
      simp [ Abbr`zeroblock`,full_padding_lemma, ZERO_def ]
    )
    >- (* LENGTH msg = dimindex(:'r)-1 *)
    (
      fsrw_tac [ARITH_ss] rws_macking >>
      ` ~(dimindex(:'r)-1 <= dimindex(:'r) -2)` by simp [] >>
      pop_assum (fn thm => fsrw_tac[ARITH_ss] [thm]) >>
      fs rws_macking >>
      (* now cntl_t, pmem_t and vmem_t are determined *)
      fsrw_tac [ARITH_ss] (a_mult_b_mod_a_lemma::rws_hash) >>
      RW_TAC arith_ss  [GSYM APPEND_ASSOC] >>
      qpat_abbrev_tac `block2 = (Zeros (dimindex(:'r) - 1) ++ [T]) ` >>
      RW_TAC arith_ss  [APPEND_ASSOC] >>
      qpat_abbrev_tac `block1 = (msg ++ [T]) ` >>
      `LENGTH (block1) = dimindex(:'r)` by simp [Abbr`block1`] >>
      `LENGTH (block2) = dimindex(:'r)` by simp [Abbr`block2`] >>
      `0 < LENGTH (block1)  /\ 0 < LENGTH (block2) ` by simp [] >>
      `LENGTH (block2) = dimindex(:'r)` by simp [Abbr`block2`] >>
      qpat_assum ` LENGTH (block1) =  dimindex(:'r)`
        (fn thm => assume_tac (SYM thm)) >>
      `~(LENGTH block1 + LENGTH(block2) <= LENGTH (block1)) ` by simp []
      >>
      RW_TAC arith_ss  [Split_LENGTH_APPEND] >>
      fs [] >>
      qpat_assum ` LENGTH (block2) = X` (fn thm=>assume_tac (SYM thm)) >>
      rw (Once (Split_def)::rws_hash) >>
      rw rws_hash >>
      pop_assum (fn thm => ALL_TAC) >>
      pop_assum (fn thm => ALL_TAC) >>
      qpat_assum `0 < LENGTH (X) ` (fn thm=> ALL_TAC) >>
      qpat_assum `0 < LENGTH (X) ` (fn thm=> ALL_TAC) >>
      rw [Abbr`block1`] >>
      fs [] >>
      pop_assum (fn thm => `LENGTH(msg)=dimindex(:'r) -1` by rw [thm]  ) >>
      `2 < dimindex(:'r)` by simp [] >>
      rw [one_short_lemma, ZERO_def ] >>
      simp [Abbr`block2`,int_min_lemma]
    )
    >- (* LENGTH msg < dimindex(:'r) -1 *)
    (
      fsrw_tac [ARITH_ss] rws_macking >>
      (* now cntl_t, pmem_t and vmem_t are determined *)
      `LENGTH msg MOD dimindex(:'r) <> dimindex(:'r)-1` by simp [] >>
      lrw [Hash_def,Pad_def,PadZerosLemma] >>
      qpat_abbrev_tac `block = msg ++ [T] ++ (Zeros (dimindex(:'r) - (LENGTH msg +
      2))) ++ [T]` >>
      `LENGTH block = dimindex(:'r)` by simp [Abbr`block`,LengthZeros] >>
      rw  (rws_hash@[(Once Split_def)]) >>
      qpat_abbrev_tac `block2=(PAD_WORD (LENGTH msg) ‖ (LENGTH msg − 1 -- 0)
      (BITS_TO_WORD msg)):'r word` >>
      qsuff_tac `block2 = (BITS_TO_WORD block)`
      >- disch_then (fn thm => rw [ZERO_def,thm])
      >> rw [Abbr`block2`,ZERO_def] >>
      (* Can this be done in a quicker way? BEGIN*)
      first_assum (assume_tac o MATCH_MP padding_lemma) >>
      pop_assum (fn t =>
         `2 < dimindex(:'r)` by simp [] >>
         pop_assum (assume_tac o (MATCH_MP t))) >>
      pop_assum (fn t =>
        `LENGTH msg <> 0 ` by simp [] >>
         pop_assum (assume_tac o SYM o (MATCH_MP t))) >>
      (* END *)
      fs [Abbr`block`] >>
      pop_assum (fn t => ALL_TAC) >>
      simp [] >>
      qpat_abbrev_tac `Z=Zeros (dimindex(:'r) - (LENGTH msg +2))`  >>
      qsuff_tac `msg ++ T::Z = msg ++ [T] ++ Z` >>
      TRY (disch_then (fn t => rw [t])) >>
      rw [CONS_APPEND]
    )
    >> (* LENGTH msg = 0 *)
    (
      `LENGTH msg <> dimindex(:'r) -1` by simp [] >>
      fsrw_tac [ARITH_ss] rws_macking >>
      pop_assum (fn t => ALL_TAC) >>
      (* now cntl_t, pmem_t and vmem_t are determined *)
      pop_assum (assume_tac o SYM) >>
      fs [LENGTH_NIL] >>
      `LENGTH (Pad (dimindex(:'r)) []) = dimindex(:'r)` by simp [Pad_def,PadZerosLemma,LengthZeros] >>
      rw  (rws_hash@[(Once Split_def),full_padding_lemma,ZERO_def]) >>
      qpat_abbrev_tac `block = T :: ((Zeros (dimindex(:'r) - 2)) ++
      [T])` >>
      `LENGTH block = dimindex(:'r)` by simp [Abbr`block`,LengthZeros] >>
      rw ([full_padding_lemma, Abbr `block`, (Once Split_def),LengthZeros]@rws_hash)
    )
  ) (* LENGTH msg > dimindex*:'r) *)
  >>
   ntac 4 strip_tac >>
   SIMP_TAC std_ss [(Once Split_def)] >>
   fs [GoodParameters_def] >>
   last_assum (fn t => lfs [t] >> assume_tac t) >>
   simp  (rws_macking) >>
   qpat_abbrev_tac `head=TAKE (dimindex(:'r)) msg` >>
   qpat_abbrev_tac `rest=DROP (dimindex(:'r)) msg` >>
   `LENGTH (rest) > 0` by simp [Abbr`rest`,LENGTH_DROP] >>
   `!a . PROCESS_MESSAGE_LIST a <> []:'r mitb_inp list` by
          (Cases  >> rw[PROCESS_MESSAGE_LIST_def] ) >>
   pop_assum (qspec_then `Split (dimindex(:'r)) rest` (fn t => simp[t]))
   >>
   (* qpat_assum `!pmem vmem. P` (fn t => qspecl_then [`pmem`,) >> *)
   rw [Hash_def] >>
   (* now we only have to argue about vmem *)
   qmatch_abbrev_tac `LHS = RHS` >> simp [Abbr`RHS`] >>
   simp [SplittoWords_def, (Once Split_def)] >>
   qpat_abbrev_tac `pad_rest = (DROP (dimindex(:'r)) (Pad
   (dimindex(:'r)) msg))` >>
   simp [Pad_def] >>
   simp rws_hash >>
   `!x . TAKE (dimindex(:'r)) (msg++x) = TAKE (dimindex(:'r)) msg`
      by simp [TAKE_APPEND1] >>
   pop_assum (fn t => RW_TAC arith_ss  [GSYM APPEND_ASSOC,t])  >>
   simp [Abbr`LHS`,ZERO_def] >>
   qpat_abbrev_tac `a = (SplittoWords (Pad (dimindex (:ς)) rest)): 'r
   word list` >>
   qpat_abbrev_tac `b = (MAP BITS_TO_WORD (Split (dimindex (:ς))
   pad_rest)): 'r word list` >>
   (* qmatch_abbrev_tac `(Absorb f (f (vmem ?? 0w @@ BITS_TO_WORD *)
   (* head)) a ) = (Absorb f (f (vmem ?? 0w @@ BITS_TO_WORD *)
   (* head)) b )` >> *)
   qsuff_tac `a=b` >> simp [Output_def] >>
   rw [Abbr`a`,Abbr`b`,SplittoWords_def]  >>
   qsuff_tac `Pad (dimindex(:'r)) rest = pad_rest` >> simp [] >>
   rw [Abbr`rest`,Abbr`pad_rest`,Pad_def]  >>
   RW_TAC arith_ss  [GSYM APPEND_ASSOC,Pad_def] >>
   qmatch_abbrev_tac `(DROP (dimindex(:'r)) msg ++ X)
    = (DROP (dimindex(:'r)) (msg ++ Y))` >>
   simp [DROP_APPEND1,Abbr`X`,Abbr`Y`] >>
   simp [PadZerosLemma, SUB_MOD]
);


val mac_message_in_ready_lemma = prove (
``! pmem vmem  m inp len .
  (GoodParameters (dimindex(:'r),dimindex(:'c),dimindex(:'n)))
==>
(
  ( RunMITB
        (MITB_STEP: ('c,'n,'r)mitbstepfunction  f)
        (Ready,pmem,vmem)
      ((F,T,inp,len)
        :: (PROCESS_MESSAGE_LIST
            (Split (dimindex(:'r)) m))
      ))
  =
  ((Ready, pmem,
      (Absorb f pmem (SplittoWords (Pad ( dimindex(:'r) ) m)))
    ),
    (T,Hash f pmem m))
)
    ``,
rw [] >>
qpat_abbrev_tac `COMS = (PROCESS_MESSAGE_LIST (Split (dimindex(:'r)) m)):'r
mitb_inp list` >>
`COMS <> []` by rw [Abbr`COMS`, PROCESS_MESSAGE_LIST_neq_NIL ] >>
simp rws >>
rw [Abbr`COMS`]  >>
(* Now in Absorbing state *)
rw [mac_message_in_absorbing]
);

val mac_message_lemma = prove (
``  (GoodParameters (dimindex(:'r),dimindex(:'c),dimindex(:'n)))
==>
(
(* ! m . *)
( PROTO ( (MITB_STEP:('c,'n,'r) mitbstepfunction) f)
   ((cntl,pmem,vmem),F) (EnvtoP (Mac m) :('n,'r)real_message) )
 =
 (((Ready, pmem, ZERO ),F), (Proto_toEnv (Hash f pmem m)))
)
    ``,
rw [PROTO_def ]  >>
split_all_pairs_tac >>
first_assum (assume_tac o (MATCH_MP mitb_skip_lemma) o SYM) >>
Cases_on `rdy0` >>
fs [] >>
simp []  >>
first_assum (assume_tac o (MATCH_MP mac_message_in_ready_lemma)) >>
`sr0=Ready` by fs [] >>
rw [] >>
pop_assum (fn t => fs [t]) >>
rw [] >>
lfs [RunMITB_def, MITB_STEP_def, MITB_def, MITB_FUN_def] >>
rw []);

(*
Given that the complete invariant holds, the corruption part of
the invariant holds in the next step.
*)
val Invariant_cor = prove(
 ``! f
     (* The MITB's state in the real game *)
     (cntl:control) (pmem:('r+'c) word) (vmem:('r+'c) word)  (cor_r:bool)
     (* The dummy adversary's state, does not matter really *)
     nd
     (* The functionality's state (cor_s is shared with Sim)*)
      k cor_f
      (* The simulator's state *)
      cor_s cntl_s vm_s m_s
      (* The environment's query *)
      (input: 'r env_message) .
        (GoodParameters (dimindex(:'r),dimindex(:'c),dimindex(:'n)))
        /\
        (STATE_INVARIANT f ((cntl,pmem,vmem),cor_r)
        ((k,cor_f),(cor_s,cntl_s,vm_s,m_s)))
      ==>
      let ((((cntl_n,pmem_n,vmem_n),cor_r_n),_), out_r: ('n word, 'n
      mitb_out) GameOutput ) =
         (MITB_GAME f) ((((cntl,pmem,vmem),cor_r),nd),input)
      in
        (
       let
        (((k_n,cor_f_n),(cor_s_n,cntl_s_n,vm_s_n,m_s_n)),out_i: ('n word, 'n
      mitb_out) GameOutput
        ) =
           (ALMOST_IDEAL_GAME (Hash f ZERO) )
                      (((k,cor_f),(cor_s,cntl_s,vm_s,m_s)),input)
        in
        (STATE_INVARIANT_COR ((cntl_n,pmem_n,vmem_n), cor_r_n)
        ((k_n,cor_f_n),(cor_s_n,cntl_s_n,vm_s_n,m_s_n)))
        )
        ``,
    rw[] >>
    `(cor_s = cor_r) ∧ (cor_f = cor_r)` by
      fs[STATE_INVARIANT_def, STATE_INVARIANT_COR_def] >>
    `∃a b. (input = Env_toA a) ∨ (input = Env_toP b)` by (
      Cases_on`input` >> rw[]) >> rw[]
    >- (
      split_all_pairs_tac >>
      split_all_control_tac >>
      Cases_on `cor_f` >>
      fs [STATE_INVARIANT_def, STATE_INVARIANT_CNTL_def] >>
      fs rws  >>
      split_all_bools_tac >>
      fsrw_tac [ARITH_ss] rws >> rw[] >>
      BasicProvers.EVERY_CASE_TAC >>
      fs rws >>
      fsrw_tac [ARITH_ss] rws >> rw[] >>
      fsrw_tac[ARITH_ss][] >>
      fs [GoodParameters_def] >>
      `~(dimindex (:'r) <= 1 + (dimindex (:'r)-2))` by (simp []) >>
      fsrw_tac [ARITH_ss] rws >>
      (* some more cases left *)
      BasicProvers.EVERY_CASE_TAC >>
      fsrw_tac [ARITH_ss] rws >> rw[]
      )
    >> (*Input to protocol *)
    (
      Cases_on `cor_f`
      >-
      ( (* cor_f T  (proto ignores messages) *)
        split_all_pairs_tac >>
        split_all_control_tac >>
        Cases_on `b` >>
        fs rws
      )
      >> (*cor_f F *)
      (
      Cases_on `? m. b=(Mac m)`
        >-
        (
          fs rws >>
          first_assum(assume_tac o MATCH_MP mac_message_lemma) >>
          fs rws
        )
        >>
        (
          Cases_on `b` >>
          split_all_pairs_tac >>
          split_all_control_tac >>
          rw [] >>
          fs [STATE_INVARIANT_def, STATE_INVARIANT_CNTL_def,
          STATE_INVARIANT_COR_def] >>
          split_all_bools_tac >>
          fsrw_tac [ARITH_ss] rws >> rw[]
        )
      )
    )
);


(*
Given that the complete invariant holds, the state part
of the invariant holds in the next step.
*)
val Invariant_cntl = prove(
``! f
  (* The MITB's state in the real game *)
  (cntl:control) (pmem:('r+'c) word) (vmem:('r+'c) word)  (cor_r:bool)
  (* The functionality's state (cor_s is shared with Sim)*)
  k cor_f
  (* The dummy adversary's state, does not matter really *)
     nd
  (* The simulator's state *)
  cor_s cntl_s vm_s m_s
  (* The environment's query *)
  (input: 'r env_message) .
    (GoodParameters (dimindex(:'r),dimindex(:'c),dimindex(:'n)))
    /\
    (STATE_INVARIANT f ((cntl,pmem,vmem),cor_r)
    ((k,cor_f),(cor_s,cntl_s,vm_s,m_s)))
  ==>
  let ((((cntl_n,pmem_n,vmem_n),cor_r_n),_), out_r: ('n word, 'n
  mitb_out) GameOutput ) =
      (MITB_GAME f) ((((cntl,pmem,vmem),cor_r),nd),input)
  in
    (
    let
    (((k_n,cor_f_n),(cor_s_n,cntl_s_n,vm_s_n,m_s_n)),out_i: ('n word, 'n
  mitb_out) GameOutput
    ) =
        (ALMOST_IDEAL_GAME (Hash f ZERO) )
                  (((k,cor_f),(cor_s,cntl_s,vm_s,m_s)),input)
    in
    (STATE_INVARIANT_CNTL ((cntl_n,pmem_n,vmem_n), cor_r_n)
    ((k_n,cor_f_n),(cor_s_n,cntl_s_n,vm_s_n,m_s_n)))
    )
``,
    rw[] >>
    `(cor_s = cor_r) ∧ (cor_f = cor_r)` by
      fs[STATE_INVARIANT_def, STATE_INVARIANT_COR_def] >>
    `∃a b. (input = Env_toA a) ∨ (input = Env_toP b)` by (
      Cases_on`input` >> rw[]) >> rw[]
    >- (
      split_all_pairs_tac >>
      split_all_control_tac >>
      Cases_on `cor_f` >>
      fs [STATE_INVARIANT_def, STATE_INVARIANT_CNTL_def] >>
      split_all_bools_tac >>
      fsrw_tac [ARITH_ss] rws >> rw[] >>
      BasicProvers.EVERY_CASE_TAC >>
      fsrw_tac [ARITH_ss] rws >> rw[] >>
      fsrw_tac[ARITH_ss][] >>
      fs [GoodParameters_def] >>
      `~(dimindex (:'r) <= 1 + (dimindex (:'r)-2))` by (simp []) >>
      fsrw_tac [ARITH_ss] rws >>
      (* some more cases left *)
      BasicProvers.EVERY_CASE_TAC >>
      fsrw_tac [ARITH_ss] rws >> rw[]
      )
    >> (*Input to protocol *)
    (
      Cases_on `cor_f`
      >-
      ( (* cor_f T  (proto ignores messages) *)
        split_all_pairs_tac >>
        split_all_control_tac >>
        Cases_on `b` >>
        fs rws >>
        RULE_ASSUM_TAC EVAL_RULE
      )
      >> (*cor_f F *)
      (
      Cases_on `? m. b=(Mac m)`
        >-
        (
          lfs [MITB_GAME_def, EXEC_STEP_def, ROUTE_THREE_def,
          ROUTE_def, ENV_WRAPPER_def] >>
          first_assum(assume_tac o MATCH_MP mac_message_lemma) >>
          fs rws
        )
        >>
        (
          Cases_on `b` >>
          split_all_pairs_tac >>
          split_all_control_tac >>
          rw [] >>
          fs [STATE_INVARIANT_def, STATE_INVARIANT_CNTL_def,
          STATE_INVARIANT_COR_def] >>
          split_all_bools_tac >>
          fsrw_tac [ARITH_ss] rws >> rw[]
        )
      )
    )
);

(* The following lemmas are all used in the proof to
Invariant_mem *)

val TAKE_Zeros = prove(
``! b a . TAKE a (Zeros (b)) = Zeros (MIN a b)``,
Induct >>
rw [MIN_DEF,Zeros_def]
>- decide_tac
>- simp [GSYM Zeros_def,ADD1]
>> fs [ADD1,ADD_COMM]
>> `b=0` by simp []
>> `a=0` by simp []
);

val l2n_MAP_Zeros = prove (
``!b . l2n 2 (MAP (\e. if e then 1 else 0) (Zeros b)) = 0``,
Induct >>
rw [Zeros_def,numposrepTheory.l2n_def]);

val LENGTH_n2n_w2n = prove (
``
!a w .
(dimindex(:'r)>1 )
/\
(a <= dimindex(:'r))
/\
(a > 0)
==>
LENGTH (n2l 2 (w2n ((a − 1 -- 0) w:'r word))) ≤ a ``,
rw [] >>
Q.ISPECL_THEN [`a-1`,`0`,`w`] assume_tac WORD_BITS_LT >>
Cases_on `(w2n ((a-1 -- 0) w)) = 0`
>- (
`((a-1 -- 0) w) = 0w` by fs [w2n_eq_0] >>
simp [] )
>>
`SUC (a-1) - 0 = a` by simp [ADD1] >>
qspecl_then [`2`,`w2n ((a-1 -- 0) w)`,`(2 **
a)-1`] assume_tac logrootTheory.LOG_LE_MONO >>
`0 < w2n ((a-1 -- 0 ) w)` by simp [] >>
fs [] >>
`w2n ((a-1 -- 0) w) <= (2 ** a)-1` by simp [] >>
res_tac >>
`LOG 2 (2**a -1) = a-1` by simp [LOG_2_POW_2_SHORT_1] >>
fs [] >>
pop_assum (fn t => all_tac) >>
`LENGTH (n2l 2 (w2n ((a-1 -- 0) w))) <= (a)`
  by simp [numposrepTheory.LENGTH_n2l,ADD1]
);

val MIN_DEF_ALT = prove (
``∀m n. MIN m n = if m <= n then m else n``,
simp [MIN_DEF]);

val BITS_TO_WORD_TAKE_WORD_TO_BITS = prove (
``
!w a.
(dimindex(:'r)>1 )
/\
(a <= dimindex(:'r))
/\
(a > 0)
==>
((BITS_TO_WORD (TAKE a (WORD_TO_BITS (((a - 1) -- 0) w: 'r word))))
= ((a - 1) -- 0) w)``,
rw [BITS_TO_WORD_def,WORD_TO_BITS_def] >>
qunabbrev_tac `bitstring_without_zeros` >>
simp [word_to_bin_list_def, w2l_def] >>
qspecl_then [`a`,`w`] assume_tac  LENGTH_n2n_w2n >>
rfs [] >>
rw [TAKE_APPEND2] >>
qspecl_then [`2`,`w2n ((a-1 -- 0) w)`] assume_tac n2l_st >>
fs [] >>
rw [MAP_MAP_o, MAP_num_to_bool_conversion] >>
rw [TAKE_Zeros] >>
`(a - LENGTH (n2l 2 (w2n ((a − 1 -- 0) w))))
<=
 (dimindex (:ς) − LENGTH (n2l 2 (w2n ((a − 1 -- 0) w))))`
 by simp [] >>
rw [MIN_DEF_ALT, word_from_bin_list_def, l2w_def,l2n_APPEND ] >>
rw [l2n_Zeros_helper] >>
rw [GSYM w2l_def, GSYM l2w_def, l2w_w2l]
);

val SplittoWords_WORD_TO_BITS = prove(
``
dimindex(:'r)>1 ==>
(SplittoWords (WORD_TO_BITS (w:'r word)) = [w] )``,
rw [] >>
`LENGTH (WORD_TO_BITS w) = dimindex(:'r)` by simp [LENGTH_WORD_TO_BITS] >>
`dimindex(:'r) <>0` by simp [] >>
rw [SplittoWords_def, (Once Split_def), BITS_TO_WORD_WORD_TO_BITS]
);

val SplittoWords2_WORD_TO_BITS = prove(
``
dimindex(:'r)>1 ==>
(SplittoWords2 (WORD_TO_BITS (w:'r word)) = [w] )``,
rw [] >>
`(WORD_TO_BITS w) <> []`
              by (fs [GoodParameters_def] >> simp
                  [WORD_TO_BITS_NEQ_NIL]) >>
rw [SplittoWords2_def, SplittoWords_WORD_TO_BITS]
);


val Split_LENGTH_APPEND = prove(
``LENGTH a > 0 /\
LENGTH b > 0
==> (Split (LENGTH a) (a++b) = a :: Split (LENGTH a) b)``,
simp [(Once Split_def)] >>
rw [DROP_LENGTH_APPEND,TAKE_LENGTH_APPEND]
);

val SplittoWords_APPEND = prove(
``! a b n.
(dimindex(:'r)>0)
/\
(LENGTH a >0 )
/\
(LENGTH a = n * dimindex(:'r))
/\
(LENGTH b > 0 )
==>
(SplittoWords ( a ++ b):'r word list
  = (SplittoWords a) ++ (SplittoWords b) )``,
rw [SplittoWords_def, SplittoWords_def] >>
`n<>0` by spose_not_then (fn t => assume_tac t >> fs [LENGTH_NIL]) >>
`n*dimindex(:'r) >= dimindex(:'r)` by simp [non_zero_mult] >>
`LENGTH a > 0 ` by simp [] >>
Q.ISPECL_THEN [`dimindex(:'r)`,`a`,`b`,`n`] assume_tac Split_APPEND >>
fs []
);

val SplittoWords2_APPEND = prove(
``! a b n.
(dimindex(:'r)>0)
/\
(LENGTH a = n * dimindex(:'r))
/\
(LENGTH b > 0 )
==>
(SplittoWords2 ( a ++ b):'r word list
  = (SplittoWords2 a) ++ (SplittoWords2 b) )``,
rw [SplittoWords2_def, SplittoWords_def] >>
fs [] >>
`n<>0` by spose_not_then (fn t => assume_tac t >> fs [LENGTH_NIL]) >>
`n*dimindex(:'r) >= dimindex(:'r)` by simp [non_zero_mult] >>
`LENGTH a > 0 ` by simp [] >>
Q.ISPECL_THEN [`dimindex(:'r)`,`a`,`b`,`n`] assume_tac Split_APPEND >>
fs []
);

val Absorb_APPEND = prove(
``! s a b . Absorb f s (a++b) = Absorb f (Absorb f s a) b``,
Induct_on `a` >> rw [Absorb_def]);

val Absorb_SplittoWords =prove(
``
! s k m more.
dimindex(:'r) > 1
/\
(? n. LENGTH m = n * dimindex(:'r))
/\
(LENGTH more > 0)
==>
((Absorb (f: ('r+'c) word -> ('r+'c) word )
   s ((SplittoWords: bits -> 'r word list)
     ((WORD_TO_BITS (k:'r word)) ++ m ++ more)))
= (Absorb f (Absorb f (f (s ?? 0w:'c word @@ k)) (SplittoWords2 m))
   (SplittoWords more )
  ))``,
  rw [] >>
  qmatch_abbrev_tac `lhs =rhs` >> qunabbrev_tac`lhs` >>
  `dimindex(:'r) > 0` by simp [] >>
  `LENGTH (WORD_TO_BITS k) > 0` by simp [LENGTH_WORD_TO_BITS] >>
  `LENGTH (m++more)>0` by simp [] >>
  `LENGTH (WORD_TO_BITS k) = 1* dimindex(:'r)` 
    by simp [LENGTH_WORD_TO_BITS] >>
  qspecl_then [`WORD_TO_BITS k`, `m ++ more`,`1`] 
          imp_res_tac SplittoWords_APPEND >>
  rw_tac pure_ss [GSYM APPEND_ASSOC, SplittoWords_WORD_TO_BITS] >>
  rw [Absorb_APPEND]  >>
  Cases_on `m=[]` 
  >- rw [Abbr`rhs`,SplittoWords2_def, Absorb_def]
  >>
     `LENGTH m <>0`
         by spose_not_then (fn t => assume_tac t >> fs [LENGTH_NIL]) >>
     `LENGTH m > 0` by simp [] >>
    qspecl_then [`m`, `more`,`n`] 
            assume_tac SplittoWords_APPEND >>
    rw [Absorb_APPEND] >>
    rw [Absorb_def,Abbr`rhs`, SplittoWords2_def]
);


(* TODO check if this can be deleted *)
val SplittoWords_Pad_reduction = prove(
``
(dimindex(:'r) >1)
==>
( SplittoWords (Pad (dimindex(:'r)) (FLAT (MAP WORD_TO_BITS (m: 'r word::mr))))
 =
  m :: SplittoWords (Pad (dimindex(:'r)) (FLAT (MAP WORD_TO_BITS
  (mr))))
)
  ``,
  rw [] >>
  qmatch_abbrev_tac `LHS = RHS` >> qunabbrev_tac `LHS` >>
  simp [LENGTH_WORD_TO_BITS,Pad_APPEND, SplittoWords_def] >>
  qpat_abbrev_tac `rest = (Pad (dimindex (:ς)) (FLAT (MAP WORD_TO_BITS
  mr)))` >>
  `LENGTH (WORD_TO_BITS m)=dimindex(:'r)` by rw [LENGTH_WORD_TO_BITS] >>
  `LENGTH (rest) > 0` by simp [Abbr`rest`,Pad_def] >>
  `LENGTH (WORD_TO_BITS m)> 0` by simp [] >>
Q.ISPECL_THEN [`rest`,`WORD_TO_BITS m`] assume_tac (GEN_ALL
Split_LENGTH_APPEND) >>
res_tac >>
rfs [] >> simp [Abbr`RHS`,BITS_TO_WORD_WORD_TO_BITS, SplittoWords_def]
);


(*
Given that the complete invariant holds, the state part
of the invariant holds in the next step.
*)
val Invariant_mem = prove(
``! f
  (* The MITB's state in the real game *)
  (cntl:control) (pmem:('r+'c) word) (vmem:('r+'c) word)  (cor_r:bool)
  (* The functionality's state (cor_s is shared with Sim)*)
  k cor_f
   (* The dummy adversary's state, does not matter really *)
   nd
  (* The simulator's state *)
  cor_s cntl_s vm_s m_s
  (* The environment's query *)
  (input: 'r env_message) .
    (GoodParameters (dimindex(:'r),dimindex(:'c),dimindex(:'n)))
    /\
    (STATE_INVARIANT f ((cntl,pmem,vmem),cor_r)
    ((k,cor_f),(cor_s,cntl_s,vm_s,m_s)))
  ==>
  let ((((cntl_n,pmem_n,vmem_n),cor_r_n),_), out_r: ('n word, 'n
  mitb_out) GameOutput ) =
      (MITB_GAME f) ((((cntl,pmem,vmem),cor_r),nd),input)
  in
    (
    let
    (((k_n,cor_f_n),(cor_s_n,cntl_s_n,vm_s_n,m_s_n)),out_i: ('n word, 'n
  mitb_out) GameOutput
    ) =
        (ALMOST_IDEAL_GAME (Hash f ZERO)
                  (((k,cor_f),(cor_s,cntl_s,vm_s,m_s)),input))
    in
    (STATE_INVARIANT_MEM f ((cntl_n,pmem_n,vmem_n), cor_r_n)
    ((k_n,cor_f_n),(cor_s_n,cntl_s_n,vm_s_n,m_s_n)))
    )
``,
    rw[] >>
    RULE_ASSUM_TAC (GSYM) >>
    `(cor_s = cor_r) ∧ (cor_f = cor_r)` by
      fs[STATE_INVARIANT_def, STATE_INVARIANT_COR_def] >>
    `∃a b. (input = Env_toA a) ∨ (input = Env_toP b)` by (
      Cases_on`input` >> rw[]) >> rw[]
    >- ( (* Input to adversary *)
      fs [STATE_INVARIANT_def,
          STATE_INVARIANT_CNTL_def,
          STATE_INVARIANT_COR_def
           ] >>
      split_all_pairs_tac >>
      fs [STATE_INVARIANT_MEM_def] >>
      Cases_on `~cor_f` (* must be corrupted *)
      >- (
       split_all_control_tac >> fs [] >>
       split_all_bools_tac >> fs [] >>
       fs rws
       ) >>
      Cases_on `a0` (* skip bit *)
      >-
       (
       split_all_control_tac >> fs [] >>
       split_all_bools_tac >> fs [] >>
       fs rws  >>
       qexists_tac `n`  >>
       decide_tac
       )
      >>
      Cases_on `a1` (* mov bit *)
      >-(
       split_all_control_tac >>
       fs [] >>
       rule_assum_tac (SIMP_RULE arith_ss rws) >>
       rw rws_hash >>
       rw ([Once Split_def] @ rws_hash) >>
       exists_tac ``0`` >> simp []
       )
      >> (* What remains to be shown: Input works nicely *)
       fs [] >>
       Cases_on `cntl_s`
       >- ( (* Ready *)
           rw (rws @ rws_hash) >> fs (rws @ rws_hash)
           )
       >- ( (* Absorbing *)
           ` (a3 > dimindex(:'r))
            \/
             (a3 = dimindex(:'r))
            \/
             (a3 = dimindex(:'r) -1 )
            \/
             (a3< dimindex(:'r) -1 )` by simp []
           >-  (* (a3 > dimindex(:'r)) *)
           (
           rfs rws  >> lfs rws >> qexists_tac `n` >> decide_tac
           )
           >- (* (a3 = dimindex(:'r)) *)
           (
            rfs rws >> 
            lfs rws >>
            qspecl_then [`dimindex(:'r)`,`2`] assume_tac SUB_LESS >>
            `2 <= dimindex(:'r)` 
                by fs [GoodParameters_def,LESS_IMP_LESS_OR_EQ] >>
            res_tac >>
            lfs rws >>
            rw [] >>
              `dimindex(:'r)>1`
                by (fs [GoodParameters_def] >> decide_tac)
            >- (
              qexists_tac `n+1`  >>
              simp [LENGTH_WORD_TO_BITS, LENGTH_TAKE] 
                )
            >>
                qspecl_then [`m_s`,`WORD_TO_BITS a2`, `n`] 
                  assume_tac  SplittoWords2_APPEND >>
                `dimindex(:'r)>0` by simp [] >>
                `LENGTH (WORD_TO_BITS a2) >0` 
                  by (fs [GoodParameters_def] >>
                  simp[LENGTH_WORD_TO_BITS])  >>
                res_tac >> 
                `dimindex(:'r)>1` by (fs [GoodParameters_def]>> simp []) >>
                simp [Absorb_APPEND,SplittoWords2_WORD_TO_BITS,Absorb_def] 
           )
           >- (*  a3 = dimindex(:'r)-1  *)
           (
            rfs rws >>
            lfs ([GoodParameters_def]@rws) >>
            `dimindex(:'r) - 1 <> dimindex(:'r)` by simp [] >>
            `dimindex(:'r) > 1 + (dimindex(:'r) -2)   ` by simp [] >>
            lfs rws  >>
            rw []
            >-
              (qexists_tac `n+1`  >>
              simp [LENGTH_WORD_TO_BITS, LENGTH_TAKE] )
            >>
              rw_tac arith_ss  [GSYM APPEND_ASSOC] >>
              qpat_abbrev_tac `BSA = (TAKE Z
                (WORD_TO_BITS X) ++ [T])` >>
              `LENGTH (BSA) = dimindex(:'r)`
                 by simp[Abbr`BSA`,LENGTH_TAKE,LENGTH_WORD_TO_BITS] >>
              `dimindex(:'r)>0` by simp [] >>
              Cases_on `m_s= []`
              >-
              (
                rw [ SplittoWords2_def, Absorb_def] >>
                simp [SplittoWords_def] >>
                simp [(Once Split_def),Absorb_def] >>
                simp [Abbr`BSA`] >>
                (rpt AP_TERM_TAC) >>
                (* prepare so we can use one_short_lemma *)
                (* `a2 = BITS_TO_WORD (WORD_TO_BITS a2)` by simp *)
                (*   [BITS_TO_WORD_WORD_TO_BITS] >> *)
                (* Q.ABBREV_TAC `a2bits = WORD_TO_BITS a2` >> *)
                (* qpat_assum `a2 = X` (fn t => PURE_REWRITE_TAC [t]) *)
                qpat_abbrev_tac `BLA = (TAKE (dimindex(:'r)-1)
                (WORD_TO_BITS ((dimindex(:'r) -2 -- 0 ) a2))
                )` >>
                `LENGTH BLA = dimindex(:'r)-1`
                 by simp[Abbr`BLA`, LENGTH_TAKE,LENGTH_WORD_TO_BITS] >>
                 rw [one_short_lemma] >>
                 qunabbrev_tac `BLA` >>
                `dimindex(:'r) > 1` by simp [] >>
                `dimindex(:'r)-1 <= dimindex(:'r)` by simp [] >>
                `dimindex(:'r)-1 > 0` by simp [] >>
                qspecl_then [`a2`,`dimindex(:'r)-1`] assume_tac
                  BITS_TO_WORD_TAKE_WORD_TO_BITS >>
                `dimindex(:'r)-1 -1 = dimindex(:'r)-2` by simp [] >>
                fs [WORD_BITS_COMP_THM]
              )
              >>
                `LENGTH (BSA ++ [T]) > 0` by simp [] >>
                `LENGTH BSA > 0` by simp [] >>
                `LENGTH m_s <> 0` by simp [LENGTH_NIL] >>
                `LENGTH m_s > 0` by simp [] >>
                qspecl_then [`m_s`,`BSA`, `n`]
                  assume_tac  SplittoWords_APPEND >>
                lfs [] >>
                simp [Absorb_APPEND] >>
                rw [SplittoWords2_def] >>
                qpat_abbrev_tac `PR=(SplittoWords m_s):'r word list` >>
                simp [SplittoWords_def,(Once Split_def), Absorb_def] >>
                qunabbrev_tac `BSA` >>
                qpat_abbrev_tac `BLA = (TAKE (dimindex(:'r)-1)
                (WORD_TO_BITS ((dimindex(:'r) -2 -- 0 ) a2))
                )` >>
                `LENGTH BLA = dimindex(:'r)-1`
                 by simp[Abbr`BLA`, LENGTH_TAKE,LENGTH_WORD_TO_BITS] >>
                rw [one_short_lemma] >>
                qunabbrev_tac `BLA` >>
                `dimindex(:'r) > 1` by simp [] >>
                `dimindex(:'r)-1 <= dimindex(:'r)` by simp [] >>
                `dimindex(:'r)-1 > 0` by simp [] >>
                qspecl_then [`a2`,`dimindex(:'r)-1`] assume_tac
                  BITS_TO_WORD_TAKE_WORD_TO_BITS >>
                `dimindex(:'r)-1 -1 = dimindex(:'r)-2` by simp [] >>
                fs [WORD_BITS_COMP_THM]
            )
           >>  (*  a3 < dimindex(:'r)-1  *)
            rfs rws >>
            lfs ([GoodParameters_def]@rws) >>
            Cases_on `a3=0` >>
            (* both cases *)
            fs rws  >>
            rw rws_hash_sans_split
            >- (
            `dimindex(:'r)>1` by simp [] >>
            simp [LENGTH_WORD_TO_BITS] >>
            rw[ADD_ASSOC ] >>
            qspecl_then [`n`,`dimindex(:'r)`] 
                (fn t=>rw[t]) MULT_COMM >>
            rw [GSYM MULT_SUC] >>
            `0 < dimindex(:'r)` by simp [] >>
            rw [MULT_COMM, n_a_mult_b_mod_a_lemma] >>
            rw_tac pure_ss [GSYM APPEND_ASSOC ] >>
            qpat_abbrev_tac 
              `PAD=[T] ++ (Zeros (dimindex(:'r) -2) ++ [T])` >>
            rw_tac pure_ss [APPEND_ASSOC ] >>
            `LENGTH (PAD)=dimindex(:'r)` 
              by simp [Abbr`PAD`,LENGTH_Zeros] >>
            `LENGTH (PAD)>0` by simp [] >> 
            qspecl_then [`0w`,`k`,`m_s`,`PAD`] imp_res_tac 
              Absorb_SplittoWords >>
            rw [Abbr`PAD`,SplittoWords_def,(Once Split_def)]  >>
            rw [full_padding_lemma,Absorb_def]
            )
            >> (* a3 <> 0 *)
            `dimindex(:'r)>1` by simp [] >>
            qpat_abbrev_tac `a=(a3 -1 -- 0) a2` >>
            `LENGTH (WORD_TO_BITS a)=dimindex(:'r)`
              by rw[LENGTH_WORD_TO_BITS] >>
            `a3 <= LENGTH (WORD_TO_BITS a)` by simp [] >>
            rw [LENGTH_TAKE, LENGTH_WORD_TO_BITS] >>
            qspecl_then [`n`,`dimindex(:'r)`] 
                (fn t=>rw[t]) MULT_COMM >>
            rw [GSYM MULT_SUC] >>
            `0 < dimindex(:'r)` by simp [] >>
            rw[GSYM ADD_ASSOC ] >>
            qpat_abbrev_tac `foo=a3+2`>>
            rw [MULT_COMM, n_a_mult_b_mod_a_lemma] >>
            `foo <= dimindex(:'r)` by simp[Abbr`foo`] >>
            `foo MOD  dimindex(:'r) < dimindex(:'r)` 
              by rw[MOD_LESS] >>
            Cases_on `a3=dimindex(:'r)-2`
            >- (
              `foo = dimindex(:'r)` by simp[Abbr`foo`] >>
              simp [] >>
              rw_tac pure_ss [GSYM APPEND_ASSOC ] >>
              qpat_abbrev_tac
                `PAD=([T] ++ (Zeros 0 ++ [T]))` >>
              qpat_abbrev_tac
                `msg=(TAKE (dimindex(:'r)-2) (WORD_TO_BITS a))` >>
              `LENGTH (msg++PAD)=dimindex(:'r)` 
                by simp [Abbr`PAD`,Abbr`msg`,LENGTH_Zeros] >>
              `LENGTH (msg++PAD)>0` by simp [] >>
              qspecl_then [`0w`,`k`,`m_s`,
                  `msg++PAD`] imp_res_tac 
                Absorb_SplittoWords >>
              fs [APPEND_ASSOC] >>
              rw [SplittoWords_def,Once (Split_def)] >>
              rw [Absorb_def,Abbr`msg`,Abbr`PAD`] >>
              (* now we prepare for using padding_lemma *)
              qpat_abbrev_tac `BLA = (TAKE (dimindex(:'r)-2) 
                (WORD_TO_BITS (a)))` >>
              `LENGTH BLA = dimindex(:'r)-2` 
                by simp[Abbr`BLA`, LENGTH_TAKE,LENGTH_WORD_TO_BITS] >>
              `LENGTH BLA < dimindex(:'r)-1` by simp[] >>
              `LENGTH BLA <> 0` by simp[] >>
              qspec_then `BLA` assume_tac padding_lemma >>
              res_tac >>
              `dimindex(:'r) -2 - (LENGTH BLA) = 0` by simp [] >>
              rfs [] >>
              ` BLA ++ (T::(Zeros 0 ++ [T])) = BLA ++ T::Zeros 0 ++ [T] `
                by simp []>>
              rw [] >>
              qunabbrev_tac `BLA` >>
              qunabbrev_tac `a` >>
              `dimindex(:'r) > 1` by simp [] >>
              `dimindex(:'r)-2 <= dimindex(:'r)` by simp [] >>
              `dimindex(:'r)-2 > 0` by simp [] >>
              qspecl_then [`a2`,`dimindex(:'r)-2`] assume_tac
              BITS_TO_WORD_TAKE_WORD_TO_BITS >>
              rw [] >>
              rw [WORD_BITS_COMP_THM] 
            )
            >>
            `foo < dimindex(:'r)` by simp[Abbr`foo`] >>
            rw [LESS_MOD] >>
            `dimindex(:'r) - foo < dimindex(:'r)`
              by simp [Abbr`foo`] >>
            rw [LESS_MOD] >>
            rw_tac pure_ss [GSYM APPEND_ASSOC ] >>
            qpat_abbrev_tac
              `PAD=([T] ++ (Zeros (dimindex(:'r) -foo) ++ [T]))` >>
            qpat_abbrev_tac
              `msg=(TAKE (a3) (WORD_TO_BITS a))` >>
            `LENGTH (msg++PAD)=dimindex(:'r)` 
              by simp [Abbr`PAD`,Abbr`msg`,Abbr`foo`,LENGTH_Zeros] >>
            `LENGTH (msg++PAD)>0` by simp [] >>
            qspecl_then [`0w`,`k`,`m_s`,
                `msg++PAD`] imp_res_tac 
              Absorb_SplittoWords >>
            fs [APPEND_ASSOC] >>
            rw [SplittoWords_def,Once (Split_def)] >>
            rw [Absorb_def,Abbr`msg`,Abbr`PAD`,Abbr`foo`] >>
            (* now we prepare for using padding_lemma *)
            qpat_abbrev_tac `BLA = (TAKE a3
            (WORD_TO_BITS (a)))` >>
            `LENGTH BLA = a3`
              by simp[Abbr`BLA`, LENGTH_TAKE,LENGTH_WORD_TO_BITS] >>
            `LENGTH BLA < dimindex(:'r)-1` by simp[] >>
            `LENGTH BLA <> 0` by simp[] >>
            qspec_then `BLA` assume_tac padding_lemma >>
            res_tac >>
            `dimindex(:'r) - (a3 +2) = dimindex(:'r) -2 - (LENGTH BLA) ` by simp [] >>
            `! n .  BLA ++ T::((Zeros n) ++ [T]) = BLA ++ (T::Zeros n ++
            [T]) `
              by simp [] >>
            rw [] >>
            fs [] >>
            qsuff_tac `a = (LENGTH BLA -1 -- 0 ) (BITS_TO_WORD BLA)` 
            >- rw []
            >>
            simp [] >>
            qpat_abbrev_tac `L = LENGTH BLA` >>
            qunabbrev_tac `BLA` >> qunabbrev_tac `a` >>
            (*cleanup *)
            qpat_assum `L+2 < X` (fn t => all_tac) >>
            qpat_assum `L+2 <= X` (fn t => all_tac) >>
            qpat_assum `L+ SUC(X) = Y` (fn t => all_tac) >>
            qpat_assum `L+ SUC(X) > Y` (fn t => all_tac) >>
            qpat_assum `! k f. X` (fn t => all_tac) >>
            fs [] >>
            `L <= dimindex(:'r)` by  simp[] >>
            `L > 0` by simp [] >>
            rw [BITS_TO_WORD_TAKE_WORD_TO_BITS] >>
            rw [WORD_BITS_COMP_THM]
            )
       >> ( (* AbsorbEnd *)
           lfs rws  >> 
           rfs rws  >> 
           Cases_on `~(a3 <= dimindex(:'r))` 
           >- (
              fs rws >> qexists_tac `n` >> decide_tac
              )
           >>
           fs rws >>
           rw rws_hash_sans_split >>
           `dimindex(:'r) >1`
             by ( fs [GoodParameters_def] >> simp [] ) >>
           rw [LENGTH_WORD_TO_BITS] >>
           `0 <  n *dimindex(:'r)` 
             by simp [arithmeticTheory.LESS_MULT2] >>
           fsrw_tac [ARITH_ss] rws >>
           `dimindex(:'r) + (n * dimindex(:'r) +1)
           = ((n+1)*dimindex(:'r))+1`
              by fsrw_tac [ARITH_ss] rws  >>
           pop_assum (fn t => rw [t]) >>
           fsrw_tac [numSimps.ARITH_AC_ss] [] >>
           rw [ADD_ASSOC] >>
           PURE_ONCE_REWRITE_TAC [ADD_COMM] >>
           PURE_ONCE_REWRITE_TAC [MULT_COMM] >>
           `0 < dimindex(:'r) ` by simp [] >>
           rw [n_a_mult_b_mod_a_lemma] >>
           (* Term in Zeros not completely reduced, but keeping this for
           later *)
           (* Prepare to use Absorb_SplittoWords *)
           qpat_abbrev_tac `ZEROS = Zeros (X)` >>
           PURE_REWRITE_TAC [GSYM APPEND_ASSOC] >>
           qpat_abbrev_tac `LASTBLOCK = ZEROS ++ [T]` >>
           `m_s ++ ([T] ++ LASTBLOCK ) = (m_s ++ [T]) ++ LASTBLOCK`
            by rw [] >>
           pop_assum (fn t => PURE_REWRITE_TAC [t]) >>
           qpat_abbrev_tac `SNDLASTBLOCK = m_s ++ [T]` >>
           `LENGTH SNDLASTBLOCK = n * dimindex(:'r)`
             by  simp [Abbr`SNDLASTBLOCK`]>>
           `LENGTH LASTBLOCK > 0`
            by simp [Abbr`LASTBLOCK`]  >>
            qspecl_then [`0w`,`k`,`SNDLASTBLOCK`,
                `LASTBLOCK`] imp_res_tac 
              Absorb_SplittoWords >>
            pop_assum (fn t => rw[t]) >>
            `SNDLASTBLOCK <> []` 
              by simp [Abbr`SNDLASTBLOCK`] >>
            rw [SplittoWords2_def] >>
            qpat_abbrev_tac `PREV=Absorb f X (SplittoWords
            SNDLASTBLOCK)` >>
            (* Now we need to resolve the thing with the Zeros *)
            qunabbrev_tac `LASTBLOCK` >>
            qunabbrev_tac `ZEROS` >>
            simp [] >>
            `LENGTH ( Zeros (dimindex(:'r) -1 )++[T]) = dimindex(:'r)`
              by simp [] >>
            rw ([ (Once Split_def)]@rws_hash) >>
            simp [int_min_lemma]
           )
       )
    >> (* Case: input to protocol *)
      fs [STATE_INVARIANT_def,
          STATE_INVARIANT_CNTL_def,
          STATE_INVARIANT_COR_def
           ] >>
      split_all_pairs_tac >>
      fs [STATE_INVARIANT_MEM_def] >>
      Cases_on `cor_f` (* must be uncorrupted *)
      >- (
       split_all_control_tac >> fs [] >>
       split_all_bools_tac >> fs [] >>
       Cases_on `b` >>
       fs rws >>
       qexists_tac `n` >>
       decide_tac
       )
      >>
       Cases_on `b` 
       >- ( (* SetKey *)
         split_all_control_tac >>  fs [] >>
         split_all_bools_tac >> fs [] >>
         fs rws
         )
       >- ( (* Mac *)
          lfs [MITB_GAME_def, EXEC_STEP_def, ROUTE_THREE_def,
          ROUTE_def, ENV_WRAPPER_def] >>
          first_assum(assume_tac o MATCH_MP ( Q.GEN `m` mac_message_lemma)) >>
          fs rws
          )
       >> ( (* Corrupt *)
         split_all_control_tac >>  fs [] >>
         split_all_bools_tac >> fs [] >>
         fs rws >>
         rw [Output_def] 
         )
);

val  Initial_State_MITB_def =
  Define `
    (Initial_State_MITB f ((cntl,pmem,vmem),cor_r) ) ⇔
    (cntl = Ready) /\
    (pmem = (f(((ZERO:'c word) @@ (ZERO:'r word)): ('r+'c)
    word)):('r+'c) word ) /\
    (vmem = ZERO) /\
    (cor_r = F)
    `;

val  Initial_State_ALMOST_IDEAL_def =
  Define `
    (Initial_State_ALMOST_IDEAL  ((k,cor_f),(cor_s,cntl_s,vm_s,m_s)) ⇔
    (k = ZERO) /\
    (cor_f = F) /\
    (cor_s = F) /\
    (cntl_s = Ready) /\
    (vm_s = ZERO) /\
    (m_s = [])
    )
    `;

val initial_state_fulfulls_invariant = prove(``
! f (cntl:control) (pmem:('r+'c) word) (vmem:('r+'c) word)  (cor_r:bool)
  k cor_f cor_s cntl_s vm_s m_s
  .
    (Initial_State_MITB f  ((cntl,pmem,vmem),cor_r) )
    /\
    (Initial_State_ALMOST_IDEAL  ((k,cor_f),(cor_s,cntl_s,vm_s,m_s)))
    ==>
    (STATE_INVARIANT f ((cntl,pmem,vmem),cor_r)
    ((k,cor_f),(cor_s,cntl_s,vm_s,m_s)))
    ``,
simp [Initial_State_MITB_def, Initial_State_ALMOST_IDEAL_def, STATE_INVARIANT_def, STATE_INVARIANT_COR_def,
STATE_INVARIANT_CNTL_def,STATE_INVARIANT_MEM_def]);

(* Hash_WORD_TO_BITS_KEY fascilitates the proof of same_output.
 I couldn't figure out how to introduce an existential in an assumption,
 so I used this lemma instead.
 *)
val simple_lemma = prove( ``? n . (n=0) \/ (dimindex(:'r) =0)``,
 qexists_tac `0` >> simp [] ) ;

val Hash_WORD_TO_BITS_KEY = prove( ``
GoodParameters(dimindex(:'r),dimindex(:'c), dimindex(:'n))
==>
(
  ( (Hash f (s:('r+'c) word) (WORD_TO_BITS (k: 'r word) ++ l)):'n word)
  =
  (Hash f (f ( s ?? 0w:'c word @@ k)) (l))
 )
  ``,
rw [Hash_def]  >>
rw [Pad_def, PadZeros_def] >>
qpat_abbrev_tac `Z1= Zeros X` >>
qpat_abbrev_tac `Z2= Zeros X` >>
qspecl_then [`s`,`k`,`[]`,`l++ [T] ++ Z1 ++ [T]`] assume_tac
Absorb_SplittoWords >>
`dimindex(:'r) >1`
  by ( fs [GoodParameters_def] >> simp [] ) >>
`LENGTH (l++ [T] ++ Z1 ++ [T])  > 0` by simp [] >>
fs [simple_lemma] >>
rw [SplittoWords2_def, Absorb_def] >>
qunabbrev_tac `Z1` >>
qunabbrev_tac `Z2` >>
rw [LENGTH_WORD_TO_BITS] >>
`dimindex(:'r)>0` by simp [GoodParameters_def] >>
rw [GSYM ADD_ASSOC,a_mult_b_mod_a_lemma] 
);


val same_output_ind = prove(
``! f
  (* The MITB's state in the real game *)
  (cntl:control) (pmem:('r+'c) word) (vmem:('r+'c) word)  (cor_r:bool)
  (* The functionality's state (cor_s is shared with Sim)*)
  k cor_f
  (* The dummy adversary's state, does not matter really *)
  nd
  (* The simulator's state *)
  cor_s cntl_s vm_s m_s
  (* The environment's query *)
  (input: ('r env_message) list)
  (* Trace in the mitbgame *)
  (mitb_trace: ((('c, 'r) proto_state # num) # ('n word,'n mitb_out)
  GameOutput) list )
  (* Trace in the almost ideal game *)
  (alm_ideal_trace)
  .
    (GoodParameters (dimindex(:'r),dimindex(:'c),dimindex(:'n)))
    /\
    (STATE_INVARIANT f  ((cntl,pmem,vmem),cor_r) ((k,cor_f),(cor_s,cntl_s,vm_s,m_s)) )
    /\
    (mitb_trace = EXEC_LIST_FULL
      ((PROTO ( (MITB_STEP:('c,'n,'r) mitbstepfunction) f))
       : ('c,'r) proto_state -> ('n,'r) real_message
         -> (('c,'r) proto_state) # 'n real_proto_message)
      DUMMY_ADV
      (((cntl,pmem,vmem),cor_r),nd)
      input)
    /\
    (alm_ideal_trace = EXEC_LIST_FULL (FMAC (Hash f ZERO)) SIM
                  ((k,cor_f),(cor_s,cntl_s,vm_s,m_s))
                  input)
    ==>
    (
    EVERY (\(((s1,_),o1),(s2,o2)). (STATE_INVARIANT f s1 s2) /\ (o1=o2) )
      (ZIP (mitb_trace,alm_ideal_trace))
    )
``,
Induct_on `input`
>- (rw rws )
>>
rw [EXEC_LIST_FULL_def] >>
rw [listTheory.EVERY_DEF]
  >- ( (* Show that property holds for the last elements *)
  qpat_assum `! f ctnl . X` (fn t=> all_tac)  >>
        (* remove IH because we don't need it *)
  simp [LET_THM] >>
  Cases_on `s''` >>
  Cases_on `s'` >>
  simp [] >>
  qsuff_tac `STATE_INVARIANT f q (q',r')`
  >- ( (*Show that if STATE_INVARIANT holds, output is equal, too *)
  Cases_on `h`
  >- (
    Cases_on `a`
    >- ( (* SetKey *)
      split_all_pairs_tac >>
      fs rws_invariants >>
      split_all_control_tac >> fs [] >>
      split_all_bools_tac >> fs [] >>
      fs [Initial_State_MITB_def, Initial_State_ALMOST_IDEAL_def] >>
      fs rws >>
      rfs []
    )
    >- ( (* Mac *)
      lfs [MITB_GAME_def, EXEC_STEP_def, ROUTE_THREE_def,
      ROUTE_def, ENV_WRAPPER_def] >>
      Cases_on `~cor_r` >>
      first_assum((fn t => fs[t]) o MATCH_MP ( Q.GEN `m` mac_message_lemma)) >>
      fs rws >>
      split_all_pairs_tac >>
      fs rws_invariants >>
      split_all_control_tac >> fs [] >>
      split_all_bools_tac >> fs [] >>
      fs [Initial_State_MITB_def, Initial_State_ALMOST_IDEAL_def] >>
      fs rws >>
      rw [Hash_WORD_TO_BITS_KEY]
      )
      >> (* Corrupt *)
      (
        split_all_pairs_tac >>
        fs rws_invariants >>
        split_all_control_tac >> fs [] >>
        split_all_bools_tac >> fs [] >>
        fs [Initial_State_MITB_def, Initial_State_ALMOST_IDEAL_def] >>
        fs rws >>
        rfs []
      )
      )
    >>
      Cases_on `b` >>
      split_all_pairs_tac >>
      fs rws_invariants >>
      split_all_control_tac >> fs [] >>
      split_all_bools_tac >> fs [] >>
      fs [Initial_State_MITB_def, Initial_State_ALMOST_IDEAL_def] >>
      fs rws >>
      lfs (rws@rws_hash) >>
      rfs [] >>
      rw (rws@rws_hash) >>
      BasicProvers.EVERY_CASE_TAC >>
      fsrw_tac [ARITH_ss] rws >> rw[]
    )
    >> (* Use Invariant_cor Invariant_cntl Invariant_mem to show
    STATE_INVARIANT holds in the next step *)
    (* not needed anymore *)
    (* `STATE_INVARIANT f ((cntl,pmem,vmem),cor_r) *)
    (* ((k,cor_f),cor_s,cntl_s,vm_s,m_s)` *)
    (*   by rw [initial_state_fulfulls_invariant] >> *)
    (* rw [STATE_INVARIANT_def] >> *)
    qpat_assum `A = ((q',r'),out)` (assume_tac o SYM) >>
    qpat_assum `A = ((q,r),out')` (assume_tac o SYM) >>
    split_all_pairs_tac >>
    fs [LET_THM] >>
    simp [] >>
    (* HERE *)
    cheat
)
    >> (* Use Invariant_cor Invariant_cntl Invariant_mem to show
    STATE_INVARIANT holds in the next step *)
    `STATE_INVARIANT f ((cntl,pmem,vmem),cor_r)
    ((k,cor_f),cor_s,cntl_s,vm_s,m_s)`
      by rw [initial_state_fulfulls_invariant] >>
    simp [STATE_INVARIANT_def] >>
    split_all_pairs_tac >>
    fs [LET_THM] >>
    simp [] >>
    conj_tac >- (
      first_x_assum(mp_tac o MATCH_MP(
      Invariant_cor |> REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
      disch_then(fn th => first_x_assum (mp_tac o MATCH_MP th)) >>
      simp[ALMOST_IDEAL_GAME_def,MITB_GAME_def] >>
      disch_then(qspecl_then [`nd`,`h`] mp_tac) >>
      simp[] ) >>
    conj_tac >- (
      first_x_assum(mp_tac o MATCH_MP(
      Invariant_cntl |> REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
      disch_then(fn th => first_x_assum (mp_tac o MATCH_MP th)) >>
      simp[ALMOST_IDEAL_GAME_def,MITB_GAME_def] >>
      disch_then(qspecl_then [`nd`,`h`] mp_tac) >> simp [] 
      )>>
      first_x_assum(mp_tac o MATCH_MP(
      Invariant_mem |> REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
      disch_then(fn th => first_x_assum (mp_tac o MATCH_MP th)) >>
      simp[ALMOST_IDEAL_GAME_def,MITB_GAME_def] >>
      disch_then(qspecl_then [`nd`,`h`] mp_tac ) >> simp []
    )
>> (* Use Invariant_cor Invariant_cntl Invariant_mem to show
STATE_INVARIANT holds in the next step *)
cheat
);

val same_output = prove(
``! f
  (* The MITB's state in the real game *)
  (cntl:control) (pmem:('r+'c) word) (vmem:('r+'c) word)  (cor_r:bool)
  (* The functionality's state (cor_s is shared with Sim)*)
  k cor_f
  (* The dummy adversary's state, does not matter really *)
  nd
  (* The simulator's state *)
  cor_s cntl_s vm_s m_s
  (* The environment's query *)
  (input: ('r env_message) list) 
  (* Trace in the mitbgame *)
  (mitb_trace: ((('c, 'r) proto_state # num) # ('n word,'n mitb_out)
  GameOutput) list )
  (* Trace in the almost ideal game *)
  (alm_ideal_trace)
  .
    (GoodParameters (dimindex(:'r),dimindex(:'c),dimindex(:'n)))
    /\
    (Initial_State_MITB f  ((cntl,pmem,vmem),cor_r) )
    /\
    (Initial_State_ALMOST_IDEAL ((k,cor_f),(cor_s,cntl_s,vm_s,m_s)))
    /\
    (mitb_trace = EXEC_LIST_FULL 
      ((PROTO ( (MITB_STEP:('c,'n,'r) mitbstepfunction) f))
       : ('c,'r) proto_state -> ('n,'r) real_message
         -> (('c,'r) proto_state) # 'n real_proto_message)
      DUMMY_ADV
      (((cntl,pmem,vmem),cor_r),nd)
      input)
    /\
    (alm_ideal_trace = EXEC_LIST_FULL (FMAC (Hash f ZERO)) SIM
                  ((k,cor_f),(cor_s,cntl_s,vm_s,m_s))
                  input)
    ==>
    (
    EVERY (\(((s1,_),o1),(s2,o2)). (STATE_INVARIANT f s1 s2) /\ (o1=o2) ) 
      (ZIP (mitb_trace,alm_ideal_trace))
    )
``,
(* TODO *)
;


val _ = export_theory();

(* vim: tw=72:comments=sr\:(*,m\:\ ,exr\:*)
 *  *)
