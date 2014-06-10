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
open UCcomTheory;
open spongeTheory;
open lcsymtacs;

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
val _ =
 Hol_datatype
  `control = Ready | Absorbing | AbsorbEnd`;

(*
Datatype of input commands
*)
val _ =
 Hol_datatype
  `command = Move
           | Skip
           | Input of 'r word => num`;

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
   ``: 
   (('r+'c) word -> ('r+'c) word)  (* permutation *)
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

(*
At every position, the bit in a word constructed using
word_from_bin_list concides with the value at the same position in the
original bitstring.
*)
val word_bit_word_from_bin_list = store_thm("word_bit_word_from_bin_list",
  ``∀ls b.
      EVERY ($> 2) ls ∧ b < LENGTH ls ⇒
      (word_bit b ((word_from_bin_list ls):'a word) = b < dimindex (:'a) ∧ (EL b ls = 1))``,
  rw[word_from_bin_list_def,l2w_def,word_bit_n2w] >>
  rw[GSYM numposrepTheory.num_from_bin_list_def] >>
  rw[numposrepTheory.BIT_num_from_bin_list] >>
  rw[EQ_IMP_THM] >>
  assume_tac DIMINDEX_GT_0 >>
  DECIDE_TAC)

(*
The previous statement holds for BITS_TO_WORD, too.
REMARK: word_from_bin_list translates from num list, where BITS_TO_WORD
translates from bool list. We have chosen the latter representation in
spongeTheory, hence the "indirection".
*)
val word_bit_BITS_TO_WORD = store_thm("word_bit_BITS_TO_WORD",
  ``∀ls x. x < LENGTH ls ⇒ (word_bit x ((BITS_TO_WORD ls):'a word) = x < dimindex (:'a) ∧ EL x ls)``,
  rw[BITS_TO_WORD_def] >>
  qmatch_abbrev_tac`word_bit x (word_from_bin_list l) ⇔ y` >>
  `EVERY ($> 2) l` by (
    simp[Abbr`l`,EVERY_MAP,EVERY_MEM] >> rw[] ) >>
  fs[Abbr`l`] >> simp[word_bit_word_from_bin_list] >>
  simp[EL_MAP,Abbr`y`] >> rw[])

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
`` (x < dimindex(:'a)) ==> ((a:'a word || b) ' x = a ' x \/ b ' x) ``,
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
(LENGTH(m) < dimindex(:'r)-1)
/\
( 2 < dimindex(:'r))
/\
(LENGTH(m) <> 0 )
==>
(
(BITS_TO_WORD (m ++ (T::(Zeros (dimindex(:'r)-2-LENGTH (m)))++[T]))):'r word
=  ((LENGTH m)-1 -- 0 ) (BITS_TO_WORD m) || PAD_WORD (LENGTH m)
)
``,
strip_tac >>
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
(BITS_TO_WORD (T::(Zeros (dimindex(:'r)-2))++[T])):'r word
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
((LENGTH m)-1 -- 0 ) (BITS_TO_WORD m) || PAD_WORD (LENGTH m) )
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
    = (Ready, f(key @@ (ZERO:'c word)),ZERO))
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
    = 2 < r /\ 0 < c /\ n <= r`;

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
      (if cntl_n = Ready then ((dimindex(:'n)-1 >< 0) vmem) else (ZERO:'n word )))
      )
    `;

(*
Datatype of commands to the library/protocol calling the MITB
*)
val _ =
 Hol_datatype
  `mac_query =
            SetKey of 'r word
          | Mac of bits
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
 Hol_datatype
  `adv_to_mac_msg =
            CorruptACK
          | OracleQuery of bits
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
              ((k,F),(Proto_toEnv 0w))
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

TODO: Will be simplified using RunMITB above.
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
           let (s0,(rdy0,dig0)) = mitbf (s,(T,F,(ZERO: 'r word),0)) in
           (* make sure that MITB is in Ready state *)
             let (sr,rdyr,digr) =
              ( if (rdy0=F) then
                  (mitbf (s0,(F,T,(ZERO: 'r word),0)))
                else
                  (s0,rdy0,dig0)
              ) in
                (* Split the message in pieces of length r or less
                * apply mitb(s,F,F,m_i,|m_i|) to every state s and block m_i
                * and use the resulting state for computation with the next
                * block
                *)
                let sf =
                 FOLDR (\blk. \state.
                  let (si,rdyi,dgi) = mitbf
                  (* TODO check if BITS to word preserves the endianness for the
                  * last block *)
                  (state,(F,F,BITS_TO_WORD(blk), (LENGTH blk))) in
                    if (LENGTH blk) = dimindex(:'r)-1 then
                      (* special case: we need to add an empty block for padding *)
                      let (sl,rdyl,dgl) = mitbf (si,(F,F,(ZERO: 'r word), 0)) in
                        sl
                    else si
                  ) sr (Split (dimindex(:'r)) m) in
                (* let sf = AUX_FEED_MITB mitbf sr m in  *)
                  (* learn digest by skipping *)
                  let (s1,rdy1,digest) = mitbf (sf,(T,F, (ZERO: 'r word),0)) in
                  (* two consecutive moves to re-initialise vmem *)
                  let (s2,rdy2,dig2) = mitbf (s1,(F,T, (ZERO: 'r word),0)) in
                  let (s3,rdy3,dig3) = mitbf (s2,(F,T, (ZERO: 'r word),0)) in
                    ((s3,F),(Proto_toEnv digest))
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
   (* TODO: Consider cutting the messages here already.
   * Cases:
   *  inp_size=r) take full block
   *  inp_size=r-1 add 1, goto absorb end and add zeros in the next step
   *  inp_size<r-1 query oracle.
   *  *)
   if (inp_size=r) then
    ((T,Absorbing,ZERO, ((inp,inp_size)::m)),(Adv_toEnv (F,ZERO)))
   else
    if (inp_size=r-1) then
      ((T,AbsorbEnd,ZERO,((inp,inp_size)::m)),(Adv_toEnv (F,ZERO)))
    else
      if inp_size<r-1 then
      (*  Send to Functionality for communication. Proceed when response is *)
      (* received, see (MARK)  *)
      ((T,Absorbing,vm,[]),(Adv_toP (OracleQuery ([(*Dummy for now*)] ))))
           else (*if inp_size>r behave like Skip*)
      ((T,Absorbing,vm,m),(Adv_toEnv (F,ZERO)))
    (* ) *)
    )
    /\
(SIM (T,AbsorbEnd,vm,m) (EnvtoA (F,F,inp,inp_size)) =
  if (inp_size <= dimindex(:'r)) then
      ((T,AbsorbEnd,vm,[]),(Adv_toP (
       OracleQuery ([ (*Dummy, for now *) ])
       (* m++(TAKE inp_size inp) *)
       )))
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

val _ = type_abbrev ("sim_plus_ideal_game_state",
   ``: (bits # bool) #('c,'r)  mitb_state ``);
(*               ^ corruption status *)

val _ = type_abbrev ("ideal_game_state", ``: (bits # bool) ``);
(*                                 corruption status ^ *)

(* ('n,'r) real_message is *)
val _ = type_abbrev ("real_message",
    ``: ('r mac_query, 'r mitb_inp,  'n word,
     'n mitb_out , 'n mitb_out ,'r mitb_inp ) Message ``);

(* ('n,'r) adv_message is *)
val _ = type_abbrev ("adv_message",
    ``: (
    'r mitb_inp,
     'n mitb_out
     ) AdvMessage ``);

val _ = type_abbrev ("env_message",
    ``: ('r mac_query, 'r mitb_inp  ) EnvMessage ``);

(*
We instantiate the real world with the protocol using the MITB, given
parameters and the compression function
*)
(* TODO Does not work I can't see why *)

(* val REAL_DUMMY_ADV_def = *)
(*   Define ` *)
(*  REAL_DUMMY_ADV  _ (m : ('n,'r) real_message) *)
(* = *)
(*     (DUMMY_ADV 0 m)`; *)

(* val MITB_GAME_def = *)
(*     Define ` *)
(*       MITB_GAME f *)
(*         = *)
(*        EXEC_STEP *)
(*        ( PROTO ( (MITB_STEP:('c,'n,'r) mitbstepfunction) f)) *)
(*        REAL_DUMMY_ADV *)
(*         `; *)

(*

val ALMOST_IDEAL_GAME_def =
    Define `
      (ALMOST_IDEAL_GAME (r,(c:num),(n:num)) (h: bits -> bits ) )
      :
      =
      EXEC_STEP ( FMAC (r,c,n) h) (SIM (r,c,n))
      `
      *)

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
    (*TODO Do we need more? We could assert that for cor_r=F,
    * the MITB is alway in ready. But I wouldn't think we need this *)
    `;

(* The complete invariant (will grow in the future) *)
val STATE_INVARIANT_def =
  Define `
  STATE_INVARIANT (state_r) (state_f) =
     (STATE_INVARIANT_COR (state_r) (state_f))
     /\
     (STATE_INVARIANT_CNTL (state_r) (state_f))
        `;

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

(*
The following two lemmas are used in the (uncomplete) proof for the
Invariant_cor and Invariant_cntl below, but will substituted by a
stronger lemma derived from put_in_ready_state_lemma, mac_message_lemma
and

TODO: When mitb_skip_lemma lemma is shown, reformulate PROTO so it
uses PROCESS_MESSAGE_LIST (defined below) and then strengthen lemma so
it defines vmem.
lemma_proto_mac_cor_one_andahalf and lemma_proto_mac_cor_two are then
obsolete.
*)

val lemma_proto_mac_cor_one_andahalf = prove (
 ``
 (ROUTE (PROTO mitbf) DUMMY_ADV state_inp = state_out) ⇒
 (state_inp = (((s,F),0),EnvtoP (Mac m)))
 ⇒
 (?dig foo bar .
 (state_out = (((foo,F),0),PtoEnv dig)))
 ``,
 rw [] >>
    simp [ROUTE_def,PROTO_def, pairTheory.UNCURRY, PROTO_WRAPPER_def]
    );

val lemma_proto_mac_cor_two = prove (
 ``
 (ROUTE (PROTO (MITB_STEP f)) DUMMY_ADV state_inp = state_out) ⇒
 (state_inp = (((s,F),0),EnvtoP (Mac m)))
 ⇒
 (?dig foo bar .
 (state_out = ((((Ready,foo,bar),F),0),PtoEnv dig)))
 ``,
 rw [] >>
    simp [ROUTE_def,PROTO_def, pairTheory.UNCURRY,
    PROTO_WRAPPER_def] >>
    (* simp [MITB_STEP_def, MITB_FUN_def] *)
    cheat
    );

val rws =
  [EXEC_STEP_def,LET_THM,ENV_WRAPPER_def,ROUTE_THREE_def,ROUTE_def,
   SIM_def,ADV_WRAPPER_def,DUMMY_ADV_def,PROTO_def,MITB_STEP_def,
   MITB_def,MITB_FUN_def,PROTO_WRAPPER_def,STATE_INVARIANT_def,FMAC_def,
   STATE_INVARIANT_COR_def, STATE_INVARIANT_CNTL_def
                                        ]


val mitb_skip_lemma =
  prove (
  ``
    (((cntl',pmem',vmem'),(rdy,dig)) = RunMITB (MITB_STEP f) (cntl,pmem,vmem) [(T,b,inp,len)] )
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

(*
A certain chain of commands can be used to put the MITB into ready
state.
*)
val put_in_ready_state_lemma = prove (
``
    (
    (((cntl',pmem',vmem'),(rdy,dig)) =
     let ((cntl_t,pmem_t,vmem_t),(rdy_t,dig_t)) =
        RunMITB (MITB_STEP f) (cntl,pmem,vmem) [(T,b,inp,len)]
      in
        if (rdy_t=F) then
          RunMITB (MITB_STEP f) (cntl_t,pmem_t,vmem_t) [(F,T,inp2,len2)]
        else
          ((cntl_t,pmem_t,vmem_t),(rdy_t,dig_t))
     )
    ==>
    (
    ( cntl'=Ready)
    )
    )
    ``,
    rw [LET_THM] >>
    last_assum(PairCases_on_tm o rand o  rand o concl) >>
    POP_ASSUM (ASSUME_TAC o SYM ) >>
    first_assum(mp_tac o MATCH_MP mitb_skip_lemma) >>
    rw [] >>
    Cases_on `p3` >>
    fs [] >>
    fs [RunMITB_def, MITB_STEP_def, MITB_FUN_def, MITB_def] >>
    fsrw_tac [ARITH_ss] [LET_THM]
    );

(*
PROCESS_MESSAGE_LIST: bits list -> 'r mitb_inp list
Given a list of bitstrings, PROCESS_MESSAGE_LIST produces a list of
input queries to the MITB that will leave the MITB in ready state, with
vmem set to the hash of the flattening of the input.

PROCESS_MESSAGE_LIST will be used in a re-definition of the protocol.
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


(* This lemma is useful for simplifying terms occuring in the padding *)
val a_b_mod_a_lemma = prove (
``( 0 < a) ==> ((a + b) MOD a = b MOD a)``,
rw [] >>
first_assum (ASSUME_TAC o SYM o (Q.SPECL [`a`,`b`]) o (MATCH_MP
MOD_PLUS)) >>
first_assum (ASSUME_TAC o CONJUNCT2 o (MATCH_MP DIVMOD_ID)) >>
rw []);

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
  Hash_def, Output_def, Absorb_def, SplittoWords_def,
  Pad_def, Zeros_def, PadZeros_def,
  a_b_mod_a_lemma
   ]
(*
This lemma shows that the MACing step in the protocol is executed
correctly, i.e., that the virtual memory after execution equals a
properly computed hash,  given that the MITB was in ready state before
(which can be established using put_in_ready_state_lemma).

REMARK: During protocol excution, we will be able to establish that
vmem equals pmem after moving into Absorbing. Thus
(Absorb f vmem (SplittoWords (Pad ( dimindex(:'r) ) m)))
will equal Hash f ..  if composed right.
*)

val mac_message_lemma = prove (
``! r m pmem vmem.
   (
   (r = dimindex(:'r))
   /\
   (GoodParameters (dimindex(:'r),dimindex(:'c),dimindex(:'n)))
   )
   ==>
   (
   (((cntl_t,pmem_t,vmem_t),(rdy_t,dig_t)) =
        RunMITB
          (MITB_STEP: ('c,'n,'r)mitbstepfunction  f)
          (Absorbing,pmem,vmem)
         (PROCESS_MESSAGE_LIST
              (Split (dimindex(:'r)) m)))
    ==>
    (
    (( cntl_t=Ready)
    /\
    ( pmem_t = pmem )
    /\
    ( vmem_t = (Absorb f vmem
       (SplittoWords (Pad ( dimindex(:'r) ) m))
       )))))
    ``,
   recInduct(Split_ind) >>
   strip_tac >> strip_tac >>
   Cases_on `(LENGTH msg) <= dimindex(:'r)`
   >-
   (
    simp [GoodParameters_def,(Once Split_def)] >>
    (ntac 4 strip_tac) >>
    `Split (dimindex(:'r)) msg = [msg]`
      by (rw [(Once Split_def)]) >>
    `(dimindex(:'r) = LENGTH msg  )
     \/
     (dimindex(:'r)-1 = LENGTH msg )
     \/
     ((0 < LENGTH msg) /\ (LENGTH msg < dimindex(:'r)-1 ))
     \/
     (0 = LENGTH msg )` by simp []
    >- (* LENGTH msg = dimindex(:'r) *)
    (
      fs rws_macking >>
      fsrw_tac [ARITH_ss] [] >>
      fs rws_macking >>
      ` ~(dimindex(:'r) <= dimindex(:'r) -2)` by simp [] >>
      pop_assum (fn thm => fsrw_tac[ARITH_ss] [thm]) >>
      fs rws_macking >>
      rw rws_hash >>
      lfs [a_b_mod_a_lemma] >>
      `! rest more . ((msg++[T])++ rest) ++ more
       = msg++ ([T]++ rest ++ more)` by rw [] >>
      pop_assum (fn thm => PURE_REWRITE_TAC [thm]) >>
      qmatch_abbrev_tac
        `word = Absorb f vmem
           (MAP BITS_TO_WORD (Split (len) (msg ++
           rest )))` >>
      cheat
      (* this proof should be easy using LengthZeros, but it isn't *)
      (* `LENGTH(rest)=dimindex(:'r)` by (simp [Abbr`rest`] >> *)
      (* fs[ LengthZeros ] ) >> *)
      (* Q.ISPECL_THEN  [`msg`,`rest`] assume_tac  Split_APPEND >> *)
      (* `0<LENGTH(msg) /\ 0<LENGTH(rest)` by simp [] >> *)
      (* lfs [] >> ntac 2 (pop_assum (fn thm => ALL_TAC)) >> *)
      (* pop_assum (fn thm => simp [thm]) >> *)
      (* qpat_abbrev_tac `bla= (LENGTH msg)` >> *)
      (* qpat_abbrev_tac `blubb=(msg++rest)` >> *)
      (* qpat_abbrev_tac `fii=((Split bla) blubb)` >> *)
      (* (1* WEIRD... this fails ... *1) *)
      (* simp [ INST_TYPE [alpha |-> Type `:bool `] Split_APPEND] >> *)
      (* pop_assum (fn thm => PURE_REWRITE_TAC [thm]) >> *)

      (* qpat_abbrev_tac `M=(Split (dimindex(:'r)) msg): bits list` >> *)
      (* qpat_assum `Split (dimindex(:'r)) msg = X` (fn thm => *)
      (* (PURE_REWRITE_TAC [thm]>> assume_tac thm)) >> *)
      (* lrfs [] *)
      (* fs rws_macking >> *)

      (* `~(dimindex (:'r) <= 1 + (dimindex (:'r)-2))` by (simp []) >> *)
      (* lfs (rws @ rws_macking @ rws_hash) >> *)
      (* simp rws_hash >> *)

      (* qpat_abbrev_tac `R=(dimindex(:'r))` >> *)
      (* qpat_abbrev_tac `Z= ( R - 2)` >> *)
      (* qpat_abbrev_tac `ZZ= ( - 2)` >> *)

      (* `! rest more . ((msg++[T])++ rest) ++ more *)
      (*  = msg++ ([T]++ rest ++ more)` by rw [] >> *)
      (* pop_assum (fn thm => PURE_REWRITE_TAC [thm]) >> *)
      (* qpat_assum `LENGTH msg = x` *)
      (*   (fn thm => PURE_REWRITE_TAC [thm,TAKE_LENGTH_APPEND] >> assume_tac thm) *)



      (* `SplittoWords w = (MAP (BITS_TO_WORD:bits -> 'r word)) (Split *)
      (* (dimindex(:'r)) w)` by *)
      (* rw[SplittoWords_def] *)
      (* simp [SplittoWords_def,GSYM combinTheory.o_THM] *)

    (* from a previous attempt  *)
    (* >> *)
    (* `~(dimindex (:'r) <= 1 + (dimindex (:'r)-2))` by (simp []) >> *)
    (* TRY (`LENGTH msg <= dimindex(:'r)-2` by decide_tac ) >> *)
    (* lfs (rws @ rws_macking) >> *)
    (* fs rws_hash >> *)
    (* lfs [] *)
    (* >- (1* LENGTH msg = dimindex(:'r) *1) *)
    (* ( *)
    (*   `((dimindex(:'r) - (dimindex(:'r)+2) MOD dimindex(:'r) MOD *)
    (*   dimindex(:'r)) = dimindex(:'r) - 2 )` by simp *)
    (*   [a_b_mod_a_lemma] >> *)
    (*   fs [] >> *)
    (*   Q.ISPEC_THEN `msg:bits` (ASSUME_TAC) TAKE_LENGTH_APPEND >> *)
    (*   Q.ISPEC_THEN `msg:bits` (ASSUME_TAC) DROP_LENGTH_APPEND >> *)
    (*   qpat_assum `LENGTH msg = X` (fn tm => fs [tm] >> assume_tac tm ) >> *)
    (*   asm_simp_tac std_ss [GSYM APPEND_ASSOC]  >> *)

    (*   rw [Once (Split_def),LengthZeros,padding_block_full] >> *)
    (*   lfs [] >> *)
    (*   (1* CURRENT POS *1) *)
    (*   cheat *)
    )
    >>
    cheat
    )
  >>
   qpat_abbrev_tac `R= dimindex(:'r) ` >>
   rw [GoodParameters_def] >>
   `R <> 0` by DECIDE_TAC >>
   POP_ASSUM (fn tm => fs [tm]) >>
   rfs [] >>
   (* qpat_assum `~(LENGTH msg <= R)` (fn thm => fs [thm]) >> *)
   (* lfs >> *)
   cheat
   (* worked quite well *)
   (* fs [(Once Split_def) ] >> *)
   (* lfs rws_macking >> *)
   (* lfs [] >> *)
   (* rfs [] >> *)
   (*  lfs [PROCESS_MESSAGE_LIST_def, (Once Split_def)]  >> *)
   (* `~(R=0)` by simp []  >> *)
   (*  fs [] >> *)
   (* ------------------------------- *)
   (*  `(LENGTH (TAKE (dimindex(:'r)) msg)) = (dimindex (:'r))` *)
   (*    by  first_assum (mp_tac o MATCH_MP listTheory.LENGTH_TAKE) *)
   (*    simp [] *)
    );

(* We want to show this thing actually *)
(* TODO use prev. lemma to  show this *)
(* `! r m . *)
(*    ( *)
(*    (r = dimindex(:'r)) *)
(*    /\ *)
(*    (GoodParameters (dimindex(:'r),dimindex(:'c),dimindex(:'n))) *)
(*    /\ *)
(*    (((cntl_t,pmem_t,vmem_t),(rdy_t,dig_t)) = *)
(*         RunMITB *)
(*           (MITB_STEP: ('c,'n,'r)mitbstepfunction  f) *)
(*           (Ready,pmem,vmem) *)
(*         ((F,T,inp,len) *)
(*          :: (PROCESS_MESSAGE_LIST *)
(*               (Split (dimindex(:'r)) m)) *)
(*         ))) *)
(*     ==> *)
(*     (( cntl_t=Ready) *)
(*     /\ *)
(*     ( pmem_t = pmem ) *)
(*     /\ *)
(*     ( vmem_t = BITS_TO_WORD (Hash (dimindex(:'r), dimindex(:'c), dimindex(:'n)) *)
(*             (WORD_TO_BITS o (f o BITS_TO_WORD )) *)
(*             ( Zeros (dimindex(:'r) + dimindex(:'c))) m)) *)
(*             ) *)
(*     ` *)



(*
Given that the complete invariant holds, the corruption part of
the invariant holds in the next step.
*)
val Invariant_cor = prove(
 ``! f h
     (* The MITB's state in the real game *)
     (cntl:control) (pmem:('r+'c) word) (vmem:('r+'c) word)  (cor_r:bool)
     (* The functionality's state (cor_s is shared with Sim)*)
      k cor_f
      (* The simulator's state *)
      cor_s cntl_s vm_s m_s
      (* The environment's query *)
      input.
        (GoodParameters (dimindex(:'r),dimindex(:'c),dimindex(:'n)))
        /\
        (STATE_INVARIANT ((cntl,pmem,vmem),cor_r)
        ((k,cor_f),(cor_s,cntl_s,vm_s,m_s)))
      ==>
      let ((((cntl_n,pmem_n,vmem_n),cor_r_n),_), out_r) =
      EXEC_STEP (PROTO (MITB_STEP f))
      DUMMY_ADV ((((cntl,pmem,vmem),cor_r),0),input)
      in
        (
        let
        (((k_n,cor_f_n),(cor_s_n,cntl_s_n,vm_s_n,m_s_n)),out_i) =
           EXEC_STEP ( FMAC  h) SIM
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
      split_all_bools_tac >>
      fsrw_tac [ARITH_ss] rws >> rw[] >>
      BasicProvers.EVERY_CASE_TAC >>
      fsrw_tac [ARITH_ss] rws >> rw[] >>
      fsrw_tac[ARITH_ss][] >>
      fs [GoodParameters_def] >>
      `~(dimindex (:'r) <= 1 + (dimindex (:'r)-2))` by (simp []) >>
      fsrw_tac [ARITH_ss] rws
      )
    >> (*Input to protocol *)
    (
      Cases_on `cor_f`
      >-
      ( (* cor_f T  (proto ignores messages) *)
        split_all_pairs_tac >>
        split_all_control_tac >>
        Cases_on `b` >>
        fs [EXEC_STEP_def, ROUTE_THREE_def, ENV_WRAPPER_def, ROUTE_def, PROTO_def, PROTO_WRAPPER_def] >>
        RULE_ASSUM_TAC EVAL_RULE >>
        fs[STATE_INVARIANT_COR_def]
      )
      >> (*cor_f F *)
      (
      Cases_on `? m. b=(Mac m)`
        >-
        (
          fs [EXEC_STEP_def, ROUTE_THREE_def, ENV_WRAPPER_def] >>
          (* we are here *)
          fs[LET_THM] >>
          last_assum(PairCases_on_tm o rand o rand o rand o lhs o concl) >>
          first_assum(mp_tac o MATCH_MP
            (GEN_ALL lemma_proto_mac_cor_one_andahalf)) >>
          simp[] >> strip_tac >> fs[] >>
          fs [ROUTE_def] >>
          split_all_control_tac >>
          split_all_pairs_tac >>
          fsrw_tac [ARITH_ss] rws >> rw[] >>
          simp []
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
Given that the complete invariant holds, the control part
of the invariant holds in the next step.
*)
(* Fails currently *)
val Invariant_cntl = prove(
 `` ! f h
     (* The MITB's state in the real game *)
     (cntl:control) (pmem:('r+'c) word) (vmem:('r+'c) word)  (cor_r:bool)
     (* The functionality's state (cor_s is shared with Sim)*)
      k cor_f
      (* The simulator's state *)
      cor_s cntl_s vm_s m_s
      (* The environment's query *)
      input.
        (GoodParameters (dimindex(:'r),dimindex(:'c),dimindex(:'n)))
        /\
        (STATE_INVARIANT ((cntl,pmem,vmem),cor_r)
        ((k,cor_f),(cor_s,cntl_s,vm_s,m_s)))
      ==>
      let ((((cntl_n,pmem_n,vmem_n),cor_r_n),_), out_r) =
      EXEC_STEP (PROTO (MITB_STEP f))
      DUMMY_ADV ((((cntl,pmem,vmem),cor_r),0),input)
      in
        (
        let
        (((k_n,cor_f_n),(cor_s_n,cntl_s_n,vm_s_n,m_s_n)),out_i) =
           EXEC_STEP ( FMAC  h) SIM
                      (((k,cor_f),(cor_s,cntl_s,vm_s,m_s)),input)
        in
        (STATE_INVARIANT_CNTL ((cntl_n,pmem_n,vmem_n), cor_r_n)
        ((k_n,cor_f_n),(cor_s_n,cntl_s_n,vm_s_n,m_s_n)))
        )
        ``,
    rw[] >>
    `(cor_s = cor_r) /\ (cor_f = cor_r)` by
      fs[STATE_INVARIANT_def, STATE_INVARIANT_COR_def] >>
    `∃a b. (input = Env_toA a) ∨ (input = Env_toP b)` by (
      Cases_on`input` >> rw[]) >>
      rw[]
      >- (* Input to Adv *)
      (
      split_all_pairs_tac >>
      split_all_control_tac >>
      Cases_on `cor_f` >>
      fs [STATE_INVARIANT_def, STATE_INVARIANT_CNTL_def] >>
      split_all_bools_tac >>
      fsrw_tac [ARITH_ss] rws >> rw[] >>
      BasicProvers.EVERY_CASE_TAC >>
      fsrw_tac [ARITH_ss] rws >> rw[] >>
      fs [GoodParameters_def] >>
      `~(dimindex (:'r) <= 1 + (dimindex (:'r)-2))` by (simp []) >>
      fsrw_tac [ARITH_ss] rws
      )
      >> (* Input to Proto *)
      Cases_on `cor_f`
      >-
      ( (* cor_f T  (proto ignores messages) *)
        split_all_pairs_tac >>
        split_all_control_tac >>
        Cases_on `b` >>
        fs [EXEC_STEP_def, ROUTE_THREE_def, ENV_WRAPPER_def, ROUTE_def, PROTO_def, PROTO_WRAPPER_def] >>
        RULE_ASSUM_TAC EVAL_RULE >>
        fs[STATE_INVARIANT_COR_def, STATE_INVARIANT_CNTL_def]
      )
      >> (* cor_f F *)
      (
      fs [STATE_INVARIANT_def, STATE_INVARIANT_COR_def,
      STATE_INVARIANT_CNTL_def ] >>
      Cases_on `? m. b=(Mac m)`
        >-
        (
          fs [EXEC_STEP_def, ROUTE_THREE_def, ENV_WRAPPER_def] >>
          (* we are here *)
          fs[LET_THM] >>
          last_assum(PairCases_on_tm o rand o rand o rand o lhs o concl) >>
          first_assum(mp_tac o MATCH_MP
            (GEN_ALL lemma_proto_mac_cor_two)) >>
          simp[] >> strip_tac >> fs[] >>
          fs [ROUTE_def] >>
          split_all_control_tac >>
          split_all_pairs_tac >>
          fsrw_tac [ARITH_ss] rws >> rw[] >>
          simp []
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
);

val _ = export_theory();

(* vim: tw=72:comments=sr\:(*,m\:\ ,exr\:*)
 *  *)
