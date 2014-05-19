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
            notation defined below: f(K++(ZEROS 448))

 volatile:  1600-bit register storing MITB state

The initial manufacturer state:

 |---------|-----------|----------|
 | Ready   |f(K||0...0)| 0        |
 |---------|-----------|----------|

 - the control state is initially Ready;

 - the permanent memory contains the Keccak-f permution of an initial
   manufacturer-supplied 1152-bit key padded with 448 zeros. In the
   HOL notation defined below: f(K++(ZEROS 448));

 - the volatile memory contains 1600-bit 0 (ZEROS 1600);

Commands (inputs from user/attacker):
 
 - Skip : {Ready -> Ready} + {Absorbing -> Absorbing}
   State unchanged (stutter, no-op).

 - Move : {Ready->Absorbing} + {Absorbing->Ready}.
   In Ready: start to hash a new message.
   In Absorbing: abandon absorbing, set vmem to zeros.

 - Input bits len : {Ready->Ready} + {Absorbing->{Absorbing,AbsorbEnd,Ready}}.
   In Ready installs f(key++(ZEROS c)) in permanent memory.  
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
(*              permanent   volatile      *)

(*
Type abbreviation for MITB inputs
*)
val _ =
 type_abbrev
  ("mitb_inp",
   ``:bool # bool # 'r word # num``);
(*    skip   move  block  size     *)
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
*)
val _ = 
 type_abbrev
 (* ('c,'r) mitb is *)
  ("mitb", 
   ``: ( ('r+'c) word -> ('r+'c) word) (* permutation *)
       -> (('c,'r) mitb_state) -> ('r command) -> (('c,'r) mitb_state) 
      ``);

val _ = 
 type_abbrev
 (* ('c, 'n,'r) mitbstepfunction is *)
  ("mitbstepfunction", 
  ``: 
  ( ('r+'c) word -> ('r+'c) word)  (* permutation *)
  -> ('c, 'r) mitb_state # 'r mitb_inp 
 -> ('c, 'r) mitb_state # 'n mitb_out
      ``);

(*
Alternative name for the zero word.
*)
val ZERO_def =
 Define
  `ZERO = (0w: 'a word) `;

(* ZERO function used on bits *)
val ZEROS_def =
 Define
  `(ZEROS 0 = [])
   /\
   (ZEROS(SUC n) = F :: ZEROS n)`;

(*
Defines one step of MITB (r,c,n) with permutation function f
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
       (Ready,
        pmem,
          f (
          (* wordlib seems to think:
          *  0 is the lsb
          *  concatination makes left-hand operator more significant
          *  .. check with Sponge implementation..
          * *)
          (* have to review after sponge construction is implemented using
          * word lib. 
          *
          * We compute:
        (*   (vmem XOR 
        *   (TAKE len blk ++ [T] ++ ZEROS(r-len-2) ++ [T] ++ ZEROS c)) *)
        by
        1. rightshifting r-len times (removing the r-len least
        siginificant bits)
        2. leftshifting back again (might remove this step based on how we are
        expected to read input
        3. || with 1^*10^*1 padding, that is 
            (0x1w:'r word) << ((r-len)-1) + 01w
        4.  append c zeroes
        Take care, might need to catch case where len=0 if this code changes.
        *)
          vmem ??
           (
            ( 
             (
              ((blk >>> (r-len))<<(r-len)) (*1 and 2*)
              ||
              ((0x1w) << ((r-len)-1) + 01w) (*3*)
             )
            @@ (ZERO:'c word) (*4*)
           )
          )   
          ))
      else
       if len = r-1 then  (* Exactly one-bit too small *) 
       (AbsorbEnd,
        pmem,
        (* see above *)
        f(vmem ??
          (((blk >>> (1))<<(1)) (*1 and 2*)
          || 
          (0x1w))
          @@ (ZERO:'c word) (*4*)
        ))
        (* f(vmem XOR (TAKE len blk ++ [T] ++ ZEROS c)))  *)
       else  (* Full block *)
      (Absorbing,pmem,f(vmem ?? (blk @@ (ZERO: 'c word)))) 
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
     * f(vmem XOR (ZEROS(r-1) ++ [T] ++ ZEROS c)))) *)
     f(vmem ?? ( (0x1w: 'r word) @@ (ZERO: 'c word) ))
     ))
    `;

(*
Split a message into blocks of a given length
*)
val SplitMessage_def =
 tDefine
  "SplitMessage"
  `SplitMessage r msg = 
    if (r = 0) \/ LENGTH msg <= r 
     then [msg]
     else TAKE r msg :: SplitMessage r (DROP r msg)`
  (WF_REL_TAC `measure (LENGTH o SND)`
    THEN RW_TAC list_ss [LENGTH_DROP]);

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

(* We define a step function that behaves like MITB, but includes the output,
* too.
* Parametric in:
*  f - compression function used inside MITB
*  Input:
*  (cnt,pmem,vmem) - current state of the MITB
*  (skip,move,block,size) - input to the MITB
*  Output:
*  (cntl_n,pmem_n,vmem_n) - next state of the MITB
*  (ready:bool, digest:bits) - output of the MITB
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


val _ =
 Hol_datatype
  `mac_query =
            SetKey of 'r word
          | Mac of bits
          | Corrupt
          `;

val _ =
 Hol_datatype
  `mac_to_adv_msg =
            WasCorrupted 
          | OracleResponse of 'n word
          `;

val _ =
 Hol_datatype
  `adv_to_mac_msg =
            CorruptACK 
          | OracleQuery of bits
          `;

(*  TODO Dummy function. Get rid of this later *)
val WORD_TO_BITS_def=
  Define
  ` WORD_TO_BITS (w:'l word) =
  let 
    bitstring_without_zeros =  MAP (\e.if e=1 then T else F) (word_to_bin_list w)
  in
    ( ZEROS (dimindex(:'l) - (LENGTH bitstring_without_zeros) )) ++
    bitstring_without_zeros`;

val BITS_TO_WORD_def=
  Define
  ` BITS_TO_WORD = 
      word_from_bin_list o ( MAP (\e.if e=T then 1 else 0))`;


(* val b2w_xor_lemma = prove ( *)
(* `` *)
(* ! l1: bits l2:bits. *)
(* ((LENGTH l1) = (LENGTH l2)) *) 
(* ==> *)
(*   ( (BITS_TO_WORD(l1 XOR l2)):'l word = *)
(*   ((BITS_TO_WORD l1):'l word ?? (BITS_TO_WORD l2):'l word)) *)
(*   ``, *)
(*   Induct *) 
(*   >- *) 
(*     ( *) 
(*     Induct >> *)
(*     rw [BITS_TO_WORD_def, XOR_def] >> *)
(*     EVAL_TAC *) 
(*     ) *)
(*   >> *)
(*     Induct_on `l2` *)  
(*     >- (rw []) *)
(*     >> *)
(*         Cases >> Cases >> *) 
(*         (1* Why does this rewrite step fail ? *1) *)
(*         PURE_REWRITE_TAC [BITS_TO_WORD_def] >> *)
(*         cheat *)
(*   ); *)

  

(* State transition function for the functionality defining a perfect MAC
* device for a given Hash function
* Parameters: H  -- Hash function
* Internal state: current key K, corruption status
* Inputs are queries of type query
* Output are bitstrings
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
              (* Adversarial interface may request Hashes with K prepended to
              * the input. This interface will be accessed by SIM, to be able to
              * emulate a MITB *)
          ( FMAC H (K,T) (AtoP (OracleQuery m)) =
          ((K,T),(Proto_toA (OracleResponse (H((WORD_TO_BITS K)++m))))))
          /\
          (* When corrupted, ignore honest queries *)
          ( FMAC H (K,T) (EnvtoP q) = ((K,T),Proto_toEnv 0w))
          `;

(* Sanity test *)
(* val th = *)
(* EVAL ``EXEC_LIST (FMAC  (\m.m)) DUMMY_ADV (((ZERO: word32),F),[]) *) 
(* [Env_toP (Mac m)]``; *)

(* Function defining the protocol that implements FMAC using a MITB. In real
 * life, this protocol corresponds to a client library that computes hashes by
 * splitting the message and feeding it into the MITB. This is how honest users
 * are supposed to use the MITB 
 *
 * Parametric in: 
 * mitbf - step function of MITB,
 * - global parameters for Sponge-construction (only r is used)
 * Inputs: 
 * s - current MITB state
 * T/F - corruption status
 * query
 * Output: bitstring
 * *)
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
           let (s0,rdy0,dig0) = mitbf (s,(T,F,(ZERO: 'r word),0)) in
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
                  ) sr (SplitMessage (dimindex(:'r)) m) in
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
          (* Give adversary blackbox access when corrupted *)
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

(* val protocol_correctness = prove ( *)
(* `` *)

(* ``, *)

(* ); *)


(* Sanity test *)
(* RESTR_EVAL_CONV not found... where does it belong too? *)
(* val RUN = RESTR_EVAL_CONV [``ZEROS``]; *)

(*
RUN ``EXEC_LIST (PROTO (MITB_STEP (r,c,n) (\m.m)) (r,c,n))
     DUMMY_ADV  
   (((Ready,(ZEROS (r+c)),(ZEROS (r+c))),F),[]) [(Env_toA (T,F,(ZEROS (r)),0))]
  ``;

RUN ``EXEC_LIST (PROTO (MITB_STEP (r,c,n) (\m.m)) (r,c,n))
     DUMMY_ADV  
   (((Ready,(ZEROS (r+c)),(ZEROS (r+c))),F),[]) 
   [(Env_toA (T,F,(ZEROS (r)),0));
   (Env_toP (SetKey (ZEROES (r)))) ]
  ``;
*)


val word_take_def =
  Define `
    ( word_take:'a word -> 'b word) w = (dimindex(:'b)-1 >< 0) w
    `;

(* Sim can make queries to F, but only on the adversarial interface. It should
* not alter F's state directly. It should not read its state either, but we
* cheat a little: the corrupt variable from F's state is used -- this should
* actually be a communications step between the two. 
*
* We first define a step function for SIM, which is then used in a wrapper
* function that instantiates the adversarial interface of F as an oracle.
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
      ((T,AbsorbEnd,vm,[]),(Adv_toP (
       OracleQuery ([ (*Dummy, for now *) ])
       (* m++(TAKE inp_size inp) *)
       ))))
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
(* Ignore other queries *)
(SIM (T,cntl,vm,m) (EnvtoA _) = ((T,cntl,vm,m),(Adv_toEnv (F,ZERO))))
      `;

(* Sanity test *)
(*
RUN ``EXEC_LIST 
     (FMAC (10,c,n) hash)
     (SIM (10,c,n))
     (((ZEROS (10+c)),F),(F,Ready,(ZEROS r),[])) 
     [
     (Env_toA (T,F,(ZEROS (10)),0));
     (Env_toP (Mac (ZEROS 20)));
     (Env_toP (Corrupt)); 
     (Env_toP (Mac (ZEROS 20)));
     (Env_toA (T,F,(ZEROS (10)),0));
     (Env_toA (F,T,(ZEROS (10)),0));
     (Env_toA (F,F,(ZEROS (10)),3));
     (Env_toA (T,F,(ZEROS (10)),0))
    ]
  ``;

(* compare with real MITB *)
RUN `` EXEC_LIST 
     (PROTO (MITB_STEP (10,c,n) f) (10,c,n))
     DUMMY_ADV
     (((Ready,(ZEROS (10+c)),(ZEROS (10+c))),F),[]) 
     [
     (Env_toA (T,F,(ZEROS (10)),0));
     (* (Env_toP (Mac (ZEROS 8))) *)
     (Env_toP (Corrupt)); 
     (Env_toP (Mac (ZEROS 20)));
     (Env_toA (T,F,(ZEROS (10)),0));
     (Env_toA (F,T,(ZEROS (10)),0));
     (Env_toA (F,F,(ZEROS (10)),3));
     (Env_toA (T,F,(ZEROS (10)),0))
    ]
  ``;
*)

val _ = 
 type_abbrev
  ("real_game_state", 
   ``: (('c,'r) mitb_state # bool) # num list ``);
(*                           ^ corruption status *)

val _ = type_abbrev ("sim_plus_ideal_game_state", 
   ``: (bits # bool) #('c,'r)  mitb_state ``);
(*               ^ corruption status *)

val _ = type_abbrev ("ideal_game_state", ``: (bits # bool) ``);
(*               ^ corruption status *)

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

(* We instantiate the real world with the protocol using the MITB, given
* parameters and the compression function *)
(* TODO Does not work I can't see why *)

val REAL_DUMMY_ADV_def = 
  Define `
 REAL_DUMMY_ADV  _ (m : ('n,'r) real_message)
=
    (DUMMY_ADV 0 m)`;

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
      


(* warmup: show that corruption status is preserved *)
(* This invariant states that the corruption status in the real game and the
* ideal game always correspond
*)
val STATE_INVARIANT_COR_def = 
    Define `
    STATE_INVARIANT_COR ((cntl,pmem,vmem),cor_r) ((k,cor_f),(cor_s,cntl_s,vm_s,m_s)) =
    ((cor_r = cor_f) /\ (cor_f = cor_s))
    `;

(* This invariant states that if the real game is corrupted, the cntl-state of
*  the MITB simulated by SIM and the actual MITB in the real game correspond.
*)
val STATE_INVARIANT_CNTL_def =
    Define `
    STATE_INVARIANT_CNTL ((cntl,pmem,vmem),cor_r)
    ((k,cor_f),(cor_s,cntl_s,vm_s,m_s))=
    cor_r ==> (cntl = cntl_s)
    `;

(* The complete invariant (which will grow in the future *)
val STATE_INVARIANT_def = 
  Define `
  STATE_INVARIANT (state_r) (state_f) =
     (STATE_INVARIANT_COR (state_r) (state_f))
     /\
     (STATE_INVARIANT_CNTL (state_r) (state_f))
        `;

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




(* val lemma_proto_mac_closed_form = prove ( *)
(* `` *)
(*     ROUTE (PROTO (MITB_STEP f)) DUMMY_ADV *) 
(*     ((((state,pmem,vmem),F),0),EnvtoP (Mac m)) = *)
(*     let vmem = *) 
(*       ( *)
(*       (ABSORB_WORDLIST f pmem) (*pmem is initial state *) *)
(*       (PADDED_WORDLIST_FROM_BITS m) *)
(*     in *)
(* ((((Ready,pmem, vmem ),F),0),((dimindex(:'n)-1 >< 0) vmem)) *)
(*     ``, *)
(*     cheat *)
(*     ); *)


val rws =
  [EXEC_STEP_def,LET_THM,ENV_WRAPPER_def,ROUTE_THREE_def,ROUTE_def,
   SIM_def,ADV_WRAPPER_def,DUMMY_ADV_def,PROTO_def,MITB_STEP_def,
   MITB_def,MITB_FUN_def,PROTO_WRAPPER_def,STATE_INVARIANT_def,FMAC_def,
   STATE_INVARIANT_COR_def, STATE_INVARIANT_CNTL_def]

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

(* We show that, given that the complete invariant holds, the corruption part of
* the invariant holds. 
* *)
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

val _ = export_theory();
