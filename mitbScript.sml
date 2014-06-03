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
val Zeros_def =
 Define
  `(Zeros 0 = [])
   /\
   (Zeros(SUC n) = F :: Zeros n)`;

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
        *   (TAKE len blk ++ [T] ++ Zeros(r-len-2) ++ [T] ++ Zeros c)) *)
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
        (* f(vmem XOR (TAKE len blk ++ [T] ++ Zeros c)))  *)
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
     * f(vmem XOR (Zeros(r-1) ++ [T] ++ Zeros c)))) *)
     f(vmem ?? ( (0x1w: 'r word) @@ (ZERO: 'c word) ))
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


(*
Run MITB
TODO Document
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

(* val protocol_correctness = prove ( *)
(* `` *)

(* ``, *)

(* ); *)


(* Sanity test *)
(* RESTR_EVAL_CONV not found... where does it belong too? *)
(* val RUN = RESTR_EVAL_CONV [``Zeros``]; *)

(*
RUN ``EXEC_LIST (PROTO (MITB_STEP (r,c,n) (\m.m)) (r,c,n))
     DUMMY_ADV  
   (((Ready,(Zeros (r+c)),(Zeros (r+c))),F),[]) [(Env_toA (T,F,(Zeros (r)),0))]
  ``;

RUN ``EXEC_LIST (PROTO (MITB_STEP (r,c,n) (\m.m)) (r,c,n))
     DUMMY_ADV  
   (((Ready,(Zeros (r+c)),(Zeros (r+c))),F),[]) 
   [(Env_toA (T,F,(Zeros (r)),0));
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

(* Sanity test *)
(*
RUN ``EXEC_LIST 
     (FMAC (10,c,n) hash)
     (SIM (10,c,n))
     (((Zeros (10+c)),F),(F,Ready,(Zeros r),[])) 
     [
     (Env_toA (T,F,(Zeros (10)),0));
     (Env_toP (Mac (Zeros 20)));
     (Env_toP (Corrupt)); 
     (Env_toP (Mac (Zeros 20)));
     (Env_toA (T,F,(Zeros (10)),0));
     (Env_toA (F,T,(Zeros (10)),0));
     (Env_toA (F,F,(Zeros (10)),3));
     (Env_toA (T,F,(Zeros (10)),0))
    ]
  ``;

(* compare with real MITB *)
RUN `` EXEC_LIST 
     (PROTO (MITB_STEP (10,c,n) f) (10,c,n))
     DUMMY_ADV
     (((Ready,(Zeros (10+c)),(Zeros (10+c))),F),[]) 
     [
     (Env_toA (T,F,(Zeros (10)),0));
     (* (Env_toP (Mac (Zeros 8))) *)
     (Env_toP (Corrupt)); 
     (Env_toP (Mac (Zeros 20)));
     (Env_toA (T,F,(Zeros (10)),0));
     (Env_toA (F,T,(Zeros (10)),0));
     (Env_toA (F,F,(Zeros (10)),3));
     (Env_toA (T,F,(Zeros (10)),0))
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
    ((cor_r ==> (cntl = cntl_s))
     /\
     (~cor_r ==> (cntl = Ready) /\ (cntl_s = Ready ))
     )
    (*TODO Do we need more? We could assert that for cor_r=F,
    * the MITB is alway in ready. But I wouldn't think we need this *)
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
   STATE_INVARIANT_COR_def, STATE_INVARIANT_CNTL_def
                                        ]

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

val word_bit_BITS_TO_WORD = store_thm("word_bit_BITS_TO_WORD",
  ``∀ls x. x < LENGTH ls ⇒ (word_bit x ((BITS_TO_WORD ls):'a word) = x < dimindex (:'a) ∧ EL x ls)``,
  rw[BITS_TO_WORD_def] >>
  qmatch_abbrev_tac`word_bit x (word_from_bin_list l) ⇔ y` >>
  `EVERY ($> 2) l` by (
    simp[Abbr`l`,EVERY_MAP,EVERY_MEM] >> rw[] ) >>
  fs[Abbr`l`] >> simp[word_bit_word_from_bin_list] >>
  simp[EL_MAP,Abbr`y`] >> rw[])

val LENGTH_Zeros = store_thm("LENGTH_Zeros",
  ``∀n. LENGTH (Zeros n) = n``,
  Induct >> simp[Zeros_def])
val _ = export_rewrites["LENGTH_Zeros"]

val EL_Zeros = store_thm("EL_Zeros",
  ``∀n m. m < n ⇒ (EL m (Zeros n) = F)``,
  Induct >> simp[Zeros_def] >> Cases >> simp[] )

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


val word_bit_concat1 = prove(
``
((FINITE 𝕌(:α)) ∧ (FINITE 𝕌(:β)) /\
(x < (dimindex(:'a) + dimindex(:'b)) /\  ~(x < dimindex(:'b) )  ))
==>
((word_bit x ( word_join (a:'a word) (b:'b word)))
= word_bit (x-dimindex(:'b)) a
)
``,
strip_tac >>
`x < dimindex(:('a+'b))` by fs [fcpTheory.index_sum]  >>
`(x -dimindex(:'b)) < dimindex(:'a)` by fsrw_tac [ARITH_ss] [] >>
rw [GSYM word_bit] >>
lrw [word_join_index] 
);

val word_bit_concat2 = prove(
``
((FINITE 𝕌(:α)) ∧ (FINITE 𝕌(:β)) /\
(x < dimindex(:'b)))
==>
((word_bit x ( word_join (a:'a word) (b:'b word)))
= word_bit x b
)
``,
strip_tac >>
`x < dimindex(:'a) + dimindex(:'b)` by fsrw_tac [ARITH_ss] [] >>
`x < dimindex(:('a+'b))` by pop_assum (fn tm =>  fs
[fcpTheory.index_sum,tm])  >>
rw [GSYM word_bit] >>
rw [word_join_index] 
);

val BITS_TO_WORD_join = prove (
``
  (dimindex(:'a) = (LENGTH  a))
  /\
  (dimindex(:'b) = (LENGTH  b))
  ==> 
 ((BITS_TO_WORD (b++a)):('a+'b) word = 
   (word_join ((BITS_TO_WORD a):'a word) ((BITS_TO_WORD b):'b word)))
``,
  simp[GSYM WORD_EQ] >>
  rw [] >>
  Cases_on `x<dimindex(:'b)` >> 
  (* TODO Have to find out what this means and then get rid of the cheat *)
  `(FINITE 𝕌(:α)) ∧ (FINITE 𝕌(:β))` by cheat  >>
  fs [fcpTheory.index_sum] >> 
  rfs [] >>
  rw [word_bit_concat1, word_bit_concat2 ] >> 
  rw [ADD_COMM, word_bit_BITS_TO_WORD,EL_APPEND1,EL_APPEND2] >> 
  rw [fcpTheory.index_sum] >> 
  `x - (LENGTH b) < LENGTH a` by simp [] >>
  simp [ word_bit_BITS_TO_WORD,EL_APPEND1,EL_APPEND2] 
);



(* val BITS_TO_WORD_concat = prove ( *)
(* `` *)
(*   (dimindex(:'a) = (LENGTH  a)) *)
(*   /\ *)
(*   (dimindex(:'b) = (LENGTH  b)) *)
(*   /\ *)
(*   (dimindex(:'c) = (LENGTH  a)+(LENGTH  b)) *)
(*   ==> *) 
(*  ((BITS_TO_WORD (b++a)):('c) word = *) 
(*    ((BITS_TO_WORD a):'a word)@@ ((BITS_TO_WORD b):'b word)) *)
(* ``, *)
(*   simp[GSYM WORD_EQ] >> *)
(*   rw [] >> *)
(*   Cases_on `x<dimindex(:'b)` >> *) 
(*   `(FINITE 𝕌(:α)) ∧ (FINITE 𝕌(:β))` by cheat  >> *)
(*   fs [fcpTheory.index_sum] >> *) 
(*   rfs [word_concat_def ] >> *)
(*   rw [WORD_w2w_EXTRACT, fcpTheory.index_sum ] *) 
(*   (1* PUH *1) *)
(*   rw [word_bit_concat1, word_bit_concat2 ] >> *) 
(*   rw [ADD_COMM, word_bit_BITS_TO_WORD,EL_APPEND1,EL_APPEND2] >> *) 
(*   (1* PUH *1) *)
(*   rw [ INST_TYPE [gamma |-> Type `:('a+'b) word`] word_concat_def] >> *)
(*   rw [BITS_TO_WORD_join] >> *) 
(* ); *)


val word_bit_or  = prove (
`` (x < dimindex(:'a)) ==>
((a:'a word || b) ' x = a ' x \/ b ' x) ``,
rw [word_or_def] >>
simp [fcpTheory.FCP_BETA] 
);

val word_bit_T  = prove (
`` 
(b < dimindex(:'a) ) ==>
((01w:'a word) ' b = (b=0))``,
rw [word_index] 
);

val padding_block_full = prove (
``
(dimindex(:'r)>1)
==>
(( BITS_TO_WORD ( T::( Zeros (dimindex(:'r)-1) ++ [T] ))): ('r+1) word
 = (INT_MINw || 1w):('r+1) word 
 )
``,
strip_tac >>
qmatch_abbrev_tac`( BITS_TO_WORD (T::rest))  = w` >>
`LENGTH [T]=1` by rw[] >>
`LENGTH rest=dimindex(:'r)` by simp[Abbr `rest`] >>
simp_tac pure_ss [Once (CONS_APPEND)] >> 
rw [BITS_TO_WORD_join] >>
`dimindex(:'r) > 0 ` by simp [] >> 
POP_ASSUM (fn thm => rw [Abbr `rest`, int_min_lemma, thm] ) >>
rw [BITS_TO_WORD_def]  >> 
simp[GSYM WORD_EQ, GSYM word_bit] >>
strip_tac >>
  `FINITE 𝕌(:'r+1) ` by cheat  >>
  `FINITE 𝕌(:'r) ` by cheat  >>
`dimindex(:'r+1) = dimindex(:'r) + 1 ` by fs [fcpTheory.index_sum] >> 
DISCH_TAC >> 
rw [word_join_index, word_L ]  >>
qunabbrev_tac `w` >>
qpat_assum `x < dimindex(:'r+1)` 
  (fn thm => ( assume_tac (MATCH_MP word_L thm))
   >> assume_tac thm) >>
rw [word_bit_or]  
>- (* x=0 *)
(
  `x=0` by simp []  >>
  rw [word_bit_T]
)
>>
 `x < dimindex(:'r+1)` by simp [] >>
  rw [word_bit_T] >>
 `x-1 < dimindex(:'r)` by simp [] >>
  rw [word_L] >>
  simp [] 
);

(* val alt_padding = prove ( *)
(* `` *)
(* (dimindex(:'r)>2) *)
(* ==> *)
(* (( BITS_TO_WORD (m ++ (T::( Zeros (dimindex(:'r)-2 - (LENGTH m)) ++ [T] )))): ('r) word *)
(*  = (INT_MINw || 1w):('r+1) word *) 
(*  ) *)
(* ``, *)



val rws_macking =
  [
  LET_THM,
  MITB_STEP_def, MITB_def,MITB_FUN_def,RunMITB_def,
  PROCESS_MESSAGE_LIST_def, (Once Split_def)
                                        ]

val rws_hash =
  [
  LET_THM,
  Hash_def, Output_def, Absorb_def, SplittoWords_def,
  Pad_def, Zeros_def, PadZeros_def,
  (Once Split_def) ]

val a_b_mod_a_lemma = prove (
``( 0 < a) ==> ((a + b) MOD a = b MOD a)``,
rw [] >>
first_assum (ASSUME_TAC o SYM o (Q.SPECL [`a`,`b`]) o (MATCH_MP
MOD_PLUS)) >>
first_assum (ASSUME_TAC o CONJUNCT2 o (MATCH_MP DIVMOD_ID)) >>
rw []);



val mac_message_lemma = prove (
``! r m pmem vmem. 
   (
   (r = dimindex(:'r))
   /\
   (GoodParameters (dimindex(:'r),dimindex(:'c),dimindex(:'n)))
   /\
   (((cntl_t,pmem_t,vmem_t),(rdy_t,dig_t)) =
        RunMITB 
          (MITB_STEP: ('c,'n,'r)mitbstepfunction  f)
          (Absorbing,pmem,vmem)
         (PROCESS_MESSAGE_LIST
              (Split (dimindex(:'r)) m)))
        )
    ==>
    (( cntl_t=Ready)
    /\
    ( pmem_t = pmem )
    /\
    ( vmem_t = (Absorb f vmem 
       (SplittoWords (Pad ( dimindex(:'r) ) m))
       )))
    ``,
   recInduct(Split_ind) >> 
   strip_tac >> strip_tac >>
   Cases_on `(LENGTH msg) <= dimindex(:'r)` 
   >-
   (
    rw [GoodParameters_def,(Once Split_def)] >>
    `Split (dimindex(:'r)) msg = [msg]`
      by (rw [(Once Split_def)]) >>
    Cases_on `LENGTH msg = dimindex(:'r)` >>
    Cases_on `LENGTH msg = dimindex(:'r) - 1` >>
    rw rws_macking >>
    lfs [] >>
    fs rws_macking >>
    `~(dimindex (:'r) <= 1 + (dimindex (:'r)-2))` by (simp []) >>
    TRY (`LENGTH msg <= dimindex(:'r)-2` by decide_tac ) >>
    lfs (rws @ rws_macking) >>
    (* vmem cases .. will need external lemma *)
    fs rws_hash >>
    lfs [] 
    >- (* LENGTH msg = dimindex(:'r) *)
    (
      `((dimindex(:'r) - (dimindex(:'r)+2) MOD dimindex(:'r) MOD
      dimindex(:'r)) = dimindex(:'r) - 2 )` by simp
      [a_b_mod_a_lemma] >>
      fs [] >>
      Q.ISPEC_THEN `msg:bits` (ASSUME_TAC) TAKE_LENGTH_APPEND >>
      Q.ISPEC_THEN `msg:bits` (ASSUME_TAC) DROP_LENGTH_APPEND >>
      qpat_assum `LENGTH msg = X` (fn tm => fs [tm] >> assume_tac tm ) >> 
      asm_simp_tac std_ss [GSYM APPEND_ASSOC]  >>
      rw [Once (Split_def),LengthZeros,padding_block_full] >>
      lfs [] >>
      (* CURRENT POS *)
      cheat
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

(* We show that, given that the complete invariant holds, the control part of
                                      * the invariant holds.  *)
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
      >> (*cor_f F *)
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

      
val helper_theorem = prove(
``( ! a . let b = f a in p b )
 ==>
 (! a . ? b. (b = f a) /\ p b)``,
 rw [] >>
 POP_ASSUM (ASSUME_TAC o EVAL_RULE o SPEC ``a``  ) >>
 rw [] 
      );

val helper_theorem_two = prove(
``(! a . ? b. (b = f a) /\ p b)
 ==>
( ! a . let b = f a in p b )
 ``,
 simp [] 
      );


val _ = export_theory();
