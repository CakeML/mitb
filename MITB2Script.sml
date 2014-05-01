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

open HolKernel Parse boolLib bossLib
     listTheory rich_listTheory
     arithmeticTheory Arith numLib computeLib;
open UCcomTheory
open lcsymtacs

(**********************************************************************)
(* Start new theory MITB                                              *)
(**********************************************************************)

val _ = new_theory "MITB2";

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
val _ = type_abbrev("bits", ``:bool list``);

(*
XOR - pads with zeros if arguments have unequal length
(Identical to Xor in sponge.ml)
*)

(* Make XOR an infix then define it *)
val _ = set_fixity "XOR" (Infixr 695); 
val XOR_def =
 Define
  `($XOR [] bl = bl)
   /\
   ($XOR bl [] = bl)
   /\
   ($XOR (b1::bl1) (b2::bl2) = (~(b1=b2)) :: $XOR bl1 bl2)`;

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
           | Input of bits => num`;

(*
Type abbreviation for MITB states
*)
val _ = 
 type_abbrev
  ("mitb_state", 
   ``:control # (*b*)bits # (*b*)bits``);
(*              permanent   volatile      *)

(*
Type abbreviation for MITB inputs
*)
val _ =
 type_abbrev
  ("mitb_inp",
   ``:bool # bool # bits # num``);
(*    skip   move  block  size     *)
(*
Type abbreviation for MITB outputs
*)
val _ =
 type_abbrev
  ("mitb_out",
   ``:bool # bits``);


(*
Type abbreviation for MITB ports (inputs and outputs)
*)
val _ =
 type_abbrev
  ("mitb_port",
   ``:bits # bits # bits # num # bits # bits``);
(*    skip   move  block  size  reasy  digest    *)
(*
Extract components of an MITB state
*)
val cntlOf_def =
 Define
  `cntlOf((cntl,pmem,vmem):mitb_state) = cntl`;

val pmemOf_def =
 Define
  `pmemOf((cntl,pmem,vmem):mitb_state) = pmem`;

val vmemOf_def =
 Define
  `vmemOf((cntl,pmem,vmem):mitb_state) = vmem`;

(*
Type abbreviation for MITB device
*)
val _ = 
 type_abbrev
  ("mitb", 
   ``:(num # num # num)           (* bitrate/capacity/digest *)
      -> ((*b*)bits -> (*b*)bits) (* permutation             *)
      -> mitb_state -> command -> mitb_state``);

(*
List of zeros (represented as Fs) of a given size
(Identical to Zeros in sponge.ml)
*)
val ZEROS_def =
 Define
  `(ZEROS 0 = [])
   /\
   (ZEROS(SUC n) = F :: ZEROS n)`;

(*
Defines one step of MITB (r,c,n) with permutation function f
MITB_FUN (r,c,n) f : mitb_state -> inputs -> mitb_state
*)

val MITB_FUN_def =
 Define
  `(* Skip : {Ready -> Ready} + {Absorbing -> Absorbing} *)
   (MITB_FUN (r,c,n) f (cntl,pmem,vmem) Skip
    = (cntl,pmem,vmem))
   /\
   (* Input : Ready -> Ready *)
   (MITB_FUN (r,c,n) f (Ready,pmem,vmem) (Input key len)
    = (Ready,f(key++(ZEROS c)),ZEROS(r+c)))
   /\
   (* Move: {Ready -> Absorbing} *)
   (MITB_FUN (r,c,n) f (Ready,pmem,vmem) Move
    = (Absorbing,pmem,pmem))
   /\
   (* Move: {Absorbing -> Ready} *)
   (MITB_FUN (r,c,n) f (Absorbing,pmem,vmem) Move
    = (Ready,pmem,ZEROS(r+c)))
   /\
   (* Input: Absorbing -> {Absorbing,AbsorbEnd,Ready} *)
   (MITB_FUN (r,c,n) f (Absorbing,pmem,vmem) (Input blk len)
    = if len <= r-2 then (* More than one bit too small *)
       (Ready,
        pmem,
        f(vmem 
          XOR 
          (TAKE len blk ++ [T] ++ ZEROS(r-len-2) ++ [T] ++ ZEROS c))) else
      if len = r-1 then  (* Exactly one-bit too small *)
       (AbsorbEnd,
        pmem,
        f(vmem XOR (TAKE len blk ++ [T] ++ ZEROS c))) else  (* Full block *)
      (Absorbing,pmem,f(vmem XOR (blk ++ ZEROS c))))
   /\
   (* Move: AbsorbEnd -> Ready} *)
   (MITB_FUN (r,c,n) f (AbsorbEnd,pmem,vmem) Move
    = (Ready, pmem, ZEROS(r+c)))
   /\
   (* Input: AbsorbEnd -> Ready} *)
   (MITB_FUN (r,c,n) f (AbsorbEnd,pmem,vmem) (Input blk len)
    = (Ready, pmem, f(vmem XOR (ZEROS(r-1) ++ [T] ++ ZEROS c))))
    `;

(*
Execute one step of MITB_FUN, except in the case when len = r-r then take
two steps so as to move through AbsorbEnd to apply the permutation f
twice.

StepMITB (r,c,n) : (bits -> bits) -> mitb_state -> command -> mitb_state
                   permutation      initial state       
*)
val StepMITB_def =
 Define
  `StepMITB (r,c,n) f s i =
    if (cntlOf s = AbsorbEnd) 
     then MITB_FUN (r,c,n) f (MITB_FUN (r,c,n) f s i) i
     else MITB_FUN (r,c,n) f s i`;

(*
Run MITB

RunMITB (r,c,n) : (bits -> bits) -> mitb_state -> command list -> mitb_state
                  permutation     initial state     commands     final state
*)
val RunMITB_def =
 Define
  `(RunMITB (r,c,n) f s [] =  s)
   /\
   (RunMITB (r,c,n) f s (i :: il) =
     RunMITB (r,c,n) f (StepMITB (r,c,n) f s i) il)`;

(*
Run SHA-3 instantiation of MITB:

SHA3 : (bits -> bits) -> mitb_state -> command list -> mitb_state
       permutation     initial state     commands      final state
*)
val SHA3_def =
 Define
  `SHA3 = RunMITB(1152,448,224)`;

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
Extract digest from a state
*)
val Digest_def =
 Define
  `(Digest n (Ready,pmem,vmem) = TAKE n vmem)
   /\
   (Digest n (Absorbing,pmem,vmem) = ZEROS n)
   /\
   (Digest n (AbsorbEnd,pmem,vmem) = ZEROS n)`;

(*
MITBHash a message by running MITB on a key on length n (224)
*)
val MITB_MAC_def =
 Define
  `MITB_MAC (r,c,n) f key msg =
    let (cntl,pmem,vmem) =
     RunMITB (r,c,n) f (Ready, ZEROS(r+c), ZEROS(r+c)) 
      ([Input key r;Move]
         ++ MAP (\blk. Input blk (LENGTH blk)) (SplitMessage r msg))
    in
     if cntl = Ready then (TAKE n vmem) else ZEROS n`;

(* 

A signal - type abbreviations sig, nsig for signals defined below -
represent sequences of bits (sig) of numbers (nsig).

If s : sig then s(t) is the value of the signal s at time t
(t=0 is the startup time). For more details of this modelling style
see: http://www.cl.cam.ac.uk/~mjcg/WhyHOL.pdf.
*)

(*
val _ = type_abbrev("sig",  ``: num -> bool list``);
val _ = type_abbrev("nsig", ``: num -> num``);
*)

(*
Predicate to test for well-formed Keccak parameters
*)
val GoodParameters_def =
 Define
  `GoodParameters (r,c,n)
    = 2 < r /\ 0 < c /\ n <= r`;

(*
Width sig n species sig is n-bits wide
*)
val Width_def =
 Define
  `Width sig n = !t. LENGTH(sig t) = n`;

(*

MITB_IMP key (r,c,n) f is a (still somewhat abstract) model of an
MITB device initialised with key; it has type:

  ((num->control)#sig#sig) -> sig#sig#sig#nsig#sig#sig -> bool
 . |--control---|  |   |  .  . |   |    |   | . |   |   .
 .               pmem  |  .  .skip |    |   | .ready|   .
 .                   vmem .  .   idle   |   | .  digest .
 .                        .  .       block  | .         .
 .                        .  .            size.         .
 .                        .  .                .         .
 .                        .  .                .         .
 |---------states---------|  |-----inputs-----|-outputs-|

White box view:

 - ready_out shows control state

 - digest_out is bottom n bits of volatile memory (vmem)

                         |------------------------------------|
                         |           |----------------------| |
                         |           |           |--------| | |
                         |           |           |        | | |
                        \|/         \|/         \|/       | | |
                   |-----------|-----------|-----------|  | | |
                   |   cntl    |  pmem     |  vmem     |  | | |
                   |   (reg)   |  (reg)    |  (reg)    |  | | |
                   |-----------|-----------|-----------|  | | |
                         |           |           |        | | |
                 control /       r+c /       r+c /        | | |
                         |           |           |        | | |
                cntl_sig |  pmem_sig |  vmem_sig |        | | |
                         |           |           |        | | |
                        \|/         \|/         \|/       | | |
                   |-----------------------------------|  | | |
              1    |                                   |  | | | 1
   skip_inp ---/-->|                                   |--|-|-|--/--> ready_out
                   |                                   |  | | |
              1    |                                   |  | | |
   move_inp ---/-->|                                   |  | | |
                   | MITB_CONTROL_LOGIC key (r,c,n) f  |  | | |
              r    |    (combinational logic)          |  | | |
   block_inp --/-->|                                   |  | | |
                   |                                   |  | | |
            num    |                                   |  | | | n
   size_inp ---/-->|                                   |--|-|-|--/--> digest_out
                   |                                   |  | | |
                   |-----------------------------------|  | | |
                         |           |           |        | | |
                 control /       r+c /       r+c /        | | |
                         |           |           |        | | |
                cntl_nxt |  pmem_nxt |  vmem_nxt |        | | |
                         |           |           |        | | |
                         |           |           |--------| | |
                         |           |----------------------| |
                         |------------------------------------|


The main interaction protocols (transactions) are:

 Set key:  if ready_out then hold skip_inp and move_inp F for 
 (time t)  one cycle and f(block_inp t ++ ZEROS c) will be stored 
           in pmem. Keeping skip_inp T in subsequent cycles
           freezes the state.

 Hash msg: if ready_out then hold skip_inp F and move_inp T 
 (time t)  for one cycle, then hold both skip_inp and move_inp F 
           until ready_out goes to T again. The message is absorbed 
           starting at t+1, data inputs (message block and size) is
           read on successive cycles until the last block is read 
           (indicated by its length being less than r). Keeping 
           skip_inp T in subsequent cycles freezes the state so 
           the digest can be read.

The two control inputs work as follows:

 skip_inp: holding T prevents the state from changing;

 move_imp: driving T always causes a transition 
           from Ready to Absorbing:
            - in Ready it starts a hash transaction
            - in Absorbing it resets vmem and returns to Ready

The data inputs block_inp and size_inp are only read if skip_in is F
and move_inp is T. When this is the case:

 - if Ready at time t, then f((block_in t)++(ZEROS c)) is written into
   pmem, ZEROS (r + c) written into vmem, the input size_inp is
   ignored and the state stays in Ready;

 - if in Absorbing, then both block_inp and size_inp are read and what
   happens depends on whether the block size is r, one less than r or
   two or more less than r (the next state could be Absorbing or Ready
   - details in MITB_FUN_def).
        
*)

(*
Unit-delay model sequential of a register that powers up holding
init_state.
*)

val REGISTER_def =
 Define
  `REGISTER init_state (inp,out) =
   (out 0 = init_state) /\ !t. out(t+1) = inp t`;

(*
Functional version as in the paper
*)
val MITB_def =
 Define
  `MITB (r,c,n:num) f ((skip,move,block,size), (cntl,pmem,vmem)) =
    MITB_FUN (r,c,n) f 
     (cntl, pmem, vmem) 
     (if skip = [T]
       then Skip else
      if move = [T]
       then Move
       else Input block size)`;

(*
Control logic - currently combinational but may need to be retimed to
be sequential.
*)
val MITB_CONTROL_LOGIC_def =
 Define
  `MITB_CONTROL_LOGIC
    (r,c,n) f 
    (cntl_sig,pmem_sig,vmem_sig,skip_inp,move_inp,block_inp,size_inp,
     cntl_nxt,pmem_nxt,vmem_nxt,ready_out,digest_out) =
    (!t.
      (cntl_nxt t, pmem_nxt t, vmem_nxt t) =
       MITB (r,c,n) f 
        ((skip_inp t,move_inp t,block_inp t,size_inp t), 
         (cntl_sig t,pmem_sig t,vmem_sig t)))
    /\
    (!t. ready_out t = [cntl_sig t = Ready])
    /\
    (!t. digest_out t = 
          if cntl_sig t = Ready then TAKE n (vmem_sig t) else ZEROS n)`;

(*
Some temporary experiments (to be deleted)

  (SIMP_RULE std_ss 
   [REGISTER_def,Width_def,GoodParameters_def,MITB_CONTROL_LOGIC_def,
   FORALL_PROD]
   MITB_IMP_def)

Q.SPECL
 [`cntl_of o sigma`,`pmem_of o sigma`,`vmem_of o sigma`,
  `skip_of o sigma`,`move_of o sigma`,`block_of o sigma`,
  `size_of o sigma`,`ready_of o sigma`,`digest_of n o sigma`]

SIMP_RULE std_ss [ZipSigs_def,PULL_EXISTS]
 (Q.SPEC `psi o ZipSigs`
  (SIMP_RULE std_ss 
   [REGISTER_def,Width_def,GoodParameters_def,MITB_CONTROL_LOGIC_def,
   MITB_IMP_def,FORALL_PROD]
   (Q.ISPEC `MITB_IMP key (r,c,n) f` Models_def)));

val it =
|- MITB_IMP key (r,c,n) f |= psi o ZipSigs <=>
   !control_sig pmem_sig vmem_sig skip_inp move_inp block_inp size_inp 
    ready_out digest_out cntl_nxt
      pmem_nxt vmem_nxt.
     (2 < r /\ 0 < c /\ n <= r) /\ 
     (!s. LENGTH (f s) = LENGTH s) /\
     (LENGTH key = r) /\ 
     (!t. LENGTH (pmem_sig t) = r + c) /\
     (!t. LENGTH (vmem_sig t) = r + c) /\
     (!t. LENGTH (pmem_nxt t) = r + c) /\
     (!t. LENGTH (vmem_nxt t) = r + c) /\ 
     (!t. LENGTH (skip_inp t) = 1) /\
     (!t. LENGTH (move_inp t) = 1) /\ 
     (!t. LENGTH (block_inp t) = r) /\
     (!t. size_inp t <= r) /\ 
     (!t. LENGTH (ready_out t) = 1) /\
     (!t. LENGTH (digest_out t) = n) /\
     (control_sig 0 = Ready) /\ 
     (!t. control_sig (t + 1) = cntl_nxt t) /\
     (pmem_sig 0 = f (key ++ ZEROS c)) /\ 
     (!t. pmem_sig (t + 1) = pmem_nxt t) /\
     (vmem_sig 0 = ZEROS (r + c)) /\ 
     (!t. vmem_sig (t + 1) = vmem_nxt t) /\
     (!t.
        (cntl_nxt t,pmem_nxt t,vmem_nxt t) =
         MITB (r,c,n) f
          ((skip_inp t,move_inp t,block_inp t,size_inp t),control_sig t,pmem_sig t,vmem_sig t)) /\ 
     (!t. ready_out t = [control_sig t = Ready]) /\
     (!t. digest_out t = if control_sig t = Ready then TAKE n (vmem_sig t) else ZEROS n) 
     ==>
     psi(\t. ((skip_inp t,move_inp t,block_inp t,size_inp t),control_sig t,pmem_sig t,vmem_sig t))

     MITB_IMP key (r,c,n) f |= phi <=>
     !cntl_sig pmem_sig vmem_sig 
      skip_inp move_inp block_inp size_inp ready_out digest_out.
       (?cntl_nxt pmem_nxt vmem_nxt.
          (2 < r /\ 0 < c /\ n <= r) /\ (!s. LENGTH (f s) = LENGTH s) /\
          (LENGTH key = r) /\ (!t. LENGTH (pmem_sig t) = r + c) /\
          (!t. LENGTH (vmem_sig t) = r + c) /\
          (!t. LENGTH (pmem_nxt t) = r + c) /\
          (!t. LENGTH (vmem_nxt t) = r + c) /\
          (!t. LENGTH (skip_inp t) = 1) /\ (!t. LENGTH (move_inp t) = 1) /\
          (!t. LENGTH (block_inp t) = r) /\ (!t. size_inp t <= r) /\
          (!t. LENGTH (ready_out t) = 1) /\ (!t. LENGTH (digest_out t) = n) /\
          ((cntl_sig 0 = Ready) /\ !t. cntl_sig (t + 1) = cntl_nxt t) /\
          ((pmem_sig 0 = f (key ++ ZEROS c)) /\
           !t. pmem_sig(t + 1) = pmem_nxt t) /\
          ((vmem_sig 0 = ZEROS (r + c)) /\ !t. vmem_sig (t + 1) = vmem_nxt t) /\
          (!t.
             (cntl_nxt t,pmem_nxt t,vmem_nxt t) =
             MITB (r,c,n) f
               ((skip_inp t,move_inp t,block_inp t,size_inp t),cntl_sig t,pmem_sig t,
                vmem_sig t)) /\ (!t. ready_out t = [cntl_sig t = Ready]) /\
          (!t.
             digest_out t =
             if cntl_sig t = Ready then TAKE n (vmem_sig t) else ZEROS n))
       ==>
       phi ((cntl_sig,pmem_sig,vmem_sig),
            (skip_inp,move_inp,block_inp,size_inp,ready_out,digest_out))



*)

(*
Schematic capture in HOL using the classical ?-/\ style
(predicates representing modules are joined using conjunction and
internal wires hidded using existential quantification - see:
http://www.cl.cam.ac.uk/~mjcg/WhyHOL.pdf)
*)
val MITB_IMP_def =
 Define
  `MITB_IMP key (r,c,n) f (cntl_sig,pmem_sig,vmem_sig)
    (skip_inp,move_inp,block_inp,size_inp,ready_out,digest_out) =
    ?cntl_nxt pmem_nxt vmem_nxt.
    (* ======== bus width specifications ======== *)
      GoodParameters(r,c,n)
      /\ 
      (!s. LENGTH(f s) = LENGTH s)
      /\
      (LENGTH key = r)
      /\
      Width pmem_sig (r+c)
      /\
      Width vmem_sig (r+c)
      /\
      Width pmem_nxt (r+c)
      /\
      Width vmem_nxt (r+c)
      /\
      Width skip_inp 1 
      /\ 
      Width move_inp 1 
      /\ 
      Width block_inp r 
      /\
      (!t. size_inp t <= r)
      /\ 
      Width ready_out 1
      /\ 
      Width digest_out n
      /\
    (* ==== netlist connection specification ==== *)
      REGISTER Ready (cntl_nxt,cntl_sig)
      /\
      REGISTER (f(key ++ ZEROS c)) (pmem_nxt,pmem_sig)
      /\
      REGISTER (ZEROS(r + c)) (vmem_nxt,vmem_sig)
      /\
      MITB_CONTROL_LOGIC
       (r,c,n) f
       (cntl_sig,pmem_sig,vmem_sig,skip_inp,move_inp,block_inp,size_inp,
        cntl_nxt,pmem_nxt,vmem_nxt,ready_out,digest_out)`;

(*
MITB_DEV is a black box version of MITB_IMP - i.e. the states are hidden
and only the inputs and outputs are visible.
*)
val MITB_DEV_def =
 Define
  `MITB_DEV key (r,c,n) f 
    (skip_inp,move_inp,block_inp,size_inp,ready_out,digest_out) =
   ?cntl_sig pmem_sig vmem_sig.
    MITB_IMP key (r,c,n) f (cntl_sig,pmem_sig,vmem_sig)
     (skip_inp,move_inp,block_inp,size_inp,ready_out,digest_out)`;

val MITB_DEV_def =
 Define
  `MITB_DEV key (r,c,n) f 
    (skip_inp,move_inp,block_inp,size_inp,ready_out,digest_out) =
   ?cntl_sig pmem_sig vmem_sig.
    MITB_IMP key (r,c,n) f (cntl_sig,pmem_sig,vmem_sig)
     (skip_inp,move_inp,block_inp,size_inp,ready_out,digest_out)`;

val _ =
 Hol_datatype
  `mac_query =
            SetKey of bits
          | Mac of bits
          | Corrupt
          `;

val _ =
 Hol_datatype
  `mac_to_adv_msg =
            WasCorrupted 
          | OracleResponse of bits
          `;

val _ =
 Hol_datatype
  `adv_to_mac_msg =
            CorruptACK 
          | OracleQuery of bits
          `;

(* State transition function for the functionality defining a perfect MAC
* device for a given Hash function
* Parameters: H (r,c,n) -- Hash function and parameters (we use only n)
* Internal state: current key K, corruption status
* Inputs are queries of type query
* Output are bitstrings
*)
val FMAC_def =
    Define
          `
          ( FMAC (r,c,n) (H:bits -> bits) (K,F) (EnvtoP (SetKey k)) =
          (
            if (LENGTH k = r) then
              ((k,F),(Proto_toEnv []))
            else
              ((K,F),(Proto_toEnv []))
              ))
          /\
          ( FMAC (r,c,n) H (K,F) (EnvtoP (Mac m)) = 
            ((K,F),(Proto_toEnv (H (K ++ m)))))
          /\
          ( FMAC (r,c,n) H (K,F) (EnvtoP (Corrupt)) = ((K,T),Proto_toA (WasCorrupted)))
          /\
          ( FMAC (r,c,n) H (K,T) (AtoP (CorruptACK)) = ((K,T),Proto_toEnv []))
          /\
              (* Adversarial interface may request Hashes with K prepended to
              * the input. This interface will be accessed by SIM, to be able to
              * emulate a MITB *)
          ( FMAC (r,c,n) H (K,T) (AtoP (OracleQuery m)) =
          ((K,T),(Proto_toA (OracleResponse (H K++m)))))
          /\
          (* When corrupted, ignore honest queries *)
          ( FMAC (r,c,n) H (K,T) (EnvtoP q) = ((K,T),Proto_toEnv []))
          `;

(* Sanity test *)
val th =
EVAL ``EXEC_LIST (FMAC (r,c,n) (\m.m)) DUMMY_ADV (((ZEROS r),F),[]) 
[Env_toP (Mac m)]``;

(* Function defining the protocol that implements FMAC using a MITB. In real
 * life, this protocol corresponds to a client library that computes hashes by
 * splitting the message and feeding it into the MITB. This is how honest users
 * are supposed to use the MITB 
 *
 * Parametric in: 
 * mitbf - step function of MITB,
 * (r,c,n) - global parameters for Sponge-construction (only r is used)
 * Inputs: 
 * s - current MITB state
 * T/F - corruption status
 * query
 * Output: bitstring
 * *)

val PROTO_def =
    Define
          `
          ( PROTO (mitbf : mitb_state # mitb_inp -> mitb_state # mitb_out) (r,c,n) (s,F) (EnvtoP (SetKey k)) =
            if (LENGTH k = r) then
              (
              let (s1,(rdy1,dig1))=mitbf (s,(T,F,(ZEROS r),0)) in
                if rdy1=F then
                  (let (s2,(rdy2,dig2)) =mitbf(s1,(F,T,(ZEROS r),0)) in
                    let (s3,(rdy3,dig3))= mitbf (s2,(F,F,k,(r:num))) in
                      ((s3,F),(Proto_toEnv [])))
                else
                    let (s2,rdy2,dig2)=mitbf(s1,(F,F,k,r)) in
                     ((s2,F),(Proto_toEnv []))
              )
            else
              ((s,F),(Proto_toEnv []))
              )
          /\
          ( PROTO mitbf (r,c,n) (s,F) (EnvtoP (Mac m)) =
          (* Bring MITB into Ready state *)
          (
           let (s0,rdy0,dig0) = mitbf (s,(T,F,(ZEROS r),0)) in
           (* make sure that MITB is in Ready state *)
             let (sr,rdyr,digr) =
              ( if (rdy0=F) then
                  (mitbf (s0,(F,T,(ZEROS r),0)))
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
                  let (si,rdyi,dgi) = mitbf (state,(F,F,blk, (LENGTH blk))) in
                    if (LENGTH blk) = r-1 then
                      (* special case: we need to add an empty block for padding *)
                      let (sl,rdyl,dgl) = mitbf (si,(F,F,(ZEROS r), 0)) in
                        sl
                    else si
                  ) sr (SplitMessage r m) in
                (* let sf = AUX_FEED_MITB mitbf (r,c,n) sr m in  *)
                  (* learn digest by skipping *)
                  let (s1,rdy1,digest) = mitbf (sf,(T,F, (ZEROS r),0)) in 
                  (* two consecutive moves to re-initialise vmem *)
                  let (s2,rdy2,dig2) = mitbf (s1,(F,T, (ZEROS r),0)) in 
                  let (s3,rdy3,dig3) = mitbf (s2,(F,T, (ZEROS r),0)) in
                    ((s3,F),(Proto_toEnv digest))
          ))
          /\
          ( PROTO mitbf (r,c,n) (s,F) (EnvtoP (Corrupt)) =
                ((s,T),(Proto_toEnv [])))
          /\
          (* Give adversary blackbox access when corrupted *)
          ( PROTO mitbf (r,c,n) (s,T) (AtoP i) =
            let (s_next,rdy:bool,dig: bits) = mitbf (s,i) in
                ((s_next,T), (Proto_toA (rdy::dig))))
          /\
          (* Ignore honest queries when corrupted *)
          ( PROTO mitbf (r,c,n) (s,T) (EnvtoP _) = ((s,T),(Proto_toEnv [])))
          /\
          (* Ignore adversarial queries when not corrupted *)
          ( PROTO mitbf (r,c,n) (s,F) (AtoP _) = ((s,F),(Proto_toA [])) )
          /\
          (* Ignore the rest TODO : get rid of this and replace with individual
          * cases.. *)
          ( PROTO mitbf (r,c,n) (s,cor) _ = ((s,cor),(Proto_toEnv [])))
                `;

(* We define a step function that behaves like MITB, but includes the output,
* too.
* It also checks the input for validity, i.e., block cannot be
* longer than r and size larger than r.
* Parametric in:
*  (r,c,n) - global parameters
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
  `MITB_STEP (r,c,n:num) f ((cntl,pmem,vmem), (skip,move,block,size)) =
  if ((LENGTH block <= r) /\ size <=r) then 
    (let (cntl_n,pmem_n,vmem_n) = MITB (r,c,n) f (([skip],[move],block,size), (cntl, pmem, vmem))
    in
      ((cntl_n,pmem_n,vmem_n),
      (
      (cntl_n = Ready),
      (if cntl_n = Ready then (TAKE n vmem) else ZEROS n))
      ))
  else (* ignore input otherwise *)
      ((cntl,pmem,vmem),
      (
      (cntl = Ready),
      (if cntl = Ready then (TAKE n vmem) else ZEROS n))
      )
    `;

(* Sanity test *)
val RUN = RESTR_EVAL_CONV [``ZEROS``];

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
(SIM (r,c,n) (T,Ready,vm,m) (EnvtoA (T,_,_,_)) = ((T,Ready,vm,m),(Adv_toEnv
(T::(vm)))))
    /\
(SIM (r,c,n) (T,Absorbing,vm,m) (EnvtoA (T,_,_,_)) =
    ((T,Absorbing,vm,m),(Adv_toEnv (F::(ZEROS n)))))
    /\
(SIM (r,c,n) (T,AbsorbEnd,vm,m) (EnvtoA (T,_,_,_)) =
((T,AbsorbEnd,vm,m),(Adv_toEnv (F::(ZEROS
n)))))
    /\
(SIM (r,c,n) (T,Ready,vm,m) (EnvtoA (F,T,_,_)) = ((T,Absorbing,vm,[]),(Adv_toEnv
(F::(ZEROS n )))))
    /\
(SIM (r,c,n) (T,Absorbing,vm,m) (EnvtoA (F,T,_,_)) = 
((T,Ready,(ZEROS (r+c)),m),(Adv_toEnv (T::(ZEROS n)))))
    /\
(SIM (r,c,n) (T,AbsorbEnd,vm,m) (EnvtoA (F,T,_,_)) = 
((T,Ready,(ZEROS (r+c)),m),(Adv_toEnv (T::(ZEROS n)))))
    /\
(SIM (r,c,n) (T,Absorbing,vm,m) (EnvtoA (F,F,inp,inp_size)) =
 if (inp_size=r) then  
  ((T,Absorbing,(ZEROS (r+c)),m++(TAKE inp_size inp)),(Adv_toEnv (F::(ZEROS n))))
 else 
   (if (inp_size=r-1) then
      ((T,AbsorbEnd,(ZEROS (r+c)),m++(TAKE inp_size inp)),(Adv_toEnv (F::(ZEROS
      n))))
    else ( if inp_size<r-1 then
      (* Send to Functionality for communication. Proceed when response is
      * received, see (MARK) *)
      ((T,Absorbing,vm,[]),(Adv_toP (OracleQuery (m++(TAKE inp_size inp)))))
           else (*if inp_size>r *)
           ARB(* CONTINUE HERE *)
    )))
    /\
(SIM (r,c,n) (T,AbsorbEnd,vm,m) (EnvtoA (F,F,inp,inp_size)) =
      ((T,AbsorbEnd,vm,[]),(Adv_toP (OracleQuery (m++(TAKE inp_size inp))))))
    /\
(* MARK *)
(SIM (r,c,n) (T,_,vm,m) (PtoA (OracleResponse hashvalue)) =
((T,Ready,hashvalue,[]),(Adv_toEnv (T::hashvalue))))
    /\
(* If FMAC was corrupted, change corruption state *)
(SIM (r,c,n) (F,cntl,vm,m) (PtoA WasCorrupted) = ((T,cntl,vm,m),(Adv_toP
(CorruptACK))))
    /\
(* Ignore other queries while not corrupted *)
(SIM (r,c,n) (F,cntl,vm,m) (EnvtoA _) = ((F,cntl,vm,m),(Adv_toEnv [])))
    /\
(* Ignore other queries *)
(SIM (r,c,n) (T,cntl,vm,m) (EnvtoA _) = ((T,cntl,vm,m),(Adv_toEnv [])))
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
   ``:mitb_state # bool ``);
(*                 ^ corruption status *)

(* We instantiate the real world with the protocol using the MITB, given
* parameters and the compression function *)
(* TODO Does not work I can't see why *)
(*
val MITB_GAME_def = 
    Define `
      MITB_GAME (r,(c:num),(n:num)) (f: bits -> bits ) 
        = 
      EXEC_STEP (PROTO (MITB_STEP (r,c,n) f) (r,c,n)) 
        DUMMY_ADV 
         `;

val ALMOST_IDEAL_GAME_def = 
    Define `
      (ALMOST_IDEAL_GAME (r,(c:num),(n:num)) (h: bits -> bits ) )
      : 
      =
      EXEC_STEP ( FMAC (r,c,n) h) (SIM (r,c,n))
      `
      *)
      
val _ = type_abbrev ("sim_plus_ideal_game_state", 
   ``: (bits # bool) # mitb_state ``);
(*               ^ corruption status *)

val _ = type_abbrev ("ideal_game_state", ``: (bits # bool) ``);
(*               ^ corruption status *)


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

val rws =
  [EXEC_STEP_def,LET_THM,ENV_WRAPPER_def,ROUTE_THREE_def,ROUTE_def,
   SIM_def,ADV_WRAPPER_def,DUMMY_ADV_def,PROTO_def,MITB_STEP_def,
   MITB_def,MITB_FUN_def,PROTO_WRAPPER_def,STATE_INVARIANT_def,FMAC_def,
   STATE_INVARIANT_COR_def]

(* We show that, given that the complete invariant holds, the corruption part of
* the invariant holds. 
* *)
val Invariant_cor = prove(
 ``! r c n f h
     (* The MITB's state in the real game *)
     (cntl:control) (pmem:bits) (vmem:bits)  (cor_r:bool)
     (* The functionality's state (cor_s is shared with Sim)*)
      k cor_f
      (* The simulator's state *)
      cor_s cntl_s vm_s m_s 
      (* The environment's query *)
      input.
        (GoodParameters (r,c,n))
        /\ 
        (STATE_INVARIANT ((cntl,pmem,vmem),cor_r)
        ((k,cor_f),(cor_s,cntl_s,vm_s,m_s)))
      ==>
      let ((((cntl_n,pmem_n,vmem_n),cor_r_n),_), out_r) =
      EXEC_STEP (PROTO (MITB_STEP (r,c,n) f) (r,c,n)) 
      DUMMY_ADV ((((cntl,pmem,vmem),cor_r),[]),input)
      in
        (
        let 
        (((k_n,cor_f_n),(cor_s_n,cntl_s_n,vm_s_n,m_s_n)),out_i) =
           EXEC_STEP ( FMAC (r,c,n) h) (SIM (r,c,n))
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
      split_all_bools_tac >>
      fsrw_tac [ARITH_ss] rws >> rw[] >>
      BasicProvers.EVERY_CASE_TAC >>
      fsrw_tac [ARITH_ss] rws >> rw[] >>
      fsrw_tac[ARITH_ss][]

      PairCases_on`a` >>
      fs[EXEC_STEP_def,LET_THM,ENV_WRAPPER_def,ROUTE_THREE_def] >>
      fs[ROUTE_def,LET_THM,SIM_def] >>
      Cases_on`cor_f`>>Cases_on`cntl_s`>>fs[SIM_def,ROUTE_def]
      BasicProvers.EVERY_CASE_TAC
      fs[FMAC_def]
      a case goes here )
    >>
     b case goes here

    (PairCases_on`a` ORELSE Cases_on`b`) >>

    (* Strip r c n f h *)
    ntac 5 strip_tac >>
    (* Case distinction over corruption status. Invariant removes six out of
     * eight cases. *)

(*
     >- (
       solution for case 1
       )
*)

     (Cases_on `cor_r`) THEN (Cases_on `cor_s`) THEN (Cases_on `cor_f`) THEN
       (REWRITE_TAC
     [STATE_INVARIANT_def, STATE_INVARIANT_COR_def, STATE_INVARIANT_CNTL_def]) THEN
     (* Case distinction on input. Two cases (Adv/Honest input) times two cases
     * from corruption state. Two cases (Adv input when uncorrupted, Honest
     * input when corrupted) are eliminated by rewriting and
     * evaluation. *)
     (Cases_on `input`)
      THENL [
      (* Case 1: Corrupted, but message from Env.
       * Can be solved right away. *)
         (Cases_on `a`) 
            THEN
              (FULL_SIMP_TAC list_ss [PROTO_def, EXEC_STEP_def,
              ENV_WRAPPER_def, DUMMY_ADV_def, ROUTE_THREE_def, ROUTE_def, PROTO_WRAPPER_def, ADV_WRAPPER_def] )
              THEN EVAL_TAC
            THEN DECIDE_TAC ,
      (* Case 2: Corrupted, message from Adv.
      *  The tuple of type mitp_input is made 
      *  explicit first. *)
           (Cases_on `b`) THEN
           (Cases_on `r'`) THEN
           (Cases_on `r''`) THEN
      (* Now we make a case distinction over the value of the skp
      *  and mov bit ..
      *)
           (Cases_on `q`) THEN

           (Cases_on `q'`) THEN
      (* TEST !As well as the length of the input and the value of
         length *)       
ALL_TAC
             ,
      (* Case 3: Uncorrupted, message from Env *)
      (* Cases distinction over input, which is a mac_query *)
            (Cases_on `a`),
      (* Case 4: Uncorrupted, message from Adv.
       *  Can be solved right away. *)
         (Cases_on `b`) 
            THEN
              (FULL_SIMP_TAC list_ss [PROTO_def, EXEC_STEP_def,
              ENV_WRAPPER_def, DUMMY_ADV_def, ROUTE_THREE_def, ROUTE_def, PROTO_WRAPPER_def, ADV_WRAPPER_def] )
              THEN EVAL_TAC
            THEN DECIDE_TAC
     ] THEN
     (* Case distinction over cntl, then we strip pmem vmem k cntl_s vm_s m_s *)
     (Cases_on `cntl`) 
     THEN
       (NTAC 3 STRIP_TAC) 
     THEN
         Cases 
     THEN (NTAC 2 STRIP_TAC)
               THEN
  (* TEST *)
  (SIMP_TAC list_ss [PROTO_def, EXEC_STEP_def, ENV_WRAPPER_def, DUMMY_ADV_def, ROUTE_THREE_def, ROUTE_def, PROTO_WRAPPER_def, ADV_WRAPPER_def])
               THEN EVAL_TAC 

           (* For queries on Adversarial interface or
           *  the honest interface, we need a case distinction.
           *  In any case we simplify *)
           (TRY (Cases_on `a`)) THEN 
             (TRY (Cases_on `b`)) );
                                
                                THEN 
             SIMP_TAC std_ss [PROTO_def, EXEC_STEP_def, ENV_WRAPPER_def, DUMMY_ADV_def, ROUTE_THREE_def, ROUTE_def, PROTO_WRAPPER_def]
                 THEN
                 (RW_TAC std_ss [] ) 
             THEN
              (* We need a case distinction over the ready state we ouput,
              * just so MITB_STEP evaluates further (for every possible cntl_n,
              * the corruption status is the same ) 
              * This part can surely be made easier....
              * *)
               (TRY (Cases_on `cntl_n`)) THEN
                 (RW_TAC std_ss [] ) ) ;

(*
val _ = export_theory();
*)
