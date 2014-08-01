(**********************************************************************)
(* Formalization of a simplified version of UC's communication model  *)
(**********************************************************************)

open HolKernel;
open Parse;
open Arith;
open boolLib;
open bossLib;
open listTheory;
open rich_listTheory;
open arithmeticTheory;
open numLib;
open computeLib;

val _ = new_theory "uccom";

(* Datatype for messages sent between protocol, environment and attacker *)
val _ =
 Hol_datatype
  `Message =
            EnvtoP of 'a
          | EnvtoA of 'b
          | PtoEnv of 'c
          | PtoA of 'd
          | AtoEnv of 'e
          | AtoP of 'f
          `;

(* To make sure the protocol can only send messages of type PtoA or PtoEnv, we
* create the following datatype. PROTO_WRAPPER below concerts it into type
* message *)
val _ =
 Hol_datatype
  `ProtoMessage =
           Proto_toEnv of 'c
          | Proto_toA of 'd
          `;

val PROTO_WRAPPER_def =
 Define
 `
    (PROTO_WRAPPER (Proto_toEnv m) = (PtoEnv m))
    /\
    (PROTO_WRAPPER (Proto_toA m) = (PtoA m))
    `;

(* Dito for Adversary *)
val _ =
 Hol_datatype
  `AdvMessage =
           Adv_toEnv of 'e
          | Adv_toP of 'f
          `;

val ADV_WRAPPER_def =
 Define
 `
    (ADV_WRAPPER (Adv_toEnv m) = (AtoEnv m))
    /\
    (ADV_WRAPPER (Adv_toP m) = (AtoP m))
    `;

(* Compute next state of the network from the perspective of the environment,
* given a message on the network addressed to the protocol or adversary.
*
* Parameters:
* p -- step function for protocol
* a -- step function for adversary
* Input:
* state_p -- current protocol state
* state_a -- current adversary state
* message to be routed
* Output:
* the adversary's and the protocols next state
* message resulting from computation *unless* input message was already adresses
* to envinronment (then ROUTE computes identity)
*)
(* ('a,'b,'c,'d,'e,'f, 'p, 'q) route_func is *)
val _ = type_abbrev ("routefunc", 
``: ('p -> ('a,'b,'c,'d,'e,'f) Message -> ('p # ('c,'d) ProtoMessage)) (* p *)
->('q -> ('a,'b,'c,'d,'e,'f) Message -> ('q # ('e,'f)AdvMessage)) (* a *)
->('p#'q) # ('a,'b,'c,'d,'e,'f) Message
->('p#'q) # ('a,'b,'c,'d,'e,'f) Message ``);

val ROUTE_def =
 Define
  `
    ((ROUTE: ('a,'b,'c,'d,'e,'f, 'p, 'q) routefunc)
     p a ((state_p,state_a),(EnvtoP m)) =
          let (state_p_n, out) = p state_p (EnvtoP m)  in
          ((state_p_n, state_a),(PROTO_WRAPPER out)))
     /\
     (ROUTE p a ((state_p,state_a),(AtoP m)) =
          let (state_p_n, out) = p state_p (AtoP m)  in
          ((state_p_n, state_a),(PROTO_WRAPPER out)))
     /\
     (ROUTE p a ((state_p,state_a),(EnvtoA m)) =
          let (state_a_n, out) = a state_a (EnvtoA m)  in
          ((state_p, state_a_n),(ADV_WRAPPER out)))
     /\
     (ROUTE p a ((state_p,state_a),(PtoA m)) =
          let (state_a_n, out) = a state_a (PtoA m)  in
          ((state_p, state_a_n),(ADV_WRAPPER out)))
     /\
     (ROUTE p a ((state_p,state_a),(PtoEnv m)) =
          ((state_p, state_a),(PtoEnv m)))
     /\
     (ROUTE p a ((state_p,state_a),(AtoEnv m)) =
          ((state_p, state_a),(AtoEnv m)))
     `;

(* Execute routing algorithm up to a depth of 3 *)
val ROUTE_THREE_def =
 Define
   ` ROUTE_THREE p a (s,m) = (ROUTE p a) (
                         (ROUTE p a) (
                          (ROUTE p a) (s,m))) `;
  (* Old def, looks nicer, but difficult to deal with in proof
 Define ` ROUTE_THREE p a  = ((ROUTE p a) o (ROUTE p a) o (ROUTE p a)) `;
   *)

val _ =
 Hol_datatype
  `EnvMessage =
           Env_toP of 'a
          | Env_toA of 'b
          `;

val ENV_WRAPPER_def =
 Define
 `
    (ENV_WRAPPER (Env_toP m) = (EnvtoP m))
    /\
    (ENV_WRAPPER (Env_toA m) = (EnvtoA m))
    `;

val _ =
 Hol_datatype
  `GameOutput =
           OutputfromP of 'c
          | OutfromA of 'e
          | RoutingError
          `;

val GAME_OUT_WRAPPER_def =
 Define
 `
    (GAME_OUT_WRAPPER (PtoEnv m) = (OutputfromP m))
    /\
    (GAME_OUT_WRAPPER (AtoEnv m) = (OutfromA m))
    /\
    (GAME_OUT_WRAPPER (_) = RoutingError)
    `;


(* Given an input from the environment, compute the out from protocol and
 * adversary to the environment. We compute the routing only up to a depth of
 * three. If this is not enough, the environment is notified of a routing
 * error.
 *)
val EXEC_STEP_def =
    Define
    `
        EXEC_STEP p a ((state_p,state_a),input) =
        let
          ((state_p_n,state_a_n),out) =
          (ROUTE_THREE : ('a,'b,'c,'d,'e,'f, 'p, 'q) routefunc)
          p a ((state_p,state_a),(ENV_WRAPPER input))
        in
              ((state_p_n,state_a_n),GAME_OUT_WRAPPER out)
    `

(* Given protocol, adversary and their respective states, compute the output
 * of a list of commands to the environment. *)
val EXEC_LIST_def =
 Define
 `(EXEC_LIST p a s [] = [] )
   /\
  (EXEC_LIST p a s (i :: il) =
     case EXEC_STEP p a (s,i) of
       (_,RoutingError)=> [RoutingError]
      |(s',out )       => out ::(EXEC_LIST p a s' il)
      )
  `;

(* Given protocol, adversary and their respective states, compute the output
 * of a list of commands to the environment. *)
val EXEC_LIST_FULL_def =
 Define
 `(EXEC_LIST_FULL p a s [] = [] )
   /\
  (EXEC_LIST_FULL p a s (i :: il) =
  let (s',out) =  EXEC_STEP p a (s,i)  in
       ((s',out)::(EXEC_LIST_FULL p a s' il)))
  `;

(* Sanity check

val TEST_PROTO_def =
  Define
  `(TEST_PROTO s (EnvtoP 1) = (s,(Proto_toA 2)))
  /\
  (TEST_PROTO s (AtoP 3) = (s,(Proto_toEnv 4)))
  /\
  (TEST_PROTO s (EnvtoP 5) = (s,(Proto_toEnv 6)))
  `;

val TEST_ADV_def =
  Define
  `TEST_ADV s (PtoA 2) = (s,(Adv_toP 3))`;

(* EVAL ``EXEC_LIST TEST_PROTO TEST_ADV (0,0) [Env_toP 1; Env_toP 5]``; *)
*)

val DUMMY_ADV_def =
  Define
  ` (DUMMY_ADV (_: num ) (EnvtoA m) = (0:num,(Adv_toP m)))
  /\
    (DUMMY_ADV (_: num)  (PtoA m) = (0,(Adv_toEnv m)))
    `

val _ = export_theory()
