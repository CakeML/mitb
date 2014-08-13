open HolKernel;
open Parse;
open boolLib;
open bossLib;
open arithmeticTheory;
open wordsTheory;
open listTheory;
open wordsLib;
open lcsymtacs;
;

val _ = numLib.prefer_num()

val _ = new_theory "keccakpermutation";

(* translated from keccak_spec.sml *)

val word2matrix_representation_def = Define`
word2matrix_representation w  = 
  (\(qx,qy,qz) .
      let 
        (x,y,z) = ((qx MOD 5),(qy MOD 5),(qz MOD 64))
      in
        (w ' (64*(5*y + x) + z))
      )
`;

val matrix_representation2word_def = Define`
(matrix_representation2word mat) = 
(
FCP i. let z=i MOD 64 in
       let x=((i-z) MOD 320) DIV 64 in
       let y=(i - (64*x) - z) DIV 320 in
         mat (x,y,z)
)`;

(* Tactic that performs case split for all numbers from 0 to n *)
fun split_num_in_range t n (g as (asl,w)) =
  let
    val eq = (mk_eq (t,(numSyntax.mk_numeral (Arbnum.fromInt
n))))
    val ineq = 
      if (n>0) then
        list_mk_comb (Term `$<=`, [t, numSyntax.mk_numeral (Arbnum.fromInt
  (n-1))])
      else (Term `F`)
    val term = mk_disj (eq, ineq) 
    val termimp = list_mk_imp (asl,term)
  in
    (if n>0 then
      mp_tac (prove(termimp, simp [])) >>
      rw [] 
      >| [all_tac,  split_num_in_range t (n-1)]
     else
       all_tac)
  end g;
fun qsplit_num_in_range q n = Q_TAC (fn t => split_num_in_range t n) q

(* Sanity check: transformation translates back correctly *)
val matrix_representation2word_word2matrix_representation = prove(``
! w:1600 word. 
matrix_representation2word  (word2matrix_representation w)
= w
``,
simp [matrix_representation2word_def, word2matrix_representation_def] >>
rw [GSYM WORD_EQ, word_bit_def, fcpTheory.FCP_BETA]  >>
qsplit_num_in_range `x` 1600 >>
fs []

`(x=0)\/(x=1)\/(x=2)\/(x=3)\/(x>3)` by simp []

);




val BSUM_def = Define`
(! f.  BSUM 0 f  = F)
/\
(!m f.  BSUM (SUC m) f  = ((BSUM m f) <> (f m) ))
`;

val theta_def = Define`
( theta mat (qx,qy,qz) )= 
(
  let (x,y,z) = ((qx MOD 5),(qy MOD 5),(qz MOD 64)) in
    let sum1 = BSUM 4 (\y'.  mat (x-1,y',z)) in
    let sum2 = BSUM 4 (\y'.  mat (x+1,y',z-1)) in 
    ( (( mat (x,y,z) ) <> sum1) <>  sum2)
)
`;

val rot_table_def = Define `
(rot_table (0,0) = 0)
/\
(rot_table (0,1) =    36)
/\
(rot_table (0,2) =     3)
/\
(rot_table (0,3) =    41)
/\
(rot_table (0,4) =    18)
/\
(rot_table (1,0) = 1)
/\
(rot_table (1,1) =    44)
/\
(rot_table (1,2) =    10)
/\
(rot_table (1,3) =    45)
/\
(rot_table (1,4) =     2)
/\
(rot_table (2,0) = 62)
/\
(rot_table (2,1) =    6)
/\
(rot_table (2,2) =    43)
/\
(rot_table (2,3) =    15)
/\
(rot_table (2,4) =    61)
/\
(rot_table (3,0) = 28)
/\
(rot_table (3,1) =   55)
/\
(rot_table (3,2) =    25)
/\
(rot_table (3,3) =    21)
/\
(rot_table (3,4) =    56)
/\
(rot_table (4,0) = 27)
/\
(rot_table (4,1) =   20)
/\
(rot_table (4,2) =    39)
/\
(rot_table (4,3) =     8)
/\
(rot_table (4,4) =    14)
`;

val rho_def = Define`
rho mat (qx,qy,qz) =
  let (x,y,z) = ((qx MOD 5),(qy MOD 5),(qz MOD 64)) in
    mat (x,y, (z - rot_table (x,y)))
`   

val pi_def = Define`
pi mat (qx,qy,qz) =
  let (x,y,z) = ((qx MOD 5),(qy MOD 5),(qz MOD 64)) in
    let (x',y') = CHOICE (\(x',y'). T (* TODO put the other matrix
    multiplication here *))
  in
    mat (x',y',z) 
`   

val chi_def = Define `
chi mat (qx,qy,qz) =
  let (x,y,z) = ((qx MOD 5),(qy MOD 5),(qz MOD 64)) in
    (mat (x,y,z))  <> ((~ (mat (x+1,y,z))) /\ (mat (x+2,y,z)))
`

val iota_def = Define `
iota RC i mat (qx,qy,qz) =
  let (x,y,z) = ((qx MOD 5),(qy MOD 5),(qz MOD 64)) in
    mat (x,y,z) <> (RC i (x,y,z))
    `

val round_def = Define `
round RC i = (iota RC i) o rho o pi o chi o theta `

val ntimes_def = Define `
(ntimes (SUC n) f  = (ntimes n f) o (f n))
/\
(ntimes 0 f  = (\x.x))`

val lsfr_comp = Define `
(lsfr_comp 0 =  ((0b10000000w:word8),T))
/\
(lsfr_comp (SUC n) = 
  let prev = (FST(lsfr_comp n)) in
   (((prev #>> 1)
      ??(if (word_bit 0 prev) then 
         0b1110w else 0w)), (word_bit 0 prev))
)`;

(* val _ = output_words_as_bin (); *)

val rc_def = Define `
rc t = SND (lsfr_comp t)  
`; 

val helper = Define `
(helper 0 = [(0,rc 0)])
/\
(helper (SUC n) = (SUC n, (rc (SUC n)))::(helper n))
`; 

val round_constants_def = Define `
(round_constants 0 = 0x0000000000000001w: word64) /\
(round_constants 1 = 0x0000000000008082w) /\
(round_constants 2 = 0x800000000000808Aw) /\
(round_constants 3 = 0x8000000080008000w) /\
(round_constants 4 = 0x000000000000808Bw) /\
(round_constants 5 = 0x0000000080000001w) /\
(round_constants 6 = 0x8000000080008081w) /\
(round_constants 7 = 0x8000000000008009w) /\
(round_constants 8 = 0x000000000000008Aw) /\
(round_constants 9 = 0x0000000000000088w) /\
(round_constants 10 = 0x0000000080008009w) /\
(round_constants 11 = 0x000000008000000Aw) /\
(round_constants 12 = 0x000000008000808Bw) /\
(round_constants 13 = 0x800000000000008Bw) /\
(round_constants 14 = 0x8000000000008089w) /\
(round_constants 15 = 0x8000000000008003w) /\
(round_constants 16 = 0x8000000000008002w) /\
(round_constants 17 = 0x8000000000000080w) /\
(round_constants 18 = 0x000000000000800Aw) /\
(round_constants 19 = 0x800000008000000Aw) /\
(round_constants 20 = 0x8000000080008081w) /\
(round_constants 21 = 0x8000000000008080w) /\
(round_constants 22 = 0x0000000080000001w) /\
(round_constants 23 = 0x8000000080008008w)
`

val IsKeccakroundconstant_def = Define `
IsKeccakroundconstant RC =
! i x y z.
((i <= 23) /\ (x <= 4)/\ (y <= 4) /\ (z <= 63))
==>
 (? j . ((j <= 6) /\ (z=2**j -1))  ==> 
   ((RC i (x,y,z)) = 
    (if ((x=0) /\ (y=0)) then
     rc (j+7*i)
    else F ))
 )
 /\
 ( (~(? j . ((j <= 6) /\ (z=2**j -1))))
   ==> (RC i (x,y,z) = F ))
`




val round_constants_correctness = prove(``
IsKeccakroundconstant (word2matrix_representation o round_constants )
``,
rw [IsKeccakroundconstant_def, word2matrix_representation_def] >>
Cases_on `i=0` >>
simp [round_constants_def] >>
qexists_tac `LOG 2 (z+1) ` >>
rw [] >>

Cases_on `x=4` >>
Cases_on `y=4` >>
Cases_on `z=63` >>
fs []
rw []
EVAL_TAC

qsplit_num_in_range `y` 4 >>
qsplit_num_in_range `x` 4 >>
qsplit_num_in_range `z` 63 >>
EVAL_TAC

`(z=63) \/ (z <= 62)` by simp []

BasicProvers.EVERY_CASE_TAC >>

EVAL ``LOG 2 8``



 
val IsKeccakpermutation1600_def = Define `
IsKeccakpermutation1600 f =
? RC .
(IsKeccakroundconstant RC)
/\
(f = ntimes 24 (round RC))`



val _ = export_theory();
