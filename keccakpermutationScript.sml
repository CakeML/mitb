open HolKernel;
open Parse;
open boolLib;
open bossLib;
open arithmeticTheory;
open wordsTheory;
open listTheory;
open wordsLib;
open lcsymtacs;
open fcpTheory;
;

val _ = numLib.prefer_num()

val _ = new_theory "keccakpermutation";

(* translate from keccak_spec.sml *)

val word2matrix_representation_def = Define `
word2matrix_representation (w: ('r+'c) word ) = 
  (\(qx,qy,qz) .
      let 
        (x,y,z) = ((qx MOD 5),(qy MOD 5),(qz MOD 64))
      in
        (w ' (64*(5*y + x) + z))
      )
`;

val matrix_representation2word_def = Define`
(matrix_representation2word mat):('r+'c) word = 
(
FCP i. let z=i MOD 64 in
       let x=((i-z) MOD 320) DIV 64 in
       let y=(i - (64*x) - z) DIV 320 in
         mat (x,y,z)
)`;


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


val matrix_0123_def= Define`
matrix_0123 =  
(FCP i . 
   if i=0 then 
      (FCP j. if j=0 then 0 else 1 )
   else 
      (FCP j. if j=0 then 2 else 3)
     ): num [2][2]
     `;

     let matrix_mul = new_definition
       `!A:real^N^M B:real^P^N.
               A ** B = lambda i j. sum(1..dimindex(:N)) (\k. A$i$k * B$k$j)`;;


val MAT_MUL_def = Define`
MATMUL (A: num ['n]['m]) (B : num ['n] ['p]) =
((FCP i j . SUM (dimindex(:'n))
(\r . (A ' i ' r) * (B ' r ' j))
): num ['m] ['p])
`;

val _ = overload_on ("*", Term`$MATMUL`);

val rho_def = Define`
rho mat (qx,qy,qz) =
  let (x,y,z) = ((qx MOD 5),(qy MOD 5),(qz MOD 64)) in
    let t = CHOICE (\t. (0 <= t) /\ (t < 24 ) /\ 
    ( ((x=0) /\ (y=0)) ==> (t=1) ) /\
    ( ~((x=0) /\ (y=0)) ==> (
      t=1 (*TODO no, complicated matrix multiplication instead *)
    ))
    )
  in
    mat (x,y,z - (t+1)*(t+2) DIV 2 )
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

val rc_def = Define `
rc t = T`; (* See how we can define the LSFR *)

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
 
val IsKeccakpermutation1600_def = Define `
IsKeccakpermutation1600 f =
? RC .
(IsKeccakroundconstant RC)
/\
(f = ntimes 24 (round RC))`

val _ = export_theory();

(* vim: tw=72:comments=sr\:(*,m\:\ ,exr\:*)
 *  *)
