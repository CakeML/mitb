open HolKernel Parse boolLib bossLib;
open arithmeticTheory wordsTheory listTheory wordsLib lcsymtacs;
val _ = numLib.prefer_num()
(* interactive use:
app load ["arithmeticTheory", "wordsTheory", "listTheory","wordsLib","lcsymtacs"];
*)

val _ = new_theory "keccak_fun";

(* Bitwise cyclic shift *)
(* Rotation is #<< *)

(* Matrix access. Note that the outer list is accessed via y coordinates, the
* lists within by x coordinates *)
val list_apply_numbered_def = Define`
  list_apply_numbered f lst =
    case
      (FOLDR (\ el (x,acc_list) . (x-1,((f x el)::acc_list))) ((LENGTH
      lst)-1,[]) lst)
    of
         (_,res) => res `

val matrix_apply_def = Define`
  matrix_apply f mat =
    list_apply_numbered (\ y row . list_apply_numbered (\ x el. f x y el)
    row) mat`;

val safe_el_def = Define`
  (safe_el d n [] = d) /\
  (safe_el d 0 (x::xs) = x) /\
  (safe_el d (SUC n) (x::xs) = safe_el d n xs)`

val matrix_el_def = Define`
  matrix_el mat x y = safe_el 0w (x MOD 5) (safe_el [] (y MOD 5) mat)`;

val matrix_generate_def = Define`
    matrix_generate f = GENLIST (\y.GENLIST (\x.f x y) 5) 5
    `;

(* Tranforming a bitstring into a matrix *)
(* TODO *)
(* Helper functions for matrix representation of list used in permutation *)
val cut_def = tDefine "cut"`
    (cut _ [] = [])
  /\(cut 0 _  = [])
  /\(cut n bs = (TAKE n bs )::(cut n (DROP n bs)))`
  (WF_REL_TAC`measure (LENGTH o SND)` >> simp[])

val list2matrix_def = Define`
    list2matrix bs = cut 5 bs
    `;

val matrix2list_def = Define`
    matrix2list mat = FLAT mat
    `;

(* Code for the permutation for a bandwidth of 1600 *)
(* Constants for permutation *)
val rot_table_def   = Define`
    (rot_table 0 0   = 0  )
  /\(rot_table 0 1   = 36 )
  /\(rot_table 0 2   = 3  )
  /\(rot_table 0 3   = 41 )
  /\(rot_table 0 4   = 18 )
  /\(rot_table 1 0   = 1  )
  /\(rot_table 1 1   = 44 )
  /\(rot_table 1 2   = 10 )
  /\(rot_table 1 3   = 45 )
  /\(rot_table 1 4   = 2  )
  /\(rot_table 2 0   = 62 )
  /\(rot_table 2 1   = 6  )
  /\(rot_table 2 2   = 43 )
  /\(rot_table 2 3   = 15 )
  /\(rot_table 2 4   = 61 )
  /\(rot_table 3 0   = 28 )
  /\(rot_table 3 1   = 55 )
  /\(rot_table 3 2   = 25 )
  /\(rot_table 3 3   = 21 )
  /\(rot_table 3 4   = 56 )
  /\(rot_table 4 0   = 27 )
  /\(rot_table 4 1   = 20 )
  /\(rot_table 4 2   = 39 )
  /\(rot_table 4 3   = 8  )
  /\(rot_table 4 4   = 14 )
  `

val rc_def = Define `
   (rc 0   = 0x0000000000000001w:word64)
/\ (rc 1   = 0x0000000000008082w:word64)
/\ (rc 2   = 0x800000000000808Aw:word64)
/\ (rc 3   = 0x8000000080008000w:word64)
/\ (rc 4   = 0x000000000000808Bw:word64)
/\ (rc 5   = 0x0000000080000001w:word64)
/\ (rc 6   = 0x8000000080008081w:word64)
/\ (rc 7   = 0x8000000000008009w:word64)
/\ (rc 8   = 0x000000000000008Aw:word64)
/\ (rc 9   = 0x0000000000000088w:word64)
/\ (rc 10  = 0x0000000080008009w:word64)
/\ (rc 11  = 0x000000008000000Aw:word64)
/\ (rc 12  = 0x000000008000808Bw:word64)
/\ (rc 13  = 0x800000000000008Bw:word64)
/\ (rc 14  = 0x8000000000008089w:word64)
/\ (rc 15  = 0x8000000000008003w:word64)
/\ (rc 16  = 0x8000000000008002w:word64)
/\ (rc 17  = 0x8000000000000080w:word64)
/\ (rc 18  = 0x000000000000800Aw:word64)
/\ (rc 19  = 0x800000008000000Aw:word64)
/\ (rc 20  = 0x8000000080008081w:word64)
/\ (rc 21  = 0x8000000000008080w:word64)
/\ (rc 22  = 0x0000000080000001w:word64)
/\ (rc 23  = 0x8000000080008008w:word64)
    `;

(* First transformation: Theta *)
val theta_matc_def = Define`
    theta_matc mat x = (
        (matrix_el mat x 0)
      ??(matrix_el mat x 1)
      ??(matrix_el mat x 2)
      ??(matrix_el mat x 3)
      ??(matrix_el mat x 4))
    `;

val theta_matd_def = Define`
    theta_matd mat x = ((theta_matc mat ( (x+4) MOD 5)) ?? ((theta_matc mat (x+1 MOD 5)))
    #<< 1)
    `;

val theta_def = Define`
    theta mat = matrix_apply (\ x y el. el ?? (theta_matd mat x)) mat
    `;

(* Second, third and fourth transformation combined *)
(* We call it rapac, because it is Rho And Pi And Chi combined. *)

(* The following function describes the reverse of the mapping from (x,y) to
* (y,2*x+3*y) as a table, which will be used to lookup values corresponding to
* the Matrix B in the implementation overview. *)

val matB_table_def   = Define`
    (matB_table 0 0 = (0, 0)  )
 /\ (matB_table 0 1 = (3, 0)  )
 /\ (matB_table 0 2 = (1, 0)  )
 /\ (matB_table 0 3 = (4, 0)  )
 /\ (matB_table 0 4 = (2, 0)  )
 /\ (matB_table 1 0 = (1, 1)  )
 /\ (matB_table 1 1 = (4, 1)  )
 /\ (matB_table 1 2 = (2, 1)  )
 /\ (matB_table 1 3 = (0, 1)  )
 /\ (matB_table 1 4 = (3, 1)  )
 /\ (matB_table 2 0 = (2, 2)  )
 /\ (matB_table 2 1 = (0, 2)  )
 /\ (matB_table 2 2 = (3, 2)  )
 /\ (matB_table 2 3 = (1, 2)  )
 /\ (matB_table 2 4 = (4, 2)  )
 /\ (matB_table 3 0 = (3, 3)  )
 /\ (matB_table 3 1 = (1, 3)  )
 /\ (matB_table 3 2 = (4, 3)  )
 /\ (matB_table 3 3 = (2, 3)  )
 /\ (matB_table 3 4 = (0, 3)  )
 /\ (matB_table 4 0 = (4, 4)  )
 /\ (matB_table 4 1 = (2, 4)  )
 /\ (matB_table 4 2 = (0, 4)  )
 /\ (matB_table 4 3 = (3, 4)  )
 /\ (matB_table 4 4 = (1, 4)  )
 `;

(* Compute the three steps using a representation of Matrix B as a list of pairs
* with coordinates and values *)
val rapac_compute_def = Define `
    rapac_compute mat =
        let matB = matrix_generate (\x y .
                     let (xt,yt) = matB_table x y in
                                     (matrix_el mat  xt yt) #<< (rot_table  xt
                                     yt ))
        in
          matrix_generate (\x y .
              (matrix_el matB x y)
           ?? (   ¬ (matrix_el matB ((x+1) MOD 5)  y)
               &&   (matrix_el matB ((x+2) MOD 5)  y)))
               `;

val iota_def = Define`
  iota i mat =
    matrix_apply (\  x y elem . case (x,y) of
                                (0,0) => (matrix_el mat  0 0 ) ?? (
                                rc i)
                               |(_,_) => elem )
                                mat
                                `;

val zeromatrix_def = Define`
    zeromatrix = GENLIST (\wildcard.GENLIST (\wildcard. 0w:word64) 5) 5
    `;

val first_round_def = Define`
    firstround mat = (iota 0 (rapac_compute (theta mat)))
      `;

val second_round_def = Define`
    secondround mat = (iota 1 (rapac_compute (theta mat)))
      `;

(*
EVAL ``firstround zeromatrix``;
EVAL ``secondround (firstround zeromatrix)``;

Anthony's help for pretty printing:
store |> concl |> rhs |> listSyntax.dest_list |> fst |> hd |>
listSyntax.dest_list |> fst |> hd |> wordsSyntax.dest_n2w;
*)

val round_def = tDefine "round" `
    round i mat =
    if i>=  24 then mat
    else
      round (i+1) (iota i (rapac_compute(theta(mat))))`
  (WF_REL_TAC `measure (($- 24) o FST )` THEN simp[])

val permutation_def = Define`
    permutation bitstring =
        matrix2list (round 0 (list2matrix bitstring))
        `;

val _ = export_theory();
