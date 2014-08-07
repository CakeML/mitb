(* Mike moved definitions of cut, cut_uneven earlier to get file to
load  - is this OK?*)

exception InvalidInputString;
exception TruncLargerThanBitrate;
exception UnpaddedBlock;
exception BlockOfWrongSize;
exception BandwidthOfWrongSize;
exception TableOutOfBounds;
exception CoordinatesNotInList of int * int;
exception InvalidIntList;
exception BadBitstringLength;

(* Part I - Preliminaries *) 
(* ====================== *) 

(* Operations on bits and bitstrings *)
fun neg a = not a;
fun bitxor (a, b) = a<>b;
fun bitand (a, b) = a andalso b;

type bitstring = bool list;
fun op xor (a,b: bitstring) = List.map bitxor (ListPair.zipEq  (a,b));
fun op andop (a,b: bitstring) = List.map bitand (ListPair.zipEq  (a,b));
fun negate (a: bitstring) = List.map (not) a;

(* Bitwise cyclic shift *)
fun rot (a  , 0) = a
  | rot ([] , n) = []
  | rot (a  , n) =
        List.drop(a,(n mod length(a)))@List.take(a,(n mod length(a)))

infix 9 xor
infix 9 andop

(* Conversion function for bitstrings *)
fun powerOftwo 0 = Int.toLarge(1)
  | powerOftwo n = 2*(powerOftwo (n-1))

(* Translation function. Tail of the list is the msb *)
fun int2bitstring n=
let 
  fun helper 1 n = [n]
    | helper p n =
    (n div p)::(helper (p div 2) (n mod p))
  val result_int_list = List.rev(helper (powerOftwo 63) n)
in
  List.map (fn n => case n of 0 => false | 1 => true | _ => raise
  InvalidIntList ) result_int_list
end;

fun bitstring2int  bs =
let  
  fun helper _ [] = Int.toLarge(0)
  | helper i (true::xs) = powerOftwo(i) + (helper (i+1) xs)
  | helper i (false::xs) = (helper (i+1) xs);
in
  helper 0 bs
end;

(* Cut a list into a list containing lists of n elements *)
fun cut n [] = []
  | cut n bs = (List.take(bs,n))::(cut n (List.drop(bs,n)))

(* Cut a list into a list containing lists of n elements, except for the
* trailing list, which might contain less than n elements. *)
fun cut_uneven n bs = 
  (* cuts with a rest *)
  if List.length(bs) <= n then [bs]
  else 
    (List.take(bs,n))::(cut_uneven n (List.drop(bs,n)))

(* little helper for examples *)
fun repeat 0 _ = []
  | repeat n item = item::(repeat (n-1) item);

(* Pretty printing a bitstring *)
fun pp bs = 
  (* This follows the conventions described in Keccak-submission-3.pdf, Section
  * 6.1 
  *
  * The message is cut into bits and every bitstring is interpreted with msb at
  * the end of the list. On the last bit in the list, zero is prefixed if
  * necessary.
  *
  * *)
    List.foldr 
    (fn (small_bs,str) => 
    let 
      val eightbit = small_bs@(repeat (8-List.length(small_bs)) false) 
      val byte =   Int.fmt StringCvt.HEX ( bitstring2int (eightbit))
    in
      if String.size(byte)=1
        then "0"^byte^str
        else byte^str
    end)
    "" (cut_uneven 8 bs);

fun pp2 bs = List.foldr (fn (lst,str) => pp(lst)^" "^str) "" (cut 8 bs)

fun pi s = 
  (* This follows the conventions described in Keccak-submission-3.pdf, Section
  * 6.1 *)
let 
  fun convert n = 
        case n of 0 => false | 1 => true | _ => raise InvalidIntList 
  fun helper 1 n = [convert n]
    | helper p n =
    (convert (n div p))::(helper (p div 2) (n mod p))
  fun powerOftwo 0 = Int.toLarge(1)
    | powerOftwo n = 2*(powerOftwo (n-1))
  fun toInt c = case 
        StringCvt.scanString (Int.scan StringCvt.HEX) (Char.toString c)
        of SOME(n) => n
                |_ => raise InvalidInputString
  fun prepend (c,lst) = ( helper (powerOftwo 3) (toInt c) )@lst
  val remove_leading_zeroes = (* MSR is at the end of list, so zeroes are
    trailing w.r.t. the list *)
    List.foldr (fn (bit,lst) => case (bit,lst) of 
                                     (false,[]) => [] 
                                   | (true,[]) => [true]
                                   | (b,lst) => b::lst)  []
  fun reorder_bits lst = List.foldr
    (fn (elem,bs) => (List.rev (elem))@bs) [] (cut_uneven 8 lst)
in
    let 
        val bitstring_with_leading_zeroes = List.foldr prepend [] (String.explode s)
    in
      reorder_bits (remove_leading_zeroes (bitstring_with_leading_zeroes))
    end
end;


(* Part II - Matrix representation *) 
(* =============================== *) 

(* The reference implementation uses arrays of arrays of bits for the
* representation of the state inside the permutation. We don't have those means,
* instead, we rely on transforming the input to the permutation, a list of bool,
* into a list representation of a matrix, that is, a list of lists of lists of
* bools. 
* The following helper functions for said matrix representation are used in the
* implementation of the permutation *)

fun list2matrix (bs:bitstring) =
  (* converts a list of bools into 25 segments of length 64, 
   * sorting them as a list that has 25 elements which are lists of size 64 *)
   if List.length(bs)<>1600 then
     raise BlockOfWrongSize
   else
     cut 5 ( List.map (List.rev) (cut 64 (bs)));

fun matrix2list mat=
let 
  fun flatten lst = List.foldr (op @) [] lst
in
  flatten ( List.map (List.rev) (flatten mat) )
end

(* Matrix access. Note that the outer list is accessed via y coordinates, the
* lists within by x coordinates *)
fun apply_numbered f lst=
    case
     (List.foldr (fn (el,(x,lst)) => (x-1,(f(x,el)::lst)))
     (List.length(lst)-1,[]) lst )
     of
         (_,res) => res;
fun apply_mat f mat=
    apply_numbered (fn (y,row) => apply_numbered (fn (x,el) => f(x,y,el)) row )
    mat;

(* Access the element at position (x,y) *)
fun el mat (x,y) = (* List.nth(mat,5*(y mod 5)+(x mod 5)); *)
  List.nth(List.nth(mat,y mod 5), x mod 5) 

(* Generate a matrix where each element is their pair of coordinates *)
val gen_mat_25 = List.tabulate (5, (fn x => List.tabulate(5, (fn y => (x,y)))));



(* Pretty printing for matrixes. Words are shown reversed, i.e., msb at the
* front. *)
fun print_mat block =
let 
  fun format_bs el = 
    (*
      let 
        val s = pp el
        val l = String.size(s)
        fun prepend s 0 = s
           |prepend s n = "0"^(prepend s (n-1))
      in
        if l < 64 then (prepend s (16-l))
        else s
      end 
      *)
      let 
        val s = ( Int.fmt StringCvt.HEX ( bitstring2int (List.rev el) ))
        val l = String.size(s)
        fun prepend s 0 = s
           |prepend s n = "0"^(prepend s (n-1))
      in
        if l < 64 then (prepend s (16-l))
        else s
      end 
  fun print_line ls = List.foldr (fn (el,str) => format_bs(el)^" "^str) "" ls
  fun print_mat mat  = List.foldr (fn (el,str) => (print_line el)^"\n"^str) ""
    mat
  (* fun rotate mat = apply_mat (fn (x,y,_) => (el mat (x,y))) gen_mat_25; *)
in
  print( print_mat block)
end;


(* Part III - The Keccak permutation *) 
(* ================================= *) 

(* Code for the permutation for a bandwidth of 1600 *)
(* Constants for permutation *)
fun rot_table (0,0) = 0
  | rot_table (0,1) =    36
  | rot_table (0,2) =     3
  | rot_table (0,3) =    41
  | rot_table (0,4) =    18
  | rot_table (1,0) = 1
  | rot_table (1,1) =    44
  | rot_table (1,2) =    10
  | rot_table (1,3) =    45
  | rot_table (1,4) =     2
  | rot_table (2,0) = 62
  | rot_table (2,1) =    6
  | rot_table (2,2) =    43
  | rot_table (2,3) =    15
  | rot_table (2,4) =    61
  | rot_table (3,0) = 28
  | rot_table (3,1) =   55
  | rot_table (3,2) =    25
  | rot_table (3,3) =    21
  | rot_table (3,4) =    56
  | rot_table (4,0) = 27
  | rot_table (4,1) =   20
  | rot_table (4,2) =    39
  | rot_table (4,3) =     8
  | rot_table (4,4) =    14
  | rot_table  _    = raise TableOutOfBounds;

fun rc 0 = 0x0000000000000001
  | rc 1 = 0x0000000000008082
  | rc 2 = 0x800000000000808A
  | rc 3 = 0x8000000080008000
  | rc 4 = 0x000000000000808B
  | rc 5 = 0x0000000080000001
  | rc 6 = 0x8000000080008081
  | rc 7 = 0x8000000000008009
  | rc 8 = 0x000000000000008A
  | rc 9 = 0x0000000000000088
  | rc 10 = 0x0000000080008009
  | rc 11 = 0x000000008000000A
  | rc 12 = 0x000000008000808B
  | rc 13 = 0x800000000000008B
  | rc 14 = 0x8000000000008089
  | rc 15 = 0x8000000000008003
  | rc 16 = 0x8000000000008002
  | rc 17 = 0x8000000000000080
  | rc 18 = 0x000000000000800A
  | rc 19 = 0x800000008000000A
  | rc 20 = 0x8000000080008081
  | rc 21 = 0x8000000000008080
  | rc 22 = 0x0000000080000001
  | rc 23 = 0x8000000080008008
  | rc _ = raise TableOutOfBounds;

  fun theta mat = 
  let
    fun matC x =  
      (el mat (x,0)) xor (el mat (x,1)) xor (el mat (x,2)) xor (el mat (x,3)) xor (el mat (x,4))
    fun matD x = matC(x-1 mod 5) xor (rot(matC(x+1 mod 5),1))
  in 
    apply_mat (fn (x,y,elem) => (elem xor matD(x))) mat 
  end;

  (* Second, third and fourth transformation combined *)
  fun rhoAndpiAndchi mat = 
  let
    fun coordinate_helper n = 
    let
      val x=n div 5
      val y=n mod 5
      val coords_in_matB = (y,((2*x+3*y) mod 5))
    in
        ( coords_in_matB, rot((el mat (x,y)),rot_table (x,y)))
    end
    val matB_list =  List.tabulate (25,coordinate_helper)
    fun matB coord = case
      ( List.find (fn elem => case elem of (c,_) => c=coord )
      matB_list)
                            of
                               SOME((_,value)) => value
                               |    NONE => raise CoordinatesNotInList(coord)
    fun compute (x,y) =
      matB(x,y) xor ( negate ( matB((x+1) mod 5,y)) andop matB((x+2) mod 5, y))
    in 
      apply_mat (fn (x,y,_) => compute (x,y)) gen_mat_25
    end;

  fun iota i mat =
    apply_mat (fn (x,y,elem) => case (x,y) of
                                (0,0) => (el mat (0,0)) xor (
                                (List.rev (int2bitstring (rc i))))
                               |(_,_) => elem )
                                mat;

(* transition for round i *)
fun round i block = 
  (* First transformation *)
    if i>=  24 then block
    else 
      round (i+1) (iota i (rhoAndpiAndchi(theta(block))))

fun permutation1600 (block:bitstring) =
  if List.length(block) <> 1600 then
    raise BlockOfWrongSize
  else
      matrix2list (round 0 (list2matrix block));

(* Part IV - The Sponge Construction *) 
(* ================================= *) 

fun multiratepad r (m:bitstring) = 
let
  val zeroes = (r - ((length(m)+2) mod r)) mod r
  val padding=true::((repeat zeroes false)@[true]);
in
  m @ padding
end;

fun truncated_sponge permutation bitrate capacity trunc message=
let
  val bandwidth=bitrate+capacity
  val initial_state=repeat bandwidth false
  fun iterate (state,[]) = state
    | iterate (state,m)= 
    let
      val next_state = permutation(state xor (List.take(m,bitrate)@(repeat
      capacity false)))
    in
      iterate (next_state,(List.drop(m,bitrate)))
    end
  val result = iterate (initial_state, message)
in
  if trunc > bitrate then
    raise TruncLargerThanBitrate
  else
    if (length(message) mod bitrate)<>0 then
      raise UnpaddedBlock
    else
      List.take (result, trunc)
end;

fun SHA_3_224 m = 
  let 
    val bitrate = 1152 
    val capacity = 448  
    val bandwidth=bitrate+capacity
    val trunc = 224 (* truncation *)
    val permutation = permutation1600
    val padding=(multiratepad bitrate)
in
  truncated_sponge permutation bitrate capacity trunc (padding m)
  end;

(* Part V - Test Vectors *) 
(* ===================== *) 

(* Testing - tools for manual checks *)
val print_bits = List.foldr (fn (el,str) => case el of false => "0"^" "^str | true => "1"^" "^str) ""

(* Sponge (to be checked manually)*)
(*
val zeromatrix = list2matrix (repeat 1600 false);
fun firstround mat = (iota 0 (rhoAndpiAndchi(theta(mat))));
fun secondround mat = (iota 1 (rhoAndpiAndchi(theta(mat))));
fun permute mat = round 0 mat;

print_mat (firstround zeromatrix);
print_mat (theta(firstround zeromatrix));
print_mat (rhoAndpiAndchi( theta(firstround zeromatrix)));
print_mat (secondround(firstround zeromatrix));
print_mat (permute zeromatrix);
pp2 (matrix2list (permute zeromatrix));
print_mat (permute zeromatrix);
print_mat (list2matrix (matrix2list (permute zeromatrix)));
pp2 (matrix2list (permute( permute zeromatrix))); *)

(* padding an bit representation *)
val m = pi("53587BC8");
val m2 = pi (
  "724627916C50338643E6996F07877EAFD96BDF01DA7E991D4155B9BE1295EA7D21C93"^
  "91F4C4A41C"^
  "75F77E5D27389253393725F1427F57914B273AB862B9E31DABCE506E558720520D333"^
  "52D119F699E784F9E548FF91BC35CA147042128709820D69A8287EA3257857615EB03"^
  "21270E94B84F446942765CE882B191FAEE7E1C87E0F0BD4E0CD8A927703524B559B76"^
  "9CA4ECE1F6DBF313FDCF67C572EC4185C1A88E86EC11B6454B371980020F19633B6B9"^
  "5BD280E4FBCB0161E1A82470320CEC6ECFA25AC73D09F1536F286D3F9DACAFB2CD1D0"^
  "CE72D64D197F5C7520B3CCB2FD74EB72664BA93853EF41EABF52F015DD591500D018D"^
  "D162815CC993595B195");

val test1 = ( m = [true, true, false, false, true, false, true, false, false, false, false,
    true, true, false, true, false, true, true, false, true, true, true,
    true, false, true, false, false, true, true]);
val test2 = ( (pp(multiratepad 1152 m)) =
  "53587B390000000000000000000000000000000000000000000000000000000000000"^
  "000000000000000000000000000000000000000000000000000000000000000000000"^
  "000000000000000000000000000000000000000000000000000000000000000000000"^
  "000000000000000000000000000000000000000000000000000000000000000000000"^
  "000000000080"
  )

val test345val = 
  "E7B462FE88FE41B20C5E11D2125D1788383CC5C0EC7E9E8AEF1A7532E4C4BF255D799"^
  "64365C9718064F9F776CACA03E930E649FC659488A349D011BE38332F86DC4F3B36D7"^
  "A58D7996D7D8A06AB26E8E4C6525B8DC47D0121CDCE1CADB52AB02BCF2E7C5EFA8088"^
  "0C7F2BDBE820C985BAE0519A597FA0F50698D3FB970D07B5BCFA9F928C55827A750DA"^
  "8C2ABCC5E8D29F50ECD2AA52FD50DDFD2B9E24D8048F4E4A97D989A555483B34812BF"^
  "EEC0A8EC70BD0DA79486607B88A71177B7AF3DEE4A1D8E670941B34";

val test3 =
 (pp(permutation1600((repeat 1600 false) xor ((multiratepad 1152 m)@(repeat
 (1600-1152) false)))))
 = test345val;

val test4 =
 (pp(permutation1600((multiratepad 1152 m)@(repeat (1600-1152) false))))
 = test345val;

val test4 =
 (pp(SHA_3_224 m))
 = "E7B462FE88FE41B20C5E11D2125D1788383CC5C0EC7E9E8AEF1A7532";

val test5 = List.length m2 = 2048;

val test6 = pp(SHA_3_224 m2) 
    = "E90F81AE86D72DCC2190AF545A345150A629EE7DC7237C1958CFCDBC";

(* Check for problems with larger values *)
