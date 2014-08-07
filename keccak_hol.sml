exception InvalidInputString;
exception TruncLargerThanBitrate;
exception UnpaddedBlock;
exception BlockOfWrongSize;
exception BandwidthOfWrongSize;
exception TableOutOfBounds;
exception CoordinatesNotInList of int * int;
exception InvalidIntList;
exception BadBitstringLength;
exception NotInRangeOfPartialLog;


(* Operations on bits and bitstrings *)
fun neg a = not a;
fun bitxor (a, b) = a<>b;
fun bitand (a, b) = a andalso b;

type bitstring = bool list;
fun op xor (a,b: bitstring) = List.map bitxor (ListPair.zipEq  (a,b));
fun op andop (a,b: bitstring) = List.map bitand (ListPair.zipEq  (a,b));
fun negate (a: bitstring) = List.map (not) a;

(* Bitwise cyclic shift *)

infix 9 bitxor
infix 9 bitand
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

(* little helper for examples *)
fun repeat 0 _ = []
  | repeat n item = item::(repeat (n-1) item);

(* Tools for the matrix representation we use *)

(* Helper functions for matrix representation of list used in permutation *)
fun cut n [] = []
  | cut n bs = (List.take(bs,n))::(cut n (List.drop(bs,n)))
fun cut_uneven n bs = 
  (* cuts with a rest *)
  if List.length(bs) <= n then [bs]
  else 
    (List.take(bs,n))::(cut_uneven n (List.drop(bs,n)))

fun list2funmatrix (bs:bitstring) = 
  (fn (qx,qy,qz) => 
      let 
        val (x,y,z) = ((qx mod 5),(qy mod 5),(qz mod 64))
      in
        List.nth(bs,64*(5*y + x) + z)
      end
      )

fun funmatrix2list (mat) = 
let
  fun create n =
  let
    val z=n mod 64
    val x=((n-z) mod 320) div 64
    val y=(n - (64*x) - z) div 320
  in
    mat (x,y,z)
  end
in
  List.tabulate (1600,create)
end

(* Input out things .. for convenience *) 

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

fun pinp s = 
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

(* Pretty printing for matrixes. Words are shown reversed, i.e., msb at the
* front. *)
fun print_mat block =
let 
  val gen_mat_25 = List.tabulate (5, (fn x => List.tabulate(5, (fn y => (x,y)))))
  fun apply_numbered f lst=
      case
       (List.foldr (fn (el,(x,lst)) => (x-1,(f(x,el)::lst)))
       (List.length(lst)-1,[]) lst )
       of
           (_,res) => res;

  fun apply_mat f mat=
      apply_numbered (fn (y,row) => apply_numbered (fn (x,el) => f(x,y,el)) row )
      mat;
  fun funmatrix2listmatrix mat =
    apply_mat (fn (x,y,_) => List.tabulate (64,(fn z => mat(x,y,z))))
    gen_mat_25;
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
        val s = ( Int.fmt StringCvt.HEX ( bitstring2int (el)))
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

fun print_funmat block =
    print_mat (funmatrix2listmatrix block) ;

  fun theta mat (qx,qy,qz)= 
  let
    val (x,y,z) = ((qx mod 5),(qy mod 5),(qz mod 64))
    val sum1 =  (mat (x-1,0,z)) bitxor (mat (x-1,1,z)) bitxor (mat (x-1,2,z)) bitxor (mat (x-1,3,z)) bitxor (mat (x-1,4,z))
    val sum2 =  (mat (x+1,0,z-1)) bitxor (mat (x+1,1,z-1)) bitxor (mat (x+1,2,z-1)) bitxor (mat (x+1,3,z-1)) bitxor (mat (x+1,4,z-1))
  in 
    ( mat (x,y,z)) bitxor sum1 bitxor sum2
  end;

fun rho mat (qx,qy,qz) =
  let
    val (x,y,z) = ((qx mod 5),(qy mod 5),(qz mod 64))
  in
    mat (x,y,z - (rot_table (x,y))) (* The rotation table results for an equation,
    maybe prove the correctness of the table seperately. *)
  end

fun equation_table coord =
let
  val coord_table = List.tabulate (25, (fn n => (n mod 5, n div 5)));
  val coord_value_table = List.map (fn (xp,yp) => ((yp, (2*xp + 3*yp) mod
  5),(xp,yp))) coord_table
in
  case ( List.find (fn elem => case elem of (c,_) => c=coord ) coord_value_table)
  of
     SOME((_,value)) => value
     |    NONE       => raise CoordinatesNotInList(coord)
end

fun pi mat (qx,qy,qz) =
  let
    val (x,y,z) = ((qx mod 5),(qy mod 5),(qz mod 64))
    val (xp,yp) = equation_table (x,y)
  in
    mat (xp,yp,z) 
  end

fun chi mat (qx,qy,qz) =
  let
    val (x,y,z) = ((qx mod 5),(qy mod 5),(qz mod 64))
  in
    mat (x,y,z) bitxor ((neg (mat (x+1,y,z))) bitand (mat (x+2,y,z)))
  end

  (* Does not work correctly, we will use constants for now, and
  * maybe later in HOL, operations on polynomials.
  * For now, we use the constants *)
  (*
fun lsfr (in1, in2, in3, in4, in5, in6, in7, in8) =
let
  val new = in8 bitxor (in6 bitxor (in5 bitxor in4 ))
in
  ((new, in1, in2, in3, in4, in5, in6, in7),in8)
end

fun lsfrout n =
let 
  fun helper 0=
    (* seed *)
     (lsfr (false, false, false, false, false, false, false, true))
    | helper n = case (helper (n-1)) of 
                      (state,_) => lsfr (state)
in
  case (helper n) of 
       (_,out) => out
end
*)

fun rc_old 0 = 0x0000000000000001
  | rc_old 1 = 0x0000000000008082
  | rc_old 2 = 0x800000000000808A
  | rc_old 3 = 0x8000000080008000
  | rc_old 4 = 0x000000000000808B
  | rc_old 5 = 0x0000000080000001
  | rc_old 6 = 0x8000000080008081
  | rc_old 7 = 0x8000000000008009
  | rc_old 8 = 0x000000000000008A
  | rc_old 9 = 0x0000000000000088
  | rc_old 10 = 0x0000000080008009
  | rc_old 11 = 0x000000008000000A
  | rc_old 12 = 0x000000008000808B
  | rc_old 13 = 0x800000000000008B
  | rc_old 14 = 0x8000000000008089
  | rc_old 15 = 0x8000000000008003
  | rc_old 16 = 0x8000000000008002
  | rc_old 17 = 0x8000000000000080
  | rc_old 18 = 0x000000000000800A
  | rc_old 19 = 0x800000008000000A
  | rc_old 20 = 0x8000000080008081
  | rc_old 21 = 0x8000000000008080
  | rc_old 22 = 0x0000000080000001
  | rc_old 23 = 0x8000000080008008
  | rc_old _ = raise TableOutOfBounds;

  (* Probably those two tables can be proven correct w.r.t. their algebraic
  * defintion *)

fun rc i (qx,qy,qz) = 
  let
    val (x,y,z) = ((qx mod 5),(qy mod 5),(qz mod 64))
    fun partial_log n = case n of 
                      1 => 0
                    | 2 => 1
                    | 4 => 2
                    | 8 => 3
                    |16 => 4
                    |32 => 5
                    |64 => 6
                    | _ => raise NotInRangeOfPartialLog
    val j = (partial_log (z+1))
    val t = j + (7*i)
  in
    if x=0 andalso y=0 then 
      (* lsfrout(t) *)
      List.nth ((int2bitstring (rc_old i)),z)
    else 
      false
  end
  handle
    NotInRangeOfPartialLog => false;

fun iota i mat (qx,qy,qz) =
  let
    val (x,y,z) = ((qx mod 5),(qy mod 5),(qz mod 64))
  in
    mat (x,y,z) bitxor (rc i (x,y,z))
  end

(* transition for round i *)
fun round i block = 
  (* First transformation *)
    if i>=  24 then block
    else 
      round (i+1) (iota i (rho(pi(chi(theta(block))))))

fun permutation1600 (block:bitstring) =
  if List.length(block) <> 1600 then
    raise BlockOfWrongSize
  else
    funmatrix2list(round 0 (list2funmatrix block));

(* Sponge Construction *)

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

(* Sponge (to be checked manually)*)
fun zeromatrix (x,y,z) = false;
fun firstround mat = (iota 0 (chi(pi(rho(theta(mat))))));
fun secondround mat = (iota 1 (chi(pi(rho(theta(mat))))));
fun thirdround mat = (iota 2 (chi(pi(rho(theta(mat))))));
fun permute mat = round 0 mat;

print_funmat (firstround zeromatrix);
print_funmat (theta(firstround zeromatrix));
print_funmat ( rho ( theta ( firstround zeromatrix)));
print_funmat ( pi (rho ( theta ( firstround zeromatrix))));
print_funmat ( chi (pi (rho ( theta ( firstround
zeromatrix)))));
print_funmat ( thirdround (secondround(firstround
zeromatrix)));
(* until here it works out .. *)

fun zeromatrix (x,y,z) = 0;
print_funmat (permute (zeromatrix2));

(* padding an bit representation *)
val m = pinp("53587BC8");
val m2 = pinp (
  "724627916C50338643E6996F07877EAFD96BDF01DA7E991D4155B9BE1295EA7D21C93"^
  "91F4C4A41C"^
  "75F77E5D27389253393725F1427F57914B273AB862B9E31DABCE506E558720520D333"^
  "52D119F699E784F9E548FF91BC35CA147042128709820D69A8287EA3257857615EB03"^
  "21270E94B84F446942765CE882B191FAEE7E1C87E0F0BD4E0CD8A927703524B559B76"^
  "9CA4ECE1F6DBF313FDCF67C572EC4185C1A88E86EC11B6454B371980020F19633B6B9"^
  "5BD280E4FBCB0161E1A82470320CEC6ECFA25AC73D09F1536F286D3F9DACAFB2CD1D0"^
  "CE72D64D197F5C7520B3CCB2FD74EB72664BA93853EF41EABF52F015DD591500D018D"^
  "D162815CC993595B195");
val test345val = 
  "E7B462FE88FE41B20C5E11D2125D1788383CC5C0EC7E9E8AEF1A7532E4C4BF255D799"^
  "64365C9718064F9F776CACA03E930E649FC659488A349D011BE38332F86DC4F3B36D7"^
  "A58D7996D7D8A06AB26E8E4C6525B8DC47D0121CDCE1CADB52AB02BCF2E7C5EFA8088"^
  "0C7F2BDBE820C985BAE0519A597FA0F50698D3FB970D07B5BCFA9F928C55827A750DA"^
  "8C2ABCC5E8D29F50ECD2AA52FD50DDFD2B9E24D8048F4E4A97D989A555483B34812BF"^
  "EEC0A8EC70BD0DA79486607B88A71177B7AF3DEE4A1D8E670941B34";

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
