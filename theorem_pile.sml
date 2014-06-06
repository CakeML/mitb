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
(*   w2w ( ((BITS_TO_WORD a):'a word) @@ ((BITS_TO_WORD b):'b word))) *)
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



(* A fully padded block concerted into a word equals INT_MINw XOR 1w *)
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

