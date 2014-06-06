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
