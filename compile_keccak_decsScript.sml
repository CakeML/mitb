open HolKernel boolLib bossLib repl_computeLib repl_computeTheory ml_keccak_funTheory
val _ = new_theory"compile_keccak_decs"

val ct = ``init_compiler_state.contab``
val m = ``<|bvars:=[];mvars:=FEMPTY;cnmap:=cmap(^ct)|>``
val cs = ``<|out:=[];next_label:=init_compiler_state.rnext_label|>``

val compile_keccak_decs_def = zDefine`
  compile_keccak_decs = FOLDL (compile_dec1 NONE FEMPTY) (^ct,^m,[],0,^cs) ml_keccak_fun_decls`

val _ = computeLib.add_funs[ml_keccak_fun_decls]
val _ = computeLib.stoppers := let
  val stoppers = [``Dlet``,``Dletrec``,``Dtype``]
  in SOME (fn tm => mem tm stoppers) end

fun mk_initial_split n =
  (rhs(concl(compile_keccak_decs_def)))
     |> (RAND_CONV (EVAL THENC chunkify_CONV n) THENC
         RATOR_CONV (RAND_CONV EVAL))

val initial_split20 = mk_initial_split 20

val (initial', decllist_defs) = let
  val r = rhs (concl initial_split20)
  val r' = rand r
  val lists = spine_binop (Lib.total listSyntax.dest_append) r'
  val defs = map mk_def lists
  fun replace ths t =
    case ths of
      []=> ALL_CONV t
    | [d] => SYM d
    | d::ds => (LAND_CONV (K (SYM d)) THENC RAND_CONV (replace ds)) t
in
  (CONV_RULE (RAND_CONV (RAND_CONV (replace defs))) initial_split20, defs)
end

fun doit i (defs, th) = let
  val list_t = rand (rhs (concl th))
  val nstr = listSyntax.mk_length list_t |> (PURE_REWRITE_CONV defs THENC EVAL)
               |> concl |> rhs |> term_to_string
  val _ = print (nstr^" declarations still to go\n")
  val (defs', th20_0) = iterate i defs (rhs (concl th))
  val th20 = CONV_RULE (RAND_CONV (K th20_0)) th
  val _ = PolyML.fullGC()
in
  (defs', th20)
end

val x100 = doit 5 (decllist_defs, initial')
val x200 = doit 5 x100
val (_,th) = x200;

val _ = save_thm("keccak_decs_compiled", th);

val _ = export_theory()
