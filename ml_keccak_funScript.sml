open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory finite_mapTheory pred_setTheory;
open ml_translatorLib ml_translatorTheory word_preludeTheory;
open keccak_funTheory;

val _ = new_theory "ml_keccak_fun";

val _ = translation_extends "word_prelude";

val res = translate matrix2list_def;
val res = translate list_apply_numbered_def;
val res = translate matrix_apply_def;
val res = translate safe_el_def;
val res = translate (INST_TYPE[alpha|->``:64``] matrix_el_def);
val res = translate rc_def; (* unproveable side-condition! *)
val res = translate iota_def;
val res = translate matrix_generate_def;
val res = translate matB_table_def; (* unproveable side-condition" *)
val res = translate rot_table_def; (* unproveable side-condition" *)
val res = translate (INST_TYPE[alpha|->``:64``] rapac_compute_def);
val res = translate (INST_TYPE[alpha|->``:64``] theta_matc_def);
val res = translate (INST_TYPE[alpha|->``:64``] theta_matd_def);
val res = translate (INST_TYPE[alpha|->``:64``] theta_def);
val res = translate round_def;
val res = translate cut_def;
val res = translate list2matrix_def;
val res = translate permutation_def;

val _ = export_theory();
