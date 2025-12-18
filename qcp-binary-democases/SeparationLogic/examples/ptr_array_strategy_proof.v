Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE Require Import ptr_array_strategy_goal.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma ptr_array_strategy1_correctness : ptr_array_strategy1.
  pre_process_default.
Admitted.

Lemma ptr_array_strategy4_correctness : ptr_array_strategy4.
  pre_process_default.
Admitted.

Lemma ptr_array_strategy5_correctness : ptr_array_strategy5.
  pre_process_default.
Admitted.

Lemma ptr_array_strategy6_correctness : ptr_array_strategy6.
  pre_process_default.
Admitted.

Lemma ptr_array_strategy7_correctness : ptr_array_strategy7.
  pre_process_default.
Admitted.

Lemma ptr_array_strategy8_correctness : ptr_array_strategy8.
  pre_process_default.
Admitted.

Lemma ptr_array_strategy9_correctness : ptr_array_strategy9.
  pre_process_default.
Admitted.

Lemma ptr_array_strategy10_correctness : ptr_array_strategy10.
  pre_process_default.
Admitted.

Lemma ptr_array_strategy2_correctness : ptr_array_strategy2.
  pre_process_default.
Admitted.

Lemma ptr_array_strategy11_correctness : ptr_array_strategy11.
  pre_process_default.
Admitted.

Lemma ptr_array_strategy3_correctness : ptr_array_strategy3.
  pre_process_default.
Admitted.

Lemma ptr_array_strategy12_correctness : ptr_array_strategy12.
  pre_process_default.
Admitted.
