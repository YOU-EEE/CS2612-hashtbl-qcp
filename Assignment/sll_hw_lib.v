Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Permutation.
Require Import String.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
From compcert.lib Require Import Integers.
Local Open Scope Z_scope.
Local Open Scope sets.
Import ListNotations.
Local Open Scope list.
Require Import String.
Local Open Scope string.

From SimpleC.EE Require Import sll_lib.

Import naive_C_Rules.
Local Open Scope sac.

Definition max : list Z -> Z :=
  fold_right Z.max 0.

Fixpoint has_zero (l : list Z) : Z :=
  match l with
  | nil => 0
  | x :: xs => if Z.eqb x 0 then 1 else has_zero xs
  end.

Lemma max_cons_tail : forall x l, max (l ++ x :: nil) = Z.max x (max l).
Proof.
  intros. revert x.
  induction l ; simpl in *; auto.
  intros.
  rewrite IHl. lia.
Qed. 

Lemma has_zero_cons_tail : forall x l, x <> 0 -> has_zero (l ++ x :: nil) = has_zero l.
Proof.
  intros. generalize dependent x. 
  induction l ; simpl in *; auto.
  - intros. destruct (Z.eqb x 0) eqn:Heq ; simpl ; try lia.
  - intros. rewrite IHl ; try lia. 
Qed.

Lemma zeroIn_has_zero : forall l, In 0 l -> has_zero l = 1.
Proof.
  intros. 
  apply in_split in H.
  destruct H as [l1 [l2 ?]]. subst.
  revert l2. 
  induction l1 ; simpl in *; auto.
  intros. destruct (Z.eqb a 0) eqn:Heq ; simpl ; try lia.
  rewrite IHl1 ; auto.
Qed.
  