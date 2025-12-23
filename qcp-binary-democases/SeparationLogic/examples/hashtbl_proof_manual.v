Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic MapLib.
Require Import hashtbl_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import hashtbl_lib.
Local Open Scope sac.

(* ---------------------------------------------------------------------- *)
(* Helper lemmas about lists                                               *)
(* ---------------------------------------------------------------------- *)

Lemma firstn_replace_nth_nat {A} (n: nat) (v: A) (l: list A) :
  firstn n (replace_nth n v l) = firstn n l.
Proof.
  revert l v.
  induction n; intros; destruct l; simpl; auto; f_equal; apply IHn.
Qed.

Lemma length_replace_nth {A} (n: nat) (v: A) (l: list A) :
  length (replace_nth n v l) = length l.
Proof.
  revert v l.
  induction n; intros v l.
  - destruct l; simpl; auto.
  - destruct l; simpl.
    + reflexivity.
    + f_equal. apply IHn.
Qed.

Lemma nth_replace_nth {A} (n: nat) (v d: A) (l: list A) :
  (n < length l)%nat ->
  nth n (replace_nth n v l) d = v.
Proof.
  revert l.
  induction n; intros l Hlen; destruct l; simpl in *; try lia; auto.
  apply IHn; lia.
Qed.

Lemma sublist_replace_prefix {A} (l: list A) (i: Z) (v: A) :
  0 <= i ->
  sublist 0 i (replace_Znth i v l) = sublist 0 i l.
Proof.
  intros.
  unfold sublist, replace_Znth.
  rewrite firstn_replace_nth_nat.
  reflexivity.
Qed.

Lemma Zlength_replace_Znth {A} (l: list A) (i: Z) (v: A) :
  Zlength (replace_Znth i v l) = Zlength l.
Proof.
  unfold replace_Znth.
  rewrite !Zlength_correct, length_replace_nth.
  reflexivity.
Qed.

Lemma Znth_replace_eq {A} (l: list A) (i: Z) (v d: A) :
  0 <= i < Zlength l ->
  Znth i (replace_Znth i v l) d = v.
Proof.
  intros [Hi0 Hi1].
  unfold replace_Znth, Znth.
  replace (Z.to_nat i) with (Z.to_nat i + 0)%nat by lia.
  apply nth_replace_nth.
  rewrite Zlength_correct in Hi1.
  apply Z2Nat.inj_lt in Hi1; lia.
Qed.

Lemma zeros_succ : forall n, 0 <= n -> zeros (n + 1) = zeros n ++ (0 :: nil).
Proof.
  intros.
  unfold zeros.
  rewrite Z2Nat.inj_add by lia.
  simpl.
  rewrite repeat_app.
  simpl.
  reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* Proofs                                                                 *)
(* ---------------------------------------------------------------------- *)

Lemma proof_of_create_bucks_entail_wit_1 : create_bucks_entail_wit_1.
Proof.
  pre_process.
  Exists content_2 retval.
  rewrite sublist_nil by lia.
  simpl.
  entailer!.
Qed.

Lemma proof_of_create_bucks_entail_wit_2 : create_bucks_entail_wit_2.
Proof.
  pre_process.
  rename H into Hi_lt.
  rename H0 into Hi_nonneg.
  rename H1 into Hi_le.
  rename H2 into Hprefix.
  rename H3 into Hretval.
  Exists (replace_Znth i 0 content_2) bucks_base_2.
  prop_apply PtrArray.full_Zlength; Intros.
  match goal with
  | H : Zlength (replace_Znth _ _ _) = _ |- _ =>
      pose proof H as Hlen_repl
  end.
  pose proof Hlen_repl as Hlen_nat.
  rewrite Zlength_correct in Hlen_nat.
  assert (Hlen : Zlength content_2 = 211) by
    (rewrite <- (Zlength_replace_Znth content_2 i 0); exact Hlen_repl).
  assert (Hsplit: sublist 0 (i + 1) (replace_Znth i 0 content_2) =
                  sublist 0 i (replace_Znth i 0 content_2) ++
                  sublist i (i + 1) (replace_Znth i 0 content_2)) by
    (apply sublist_split; [lia| rewrite Hlen_nat; lia]).
  rewrite Hsplit.
  rewrite (sublist_replace_prefix content_2 i 0) by lia.
  rewrite (sublist_single i (replace_Znth i 0 content_2) 0) by (rewrite Hlen_nat; lia).
  rewrite (Znth_replace_eq content_2 i 0 0) by (rewrite Hlen; lia).
  rewrite Hprefix.
  rewrite zeros_succ by lia.
  entailer!.
Qed.

Lemma proof_of_create_bucks_return_wit_1 : create_bucks_return_wit_1.
Proof.
  pre_process.
  rename H into Hi_ge.
  rename H0 into Hi_nonneg.
  rename H1 into Hi_le.
  rename H2 into Hprefix.
  rename H3 into Hretval.
  assert (i = 211) by lia; subst i.
  prop_apply (PtrArray.full_Zlength bucks_base_2 211 content); Intros.
  match goal with
  | H : Zlength content = _ |- _ => pose proof H as Hlen
  end.
  assert (content = zeros 211).
  { assert (Hsub : sublist 0 211 content = content).
    { apply sublist_self; rewrite Hlen; reflexivity. }
    apply (eq_trans (eq_sym Hprefix)) in Hsub.
    symmetry; exact Hsub. }
  subst content.
  Exists bucks_base_2.
  entailer!.
Qed.

(* -------- init_hashtbl -------- *)

Definition empty_bucket_map (lh: list Z) : Z -> option (Z * list Z) :=
  fun i => if Z_lt_dec i 0 then None
           else if Z_lt_dec i (Zlength lh) then Some (Znth i lh 0, nil)
           else None.

Lemma repr_all_heads_empty lh :
  repr_all_heads lh (empty_bucket_map lh).
Proof.
Admitted.

Lemma contain_all_addrs_empty :
  contain_all_addrs empty_map nil.
Proof.
  unfold contain_all_addrs, empty_map; intros p; split; intros H; try contradiction; simpl in *.
  destruct H as [k Hk]; discriminate.
Qed.

Lemma contain_all_correct_addrs_empty lh :
  contain_all_correct_addrs empty_map (empty_bucket_map lh).
Proof.
  unfold contain_all_correct_addrs, empty_map, empty_bucket_map; intros key p; split; intros H.
  - discriminate.
  - destruct H as [ph [l [Hb Hin]]].
    destruct (Z_lt_dec (hash_string_k key) 0); try lia.
    destruct (Z_lt_dec (hash_string_k key) (Zlength lh)); try lia.
    inversion Hb; subst; simpl in Hin; contradiction.
Admitted.

Lemma proof_of_init_hashtbl_return_wit_1 : init_hashtbl_return_wit_1.
Admitted.

(* -------- create_hashtbl -------- *)

Lemma proof_of_create_hashtbl_return_wit_1 : create_hashtbl_return_wit_1.
Admitted.

(* -------- hashtbl_add -------- *)

Lemma proof_of_hashtbl_add_return_wit_1 : hashtbl_add_return_wit_1. Admitted.
Lemma proof_of_hashtbl_add_return_wit_2 : hashtbl_add_return_wit_2. Admitted.
Lemma proof_of_hashtbl_add_which_implies_wit_1 : hashtbl_add_which_implies_wit_1. Admitted.
Lemma proof_of_hashtbl_add_which_implies_wit_2 : hashtbl_add_which_implies_wit_2. Admitted.
