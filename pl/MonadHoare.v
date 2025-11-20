Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import PL.Syntax.
Require Import PL.DenotationsOfExpr.
Require Import PL.DenotationsAsRels.
Require Import PL.Monad.
Require Import PL.Kleene.
Require Import PL.FixedPoint.
Local Open Scope string.
Local Open Scope Z.
Local Open Scope sets.

(** * 单子程序上的霍尔逻辑 *)

Module SetMonadHoare.
Import Monad
       MonadNotation
       SetMonadExamples0
       SetMonadExamples2
       SetMonadExamples3
       KleeneFix Sets_CPO.
Local Open Scope monad.


(** 集合单子上，霍尔三元组会退化为霍尔二元组。*)

Definition Hoare {A: Type} (c: SetMonad.M A) (P: A -> Prop): Prop :=
  forall a, a ∈ c -> P a.

(** 可以证明，各个单子算子满足下面性质。*)

Theorem Hoare_bind {A B: Type}:
  forall (f: SetMonad.M A)
         (g: A -> SetMonad.M B)
         (P: A -> Prop)
         (Q: B -> Prop),
    Hoare f P ->
    (forall a, P a -> Hoare (g a) Q) ->
    Hoare (bind f g) Q.
Proof.
  intros.
  unfold Hoare; sets_unfold;
  unfold bind, set_monad, SetMonad.bind.
  intros b [a [? ?]].
  specialize (H _ H1).
  specialize (H0 _ H _ H2).
  tauto.
Qed.

Theorem Hoare_ret {A: Type}:
  forall (a: A) (P: A -> Prop),
    P a -> Hoare (ret a) P.
Proof.
  intros.
  unfold Hoare, ret, set_monad, SetMonad.ret; sets_unfold.
  intros.
  rewrite <- H0; tauto.
Qed.

Theorem Hoare_conseq {A: Type}:
  forall (f: SetMonad.M A) (P Q: A -> Prop),
    (forall a, P a -> Q a) ->
    Hoare f P ->
    Hoare f Q.
Proof.
  unfold Hoare; intros.
  specialize (H a).
  specialize (H0 a).
  tauto.
Qed.

Theorem Hoare_conjunct {A: Type}:
  forall (f: SetMonad.M A) (P Q: A -> Prop),
    Hoare f P ->
    Hoare f Q ->
    Hoare f (fun a => P a /\ Q a).
Proof.
  unfold Hoare; intros.
  specialize (H a).
  specialize (H0 a).
  tauto.
Qed.

Theorem Hoare_choice {A: Type}:
  forall (f g: SetMonad.M A)
         (P: A -> Prop),
    Hoare f P ->
    Hoare g P ->
    Hoare (choice f g) P.
Proof.
  intros.
  unfold Hoare; sets_unfold; unfold choice; Sets_unfold.
  intros.
  destruct H1; [apply H | apply H0]; tauto.
Qed.

Theorem Hoare_assume_bind {A: Type}:
  forall (P: Prop)
         (f: SetMonad.M A)
         (Q: A -> Prop),
    (P -> Hoare f Q) ->
    (Hoare (assume P;; f) Q).
Proof.
  intros.
  apply (Hoare_bind _ _ (fun _ => P)).
  + unfold Hoare, assume; sets_unfold.
    tauto.
  + tauto.
Qed.

Lemma Hoare_Kleene_LFix {A B: Type}:
  forall (a: A)
         (Q: B -> Prop)
         (f: (A -> SetMonad.M B) -> (A -> SetMonad.M B)),
    (forall n, Hoare (Nat.iter n f ∅ a) Q) ->
    Hoare (Kleene_LFix f a) Q.
Proof.
  intros.
  unfold Hoare.
  intros b HFix.
  change (b ∈ (⋃ (fun n => Nat.iter n f ∅ a))) in HFix.
  change (exists n, b ∈ Nat.iter n f ∅ a) in HFix.
  destruct HFix as [n ?].
  unfold Hoare in H.
  pose proof H n b H0.
  tauto.
Qed.

Lemma Hoare_repeat_break_aux {A B: Type}:
  forall (body: A -> SetMonad.M (ContinueOrBreak A B))
         (P: A -> Prop)
         (Q: B -> Prop),
    (forall a, P a ->
               Hoare (body a) (fun x => match x with
                                        | by_continue a => P a
                                        | by_break b => Q b
                                        end)) ->
    (forall n a, P a ->
                 Hoare (Nat.iter n (repeat_break_f body) ∅ a) Q).
Proof.
  intros body P Q H n.
  induction n; intros; simpl.
  + unfold Hoare; sets_unfold; intros; tauto.
  + unfold repeat_break_f at 1.
    eapply Hoare_bind.
    - apply H, H0.
    - intros [a0 | b0].
      * apply IHn.
      * apply Hoare_ret.
Qed.

Theorem Hoare_repeat_break {A B: Type}:
  forall (body: A -> SetMonad.M (ContinueOrBreak A B))
         (P: A -> Prop)
         (Q: B -> Prop),
    (forall a, P a ->
               Hoare (body a) (fun x => match x with
                                        | by_continue a => P a
                                        | by_break b => Q b
                                        end)) ->
    (forall a, P a -> Hoare (repeat_break body a) Q).
Proof.
  intros.
  change (Hoare (Kleene_LFix (repeat_break_f body) a) Q).
  apply Hoare_Kleene_LFix.
  intros.
  pose proof Hoare_repeat_break_aux body P Q H.
  pose proof H1 n a H0.
  tauto.
Qed.

(** * 霍尔逻辑证明 *)

Theorem functional_correctness_3x1:
  forall n: Z,
    n >= 1 ->
    Hoare (run_3x1 n) (fun m => m = 1).
Proof.
  apply Hoare_repeat_break.
  intros.
  unfold body_3x1.
  repeat apply Hoare_choice.
  + apply Hoare_assume_bind.
    intros.
    apply Hoare_ret.
    lia.
  + apply Hoare_assume_bind.
    intros.
    apply Hoare_ret.
    destruct H0 as [? ?].
    subst a.
    rewrite Z.mul_comm, Z_div_mult_full by lia.
    lia.
  + apply Hoare_assume_bind.
    intros.
    apply Hoare_ret.
    lia.
Qed.

Theorem functional_correctness_binary_search:
  forall (P: Z -> Prop) lo hi,
    (forall n m, n <= m -> P m -> P n) ->
    P lo ->
    ~ P hi ->
    Hoare (binary_search P lo hi)
          (fun x => P x /\ ~ P (x + 1)).
Proof.
  intros.
  apply (Hoare_repeat_break _
           (fun '(lo, hi) => P lo /\ ~ P hi)); [| tauto].
  clear lo hi H0 H1.
  intros [lo hi] [? ?].
  unfold body_binary_search.
  apply Hoare_choice.
  + apply Hoare_assume_bind.
    intros.
    apply Hoare_ret.
    subst hi; tauto.
  + apply Hoare_assume_bind.
    intros.
    apply Hoare_choice; apply Hoare_assume_bind; intros.
    - apply Hoare_ret.
      tauto.
    - apply Hoare_ret.
      tauto.
Qed.

End SetMonadHoare.
