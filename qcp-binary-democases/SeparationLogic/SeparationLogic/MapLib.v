Require Import Coq.Strings.String.
Require Import Coq.Init.Datatypes.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Import ListNotations.
Local Open Scope list.

Export naive_C_Rules.
Local Open Scope sac.

Definition store_map {A B: Type} (P: A -> B -> Assertion) (m: A -> option B): Assertion :=
  EX l: list A,
    [| forall a, In a l <-> exists b, m a = Some b |] &&
    [| NoDup l |] &&
    iter_sepcon
      (map (fun a => match m a with Some b => P a b | None => emp end) l).

Definition store_map_missing_i {A B: Type} (P: A -> B -> Assertion) (m: A -> option B) (i:A): Assertion :=
  EX l: list A,
    [| forall a, In a l <-> (exists b, m a = Some b ) /\ a <> i |] &&
    [| NoDup l |] &&
    iter_sepcon
      (map (fun a => match m a with Some b => P a b | None => emp end) l).

Lemma store_map_split:
  forall {A B: Type} (P: A -> B -> Assertion) (a: A) (b: B) (m: A -> option B),
    m a = Some b ->
    store_map P m |-- store_map_missing_i P m a ** P a b.
Proof.
  intros.
  unfold store_map, store_map_missing_i.
  Intros l.
  assert (In a l). {
    apply H0.
    eauto.
  }
  apply in_split in H2.
  destruct H2 as [l1 [l2 ?] ].
  Exists (l1 ++ l2).
  entailer!.
  + subst l.
    change (l1 ++ a :: l2) with (l1 ++ (a :: nil) ++ l2).
    rewrite !map_app.
    rewrite !derivable1_sepcon_iter_sepcon2.
    rewrite <- derivable1_sepcon_iter_sepcon1.
    entailer!.
    rewrite derivable1_iter_sepcon_l.
    simpl.
    rewrite H.
    entailer!.
  + subst l.
    apply NoDup_remove in H1.
    tauto.
  + intros.
    subst l.
    apply NoDup_remove in H1.
    specialize (H0 a0).
    rewrite in_app_iff in *.
    simpl in H0.
    rewrite <- H0.
    assert (a = a0 <-> a0 = a) by (split; intros; congruence).
    assert (a = a0 -> ~ (In a0 l1 \/ In a0 l2)) by (intros; subst; tauto).
    tauto.
Qed.

Lemma store_map_merge:
  forall {A B: Type} (P: A -> B -> Assertion) (a: A) (b: B) (m: A -> option B),
    m a = Some b ->
    store_map_missing_i P m a ** P a b |-- store_map P m.
Proof.
  intros.
  unfold store_map, store_map_missing_i.
  Intros l.
  Exists ((a :: nil) ++ l).
  entailer!.
  + rewrite !map_app.
    rewrite <- derivable1_sepcon_iter_sepcon1.
    entailer!.
    rewrite <- derivable1_iter_sepcon_r.
    simpl.
    rewrite H.
    entailer!.
  + simpl; constructor.
    - rewrite H0.
      tauto.
    - tauto.
  + intros.
    simpl.
    rewrite H0.
    assert (a = a0 <-> a0 = a) by (split; intros; congruence).
    assert (a = a0 -> exists b0, m a0 = Some b0) by (intros; subst; eauto).
    tauto.
Qed.

Lemma store_map_missing_equiv_store_map :
  forall {A B: Type} (P: A -> B -> Assertion) (m: A -> option B) (a: A),
    m a = None ->
    store_map_missing_i P m a |-- store_map P m.
Proof.
  intros.
  unfold store_map, store_map_missing_i.
  Intros l.
  Exists l.
  entailer!.
  intros.
  rewrite H0.
  split;  intros ; destruct H2; auto.
  split.
  - exists x. auto.
  - intro. subst. rewrite H in H2. inversion H2.
Qed.

Lemma store_map_equiv_store_map_missing :
  forall {A B: Type} (P: A -> B -> Assertion) (m: A -> option B) (a: A),
    m a = None ->
    store_map P m |-- store_map_missing_i P m a .
Proof.
  intros.
  unfold store_map, store_map_missing_i.
  Intros l.
  Exists l.
  entailer!.
  intros.
  rewrite H0.
  split;  intros ; destruct H2; auto.
  split.
  - exists x. auto.
  - intro. subst. rewrite H in H2. inversion H2.
Qed.

Lemma store_map_equiv :
  forall {A B: Type} (P: A -> B -> Assertion) (m m1: A -> option B),
    (forall a, m a = m1 a) ->
    store_map P m --||-- store_map P m1.
Proof.
  intros.
  unfold store_map.
  split; Intros l ; Exists l; entailer!.
  - assert (map (fun a : A => match m a with
                               | Some b => P a b
                               | None => emp
                               end) l =
            map (fun a : A => match m1 a with
                               | Some b => P a b
                               | None => emp
                               end) l). {
      apply map_ext_in.
      intros.
      rewrite H.
      auto.
    }
    rewrite H2. entailer!.
  - intros. rewrite H0. rewrite H. reflexivity.
  - assert (map (fun a : A => match m a with
                                | Some b => P a b
                                | None => emp
                              end) l =
            map (fun a : A => match m1 a with
                                | Some b => P a b
                                | None => emp
                              end) l). {
        apply map_ext_in.
        intros.
        rewrite H.
        auto.
    }
    rewrite H2. entailer!.
  - intros. rewrite H0. rewrite H. reflexivity.
Qed.

Lemma store_map_missing_i_equiv :
  forall {A B: Type} (P: A -> B -> Assertion) (m m1: A -> option B) (i : A),
    (forall a, (a <> i) -> m a = m1 a) ->
    store_map_missing_i P m i --||-- store_map_missing_i P m1 i.
Proof.
  intros.
  unfold store_map_missing_i.
  split; Intros l ; Exists l; entailer!.
  - assert (map (fun a : A => match m a with
                               | Some b => P a b
                               | None => emp
                               end) l =
            map (fun a : A => match m1 a with
                               | Some b => P a b
                               | None => emp
                               end) l). {
      apply map_ext_in.
      intros. rewrite H0 in H2.
      rewrite H;
      auto.
      apply H2.
    }
    rewrite H2. entailer!.
  - intros. split; intros.
    + apply H0 in H2. rewrite H in H2 ; auto. apply H2.
    + apply H0. rewrite H ; auto. apply H2.
  - assert (map (fun a : A => match m a with
                                | Some b => P a b
                                | None => emp
                              end) l =
            map (fun a : A => match m1 a with
                                | Some b => P a b
                                | None => emp
                              end) l). {
        apply map_ext_in.
        intros. rewrite H0 in H2.
        rewrite H;
        auto.
        apply H2.
    }
    rewrite H2. entailer!.
  - intros. split; intros.
    + apply H0 in H2. rewrite H; auto. apply H2.
    + apply H0. rewrite H in H2; auto. apply H2.
Qed.