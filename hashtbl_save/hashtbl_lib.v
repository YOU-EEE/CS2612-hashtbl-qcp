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
From SimpleC.SL Require Import Mem SeparationLogic MapLib.
Require Import Logic.LogicGenerator.demo932.Interface.
From compcert.lib Require Import Integers.
Local Open Scope Z_scope.
Local Open Scope sets.
Import ListNotations.
Local Open Scope list.
Require Import String.
Local Open Scope string.

Import naive_C_Rules.
Local Open Scope sac.

(** ********* Assumptions ********* *)

Parameter hash_string_k: list Z -> Z.
Axiom hash_string_in_range:
  forall l, 0 <= hash_string_k l <= Int.max_unsigned.
Parameter store_string: addr -> list Z -> Assertion.

Module KP.
Parameter insert_map:
  (list Z -> option addr) -> list Z -> addr -> (list Z -> option addr).
Axiom insert_map_same:
  forall m k v, insert_map m k v k = Some v.
Axiom insert_map_diff:
  forall m k1 k2 v, k1 <> k2 -> insert_map m k1 v k2 = m k2.
Parameter remove_map:
  (list Z -> option addr) -> list Z -> (list Z -> option addr).
Axiom remove_map_same:
  forall m k, remove_map m k k = None.
Axiom remove_map_diff:
  forall m k1 k2, k1 <> k2 -> remove_map m k1 k2 = m k2.
End KP.

Module PV.
Parameter insert_map:
  (addr -> option Z) -> addr -> Z -> (addr -> option Z).
Axiom insert_map_same:
  forall m k v, insert_map m k v k = Some v.
Axiom insert_map_diff:
  forall m k1 k2 v, k1 <> k2 -> insert_map m k1 v k2 = m k2.
Parameter remove_map:
  (addr -> option Z) -> addr -> (addr -> option Z).
Axiom remove_map_same:
  forall m k, remove_map m k k = None.
Axiom remove_map_diff:
  forall m k1 k2, k1 <> k2 -> remove_map m k1 k2 = m k2.
End PV.

(** ********* Definitions ********* *)

Definition NBUCK: Z := 211.

Fixpoint sll (x: addr) (l: list addr): Assertion :=
  match l with
    | nil      => [| x = NULL |] && emp
    | x0 :: l0 => [| x <> NULL |] && [| x = x0 |] &&
                  EX y: addr,
                   &(x # "blist" ->ₛ "next") # Ptr |-> y **
                   sll y l0
  end.

Fixpoint sllseg (x y: addr) (l: list addr): Assertion :=
  match l with
    | nil      => [| x = y |] && emp
    | x0 :: l0 => [| x <> NULL |] && [| x = x0 |] &&
                  EX z: addr,
                    &(x # "blist" ->ₛ "next") # Ptr |-> z **
                    sllseg z y l0
  end.

Fixpoint sllbseg (x y: addr) (l: list addr): Assertion :=
  match l with
    | nil      => [| x = y |] && emp
    | x0 :: l0 => [| x0 <> NULL |] &&
                    x # Ptr |-> x0 **
                    sllbseg (&(x0 # "blist" ->ₛ "next")) y l0
  end.

Fixpoint dll (x x_up: addr) (l: list addr): Assertion :=
  match l with
    | nil      => [| x = NULL |] && emp
    | x0 :: l0 => [| x <> NULL |] && [| x = x0 |] &&
                  EX x_down: addr,
                    &(x # "blist" ->ₛ "down") # Ptr |-> x_down **
                    &(x # "blist" ->ₛ "up") # Ptr |-> x_up **
                    dll x_down x l0
  end.

Fixpoint dllseg (x y x_up y_up: addr) (l: list addr): Assertion :=
  match l with
    | nil      => [| x = y |] && [| x_up = y_up |] &&
                  emp
    | x0 :: l0 => [| x <> NULL |] && [| x = x0 |] &&
                  EX x_down: addr,
                    &(x # "blist" ->ₛ "down") # Ptr |-> x_down **
                    &(x # "blist" ->ₛ "up") # Ptr |-> x_up **
                    dllseg x_down y x y_up l0
  end.

Definition store_sll (n: Z): addr * list addr -> Assertion :=
  fun '(p, l) => sll p l.

Definition store_name (k: list Z) (p: addr): Assertion :=
  store_string (&(p # "blist" ->ₛ "key")) k.

Definition store_val (v: Z) (p: addr) : Assertion :=
  &(p # "blist" ->ₛ "val") # UInt |-> v. (* 或者是 Int 类型 *)

Definition contain_all_addrs (m: list Z -> option addr) (l: list addr) :=
  forall p: addr,
    (exists key: list Z, m key = Some p) <-> In p l.

Definition repr_all_heads
             (lh: list addr)
             (b: Z -> option (addr * list addr)): Prop :=
  forall i p,
    (exists l, b i = Some (p, l)) <->
    (0 <= i < Zlength lh /\ Znth i lh 0 = p).

Definition contain_all_correct_addrs
             (m: list Z -> option addr)
             (b: Z -> option (addr * list addr)): Prop :=
  forall key p,
    (m key = Some p) <->
    (exists ph l, b (hash_string_k key) = Some (ph, l) /\ In p l).

Definition store_hash_skeleton (x: addr) (m: list Z -> option addr): Assertion :=
  EX (l lh: list addr) (b: Z -> option (addr * list addr)) (top bucks: addr),
    [| contain_all_addrs m l |] &&
    [| repr_all_heads lh b |] &&
    [| contain_all_correct_addrs m b |] &&
    &(x # "hashtbl" ->ₛ "top") # Ptr |-> top ** dll top NULL l **
    &(x # "hashtbl" ->ₛ "bucks") # Ptr |-> bucks ** PtrArray.full bucks NBUCK lh **
    store_map store_sll b **
    store_map store_name m.

Definition map_compose
             {A B C: Type}
             (m1: A -> option B)
             (m2: B -> option C)
             (m: A -> option C): Prop :=
  (forall a,
    (m1 a = None /\ m a = None) \/
    (exists b c, m1 a = Some b /\ m2 b = Some c /\ m a = Some c)) /\
  (forall b,
    m2 b = None /\ (forall a, m1 a <> Some b) \/
    exists a c, m1 a = Some b /\ m2 b = Some c).

Definition map_composable
             {A B C: Type}
             (m1: A -> option B)
             (m2: B -> option C): Prop :=
  (forall a,
    m1 a = None \/
    (exists b c, m1 a = Some b /\ m2 b = Some c)) /\
  (forall b,
    m2 b = None /\ (forall a, m1 a <> Some b) \/
    exists a c, m1 a = Some b /\ m2 b = Some c).

Definition store_hashtbl (x: addr) (m: list Z -> option Z): Assertion :=
  EX (m1: list Z -> option addr) (m2: addr -> option Z),
    [| map_compose m1 m2 m |] &&
    store_hash_skeleton x m1 **
    store_map store_uint m2.

Definition empty_map {Key Value: Type}: Key -> option Value := fun _ => None.

(** ********* Proofs ********* *)

Lemma sll_zero: forall x l,
  x = NULL ->
  sll x l |-- [| l = nil |] && emp.
Proof.
  intros.
  destruct l.
  + entailer!.
  + simpl.
    Intros. Intros x0.
    entailer!.
Qed.

Lemma sll_not_zero: forall x l,
  x <> NULL ->
  sll x l |--
    EX y l0,
      [| l = x :: l0 |] &&
      &(x # "blist" ->ₛ "next") # Ptr |-> y **
      sll y l0.
Proof.
  intros.
  destruct l.
  + simpl.
    Intros.
    tauto.
  + simpl. Intros.
    Intros y.
    Exists y l.
    subst.
    entailer!.
Qed.

Lemma sll_not_zero': forall x l,
  x <> NULL ->
  sll x l |-- [| l <> nil |].
Proof.
  intros.
  destruct l.
  + simpl.
    Intros.
    tauto.
  + simpl. Intros.
    Intros y.
    entailer!.
    congruence.
Qed.

Lemma sllseg_len1: forall x y,
  x <> NULL ->
  &(x # "blist" ->ₛ "next") # Ptr |-> y |--
  sllseg x y [x].
Proof.
  intros.
  simpl sllseg.
  Exists y.
  entailer!.
Qed.

Lemma sllseg_sllseg: forall x y z l1 l2,
  sllseg x y l1 ** sllseg y z l2 |--
  sllseg x z (l1 ++ l2).
Proof.
  intros.
  revert x; induction l1; simpl sllseg; intros.
  + Intros.
    subst y.
    entailer!.
  + Intros. Intros z0.
    Exists z0.
    sep_apply IHl1.
    entailer!.
Qed.

Lemma sllseg_sll: forall x y l1 l2,
  sllseg x y l1 ** sll y l2 |--
  sll x (l1 ++ l2).
Proof.
  intros.
  revert x; induction l1; simpl sllseg; simpl sll; intros.
  + Intros.
    subst y.
    entailer!.
  + Intros. Intros z0.
    Exists z0.
    sep_apply IHl1.
    entailer!.
Qed.

Lemma sllbseg_2_sllseg: forall x y z l,
  sllbseg x y l ** y # Ptr |-> z |--
  EX y': addr, x # Ptr |-> y' ** sllseg y' z l.
Proof.
  intros.
  revert x; induction l; simpl; intros.
  + Intros.
    subst x.
    Exists z; entailer!.
  + Intros.
    sep_apply (IHl (&( a # "blist" ->ₛ "next"))).
    Intros y'.
    Exists a y'.
    entailer!.
Qed.

Lemma sllbseg_len1: forall (x y: addr),
  y <> 0 ->
  x # Ptr |-> y  |--
  sllbseg x (&( y # "blist" ->ₛ "next")) [y].
Proof.
  intros.
  simpl.
  entailer!.
Qed.

Lemma sllbseg_sllbseg: forall x y z l1 l2,
  sllbseg x y l1 ** sllbseg y z l2 |--
  sllbseg x z (l1 ++ l2).
Proof.
  intros.
  revert x; induction l1; simpl; intros.
  + entailer!.
    subst x.
    entailer!.
  + entailer!.
Qed.

Lemma sllseg_0_sll: forall x l,
  sllseg x 0 l |-- sll x l.
Proof.
  intros. revert x. 
  induction l; try easy.
  simpl. intros. 
  Intros z. Exists z. entailer!.
Qed.

Lemma sll2sllseg: forall x l,
  sll x l |-- sllseg x NULL l.
Proof.
  intros.
  revert x; induction l; simpl; intros.
  + entailer!.
  + Intros y; Exists y; entailer!.
Qed.

Lemma sllseg_not_in: forall x x' y z l,
  &(x # "blist" ->ₛ "next") # Ptr |-> x' **
  sllseg y z l |--
  [| ~ In x l |].
Proof.
  intros.
  revert y; induction l; simpl; intros.
  + entailer!.
  + Intros y'.
    subst a.
    prop_apply (IHl y').
    destruct (Classical_Prop.classic (y = x)).
    - subst y.
      Intros.
      prop_apply (dup_store_ptr (&(x # "blist" ->ₛ "next")) x' y').
      entailer!.
    - entailer!.
      tauto.
Qed.

Lemma sllseg_nodup: forall x y l,
  sllseg x y l |-- [| NoDup l |].
Proof.
  intros.
  revert x; induction l; simpl; intros.
  + entailer!.
    apply NoDup_nil.
  + Intros x'.
    prop_apply IHl.
    Intros.
    prop_apply sllseg_not_in.
    entailer!.
    subst.
    apply NoDup_cons; tauto.
Qed.

Lemma sll_nodup: forall x l,
  sll x l |-- [| NoDup l |].
Proof.
  intros.
  sep_apply sll2sllseg.
  prop_apply sllseg_nodup.
  entailer!.
Qed.

Lemma dllseg_len1: forall (x x_up x_down: addr),
  x <> NULL ->
  &(x # "blist" ->ₛ "down") # Ptr |-> x_down **
  &(x # "blist" ->ₛ "up") # Ptr |-> x_up |--
  dllseg x x_down x_up x [x].
Proof.
  intros.
  simpl.
  Exists x_down.
  entailer!.
Qed.

Lemma dllseg_dllseg: forall (x y z x_up y_up z_up: addr) l1 l2,
  dllseg x y x_up y_up l1 **
  dllseg y z y_up z_up l2 |--
  dllseg x z x_up z_up (l1 ++ l2).
Proof.
  intros.
  revert x x_up; induction l1; simpl; intros.
  + Intros.
    subst.
    entailer!.
  + Intros u.
    Exists u.
    sep_apply IHl1.
    entailer!.
Qed.

Lemma dllseg_head_zero: forall x y x_up y_up l,
  x = 0 ->
  dllseg x y x_up y_up l |--
  [| y = 0 |] && [| x_up = y_up |] && [| l = nil |] && emp.
Proof.
  intros.
  destruct l; simpl.
  + entailer!.
  + Intros x0.
    tauto.
Qed.

Lemma dllseg_head_neq: forall x y x_up y_up l,
  x <> y ->
  dllseg x y x_up y_up l |--
  EX z l0,
    [| l = x :: l0 |] &&
    &(x # "blist" ->ₛ "down") # Ptr |-> z **
    &(x # "blist" ->ₛ "up") # Ptr |-> x_up **
    dllseg z y x y_up l0.
Proof.
  intros.
  destruct l; simpl.
  + entailer!.
  + Intros z0.
    Exists z0 l.
    subst.
    entailer!.
Qed.

Lemma dllseg_head_neq_destruct_tail_aux: forall x y x_up y_up l,
  dllseg x y x_up y_up l |--
  [| x = y |] && [| x_up = y_up |] && [| l = nil |] && emp ||
  EX z l0,
    [| y_up <> 0 |] &&
    [| l = (l0 ++ y_up :: nil)%list |] &&
    dllseg x y_up x_up z l0 **
    &(y_up # "blist" ->ₛ "down") # Ptr |-> y **
    &(y_up # "blist" ->ₛ "up") # Ptr |-> z.
Proof.
  intros.
  revert x x_up; induction l; simpl; intros.
  + rewrite <- derivable1_orp_intros1.
    entailer!.
  + rewrite <- derivable1_orp_intros2.
    Intros z.
    sep_apply IHl.
    rewrite derivable1_wand_sepcon_adjoint.
    apply derivable1_orp_elim; rewrite <- derivable1_wand_sepcon_adjoint.
    - Intros.
      Exists x_up nil.
      subst.
      simpl.
      entailer!.
    - Intros z0 l0.
      Exists z0 (a :: l0).
      sep_apply (dllseg_len1 x); [ | tauto ].
      sep_apply (dllseg_dllseg x).
      subst l.
      simpl app.
      entailer!.
      subst.
      reflexivity.
Qed.

Lemma dllseg_head_neq_destruct_tail: forall x y x_up y_up l,
  x <> y ->
  dllseg x y x_up y_up l |--
  EX z l0,
    [| y_up <> 0 |] &&
    [| l = (l0 ++ y_up :: nil)%list |] &&
    dllseg x y_up x_up z l0 **
    &(y_up # "blist" ->ₛ "down") # Ptr |-> y **
    &(y_up # "blist" ->ₛ "up") # Ptr |-> z.
Proof.
  intros.
  sep_apply dllseg_head_neq_destruct_tail_aux.
  apply derivable1_orp_elim.
  + Intros.
    tauto.
  + entailer!.
Qed.

Lemma dll_zero : forall (x x_up : addr) (l : list Z),
  x = NULL ->
  dll x x_up l |-- [| l = nil|] && emp.
Proof.
  intros.
  destruct l.
  + entailer!.
  + simpl.
    Intros. Intros x0.
    entailer!.
Qed.

Lemma dll_not_zero: forall x x_up l,
  x <> NULL ->
  dll x x_up l |--
    EX y l0,
      [| l = x :: l0 |] &&
      &(x # "blist" ->ₛ "down") # Ptr |-> y **
      &(x # "blist" ->ₛ "up") # Ptr |-> x_up **
      dll y x l0.
Proof.
  intros.
  destruct l.
  + simpl.
    Intros.
    tauto.
  + simpl. Intros.
    Intros y.
    Exists y l.
    subst.
    entailer!.
Qed.

Lemma dllseg_dll : forall x y x_up y_up l1 l2,
  dllseg x y x_up y_up l1 ** dll y y_up l2 |-- dll x x_up (l1 ++ l2).
Proof.
  intros.
  revert x y x_up y_up l2.
  induction l1 ; simpl in * ; intros ; auto.
  - entailer!. subst. entailer!.
  - Intros z. 
    Exists z. entailer!.
Qed.

Lemma dll2dllseg: forall x x_up l,
  dll x x_up l |-- EX y_up, dllseg x NULL x_up y_up l.
Proof.
  intros.
  revert x x_up; induction l; simpl; intros.
  + Exists x_up. entailer!.
  + Intros x_down.
    sep_apply IHl.
    Intros y_up.
    Exists y_up x_down; entailer!.
Qed.

Lemma dllseg_not_in: forall x x_down y z y_up z_up l,
  &(x # "blist" ->ₛ "down") # Ptr |-> x_down **
  dllseg y z y_up z_up l |--
  [| ~ In x l |].
Proof.
  intros.
  revert y y_up; induction l; simpl; intros.
  + entailer!.
  + Intros y_down.
    subst a.
    prop_apply (IHl y_down).
    destruct (Classical_Prop.classic (y = x)).
    - subst y.
      Intros.
      prop_apply (dup_store_ptr (&(x # "blist" ->ₛ "down")) x_down y_down).
      entailer!.
    - entailer!.
      tauto.
Qed.

Lemma dllseg_nodup: forall x y x_up y_up l,
  dllseg x y x_up y_up l |-- [| NoDup l |].
Proof.
  intros.
  revert x x_up; induction l; simpl; intros.
  + entailer!.
    apply NoDup_nil.
  + Intros x_down.
    prop_apply IHl.
    Intros.
    prop_apply dllseg_not_in.
    entailer!.
    subst.
    apply NoDup_cons; tauto.
Qed.

Lemma dll_nodup: forall x x_up l,
  dll x x_up l |-- [| NoDup l |].
Proof.
  intros.
  sep_apply dll2dllseg.
  Intros y_up.
  prop_apply dllseg_nodup.
  entailer!.
Qed.
