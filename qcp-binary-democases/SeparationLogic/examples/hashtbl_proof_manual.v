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
From SimpleC.SL Require Import Mem SeparationLogic MapLib CommonAssertion.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import hashtbl_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import hashtbl_lib.
Local Open Scope sac.

Module BV.
  Definition insert_map {A} (m: Z -> option A) (k: Z) (v: A) : Z -> option A :=
    fun x => if Z.eq_dec x k then Some v else m x.

  Lemma insert_map_same {A} : forall (m: Z -> option A) k v,
    insert_map m k v k = Some v.
  Proof.
    intros. unfold insert_map. destruct (Z.eq_dec k k); congruence.
  Qed.

  Lemma insert_map_diff {A} : forall (m: Z -> option A) k1 k2 v,
    k1 <> k2 -> insert_map m k1 v k2 = m k2.
  Proof.
    intros. unfold insert_map. destruct (Z.eq_dec k2 k1); congruence.
  Qed.

  Lemma insert_map_iff {A} : forall (m: Z -> option A) k v p,
    insert_map m k v p <> None <-> (p = k \/ m p <> None).
  Proof.
    intros. unfold insert_map. destruct (Z.eq_dec p k).
    - subst. split; intros.
      + left; auto.
      + congruence.
    - split; intros.
      + right. auto.
      + destruct H; try congruence.
  Qed.
End BV.





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

Lemma store_map_empty :
  forall {A B} (P: A -> B -> Assertion),
    store_map P (@empty_map A B) --||-- emp.
Proof.
  intros A B P.
  unfold store_map, empty_map.
  unfold logic_equiv, derivable1.
  unfold exp, andp, coq_prop, iter_sepcon, emp.
  split.
  - intros st H.
    destruct H as [l [[HIn HNoDup] HIter]].
    destruct l.
    + exact HIter.
    + exfalso.
      match goal with
      | HIn0: (forall x, In x (?hd :: ?tl) <-> exists b, None = Some b) |- _ =>
          pose proof (HIn0 hd) as Hhd;
          assert (In hd (hd :: tl)) as Hin by (simpl; auto);
          apply Hhd in Hin;
          destruct Hin as [b Hb];
          discriminate Hb
      end.
  - intros st Hemp.
    exists (@nil A).
    split.
    + split.
      * intros a; split; intros Hin.
        { inversion Hin. }
        { destruct Hin as [b Hb]. discriminate Hb. }
      * constructor.
    + exact Hemp.
Qed.

Lemma dup_store_uint : forall p v1 v2,
  p # UInt |-> v1 ** p # UInt |-> v2 |-- [| False |].
Proof.
  intros.
  sep_apply store_uint_undef_store_uint.
  sep_apply store_uint_undef_store_uint.
  unfold undef_store_uint.
  eapply derivable1_trans.
  2: apply (dup_store_4bytes_noninit p).
  entailer!.
Qed.

Lemma dup_store_val : forall p v1 v2,
  store_val p v1 ** store_val p v2 |-- [| False |].
Proof.
  intros.
  unfold store_val.
  apply dup_store_uint.
Qed.

Lemma store_val_to_field : forall p v,
  store_val p v |-- (&(p # "blist" ->ₛ "val")) # UInt |-> v.
Proof.
  intros.
  unfold store_val.
  entailer!.
Qed.

Lemma store_val_from_field : forall p v,
  (&(p # "blist" ->ₛ "val")) # UInt |-> v |-- store_val p v.
Proof.
  intros.
  unfold store_val.
  entailer!.
Qed.

(* Axiom store_name_from_key :
  forall p key_pre k,
    &(p # "blist" ->ₛ "key") # Ptr |-> key_pre ** store_string key_pre k
    |-- store_name k p. *)

(* Axiom dll_singleton_from_fields :
  forall x x_up x_down,
    x <> NULL ->
    &(x # "blist" ->ₛ "down") # Ptr |-> x_down **
    &(x # "blist" ->ₛ "up") # Ptr |-> x_up
    |-- dll x x_up (x :: nil). *)

Lemma store_hash_skeleton_intro :
  forall (x: addr) (m: list Z -> option addr)
         (l lh: list addr) (b: Z -> option (addr * list addr))
         (top bucks: addr),
    (&(x # "hashtbl" ->ₛ "top") # Ptr |-> top **
     &(x # "hashtbl" ->ₛ "bucks") # Ptr |-> bucks) **
    PtrArray.full bucks 211 lh
    |-- store_hash_skeleton x m.
Proof.
  pre_process.
  unfold store_hash_skeleton.
Abort.


Definition hash_skeleton_inputs
           (x: addr) (l lh: list addr) (b: Z -> option (addr * list addr))
           (top bucks old_top old_down old_up next: addr)
           (m: list Z -> option addr) : Assertion :=
  (((((((( &(x # "hashtbl" ->ₛ "top") # Ptr |-> top **
           dll top NULL l) **
          &(x # "hashtbl" ->ₛ "bucks") # Ptr |-> bucks) **
         PtrArray.full bucks 211 lh) **
        store_map store_sll b) **
       store_map store_name m) **
      &(old_top # "blist" ->ₛ "down") # Ptr |-> old_down) **
     &(old_top # "blist" ->ₛ "up") # Ptr |-> old_up) **
    &(top # "blist" ->ₛ "next") # Ptr |-> next).


Lemma dll_head_exists_with_TT :
  forall x y l,
    x <> NULL ->
    dll x y l |-- EX x_down x_up l_tail,
      [| l = x :: l_tail |] &&
      &(x # "blist" ->ₛ "down") # Ptr |-> x_down **
      &(x # "blist" ->ₛ "up") # Ptr |-> x_up **
      TT.
Proof.
  intros x y l Hx.
  sep_apply (dll_not_zero x y l Hx).
  Intros x_down l_tail.
  Exists x_down y l_tail.
  entailer!.
  apply derivable1_truep_intros.
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




Lemma proof_of_init_hashtbl_return_wit_1 : init_hashtbl_return_wit_1.
Proof.
  pre_process.
  sep_apply (store_hash_skeleton_intro h_pre empty_map nil (zeros 211) empty_map 0 bucks_base).
  entailer!.
Qed.

(* -------- create_hashtbl -------- *)

Lemma proof_of_create_hashtbl_return_wit_1 : create_hashtbl_return_wit_1.
Proof.
  pre_process.
  apply derivable1s_emp_sepcon_unfold.
  - apply derivable1_refl.
  - setoid_rewrite <- (store_map_empty store_val).
    entailer!.
Qed.

(* -------- hashtbl_add -------- *)

Lemma proof_of_hashtbl_add_entail_wit_1 : hashtbl_add_entail_wit_1.
Proof.
  pre_process.
  entailer!.
  - pose proof (Z.rem_bound_pos retval 211) as Hrem.
    lia.
  - pose proof (Z.rem_nonneg retval 211) as Hrem.
    lia.
Qed. 


Lemma proof_of_hashtbl_add_return_wit_1 : hashtbl_add_return_wit_1.
Proof.
  pre_process.
  Exists retval_2.
  destruct (m2 retval_2) eqn:Hm2_at_new.
  - match goal with
    | H : m2 retval_2 = Some ?v |- _ => rename v into v_old
    end.
    sep_apply (store_map_split store_val retval_2 v_old m2 Hm2_at_new).
    sep_apply store_val_to_field.
    sep_apply (dup_store_uint (&(retval_2 # "blist" ->ₛ "val")) v_old val_pre).
    entailer!.
  - set (m2' := PV.insert_map m2 retval_2 val_pre).
    sep_apply (store_map_equiv_store_map_missing store_val m2 retval_2 Hm2_at_new).
    assert (Houtside : forall a, a <> retval_2 -> m2 a = m2' a).
    { intros a Ha.
      unfold m2'.
      symmetry.
      rewrite PV.insert_map_diff by congruence.
      reflexivity. }
    pose proof (store_map_missing_i_equiv store_val m2 m2' retval_2 Houtside) as Heq.
    destruct Heq as [Hmiss _].
    sep_apply Hmiss.
    assert (Hm2'_at_new : m2' retval_2 = Some val_pre).
    { unfold m2'. apply PV.insert_map_same. }
    sep_apply store_val_from_field.
    sep_apply (store_map_merge store_val retval_2 val_pre m2' Hm2'_at_new).
    sep_apply (store_hash_skeleton_intro
                 h_pre
                 (KP.insert_map m1 k retval_2)
                 l
                 (replace_Znth (retval % 211) retval_2 lh)
                 b
                 retval_2
                 bucks_ph).
    unfold m2' in *.
    unfold store_hash_skeleton.
    Intros l0 lh0 b0 top0 bucks0.
    assert (Hins_k : KP.insert_map m1 k retval_2 k = Some retval_2) by
      apply KP.insert_map_same.
    sep_apply (store_map_split store_name k retval_2 (KP.insert_map m1 k retval_2) Hins_k).
    unfold store_name.
    Intros key_ptr.
    sep_apply (dup_store_ptr (&(retval_2 # "blist" ->ₛ "key")) key_ptr key_pre).
    entailer!.
Qed.
      
Lemma proof_of_hashtbl_add_return_wit_2 : hashtbl_add_return_wit_2.
Proof.
  pre_process.
  Exists retval_2.
  destruct (m2 retval_2) eqn:Hm2_at_new.
  - match goal with
    | H : m2 retval_2 = Some ?v |- _ => rename v into v_old
    end.
    sep_apply (store_map_split store_val retval_2 v_old m2 Hm2_at_new).
    sep_apply store_val_to_field.
    sep_apply (dup_store_uint (&(retval_2 # "blist" ->ₛ "val")) v_old val_pre).
    entailer!.
  - set (m2' := PV.insert_map m2 retval_2 val_pre).
    sep_apply (store_map_equiv_store_map_missing store_val m2 retval_2 Hm2_at_new).
    assert (Houtside : forall a, a <> retval_2 -> m2 a = m2' a).
    { intros a Ha.
      unfold m2'.
      symmetry.
      rewrite PV.insert_map_diff by congruence.
      reflexivity. }
    pose proof (store_map_missing_i_equiv store_val m2 m2' retval_2 Houtside) as Heq.
    destruct Heq as [Hmiss _].
    sep_apply Hmiss.
    assert (Hm2'_at_new : m2' retval_2 = Some val_pre).
    { unfold m2'. apply PV.insert_map_same. }
    sep_apply store_val_from_field.
    sep_apply (store_map_merge store_val retval_2 val_pre m2' Hm2'_at_new).
    sep_apply (store_hash_skeleton_intro
                 h_pre
                 (KP.insert_map m1 k retval_2)
                 (retval_2 :: l)
                 (replace_Znth (retval % 211) retval_2 lh)
                 b
                 retval_2
                 bucks_ph).
    unfold m2' in *.
    unfold store_hash_skeleton.
    Intros l0 lh0 b0 top0 bucks0.
    assert (Hins_k : KP.insert_map m1 k retval_2 k = Some retval_2) by
      apply KP.insert_map_same.
    sep_apply (store_map_split store_name k retval_2 (KP.insert_map m1 k retval_2) Hins_k).
    unfold store_name.
    Intros key_ptr.
    sep_apply (dup_store_ptr (&(retval_2 # "blist" ->ₛ "key")) key_ptr key_pre).
    entailer!.
Qed.


Lemma proof_of_hashtbl_add_which_implies_wit_1 : hashtbl_add_which_implies_wit_1.
Proof. 
  pre_process.
  unfold store_hash_skeleton.
  Intros l lh b top bucks.
  unfold NBUCK, NULL.
  Exists b lh l bucks top.
  eapply sepcon_cancel_end.
  - entailer!.
  - apply derivable1_truep_intros.
Qed.

Lemma proof_of_hashtbl_add_which_implies_wit_2 : hashtbl_add_which_implies_wit_2.
Proof.
  pre_process.
  assert (top_ph <> NULL) as Htop by (unfold NULL; auto).
  sep_apply (dll_head_exists_with_TT top_ph 0 l Htop).
  Intros top_down top_up l_tail.
  Exists top_up top_down l_tail.
  entailer!.
Qed.

