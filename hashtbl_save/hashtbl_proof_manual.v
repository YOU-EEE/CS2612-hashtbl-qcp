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
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import hashtbl_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import hashtbl_lib.
Local Open Scope sac.

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

Lemma proof_of_create_bucks_entail_wit_1 : create_bucks_entail_wit_1.
Proof. 
    pre_process.
    Exists content_2 retval.
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

(* Axiom store_map_empty : 
  forall {A B: Type} (P: A -> B -> Assertion) (m: A -> option B),
    (forall a, m a = None \/ (forall b, m a = Some b -> P a b --||-- emp)) ->
    MapLib.store_map P m --||-- emp. *)

Axiom store_map_empty : 
  forall {A B: Type} (P: A -> B -> Assertion) (m: A -> option B),
    (exists l, (forall a, In a l <-> exists b, m a = Some b) /\ NoDup l) ->
    (forall a, m a = None \/ (forall b, m a = Some b -> P a b --||-- emp)) ->
    MapLib.store_map P m --||-- emp.

Definition b_init (x : Z) : option (Z * list Z):= 
  if (Z.geb x 0 && Z.leb x 211)%bool then Some (0, nil) 
  else None.

Axiom null_emp: 
  [|0 = NULL|] && emp --||-- emp.

Lemma proof_of_init_hashtbl_return_wit_1 : init_hashtbl_return_wit_1.
Proof.
  pre_process.
  unfold store_hash_skeleton.

  Exists (@nil addr) (zeros 211) b_init 0 bucks_base.
  unfold NBUCK.
  entailer!.
  + simpl.
    (* 1) store_map store_sll b_init --||-- emp *)
    assert (H_sll_emp : MapLib.store_map store_sll b_init --||-- emp).
    {
      eapply store_map_empty.
      - (* finite support for b_init *)
        exists (Z.seq 0 211).
        split.
        + intros a; split.
          * intro Hin.
            exists (0, @nil addr).
            unfold b_init.
            apply Z.in_seq in Hin.
            assert (Hge : Z.geb a 0 = true) by (apply Z.geb_le; lia).
            assert (Hlt : (a <? 211) = true) by (apply Z.ltb_lt; lia).
            rewrite Hge, Hlt. reflexivity.
          * intros [b Hb].
            unfold b_init in Hb.
            destruct ((Z.geb a 0 && (a <? 211))%bool) eqn:Hba; try discriminate.
            apply andb_true_iff in Hba as [Hge Hlt].
            apply Z.geb_le in Hge.
            apply Z.ltb_lt in Hlt.
            apply Z.in_seq. lia.
        + apply Z.seq_NoDup.
      - (* pointwise emptiness of store_sll entries *)
        intros a.
        unfold b_init.
        destruct ((Z.geb a 0 && (a <? 211))%bool) eqn:Hba.
        * right. intros b Hb.
          inversion Hb; subst.
          unfold store_sll. simpl.
          apply null_emp.
        * left. reflexivity.
    }.

(* Proof. 
    pre_process.
    unfold store_hash_skeleton.
    set (b_init := fun (_ : Z) => Some (0, @nil addr)).
                                
    Exists (@nil addr) (zeros 211) b_init 0 bucks_base.
    unfold NBUCK.
    entailer!.
    + simpl. 
      assert (H_sll_emp: MapLib.store_map store_sll b_init --||-- emp).
      {
        apply store_map_empty.
        intros a. right. intros b Hb.
        unfold b_init in Hb. injection Hb; intros; subst.
        unfold store_sll. simpl. apply null_emp.  
      }
      assert (H_name_emp: MapLib.store_map store_name empty_map --||-- emp).
      {
        apply store_map_empty.
        intros a. left. reflexivity.
      }
      entailer!.
      rewrite H_sll_emp.
      rewrite H_name_emp.
      entailer!.
    + unfold contain_all_correct_addrs. 

Qed.       *)


Lemma proof_of_create_hashtbl_return_wit_1 : create_hashtbl_return_wit_1.
Proof. 
    pre_process.
    entailer!.
Abort.

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
    
Abort.

Lemma proof_of_hashtbl_add_return_wit_2 : hashtbl_add_return_wit_2.
Proof. Admitted. 

Lemma proof_of_hashtbl_add_which_implies_wit_1 : hashtbl_add_which_implies_wit_1.
Proof. Admitted. 

Lemma proof_of_hashtbl_add_which_implies_wit_2 : hashtbl_add_which_implies_wit_2.
Proof. Admitted. 

Lemma proof_of_hashtbl_find_entail_wit_1 : hashtbl_find_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_hashtbl_find_entail_wit_2 : hashtbl_find_entail_wit_2.
Proof. Admitted. 

Axiom bucket_in_global : forall m b l ind ph lb p,
  contain_all_addrs m l ->
  contain_all_correct_addrs m b ->
  b ind = Some (ph, lb) ->
  In p lb ->
  In p l.

  Axiom store_string_on_field : forall (field_addr : addr) (s : list Z),
  store_string field_addr s |-- 
  EX (kp : Z), field_addr # Ptr |-> kp ** store_string kp s.

  Lemma proof_of_hashtbl_find_entail_wit_3 : hashtbl_find_entail_wit_3.
Proof. 
    pre_process.
    sep_apply (sll_not_zero i_v_3 l2_2).
    Intros p_next l_tail.

    unfold contain_all_addrs in H4.
    assert (Hin_bucket: In i_v_3 (l1_2 ++ l2_2)).
    {
      rewrite in_app_iff. right. 
      subst l2_2. 
      simpl; left; reflexivity.
    }

    assert (Hin: In i_v_3 l_2).
    {
      eapply bucket_in_global; eauto.
    }
    specialize (H4 i_v_3).
    destruct H4 as [_ H4_imp].
    specialize (H4_imp Hin).
    destruct H4_imp as [k_cur Hk_cur].

    sep_apply (MapLib.store_map_split store_name k_cur i_v_3 m1 Hk_cur).
    unfold store_name.

    sep_apply (store_string_on_field (&(i_v_3 # "blist" ->ₛ "key")) k_cur).
    Intros kp.
    destruct (m2 i_v_3) eqn:Hm2.
    - rename z into vp.
      pose (h_val := Znth ind lh_2 0).
      destruct l1_2 as [ | head_addr t_l1].
      + 
        


Lemma proof_of_hashtbl_find_entail_wit_6_1 : hashtbl_find_entail_wit_6_1.
Proof. Admitted. 

Lemma proof_of_hashtbl_find_entail_wit_6_2 : hashtbl_find_entail_wit_6_2.
Proof. Admitted. 

Lemma proof_of_hashtbl_find_return_wit_1 : hashtbl_find_return_wit_1.
Proof. Admitted. 

Lemma proof_of_hashtbl_find_return_wit_2 : hashtbl_find_return_wit_2.
Proof. Admitted. 

Lemma proof_of_hashtbl_find_return_wit_3 : hashtbl_find_return_wit_3.
Proof. Admitted. 

Lemma proof_of_hashtbl_find_which_implies_wit_1 : hashtbl_find_which_implies_wit_1.
Proof. Admitted. 

