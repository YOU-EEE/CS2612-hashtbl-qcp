Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zquot.
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

Lemma nth_replace_nth_neq {A} (i j: nat) (v d: A) (l: list A) :
  i <> j ->
  nth j (replace_nth i v l) d = nth j l d.
Proof.
  revert i l.
  induction j; intros i l Hneq; destruct l; simpl;
    try (destruct i; simpl; try congruence; reflexivity).
  - destruct i; simpl; try reflexivity.
    apply IHj. congruence.
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

Lemma Znth_replace_neq {A} (l: list A) (i j: Z) (v d: A) :
  0 <= i < Zlength l ->
  0 <= j < Zlength l ->
  i <> j ->
  Znth j (replace_Znth i v l) d = Znth j l d.
Proof.
  intros Hi Hj Hneq.
  unfold replace_Znth, Znth.
  apply nth_replace_nth_neq.
  intros Heq.
  apply Hneq.
  apply Z2Nat.inj; lia.
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

(* Axiom store_hash_skeleton_intro :
  forall (x: addr) (m: list Z -> option addr)
         (l lh: list addr) (b: Z -> option (addr * list addr))
         (top bucks: addr),
    contain_all_addrs m l ->
    repr_all_heads lh b ->
    contain_all_correct_addrs m b ->
    &(x # "hashtbl" ->ₛ "top") # Ptr |-> top **
    dll top NULL l **
    &(x # "hashtbl" ->ₛ "bucks") # Ptr |-> bucks **
    PtrArray.full bucks NBUCK lh **
    store_map store_sll b **
    store_map store_name m
    |-- store_hash_skeleton x m. *)

Axiom sepcon_TT_elim : forall P : Assertion, (P ** TT) |-- P.



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
Definition b_init (x : Z) : option (Z * list Z):= 
  if (Z.geb x 0 && Z.ltb x 211)%bool then Some (0, nil) 
  else None.

Lemma Zlength_zeros : forall n, 0 <= n -> Zlength (zeros n) = n.
Proof.
  intros n Hn.
  unfold zeros.
  rewrite Zlength_correct.
  rewrite repeat_length.
  rewrite Z2Nat.id by lia.
  reflexivity.
Qed.

Lemma Znth_zeros : forall n i d,
  0 <= i < n ->
  Znth i (zeros n) d = 0.
Proof.
  intros n i d Hi.
  assert (Hrange : 0 <= i < Zlength (zeros n)).
  { rewrite Zlength_zeros by lia. lia. }
  rewrite (Znth_indep (zeros n) i d 0) by exact Hrange.
  unfold Znth, zeros.
  rewrite nth_repeat by (apply Z2Nat.inj_lt; lia).
  reflexivity.
Qed.

Lemma Zlength_zeros_211 : Zlength (zeros 211) = 211.
Proof.
  apply Zlength_zeros; lia.
Qed.

Lemma empty_contain_all_addrs : contain_all_addrs empty_map nil.
Proof. 
  unfold contain_all_addrs, empty_map. 
  intros; split; intros; simpl in *; [destruct H; discriminate | tauto]. 
Qed.

Lemma empty_contain_all_correct_addrs: contain_all_correct_addrs empty_map b_init.
Proof.
  unfold contain_all_correct_addrs, empty_map, b_init. split; intros.
  - discriminate.
  - exfalso.
    destruct (((Z.geb i 0) && (Z.ltb i 211))%bool) eqn:Hi.
    + (* case true *)
      simpl in H.
      inversion H; subst.     (* 得到 l = nil *)
      simpl in H0.            (* H0 : In p nil *)
      contradiction.          (* 或者: inversion H0. *)
    + (* case false *)
      simpl in H.
      discriminate.
Qed.


Lemma empty_repr_all_heads : repr_all_heads (zeros 211) b_init.
Proof.
  unfold repr_all_heads, b_init. intros.
  split; intros.
  - destruct H as [l Hl].
    remember (((Z.geb i 0) && (Z.ltb i 211))%bool) as b eqn:Hb.
    destruct b.
    + inversion Hl; subst; clear Hl.
      assert (Hb' : ((Z.geb i 0) && (Z.ltb i 211))%bool = true).
      { now symmetry. }
      (* 通过 apply 和 destruct 继续推理 *)
      apply andb_true_iff in Hb'.
      destruct Hb' as [Hi0 Hi211].
      apply Z.geb_le in Hi0.
      apply Z.ltb_lt in Hi211.
      split.
      * split; [exact Hi0 | unfold zeros; rewrite Zlength_correct;
          rewrite repeat_length; rewrite Z2Nat.id by lia; lia].
      * assert (Hz : Znth i (zeros 211) 0 = 0) by (apply Znth_zeros; lia).
        exact Hz.
    + discriminate.
  - destruct H as [Hi Hnth].
    destruct Hi as [Hi0 Hi1].
    assert (Hrange : 0 <= i < 211).
    { split.
      - exact Hi0.
      - rewrite <- Zlength_zeros_211. exact Hi1. }
    assert (Hz : Znth i (zeros 211) 0 = 0) by (apply Znth_zeros; exact Hrange).
    assert (Hp : p = 0) by (eapply eq_trans; [exact (eq_sym Hnth) | exact Hz]).
    clear Hnth.
    subst p.
    exists nil.
    unfold b_init.
    assert (Hge : Z.geb i 0 = true) by (apply Z.geb_le; lia).
    assert (Hlt : Z.ltb i 211 = true) by (apply Z.ltb_lt; lia).
    rewrite Hge, Hlt.
    reflexivity.
Qed.

Lemma In_Zseq_iff :
  forall s len a,
    In a (Zseq s len) <-> exists n, (n < len)%nat /\ a = s + Z.of_nat n.
Proof.
  intros s len; revert s.
  induction len; intros s a; simpl.
  - split; intros H.
    + contradiction.
    + destruct H as [n [Hlt _]]. lia.
  - split; intros H.
    + destruct H as [Heq | Hin].
      * exists 0%nat. split; [lia | subst; simpl; lia].
      * apply IHlen in Hin.
        destruct Hin as [n [Hlt Heq]].
        exists (S n). split; [lia | subst; simpl; lia].
    + destruct H as [n [Hlt Heq]].
      destruct n.
      * simpl in Heq. left. subst. lia.
      * right. apply IHlen.
        exists n. split; [lia | subst; simpl; lia].
Qed.

Lemma In_Zseq_0_iff : forall a len,
  In a (Zseq 0 len) <-> 0 <= a < Z.of_nat len.
Proof.
  intros a len; split; intros H.
  - apply In_Zseq_iff in H.
    destruct H as [n [Hlt Heq]].
    subst. split.
    + lia.
    + apply Nat2Z.inj_lt in Hlt. lia.
  - destruct H as [Hge Hlt].
    apply In_Zseq_iff.
    exists (Z.to_nat a). split.
    + rewrite <- Nat2Z.id.
      apply Z2Nat.inj_lt; lia.
    + rewrite Z2Nat.id by lia. lia.
Qed.

Lemma Zseq_NoDup : forall s len, NoDup (Zseq s len).
Proof.
  intros s len; revert s.
  induction len; intros s; simpl.
  - constructor.
  - constructor.
    + intro Hin. apply In_Zseq_iff in Hin.
      destruct Hin as [n [Hlt Heq]]. lia.
    + apply IHlen.
Qed.

Lemma dll_null: dll 0 NULL nil --||-- emp.
Proof.
  simpl.
  unfold NULL.
  split.
  entailer!.
  entailer!.
Qed.

Lemma store_sll_null: emp |-- store_map store_sll b_init.
Proof.
  unfold store_map.
  Exists (Zseq 0 211%nat).
  entailer!.
  - induction (Zseq 0 211%nat); simpl.
    + entailer!.
    + assert (Hhead :
        emp |-- iter_sepcon ((match b_init a with
                              | Some b => store_sll a b
                              | None => emp
                              end) :: nil)).
      { unfold b_init.
        destruct ((Z.geb a 0 && Z.ltb a 211)%bool) eqn:Hb; simpl;
          unfold iter_sepcon; simpl; entailer!. }
      assert (Htail : emp |-- iter_sepcon (map (fun a0 : Z => match b_init a0 with
                                      | Some b0 => store_sll a0 b0
                                      | None => emp
                                      end) l)).
      { exact IHl. }
      eapply derivable1_trans.
      * apply (sepcon_cancel_end emp
                                 (iter_sepcon (map (fun a0 : Z => match b_init a0 with
                                                          | Some b0 => store_sll a0 b0
                                                          | None => emp
                                                          end) l))
                                 (iter_sepcon ((match b_init a with
                                                | Some b => store_sll a b
                                                | None => emp
                                                end) :: nil))).
        -- exact Hhead.
        -- exact Htail.
      * apply derivable1_sepcon_iter_sepcon1.
  - apply Zseq_NoDup.
  - intros a; split; intros Hin.
    + exists (0, @nil addr).
      unfold b_init.
      apply In_Zseq_0_iff in Hin.
      destruct Hin as [Hge Hlt].
      assert (Hgeb : Z.geb a 0 = true) by (apply Z.geb_le; lia).
      assert (Hltb : Z.ltb a 211 = true) by (apply Z.ltb_lt; lia).
      rewrite Hgeb, Hltb. reflexivity.
    + destruct Hin as [b Hb].
      unfold b_init in Hb.
      destruct ((Z.geb a 0 && Z.ltb a 211)%bool) eqn:Hb'; try discriminate.
      apply andb_true_iff in Hb' as [Hge Hlt].
      apply Z.geb_le in Hge.
      apply Z.ltb_lt in Hlt.
      apply In_Zseq_0_iff. lia.
Qed.


Lemma store_name_null: emp |-- store_map store_name empty_map.
Proof.
  setoid_rewrite <- (store_map_empty store_name).
  entailer!.
Qed.

Lemma proof_of_init_hashtbl_return_wit_1 : init_hashtbl_return_wit_1.
Proof.
  pre_process.
  unfold store_hash_skeleton.
  Exists nil (zeros 211) b_init 0 bucks_base.
  pose proof empty_contain_all_addrs.
  pose proof empty_repr_all_heads.
  pose proof empty_contain_all_addrs.
  pose proof dll_null.
  pose proof store_sll_null.
  pose proof store_name_null.
  entailer!.
  + unfold NBUCK.
    entailer!.
    destruct H2 as [Hdll_to_emp Hemp_to_dll].  (* 从 --||-- 拿到两个方向 *)
    apply derivable1s_emp_sepcon_unfold.
    - exact Hemp_to_dll.
    - apply derivable1s_emp_sepcon_unfold.
      * exact H3.
      * exact H4.
  + apply empty_contain_all_correct_addrs.
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

Lemma KP_insert_map_ext_same :
  forall (m: list Z -> option addr) k p,
    m k = Some p ->
    (forall key, KP.insert_map m k p key = m key).
Proof.
  intros m k p Hmk key.
  destruct (list_eq_dec Z.eq_dec key k) as [Heq|Hneq].
  - subst. rewrite KP.insert_map_same. rewrite Hmk. reflexivity.
  - rewrite KP.insert_map_diff by (intro Heq; apply Hneq; symmetry; exact Heq).
    reflexivity.
Qed.

Lemma store_name_intro : forall k node key_pre,
  (&( node # "blist" ->ₛ "key") # Ptr |-> key_pre ** store_string key_pre k)
  |-- store_name k node.
Proof.
  intros.
  unfold store_name.
  Exists key_pre.
  entailer!.
Qed.

Definition b' (b : Z -> option (addr * list addr)) (idx new : Z)
  : Z -> option (addr * list addr) :=
  fun j =>
    if Z.eq_dec j idx then
      match b j with
      | Some (_old_head, l_old) => Some (new, new :: l_old)
      | None => Some (new, new :: nil)
      end
    else b j.

Lemma contain_all_addrs_insert_cons :
  forall (m : list Z -> option addr) (l : list addr) (k : list Z) (p : addr),
    contain_all_addrs m l ->
    m k = None ->
    contain_all_addrs (KP.insert_map m k p) (p :: l).
Proof.
  intros m l k p Hcontain Hmk.
  unfold contain_all_addrs in *.
  intro p0.
  split; intros H.
  - destruct H as [key Hkey].
    destruct (list_eq_dec Z.eq_dec key k) as [Heq|Hneq].
    + subst key.
      rewrite KP.insert_map_same in Hkey.
      inversion Hkey; subst.
      simpl; auto.
    + rewrite KP.insert_map_diff in Hkey
        by (intro Heq; apply Hneq; symmetry; exact Heq).
      specialize (Hcontain p0).
      assert (Hinl : In p0 l).
      { apply (proj1 Hcontain). exists key; exact Hkey. }
      simpl; right; exact Hinl.
  - simpl in H.
    destruct H as [Hp | Hin].
    + subst p0.
      exists k.
      rewrite KP.insert_map_same.
      reflexivity.
    + specialize (Hcontain p0).
      apply (proj2 Hcontain) in Hin.
      destruct Hin as [key Hkey].
      exists key.
      destruct (list_eq_dec Z.eq_dec key k) as [Heq|Hneq].
      * subst. rewrite Hmk in Hkey. discriminate.
      * rewrite KP.insert_map_diff
          by (intro Heq; apply Hneq; symmetry; exact Heq).
        exact Hkey.
Qed.

Lemma repr_all_heads_update :
  forall lh b idx new,
    0 <= idx < Zlength lh ->
    repr_all_heads lh b ->
    (* 需要从旧 repr_all_heads 推出 b idx = Some(old_head, l_old) 的存在性 *)
    repr_all_heads (replace_Znth idx new lh) (b' b idx new).
Proof.
  intros lh b idx new Hidx Hrepr.
  unfold repr_all_heads in *.
  intros j p; split; intros H.
  - destruct (Z.eq_dec j idx) as [Heq|Hneq].
    + subst j.
      destruct H as [l Hb].
      unfold b' in Hb.
      destruct (Z.eq_dec idx idx) as [_|Hneq].
      * simpl in Hb.
        destruct (b idx) as [pl | ] eqn:Hbidx.
        -- destruct pl as [ph l_old].
           inversion Hb; subst; clear Hb.
           split.
           ++ rewrite Zlength_replace_Znth. exact Hidx.
           ++ rewrite (Znth_replace_eq lh idx p 0) by exact Hidx. reflexivity.
        -- inversion Hb; subst; clear Hb.
           split.
           ++ rewrite Zlength_replace_Znth. exact Hidx.
           ++ rewrite (Znth_replace_eq lh idx p 0) by exact Hidx. reflexivity.
      * exfalso. apply Hneq. reflexivity.
    + destruct H as [l Hb].
      unfold b' in Hb.
      destruct (Z.eq_dec j idx) as [Heq|Hneq'].
      * exfalso. apply Hneq. exact Heq.
      * simpl in Hb.
      specialize (Hrepr j p) as Hreprj.
      destruct (proj1 Hreprj (ex_intro _ l Hb)) as [Hrange Hnth].
      split;
        [rewrite Zlength_replace_Znth; exact Hrange
        |rewrite (Znth_replace_neq lh idx j new 0)
           by (try exact Hidx; try exact Hrange;
               intro Heq; apply Hneq; symmetry; exact Heq);
         exact Hnth].
  - destruct (Z.eq_dec j idx) as [Heq|Hneq].
    + subst j.
      destruct H as [Hrange Hnth].
      pose proof (Znth_replace_eq lh idx new 0 Hidx) as Hz.
      rewrite Hz in Hnth. subst p.
      destruct (b idx) as [pl | ] eqn:Hbidx.
      * destruct pl as [ph l_old].
        exists (new :: l_old).
        unfold b'. destruct (Z.eq_dec idx idx) as [_|Hneq].
        -- rewrite Hbidx. reflexivity.
        -- exfalso. apply Hneq. reflexivity.
      * exists (new :: nil).
        unfold b'. destruct (Z.eq_dec idx idx) as [_|Hneq].
        -- rewrite Hbidx. reflexivity.
        -- exfalso. apply Hneq. reflexivity.
    + destruct H as [Hrange Hnth].
      rewrite Zlength_replace_Znth in Hrange.
      assert (Hnth' : Znth j lh 0 = p).
      { rewrite (Znth_replace_neq lh idx j new 0) in Hnth
          by (try exact Hidx; try exact Hrange;
              intro Heq; apply Hneq; symmetry; exact Heq).
        exact Hnth. }
      specialize (Hrepr j p) as Hreprj.
      destruct (proj2 Hreprj (conj Hrange Hnth')) as [l Hb].
      exists l.
      unfold b'.
      destruct (Z.eq_dec j idx) as [Heq|Hneq'].
      * exfalso. apply Hneq. exact Heq.
      * simpl. exact Hb.
Qed.

Lemma dll_singleton_from_fields :
  forall x,
    x <> NULL ->
    &(x # "blist" ->ₛ "down") # Ptr |-> NULL **
    &(x # "blist" ->ₛ "up") # Ptr |-> NULL
    |-- dll x NULL (x :: nil).
Proof.
  intros x Hx.
  simpl dll.
  Exists NULL.
  entailer!.
Qed.

(* ------------------ store_map store_sll update (admit for now) ------------------ *)


Lemma contain_all_correct_addrs_insert_update :
  forall (m: list Z -> option addr) (b: Z -> option (addr * list addr))
         (k: list Z) (p: addr) (idx: Z),
    m k = None ->
    idx = hash_string_k k mod NBUCK ->
    contain_all_correct_addrs m b ->
    contain_all_correct_addrs (KP.insert_map m k p) (b' b idx p).
Proof.
  intros m b k p idx Hmk Hidx Hcorr.
  pose proof Hidx as Hidx0.
  destruct Hcorr as [Hfwd Hbwd].
  split.
  - intros key p0 Hm'.
    destruct (list_eq_dec Z.eq_dec key k) as [Heq|Hneq].
    + subst key.
      rewrite KP.insert_map_same in Hm'.
      inversion Hm'; subst p0.
      unfold b'.
      rewrite <- Hidx0.
      destruct (Z.eq_dec idx idx) as [_|Hneq_idx0].
      * destruct (b idx) as [[ph l] | ] eqn:Hbidx.
        -- simpl. exists p. exists (p :: l). split; [reflexivity | simpl; auto].
        -- simpl. exists p. exists (p :: nil). split; [reflexivity | simpl; auto].
      * exfalso. apply Hneq_idx0. reflexivity.
    + rewrite KP.insert_map_diff in Hm'
        by (intro Heq; apply Hneq; symmetry; exact Heq).
      specialize (Hfwd key p0 Hm') as [ph [l [Hb Hin]]].
      set (h := hash_string_k key mod NBUCK) in *.
      destruct (Z.eq_dec h idx) as [Heq_idx|Hneq_idx].
      * rewrite Heq_idx in Hb.
        unfold b'.
        rewrite Heq_idx.
        destruct (Z.eq_dec idx idx) as [_|Hneq_idx1].
        -- rewrite Hb.
           exists p. exists (p :: l). split; [reflexivity | simpl; auto].
        -- exfalso. apply Hneq_idx1. reflexivity.
      * unfold b'.
        destruct (Z.eq_dec h idx) as [Heq|Hneq'].
        -- exfalso. apply Hneq_idx. exact Heq.
        -- simpl. exists ph. exists l. split; [exact Hb | exact Hin].
  - intros i ph l p0 Hb' Hin.
    destruct (Z.eq_dec i idx) as [Heq|Hneq].
    + subst i.
      unfold b' in Hb'.
      destruct (Z.eq_dec idx idx) as [_|Hneq_idx2].
      * simpl in Hb'.
        destruct (b idx) as [pl | ] eqn:Hbidx.
        -- destruct pl as [ph0 l0].
           inversion Hb'; subst ph l.
           simpl in Hin. destruct Hin as [Hp0 | Hin].
           ++ subst p0. exists k. split.
              ** apply KP.insert_map_same.
              ** rewrite Hidx. reflexivity.
           ++ specialize (Hbwd idx ph0 l0 p0 Hbidx Hin) as [key [Hmk0 Hhash]].
              assert (Hneq_key : key <> k).
              { intro Hk. subst key. rewrite Hmk in Hmk0. discriminate. }
              exists key. split.
              ** rewrite KP.insert_map_diff
                   by (intro Heq; apply Hneq_key; symmetry; exact Heq).
                 exact Hmk0.
              ** exact Hhash.
        -- inversion Hb'; subst ph l.
           simpl in Hin. destruct Hin as [Hp0 | Hin].
           ++ subst p0. exists k. split.
              ** apply KP.insert_map_same.
              ** rewrite Hidx. reflexivity.
           ++ simpl in Hin. contradiction.
      * exfalso. apply Hneq_idx2. reflexivity.
    + unfold b' in Hb'.
      destruct (Z.eq_dec i idx) as [Heq|Hneq'].
      * exfalso. apply Hneq. exact Heq.
      * simpl in Hb'.
      specialize (Hbwd i ph l p0 Hb' Hin) as [key [Hmk0 Hhash]].
      assert (Hneq_key : key <> k).
      { intro Hk. subst key. rewrite <- Hidx in Hhash. lia. }
      exists key. split;
        [rewrite KP.insert_map_diff
           by (intro Heq; apply Hneq_key; symmetry; exact Heq); exact Hmk0
        |exact Hhash].
Qed.

Lemma store_map_store_sll_update_at_idx :
  forall (bucks: addr) (lh: list addr) (b: Z -> option (addr * list addr))
         (idx new: Z) (l_idx: list addr),
    0 <= idx < NBUCK ->
    new <> NULL ->
    b idx = Some (Znth idx lh 0, l_idx) ->
    PtrArray.full bucks 211 (replace_Znth idx new lh) **
    &(new # "blist" ->ₛ "next") # Ptr |-> Znth idx lh 0 **
    store_map store_sll b
    |-- PtrArray.full bucks 211 (replace_Znth idx new lh) **
        store_map store_sll (b' b idx new).
Proof.
  intros bucks lh b idx new l_idx Hidx Hnew Hbidx.
  set (old_head := Znth idx lh 0).
  sep_apply (store_map_split store_sll idx (old_head, l_idx) b Hbidx).
  assert (Houtside : forall j, j <> idx -> b j = b' b idx new j).
  { intros j Hneq. unfold b'.
    destruct (Z.eq_dec j idx) as [Heq|Hneq'].
    - exfalso. apply Hneq. exact Heq.
    - reflexivity. }
  pose proof (store_map_missing_i_equiv store_sll b (b' b idx new) idx Houtside) as Heq.
  destruct Heq as [Hmiss _].
  sep_apply Hmiss.
  assert (Hsll :
            &(new # "blist" ->ₛ "next") # Ptr |-> old_head **
            store_sll idx (old_head, l_idx)
            |-- store_sll idx (new, new :: l_idx)).
  { unfold store_sll. simpl sll. Exists old_head. entailer!. }
  sep_apply Hsll.
  assert (Hb' : b' b idx new idx = Some (new, new :: l_idx)).
  { unfold b'.
    destruct (Z.eq_dec idx idx) as [_|Hneq].
    - rewrite Hbidx. reflexivity.
    - exfalso. apply Hneq. reflexivity. }
  sep_apply (store_map_merge store_sll idx (new, new :: l_idx) (b' b idx new) Hb').
  entailer!.
Qed.

Lemma store_map_store_sll_update_at_idx_frame :
  forall (bucks: addr) (lh: list addr) (b: Z -> option (addr * list addr))
         (idx new: Z) (l_idx: list addr) (R: Assertion),
    0 <= idx < NBUCK ->
    new <> NULL ->
    b idx = Some (Znth idx lh 0, l_idx) ->
    PtrArray.full bucks 211 (replace_Znth idx new lh) **
    &(new # "blist" ->ₛ "next") # Ptr |-> Znth idx lh 0 **
    store_map store_sll b ** R
    |-- PtrArray.full bucks 211 (replace_Znth idx new lh) **
        store_map store_sll (b' b idx new) ** R.
Proof.
  intros bucks lh b idx new l_idx R Hidx Hnew Hbidx.
  apply derivable1_sepcon_mono.
  - eapply (store_map_store_sll_update_at_idx bucks lh b idx new l_idx); eauto.
  - apply derivable1_refl.
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
    
    set (m1' := KP.insert_map m1 k retval_2).

    (* 1) 把 store_map store_name m1 改写成 “k 缺失”的形态 *)
    sep_apply (store_map_equiv_store_map_missing store_name m1 k H9).

    (* 2) 把 “缺失形态”从 m1 迁移到 m1'：证明除 k 以外两张 map 一样 *)
    assert (Houtside_name : forall key, key <> k -> m1 key = m1' key).
    { intros key Hneq. unfold m1'.
      rewrite KP.insert_map_diff
        by (intro Heq; apply Hneq; symmetry; exact Heq).
      reflexivity. }

    pose proof (store_map_missing_i_equiv store_name m1 m1' k Houtside_name) as Heq_name.
    destruct Heq_name as [Hmiss_name _].
    sep_apply Hmiss_name.

    (* 3) 构造 store_name k retval_2（已有 store_name_intro） *)
    sep_apply (store_name_intro k retval_2 key_pre).

    (* 4) merge 回 store_map store_name m1' *)
    assert (Hins_name : m1' k = Some retval_2).
    { unfold m1'. apply KP.insert_map_same. }

    sep_apply (store_map_merge store_name k retval_2 m1' Hins_name).

    unfold store_hash_skeleton.

    set (idx := (retval % 211)).
    set (b_new := b' b idx retval_2).
    (* 在 unfold store_hash_skeleton 之后，按 (l, lh, b, top, bucks) 的顺序给见证 *)
    Exists (retval_2 :: l)
       (replace_Znth (retval % 211) retval_2 lh)
       b_new                (* 不能再用旧 b；需要更新后的 b' *)
       retval_2           (* top 应该是新 top *)
       bucks_ph.
    subst idx b_new.
    prop_apply (PtrArray.full_Zlength bucks_ph 211 (replace_Znth (retval % 211) retval_2 lh)); Intros.
    match goal with
    | Hlen : Zlength (replace_Znth _ _ _) = _ |- _ =>
        pose proof
          (eq_trans (eq_sym (Zlength_replace_Znth lh (retval % 211) retval_2)) Hlen)
          as Hlen_lh
    end.
    assert (Hidx_lh : 0 <= retval % 211 < Zlength lh) by (rewrite Hlen_lh; lia).
    pose proof (H7 (retval % 211) (Znth (retval % 211) lh 0)) as Hrepr_idx.
    assert (Hexists : exists l_idx, b (retval % 211) = Some (Znth (retval % 211) lh 0, l_idx)).
    { apply (proj2 Hrepr_idx). split; [exact Hidx_lh | reflexivity]. }
    destruct Hexists as [l_idx Hbidx].
    entailer!.
    1: { unfold NBUCK.
      assert (Hnew : retval_2 <> NULL) by (unfold NULL; lia).
      sepcon_lift (store_map store_sll b).
      sepcon_lift (&(retval_2 # "blist" ->ₛ "next") # Ptr |-> Znth (retval % 211) lh 0).
      sepcon_lift (PtrArray.full bucks_ph 211 (replace_Znth (retval % 211) retval_2 lh)).
      sepcon_assoc_change.
      rewrite (logic_equiv_sepcon_assoc
                (&(retval_2 # "blist" ->ₛ "next") # Ptr |-> Znth (retval % 211) lh 0)
                (store_map store_sll b)
                (&(retval_2 # "blist" ->ₛ "down") # Ptr |-> top_ph **
                 (&(retval_2 # "blist" ->ₛ "up") # Ptr |-> 0 **
                  (dll top_ph 0 l ** TT)))).
      rewrite (logic_equiv_sepcon_assoc
                (PtrArray.full bucks_ph 211 (replace_Znth (retval % 211) retval_2 lh))
                (&(retval_2 # "blist" ->ₛ "next") # Ptr |-> Znth (retval % 211) lh 0 **
                 store_map store_sll b)
                (&(retval_2 # "blist" ->ₛ "down") # Ptr |-> top_ph **
                 (&(retval_2 # "blist" ->ₛ "up") # Ptr |-> 0 **
                  (dll top_ph 0 l ** TT)))).
      rewrite (logic_equiv_sepcon_assoc
                (PtrArray.full bucks_ph 211 (replace_Znth (retval % 211) retval_2 lh))
                (&(retval_2 # "blist" ->ₛ "next") # Ptr |-> Znth (retval % 211) lh 0)
                (store_map store_sll b)).
      set (R :=
        (&(retval_2 # "blist" ->ₛ "down") # Ptr |-> top_ph **
         (&(retval_2 # "blist" ->ₛ "up") # Ptr |-> 0 ** (dll top_ph 0 l ** TT)))).
      change (PtrArray.full bucks_ph 211 (replace_Znth (retval % 211) retval_2 lh) **
              &(retval_2 # "blist" ->ₛ "next") # Ptr |-> Znth (retval % 211) lh 0 **
              store_map store_sll b ** R
              |-- PtrArray.full bucks_ph 211 (replace_Znth (retval % 211) retval_2 lh) **
                  (dll retval_2 NULL (retval_2 :: l) **
                   store_map store_sll (b' b (retval % 211) retval_2))).
      eapply derivable1_trans.
      { apply (store_map_store_sll_update_at_idx_frame
          bucks_ph lh b (retval % 211) retval_2 l_idx R);
        [unfold NBUCK; lia | exact Hnew | exact Hbidx]. }
      subst R.
      sepcon_lift (dll top_ph 0 l).
      sepcon_assoc_change.
      assert (Htop_null : top_ph = NULL) by (unfold NULL; lia).
      sep_apply (dll_zero top_ph 0 l Htop_null).
      entailer!.
      rewrite Htop_null.
      change 0 with NULL.
      sepcon_lift (&(retval_2 # "blist" ->ₛ "down") # Ptr |-> NULL).
      sepcon_lift (&(retval_2 # "blist" ->ₛ "up") # Ptr |-> NULL).
      sepcon_assoc_change.
      rewrite H11.
      rewrite (logic_equiv_sepcon_assoc
                (&(retval_2 # "blist" ->ₛ "up") # Ptr |-> NULL)
                (&(retval_2 # "blist" ->ₛ "down") # Ptr |-> NULL)
                (TT)%sac).
      rewrite (logic_equiv_sepcon_comm
                (&(retval_2 # "blist" ->ₛ "up") # Ptr |-> NULL)
                (&(retval_2 # "blist" ->ₛ "down") # Ptr |-> NULL)).
      eapply derivable1_trans.
      { apply sepcon_TT_elim. }
      sep_apply (dll_singleton_from_fields retval_2).
      { apply derivable1_refl. }
      { unfold NULL; lia. }
    }
    all: try (eapply contain_all_correct_addrs_insert_update;
              [exact H9
              | unfold NBUCK; rewrite H5; rewrite Zrem_Zmod_pos by lia; reflexivity
              | exact H8]).
    all: try (eapply repr_all_heads_update; eauto).
    all: try (eapply contain_all_addrs_insert_cons; eauto).
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

    set (m1' := KP.insert_map m1 k retval_2).

    (* 1) 把 store_map store_name m1 改写成 “k 缺失”的形态 *)
    sep_apply (store_map_equiv_store_map_missing store_name m1 k H10).

    (* 2) 把 “缺失形态”从 m1 迁移到 m1'：证明除 k 以外两张 map 一样 *)
    assert (Houtside_name : forall key, key <> k -> m1 key = m1' key).
    { intros key Hneq. unfold m1'.
      rewrite KP.insert_map_diff
        by (intro Heq; apply Hneq; symmetry; exact Heq).
      reflexivity. }

    pose proof (store_map_missing_i_equiv store_name m1 m1' k Houtside_name) as Heq_name.
    destruct Heq_name as [Hmiss_name _].
    sep_apply Hmiss_name.

    (* 3) 构造 store_name k retval_2（已有 store_name_intro） *)
    sep_apply (store_name_intro k retval_2 key_pre).

    (* 4) merge 回 store_map store_name m1' *)
    assert (Hins_name : m1' k = Some retval_2).
    { unfold m1'. apply KP.insert_map_same. }

    sep_apply (store_map_merge store_name k retval_2 m1' Hins_name).

    unfold store_hash_skeleton.
    set (idx := (retval % 211)).
    set (b_new := b' b idx retval_2).
    Exists (retval_2 :: l)
        (replace_Znth idx retval_2 lh)
        b_new
        retval_2
        bucks_ph.
    subst idx b_new.
    prop_apply (PtrArray.full_Zlength bucks_ph 211 (replace_Znth (retval % 211) retval_2 lh)); Intros.
    match goal with
    | Hlen : Zlength (replace_Znth _ _ _) = _ |- _ =>
        pose proof (eq_trans (eq_sym (Zlength_replace_Znth lh (retval % 211) retval_2)) Hlen) as Hlen_lh
    end.
    assert (Hidx_lh : 0 <= retval % 211 < Zlength lh) by (rewrite Hlen_lh; lia).
    entailer!.
    1: { unfold NBUCK.
      assert (Hnew : retval_2 <> NULL) by (unfold NULL; lia).
      pose proof (H8 (retval % 211) (Znth (retval % 211) lh 0)) as Hrepr_idx.
      assert (Hexists : exists l_idx, b (retval % 211) = Some (Znth (retval % 211) lh 0, l_idx)).
      { apply (proj2 Hrepr_idx). split; [exact Hidx_lh | reflexivity]. }
      destruct Hexists as [l_idx Hbidx].
      sepcon_lift (store_map store_sll b).
      sepcon_lift (&(retval_2 # "blist" ->ₛ "next") # Ptr |-> Znth (retval % 211) lh 0).
      sepcon_lift (PtrArray.full bucks_ph 211 (replace_Znth (retval % 211) retval_2 lh)).
      sepcon_assoc_change.
      set (R :=
        (dll top_ph retval_2 l **
         (&(retval_2 # "blist" ->ₛ "down") # Ptr |-> top_ph **
          (&(retval_2 # "blist" ->ₛ "up") # Ptr |-> 0 ** TT)))).
      eapply derivable1_trans.
      { apply (derivable1_sepcon_assoc1
          (PtrArray.full bucks_ph 211 (replace_Znth (retval % 211) retval_2 lh))
          (&(retval_2 # "blist" ->ₛ "next") # Ptr |-> Znth (retval % 211) lh 0)
          (store_map store_sll b ** R)). }
      eapply derivable1_trans.
      { apply (derivable1_sepcon_assoc1
          (PtrArray.full bucks_ph 211 (replace_Znth (retval % 211) retval_2 lh) **
           &(retval_2 # "blist" ->ₛ "next") # Ptr |-> Znth (retval % 211) lh 0)
          (store_map store_sll b)
          R). }
      eapply derivable1_trans.
      { apply (store_map_store_sll_update_at_idx_frame
          bucks_ph lh b (retval % 211) retval_2 l_idx R);
        [unfold NBUCK; lia | exact Hnew | exact Hbidx]. }
      subst R.
      sepcon_assoc_change.
      sepcon_lift (TT)%sac.
      set (P :=
        PtrArray.full bucks_ph 211 (replace_Znth (retval % 211) retval_2 lh) **
        (store_map store_sll (b' b (retval % 211) retval_2) **
         (dll top_ph retval_2 l **
          (&(retval_2 # "blist" ->ₛ "down") # Ptr |-> top_ph **
           &(retval_2 # "blist" ->ₛ "up") # Ptr |-> 0)))).
      change ((TT)%sac ** P
              |-- PtrArray.full bucks_ph 211 (replace_Znth (retval % 211) retval_2 lh) **
                  (dll retval_2 NULL (retval_2 :: l) **
                   store_map store_sll (b' b (retval % 211) retval_2))).
      rewrite (logic_equiv_sepcon_comm (TT)%sac P).
      eapply derivable1_trans.
      { apply sepcon_TT_elim. }
      subst P.
      simpl dll.
      Exists top_ph.
      entailer!.
    }
    all: try (eapply contain_all_correct_addrs_insert_update;
              [exact H10
              | unfold NBUCK; rewrite H6; rewrite Zrem_Zmod_pos by lia; reflexivity
              | exact H9]).
    all: try (eapply repr_all_heads_update; eauto).
    all: try (eapply contain_all_addrs_insert_cons; eauto).
Qed.

Lemma proof_of_hashtbl_add_which_implies_wit_1 : hashtbl_add_which_implies_wit_1.
Proof. 
  pre_process.
  unfold store_hash_skeleton.
  Intros l lh b top bucks.
  unfold NBUCK, NULL.
  Exists bucks top lh b l .
  entailer!.
  apply derivable1_truep_intros.
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
