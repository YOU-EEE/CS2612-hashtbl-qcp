Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.Morphisms.
Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import PL.AlgebraicStructure.
Require Import PL.Syntax.
Require Import PL.DenotationsOfExpr.
Require Import PL.DenotationsAsRels.
Import Lang_SimpleWhile
       StateModel_SimpleWhile1
       DntSem_SimpleWhile2
       DntSem_SimpleWhile3
       DntSem_SimpleWhile4.
Local Open Scope string.
Local Open Scope Z.
Local Open Scope sets.

(************)
(** 习题：  *)
(************)

(** 请试着在不使用_[sets_unfold]_或_[Sets_unfold]_的情况下证明下面集合运算的性质。*)

Fact Sets_ex1:
  forall {A: Type} (x y z: A -> Prop),
    x ⊆ y ->
    x ∪ z ⊆ z ∪ y.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


(************)
(** 习题：  *)
(************)

(** 请试着在不使用_[sets_unfold]_或_[Sets_unfold]_的情况下证明下面集合运算的性质。*)

Fact Sets_ex2:
  forall {A: Type} (x1 x2 y1 y2: A -> Prop),
    (x1 ∩ x2) ∪ (y1 ∩ y2) ⊆
    (x1 ∪ y1) ∩ (x2 ∪ y2).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)



(************)
(** 习题：  *)
(************)

(** 请试着在不使用_[sets_unfold]_或_[Sets_unfold]_的情况下证明下面集合运算的性质。*)

Fact IndexUnion_ex1:
  forall {A: Type} (xs: nat -> A -> Prop),
    ⋃ (fun n => xs (2 * n)%nat) ⊆ ⋃ xs.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


(************)
(** 习题：  *)
(************)

(** 请试着在不使用_[sets_unfold]_或_[Sets_unfold]_的情况下证明下面集合运算的性质。*)

Fact IndexUnion_ex2:
  forall {A: Type} (xs: nat -> A -> Prop),
    (forall n m, (n <= m)%nat -> xs n ⊆ xs m) ->
    ⋃ (fun n => xs (2 * n)%nat) == ⋃ xs.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)



(************)
(** 习题：  *)
(************)

(** 请证明下面二元关系的运算性质。*)

Example Rels_concat_ex1:
  forall (A: Type) (R1 R2: A -> A -> Prop),
    R1 ∘ R1 == ∅ ->
    R2 ∘ R2 == ∅ ->
    (R1 ∪ R2) ∘ (R1 ∪ R2) == R1 ∘ R2 ∪ R2 ∘ R1.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


(************)
(** 习题：  *)
(************)

(** 请证明下面二元关系的性质。*)

Example Rels_concat_ex2:
  forall (A: Type) (T R1 R2 R3: A -> A -> Prop),
    T ∘ R1 ⊆ R2 ->
    T ∘ R2 ⊆ R3 ->
    T ∘ R3 ⊆ R1 ->
    T ∘ (R1 ∪ R2 ∪ R3) ⊆ R1 ∪ R2 ∪ R3.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


(************)
(** 习题：  *)
(************)

(** 我们知道_[while (b) do { c }]_的语义满足一下等式：
   
          ⟦ while (b) do { c } ⟧ ==
          test_true ⟦ e ⟧ ∘ ⟦ c ⟧ ∘ ⟦ while (b) do { c } ⟧ ∪ test_false ⟦ e ⟧
      
    那么是否有其他程序状态上的二元关系_[R]_满足以下性质呢？
   
          R == test_true ⟦ e ⟧ ∘ ⟦ c ⟧ ∘ R ∪ test_false ⟦ e ⟧
      
    尽管下面的要你证明的这个结论并不能给出一个肯定或者否定的答案，但是至少也给出这样的
    _[R]_应当满足的一些基本性质。*)

Lemma while_sem_fact0:
  forall (e: expr_bool) (c: com) (R: state -> state -> Prop),
    test_true ⟦ e ⟧ ∘ ⟦ c ⟧ ∘ R ∪ test_false ⟦ e ⟧ ⊆ R ->
    while_sem ⟦ e ⟧ ⟦ c ⟧ ⊆ R.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


