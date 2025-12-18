Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition ptr_array_strategy1 :=
  forall (i : Z) (n : Z) (p : Z) (l : (@list Z)),
    TT &&
    ([| (Z.le 0 i) |]) &&
    ([| (Z.lt i n) |]) &&
    emp **
    ((PtrArray.full p n l))
    |--
    (
    TT &&
    emp **
    ((PtrArray.missing_i p i 0 n l))
    ) ** (
    ALL (v : Z),
      TT &&
      ([| (v = (Znth i l  0)) |]) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_ptr (Z.add p (Z.mul i (@sizeof_front_end_type FET_ptr))) v))
      ).

Definition ptr_array_strategy4 :=
  forall (p : Z) (l1 : (@list Z)) (n : Z),
    TT &&
    emp **
    ((PtrArray.full p n l1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l2 : (@list Z)),
      TT &&
      ([| (l1 = l2) |]) &&
      emp -*
      TT &&
      emp **
      ((PtrArray.full p n l2))
      ).

Definition ptr_array_strategy5 :=
  forall (p : Z) (v : Z) (l : (@list Z)) (n : Z) (i : Z),
    TT &&
    emp **
    ((PtrArray.missing_i p i v n l))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((PtrArray.missing_i p i v n l))
    ).

Definition ptr_array_strategy6 :=
  forall (p : Z) (y : Z) (l1 : (@list Z)) (x : Z),
    TT &&
    emp **
    ((PtrArray.ceil p x y l1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l2 : (@list Z)),
      TT &&
      ([| (l1 = l2) |]) &&
      emp -*
      TT &&
      emp **
      ((PtrArray.ceil p x y l2))
      ).

Definition ptr_array_strategy7 :=
  forall (i : Z) (y : Z) (x : Z) (p : Z) (l : (@list Z)),
    TT &&
    ([| (Z.le x i) |]) &&
    ([| (Z.lt i y) |]) &&
    emp **
    ((PtrArray.ceil p x y l))
    |--
    (
    TT &&
    emp **
    ((PtrArray.missing_i p i x y l))
    ) ** (
    ALL Ptr (v : Z),
      TT &&
      ([| (v = (Znth (Z.sub i x) l  0)) |]) &&
      emp -*
      TT &&
      emp **
      ((poly_store Ptr (Z.add p (Z.mul i (@sizeof_front_end_type FET_ptr))) v))
      ).

Definition ptr_array_strategy8 :=
  forall (x : Z) (y : Z) (z : Z) (l1 : (@list Z)) (p : Z) (l2 : (@list Z)),
    TT &&
    ([| (Z.le y z) |]) &&
    ([| (Z.le x y) |]) &&
    emp **
    ((PtrArray.ceil p x y l1)) **
    ((PtrArray.ceil p y z l2))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l3 : (@list Z)),
      TT &&
      ([| (l3 = (@app Z l1 l2)) |]) &&
      emp -*
      TT &&
      emp **
      ((PtrArray.ceil p x z l3))
      ).

Definition ptr_array_strategy9 :=
  forall (x : Z) (y : Z) (z : Z) (p : Z) (l3 : (@list Z)),
    TT &&
    ([| (Z.le y z) |]) &&
    ([| (Z.le x y) |]) &&
    emp **
    ((PtrArray.ceil p x z l3))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l1 : (@list Z)) (l2 : (@list Z)),
      TT &&
      ([| (l3 = (@app Z l1 l2)) |]) &&
      ([| ((@Zlength Z l1) = (Z.sub y x)) |]) &&
      emp -*
      TT &&
      emp **
      ((PtrArray.ceil p x y l1)) **
      ((PtrArray.ceil p y z l2))
      ).

Definition ptr_array_strategy10 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (l : (@list Z)) (p : Z) (x : Z),
    TT &&
    ([| (l = (@nil Z)) |]) &&
    emp -*
    TT &&
    emp **
    ((PtrArray.ceil p x x l))
    ).

Definition ptr_array_strategy2 :=
  forall (i : Z) (n : Z) (l : (@list Z)) (p : Z),
    TT &&
    ([| (Z.le 0 i) |]) &&
    ([| (Z.lt i n) |]) &&
    emp **
    ((PtrArray.missing_i p i 0 n l)) **
    ((poly_store FET_ptr (Z.add p (Z.mul i (@sizeof_front_end_type FET_ptr))) (Znth i l  0)))
    |--
    (
    TT &&
    emp **
    ((PtrArray.full p n l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition ptr_array_strategy11 :=
  forall (i : Z) (y : Z) (x : Z) (l : (@list Z)) (p : Z),
    TT &&
    ([| (Z.le x i) |]) &&
    ([| (Z.lt i y) |]) &&
    emp **
    ((PtrArray.missing_i p i x y l)) **
    ((poly_store FET_ptr (Z.add p (Z.mul i (@sizeof_front_end_type FET_ptr))) (Znth (Z.sub i x) l  0)))
    |--
    (
    TT &&
    emp **
    ((PtrArray.ceil p x y l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition ptr_array_strategy3 :=
  forall (i : Z) (n : Z) (l : (@list Z)) (v : Z) (p : Z),
    TT &&
    ([| (Z.le 0 i) |]) &&
    ([| (Z.lt i n) |]) &&
    emp **
    ((PtrArray.missing_i p i 0 n l)) **
    ((poly_store FET_ptr (Z.add p (Z.mul i (@sizeof_front_end_type FET_ptr))) v))
    |--
    (
    TT &&
    emp **
    ((PtrArray.full p n (@replace_Znth Z i v l)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition ptr_array_strategy12 :=
  forall (i : Z) (y : Z) (x : Z) (l : (@list Z)) (v : Z) (p : Z),
    TT &&
    ([| (Z.le x i) |]) &&
    ([| (Z.lt i y) |]) &&
    emp **
    ((PtrArray.missing_i p i x y l)) **
    ((poly_store FET_ptr (Z.add p (Z.mul i (@sizeof_front_end_type FET_ptr))) v))
    |--
    (
    TT &&
    emp **
    ((PtrArray.ceil p x y (@replace_Znth Z (Z.sub i x) v l)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type ptr_array_Strategy_Correct.

  Axiom ptr_array_strategy1_correctness : ptr_array_strategy1.
  Axiom ptr_array_strategy4_correctness : ptr_array_strategy4.
  Axiom ptr_array_strategy5_correctness : ptr_array_strategy5.
  Axiom ptr_array_strategy6_correctness : ptr_array_strategy6.
  Axiom ptr_array_strategy7_correctness : ptr_array_strategy7.
  Axiom ptr_array_strategy8_correctness : ptr_array_strategy8.
  Axiom ptr_array_strategy9_correctness : ptr_array_strategy9.
  Axiom ptr_array_strategy10_correctness : ptr_array_strategy10.
  Axiom ptr_array_strategy2_correctness : ptr_array_strategy2.
  Axiom ptr_array_strategy11_correctness : ptr_array_strategy11.
  Axiom ptr_array_strategy3_correctness : ptr_array_strategy3.
  Axiom ptr_array_strategy12_correctness : ptr_array_strategy12.

End ptr_array_Strategy_Correct.
