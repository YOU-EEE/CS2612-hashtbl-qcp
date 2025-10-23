Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.Morphisms.
Require Import SetsClass.SetsClass. Import SetsNotation.
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

(** 请证明下面关于行为等价的性质。*)

Theorem if_seq:
  forall e c1 c2 c3,
    [[ if (e) then { c1 } else { c2 }; c3 ]] ~=~
    [[ if (e) then { c1; c3 } else { c2; c3 } ]].
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


(************)
(** 习题：  *)
(************)

(** 请证明下面关于行为等价的性质。*)

Theorem if_not:
  forall e c1 c2,
    [[ if (! e) then { c1 } else { c2 } ]] ~=~
    [[ if (e) then { c2 } else { c1 } ]].
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


