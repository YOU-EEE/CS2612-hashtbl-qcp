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
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import hashtbl_lib.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.
From SimpleC.EE Require Import int_array_strategy_goal.
From SimpleC.EE Require Import int_array_strategy_proof.
From SimpleC.EE Require Import uint_array_strategy_goal.
From SimpleC.EE Require Import uint_array_strategy_proof.
From SimpleC.EE Require Import undef_uint_array_strategy_goal.
From SimpleC.EE Require Import undef_uint_array_strategy_proof.
From SimpleC.EE Require Import array_shape_strategy_goal.
From SimpleC.EE Require Import array_shape_strategy_proof.
From SimpleC.EE Require Import ptr_array_strategy_goal.
From SimpleC.EE Require Import ptr_array_strategy_proof.

(*----- Function create_bucks -----*)

Definition create_bucks_safety_wit_1 := 
forall (h_pre: Z) (content: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |]
  &&  (PtrArray.full retval 211 content )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> retval)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition create_bucks_safety_wit_2 := 
forall (h_pre: Z) (retval: Z) (content: (@list Z)) (bucks_base: Z) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i <= 211) |] 
  &&  [| ((sublist (0) (i) (content)) = (zeros (i))) |] 
  &&  [| (retval <> 0) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_base)
  **  (PtrArray.full bucks_base 211 content )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
|--
  [| (211 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 211) |]
.

Definition create_bucks_safety_wit_3 := 
forall (h_pre: Z) (retval: Z) (content: (@list Z)) (bucks_base: Z) (i: Z) ,
  [| (i < 211) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 211) |] 
  &&  [| ((sublist (0) (i) (content)) = (zeros (i))) |] 
  &&  [| (retval <> 0) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_base)
  **  (PtrArray.full bucks_base 211 content )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition create_bucks_safety_wit_4 := 
forall (h_pre: Z) (retval: Z) (content: (@list Z)) (bucks_base: Z) (i: Z) ,
  [| (i < 211) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 211) |] 
  &&  [| ((sublist (0) (i) (content)) = (zeros (i))) |] 
  &&  [| (retval <> 0) |]
  &&  (PtrArray.full bucks_base 211 (replace_Znth (i) (0) (content)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_base)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition create_bucks_entail_wit_1 := 
forall (h_pre: Z) (content_2: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |]
  &&  (PtrArray.full retval 211 content_2 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> retval)
|--
  EX (content: (@list Z))  (bucks_base: Z) ,
  [| (0 <= 0) |] 
  &&  [| (0 <= 211) |] 
  &&  [| ((sublist (0) (0) (content)) = (zeros (0))) |] 
  &&  [| (retval <> 0) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_base)
  **  (PtrArray.full bucks_base 211 content )
.

Definition create_bucks_entail_wit_2 := 
forall (h_pre: Z) (retval: Z) (content_2: (@list Z)) (bucks_base_2: Z) (i: Z) ,
  [| (i < 211) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 211) |] 
  &&  [| ((sublist (0) (i) (content_2)) = (zeros (i))) |] 
  &&  [| (retval <> 0) |]
  &&  (PtrArray.full bucks_base_2 211 (replace_Znth (i) (0) (content_2)) )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_base_2)
|--
  EX (content: (@list Z))  (bucks_base: Z) ,
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= 211) |] 
  &&  [| ((sublist (0) ((i + 1 )) (content)) = (zeros ((i + 1 )))) |] 
  &&  [| (retval <> 0) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_base)
  **  (PtrArray.full bucks_base 211 content )
.

Definition create_bucks_return_wit_1 := 
forall (h_pre: Z) (retval: Z) (content: (@list Z)) (bucks_base_2: Z) (i: Z) ,
  [| (i >= 211) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 211) |] 
  &&  [| ((sublist (0) (i) (content)) = (zeros (i))) |] 
  &&  [| (retval <> 0) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_base_2)
  **  (PtrArray.full bucks_base_2 211 content )
|--
  EX (bucks_base: Z) ,
  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_base)
  **  (PtrArray.full bucks_base 211 (zeros (211)) )
.

Definition create_bucks_partial_solve_wit_1 := 
forall (h_pre: Z) (bucks_random: Z) ,
  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_random)
|--
  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_random)
.

Definition create_bucks_partial_solve_wit_2 := 
forall (h_pre: Z) (retval: Z) (content: (@list Z)) (bucks_base: Z) (i: Z) ,
  [| (i < 211) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 211) |] 
  &&  [| ((sublist (0) (i) (content)) = (zeros (i))) |] 
  &&  [| (retval <> 0) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_base)
  **  (PtrArray.full bucks_base 211 content )
|--
  [| (i < 211) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 211) |] 
  &&  [| ((sublist (0) (i) (content)) = (zeros (i))) |] 
  &&  [| (retval <> 0) |]
  &&  (((bucks_base + (i * sizeof(PTR) ) )) # Ptr  |->_)
  **  (PtrArray.missing_i bucks_base i 0 211 content )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_base)
.

(*----- Function init_hashtbl -----*)

Definition init_hashtbl_safety_wit_1 := 
forall (h_pre: Z) (top_ph: Z) (bucks_ph: Z) ,
  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition init_hashtbl_safety_wit_2 := 
forall (h_pre: Z) (top_ph: Z) ,
  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> 0)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition init_hashtbl_return_wit_1 := 
forall (h_pre: Z) (bucks_base: Z) ,
  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_base)
  **  (PtrArray.full bucks_base 211 (zeros (211)) )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> 0)
|--
  (store_hash_skeleton h_pre empty_map )
.

Definition init_hashtbl_partial_solve_wit_1 := 
forall (h_pre: Z) ,
  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> 0)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> 0)
|--
  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> 0)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> 0)
.

(*----- Function create_hashtbl -----*)

Definition create_hashtbl_entail_wit_1 := 
forall (top_ph_2: Z) (bucks_ph_2: Z) (retval: Z) ,
  [| (retval <> 0) |]
  &&  ((&((retval)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph_2)
  **  ((&((retval)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph_2)
|--
  EX (top_ph: Z)  (bucks_ph: Z) ,
  [| (retval <> 0) |]
  &&  ((&((retval)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  ((&((retval)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
.

Definition create_hashtbl_return_wit_1 := 
forall (retval: Z) ,
  [| (retval <> 0) |]
  &&  (store_hash_skeleton retval empty_map )
|--
  (store_hash_skeleton retval empty_map )
  **  (store_map store_val empty_map )
.

Definition create_hashtbl_partial_solve_wit_1 := 
  TT && emp 
|--
  TT && emp 
.

Definition create_hashtbl_partial_solve_wit_2 := 
forall (retval: Z) (top_ph: Z) (bucks_ph: Z) ,
  [| (retval <> 0) |]
  &&  ((&((retval)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  ((&((retval)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
|--
  [| (retval <> 0) |]
  &&  ((&((retval)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  ((&((retval)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
.

(*----- Function hashtbl_add -----*)

Definition hashtbl_add_safety_wit_1 := 
forall (val_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (b: (Z -> (@option (Z * (@list Z))))) (lh: (@list Z)) (l: (@list Z)) (bucks_ph: Z) (top_ph: Z) (retval: Z) ,
  [| (0 <= retval) |] 
  &&  [| (retval <= 4294967295) |] 
  &&  [| (retval = (hash_string_k (k))) |] 
  &&  [| ((m1 (k)) = None) |]
  &&  (store_string key_pre k )
  **  ((( &( "buc" ) )) # Ptr  |->_)
  **  ((( &( "ind" ) )) # UInt  |->_)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.full bucks_ph 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
  **  (TT )
  **  ((( &( "val" ) )) # UInt  |-> val_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  (store_map store_val m2 )
|--
  [| (211 <> 0) |]
.

Definition hashtbl_add_safety_wit_2 := 
forall (val_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (b: (Z -> (@option (Z * (@list Z))))) (lh: (@list Z)) (l: (@list Z)) (bucks_ph: Z) (top_ph: Z) (retval: Z) ,
  [| (0 <= retval) |] 
  &&  [| (retval <= 4294967295) |] 
  &&  [| (retval = (hash_string_k (k))) |] 
  &&  [| ((m1 (k)) = None) |]
  &&  (store_string key_pre k )
  **  ((( &( "buc" ) )) # Ptr  |->_)
  **  ((( &( "ind" ) )) # UInt  |->_)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.full bucks_ph 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
  **  (TT )
  **  ((( &( "val" ) )) # UInt  |-> val_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  (store_map store_val m2 )
|--
  [| (211 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 211) |]
.

Definition hashtbl_add_safety_wit_3 := 
forall (val_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (b: (Z -> (@option (Z * (@list Z))))) (lh: (@list Z)) (l: (@list Z)) (bucks_ph: Z) (top_ph: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (retval % ( 211 ) )) |] 
  &&  [| ((retval % ( 211 ) ) < 211) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval <= 4294967295) |] 
  &&  [| (retval = (hash_string_k (k))) |] 
  &&  [| ((m1 (k)) = None) |]
  &&  ((&((retval_2)  # "blist" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "val")) # UInt  |-> val_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_2)  # "blist" ->ₛ "down")) # Ptr  |-> 0)
  **  ((&((retval_2)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((( &( "ind" ) )) # UInt  |-> (retval % ( 211 ) ))
  **  (store_string key_pre k )
  **  ((( &( "buc" ) )) # Ptr  |-> retval_2)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.full bucks_ph 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
  **  (TT )
  **  ((( &( "val" ) )) # UInt  |-> val_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  (store_map store_val m2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_add_safety_wit_4 := 
forall (val_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (b: (Z -> (@option (Z * (@list Z))))) (lh: (@list Z)) (l: (@list Z)) (bucks_ph: Z) (top_ph: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (retval % ( 211 ) )) |] 
  &&  [| ((retval % ( 211 ) ) < 211) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval <= 4294967295) |] 
  &&  [| (retval = (hash_string_k (k))) |] 
  &&  [| ((m1 (k)) = None) |]
  &&  ((&((retval_2)  # "blist" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "val")) # UInt  |-> val_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_2)  # "blist" ->ₛ "down")) # Ptr  |-> top_ph)
  **  ((&((retval_2)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((( &( "ind" ) )) # UInt  |-> (retval % ( 211 ) ))
  **  (store_string key_pre k )
  **  ((( &( "buc" ) )) # Ptr  |-> retval_2)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.full bucks_ph 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
  **  (TT )
  **  ((( &( "val" ) )) # UInt  |-> val_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  (store_map store_val m2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_add_entail_wit_1 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (b: (Z -> (@option (Z * (@list Z))))) (lh: (@list Z)) (l: (@list Z)) (bucks_ph: Z) (top_ph: Z) (retval: Z) ,
  [| (0 <= retval) |] 
  &&  [| (retval <= 4294967295) |] 
  &&  [| (retval = (hash_string_k (k))) |] 
  &&  [| ((m1 (k)) = None) |]
  &&  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.full bucks_ph 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
  **  (TT )
  **  (store_map store_val m2 )
|--
  [| (0 <= (retval % ( 211 ) )) |] 
  &&  [| ((retval % ( 211 ) ) < 211) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval <= 4294967295) |] 
  &&  [| (retval = (hash_string_k (k))) |] 
  &&  [| ((m1 (k)) = None) |]
  &&  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.full bucks_ph 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
  **  (TT )
  **  (store_map store_val m2 )
.

Definition hashtbl_add_return_wit_1 := 
forall (val_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (b: (Z -> (@option (Z * (@list Z))))) (lh: (@list Z)) (l: (@list Z)) (bucks_ph: Z) (top_ph: Z) (retval: Z) (retval_2: Z) ,
  [| (top_ph = 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (retval % ( 211 ) )) |] 
  &&  [| ((retval % ( 211 ) ) < 211) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval <= 4294967295) |] 
  &&  [| (retval = (hash_string_k (k))) |] 
  &&  [| ((m1 (k)) = None) |]
  &&  (PtrArray.full bucks_ph 211 (replace_Znth ((retval % ( 211 ) )) (retval_2) (lh)) )
  **  ((&((retval_2)  # "blist" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "val")) # UInt  |-> val_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "next")) # Ptr  |-> (Znth (retval % ( 211 ) ) lh 0))
  **  ((&((retval_2)  # "blist" ->ₛ "down")) # Ptr  |-> top_ph)
  **  ((&((retval_2)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> retval_2)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
  **  (TT )
  **  (store_map store_val m2 )
|--
  EX (p: Z) ,
  (store_hash_skeleton h_pre (KP.insert_map (m1) (k) (p)) )
  **  (store_map store_val (PV.insert_map (m2) (p) (val_pre)) )
.

Definition hashtbl_add_return_wit_2 := 
forall (val_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (b: (Z -> (@option (Z * (@list Z))))) (lh: (@list Z)) (l: (@list Z)) (bucks_ph: Z) (top_ph: Z) (retval: Z) (retval_2: Z) (top_down: Z) (l_tail: (@list Z)) ,
  [| (l = (cons (top_ph) (l_tail))) |] 
  &&  [| (top_ph <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (retval % ( 211 ) )) |] 
  &&  [| ((retval % ( 211 ) ) < 211) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval <= 4294967295) |] 
  &&  [| (retval = (hash_string_k (k))) |] 
  &&  [| ((m1 (k)) = None) |]
  &&  (PtrArray.full bucks_ph 211 (replace_Znth ((retval % ( 211 ) )) (retval_2) (lh)) )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> retval_2)
  **  ((&((top_ph)  # "blist" ->ₛ "down")) # Ptr  |-> top_down)
  **  ((&((top_ph)  # "blist" ->ₛ "up")) # Ptr  |-> retval_2)
  **  (TT )
  **  ((&((retval_2)  # "blist" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "val")) # UInt  |-> val_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "next")) # Ptr  |-> (Znth (retval % ( 211 ) ) lh 0))
  **  ((&((retval_2)  # "blist" ->ₛ "down")) # Ptr  |-> top_ph)
  **  ((&((retval_2)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
  **  (TT )
  **  (store_map store_val m2 )
|--
  EX (p: Z) ,
  (store_hash_skeleton h_pre (KP.insert_map (m1) (k) (p)) )
  **  (store_map store_val (PV.insert_map (m2) (p) (val_pre)) )
.

Definition hashtbl_add_partial_solve_wit_1 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) ,
  [| ((m1 (k)) = None) |]
  &&  (store_hash_skeleton h_pre m1 )
  **  (store_map store_val m2 )
  **  (store_string key_pre k )
|--
  [| ((m1 (k)) = None) |]
  &&  (store_hash_skeleton h_pre m1 )
  **  (store_map store_val m2 )
  **  (store_string key_pre k )
.

Definition hashtbl_add_partial_solve_wit_2 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (b: (Z -> (@option (Z * (@list Z))))) (lh: (@list Z)) (l: (@list Z)) (bucks_ph: Z) (top_ph: Z) ,
  [| ((m1 (k)) = None) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.full bucks_ph 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
  **  (TT )
  **  (store_map store_val m2 )
  **  (store_string key_pre k )
|--
  [| ((m1 (k)) = None) |]
  &&  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.full bucks_ph 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
  **  (TT )
  **  (store_map store_val m2 )
.

Definition hashtbl_add_partial_solve_wit_3 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (b: (Z -> (@option (Z * (@list Z))))) (lh: (@list Z)) (l: (@list Z)) (bucks_ph: Z) (top_ph: Z) (retval: Z) ,
  [| (0 <= (retval % ( 211 ) )) |] 
  &&  [| ((retval % ( 211 ) ) < 211) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval <= 4294967295) |] 
  &&  [| (retval = (hash_string_k (k))) |] 
  &&  [| ((m1 (k)) = None) |]
  &&  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.full bucks_ph 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
  **  (TT )
  **  (store_map store_val m2 )
|--
  [| (0 <= (retval % ( 211 ) )) |] 
  &&  [| ((retval % ( 211 ) ) < 211) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval <= 4294967295) |] 
  &&  [| (retval = (hash_string_k (k))) |] 
  &&  [| ((m1 (k)) = None) |]
  &&  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.full bucks_ph 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
  **  (TT )
  **  (store_map store_val m2 )
.

Definition hashtbl_add_partial_solve_wit_4_pure := 
forall (val_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (b: (Z -> (@option (Z * (@list Z))))) (lh: (@list Z)) (l: (@list Z)) (bucks_ph: Z) (top_ph: Z) (retval: Z) (retval_2: Z) ,
  [| (top_ph <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (retval % ( 211 ) )) |] 
  &&  [| ((retval % ( 211 ) ) < 211) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval <= 4294967295) |] 
  &&  [| (retval = (hash_string_k (k))) |] 
  &&  [| ((m1 (k)) = None) |]
  &&  ((&((retval_2)  # "blist" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "val")) # UInt  |-> val_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_2)  # "blist" ->ₛ "down")) # Ptr  |-> top_ph)
  **  ((&((retval_2)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((( &( "ind" ) )) # UInt  |-> (retval % ( 211 ) ))
  **  (store_string key_pre k )
  **  ((( &( "buc" ) )) # Ptr  |-> retval_2)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.full bucks_ph 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
  **  (TT )
  **  ((( &( "val" ) )) # UInt  |-> val_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  (store_map store_val m2 )
|--
  [| (top_ph <> 0) |]
.

Definition hashtbl_add_partial_solve_wit_4_aux := 
forall (val_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (b: (Z -> (@option (Z * (@list Z))))) (lh: (@list Z)) (l: (@list Z)) (bucks_ph: Z) (top_ph: Z) (retval: Z) (retval_2: Z) ,
  [| (top_ph <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (retval % ( 211 ) )) |] 
  &&  [| ((retval % ( 211 ) ) < 211) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval <= 4294967295) |] 
  &&  [| (retval = (hash_string_k (k))) |] 
  &&  [| ((m1 (k)) = None) |]
  &&  ((&((retval_2)  # "blist" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "val")) # UInt  |-> val_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_2)  # "blist" ->ₛ "down")) # Ptr  |-> top_ph)
  **  ((&((retval_2)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.full bucks_ph 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
  **  (TT )
  **  (store_map store_val m2 )
|--
  [| (top_ph <> 0) |] 
  &&  [| (top_ph <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (retval % ( 211 ) )) |] 
  &&  [| ((retval % ( 211 ) ) < 211) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval <= 4294967295) |] 
  &&  [| (retval = (hash_string_k (k))) |] 
  &&  [| ((m1 (k)) = None) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  (dll top_ph 0 l )
  **  ((&((retval_2)  # "blist" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "val")) # UInt  |-> val_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_2)  # "blist" ->ₛ "down")) # Ptr  |-> top_ph)
  **  ((&((retval_2)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (PtrArray.full bucks_ph 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
  **  (TT )
  **  (store_map store_val m2 )
.

Definition hashtbl_add_partial_solve_wit_4 := hashtbl_add_partial_solve_wit_4_pure -> hashtbl_add_partial_solve_wit_4_aux.

Definition hashtbl_add_partial_solve_wit_5 := 
forall (val_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (b: (Z -> (@option (Z * (@list Z))))) (lh: (@list Z)) (l: (@list Z)) (bucks_ph: Z) (top_ph: Z) (retval: Z) (retval_2: Z) ,
  [| (top_ph = 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (retval % ( 211 ) )) |] 
  &&  [| ((retval % ( 211 ) ) < 211) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval <= 4294967295) |] 
  &&  [| (retval = (hash_string_k (k))) |] 
  &&  [| ((m1 (k)) = None) |]
  &&  ((&((retval_2)  # "blist" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "val")) # UInt  |-> val_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_2)  # "blist" ->ₛ "down")) # Ptr  |-> top_ph)
  **  ((&((retval_2)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> retval_2)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.full bucks_ph 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
  **  (TT )
  **  (store_map store_val m2 )
|--
  [| (top_ph = 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (retval % ( 211 ) )) |] 
  &&  [| ((retval % ( 211 ) ) < 211) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval <= 4294967295) |] 
  &&  [| (retval = (hash_string_k (k))) |] 
  &&  [| ((m1 (k)) = None) |]
  &&  (((bucks_ph + ((retval % ( 211 ) ) * sizeof(PTR) ) )) # Ptr  |-> (Znth (retval % ( 211 ) ) lh 0))
  **  (PtrArray.missing_i bucks_ph (retval % ( 211 ) ) 0 211 lh )
  **  ((&((retval_2)  # "blist" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "val")) # UInt  |-> val_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_2)  # "blist" ->ₛ "down")) # Ptr  |-> top_ph)
  **  ((&((retval_2)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> retval_2)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
  **  (TT )
  **  (store_map store_val m2 )
.

Definition hashtbl_add_partial_solve_wit_6 := 
forall (val_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (b: (Z -> (@option (Z * (@list Z))))) (lh: (@list Z)) (l: (@list Z)) (bucks_ph: Z) (top_ph: Z) (retval: Z) (retval_2: Z) (top_down: Z) (l_tail: (@list Z)) ,
  [| (l = (cons (top_ph) (l_tail))) |] 
  &&  [| (top_ph <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (retval % ( 211 ) )) |] 
  &&  [| ((retval % ( 211 ) ) < 211) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval <= 4294967295) |] 
  &&  [| (retval = (hash_string_k (k))) |] 
  &&  [| ((m1 (k)) = None) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> retval_2)
  **  ((&((top_ph)  # "blist" ->ₛ "down")) # Ptr  |-> top_down)
  **  ((&((top_ph)  # "blist" ->ₛ "up")) # Ptr  |-> retval_2)
  **  (TT )
  **  ((&((retval_2)  # "blist" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "val")) # UInt  |-> val_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_2)  # "blist" ->ₛ "down")) # Ptr  |-> top_ph)
  **  ((&((retval_2)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (PtrArray.full bucks_ph 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
  **  (TT )
  **  (store_map store_val m2 )
|--
  [| (l = (cons (top_ph) (l_tail))) |] 
  &&  [| (top_ph <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (retval % ( 211 ) )) |] 
  &&  [| ((retval % ( 211 ) ) < 211) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval <= 4294967295) |] 
  &&  [| (retval = (hash_string_k (k))) |] 
  &&  [| ((m1 (k)) = None) |]
  &&  (((bucks_ph + ((retval % ( 211 ) ) * sizeof(PTR) ) )) # Ptr  |-> (Znth (retval % ( 211 ) ) lh 0))
  **  (PtrArray.missing_i bucks_ph (retval % ( 211 ) ) 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> retval_2)
  **  ((&((top_ph)  # "blist" ->ₛ "down")) # Ptr  |-> top_down)
  **  ((&((top_ph)  # "blist" ->ₛ "up")) # Ptr  |-> retval_2)
  **  (TT )
  **  ((&((retval_2)  # "blist" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "val")) # UInt  |-> val_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_2)  # "blist" ->ₛ "down")) # Ptr  |-> top_ph)
  **  ((&((retval_2)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
  **  (TT )
  **  (store_map store_val m2 )
.

Definition hashtbl_add_partial_solve_wit_7 := 
forall (val_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (b: (Z -> (@option (Z * (@list Z))))) (lh: (@list Z)) (l: (@list Z)) (bucks_ph: Z) (top_ph: Z) (retval: Z) (retval_2: Z) (top_down: Z) (l_tail: (@list Z)) ,
  [| (l = (cons (top_ph) (l_tail))) |] 
  &&  [| (top_ph <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (retval % ( 211 ) )) |] 
  &&  [| ((retval % ( 211 ) ) < 211) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval <= 4294967295) |] 
  &&  [| (retval = (hash_string_k (k))) |] 
  &&  [| ((m1 (k)) = None) |]
  &&  (PtrArray.full bucks_ph 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> retval_2)
  **  ((&((top_ph)  # "blist" ->ₛ "down")) # Ptr  |-> top_down)
  **  ((&((top_ph)  # "blist" ->ₛ "up")) # Ptr  |-> retval_2)
  **  (TT )
  **  ((&((retval_2)  # "blist" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "val")) # UInt  |-> val_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "next")) # Ptr  |-> (Znth (retval % ( 211 ) ) lh 0))
  **  ((&((retval_2)  # "blist" ->ₛ "down")) # Ptr  |-> top_ph)
  **  ((&((retval_2)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
  **  (TT )
  **  (store_map store_val m2 )
|--
  [| (l = (cons (top_ph) (l_tail))) |] 
  &&  [| (top_ph <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (retval % ( 211 ) )) |] 
  &&  [| ((retval % ( 211 ) ) < 211) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval <= 4294967295) |] 
  &&  [| (retval = (hash_string_k (k))) |] 
  &&  [| ((m1 (k)) = None) |]
  &&  (((bucks_ph + ((retval % ( 211 ) ) * sizeof(PTR) ) )) # Ptr  |->_)
  **  (PtrArray.missing_i bucks_ph (retval % ( 211 ) ) 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> retval_2)
  **  ((&((top_ph)  # "blist" ->ₛ "down")) # Ptr  |-> top_down)
  **  ((&((top_ph)  # "blist" ->ₛ "up")) # Ptr  |-> retval_2)
  **  (TT )
  **  ((&((retval_2)  # "blist" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "val")) # UInt  |-> val_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "next")) # Ptr  |-> (Znth (retval % ( 211 ) ) lh 0))
  **  ((&((retval_2)  # "blist" ->ₛ "down")) # Ptr  |-> top_ph)
  **  ((&((retval_2)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
  **  (TT )
  **  (store_map store_val m2 )
.

Definition hashtbl_add_partial_solve_wit_8 := 
forall (val_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (b: (Z -> (@option (Z * (@list Z))))) (lh: (@list Z)) (l: (@list Z)) (bucks_ph: Z) (top_ph: Z) (retval: Z) (retval_2: Z) ,
  [| (top_ph = 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (retval % ( 211 ) )) |] 
  &&  [| ((retval % ( 211 ) ) < 211) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval <= 4294967295) |] 
  &&  [| (retval = (hash_string_k (k))) |] 
  &&  [| ((m1 (k)) = None) |]
  &&  (PtrArray.full bucks_ph 211 lh )
  **  ((&((retval_2)  # "blist" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "val")) # UInt  |-> val_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "next")) # Ptr  |-> (Znth (retval % ( 211 ) ) lh 0))
  **  ((&((retval_2)  # "blist" ->ₛ "down")) # Ptr  |-> top_ph)
  **  ((&((retval_2)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> retval_2)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
  **  (TT )
  **  (store_map store_val m2 )
|--
  [| (top_ph = 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (retval % ( 211 ) )) |] 
  &&  [| ((retval % ( 211 ) ) < 211) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval <= 4294967295) |] 
  &&  [| (retval = (hash_string_k (k))) |] 
  &&  [| ((m1 (k)) = None) |]
  &&  (((bucks_ph + ((retval % ( 211 ) ) * sizeof(PTR) ) )) # Ptr  |->_)
  **  (PtrArray.missing_i bucks_ph (retval % ( 211 ) ) 0 211 lh )
  **  ((&((retval_2)  # "blist" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "val")) # UInt  |-> val_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "next")) # Ptr  |-> (Znth (retval % ( 211 ) ) lh 0))
  **  ((&((retval_2)  # "blist" ->ₛ "down")) # Ptr  |-> top_ph)
  **  ((&((retval_2)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> retval_2)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
  **  (TT )
  **  (store_map store_val m2 )
.

Definition hashtbl_add_which_implies_wit_1 := 
forall (m1: ((@list Z) -> (@option Z))) (h: Z) ,
  (store_hash_skeleton h m1 )
|--
  EX (b: (Z -> (@option (Z * (@list Z)))))  (lh: (@list Z))  (l: (@list Z))  (bucks_ph: Z)  (top_ph: Z) ,
  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.full bucks_ph 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
  **  (TT )
.

Definition hashtbl_add_which_implies_wit_2 := 
forall (l: (@list Z)) (top_ph: Z) (h: Z) ,
  [| (top_ph <> 0) |]
  &&  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  (dll top_ph 0 l )
|--
  EX (top_up: Z)  (top_down: Z)  (l_tail: (@list Z)) ,
  [| (l = (cons (top_ph) (l_tail))) |]
  &&  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((top_ph)  # "blist" ->ₛ "down")) # Ptr  |-> top_down)
  **  ((&((top_ph)  # "blist" ->ₛ "up")) # Ptr  |-> top_up)
  **  (TT )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.
Include ptr_array_Strategy_Correct.

Axiom proof_of_create_bucks_safety_wit_1 : create_bucks_safety_wit_1.
Axiom proof_of_create_bucks_safety_wit_2 : create_bucks_safety_wit_2.
Axiom proof_of_create_bucks_safety_wit_3 : create_bucks_safety_wit_3.
Axiom proof_of_create_bucks_safety_wit_4 : create_bucks_safety_wit_4.
Axiom proof_of_create_bucks_entail_wit_1 : create_bucks_entail_wit_1.
Axiom proof_of_create_bucks_entail_wit_2 : create_bucks_entail_wit_2.
Axiom proof_of_create_bucks_return_wit_1 : create_bucks_return_wit_1.
Axiom proof_of_create_bucks_partial_solve_wit_1 : create_bucks_partial_solve_wit_1.
Axiom proof_of_create_bucks_partial_solve_wit_2 : create_bucks_partial_solve_wit_2.
Axiom proof_of_init_hashtbl_safety_wit_1 : init_hashtbl_safety_wit_1.
Axiom proof_of_init_hashtbl_safety_wit_2 : init_hashtbl_safety_wit_2.
Axiom proof_of_init_hashtbl_return_wit_1 : init_hashtbl_return_wit_1.
Axiom proof_of_init_hashtbl_partial_solve_wit_1 : init_hashtbl_partial_solve_wit_1.
Axiom proof_of_create_hashtbl_entail_wit_1 : create_hashtbl_entail_wit_1.
Axiom proof_of_create_hashtbl_return_wit_1 : create_hashtbl_return_wit_1.
Axiom proof_of_create_hashtbl_partial_solve_wit_1 : create_hashtbl_partial_solve_wit_1.
Axiom proof_of_create_hashtbl_partial_solve_wit_2 : create_hashtbl_partial_solve_wit_2.
Axiom proof_of_hashtbl_add_safety_wit_1 : hashtbl_add_safety_wit_1.
Axiom proof_of_hashtbl_add_safety_wit_2 : hashtbl_add_safety_wit_2.
Axiom proof_of_hashtbl_add_safety_wit_3 : hashtbl_add_safety_wit_3.
Axiom proof_of_hashtbl_add_safety_wit_4 : hashtbl_add_safety_wit_4.
Axiom proof_of_hashtbl_add_entail_wit_1 : hashtbl_add_entail_wit_1.
Axiom proof_of_hashtbl_add_return_wit_1 : hashtbl_add_return_wit_1.
Axiom proof_of_hashtbl_add_return_wit_2 : hashtbl_add_return_wit_2.
Axiom proof_of_hashtbl_add_partial_solve_wit_1 : hashtbl_add_partial_solve_wit_1.
Axiom proof_of_hashtbl_add_partial_solve_wit_2 : hashtbl_add_partial_solve_wit_2.
Axiom proof_of_hashtbl_add_partial_solve_wit_3 : hashtbl_add_partial_solve_wit_3.
Axiom proof_of_hashtbl_add_partial_solve_wit_4_pure : hashtbl_add_partial_solve_wit_4_pure.
Axiom proof_of_hashtbl_add_partial_solve_wit_4 : hashtbl_add_partial_solve_wit_4.
Axiom proof_of_hashtbl_add_partial_solve_wit_5 : hashtbl_add_partial_solve_wit_5.
Axiom proof_of_hashtbl_add_partial_solve_wit_6 : hashtbl_add_partial_solve_wit_6.
Axiom proof_of_hashtbl_add_partial_solve_wit_7 : hashtbl_add_partial_solve_wit_7.
Axiom proof_of_hashtbl_add_partial_solve_wit_8 : hashtbl_add_partial_solve_wit_8.
Axiom proof_of_hashtbl_add_which_implies_wit_1 : hashtbl_add_which_implies_wit_1.
Axiom proof_of_hashtbl_add_which_implies_wit_2 : hashtbl_add_which_implies_wit_2.

End VC_Correct.
