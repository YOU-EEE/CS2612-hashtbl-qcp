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
forall (val_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (bucks_ph: Z) (top_ph: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (retval: Z) ,
  [| (0 <= retval) |] 
  &&  [| (retval <= 4294967295) |] 
  &&  [| (retval = (hash_string_k (k))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
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
forall (val_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (bucks_ph: Z) (top_ph: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (retval: Z) ,
  [| (0 <= retval) |] 
  &&  [| (retval <= 4294967295) |] 
  &&  [| (retval = (hash_string_k (k))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
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
forall (val_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (bucks_ph: Z) (top_ph: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (retval % ( 211 ) )) |] 
  &&  [| ((retval % ( 211 ) ) < 211) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval <= 4294967295) |] 
  &&  [| (retval = (hash_string_k (k))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
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
forall (val_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (bucks_ph: Z) (top_ph: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (retval % ( 211 ) )) |] 
  &&  [| ((retval % ( 211 ) ) < 211) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval <= 4294967295) |] 
  &&  [| (retval = (hash_string_k (k))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
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
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (bucks_ph: Z) (top_ph: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (retval: Z) ,
  [| (0 <= retval) |] 
  &&  [| (retval <= 4294967295) |] 
  &&  [| (retval = (hash_string_k (k))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
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
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
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
forall (val_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (bucks_ph: Z) (top_ph: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (top_ph = 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (retval % ( 211 ) )) |] 
  &&  [| ((retval % ( 211 ) ) < 211) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval <= 4294967295) |] 
  &&  [| (retval = (hash_string_k (k))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
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
forall (val_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (bucks_ph: Z) (top_ph: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (retval: Z) (retval_2: Z) (top_down: Z) (l_tail: (@list Z)) ,
  [| (l = (cons (top_ph) (l_tail))) |] 
  &&  [| (top_ph <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (retval % ( 211 ) )) |] 
  &&  [| ((retval % ( 211 ) ) < 211) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval <= 4294967295) |] 
  &&  [| (retval = (hash_string_k (k))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((m1 (k)) = None) |]
  &&  (PtrArray.full bucks_ph 211 (replace_Znth ((retval % ( 211 ) )) (retval_2) (lh)) )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> retval_2)
  **  (dll top_ph retval_2 l )
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
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (bucks_ph: Z) (top_ph: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) ,
  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| ((m1 (k)) = None) |]
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
  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
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

Definition hashtbl_add_partial_solve_wit_3 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (bucks_ph: Z) (top_ph: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (retval: Z) ,
  [| (0 <= (retval % ( 211 ) )) |] 
  &&  [| ((retval % ( 211 ) ) < 211) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval <= 4294967295) |] 
  &&  [| (retval = (hash_string_k (k))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
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
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
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
forall (val_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (bucks_ph: Z) (top_ph: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (top_ph <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (retval % ( 211 ) )) |] 
  &&  [| ((retval % ( 211 ) ) < 211) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval <= 4294967295) |] 
  &&  [| (retval = (hash_string_k (k))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
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
forall (val_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (bucks_ph: Z) (top_ph: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (top_ph <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (retval % ( 211 ) )) |] 
  &&  [| ((retval % ( 211 ) ) < 211) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval <= 4294967295) |] 
  &&  [| (retval = (hash_string_k (k))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
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
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
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
forall (val_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (bucks_ph: Z) (top_ph: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (top_ph = 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (retval % ( 211 ) )) |] 
  &&  [| ((retval % ( 211 ) ) < 211) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval <= 4294967295) |] 
  &&  [| (retval = (hash_string_k (k))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
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
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
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
forall (val_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (bucks_ph: Z) (top_ph: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (retval: Z) (retval_2: Z) (top_down: Z) (l_tail: (@list Z)) ,
  [| (l = (cons (top_ph) (l_tail))) |] 
  &&  [| (top_ph <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (retval % ( 211 ) )) |] 
  &&  [| ((retval % ( 211 ) ) < 211) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval <= 4294967295) |] 
  &&  [| (retval = (hash_string_k (k))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
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
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
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
forall (val_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (bucks_ph: Z) (top_ph: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (retval: Z) (retval_2: Z) (top_down: Z) (l_tail: (@list Z)) ,
  [| (l = (cons (top_ph) (l_tail))) |] 
  &&  [| (top_ph <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (retval % ( 211 ) )) |] 
  &&  [| ((retval % ( 211 ) ) < 211) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval <= 4294967295) |] 
  &&  [| (retval = (hash_string_k (k))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
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
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
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
forall (val_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (bucks_ph: Z) (top_ph: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (top_ph = 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (retval % ( 211 ) )) |] 
  &&  [| ((retval % ( 211 ) ) < 211) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval <= 4294967295) |] 
  &&  [| (retval = (hash_string_k (k))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
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
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
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
  EX (bucks_ph: Z)  (top_ph: Z)  (lh: (@list Z))  (b: (Z -> (@option (Z * (@list Z)))))  (l: (@list Z)) ,
  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
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

(*----- Function hashtbl_find -----*)

Definition hashtbl_find_safety_wit_1 := 
forall (valid_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (bucks_ph: Z) (top_ph: Z) (retval: Z) ,
  [| (0 <= retval) |] 
  &&  [| (retval <= 4294967295) |] 
  &&  [| (retval = (hash_string_k (k))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  (store_string key_pre k )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.full bucks_ph 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
  **  ((( &( "i" ) )) # Ptr  |->_)
  **  ((( &( "ind" ) )) # UInt  |->_)
  **  ((( &( "valid" ) )) # Ptr  |-> valid_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  (store_map store_uint m2 )
  **  ((valid_pre) # Int  |->_)
|--
  [| (211 <> 0) |]
.

Definition hashtbl_find_safety_wit_2 := 
forall (valid_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (bucks_ph: Z) (top_ph: Z) (retval: Z) ,
  [| (0 <= retval) |] 
  &&  [| (retval <= 4294967295) |] 
  &&  [| (retval = (hash_string_k (k))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  (store_string key_pre k )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.full bucks_ph 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
  **  ((( &( "i" ) )) # Ptr  |->_)
  **  ((( &( "ind" ) )) # UInt  |->_)
  **  ((( &( "valid" ) )) # Ptr  |-> valid_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  (store_map store_uint m2 )
  **  ((valid_pre) # Int  |->_)
|--
  [| (211 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 211) |]
.

Definition hashtbl_find_safety_wit_3 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (valid: Z) (key: Z) (i_v: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (lh: (@list Z)) (l: (@list Z)) (bucks_ph: Z) (top_ph: Z) (h: Z) (ind: Z) ,
  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| forall (x: Z) , ~(((In x l1 ) /\ ((m1 (k)) = (Some (x))))) |]
  &&  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind (Znth (ind) (lh) (0)) 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m1 )
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR) ) ) i l1 )
  **  ((i) # Ptr  |-> i_v)
  **  (sll i_v l2 )
  **  (store_map store_uint m2 )
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  (store_string key k )
  **  ((( &( "valid" ) )) # Ptr  |-> valid)
  **  ((valid) # Int  |->_)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_find_safety_wit_4 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (l1: (@list Z)) (l2: (@list Z)) (top_ph: Z) (bucks_ph: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (kp: Z) (vp: Z) (p_next: Z) (k_cur: (@list Z)) (l_tail: (@list Z)) (h_val: Z) (t_l1: (@list Z)) (ind: Z) (i: Z) (i_v: Z) (h: Z) (key: Z) (valid: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (k <> k_cur) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| (l2 = (cons (i_v) (l_tail))) |] 
  &&  [| ((m1 (k_cur)) = (Some (&((i_v)  # "blist" ->ₛ "key")))) |] 
  &&  [| ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) |] 
  &&  [| (l1 <> nil) |] 
  &&  [| (l1 = (cons (h_val) (t_l1))) |] 
  &&  [| (h_val = (Znth (ind) (lh) (0))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| forall (x: Z) , ~(((In x l1 ) /\ ((m1 (k)) = (Some (x))))) |]
  &&  (store_string key k )
  **  (store_string kp k_cur )
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  ((i) # Ptr  |-> i_v)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind (Znth (ind) (lh) (0)) 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m1 )
  **  (((bucks_ph + (ind * sizeof(PTR) ) )) # Ptr  |-> h_val)
  **  (sllbseg &((h_val)  # "blist" ->ₛ "next") i t_l1 )
  **  (store_map store_uint m2 )
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "valid" ) )) # Ptr  |-> valid)
  **  ((valid) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l_tail )
|--
  [| False |]
.

Definition hashtbl_find_safety_wit_5 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (l1: (@list Z)) (l2: (@list Z)) (top_ph: Z) (bucks_ph: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (kp: Z) (vp: Z) (p_next: Z) (k_cur: (@list Z)) (l_tail: (@list Z)) (ind: Z) (i: Z) (i_v: Z) (h: Z) (key: Z) (valid: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (k <> k_cur) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| (l2 = (cons (i_v) (l_tail))) |] 
  &&  [| ((m1 (k_cur)) = (Some (&((i_v)  # "blist" ->ₛ "key")))) |] 
  &&  [| ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) |] 
  &&  [| (l1 = nil) |] 
  &&  [| (i = (bucks_ph + (ind * sizeof(PTR) ) )) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| forall (x: Z) , ~(((In x l1 ) /\ ((m1 (k)) = (Some (x))))) |]
  &&  (store_string key k )
  **  (store_string kp k_cur )
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  ((i) # Ptr  |-> i_v)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind (Znth (ind) (lh) (0)) 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m1 )
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR) ) ) i l1 )
  **  (store_map store_uint m2 )
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "valid" ) )) # Ptr  |-> valid)
  **  ((valid) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l_tail )
|--
  [| False |]
.

Definition hashtbl_find_safety_wit_6 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (l1: (@list Z)) (l2: (@list Z)) (top_ph: Z) (bucks_ph: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (kp: Z) (vp: Z) (p_next: Z) (k_cur: (@list Z)) (l_tail: (@list Z)) (h_val: Z) (t_l1: (@list Z)) (ind: Z) (i: Z) (i_v: Z) (h: Z) (key: Z) (valid: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_cur) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| (l2 = (cons (i_v) (l_tail))) |] 
  &&  [| ((m1 (k_cur)) = (Some (&((i_v)  # "blist" ->ₛ "key")))) |] 
  &&  [| ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) |] 
  &&  [| (l1 <> nil) |] 
  &&  [| (l1 = (cons (h_val) (t_l1))) |] 
  &&  [| (h_val = (Znth (ind) (lh) (0))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| forall (x: Z) , ~(((In x l1 ) /\ ((m1 (k)) = (Some (x))))) |]
  &&  (store_string key k )
  **  (store_string kp k_cur )
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  ((i) # Ptr  |-> i_v)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind (Znth (ind) (lh) (0)) 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m1 )
  **  (((bucks_ph + (ind * sizeof(PTR) ) )) # Ptr  |-> h_val)
  **  (sllbseg &((h_val)  # "blist" ->ₛ "next") i t_l1 )
  **  (store_map store_uint m2 )
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "valid" ) )) # Ptr  |-> valid)
  **  ((valid) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l_tail )
|--
  [| False |]
.

Definition hashtbl_find_safety_wit_7 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (l1: (@list Z)) (l2: (@list Z)) (top_ph: Z) (bucks_ph: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (kp: Z) (vp: Z) (p_next: Z) (k_cur: (@list Z)) (l_tail: (@list Z)) (ind: Z) (i: Z) (i_v: Z) (h: Z) (key: Z) (valid: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_cur) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| (l2 = (cons (i_v) (l_tail))) |] 
  &&  [| ((m1 (k_cur)) = (Some (&((i_v)  # "blist" ->ₛ "key")))) |] 
  &&  [| ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) |] 
  &&  [| (l1 = nil) |] 
  &&  [| (i = (bucks_ph + (ind * sizeof(PTR) ) )) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| forall (x: Z) , ~(((In x l1 ) /\ ((m1 (k)) = (Some (x))))) |]
  &&  (store_string key k )
  **  (store_string kp k_cur )
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  ((i) # Ptr  |-> i_v)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind (Znth (ind) (lh) (0)) 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m1 )
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR) ) ) i l1 )
  **  (store_map store_uint m2 )
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "valid" ) )) # Ptr  |-> valid)
  **  ((valid) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l_tail )
|--
  [| False |]
.

Definition hashtbl_find_safety_wit_8 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (l1: (@list Z)) (l2: (@list Z)) (top_ph: Z) (bucks_ph: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (kp: Z) (vp: Z) (p_next: Z) (k_cur: (@list Z)) (l_tail: (@list Z)) (h_val: Z) (t_l1: (@list Z)) (ind: Z) (i: Z) (i_v: Z) (h: Z) (key: Z) (valid: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_cur) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| (l2 = (cons (i_v) (l_tail))) |] 
  &&  [| ((m1 (k_cur)) = (Some (&((i_v)  # "blist" ->ₛ "key")))) |] 
  &&  [| ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) |] 
  &&  [| (l1 <> nil) |] 
  &&  [| (l1 = (cons (h_val) (t_l1))) |] 
  &&  [| (h_val = (Znth (ind) (lh) (0))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| forall (x: Z) , ~(((In x l1 ) /\ ((m1 (k)) = (Some (x))))) |]
  &&  ((( &( "b" ) )) # Ptr  |-> i_v)
  **  (store_string key k )
  **  (store_string kp k_cur )
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  ((i) # Ptr  |-> p_next)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind (Znth (ind) (lh) (0)) 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m1 )
  **  (((bucks_ph + (ind * sizeof(PTR) ) )) # Ptr  |-> i_v)
  **  (sllbseg &((h_val)  # "blist" ->ₛ "next") i t_l1 )
  **  (store_map store_uint m2 )
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "valid" ) )) # Ptr  |-> valid)
  **  ((valid) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> h_val)
  **  (sll p_next l_tail )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition hashtbl_find_safety_wit_9 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (l1: (@list Z)) (l2: (@list Z)) (top_ph: Z) (bucks_ph: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (kp: Z) (vp: Z) (p_next: Z) (k_cur: (@list Z)) (l_tail: (@list Z)) (ind: Z) (i: Z) (i_v: Z) (h: Z) (key: Z) (valid: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_cur) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| (l2 = (cons (i_v) (l_tail))) |] 
  &&  [| ((m1 (k_cur)) = (Some (&((i_v)  # "blist" ->ₛ "key")))) |] 
  &&  [| ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) |] 
  &&  [| (l1 = nil) |] 
  &&  [| (i = (bucks_ph + (ind * sizeof(PTR) ) )) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| forall (x: Z) , ~(((In x l1 ) /\ ((m1 (k)) = (Some (x))))) |]
  &&  (((bucks_ph + (ind * sizeof(PTR) ) )) # Ptr  |-> i_v)
  **  ((( &( "b" ) )) # Ptr  |-> i_v)
  **  (store_string key k )
  **  (store_string kp k_cur )
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind (Znth (ind) (lh) (0)) 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m1 )
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR) ) ) i l1 )
  **  (store_map store_uint m2 )
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "valid" ) )) # Ptr  |-> valid)
  **  ((valid) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l_tail )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition hashtbl_find_safety_wit_10 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (valid: Z) (key: Z) (i_v: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (lh: (@list Z)) (l: (@list Z)) (bucks_ph: Z) (top_ph: Z) (h: Z) (ind: Z) ,
  [| (i_v = 0) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| forall (x: Z) , ~(((In x l1 ) /\ ((m1 (k)) = (Some (x))))) |]
  &&  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind (Znth (ind) (lh) (0)) 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m1 )
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR) ) ) i l1 )
  **  ((i) # Ptr  |-> i_v)
  **  (sll i_v l2 )
  **  (store_map store_uint m2 )
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  (store_string key k )
  **  ((( &( "valid" ) )) # Ptr  |-> valid)
  **  ((valid) # Int  |->_)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_find_safety_wit_11 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (valid: Z) (key: Z) (i_v: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (lh: (@list Z)) (l: (@list Z)) (bucks_ph: Z) (top_ph: Z) (h: Z) (ind: Z) ,
  [| (i_v = 0) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| forall (x: Z) , ~(((In x l1 ) /\ ((m1 (k)) = (Some (x))))) |]
  &&  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind (Znth (ind) (lh) (0)) 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m1 )
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR) ) ) i l1 )
  **  ((i) # Ptr  |-> i_v)
  **  (sll i_v l2 )
  **  (store_map store_uint m2 )
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  (store_string key k )
  **  ((( &( "valid" ) )) # Ptr  |-> valid)
  **  ((valid) # Int  |-> 0)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hashtbl_find_entail_wit_1 := 
forall (valid_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (bucks_ph: Z) (top_ph: Z) (retval: Z) ,
  [| (0 <= retval) |] 
  &&  [| (retval <= 4294967295) |] 
  &&  [| (retval = (hash_string_k (k))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.full bucks_ph 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  ((valid_pre) # Int  |->_)
|--
  [| (0 <= (retval % ( 211 ) )) |] 
  &&  [| ((retval % ( 211 ) ) < 211) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval <= 4294967295) |] 
  &&  [| (retval = (hash_string_k (k))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.full bucks_ph 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  ((valid_pre) # Int  |->_)
.

Definition hashtbl_find_entail_wit_2 := 
forall (valid_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (lh_2: (@list Z)) (b_2: (Z -> (@option (Z * (@list Z))))) (l_2: (@list Z)) (bucks_ph: Z) (top_ph_2: Z) (retval: Z) ,
  [| (0 <= (retval % ( 211 ) )) |] 
  &&  [| ((retval % ( 211 ) ) < 211) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval <= 4294967295) |] 
  &&  [| (retval = (hash_string_k (k))) |] 
  &&  [| (contain_all_addrs m1 l_2 ) |] 
  &&  [| (repr_all_heads lh_2 b_2 ) |] 
  &&  [| (contain_all_correct_addrs m1 b_2 ) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph_2)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph_2 0 l_2 )
  **  (PtrArray.full bucks_ph 211 lh_2 )
  **  (store_map store_sll b_2 )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  ((valid_pre) # Int  |->_)
|--
  EX (i_v: Z)  (l1: (@list Z))  (l2: (@list Z))  (b: (Z -> (@option (Z * (@list Z)))))  (lh: (@list Z))  (l: (@list Z))  (bucks_ph_2: Z)  (top_ph: Z) ,
  [| (0 <= (retval % ( 211 ) )) |] 
  &&  [| ((retval % ( 211 ) ) < 211) |] 
  &&  [| ((retval % ( 211 ) ) = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| ((b ((retval % ( 211 ) ))) = (Some ((pair ((Znth ((retval % ( 211 ) )) (lh) (0))) ((app (l1) (l2))))))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| forall (x: Z) , ~(((In x l1 ) /\ ((m1 (k)) = (Some (x))))) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph_2)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph_2 (retval % ( 211 ) ) (Znth ((retval % ( 211 ) )) (lh) (0)) 211 lh )
  **  (store_map_missing_i store_sll b (retval % ( 211 ) ) )
  **  (store_map store_name m1 )
  **  (sllbseg (bucks_ph_2 + ((retval % ( 211 ) ) * sizeof(PTR) ) ) (bucks_ph + ((retval % ( 211 ) ) * sizeof(PTR) ) ) l1 )
  **  (((bucks_ph + ((retval % ( 211 ) ) * sizeof(PTR) ) )) # Ptr  |-> i_v)
  **  (sll i_v l2 )
  **  (store_map store_uint m2 )
  **  (store_string key_pre k )
  **  ((valid_pre) # Int  |->_)
.

Definition hashtbl_find_entail_wit_3 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (valid: Z) (key: Z) (i_v_3: Z) (i: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (b_2: (Z -> (@option (Z * (@list Z))))) (lh_2: (@list Z)) (l_2: (@list Z)) (bucks_ph_2: Z) (top_ph_2: Z) (h: Z) (ind: Z) ,
  [| (i_v_3 <> 0) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| ((b_2 (ind)) = (Some ((pair ((Znth (ind) (lh_2) (0))) ((app (l1_2) (l2_2))))))) |] 
  &&  [| (contain_all_addrs m1 l_2 ) |] 
  &&  [| (repr_all_heads lh_2 b_2 ) |] 
  &&  [| (contain_all_correct_addrs m1 b_2 ) |] 
  &&  [| forall (x_2: Z) , ~(((In x_2 l1_2 ) /\ ((m1 (k)) = (Some (x_2))))) |]
  &&  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph_2)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph_2)
  **  (dll top_ph_2 0 l_2 )
  **  (PtrArray.missing_i bucks_ph_2 ind (Znth (ind) (lh_2) (0)) 211 lh_2 )
  **  (store_map_missing_i store_sll b_2 ind )
  **  (store_map store_name m1 )
  **  (sllbseg (bucks_ph_2 + (ind * sizeof(PTR) ) ) i l1_2 )
  **  ((i) # Ptr  |-> i_v_3)
  **  (sll i_v_3 l2_2 )
  **  (store_map store_uint m2 )
  **  (store_string key k )
  **  ((valid) # Int  |->_)
|--
  (EX (p_next: Z)  (vp: Z)  (kp: Z)  (h_val: Z)  (t_l1: (@list Z))  (l1: (@list Z))  (b: (Z -> (@option (Z * (@list Z)))))  (lh: (@list Z))  (l: (@list Z))  (bucks_ph: Z)  (top_ph: Z)  (k_cur: (@list Z))  (i_v: Z)  (l_tail: (@list Z))  (l2: (@list Z)) ,
  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| (l2 = (cons (i_v) (l_tail))) |] 
  &&  [| ((m1 (k_cur)) = (Some (&((i_v)  # "blist" ->ₛ "key")))) |] 
  &&  [| ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) |] 
  &&  [| (l1 <> nil) |] 
  &&  [| (l1 = (cons (h_val) (t_l1))) |] 
  &&  [| (h_val = (Znth (ind) (lh) (0))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| forall (x: Z) , ~(((In x l1 ) /\ ((m1 (k)) = (Some (x))))) |]
  &&  ((i) # Ptr  |-> i_v)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind (Znth (ind) (lh) (0)) 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m1 )
  **  (((bucks_ph + (ind * sizeof(PTR) ) )) # Ptr  |-> h_val)
  **  (sllbseg &((h_val)  # "blist" ->ₛ "next") i t_l1 )
  **  (store_map store_uint m2 )
  **  (store_string key k )
  **  ((valid) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (store_string kp k_cur )
  **  (sll p_next l_tail ))
  ||
  (EX (p_next: Z)  (vp: Z)  (kp: Z)  (l1: (@list Z))  (b: (Z -> (@option (Z * (@list Z)))))  (lh: (@list Z))  (l: (@list Z))  (bucks_ph: Z)  (top_ph: Z)  (k_cur: (@list Z))  (i_v_2: Z)  (l_tail: (@list Z))  (l2: (@list Z)) ,
  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| (l2 = (cons (i_v_2) (l_tail))) |] 
  &&  [| ((m1 (k_cur)) = (Some (&((i_v_2)  # "blist" ->ₛ "key")))) |] 
  &&  [| ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) |] 
  &&  [| (l1 = nil) |] 
  &&  [| (i = (bucks_ph + (ind * sizeof(PTR) ) )) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| forall (x: Z) , ~(((In x l1 ) /\ ((m1 (k)) = (Some (x))))) |]
  &&  ((i) # Ptr  |-> i_v_2)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind (Znth (ind) (lh) (0)) 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m1 )
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR) ) ) i l1 )
  **  (store_map store_uint m2 )
  **  (store_string key k )
  **  ((valid) # Int  |->_)
  **  ((&((i_v_2)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v_2)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v_2)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (store_string kp k_cur )
  **  (sll p_next l_tail ))
.

Definition hashtbl_find_entail_wit_4_1 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (l1: (@list Z)) (l2: (@list Z)) (top_ph: Z) (bucks_ph: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (kp: Z) (vp: Z) (p_next: Z) (k_cur: (@list Z)) (l_tail: (@list Z)) (h_val: Z) (t_l1: (@list Z)) (ind: Z) (i: Z) (i_v: Z) (h: Z) (key: Z) (valid: Z) (retval_3: Z) ,
  [| (retval_3 <> 0) |] 
  &&  [| (retval_3 = 0) |] 
  &&  [| (k <> k_cur) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| (l2 = (cons (i_v) (l_tail))) |] 
  &&  [| ((m1 (k_cur)) = (Some (&((i_v)  # "blist" ->ₛ "key")))) |] 
  &&  [| ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) |] 
  &&  [| (l1 <> nil) |] 
  &&  [| (l1 = (cons (h_val) (t_l1))) |] 
  &&  [| (h_val = (Znth (ind) (lh) (0))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| forall (x: Z) , ~(((In x l1 ) /\ ((m1 (k)) = (Some (x))))) |]
  &&  (store_string key k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind (Znth (ind) (lh) (0)) 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m1 )
  **  (((bucks_ph + (ind * sizeof(PTR) ) )) # Ptr  |-> h_val)
  **  (sllbseg &((h_val)  # "blist" ->ₛ "next") i t_l1 )
  **  (store_map store_uint m2 )
  **  ((valid) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l_tail )
|--
  (EX (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_cur) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| (l2 = (cons (i_v) (l_tail))) |] 
  &&  [| ((m1 (k_cur)) = (Some (&((i_v)  # "blist" ->ₛ "key")))) |] 
  &&  [| ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) |] 
  &&  [| (l1 <> nil) |] 
  &&  [| (l1 = (cons (h_val) (t_l1))) |] 
  &&  [| (h_val = (Znth (ind) (lh) (0))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| forall (x: Z) , ~(((In x l1 ) /\ ((m1 (k)) = (Some (x))))) |]
  &&  (store_string key k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind (Znth (ind) (lh) (0)) 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m1 )
  **  (((bucks_ph + (ind * sizeof(PTR) ) )) # Ptr  |-> h_val)
  **  (sllbseg &((h_val)  # "blist" ->ₛ "next") i t_l1 )
  **  (store_map store_uint m2 )
  **  ((valid) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l_tail ))
  ||
  (EX (retval_2: Z)  (i_v_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 = 1) |] 
  &&  [| (k = k_cur) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| (l2 = (cons (i_v_2) (l_tail))) |] 
  &&  [| ((m1 (k_cur)) = (Some (&((i_v_2)  # "blist" ->ₛ "key")))) |] 
  &&  [| ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) |] 
  &&  [| (l1 = nil) |] 
  &&  [| (i = (bucks_ph + (ind * sizeof(PTR) ) )) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| forall (x: Z) , ~(((In x l1 ) /\ ((m1 (k)) = (Some (x))))) |]
  &&  (store_string key k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v_2)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind (Znth (ind) (lh) (0)) 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m1 )
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR) ) ) i l1 )
  **  (store_map store_uint m2 )
  **  ((valid) # Int  |->_)
  **  ((&((i_v_2)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v_2)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v_2)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l_tail ))
.

Definition hashtbl_find_entail_wit_4_2 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (l1: (@list Z)) (l2: (@list Z)) (top_ph: Z) (bucks_ph: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (kp: Z) (vp: Z) (p_next: Z) (k_cur: (@list Z)) (l_tail: (@list Z)) (h_val: Z) (t_l1: (@list Z)) (ind: Z) (i: Z) (i_v: Z) (h: Z) (key: Z) (valid: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_cur) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| (l2 = (cons (i_v) (l_tail))) |] 
  &&  [| ((m1 (k_cur)) = (Some (&((i_v)  # "blist" ->ₛ "key")))) |] 
  &&  [| ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) |] 
  &&  [| (l1 <> nil) |] 
  &&  [| (l1 = (cons (h_val) (t_l1))) |] 
  &&  [| (h_val = (Znth (ind) (lh) (0))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| forall (x: Z) , ~(((In x l1 ) /\ ((m1 (k)) = (Some (x))))) |]
  &&  (store_string key k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind (Znth (ind) (lh) (0)) 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m1 )
  **  (((bucks_ph + (ind * sizeof(PTR) ) )) # Ptr  |-> h_val)
  **  (sllbseg &((h_val)  # "blist" ->ₛ "next") i t_l1 )
  **  (store_map store_uint m2 )
  **  ((valid) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l_tail )
|--
  ([| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_cur) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| (l2 = (cons (i_v) (l_tail))) |] 
  &&  [| ((m1 (k_cur)) = (Some (&((i_v)  # "blist" ->ₛ "key")))) |] 
  &&  [| ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) |] 
  &&  [| (l1 <> nil) |] 
  &&  [| (l1 = (cons (h_val) (t_l1))) |] 
  &&  [| (h_val = (Znth (ind) (lh) (0))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| forall (x: Z) , ~(((In x l1 ) /\ ((m1 (k)) = (Some (x))))) |]
  &&  (store_string key k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind (Znth (ind) (lh) (0)) 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m1 )
  **  (((bucks_ph + (ind * sizeof(PTR) ) )) # Ptr  |-> h_val)
  **  (sllbseg &((h_val)  # "blist" ->ₛ "next") i t_l1 )
  **  (store_map store_uint m2 )
  **  ((valid) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l_tail ))
  ||
  (EX (retval_2: Z)  (i_v_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 = 1) |] 
  &&  [| (k = k_cur) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| (l2 = (cons (i_v_2) (l_tail))) |] 
  &&  [| ((m1 (k_cur)) = (Some (&((i_v_2)  # "blist" ->ₛ "key")))) |] 
  &&  [| ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) |] 
  &&  [| (l1 = nil) |] 
  &&  [| (i = (bucks_ph + (ind * sizeof(PTR) ) )) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| forall (x: Z) , ~(((In x l1 ) /\ ((m1 (k)) = (Some (x))))) |]
  &&  (store_string key k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v_2)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind (Znth (ind) (lh) (0)) 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m1 )
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR) ) ) i l1 )
  **  (store_map store_uint m2 )
  **  ((valid) # Int  |->_)
  **  ((&((i_v_2)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v_2)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v_2)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l_tail ))
.

Definition hashtbl_find_entail_wit_4_3 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (l1: (@list Z)) (l2: (@list Z)) (top_ph: Z) (bucks_ph: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (kp: Z) (vp: Z) (p_next: Z) (k_cur: (@list Z)) (l_tail: (@list Z)) (ind: Z) (i: Z) (i_v_2: Z) (h: Z) (key: Z) (valid: Z) (retval_3: Z) ,
  [| (retval_3 <> 0) |] 
  &&  [| (retval_3 = 0) |] 
  &&  [| (k <> k_cur) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| (l2 = (cons (i_v_2) (l_tail))) |] 
  &&  [| ((m1 (k_cur)) = (Some (&((i_v_2)  # "blist" ->ₛ "key")))) |] 
  &&  [| ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) |] 
  &&  [| (l1 = nil) |] 
  &&  [| (i = (bucks_ph + (ind * sizeof(PTR) ) )) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| forall (x: Z) , ~(((In x l1 ) /\ ((m1 (k)) = (Some (x))))) |]
  &&  (store_string key k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v_2)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind (Znth (ind) (lh) (0)) 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m1 )
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR) ) ) i l1 )
  **  (store_map store_uint m2 )
  **  ((valid) # Int  |->_)
  **  ((&((i_v_2)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v_2)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v_2)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l_tail )
|--
  (EX (retval: Z)  (h_val: Z)  (t_l1: (@list Z))  (i_v: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_cur) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| (l2 = (cons (i_v) (l_tail))) |] 
  &&  [| ((m1 (k_cur)) = (Some (&((i_v)  # "blist" ->ₛ "key")))) |] 
  &&  [| ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) |] 
  &&  [| (l1 <> nil) |] 
  &&  [| (l1 = (cons (h_val) (t_l1))) |] 
  &&  [| (h_val = (Znth (ind) (lh) (0))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| forall (x: Z) , ~(((In x l1 ) /\ ((m1 (k)) = (Some (x))))) |]
  &&  (store_string key k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind (Znth (ind) (lh) (0)) 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m1 )
  **  (((bucks_ph + (ind * sizeof(PTR) ) )) # Ptr  |-> h_val)
  **  (sllbseg &((h_val)  # "blist" ->ₛ "next") i t_l1 )
  **  (store_map store_uint m2 )
  **  ((valid) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l_tail ))
  ||
  (EX (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 = 1) |] 
  &&  [| (k = k_cur) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| (l2 = (cons (i_v_2) (l_tail))) |] 
  &&  [| ((m1 (k_cur)) = (Some (&((i_v_2)  # "blist" ->ₛ "key")))) |] 
  &&  [| ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) |] 
  &&  [| (l1 = nil) |] 
  &&  [| (i = (bucks_ph + (ind * sizeof(PTR) ) )) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| forall (x: Z) , ~(((In x l1 ) /\ ((m1 (k)) = (Some (x))))) |]
  &&  (store_string key k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v_2)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind (Znth (ind) (lh) (0)) 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m1 )
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR) ) ) i l1 )
  **  (store_map store_uint m2 )
  **  ((valid) # Int  |->_)
  **  ((&((i_v_2)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v_2)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v_2)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l_tail ))
.

Definition hashtbl_find_entail_wit_4_4 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (l1: (@list Z)) (l2: (@list Z)) (top_ph: Z) (bucks_ph: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (kp: Z) (vp: Z) (p_next: Z) (k_cur: (@list Z)) (l_tail: (@list Z)) (ind: Z) (i: Z) (i_v_2: Z) (h: Z) (key: Z) (valid: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 = 1) |] 
  &&  [| (k = k_cur) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| (l2 = (cons (i_v_2) (l_tail))) |] 
  &&  [| ((m1 (k_cur)) = (Some (&((i_v_2)  # "blist" ->ₛ "key")))) |] 
  &&  [| ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) |] 
  &&  [| (l1 = nil) |] 
  &&  [| (i = (bucks_ph + (ind * sizeof(PTR) ) )) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| forall (x: Z) , ~(((In x l1 ) /\ ((m1 (k)) = (Some (x))))) |]
  &&  (store_string key k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v_2)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind (Znth (ind) (lh) (0)) 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m1 )
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR) ) ) i l1 )
  **  (store_map store_uint m2 )
  **  ((valid) # Int  |->_)
  **  ((&((i_v_2)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v_2)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v_2)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l_tail )
|--
  (EX (retval: Z)  (h_val: Z)  (t_l1: (@list Z))  (i_v: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_cur) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| (l2 = (cons (i_v) (l_tail))) |] 
  &&  [| ((m1 (k_cur)) = (Some (&((i_v)  # "blist" ->ₛ "key")))) |] 
  &&  [| ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) |] 
  &&  [| (l1 <> nil) |] 
  &&  [| (l1 = (cons (h_val) (t_l1))) |] 
  &&  [| (h_val = (Znth (ind) (lh) (0))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| forall (x: Z) , ~(((In x l1 ) /\ ((m1 (k)) = (Some (x))))) |]
  &&  (store_string key k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind (Znth (ind) (lh) (0)) 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m1 )
  **  (((bucks_ph + (ind * sizeof(PTR) ) )) # Ptr  |-> h_val)
  **  (sllbseg &((h_val)  # "blist" ->ₛ "next") i t_l1 )
  **  (store_map store_uint m2 )
  **  ((valid) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l_tail ))
  ||
  ([| (retval_2 <> 0) |] 
  &&  [| (retval_2 = 1) |] 
  &&  [| (k = k_cur) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| (l2 = (cons (i_v_2) (l_tail))) |] 
  &&  [| ((m1 (k_cur)) = (Some (&((i_v_2)  # "blist" ->ₛ "key")))) |] 
  &&  [| ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) |] 
  &&  [| (l1 = nil) |] 
  &&  [| (i = (bucks_ph + (ind * sizeof(PTR) ) )) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| forall (x: Z) , ~(((In x l1 ) /\ ((m1 (k)) = (Some (x))))) |]
  &&  (store_string key k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v_2)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind (Znth (ind) (lh) (0)) 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m1 )
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR) ) ) i l1 )
  **  (store_map store_uint m2 )
  **  ((valid) # Int  |->_)
  **  ((&((i_v_2)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v_2)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v_2)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l_tail ))
.

Definition hashtbl_find_entail_wit_5_1 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (l1: (@list Z)) (l2: (@list Z)) (top_ph: Z) (bucks_ph: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (kp: Z) (vp: Z) (p_next: Z) (k_cur: (@list Z)) (l_tail: (@list Z)) (h_val: Z) (t_l1: (@list Z)) (ind: Z) (i: Z) (i_v: Z) (h: Z) (key: Z) (valid: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (k <> k_cur) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| (l2 = (cons (i_v) (l_tail))) |] 
  &&  [| ((m1 (k_cur)) = (Some (&((i_v)  # "blist" ->ₛ "key")))) |] 
  &&  [| ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) |] 
  &&  [| (l1 <> nil) |] 
  &&  [| (l1 = (cons (h_val) (t_l1))) |] 
  &&  [| (h_val = (Znth (ind) (lh) (0))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| forall (x: Z) , ~(((In x l1 ) /\ ((m1 (k)) = (Some (x))))) |]
  &&  (store_string key k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind (Znth (ind) (lh) (0)) 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m1 )
  **  (((bucks_ph + (ind * sizeof(PTR) ) )) # Ptr  |-> h_val)
  **  (sllbseg &((h_val)  # "blist" ->ₛ "next") i t_l1 )
  **  (store_map store_uint m2 )
  **  ((valid) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l_tail )
|--
  ([| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (k <> k_cur) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| (l2 = (cons (i_v) (l_tail))) |] 
  &&  [| ((m1 (k_cur)) = (Some (&((i_v)  # "blist" ->ₛ "key")))) |] 
  &&  [| ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) |] 
  &&  [| (l1 <> nil) |] 
  &&  [| (l1 = (cons (h_val) (t_l1))) |] 
  &&  [| (h_val = (Znth (ind) (lh) (0))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| forall (x: Z) , ~(((In x l1 ) /\ ((m1 (k)) = (Some (x))))) |]
  &&  (store_string key k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind (Znth (ind) (lh) (0)) 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m1 )
  **  (((bucks_ph + (ind * sizeof(PTR) ) )) # Ptr  |-> h_val)
  **  (sllbseg &((h_val)  # "blist" ->ₛ "next") i t_l1 )
  **  (store_map store_uint m2 )
  **  ((valid) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l_tail ))
  ||
  (EX (retval_2: Z)  (i_v_2: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (k <> k_cur) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| (l2 = (cons (i_v_2) (l_tail))) |] 
  &&  [| ((m1 (k_cur)) = (Some (&((i_v_2)  # "blist" ->ₛ "key")))) |] 
  &&  [| ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) |] 
  &&  [| (l1 = nil) |] 
  &&  [| (i = (bucks_ph + (ind * sizeof(PTR) ) )) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| forall (x: Z) , ~(((In x l1 ) /\ ((m1 (k)) = (Some (x))))) |]
  &&  (store_string key k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v_2)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind (Znth (ind) (lh) (0)) 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m1 )
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR) ) ) i l1 )
  **  (store_map store_uint m2 )
  **  ((valid) # Int  |->_)
  **  ((&((i_v_2)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v_2)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v_2)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l_tail ))
.

Definition hashtbl_find_entail_wit_5_2 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (l1: (@list Z)) (l2: (@list Z)) (top_ph: Z) (bucks_ph: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (kp: Z) (vp: Z) (p_next: Z) (k_cur: (@list Z)) (l_tail: (@list Z)) (h_val: Z) (t_l1: (@list Z)) (ind: Z) (i: Z) (i_v: Z) (h: Z) (key: Z) (valid: Z) (retval_3: Z) ,
  [| (retval_3 = 0) |] 
  &&  [| (retval_3 = 1) |] 
  &&  [| (k = k_cur) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| (l2 = (cons (i_v) (l_tail))) |] 
  &&  [| ((m1 (k_cur)) = (Some (&((i_v)  # "blist" ->ₛ "key")))) |] 
  &&  [| ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) |] 
  &&  [| (l1 <> nil) |] 
  &&  [| (l1 = (cons (h_val) (t_l1))) |] 
  &&  [| (h_val = (Znth (ind) (lh) (0))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| forall (x: Z) , ~(((In x l1 ) /\ ((m1 (k)) = (Some (x))))) |]
  &&  (store_string key k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind (Znth (ind) (lh) (0)) 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m1 )
  **  (((bucks_ph + (ind * sizeof(PTR) ) )) # Ptr  |-> h_val)
  **  (sllbseg &((h_val)  # "blist" ->ₛ "next") i t_l1 )
  **  (store_map store_uint m2 )
  **  ((valid) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l_tail )
|--
  (EX (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (k <> k_cur) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| (l2 = (cons (i_v) (l_tail))) |] 
  &&  [| ((m1 (k_cur)) = (Some (&((i_v)  # "blist" ->ₛ "key")))) |] 
  &&  [| ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) |] 
  &&  [| (l1 <> nil) |] 
  &&  [| (l1 = (cons (h_val) (t_l1))) |] 
  &&  [| (h_val = (Znth (ind) (lh) (0))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| forall (x: Z) , ~(((In x l1 ) /\ ((m1 (k)) = (Some (x))))) |]
  &&  (store_string key k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind (Znth (ind) (lh) (0)) 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m1 )
  **  (((bucks_ph + (ind * sizeof(PTR) ) )) # Ptr  |-> h_val)
  **  (sllbseg &((h_val)  # "blist" ->ₛ "next") i t_l1 )
  **  (store_map store_uint m2 )
  **  ((valid) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l_tail ))
  ||
  (EX (retval_2: Z)  (i_v_2: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (k <> k_cur) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| (l2 = (cons (i_v_2) (l_tail))) |] 
  &&  [| ((m1 (k_cur)) = (Some (&((i_v_2)  # "blist" ->ₛ "key")))) |] 
  &&  [| ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) |] 
  &&  [| (l1 = nil) |] 
  &&  [| (i = (bucks_ph + (ind * sizeof(PTR) ) )) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| forall (x: Z) , ~(((In x l1 ) /\ ((m1 (k)) = (Some (x))))) |]
  &&  (store_string key k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v_2)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind (Znth (ind) (lh) (0)) 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m1 )
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR) ) ) i l1 )
  **  (store_map store_uint m2 )
  **  ((valid) # Int  |->_)
  **  ((&((i_v_2)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v_2)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v_2)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l_tail ))
.

Definition hashtbl_find_entail_wit_5_3 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (l1: (@list Z)) (l2: (@list Z)) (top_ph: Z) (bucks_ph: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (kp: Z) (vp: Z) (p_next: Z) (k_cur: (@list Z)) (l_tail: (@list Z)) (ind: Z) (i: Z) (i_v_2: Z) (h: Z) (key: Z) (valid: Z) (retval_2: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (k <> k_cur) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| (l2 = (cons (i_v_2) (l_tail))) |] 
  &&  [| ((m1 (k_cur)) = (Some (&((i_v_2)  # "blist" ->ₛ "key")))) |] 
  &&  [| ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) |] 
  &&  [| (l1 = nil) |] 
  &&  [| (i = (bucks_ph + (ind * sizeof(PTR) ) )) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| forall (x: Z) , ~(((In x l1 ) /\ ((m1 (k)) = (Some (x))))) |]
  &&  (store_string key k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v_2)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind (Znth (ind) (lh) (0)) 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m1 )
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR) ) ) i l1 )
  **  (store_map store_uint m2 )
  **  ((valid) # Int  |->_)
  **  ((&((i_v_2)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v_2)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v_2)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l_tail )
|--
  (EX (retval: Z)  (h_val: Z)  (t_l1: (@list Z))  (i_v: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (k <> k_cur) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| (l2 = (cons (i_v) (l_tail))) |] 
  &&  [| ((m1 (k_cur)) = (Some (&((i_v)  # "blist" ->ₛ "key")))) |] 
  &&  [| ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) |] 
  &&  [| (l1 <> nil) |] 
  &&  [| (l1 = (cons (h_val) (t_l1))) |] 
  &&  [| (h_val = (Znth (ind) (lh) (0))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| forall (x: Z) , ~(((In x l1 ) /\ ((m1 (k)) = (Some (x))))) |]
  &&  (store_string key k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind (Znth (ind) (lh) (0)) 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m1 )
  **  (((bucks_ph + (ind * sizeof(PTR) ) )) # Ptr  |-> h_val)
  **  (sllbseg &((h_val)  # "blist" ->ₛ "next") i t_l1 )
  **  (store_map store_uint m2 )
  **  ((valid) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l_tail ))
  ||
  ([| (retval_2 = 0) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (k <> k_cur) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| (l2 = (cons (i_v_2) (l_tail))) |] 
  &&  [| ((m1 (k_cur)) = (Some (&((i_v_2)  # "blist" ->ₛ "key")))) |] 
  &&  [| ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) |] 
  &&  [| (l1 = nil) |] 
  &&  [| (i = (bucks_ph + (ind * sizeof(PTR) ) )) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| forall (x: Z) , ~(((In x l1 ) /\ ((m1 (k)) = (Some (x))))) |]
  &&  (store_string key k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v_2)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind (Znth (ind) (lh) (0)) 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m1 )
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR) ) ) i l1 )
  **  (store_map store_uint m2 )
  **  ((valid) # Int  |->_)
  **  ((&((i_v_2)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v_2)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v_2)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l_tail ))
.

Definition hashtbl_find_entail_wit_5_4 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (l1: (@list Z)) (l2: (@list Z)) (top_ph: Z) (bucks_ph: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (kp: Z) (vp: Z) (p_next: Z) (k_cur: (@list Z)) (l_tail: (@list Z)) (ind: Z) (i: Z) (i_v_2: Z) (h: Z) (key: Z) (valid: Z) (retval_3: Z) ,
  [| (retval_3 = 0) |] 
  &&  [| (retval_3 = 1) |] 
  &&  [| (k = k_cur) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| (l2 = (cons (i_v_2) (l_tail))) |] 
  &&  [| ((m1 (k_cur)) = (Some (&((i_v_2)  # "blist" ->ₛ "key")))) |] 
  &&  [| ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) |] 
  &&  [| (l1 = nil) |] 
  &&  [| (i = (bucks_ph + (ind * sizeof(PTR) ) )) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| forall (x: Z) , ~(((In x l1 ) /\ ((m1 (k)) = (Some (x))))) |]
  &&  (store_string key k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v_2)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind (Znth (ind) (lh) (0)) 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m1 )
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR) ) ) i l1 )
  **  (store_map store_uint m2 )
  **  ((valid) # Int  |->_)
  **  ((&((i_v_2)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v_2)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v_2)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l_tail )
|--
  (EX (retval: Z)  (h_val: Z)  (t_l1: (@list Z))  (i_v: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (k <> k_cur) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| (l2 = (cons (i_v) (l_tail))) |] 
  &&  [| ((m1 (k_cur)) = (Some (&((i_v)  # "blist" ->ₛ "key")))) |] 
  &&  [| ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) |] 
  &&  [| (l1 <> nil) |] 
  &&  [| (l1 = (cons (h_val) (t_l1))) |] 
  &&  [| (h_val = (Znth (ind) (lh) (0))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| forall (x: Z) , ~(((In x l1 ) /\ ((m1 (k)) = (Some (x))))) |]
  &&  (store_string key k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind (Znth (ind) (lh) (0)) 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m1 )
  **  (((bucks_ph + (ind * sizeof(PTR) ) )) # Ptr  |-> h_val)
  **  (sllbseg &((h_val)  # "blist" ->ₛ "next") i t_l1 )
  **  (store_map store_uint m2 )
  **  ((valid) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l_tail ))
  ||
  (EX (retval_2: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (k <> k_cur) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| (l2 = (cons (i_v_2) (l_tail))) |] 
  &&  [| ((m1 (k_cur)) = (Some (&((i_v_2)  # "blist" ->ₛ "key")))) |] 
  &&  [| ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) |] 
  &&  [| (l1 = nil) |] 
  &&  [| (i = (bucks_ph + (ind * sizeof(PTR) ) )) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| forall (x: Z) , ~(((In x l1 ) /\ ((m1 (k)) = (Some (x))))) |]
  &&  (store_string key k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v_2)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind (Znth (ind) (lh) (0)) 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m1 )
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR) ) ) i l1 )
  **  (store_map store_uint m2 )
  **  ((valid) # Int  |->_)
  **  ((&((i_v_2)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v_2)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v_2)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l_tail ))
.

Definition hashtbl_find_entail_wit_6_1 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (l1_2: (@list Z)) (l2_2: (@list Z)) (top_ph_2: Z) (bucks_ph_2: Z) (l_2: (@list Z)) (lh_2: (@list Z)) (b_2: (Z -> (@option (Z * (@list Z))))) (kp: Z) (vp: Z) (p_next: Z) (k_cur: (@list Z)) (l_tail: (@list Z)) (ind: Z) (i: Z) (i_v_2: Z) (h: Z) (key: Z) (valid: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (k <> k_cur) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| (l2_2 = (cons (i_v_2) (l_tail))) |] 
  &&  [| ((m1 (k_cur)) = (Some (&((i_v_2)  # "blist" ->ₛ "key")))) |] 
  &&  [| ((b_2 (ind)) = (Some ((pair ((Znth (ind) (lh_2) (0))) ((app (l1_2) (l2_2))))))) |] 
  &&  [| (l1_2 = nil) |] 
  &&  [| (i = (bucks_ph_2 + (ind * sizeof(PTR) ) )) |] 
  &&  [| (contain_all_addrs m1 l_2 ) |] 
  &&  [| (repr_all_heads lh_2 b_2 ) |] 
  &&  [| (contain_all_correct_addrs m1 b_2 ) |] 
  &&  [| forall (x_2: Z) , ~(((In x_2 l1_2 ) /\ ((m1 (k)) = (Some (x_2))))) |]
  &&  (store_string key k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v_2)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph_2)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph_2)
  **  (dll top_ph_2 0 l_2 )
  **  (PtrArray.missing_i bucks_ph_2 ind (Znth (ind) (lh_2) (0)) 211 lh_2 )
  **  (store_map_missing_i store_sll b_2 ind )
  **  (store_map store_name m1 )
  **  (sllbseg (bucks_ph_2 + (ind * sizeof(PTR) ) ) i l1_2 )
  **  (store_map store_uint m2 )
  **  ((valid) # Int  |->_)
  **  ((&((i_v_2)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v_2)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v_2)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l_tail )
|--
  EX (i_v: Z)  (l1: (@list Z))  (l2: (@list Z))  (b: (Z -> (@option (Z * (@list Z)))))  (lh: (@list Z))  (l: (@list Z))  (bucks_ph: Z)  (top_ph: Z) ,
  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| forall (x: Z) , ~(((In x l1 ) /\ ((m1 (k)) = (Some (x))))) |]
  &&  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind (Znth (ind) (lh) (0)) 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m1 )
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR) ) ) &((i_v_2)  # "blist" ->ₛ "next") l1 )
  **  ((&((i_v_2)  # "blist" ->ₛ "next")) # Ptr  |-> i_v)
  **  (sll i_v l2 )
  **  (store_map store_uint m2 )
  **  (store_string key k )
  **  ((valid) # Int  |->_)
.

Definition hashtbl_find_entail_wit_6_2 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (l1_2: (@list Z)) (l2_2: (@list Z)) (top_ph_2: Z) (bucks_ph_2: Z) (l_2: (@list Z)) (lh_2: (@list Z)) (b_2: (Z -> (@option (Z * (@list Z))))) (kp: Z) (vp: Z) (p_next: Z) (k_cur: (@list Z)) (l_tail: (@list Z)) (h_val: Z) (t_l1: (@list Z)) (ind: Z) (i: Z) (i_v_2: Z) (h: Z) (key: Z) (valid: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (k <> k_cur) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| (l2_2 = (cons (i_v_2) (l_tail))) |] 
  &&  [| ((m1 (k_cur)) = (Some (&((i_v_2)  # "blist" ->ₛ "key")))) |] 
  &&  [| ((b_2 (ind)) = (Some ((pair ((Znth (ind) (lh_2) (0))) ((app (l1_2) (l2_2))))))) |] 
  &&  [| (l1_2 <> nil) |] 
  &&  [| (l1_2 = (cons (h_val) (t_l1))) |] 
  &&  [| (h_val = (Znth (ind) (lh_2) (0))) |] 
  &&  [| (contain_all_addrs m1 l_2 ) |] 
  &&  [| (repr_all_heads lh_2 b_2 ) |] 
  &&  [| (contain_all_correct_addrs m1 b_2 ) |] 
  &&  [| forall (x_2: Z) , ~(((In x_2 l1_2 ) /\ ((m1 (k)) = (Some (x_2))))) |]
  &&  (store_string key k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v_2)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph_2)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph_2)
  **  (dll top_ph_2 0 l_2 )
  **  (PtrArray.missing_i bucks_ph_2 ind (Znth (ind) (lh_2) (0)) 211 lh_2 )
  **  (store_map_missing_i store_sll b_2 ind )
  **  (store_map store_name m1 )
  **  (((bucks_ph_2 + (ind * sizeof(PTR) ) )) # Ptr  |-> h_val)
  **  (sllbseg &((h_val)  # "blist" ->ₛ "next") i t_l1 )
  **  (store_map store_uint m2 )
  **  ((valid) # Int  |->_)
  **  ((&((i_v_2)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v_2)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v_2)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l_tail )
|--
  EX (i_v: Z)  (l1: (@list Z))  (l2: (@list Z))  (b: (Z -> (@option (Z * (@list Z)))))  (lh: (@list Z))  (l: (@list Z))  (bucks_ph: Z)  (top_ph: Z) ,
  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| forall (x: Z) , ~(((In x l1 ) /\ ((m1 (k)) = (Some (x))))) |]
  &&  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind (Znth (ind) (lh) (0)) 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m1 )
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR) ) ) &((i_v_2)  # "blist" ->ₛ "next") l1 )
  **  ((&((i_v_2)  # "blist" ->ₛ "next")) # Ptr  |-> i_v)
  **  (sll i_v l2 )
  **  (store_map store_uint m2 )
  **  (store_string key k )
  **  ((valid) # Int  |->_)
.

Definition hashtbl_find_return_wit_1 := 
forall (valid_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (l1: (@list Z)) (l2: (@list Z)) (top_ph: Z) (bucks_ph: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (kp: Z) (vp: Z) (p_next: Z) (k_cur: (@list Z)) (l_tail: (@list Z)) (ind: Z) (i: Z) (i_v: Z) (h: Z) (key: Z) (valid: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_cur) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| (l2 = (cons (i_v) (l_tail))) |] 
  &&  [| ((m1 (k_cur)) = (Some (&((i_v)  # "blist" ->ₛ "key")))) |] 
  &&  [| ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) |] 
  &&  [| (l1 = nil) |] 
  &&  [| (i = (bucks_ph + (ind * sizeof(PTR) ) )) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| forall (x: Z) , ~(((In x l1 ) /\ ((m1 (k)) = (Some (x))))) |]
  &&  (((bucks_ph + (ind * sizeof(PTR) ) )) # Ptr  |-> i_v)
  **  (store_string key k )
  **  (store_string kp k_cur )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind (Znth (ind) (lh) (0)) 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m1 )
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR) ) ) i l1 )
  **  (store_map store_uint m2 )
  **  ((valid) # Int  |-> 1)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l_tail )
|--
  ([| ((m1 (k)) = None) |] 
  &&  [| (vp = 0) |]
  &&  (store_hash_skeleton h_pre m1 )
  **  (store_map store_uint m2 )
  **  (store_string key_pre k )
  **  ((valid_pre) # Int  |-> 0))
  ||
  (EX (v: Z)  (p: Z) ,
  [| ((m1 (k)) = (Some (p))) |] 
  &&  [| ((m2 (p)) = (Some (v))) |] 
  &&  [| (vp = v) |]
  &&  (store_hash_skeleton h_pre m1 )
  **  (store_map store_uint m2 )
  **  (store_string key_pre k )
  **  ((valid_pre) # Int  |-> 1))
.

Definition hashtbl_find_return_wit_2 := 
forall (valid_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (l1: (@list Z)) (l2: (@list Z)) (top_ph: Z) (bucks_ph: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (kp: Z) (vp: Z) (p_next: Z) (k_cur: (@list Z)) (l_tail: (@list Z)) (h_val: Z) (t_l1: (@list Z)) (ind: Z) (i: Z) (i_v: Z) (h: Z) (key: Z) (valid: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_cur) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| (l2 = (cons (i_v) (l_tail))) |] 
  &&  [| ((m1 (k_cur)) = (Some (&((i_v)  # "blist" ->ₛ "key")))) |] 
  &&  [| ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) |] 
  &&  [| (l1 <> nil) |] 
  &&  [| (l1 = (cons (h_val) (t_l1))) |] 
  &&  [| (h_val = (Znth (ind) (lh) (0))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| forall (x: Z) , ~(((In x l1 ) /\ ((m1 (k)) = (Some (x))))) |]
  &&  (store_string key k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> p_next)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind (Znth (ind) (lh) (0)) 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m1 )
  **  (((bucks_ph + (ind * sizeof(PTR) ) )) # Ptr  |-> i_v)
  **  (sllbseg &((h_val)  # "blist" ->ₛ "next") i t_l1 )
  **  (store_map store_uint m2 )
  **  ((valid) # Int  |-> 1)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> h_val)
  **  (sll p_next l_tail )
|--
  ([| ((m1 (k)) = None) |] 
  &&  [| (vp = 0) |]
  &&  (store_hash_skeleton h_pre m1 )
  **  (store_map store_uint m2 )
  **  (store_string key_pre k )
  **  ((valid_pre) # Int  |-> 0))
  ||
  (EX (v: Z)  (p: Z) ,
  [| ((m1 (k)) = (Some (p))) |] 
  &&  [| ((m2 (p)) = (Some (v))) |] 
  &&  [| (vp = v) |]
  &&  (store_hash_skeleton h_pre m1 )
  **  (store_map store_uint m2 )
  **  (store_string key_pre k )
  **  ((valid_pre) # Int  |-> 1))
.

Definition hashtbl_find_return_wit_3 := 
forall (valid_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (valid: Z) (key: Z) (i_v: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (lh: (@list Z)) (l: (@list Z)) (bucks_ph: Z) (top_ph: Z) (h: Z) (ind: Z) ,
  [| (i_v = 0) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| forall (x: Z) , ~(((In x l1 ) /\ ((m1 (k)) = (Some (x))))) |]
  &&  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind (Znth (ind) (lh) (0)) 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m1 )
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR) ) ) i l1 )
  **  ((i) # Ptr  |-> i_v)
  **  (sll i_v l2 )
  **  (store_map store_uint m2 )
  **  (store_string key k )
  **  ((valid) # Int  |-> 0)
|--
  ([| ((m1 (k)) = None) |] 
  &&  [| (0 = 0) |]
  &&  (store_hash_skeleton h_pre m1 )
  **  (store_map store_uint m2 )
  **  (store_string key_pre k )
  **  ((valid_pre) # Int  |-> 0))
  ||
  (EX (v: Z)  (p: Z) ,
  [| ((m1 (k)) = (Some (p))) |] 
  &&  [| ((m2 (p)) = (Some (v))) |] 
  &&  [| (0 = v) |]
  &&  (store_hash_skeleton h_pre m1 )
  **  (store_map store_uint m2 )
  **  (store_string key_pre k )
  **  ((valid_pre) # Int  |-> 1))
.

Definition hashtbl_find_partial_solve_wit_1 := 
forall (valid_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) ,
  [| (map_composable m1 m2 ) |]
  &&  (store_hash_skeleton h_pre m1 )
  **  (store_map store_uint m2 )
  **  (store_string key_pre k )
  **  ((valid_pre) # Int  |->_)
|--
  [| (map_composable m1 m2 ) |]
  &&  (store_hash_skeleton h_pre m1 )
  **  (store_map store_uint m2 )
  **  (store_string key_pre k )
  **  ((valid_pre) # Int  |->_)
.

Definition hashtbl_find_partial_solve_wit_2 := 
forall (valid_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (bucks_ph: Z) (top_ph: Z) ,
  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.full bucks_ph 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  (store_string key_pre k )
  **  ((valid_pre) # Int  |->_)
|--
  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| (map_composable m1 m2 ) |]
  &&  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.full bucks_ph 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
  **  ((valid_pre) # Int  |->_)
.

Definition hashtbl_find_partial_solve_wit_3 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (l1: (@list Z)) (l2: (@list Z)) (top_ph: Z) (bucks_ph: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (kp: Z) (vp: Z) (p_next: Z) (k_cur: (@list Z)) (l_tail: (@list Z)) (h_val: Z) (t_l1: (@list Z)) (ind: Z) (i: Z) (i_v: Z) (h: Z) (key: Z) (valid: Z) ,
  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| (l2 = (cons (i_v) (l_tail))) |] 
  &&  [| ((m1 (k_cur)) = (Some (&((i_v)  # "blist" ->ₛ "key")))) |] 
  &&  [| ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) |] 
  &&  [| (l1 <> nil) |] 
  &&  [| (l1 = (cons (h_val) (t_l1))) |] 
  &&  [| (h_val = (Znth (ind) (lh) (0))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| forall (x: Z) , ~(((In x l1 ) /\ ((m1 (k)) = (Some (x))))) |]
  &&  ((i) # Ptr  |-> i_v)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind (Znth (ind) (lh) (0)) 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m1 )
  **  (((bucks_ph + (ind * sizeof(PTR) ) )) # Ptr  |-> h_val)
  **  (sllbseg &((h_val)  # "blist" ->ₛ "next") i t_l1 )
  **  (store_map store_uint m2 )
  **  (store_string key k )
  **  ((valid) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (store_string kp k_cur )
  **  (sll p_next l_tail )
|--
  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| (l2 = (cons (i_v) (l_tail))) |] 
  &&  [| ((m1 (k_cur)) = (Some (&((i_v)  # "blist" ->ₛ "key")))) |] 
  &&  [| ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) |] 
  &&  [| (l1 <> nil) |] 
  &&  [| (l1 = (cons (h_val) (t_l1))) |] 
  &&  [| (h_val = (Znth (ind) (lh) (0))) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| forall (x: Z) , ~(((In x l1 ) /\ ((m1 (k)) = (Some (x))))) |]
  &&  (store_string key k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind (Znth (ind) (lh) (0)) 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m1 )
  **  (((bucks_ph + (ind * sizeof(PTR) ) )) # Ptr  |-> h_val)
  **  (sllbseg &((h_val)  # "blist" ->ₛ "next") i t_l1 )
  **  (store_map store_uint m2 )
  **  ((valid) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l_tail )
.

Definition hashtbl_find_partial_solve_wit_4 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (l1: (@list Z)) (l2: (@list Z)) (top_ph: Z) (bucks_ph: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (kp: Z) (vp: Z) (p_next: Z) (k_cur: (@list Z)) (l_tail: (@list Z)) (ind: Z) (i: Z) (i_v: Z) (h: Z) (key: Z) (valid: Z) ,
  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| (l2 = (cons (i_v) (l_tail))) |] 
  &&  [| ((m1 (k_cur)) = (Some (&((i_v)  # "blist" ->ₛ "key")))) |] 
  &&  [| ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) |] 
  &&  [| (l1 = nil) |] 
  &&  [| (i = (bucks_ph + (ind * sizeof(PTR) ) )) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| forall (x: Z) , ~(((In x l1 ) /\ ((m1 (k)) = (Some (x))))) |]
  &&  ((i) # Ptr  |-> i_v)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind (Znth (ind) (lh) (0)) 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m1 )
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR) ) ) i l1 )
  **  (store_map store_uint m2 )
  **  (store_string key k )
  **  ((valid) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (store_string kp k_cur )
  **  (sll p_next l_tail )
|--
  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| (l2 = (cons (i_v) (l_tail))) |] 
  &&  [| ((m1 (k_cur)) = (Some (&((i_v)  # "blist" ->ₛ "key")))) |] 
  &&  [| ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) |] 
  &&  [| (l1 = nil) |] 
  &&  [| (i = (bucks_ph + (ind * sizeof(PTR) ) )) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| forall (x: Z) , ~(((In x l1 ) /\ ((m1 (k)) = (Some (x))))) |]
  &&  (store_string key k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind (Znth (ind) (lh) (0)) 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m1 )
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR) ) ) i l1 )
  **  (store_map store_uint m2 )
  **  ((valid) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l_tail )
.

Definition hashtbl_find_partial_solve_wit_5 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (l1: (@list Z)) (l2: (@list Z)) (top_ph: Z) (bucks_ph: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (kp: Z) (vp: Z) (p_next: Z) (k_cur: (@list Z)) (l_tail: (@list Z)) (ind: Z) (i: Z) (i_v: Z) (h: Z) (key: Z) (valid: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_cur) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| (l2 = (cons (i_v) (l_tail))) |] 
  &&  [| ((m1 (k_cur)) = (Some (&((i_v)  # "blist" ->ₛ "key")))) |] 
  &&  [| ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) |] 
  &&  [| (l1 = nil) |] 
  &&  [| (i = (bucks_ph + (ind * sizeof(PTR) ) )) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| forall (x: Z) , ~(((In x l1 ) /\ ((m1 (k)) = (Some (x))))) |]
  &&  (store_string key k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> p_next)
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind (Znth (ind) (lh) (0)) 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m1 )
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR) ) ) i l1 )
  **  (store_map store_uint m2 )
  **  ((valid) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l_tail )
|--
  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (k = k_cur) |] 
  &&  [| (0 <= ind) |] 
  &&  [| (ind < 211) |] 
  &&  [| (ind = ((hash_string_k (k)) % ( 211 ) )) |] 
  &&  [| (l2 = (cons (i_v) (l_tail))) |] 
  &&  [| ((m1 (k_cur)) = (Some (&((i_v)  # "blist" ->ₛ "key")))) |] 
  &&  [| ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) |] 
  &&  [| (l1 = nil) |] 
  &&  [| (i = (bucks_ph + (ind * sizeof(PTR) ) )) |] 
  &&  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |] 
  &&  [| forall (x: Z) , ~(((In x l1 ) /\ ((m1 (k)) = (Some (x))))) |]
  &&  (((bucks_ph + (ind * sizeof(PTR) ) )) # Ptr  |-> p_next)
  **  (store_string key k )
  **  (store_string kp k_cur )
  **  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind (Znth (ind) (lh) (0)) 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m1 )
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR) ) ) i l1 )
  **  (store_map store_uint m2 )
  **  ((valid) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l_tail )
.

Definition hashtbl_find_which_implies_wit_1 := 
forall (m1: ((@list Z) -> (@option Z))) (h: Z) ,
  (store_hash_skeleton h m1 )
|--
  EX (lh: (@list Z))  (b: (Z -> (@option (Z * (@list Z)))))  (l: (@list Z))  (bucks_ph: Z)  (top_ph: Z) ,
  [| (contain_all_addrs m1 l ) |] 
  &&  [| (repr_all_heads lh b ) |] 
  &&  [| (contain_all_correct_addrs m1 b ) |]
  &&  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.full bucks_ph 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1 )
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
Axiom proof_of_hashtbl_find_safety_wit_1 : hashtbl_find_safety_wit_1.
Axiom proof_of_hashtbl_find_safety_wit_2 : hashtbl_find_safety_wit_2.
Axiom proof_of_hashtbl_find_safety_wit_3 : hashtbl_find_safety_wit_3.
Axiom proof_of_hashtbl_find_safety_wit_4 : hashtbl_find_safety_wit_4.
Axiom proof_of_hashtbl_find_safety_wit_5 : hashtbl_find_safety_wit_5.
Axiom proof_of_hashtbl_find_safety_wit_6 : hashtbl_find_safety_wit_6.
Axiom proof_of_hashtbl_find_safety_wit_7 : hashtbl_find_safety_wit_7.
Axiom proof_of_hashtbl_find_safety_wit_8 : hashtbl_find_safety_wit_8.
Axiom proof_of_hashtbl_find_safety_wit_9 : hashtbl_find_safety_wit_9.
Axiom proof_of_hashtbl_find_safety_wit_10 : hashtbl_find_safety_wit_10.
Axiom proof_of_hashtbl_find_safety_wit_11 : hashtbl_find_safety_wit_11.
Axiom proof_of_hashtbl_find_entail_wit_1 : hashtbl_find_entail_wit_1.
Axiom proof_of_hashtbl_find_entail_wit_2 : hashtbl_find_entail_wit_2.
Axiom proof_of_hashtbl_find_entail_wit_3 : hashtbl_find_entail_wit_3.
Axiom proof_of_hashtbl_find_entail_wit_4_1 : hashtbl_find_entail_wit_4_1.
Axiom proof_of_hashtbl_find_entail_wit_4_2 : hashtbl_find_entail_wit_4_2.
Axiom proof_of_hashtbl_find_entail_wit_4_3 : hashtbl_find_entail_wit_4_3.
Axiom proof_of_hashtbl_find_entail_wit_4_4 : hashtbl_find_entail_wit_4_4.
Axiom proof_of_hashtbl_find_entail_wit_5_1 : hashtbl_find_entail_wit_5_1.
Axiom proof_of_hashtbl_find_entail_wit_5_2 : hashtbl_find_entail_wit_5_2.
Axiom proof_of_hashtbl_find_entail_wit_5_3 : hashtbl_find_entail_wit_5_3.
Axiom proof_of_hashtbl_find_entail_wit_5_4 : hashtbl_find_entail_wit_5_4.
Axiom proof_of_hashtbl_find_entail_wit_6_1 : hashtbl_find_entail_wit_6_1.
Axiom proof_of_hashtbl_find_entail_wit_6_2 : hashtbl_find_entail_wit_6_2.
Axiom proof_of_hashtbl_find_return_wit_1 : hashtbl_find_return_wit_1.
Axiom proof_of_hashtbl_find_return_wit_2 : hashtbl_find_return_wit_2.
Axiom proof_of_hashtbl_find_return_wit_3 : hashtbl_find_return_wit_3.
Axiom proof_of_hashtbl_find_partial_solve_wit_1 : hashtbl_find_partial_solve_wit_1.
Axiom proof_of_hashtbl_find_partial_solve_wit_2 : hashtbl_find_partial_solve_wit_2.
Axiom proof_of_hashtbl_find_partial_solve_wit_3 : hashtbl_find_partial_solve_wit_3.
Axiom proof_of_hashtbl_find_partial_solve_wit_4 : hashtbl_find_partial_solve_wit_4.
Axiom proof_of_hashtbl_find_partial_solve_wit_5 : hashtbl_find_partial_solve_wit_5.
Axiom proof_of_hashtbl_find_which_implies_wit_1 : hashtbl_find_which_implies_wit_1.

End VC_Correct.
