/*@ Extern Coq (sublist : {A} -> Z -> Z -> list A -> list A)
               (PtrArray::full : Z -> Z -> list Z -> Assertion)
               (PtrArray::missing_i: Z -> Z -> Z -> Z -> list Z -> Assertion)
               (PtrArray::ceil: Z -> Z -> Z -> list Z -> Assertion)
               (PtrArray::ceil_shape: Z -> Z -> Z -> Assertion)
               (PtrArray::full_shape: Z -> Z -> Assertion)
               (PtrArray::missing_i_shape : Z -> Z -> Z -> Z -> Assertion)
               (PtrArray::undef_full : Z -> Z -> Assertion)
               (PtrArray::undef_ceil: Z -> Z -> Z -> Assertion)
               (PtrArray::undef_missing_i: Z -> Z -> Z -> Z -> Assertion)
               (Znth: {A} -> Z -> list A -> A -> A)
               (replace_Znth: {A} -> Z -> A -> list A -> list A)
               (zeros: Z -> list Z)
               (repeat_Z: {A} -> A -> Z -> list A)
*/

/*@ include strategies "ptr_array.strategies" */
