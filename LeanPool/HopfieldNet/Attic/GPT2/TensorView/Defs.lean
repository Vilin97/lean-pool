/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.LLM.GPT2.Core
import LeanPool.HopfieldNet.LLM.GPT2.ByteArrayUtils
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Data.Array.Extract
import Mathlib.Data.Nat.Lattice

open LLM.GPT2
open Batteries

set_option linter.unusedVariables false
namespace LLM.GPT2

--  Section 3: TensorView Structure and Safety


/--
A `TensorView` provides a typed, multi-dimensional view into a `ByteArray` storage.
It defines the shape, rank, and offset of the tensor data within the storage.

This structure is designed to work within a stateful context `s`
because it holds a reference (`ST.Ref`) to the underlying `ByteArray`.

A `ByteArray` in Lean is a mutable, fixed-size array of bytes (8-bit unsigned integers).
It is used for efficient storage and manipulation of raw binary data, such as the contents of files,
serialized objects, or memory buffers. In this context, the `ByteArray` holds the raw tensor data,
typically representing a sequence of floating-point numbers encoded as bytes.

Key properties:
- The `rank` (number of dimensions) is explicitly stored and proven to be equal to `shape.size`.
- The `offsetBytes` into the storage is proven to be aligned to `bytesPerFloat`.
- All dimension sizes in `shape` are proven to be positive.

# Example

Suppose you have a 2x3 matrix of floats stored in a `ByteArray` (6 floats in total).
You can create a `TensorView` for this matrix as follows:

- `shape = #[2, 3]` (2 rows, 3 columns)
- `rank = 2`
- `storageRef` points to the `ByteArray` containing the data
- `offsetBytes = 0` (starts at the beginning)
- `h_offset_aligned` proves that `0 % bytesPerFloat = 0`
- `h_rank_eq_size` proves that `rank = shape.size`
- `h_dims_positive` proves that both 2 and 3 are > 0

This `TensorView` lets you treat the underlying bytes as a 2x3 matrix, with all accesses and indexing checked for safety.
-/
structure TensorView (s : Type) where
  /-- Shape of the tensor, as an array of dimension sizes. Validated > 0. -/
  shape : Array Nat
  /-- Rank (number of dimensions). `shape.size`. -/
  rank : Nat
  /-- Proof that rank equals the size of shape. -/
  h_rank_eq_size : rank = shape.size
  /-- Reference to the underlying storage ByteArray containing the tensor data. -/
  storageRef : ST.Ref s ByteArray
  /-- Byte offset in the storage where this tensor view begins. Proven aligned to `bytesPerFloat`. -/
  offsetBytes : Nat
  /-- Proof that offsetBytes is aligned. -/
  h_offset_aligned : offsetBytes % bytesPerFloat = 0
  /-- Proof that all dimensions in shape are positive. -/
    h_dims_positive : ∀ (i : Fin rank), shape[i.val]'(by {
        have h1 : i.val < rank := i.isLt
        have h2 : rank = shape.size := h_rank_eq_size
        exact Nat.lt_of_lt_of_eq h1 h2
      }) > 0
  -- No Inhabited instance needed or desirable

/--
Total number of elements in the tensor view. Guaranteed > 0 since dims > 0.

# Example

Suppose `tv.shape = #[2, 3, 4]`. Then `tv.elementCount = 2 * 3 * 4 = 24`.

This means the tensor view represents a 3-dimensional tensor with 2 × 3 × 4 = 24 elements.
-/
@[inline] def TensorView.elementCount {s : Type} (tv : TensorView s) : Nat :=
  -- Foldl starts with 1, and all shape[i] > 0, so result > 0
  tv.shape.foldl (· * ·) 1

namespace Array

/--
If an index `i` is within the bounds of an array `arr`, then `arr[i]!` (unsafe get)
is equal to `arr[i]` (safe get, written as `arr[i]'h_bounds`).

# Example

Suppose `arr : Array Nat := #[10, 20, 30]` and `i = 1`.
Since `1 < arr.size`, we have:
- `arr[1]! = 20`
- `arr[1]'(by decide) = 20`
Therefore, `arr[1]! = arr[1]'(by decide)`.

-/
lemma getElem_eq_get! {α : Type} [Inhabited α] {arr : Array α} {i : Nat} (h_bounds : i < arr.size) :
  arr[i]! = arr[i]'h_bounds := by
  exact getElem!_pos arr i h_bounds

end Array

/--
This lemma is similar to `Array.getElem_of_mem`, but it provides the equality with `arr[i]!`
instead of `arr[i]`.
Suppose `arr : Array Nat := #[4, 7, 9]` and `x = 7`. Since `7 ∈ arr`, there exists `i = 1` such that `arr[1]! = 7`.
-/
lemma exists_index_of_mem_with_get_bang
    {α : Type} [Inhabited α]
    {arr : Array α} {x : α} (h_mem : x ∈ arr) :
    ∃ i : Nat, i < arr.size ∧ arr[i]! = x := by
  rcases Array.getElem_of_mem h_mem with ⟨i, h_i_lt, h_get⟩
  have h_get_bang : arr[i]! = x := by
    rw [Array.getElem_eq_get! h_i_lt]
    exact h_get
  exact ⟨i, h_i_lt, h_get_bang⟩

/-- Proof that the element count is positive.
Suppose we have a `TensorView` with shape `[2, 3, 4]`. Then the element count is `2 * 3 * 4 = 24`, which is greater than zero.
-/
lemma TensorView.elementCount_pos {s : Type} (tv : TensorView s) : tv.elementCount > 0 := by
  rw [TensorView.elementCount]
  have h_array_to_list : tv.shape.foldl (· * ·) 1 = List.foldl (· * ·) 1 tv.shape.toList := by
    simp only [Array.foldl_toList, Array.toListImpl_eq]
  rw [h_array_to_list]
  have h : List.foldl (· * ·) 1 tv.shape.toList = tv.shape.toList.prod := by
    exact (List.prod_eq_foldl (l := tv.shape.toList)).symm
  rw [h]
  apply List.prod_pos
  intro x hx_mem_list
  have h_x_in_array : x ∈ tv.shape := by
    rw [← Array.mem_toList_iff]
    exact hx_mem_list
  have h_exists_idx : ∃ i < tv.shape.size, tv.shape[i]! = x := by
    have : ∃ i, i < tv.shape.size ∧ tv.shape[i]! = x := by
      by_contra h_no_idx
      simp only [not_exists, not_and] at h_no_idx
      have h_x_not_in : x ∉ tv.shape := by
        intro h_in
        have h_exists : ∃ i, i < tv.shape.size ∧ tv.shape[i]! = x :=
          exists_index_of_mem_with_get_bang h_x_in_array
        rcases h_exists with ⟨i, h_i_lt, h_x_eq⟩
        specialize h_no_idx i
        exact h_no_idx h_i_lt h_x_eq
      exact h_x_not_in h_x_in_array
    rcases this with ⟨i, h_i_lt, h_eq⟩
    exact ⟨i, h_i_lt, h_eq⟩
  rcases h_exists_idx with ⟨i, h_i_lt, h_x_eq⟩
  rw [← h_x_eq]
  have h_i_lt_rank : i < tv.rank := by { rw [tv.h_rank_eq_size]; exact h_i_lt }
  let fin_i_rank : Fin tv.rank := ⟨i, h_i_lt_rank⟩
  have h_get_eq_get_bang : tv.shape[fin_i_rank] = tv.shape[i]! := by
    exact Eq.symm (getElem!_pos tv.shape i h_i_lt)
  have h_pos : tv.shape[fin_i_rank] > 0 := tv.h_dims_positive fin_i_rank
  rw [h_get_eq_get_bang] at h_pos
  exact h_pos

/-- Total size in bytes of this tensor view. Guaranteed divisible by `bytesPerFloat`. -/
@[inline] def TensorView.sizeBytes {s : Type} (tv : TensorView s) : Nat :=
  tv.elementCount * bytesPerFloat

/-- Proof that sizeBytes is a multiple of bytesPerFloat. -/
lemma TensorView.sizeBytes_dvd {s : Type} (tv : TensorView s) : bytesPerFloat ∣ tv.sizeBytes := by
  simp [sizeBytes];

/-- Proof that the view fits within the storage, derived from creation. -/
structure TensorView.ValidView {s : Type} (tv : TensorView s) (storageSize : Nat) where
  h_valid : tv.offsetBytes + tv.sizeBytes <= storageSize

/-- Internal helper to validate shape dimensions. -/
def validateShape (shape : Array Nat) : Except TensorError (Nat × (Nat → Prop)) := Id.run do
  if shape.isEmpty then
    -- Allow scalar tensors (rank 0)
    return Except.ok (0, fun _ => True)
  else
    -- Check each dimension
    for i in [:shape.size] do
      if shape[i]! == 0 then return Except.error (TensorError.negativeDimension shape)
    -- If loop completes, all dimensions are positive
    let rank := shape.size
    -- Return the rank and a predicate that validates indices
    return Except.ok (rank, fun i => i < rank → shape[i]! > 0)

/--
A recursive helper for `validateShapeRec`.
Checks dimensions from `idx` onwards.
Returns `Except.ok ()` if all dimensions from `idx` are positive.
Returns `Except.error` if a zero dimension is found.
-/
def validateShapeLoopRec (shape : Array Nat) (idx : Nat) : Except TensorError Unit :=
  if h_idx_lt_size : idx < shape.size then
    if shape[idx]! == 0 then
      Except.error (TensorError.negativeDimension shape)
    else
      validateShapeLoopRec shape (idx + 1)
  else
    Except.ok () -- All checked dimensions were positive
termination_by shape.size - idx

/-- Creates a TensorView assuming validation and checks passed during buffer construction. -/
@[inline]
def TensorView.mkUnsafe (s : Type) (shape : Array Nat) (rank : Nat) (storageRef : ST.Ref s ByteArray)
    (offsetBytes : Nat) (h_offset_aligned : offsetBytes % bytesPerFloat = 0)
    (h_rank_eq_size : rank = shape.size)
    (h_dims_positive : ∀ (i : Fin rank), shape[i.val]'(by
        rw [← h_rank_eq_size]
        exact i.isLt) > 0) : TensorView s :=
  { shape, rank, storageRef, offsetBytes, h_offset_aligned, h_dims_positive, h_rank_eq_size }

/-- Represent the `TensorView` as `Std.Format` with the given precedence. -/
protected def TensorView.reprPrec {s : Type} (tv : TensorView s) (prec : Nat) : Std.Format :=
  let shapeStr := toString tv.shape
  let rankStr := toString tv.rank
  let offsetStr := toString tv.offsetBytes
  Std.Format.bracket "TensorView(" (Std.Format.text ("shape: " ++ shapeStr ++ ",
    rank: " ++ rankStr ++ ", offsetBytes: " ++ offsetStr)) ")"

instance (s : Type) : Repr (TensorView s) where
  reprPrec := TensorView.reprPrec

/--
Helper function for computing flat indices. Processes the dimensions in reverse order
(from least significant to most significant).

Given:

- `shape`: An array representing the dimensions of the tensor.
- `rank`: The number of dimensions of the tensor (i.e., `shape.size`).
- `indices`: An array of indices specifying the element to access.
- `i_rev`: The current dimension index being processed, in reverse order (from `0` to `rank - 1`).
       It corresponds to `rank - 1 - i` where `i` is the actual dimension index.
- `flatIndexRel`: The partially computed flat index from less significant dimensions.
- `stride`: The stride for the current dimension `i`.

this function iterates from the least significant dimension (`i_rev = 0`, which is `i = rank - 1`)
to the most significant dimension.
In each step:
1. It retrieves the current `index` and `dimSize` for dimension `i = rank - 1 - i_rev`.
2. It checks if `index` is out of bounds for `dimSize`. If so, it returns `TensorError.indexOutOfBounds`.
3. Otherwise, it updates `flatIndexRel` by adding `index * stride`.
4. It updates `stride` for the next (more significant) dimension by multiplying with `dimSize`.
5. It recursively calls itself for the next dimension (`i_rev + 1`).

The base case for the recursion is when `i_rev >= rank`, meaning all dimensions have been processed.
In this case, it returns the final `flatIndexRel`.

The `termination_by` clause `rank - i_rev` makes the function terminate because `i_rev` increases
in each recursive call, and `rank` is fixed, so `rank - i_rev` decreases.
-/
def computeHelper (shape : Array Nat) (rank : Nat) (indices : Array Nat)
                  (i_rev : Nat) (flatIndexRel : Nat) (stride : Nat)
                  : Except TensorError Nat :=
  if i_rev >= rank then
    Except.ok flatIndexRel
  else
    let i := rank - 1 - i_rev
    let index := indices[i]!
    let dimSize := shape[i]!
    if index >= dimSize then
      Except.error (TensorError.indexOutOfBounds indices shape)
    else
      let newFlatIndex := flatIndexRel + index * stride
      let newStride := stride * dimSize
      computeHelper shape rank indices (i_rev + 1) newFlatIndex newStride
termination_by rank - i_rev

/--
`ComputeHelperRel` defines a relation that mirrors the logic of the `computeHelper`
function, which is  used to calculate a flat (1D) index from a
multi-dimensional index array. This relational definition is provided as an
alternative to the functional one, primarily to try simplify and facilitate proofs
about the properties of `computeHelper` within the `Lemmas.lean` file.

The relation `ComputeHelperRel shape rank indices i fir sa res` holds if,
starting from an iteration index `i`, a current flat index `fir` (flat index relative),
and a current stride `sa` (stride accumulator), the computation eventually
results in `res`.
-/
inductive ComputeHelperRel (shape : Array Nat) (rank : Nat) (indices : Array Nat) :
  Nat → Nat → Nat → Nat → Prop where
| tc (i fir sa) (h_term : i >= rank) :
    ComputeHelperRel shape rank indices i fir sa fir
| rs (i fir sa newFir newSa res)
    (h_not_term : i < rank)
    (k : Nat) (hk_def : k = rank - 1 - i)
    (h_k_lt_idx_size : k < indices.size) (h_k_lt_shape_size : k < shape.size)
    (idx_val : Nat) (h_idx_eq : idx_val = indices[k]'h_k_lt_idx_size)
    (dim_val : Nat) (h_dim_eq : dim_val = shape[k]'h_k_lt_shape_size)
    (h_bound : idx_val < dim_val)
    (h_newFir_def : newFir = fir + idx_val * sa)
    (h_newSa_def : newSa = sa * dim_val)
    (h_recursive_call : ComputeHelperRel shape rank indices (i+1) newFir newSa res) :
    ComputeHelperRel shape rank indices i fir sa res

/--
Computes the flat (1D) index from a multi-dimensional `indices` array for a tensor
with a given `shape` and `rank`.

This function translates a coordinate in a multi-dimensional space into a
single linear index, which can be used for accessing elements in a flat memory layout.
The specific mapping (e.g., row-major or column-major) depends on the
implementation of the `computeHelper` function, which performs the actual calculation.

Given:
- `shape`: An `Array Nat` representing the dimensions of the tensor.
  Each element `shape[j]` is the size of the j-th dimension.
- `rank`: A `Nat` indicating the number of dimensions of the tensor.
- `h_rank_eq_size`: A proof that `rank` is equal to `shape.size`. This ensures
  consistency between the provided rank and the shape array.
- `_`: An (unnamed) proof that all dimension sizes in `shape` are strictly positive
  (i.e., `shape[j] > 0` for all `j` up to `rank`). This is crucial for meaningful tensor
  structures and stride calculations.
- `indices`: An `Array Nat` containing the multi-dimensional coordinates for which
  the flat index is to be computed. `indices[j]` is the index for the j-th dimension.

it returns:
- `Except TensorError Nat`:
  - `Except.ok flatIndex`: If the input is valid (specifically, if `indices.size == rank`),
    this contains the calculated `flatIndex` as a `Nat`.
  - `Except.error (TensorError.shapeMismatch rank indices.size)`: If the number of
    provided `indices` (i.e., `indices.size`) does not match the tensor `rank`.

Note:
- The validation of whether individual `indices[j]` are within the bounds of `shape[j]`
  (i.e., `0 <= indices[j] < shape[j]`) is not performed by this function directly.
  It is assumed that such checks are either handled by the `computeHelper` function
  or ?.
- The `computeHelper` function is responsible for the actual index calculation,
  being invoked as `computeHelper shape rank indices 0 0 1`. The precise meaning
  of the `0 0 1` arguments depends on `computeHelper`'s signature and logic,
  but they would represent initial values for an iterative or recursive calculation
  (e.g., current dimension index, accumulated offset, and an initial multiplier/stride).
-/
@[inline]
def computeFlatIndex (shape : Array Nat) (rank : Nat)
                     (h_rank_eq_size : rank = shape.size)
                     (_ : ∀ (i : Fin rank), shape[i.val]'(by {
                        have h1 : i.val < rank := i.isLt
                        have h2 : rank = shape.size := h_rank_eq_size
                        exact Nat.lt_of_lt_of_eq h1 h2
                      }) > 0)
                     (indices : Array Nat) : Except TensorError Nat :=
  if indices.size != rank then
    Except.error (TensorError.shapeMismatch rank indices.size)
  else
    computeHelper shape rank indices 0 0 1

end LLM.GPT2
