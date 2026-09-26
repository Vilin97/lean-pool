/-
Copyright (c) 2026 David Muñoz-Lahoz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Muñoz-Lahoz
-/

module

public import LeanPool.OrderClosures.BanLat.Normed

/-!
# Products of vector lattices

The pointwise product of vector lattices is a vector lattice. This is the product
instance from BanLat `Pi.lean`; the separate finite-dimensional normed products
are outside the dependency closure of the order-adherence constructions.
-/

@[expose] public section

/-! ### Pointwise product -/

namespace Pi

variable {ι : Type*} {X : ι → Type*}
  [∀ i, AddCommGroup (X i)] [∀ i, Lattice (X i)] [∀ i, IsOrderedAddMonoid (X i)]
  [∀ i, VectorLattice (X i)]

/-- The pointwise product of a family of vector lattices is a vector lattice.
The lattice operations and absolute value are computed pointwise (see
`Pi.sup_apply`, `Pi.inf_apply`, `Pi.abs_apply` in Mathlib). -/
instance instVectorLattice : VectorLattice (∀ i, X i) := ⟨⟩

end Pi
