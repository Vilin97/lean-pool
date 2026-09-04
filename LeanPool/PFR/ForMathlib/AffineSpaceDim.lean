/-
Copyright (c) 2026 PFR contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PFR contributors
-/

module

public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import LeanPool.PFR.Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Dimensions of affine spaces
-/

open scoped Pointwise

namespace AffineSpace
variable {k V P : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P] {s : Set P}
  {S : Submodule k V}

variable (k) in
open scoped Classical in
/-- The dimension of the affine span over `ℤ` of a subset of an additive group. -/
@[expose]
public
noncomputable def finrank (s : Set P) : ℕ := (vectorSpan k s).finrank

variable (k) in
@[simp]
public
lemma finrank_vadd_set (s : Set P) (v : V) : finrank k (v +ᵥ s) = AffineSpace.finrank k s := by
  simp [finrank]



variable [StrongRankCondition k]



public
lemma finrank_le_moduleFinrank [Module.Finite k V] : finrank k s ≤ Module.finrank k V :=
  (vectorSpan k s).finrank_le

end AffineSpace
