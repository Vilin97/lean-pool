/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# Finite-dimensionality from uniform finite independence bounds

Čech obstruction spaces are naturally presented as quotients of an
infinite-dimensional function field.  It is often easier to bound each
finite linearly independent family than to exhibit one global finite set of
generators.  The lemma below packages the standard basis argument converting
that uniform bound into finite-dimensionality and a `finrank` estimate.
-/

@[expose] public section

namespace BGS.HasseWeil

noncomputable section

universe u v

/-- If every finite linearly independent family in a vector space has at
most `g` elements, then the whole space is finite-dimensional of dimension
at most `g`. -/
theorem moduleFinite_and_finrank_le_of_finite_linearIndependent_card_le
    {K : Type u} {V : Type v}
    [DivisionRing K] [AddCommGroup V] [Module K V]
    (g : ℕ)
    (hbound : ∀ (ι : Type v) [Fintype ι] (v : ι → V),
      LinearIndependent K v → Fintype.card ι ≤ g) :
    Module.Finite K V ∧ Module.finrank K V ≤ g := by
  classical
  let b := Module.Basis.ofVectorSpace K V
  let ι := Module.Basis.ofVectorSpaceIndex K V
  have hιFinite : Finite ι := by
    rw [← not_infinite_iff_finite]
    intro hιInfinite
    let : Infinite ι := hιInfinite
    obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq ι (g + 1)
    let v : s → V := fun i ↦ b i.1
    have hv : LinearIndependent K v :=
      b.linearIndependent.comp _ Subtype.val_injective
    have hle := hbound s v hv
    have hcard : Fintype.card s = g + 1 := by
      simpa only [Fintype.card_coe] using hs
    omega
  let : Finite ι := hιFinite
  let : Fintype ι := Fintype.ofFinite ι
  let hfinite : Module.Finite K V := Module.Finite.of_basis b
  let : Module.Finite K V := hfinite
  refine ⟨hfinite, ?_⟩
  rw [Module.finrank_eq_card_basis b]
  exact hbound ι b b.linearIndependent

end

end BGS.HasseWeil
