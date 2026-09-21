/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# A nontrivial relation among too many vectors of a finite span

More vectors than generators are linearly dependent: if a family `w : Γ → V` of vectors lies in
the span of `M` generators and `Γ` has more than `M` elements, then some finite nontrivial
`K`-linear combination of the `w γ` vanishes. The vectors `w γ` need not be distinct.
-/

universe u v w

public section

namespace Module

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

/-- A family of more than `M` vectors in the span of `M` generators admits a nontrivial vanishing
linear combination. -/
theorem exists_nontrivial_relation_of_mem_span_range {ι : Type w} [Fintype ι] (gens : ι → V)
    {Γ : Type*} [Fintype Γ] (w : Γ → V)
    (hw : ∀ γ, w γ ∈ Submodule.span K (Set.range gens)) (hcard : Fintype.card ι < Fintype.card Γ) :
    ∃ (s : Finset Γ) (δ : Γ → K), ∑ γ ∈ s, δ γ • w γ = 0 ∧ ∃ γ ∈ s, δ γ ≠ 0 := by
  by_contra hrel
  rw [← not_linearIndependent_iff, not_not] at hrel
  let w' : Γ → Submodule.span K (Set.range gens) := fun γ ↦ ⟨w γ, hw γ⟩
  have hw' : LinearIndependent K w' := by
    refine LinearIndependent.of_comp (Submodule.span K (Set.range gens)).subtype ?_
    exact hrel
  haveI : Module.Finite K (Submodule.span K (Set.range gens)) :=
    Module.Finite.span_of_finite K (Set.finite_range gens)
  have hle := hw'.fintype_card_le_finrank
  have hrank := finrank_range_le_card (R := K) gens
  exact absurd (hle.trans hrank) (not_le.mpr hcard)

end Module

end
