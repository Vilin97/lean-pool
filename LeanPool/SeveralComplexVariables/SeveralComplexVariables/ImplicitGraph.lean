/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.ImplicitMapping
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Topology.Graph

/-!
# Local zero sets as graphs

The implicit mapping theorem supplies a homeomorphism from a regular local zero set to the
parameter neighborhood. This is an elementary statement about subsets of product spaces, without
a manifold or analytic-space structure. Reference: [Scheidemann][Scheidemann2005] (2005),
Corollary 3.1.5.

## Main results

`Homeomorph.implicitGraph` is the local graph homeomorphism of a regular zero set in a product.
`exists_implicit_zero_homeomorph` packages existence of that homeomorphism from the implicit
mapping theorem.

## References

* [V. Scheidemann, *Introduction to Complex Analysis in Several Variables*][Scheidemann2005]
-/

public noncomputable section

open Set

namespace SeveralComplexVariables

variable {P Q R : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup Q] [NormedSpace ℂ Q] [NormedAddCommGroup R] [NormedSpace ℂ R]

/-- Near a regular zero, projection identifies the zero set homeomorphically with an open parameter
neighborhood. This retains the analytic graph and its explicit projection. -/
theorem exists_implicit_zero_homeomorph [FiniteDimensional ℂ P] [FiniteDimensional ℂ Q]
    [CompleteSpace R] {D : Set (P × Q)} (hD : IsOpen D)
    {f : P × Q → R} (hf : DifferentiableOn ℂ f D) {a : P} {b : Q}
    (hab : (a, b) ∈ D) (hz : f (a, b) = 0)
    (hi : ((fderiv ℂ f (a, b)).comp (ContinuousLinearMap.inr ℂ P Q)).IsInvertible) :
    ∃ (U : Set P) (V : Set Q), IsOpen U ∧ a ∈ U ∧ IsOpen V ∧ b ∈ V ∧ U ×ˢ V ⊆ D ∧
      ∃ e : {p : P × Q // p ∈ U ×ˢ V ∧ f p = 0} ≃ₜ U,
        ∀ p, (e p).val = p.val.1 := by
  obtain ⟨U, V, g, hU, ha, hV, hb, hsub, hg, hm, _, hgraph⟩ :=
    exists_holomorphic_implicit_zero hD hf hab hz hi
  exact ⟨U, V, hU, ha, hV, hb, hsub, Homeomorph.implicitGraph hg.continuousOn hm hgraph,
    fun _ => rfl⟩

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
