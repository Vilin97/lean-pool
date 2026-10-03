/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.Directional.EstimateDefs
public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.DirectionalQuadratic.Polarization

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Reconstruction from directional quadratic data

This file converts mixed directional quadratic estimate data into the project-local
second-order differentiability predicate.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Mixed-directional quadratic estimate data implies second-order differentiability. -/
theorem MixedDirectionalQuadraticEstimateAt.secondOrderDifferentiableAt
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : MixedDirectionalQuadraticEstimateAt D v u x) :
    SecondOrderDifferentiableAt u x := by
  rcases h with ⟨p, a, hest⟩
  exact secondOrderDifferentiableAt_of_eventually_norm_affineRemainder_sub_quadratic_le_mul
    (isSymmetricOperator_mixedDirectionalQuadraticSum D v a) hest

/-- Mixed-directional quadratic quotient data implies second-order differentiability. -/
theorem MixedDirectionalQuadraticQuotientEstimateAt.secondOrderDifferentiableAt
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : MixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    SecondOrderDifferentiableAt u x := by
  rcases h with ⟨p, a, hest⟩
  exact secondOrderDifferentiableAt_of_eventually_norm_affineRemainder_sub_quadratic_div_norm_sq_le
    (isSymmetricOperator_mixedDirectionalQuadraticSum D v a) hest

/-- Polarized coefficient estimate data is a special case of mixed-directional estimate data. -/
theorem PolarizedMixedDirectionalQuadraticEstimateAt.mixedDirectionalQuadraticEstimateAt
    {ι : Type*} [DecidableEq ι] {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    MixedDirectionalQuadraticEstimateAt D v u x := by
  rcases h with ⟨p, q, r, hest⟩
  refine ⟨p, polarizedMixedCoefficient q r, ?_⟩
  simpa [polarizedMixedQuadraticSum] using hest

namespace PolarizedMixedDirectionalQuadraticQuotientEstimateAt

/-- Punctured normalized polarized coefficient estimate data is a special case of
mixed-directional quotient estimate data. -/
theorem mixedDirectionalQuadraticQuotientEstimateAt
    {ι : Type*} [DecidableEq ι] {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    MixedDirectionalQuadraticQuotientEstimateAt D v u x := by
  rcases h with ⟨p, q, r, hest⟩
  refine ⟨p, polarizedMixedCoefficient q r, ?_⟩
  simpa [polarizedMixedQuadraticSum] using hest

end PolarizedMixedDirectionalQuadraticQuotientEstimateAt

/-- Polarized mixed-directional estimate data implies second-order differentiability. -/
theorem PolarizedMixedDirectionalQuadraticEstimateAt.secondOrderDifferentiableAt
    {ι : Type*} [DecidableEq ι] {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    SecondOrderDifferentiableAt u x :=
  h.mixedDirectionalQuadraticEstimateAt.secondOrderDifferentiableAt

/-- Polarized mixed-directional quotient estimate data implies second-order differentiability. -/
theorem PolarizedMixedDirectionalQuadraticQuotientEstimateAt.secondOrderDifferentiableAt
    {ι : Type*} [DecidableEq ι] {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    SecondOrderDifferentiableAt u x :=
  h.mixedDirectionalQuadraticQuotientEstimateAt.secondOrderDifferentiableAt

/-- If a symmetric ambient quadratic estimate has the prescribed pure and off-diagonal
pairwise-sum quadratic coefficients on a finite orthonormal spanning frame, then it is the
canonical polarized mixed-directional estimate. The algebraic identification of the Hessian
candidate is handled by finite-frame off-diagonal uniqueness. -/
theorem polarizedMixedDirectionalQuadraticEstimateAt_of_quadraticEstimateData_coefficients
    {ι : Type*} [DecidableEq ι] {D : Finset ι} {v : ι → E}
    (hv : FiniteOrthonormalSpanningOn D v) {u : E → ℝ} {x p : E}
    {B : E →L[ℝ] E} (hB : IsSymmetricOperator B) {q : ι → ℝ} {r : ι → ι → ℝ}
    (hest : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in nhds 0,
        ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ ≤
          ε * ‖z‖ ^ 2)
    (hr : ∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → r j i = r i j)
    (hpure : ∀ ⦃i : ι⦄, i ∈ D → inner ℝ (v i) (B (v i)) = q i)
    (hpair : ∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → i ≠ j →
      inner ℝ (v i + v j) (B (v i + v j)) = r i j) :
    PolarizedMixedDirectionalQuadraticEstimateAt D v u x := by
  have hEq :=
    hv.eq_polarizedMixedQuadraticSum_of_quadraticForm_eq_on_frame_and_add_offDiagonal
      hB hr hpure hpair
  refine ⟨p, q, r, ?_⟩
  simpa [hEq] using hest

/-- Punctured normalized quotient version of
`polarizedMixedDirectionalQuadraticEstimateAt_of_quadraticEstimateData_coefficients`. -/
theorem
    polarizedMixedDirectionalQuadraticQuotientEstimateAt_of_quadraticQuotientData_coefficients
    {ι : Type*} [DecidableEq ι] {D : Finset ι} {v : ι → E}
    (hv : FiniteOrthonormalSpanningOn D v) {u : E → ℝ} {x p : E}
    {B : E →L[ℝ] E} (hB : IsSymmetricOperator B) {q : ι → ℝ} {r : ι → ι → ℝ}
    (hest : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in nhdsWithin (0 : E) {z : E | z ≠ 0},
        ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ /
            ‖z‖ ^ 2 ≤ ε)
    (hr : ∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → r j i = r i j)
    (hpure : ∀ ⦃i : ι⦄, i ∈ D → inner ℝ (v i) (B (v i)) = q i)
    (hpair : ∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → i ≠ j →
      inner ℝ (v i + v j) (B (v i + v j)) = r i j) :
    PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x := by
  have hEq :=
    hv.eq_polarizedMixedQuadraticSum_of_quadraticForm_eq_on_frame_and_add_offDiagonal
      hB hr hpure hpair
  refine ⟨p, q, r, ?_⟩
  simpa [hEq] using hest

/-- A local mixed-directional estimate gives the punctured normalized quotient estimate with the
same directional coefficient matrix. -/
theorem MixedDirectionalQuadraticEstimateAt.mixedDirectionalQuadraticQuotientEstimateAt
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : MixedDirectionalQuadraticEstimateAt D v u x) :
    MixedDirectionalQuadraticQuotientEstimateAt D v u x := by
  rcases h with ⟨p, a, hest⟩
  refine ⟨p, a, ?_⟩
  intro ε hε
  filter_upwards [(hest ε hε).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hz hz_ne
  have hden : 0 < ‖z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz_ne)
  exact (div_le_iff₀ hden).mpr hz

/-- A local polarized mixed-directional estimate gives the punctured normalized quotient estimate
with the same pure and pairwise-sum coefficients. -/
theorem PolarizedMixedDirectionalQuadraticEstimateAt.quotientEstimateAt
    {ι : Type*} [DecidableEq ι] {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x := by
  rcases h with ⟨p, q, r, hest⟩
  refine ⟨p, q, r, ?_⟩
  intro ε hε
  filter_upwards [(hest ε hε).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hz hz_ne
  have hden : 0 < ‖z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz_ne)
  exact (div_le_iff₀ hden).mpr hz

/-- Mixed-directional quadratic estimate data is ambient quadratic estimate data with the
assembled mixed-directional Hessian candidate. -/
theorem MixedDirectionalQuadraticEstimateAt.quadraticEstimateAt
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : MixedDirectionalQuadraticEstimateAt D v u x) :
    QuadraticEstimateAt u x := by
  rcases h with ⟨p, a, hest⟩
  exact ⟨p, mixedDirectionalQuadraticSum D v a,
    isSymmetricOperator_mixedDirectionalQuadraticSum D v a, hest⟩

/-- Mixed-directional quotient estimate data is ambient quadratic quotient estimate data with
the assembled mixed-directional Hessian candidate. -/
theorem MixedDirectionalQuadraticQuotientEstimateAt.quadraticQuotientEstimateAt
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : MixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    QuadraticQuotientEstimateAt u x := by
  rcases h with ⟨p, a, hest⟩
  exact ⟨p, mixedDirectionalQuadraticSum D v a,
    isSymmetricOperator_mixedDirectionalQuadraticSum D v a, hest⟩

/-- Polarized mixed-directional quadratic estimate data is ambient quadratic estimate data. -/
theorem PolarizedMixedDirectionalQuadraticEstimateAt.quadraticEstimateAt
    {ι : Type*} [DecidableEq ι] {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    QuadraticEstimateAt u x :=
  h.mixedDirectionalQuadraticEstimateAt.quadraticEstimateAt

/-- Polarized mixed-directional quotient estimate data is ambient quadratic quotient estimate
data. -/
theorem PolarizedMixedDirectionalQuadraticQuotientEstimateAt.quadraticQuotientEstimateAt
    {ι : Type*} [DecidableEq ι] {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    QuadraticQuotientEstimateAt u x :=
  h.mixedDirectionalQuadraticQuotientEstimateAt.quadraticQuotientEstimateAt

/-- The mixed-directional estimate set is contained in the second-order differentiability locus. -/
theorem mixedDirectionalQuadraticEstimateSet_subset_secondOrderDifferentiabilitySet
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} :
    mixedDirectionalQuadraticEstimateSet D v u ⊆ secondOrderDifferentiabilitySet u := by
  intro x hx
  exact hx.secondOrderDifferentiableAt

/-- The mixed-directional quotient-estimate set is contained in the second-order differentiability
locus. -/
theorem mixedDirectionalQuadraticQuotientEstimateSet_subset_secondOrderDifferentiabilitySet
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} :
    mixedDirectionalQuadraticQuotientEstimateSet D v u ⊆ secondOrderDifferentiabilitySet u := by
  intro x hx
  exact hx.secondOrderDifferentiableAt

/-- The polarized mixed-directional estimate set is contained in the mixed-directional estimate
set. -/
theorem polarizedMixedDirectionalQuadraticEstimateSet_subset_mixedDirectionalQuadraticEstimateSet
    {ι : Type*} [DecidableEq ι] {D : Finset ι} {v : ι → E} {u : E → ℝ} :
    polarizedMixedDirectionalQuadraticEstimateSet D v u ⊆
      mixedDirectionalQuadraticEstimateSet D v u := by
  intro x hx
  exact hx.mixedDirectionalQuadraticEstimateAt

/-- The polarized mixed-directional quotient estimate set is contained in the mixed-directional
quotient estimate set. -/
theorem polarizedMixedDirectionalQuotientSet_subset_mixedDirectionalQuotientSet
    {ι : Type*} [DecidableEq ι] {D : Finset ι} {v : ι → E} {u : E → ℝ} :
    polarizedMixedDirectionalQuadraticQuotientEstimateSet D v u ⊆
      mixedDirectionalQuadraticQuotientEstimateSet D v u := by
  intro x hx
  exact hx.mixedDirectionalQuadraticQuotientEstimateAt

/-- The local mixed-directional estimate set is contained in its punctured normalized quotient
version. -/
theorem mixedDirectionalQuadraticEstimateSet_subset_mixedDirectionalQuadraticQuotientSet
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} :
    mixedDirectionalQuadraticEstimateSet D v u ⊆
      mixedDirectionalQuadraticQuotientEstimateSet D v u := by
  intro x hx
  exact hx.mixedDirectionalQuadraticQuotientEstimateAt

/-- The local polarized mixed-directional estimate set is contained in its punctured normalized
quotient version. -/
theorem
    polarizedMixedDirectionalQuadraticSet_subset_polarizedMixedDirectionalQuadraticQuotientSet
    {ι : Type*} [DecidableEq ι] {D : Finset ι} {v : ι → E} {u : E → ℝ} :
    polarizedMixedDirectionalQuadraticEstimateSet D v u ⊆
      polarizedMixedDirectionalQuadraticQuotientEstimateSet D v u := by
  intro x hx
  exact hx.quotientEstimateAt

/-- The mixed-directional estimate set is contained in the generic ambient quadratic estimate
set. -/
theorem mixedDirectionalQuadraticEstimateSet_subset_quadraticEstimateSet
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} :
    mixedDirectionalQuadraticEstimateSet D v u ⊆ quadraticEstimateSet u := by
  intro x hx
  exact hx.quadraticEstimateAt

/-- The mixed-directional quotient-estimate set is contained in the generic ambient quadratic
quotient-estimate set. -/
theorem mixedDirectionalQuadraticQuotientSet_subset_quadraticQuotientEstimateSet
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} :
    mixedDirectionalQuadraticQuotientEstimateSet D v u ⊆ quadraticQuotientEstimateSet u := by
  intro x hx
  exact hx.quadraticQuotientEstimateAt

/-- The polarized mixed-directional estimate set is contained in the generic ambient quadratic
estimate set. -/
theorem polarizedMixedDirectionalQuadraticSet_subset_quadraticEstimateSet
    {ι : Type*} [DecidableEq ι] {D : Finset ι} {v : ι → E} {u : E → ℝ} :
    polarizedMixedDirectionalQuadraticEstimateSet D v u ⊆ quadraticEstimateSet u := by
  intro x hx
  exact hx.quadraticEstimateAt

/-- The polarized mixed-directional quotient-estimate set is contained in the generic ambient
quadratic quotient-estimate set. -/
theorem polarizedMixedDirectionalQuotientSet_subset_quadraticQuotientEstimateSet
    {ι : Type*} [DecidableEq ι] {D : Finset ι} {v : ι → E} {u : E → ℝ} :
    polarizedMixedDirectionalQuadraticQuotientEstimateSet D v u ⊆
      quadraticQuotientEstimateSet u := by
  intro x hx
  exact hx.quadraticQuotientEstimateAt

/-- The polarized mixed-directional estimate set is contained in the second-order
differentiability locus. -/
theorem polarizedMixedDirectionalQuadraticEstimateSet_subset_secondOrderDifferentiabilitySet
    {ι : Type*} [DecidableEq ι] {D : Finset ι} {v : ι → E} {u : E → ℝ} :
    polarizedMixedDirectionalQuadraticEstimateSet D v u ⊆ secondOrderDifferentiabilitySet u := by
  intro x hx
  exact hx.secondOrderDifferentiableAt

/-- The polarized mixed-directional quotient estimate set is contained in the second-order
differentiability locus. -/
theorem
    polarizedMixedDirectionalQuadraticQuotientEstimateSet_subset_secondOrderDifferentiabilitySet
    {ι : Type*} [DecidableEq ι] {D : Finset ι} {v : ι → E} {u : E → ℝ} :
    polarizedMixedDirectionalQuadraticQuotientEstimateSet D v u ⊆
      secondOrderDifferentiabilitySet u := by
  intro x hx
  exact hx.secondOrderDifferentiableAt

/-- Mixed-directional quadratic estimate data restricts to scalar quadratic estimate data on
every affine line through the base point. -/
theorem MixedDirectionalQuadraticEstimateAt.realScalarQuadraticEstimateAt_lineRestriction
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : MixedDirectionalQuadraticEstimateAt D v u x) (w : E) :
    RealScalarQuadraticEstimateAt (lineRestriction u x w) 0 := by
  rcases h with ⟨p, a, hest⟩
  have hExp : HasSecondOrderExpansionAt u x p (mixedDirectionalQuadraticSum D v a) :=
    hasSecondOrderExpansionAt_of_eventually_norm_affineRemainder_sub_quadratic_le_mul hest
  exact realScalarQuadraticEstimateAt_of_hasSecondOrderExpansionAt
    (hExp.lineRestriction_hasSecondOrderExpansionAt w)

/-- Mixed-directional quadratic estimate data restricts to scalar quadratic estimate data with
the line slope and quadratic coefficient specified by the ambient data. -/
theorem MixedDirectionalQuadraticEstimateAt.realScalarQuadraticEstimateWithDataAt_lineRestriction
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : MixedDirectionalQuadraticEstimateAt D v u x) (w : E) :
    ∃ p : E, ∃ a : ι → ι → ℝ,
      RealScalarQuadraticEstimateWithDataAt (lineRestriction u x w) 0
        (inner ℝ p w) (inner ℝ w (mixedDirectionalQuadraticSum D v a w)) := by
  rcases h with ⟨p, a, hest⟩
  refine ⟨p, a, ?_⟩
  have hExp : HasSecondOrderExpansionAt u x p (mixedDirectionalQuadraticSum D v a) :=
    hasSecondOrderExpansionAt_of_eventually_norm_affineRemainder_sub_quadratic_le_mul hest
  have hline :=
    realScalarQuadraticEstimateWithDataAt_of_hasSecondOrderExpansionAt
      (hExp.lineRestriction_hasSecondOrderExpansionAt w)
  simpa using hline

/-- Mixed-directional punctured quotient estimate data restricts to scalar quadratic estimate
data on every affine line through the base point. -/
theorem MixedDirectionalQuadraticQuotientEstimateAt.realScalarQuadraticEstimateAt_lineRestriction
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : MixedDirectionalQuadraticQuotientEstimateAt D v u x) (w : E) :
    RealScalarQuadraticEstimateAt (lineRestriction u x w) 0 := by
  rcases h with ⟨p, a, hest⟩
  have hExp : HasSecondOrderExpansionAt u x p (mixedDirectionalQuadraticSum D v a) :=
    hasSecondOrderExpansionAt_of_eventually_norm_affineRemainder_sub_quadratic_div_norm_sq_le hest
  exact realScalarQuadraticEstimateAt_of_hasSecondOrderExpansionAt
    (hExp.lineRestriction_hasSecondOrderExpansionAt w)

/-- Mixed-directional punctured quotient estimate data restricts to explicit scalar quotient
estimate data with the line slope and quadratic coefficient specified by the ambient data. -/
theorem
    MixedDirectionalQuadraticQuotientEstimateAt.scalarQuotientWithData_lineRestriction
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : MixedDirectionalQuadraticQuotientEstimateAt D v u x) (w : E) :
    ∃ p : E, ∃ a : ι → ι → ℝ,
      RealScalarQuadraticQuotientEstimateWithDataAt (lineRestriction u x w) 0
        (inner ℝ p w) (inner ℝ w (mixedDirectionalQuadraticSum D v a w)) := by
  rcases h with ⟨p, a, hest⟩
  refine ⟨p, a, ?_⟩
  have hExp : HasSecondOrderExpansionAt u x p (mixedDirectionalQuadraticSum D v a) :=
    hasSecondOrderExpansionAt_of_eventually_norm_affineRemainder_sub_quadratic_div_norm_sq_le hest
  have hline :=
    realScalarQuadraticEstimateWithDataAt_of_hasSecondOrderExpansionAt
      (hExp.lineRestriction_hasSecondOrderExpansionAt w)
  simpa using hline.quadraticQuotientEstimateWithDataAt

/-- Mixed-directional quadratic estimate data restricts to punctured scalar quotient-estimate
data on every affine line through the base point. -/
theorem MixedDirectionalQuadraticEstimateAt.realScalarQuadraticQuotientEstimateAt_lineRestriction
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : MixedDirectionalQuadraticEstimateAt D v u x) (w : E) :
    RealScalarQuadraticQuotientEstimateAt (lineRestriction u x w) 0 :=
  (h.realScalarQuadraticEstimateAt_lineRestriction w).quadraticQuotientEstimateAt

/-- Mixed-directional punctured quotient estimate data restricts to punctured scalar
quotient-estimate data on every affine line through the base point. -/
theorem MixedDirectionalQuadraticQuotientEstimateAt.scalarQuotientEstimateAt_lineRestriction
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : MixedDirectionalQuadraticQuotientEstimateAt D v u x) (w : E) :
    RealScalarQuadraticQuotientEstimateAt (lineRestriction u x w) 0 :=
  (h.realScalarQuadraticEstimateAt_lineRestriction w).quadraticQuotientEstimateAt

/-- Mixed-directional quadratic estimate data implies the finite slice-estimate target for the
selected directions and their pairwise sums. -/
theorem MixedDirectionalQuadraticEstimateAt.directionalSliceEstimateAt
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : MixedDirectionalQuadraticEstimateAt D v u x) :
    DirectionalSliceEstimateAt D v u x :=
  ⟨fun i _hi => h.realScalarQuadraticEstimateAt_lineRestriction (v i),
    fun i _hi j _hj => h.realScalarQuadraticEstimateAt_lineRestriction (v i + v j)⟩

/-- Mixed-directional quadratic estimate data implies compatible finite slice data: all
one-dimensional first-order coefficients come from the same ambient slope. -/
theorem MixedDirectionalQuadraticEstimateAt.compatibleDirectionalSliceEstimateAt
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : MixedDirectionalQuadraticEstimateAt D v u x) :
    CompatibleDirectionalSliceEstimateAt D v u x := by
  rcases h with ⟨p, a, hest⟩
  let B : E →L[ℝ] E := mixedDirectionalQuadraticSum D v a
  have hExp : HasSecondOrderExpansionAt u x p B :=
    hasSecondOrderExpansionAt_of_eventually_norm_affineRemainder_sub_quadratic_le_mul hest
  refine ⟨p, (fun i => inner ℝ (v i) (B (v i))),
    (fun i j => inner ℝ (v i + v j) (B (v i + v j))), ?_, ?_⟩
  · intro i _hi
    have hline :=
      realScalarQuadraticEstimateWithDataAt_of_hasSecondOrderExpansionAt
        (hExp.lineRestriction_hasSecondOrderExpansionAt (v i))
    simpa [B] using hline
  · intro i _hi j _hj
    have hline :=
      realScalarQuadraticEstimateWithDataAt_of_hasSecondOrderExpansionAt
        (hExp.lineRestriction_hasSecondOrderExpansionAt (v i + v j))
    simpa [B] using hline

/-- Mixed-directional quadratic estimate data implies symmetric-compatible finite slice data.
The pairwise coefficients are read directly from the ambient quadratic model, so reversing the
order of the two selected directions does not change them. -/
theorem MixedDirectionalQuadraticEstimateAt.symmetricCompatibleDirectionalSliceEstimateAt
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : MixedDirectionalQuadraticEstimateAt D v u x) :
    SymmetricCompatibleDirectionalSliceEstimateAt D v u x := by
  rcases h with ⟨p, a, hest⟩
  let B : E →L[ℝ] E := mixedDirectionalQuadraticSum D v a
  have hExp : HasSecondOrderExpansionAt u x p B :=
    hasSecondOrderExpansionAt_of_eventually_norm_affineRemainder_sub_quadratic_le_mul hest
  refine ⟨p, (fun i => inner ℝ (v i) (B (v i))),
    (fun i j => inner ℝ (v i + v j) (B (v i + v j))), ?_, ?_, ?_⟩
  · intro i _hi j _hj
    simp [add_comm]
  · intro i _hi
    have hline :=
      realScalarQuadraticEstimateWithDataAt_of_hasSecondOrderExpansionAt
        (hExp.lineRestriction_hasSecondOrderExpansionAt (v i))
    simpa [B] using hline
  · intro i _hi j _hj
    have hline :=
      realScalarQuadraticEstimateWithDataAt_of_hasSecondOrderExpansionAt
        (hExp.lineRestriction_hasSecondOrderExpansionAt (v i + v j))
    simpa [B] using hline

/-- Mixed-directional quadratic estimate data implies the finite slice quotient-estimate target
for the selected directions and their pairwise sums. -/
theorem MixedDirectionalQuadraticEstimateAt.directionalSliceQuotientEstimateAt
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : MixedDirectionalQuadraticEstimateAt D v u x) :
    DirectionalSliceQuotientEstimateAt D v u x :=
  ⟨fun i _hi => h.realScalarQuadraticQuotientEstimateAt_lineRestriction (v i),
    fun i _hi j _hj => h.realScalarQuadraticQuotientEstimateAt_lineRestriction (v i + v j)⟩

/-- Mixed-directional quotient estimate data implies the finite slice-estimate target for the
selected directions and their pairwise sums. -/
theorem MixedDirectionalQuadraticQuotientEstimateAt.directionalSliceEstimateAt
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : MixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    DirectionalSliceEstimateAt D v u x :=
  ⟨fun i _hi => h.realScalarQuadraticEstimateAt_lineRestriction (v i),
    fun i _hi j _hj => h.realScalarQuadraticEstimateAt_lineRestriction (v i + v j)⟩

/-- Mixed-directional quotient estimate data implies compatible finite quotient-slice data. -/
theorem MixedDirectionalQuadraticQuotientEstimateAt.compatibleDirectionalSliceQuotientEstimateAt
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : MixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    CompatibleDirectionalSliceQuotientEstimateAt D v u x := by
  rcases h with ⟨p, a, hest⟩
  let B : E →L[ℝ] E := mixedDirectionalQuadraticSum D v a
  have hExp : HasSecondOrderExpansionAt u x p B :=
    hasSecondOrderExpansionAt_of_eventually_norm_affineRemainder_sub_quadratic_div_norm_sq_le hest
  refine ⟨p, (fun i => inner ℝ (v i) (B (v i))),
    (fun i j => inner ℝ (v i + v j) (B (v i + v j))), ?_, ?_⟩
  · intro i _hi
    have hline :=
      realScalarQuadraticEstimateWithDataAt_of_hasSecondOrderExpansionAt
        (hExp.lineRestriction_hasSecondOrderExpansionAt (v i))
    simpa [B] using hline.quadraticQuotientEstimateWithDataAt
  · intro i _hi j _hj
    have hline :=
      realScalarQuadraticEstimateWithDataAt_of_hasSecondOrderExpansionAt
        (hExp.lineRestriction_hasSecondOrderExpansionAt (v i + v j))
    simpa [B] using hline.quadraticQuotientEstimateWithDataAt

/-- Mixed-directional quotient estimate data implies symmetric-compatible finite quotient-slice
data. -/
theorem
    MixedDirectionalQuadraticQuotientEstimateAt.symmetricCompatibleQuotientEstimateAt
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : MixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    SymmetricCompatibleDirectionalSliceQuotientEstimateAt D v u x := by
  rcases h with ⟨p, a, hest⟩
  let B : E →L[ℝ] E := mixedDirectionalQuadraticSum D v a
  have hExp : HasSecondOrderExpansionAt u x p B :=
    hasSecondOrderExpansionAt_of_eventually_norm_affineRemainder_sub_quadratic_div_norm_sq_le hest
  refine ⟨p, (fun i => inner ℝ (v i) (B (v i))),
    (fun i j => inner ℝ (v i + v j) (B (v i + v j))), ?_, ?_, ?_⟩
  · intro i _hi j _hj
    simp [add_comm]
  · intro i _hi
    have hline :=
      realScalarQuadraticEstimateWithDataAt_of_hasSecondOrderExpansionAt
        (hExp.lineRestriction_hasSecondOrderExpansionAt (v i))
    simpa [B] using hline.quadraticQuotientEstimateWithDataAt
  · intro i _hi j _hj
    have hline :=
      realScalarQuadraticEstimateWithDataAt_of_hasSecondOrderExpansionAt
        (hExp.lineRestriction_hasSecondOrderExpansionAt (v i + v j))
    simpa [B] using hline.quadraticQuotientEstimateWithDataAt

/-- Mixed-directional quotient estimate data implies the finite slice quotient-estimate target
for the selected directions and their pairwise sums. -/
theorem MixedDirectionalQuadraticQuotientEstimateAt.directionalSliceQuotientEstimateAt
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : MixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    DirectionalSliceQuotientEstimateAt D v u x :=
  ⟨fun i _hi => h.scalarQuotientEstimateAt_lineRestriction (v i),
    fun i _hi j _hj => h.scalarQuotientEstimateAt_lineRestriction (v i + v j)⟩

/-- Polarized mixed-directional quadratic estimate data implies the finite slice-estimate target
for the selected directions and their pairwise sums. -/
theorem PolarizedMixedDirectionalQuadraticEstimateAt.directionalSliceEstimateAt
    {ι : Type*} [DecidableEq ι] {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    DirectionalSliceEstimateAt D v u x :=
  h.mixedDirectionalQuadraticEstimateAt.directionalSliceEstimateAt

/-- Polarized mixed-directional quadratic estimate data implies compatible finite slice data. -/
theorem PolarizedMixedDirectionalQuadraticEstimateAt.compatibleDirectionalSliceEstimateAt
    {ι : Type*} [DecidableEq ι] {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    CompatibleDirectionalSliceEstimateAt D v u x :=
  h.mixedDirectionalQuadraticEstimateAt.compatibleDirectionalSliceEstimateAt

/-- Polarized mixed-directional quadratic estimate data implies symmetric-compatible finite
slice data. -/
theorem PolarizedMixedDirectionalQuadraticEstimateAt.symmetricCompatibleSliceEstimateAt
    {ι : Type*} [DecidableEq ι] {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    SymmetricCompatibleDirectionalSliceEstimateAt D v u x :=
  h.mixedDirectionalQuadraticEstimateAt.symmetricCompatibleDirectionalSliceEstimateAt

/-- Polarized mixed-directional quadratic estimate data implies the finite slice quotient target
for the selected directions and their pairwise sums. -/
theorem PolarizedMixedDirectionalQuadraticEstimateAt.directionalSliceQuotientEstimateAt
    {ι : Type*} [DecidableEq ι] {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    DirectionalSliceQuotientEstimateAt D v u x :=
  h.mixedDirectionalQuadraticEstimateAt.directionalSliceQuotientEstimateAt

/-- Polarized mixed-directional quotient estimate data implies the finite slice-estimate target
for the selected directions and their pairwise sums. -/
theorem PolarizedMixedDirectionalQuadraticQuotientEstimateAt.directionalSliceEstimateAt
    {ι : Type*} [DecidableEq ι] {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    DirectionalSliceEstimateAt D v u x :=
  h.mixedDirectionalQuadraticQuotientEstimateAt.directionalSliceEstimateAt

/-- Polarized mixed-directional quotient estimate data implies compatible finite quotient-slice
data. -/
theorem
    PolarizedMixedDirectionalQuadraticQuotientEstimateAt.compatibleSliceQuotientEstimateAt
    {ι : Type*} [DecidableEq ι] {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    CompatibleDirectionalSliceQuotientEstimateAt D v u x :=
  h.mixedDirectionalQuadraticQuotientEstimateAt.compatibleDirectionalSliceQuotientEstimateAt

/-- Polarized mixed-directional quotient estimate data implies symmetric-compatible finite
quotient-slice data. -/
theorem
    PolarizedMixedDirectionalQuadraticQuotientEstimateAt.symmetricCompatibleQuotientEstimateAt
    {ι : Type*} [DecidableEq ι] {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    SymmetricCompatibleDirectionalSliceQuotientEstimateAt D v u x :=
  h.mixedDirectionalQuadraticQuotientEstimateAt.symmetricCompatibleQuotientEstimateAt

/-- Polarized mixed-directional quotient estimate data implies the finite slice quotient target
for the selected directions and their pairwise sums. -/
theorem PolarizedMixedDirectionalQuadraticQuotientEstimateAt.directionalSliceQuotientEstimateAt
    {ι : Type*} [DecidableEq ι] {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    DirectionalSliceQuotientEstimateAt D v u x :=
  h.mixedDirectionalQuadraticQuotientEstimateAt.directionalSliceQuotientEstimateAt

/-- Compatible finite slice data forgets to the existential finite slice target. -/
theorem CompatibleDirectionalSliceEstimateAt.directionalSliceEstimateAt
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : CompatibleDirectionalSliceEstimateAt D v u x) :
    DirectionalSliceEstimateAt D v u x := by
  rcases h with ⟨p, q, r, hpure, hpair⟩
  exact
    ⟨fun i hi => (hpure hi).realScalarQuadraticEstimateAt,
      fun i hi j hj => (hpair hi hj).realScalarQuadraticEstimateAt⟩

/-- Symmetric compatible finite slice data forgets to compatible finite slice data. -/
theorem SymmetricCompatibleDirectionalSliceEstimateAt.compatibleDirectionalSliceEstimateAt
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : SymmetricCompatibleDirectionalSliceEstimateAt D v u x) :
    CompatibleDirectionalSliceEstimateAt D v u x := by
  rcases h with ⟨p, q, r, _hr, hpure, hpair⟩
  exact ⟨p, q, r, hpure, hpair⟩

/-- Compatible finite slice data can be represented with symmetric pairwise-sum coefficients by
averaging the two ordered pair coefficients. -/
theorem CompatibleDirectionalSliceEstimateAt.symmetricCompatibleDirectionalSliceEstimateAt
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : CompatibleDirectionalSliceEstimateAt D v u x) :
    SymmetricCompatibleDirectionalSliceEstimateAt D v u x := by
  rcases h with ⟨p, q, r, hpure, hpair⟩
  let rsym : ι → ι → ℝ := fun i j => (r i j + r j i) / 2
  refine ⟨p, q, rsym, ?_, hpure, ?_⟩
  · intro i _hi j _hj
    simp [rsym, add_comm]
  · intro i hi j hj
    have hji :
        RealScalarQuadraticEstimateWithDataAt (lineRestriction u x (v i + v j)) 0
          (inner ℝ p (v i + v j)) (r j i) := by
      simpa [add_comm] using (hpair hj hi)
    exact (hpair hi hj).average hji

/-- Compatible finite quotient-slice data forgets to the existential finite quotient-slice
target. -/
theorem CompatibleDirectionalSliceQuotientEstimateAt.directionalSliceQuotientEstimateAt
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : CompatibleDirectionalSliceQuotientEstimateAt D v u x) :
    DirectionalSliceQuotientEstimateAt D v u x := by
  rcases h with ⟨p, q, r, hpure, hpair⟩
  exact
    ⟨fun i hi => (hpure hi).realScalarQuadraticQuotientEstimateAt,
      fun i hi j hj => (hpair hi hj).realScalarQuadraticQuotientEstimateAt⟩

/-- Symmetric compatible finite quotient-slice data forgets to compatible finite quotient-slice
data. -/
theorem
    SymmetricCompatibleDirectionalSliceQuotientEstimateAt.compatibleQuotientEstimateAt
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : SymmetricCompatibleDirectionalSliceQuotientEstimateAt D v u x) :
    CompatibleDirectionalSliceQuotientEstimateAt D v u x := by
  rcases h with ⟨p, q, r, _hr, hpure, hpair⟩
  exact ⟨p, q, r, hpure, hpair⟩

/-- Compatible finite quotient-slice data can be represented with symmetric pairwise-sum
coefficients by averaging the two ordered pair coefficients. -/
theorem
    CompatibleDirectionalSliceQuotientEstimateAt.symmetricCompatibleQuotientEstimateAt
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : CompatibleDirectionalSliceQuotientEstimateAt D v u x) :
    SymmetricCompatibleDirectionalSliceQuotientEstimateAt D v u x := by
  rcases h with ⟨p, q, r, hpure, hpair⟩
  let rsym : ι → ι → ℝ := fun i j => (r i j + r j i) / 2
  refine ⟨p, q, rsym, ?_, hpure, ?_⟩
  · intro i _hi j _hj
    simp [rsym, add_comm]
  · intro i hi j hj
    have hji :
        RealScalarQuadraticQuotientEstimateWithDataAt (lineRestriction u x (v i + v j)) 0
          (inner ℝ p (v i + v j)) (r j i) := by
      simpa [add_comm] using (hpair hj hi)
    exact (hpair hi hj).average hji

/-- Compatible finite slice data gives compatible finite quotient-slice data with the same
ambient slope and scalar quadratic coefficients. -/
theorem CompatibleDirectionalSliceEstimateAt.compatibleDirectionalSliceQuotientEstimateAt
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : CompatibleDirectionalSliceEstimateAt D v u x) :
    CompatibleDirectionalSliceQuotientEstimateAt D v u x := by
  rcases h with ⟨p, q, r, hpure, hpair⟩
  refine ⟨p, q, r, ?_, ?_⟩
  · intro i hi
    exact (hpure hi).quadraticQuotientEstimateWithDataAt
  · intro i hi j hj
    exact (hpair hi hj).quadraticQuotientEstimateWithDataAt

/-- Symmetric compatible finite slice data gives symmetric compatible finite quotient-slice data
with the same ambient slope and scalar quadratic coefficients. -/
theorem
    SymmetricCompatibleDirectionalSliceEstimateAt.symmetricCompatibleQuotientEstimateAt
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : SymmetricCompatibleDirectionalSliceEstimateAt D v u x) :
    SymmetricCompatibleDirectionalSliceQuotientEstimateAt D v u x := by
  rcases h with ⟨p, q, r, hr, hpure, hpair⟩
  refine ⟨p, q, r, hr, ?_, ?_⟩
  · intro i hi
    exact (hpure hi).quadraticQuotientEstimateWithDataAt
  · intro i hi j hj
    exact (hpair hi hj).quadraticQuotientEstimateWithDataAt

/-- Points with mixed-directional estimate data restrict to scalar estimate points on every
affine line through the base point. -/
theorem mixedDirectionalQuadraticEstimateSet_subset_lineScalarEstimateAtZero
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {w : E} :
    mixedDirectionalQuadraticEstimateSet D v u ⊆
      {x : E | (0 : ℝ) ∈ realScalarQuadraticEstimateSet (lineRestriction u x w)} := by
  intro x hx
  exact hx.realScalarQuadraticEstimateAt_lineRestriction w

/-- Points with mixed-directional quotient estimate data restrict to scalar quotient-estimate
points on every affine line through the base point. -/
theorem mixedDirectionalQuadraticQuotientEstimateSet_subset_lineScalarQuotientEstimateAtZero
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {w : E} :
    mixedDirectionalQuadraticQuotientEstimateSet D v u ⊆
      {x : E | (0 : ℝ) ∈ realScalarQuadraticQuotientEstimateSet (lineRestriction u x w)} := by
  intro x hx
  exact hx.scalarQuotientEstimateAt_lineRestriction w

/-- The mixed-directional estimate set is contained in the finite directional slice-estimate
set. -/
theorem mixedDirectionalQuadraticEstimateSet_subset_directionalSliceEstimateSet
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} :
    mixedDirectionalQuadraticEstimateSet D v u ⊆ directionalSliceEstimateSet D v u := by
  intro x hx
  exact hx.directionalSliceEstimateAt

/-- The mixed-directional estimate set is contained in the compatible finite slice-estimate set. -/
theorem mixedDirectionalQuadraticEstimateSet_subset_compatibleDirectionalSliceEstimateSet
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} :
    mixedDirectionalQuadraticEstimateSet D v u ⊆
      compatibleDirectionalSliceEstimateSet D v u := by
  intro x hx
  exact hx.compatibleDirectionalSliceEstimateAt

/-- The mixed-directional estimate set is contained in the symmetric-compatible finite
slice-estimate set. -/
theorem mixedDirectionalQuadraticEstimateSet_subset_symmetricCompatibleDirectionalSliceEstimateSet
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} :
    mixedDirectionalQuadraticEstimateSet D v u ⊆
      symmetricCompatibleDirectionalSliceEstimateSet D v u := by
  intro x hx
  exact hx.symmetricCompatibleDirectionalSliceEstimateAt

/-- The compatible finite slice-estimate set is contained in the symmetric compatible finite
slice-estimate set. -/
theorem compatibleDirectionalSliceEstimateSet_subset_symmetricCompatibleDirectionalSliceEstimateSet
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} :
    compatibleDirectionalSliceEstimateSet D v u ⊆
      symmetricCompatibleDirectionalSliceEstimateSet D v u := by
  intro x hx
  exact hx.symmetricCompatibleDirectionalSliceEstimateAt

/-- Pure directional scalar estimates plus off-diagonal pairwise-sum estimates give the bundled
finite slice target. The diagonal pair directions are supplied by rescaling the pure estimates. -/
theorem directionalSliceEstimateAt_of_pure_offDiagonal
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (hpure : ∀ ⦃i : ι⦄, i ∈ D →
      RealScalarQuadraticEstimateAt (lineRestriction u x (v i)) 0)
    (hpair : ∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → i ≠ j →
      RealScalarQuadraticEstimateAt (lineRestriction u x (v i + v j)) 0) :
    DirectionalSliceEstimateAt D v u x := by
  refine ⟨hpure, ?_⟩
  intro i hi j hj
  by_cases hij : i = j
  · subst j
    exact RealScalarQuadraticEstimateAt.lineRestriction_add_self
      (u := u) (x := x) (v := v i) (hpure hi)
  · exact hpair hi hj hij

/-- Quotient-estimate version of `directionalSliceEstimateAt_of_pure_offDiagonal`. -/
theorem directionalSliceQuotientEstimateAt_of_pure_offDiagonal
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (hpure : ∀ ⦃i : ι⦄, i ∈ D →
      RealScalarQuadraticQuotientEstimateAt (lineRestriction u x (v i)) 0)
    (hpair : ∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → i ≠ j →
      RealScalarQuadraticQuotientEstimateAt (lineRestriction u x (v i + v j)) 0) :
    DirectionalSliceQuotientEstimateAt D v u x := by
  refine ⟨hpure, ?_⟩
  intro i hi j hj
  by_cases hij : i = j
  · subst j
    exact RealScalarQuadraticQuotientEstimateAt.lineRestriction_add_self
      (u := u) (x := x) (v := v i) (hpure hi)
  · exact hpair hi hj hij

/-- The symmetric compatible finite slice-estimate set is contained in the compatible finite
slice-estimate set. -/
theorem symmetricCompatibleDirectionalSliceEstimateSet_subset_compatibleDirectionalSliceEstimateSet
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} :
    symmetricCompatibleDirectionalSliceEstimateSet D v u ⊆
      compatibleDirectionalSliceEstimateSet D v u := by
  intro x hx
  exact hx.compatibleDirectionalSliceEstimateAt

/-- The compatible finite slice-estimate set is contained in the older existential finite
slice-estimate set. -/
theorem compatibleDirectionalSliceEstimateSet_subset_directionalSliceEstimateSet
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} :
    compatibleDirectionalSliceEstimateSet D v u ⊆ directionalSliceEstimateSet D v u := by
  intro x hx
  exact hx.directionalSliceEstimateAt

/-- The mixed-directional estimate set is contained in the finite directional slice
quotient-estimate set. -/
theorem mixedDirectionalQuadraticEstimateSet_subset_directionalSliceQuotientEstimateSet
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} :
    mixedDirectionalQuadraticEstimateSet D v u ⊆ directionalSliceQuotientEstimateSet D v u := by
  intro x hx
  exact hx.directionalSliceQuotientEstimateAt

/-- The compatible finite slice-estimate set is contained in the compatible finite quotient-slice
estimate set. -/
theorem compatibleDirectionalSliceEstimateSet_subset_compatibleDirectionalSliceQuotientEstimateSet
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} :
    compatibleDirectionalSliceEstimateSet D v u ⊆
      compatibleDirectionalSliceQuotientEstimateSet D v u := by
  intro x hx
  exact hx.compatibleDirectionalSliceQuotientEstimateAt

/-- The symmetric compatible finite slice-estimate set is contained in the symmetric compatible
finite quotient-slice estimate set. -/
theorem
    symmetricCompatibleDirectionalSliceEstimateSet_subset_symmetricCompatibleQuotientSet
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} :
    symmetricCompatibleDirectionalSliceEstimateSet D v u ⊆
      symmetricCompatibleDirectionalSliceQuotientEstimateSet D v u := by
  intro x hx
  exact hx.symmetricCompatibleQuotientEstimateAt

/-- The compatible finite quotient-slice estimate set is contained in the older existential
finite quotient-slice estimate set. -/
theorem compatibleDirectionalSliceQuotientEstimateSet_subset_directionalSliceQuotientEstimateSet
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} :
    compatibleDirectionalSliceQuotientEstimateSet D v u ⊆
      directionalSliceQuotientEstimateSet D v u := by
  intro x hx
  exact hx.directionalSliceQuotientEstimateAt

/-- The compatible finite slice-estimate set is contained in the older existential finite
quotient-slice estimate set. -/
theorem compatibleDirectionalSliceEstimateSet_subset_directionalSliceQuotientEstimateSet
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} :
    compatibleDirectionalSliceEstimateSet D v u ⊆ directionalSliceQuotientEstimateSet D v u :=
  subset_trans
    compatibleDirectionalSliceEstimateSet_subset_compatibleDirectionalSliceQuotientEstimateSet
    compatibleDirectionalSliceQuotientEstimateSet_subset_directionalSliceQuotientEstimateSet

/-- The mixed-directional quotient-estimate set is contained in the finite directional
slice-estimate set. -/
theorem mixedDirectionalQuadraticQuotientEstimateSet_subset_directionalSliceEstimateSet
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} :
    mixedDirectionalQuadraticQuotientEstimateSet D v u ⊆
      directionalSliceEstimateSet D v u := by
  intro x hx
  exact hx.directionalSliceEstimateAt

/-- The mixed-directional quotient-estimate set is contained in the finite directional slice
quotient-estimate set. -/
theorem mixedDirectionalQuadraticQuotientEstimateSet_subset_directionalSliceQuotientEstimateSet
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} :
    mixedDirectionalQuadraticQuotientEstimateSet D v u ⊆
      directionalSliceQuotientEstimateSet D v u := by
  intro x hx
  exact hx.directionalSliceQuotientEstimateAt

/-- The mixed-directional quotient-estimate set is contained in the compatible finite
quotient-slice estimate set. -/
theorem
    mixedDirectionalQuadraticQuotientEstimateSet_subset_compatibleDirectionalSliceQuotientSet
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} :
    mixedDirectionalQuadraticQuotientEstimateSet D v u ⊆
      compatibleDirectionalSliceQuotientEstimateSet D v u := by
  intro x hx
  exact hx.compatibleDirectionalSliceQuotientEstimateAt

/-- The mixed-directional quotient-estimate set is contained in the symmetric-compatible finite
quotient-slice estimate set. -/
theorem
    mixedDirectionalQuadraticQuotientEstimateSet_subset_symmetricCompatibleQuotientSliceSet
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} :
    mixedDirectionalQuadraticQuotientEstimateSet D v u ⊆
      symmetricCompatibleDirectionalSliceQuotientEstimateSet D v u := by
  intro x hx
  exact hx.symmetricCompatibleQuotientEstimateAt

/-- The compatible finite quotient-slice estimate set is contained in the symmetric compatible
finite quotient-slice estimate set. -/
theorem
    compatibleDirectionalSliceQuotientSet_subset_symmetricCompatibleDirectionalSliceQuotientSet
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} :
    compatibleDirectionalSliceQuotientEstimateSet D v u ⊆
      symmetricCompatibleDirectionalSliceQuotientEstimateSet D v u := by
  intro x hx
  exact hx.symmetricCompatibleQuotientEstimateAt

/-- The symmetric compatible finite quotient-slice estimate set is contained in the compatible
finite quotient-slice estimate set. -/
theorem
    symmetricCompatibleDirectionalSliceQuotientSet_subset_compatibleDirectionalSliceQuotientSet
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} :
    symmetricCompatibleDirectionalSliceQuotientEstimateSet D v u ⊆
      compatibleDirectionalSliceQuotientEstimateSet D v u := by
  intro x hx
  exact hx.compatibleQuotientEstimateAt

/-- The polarized mixed-directional estimate set is contained in the finite directional
slice-estimate set. -/
theorem polarizedMixedDirectionalQuadraticSet_subset_directionalSliceEstimateSet
    {ι : Type*} [DecidableEq ι] {D : Finset ι} {v : ι → E} {u : E → ℝ} :
    polarizedMixedDirectionalQuadraticEstimateSet D v u ⊆
      directionalSliceEstimateSet D v u := by
  intro x hx
  exact hx.directionalSliceEstimateAt

/-- The polarized mixed-directional estimate set is contained in the finite directional slice
quotient-estimate set. -/
theorem polarizedMixedDirectionalQuadraticSet_subset_directionalSliceQuotientSet
    {ι : Type*} [DecidableEq ι] {D : Finset ι} {v : ι → E} {u : E → ℝ} :
    polarizedMixedDirectionalQuadraticEstimateSet D v u ⊆
      directionalSliceQuotientEstimateSet D v u := by
  intro x hx
  exact hx.directionalSliceQuotientEstimateAt

/-- The polarized mixed-directional estimate set is contained in the compatible finite
slice-estimate set. -/
theorem polarizedMixedDirectionalQuadraticSet_subset_compatibleDirectionalSliceEstimateSet
    {ι : Type*} [DecidableEq ι] {D : Finset ι} {v : ι → E} {u : E → ℝ} :
    polarizedMixedDirectionalQuadraticEstimateSet D v u ⊆
      compatibleDirectionalSliceEstimateSet D v u := by
  intro x hx
  exact hx.compatibleDirectionalSliceEstimateAt

/-- The polarized mixed-directional quotient estimate set is contained in the finite directional
slice-estimate set. -/
theorem polarizedMixedDirectionalQuotientSet_subset_directionalSliceEstimateSet
    {ι : Type*} [DecidableEq ι] {D : Finset ι} {v : ι → E} {u : E → ℝ} :
    polarizedMixedDirectionalQuadraticQuotientEstimateSet D v u ⊆
      directionalSliceEstimateSet D v u := by
  intro x hx
  exact hx.directionalSliceEstimateAt

/-- The polarized mixed-directional quotient estimate set is contained in the finite directional
slice quotient-estimate set. -/
theorem polarizedMixedDirectionalQuotientSet_subset_directionalSliceQuotientSet
    {ι : Type*} [DecidableEq ι] {D : Finset ι} {v : ι → E} {u : E → ℝ} :
    polarizedMixedDirectionalQuadraticQuotientEstimateSet D v u ⊆
      directionalSliceQuotientEstimateSet D v u := by
  intro x hx
  exact hx.directionalSliceQuotientEstimateAt

/-- The polarized mixed-directional quotient-estimate set is contained in the compatible finite
quotient-slice estimate set. -/
theorem polarizedMixedDirectionalQuotientSet_subset_compatibleDirectionalSliceQuotientSet
    {ι : Type*} [DecidableEq ι] {D : Finset ι} {v : ι → E} {u : E → ℝ} :
    polarizedMixedDirectionalQuadraticQuotientEstimateSet D v u ⊆
      compatibleDirectionalSliceQuotientEstimateSet D v u := by
  intro x hx
  exact hx.compatibleSliceQuotientEstimateAt

end AleksandrovDifferentiability
