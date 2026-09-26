/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.NumericalInterior
public import Mathlib.Tactic

/-! # Numerical Capacity -/

@[expose] public section

namespace BeyondBethe

/-!
# Exact feasibility and interior mixing for capacity certificates

These auxiliary lemmas record the feasibility-recovery argument for a generic
capacity routine.  The final algorithm uses the explicit sparse witnesses in
`NumericalWitness` and therefore no longer invokes such a routine, but the
lemmas remain useful independent checks: affine mixing preserves the mass and
moment equalities, creates an explicit coordinate floor, and loses only a
controlled fraction of the entropy objective range.
-/

/-- Feasibility of a coefficient distribution for the entropy capacity
certificate. -/
def IsCapacityDistribution
    {κ σ : Type*} [Fintype κ]
    (θ : κ → ℝ) (E : κ → σ → ℕ) (α : σ → ℝ) : Prop :=
  IsProbabilityVector θ ∧ ∀ j, exponentMoment θ E j = α j

/-- Coordinatewise affine interpolation of two coefficient distributions. -/
def distributionSegment
    {κ : Type*} (t : ℝ) (θ φ : κ → ℝ) : κ → ℝ :=
  fun e ↦ (1 - t) * θ e + t * φ e

/-- Exact mass and moment constraints are preserved by rational affine
mixing. -/
theorem distributionSegment_isCapacityDistribution
    {κ σ : Type*} [Fintype κ]
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {θ φ : κ → ℝ} {E : κ → σ → ℕ} {α : σ → ℝ}
    (hθ : IsCapacityDistribution θ E α)
    (hφ : IsCapacityDistribution φ E α) :
    IsCapacityDistribution (distributionSegment t θ φ) E α := by
  constructor
  · constructor
    · intro e
      exact add_nonneg
        (mul_nonneg (sub_nonneg.mpr ht1) (hθ.1.nonnegative e))
        (mul_nonneg ht0 (hφ.1.nonnegative e))
    · simp_rw [distributionSegment, Finset.sum_add_distrib,
        ← Finset.mul_sum, hθ.1.sum_eq_one, hφ.1.sum_eq_one]
      ring
  · intro j
    rw [exponentMoment]
    simp_rw [distributionSegment, add_mul, Finset.sum_add_distrib,
      mul_assoc, ← Finset.mul_sum]
    rw [← exponentMoment, ← exponentMoment, hθ.2 j, hφ.2 j]
    ring

theorem capacityCoordinate_eq
    {c x : ℝ} (hc : 0 < c) :
    x * Real.log (c / x) = x * Real.log c + Real.negMulLog x := by
  by_cases hx0 : x = 0
  · simp [hx0]
  · rw [Real.log_div hc.ne' hx0, Real.negMulLog_def]
    ring

/-- Concavity of the entropy capacity objective along a nonnegative segment. -/
theorem entropyCapacityCertificate_segment_lower
    {κ : Type*} [Fintype κ]
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {θ φ c : κ → ℝ}
    (hθ : ∀ e, 0 ≤ θ e) (hφ : ∀ e, 0 ≤ φ e)
    (hc : ∀ e, 0 < c e) :
    (1 - t) * entropyCapacityCertificate θ c +
        t * entropyCapacityCertificate φ c ≤
      entropyCapacityCertificate (distributionSegment t θ φ) c := by
  simp only [entropyCapacityCertificate]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro e _
  rw [capacityCoordinate_eq (hc e),
    capacityCoordinate_eq (hc e),
    capacityCoordinate_eq (hc e)]
  have hgap := negMulLog_segment_gap_nonneg ht0 ht1 (hθ e) (hφ e)
  dsimp only [distributionSegment] at hgap ⊢
  linarith

/-- Mixing toward a point with coordinate floor `ρ` creates floor `tρ`. -/
theorem distributionSegment_coordinate_floor
    {κ : Type*} {t ρ : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {θ φ : κ → ℝ} (hθ : ∀ e, 0 ≤ θ e) (hφ : ∀ e, ρ ≤ φ e) :
    ∀ e, t * ρ ≤ distributionSegment t θ φ e := by
  intro e
  dsimp only [distributionSegment]
  have hfirst : 0 ≤ (1 - t) * θ e :=
    mul_nonneg (sub_nonneg.mpr ht1) (hθ e)
  have hsecond := mul_le_mul_of_nonneg_left (hφ e) ht0
  linarith

/-- The objective loss under interior mixing is at most the mixing weight
times the objective range between the two endpoints. -/
theorem entropyCapacityCertificate_sub_segment_le
    {κ : Type*} [Fintype κ]
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {θ φ c : κ → ℝ}
    (hθ : ∀ e, 0 ≤ θ e) (hφ : ∀ e, 0 ≤ φ e)
    (hc : ∀ e, 0 < c e) :
    entropyCapacityCertificate θ c -
        entropyCapacityCertificate (distributionSegment t θ φ) c ≤
      t * (entropyCapacityCertificate θ c -
        entropyCapacityCertificate φ c) := by
  have hconc := entropyCapacityCertificate_segment_lower ht0 ht1 hθ hφ hc
  linarith

end BeyondBethe
