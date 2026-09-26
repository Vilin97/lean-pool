/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.OmegaSupport
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.TruncationPolynomial
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Tests.Fixtures.ApproachZero

/-!
# Cutoff and convolution API checks

These clients exercise finiteness below an arbitrary negative cutoff and polynomial convolution
under bounds imposed only on nonzero germ products. The cutoff client uses the nonconstant
approach-zero series, so its value and support order type are genuinely omega. The convolution
boundary checks include an empty sum for a zero factor and a nonzero term at the zero cutoff.
They check these strengthened interfaces, not new definitions of series or ordinal value.
-/

open scoped NatOrdinal HahnSeries
open Berarducci HahnSeries MvPolynomial OrdinalGraded

public noncomputable section

namespace Tests

universe v w

variable {K : Type v} [Field K]

/-- The nonconstant approach-zero series has finitely many cutoffs of ordinal value at least one
below every negative real, without requiring that real to belong to the cutoff set. -/
theorem approachZero_negative_cutoff_finite {ξ : ℝ} (hξ : ξ < 0) :
    (cutoffsGE 0 approachZeroNonpositive ∩ Set.Iic ξ).Finite := by
  have hv := ordinalValue_eq_wpow_of_isPrincipal
    approachZero_isPrincipal approachZero_degree_eq_one
  apply cutoffsGE_inter_Iic_finite_of_neg approachZeroNonpositive
    (by simpa using hv) ?_ hξ
  simp [coe_approachZeroNonpositive, approachZero_supportOrderType]

/-- The original membership-based cutoff interface remains available. -/
theorem cutoff_membership_interface {δ : NatOrdinal} (p : Series K)
    (hv : ordinalValue p = ω^ (δ + 1))
    (hot : (p : K⟦ℝ⟧).supportOrderType = (ω^ (δ + 1)).val)
    {ξ : ℝ} (hξ : ξ ∈ cutoffsGE δ p) : (cutoffsGE δ p ∩ Set.Iic ξ).Finite :=
  cutoffsGE_inter_Iic_finite p hv hot hξ

/-- A zero factor needs no cutoff in the support-indexed germ convolution sum. -/
theorem zero_germ_convolution_empty (γ : ℝ) :
    germAt ((0 : K⟦ℝ⟧) * 1) γ =
      ∑ ξ ∈ (∅ : Finset ℝ), germAt (0 : K⟦ℝ⟧) ξ * germAt (1 : K⟦ℝ⟧) (γ - ξ) := by
  apply germAt_mul_of_support_subset (0 : Series K) 1 γ
  intro ξ hξ
  exact (hξ (by
    rw [Subring.coe_zero, germAt_apply, translatedTruncation_zero_input, map_zero, zero_mul])).elim

/-- At the zero cutoff the product of two units has the singleton convolution term. -/
theorem one_germ_convolution_at_zero :
    germAt ((1 : ℚ⟦ℝ⟧) * 1) 0 =
      ∑ ξ ∈ ({0} : Finset ℝ), germAt (1 : ℚ⟦ℝ⟧) ξ * germAt (1 : ℚ⟦ℝ⟧) (0 - ξ) := by
  apply germAt_mul_of_support_subset (1 : Series ℚ) 1 0
  intro ξ hξ
  by_contra hnot
  have hclosure : ξ ∉ closure (1 : ℚ⟦ℝ⟧).support := by
    simpa [HahnSeries.support_one] using hnot
  exact hξ (by rw [Subring.coe_one, germAt_eq_zero_of_not_mem_closure_support hclosure, zero_mul])

/-- The singleton boundary check is not a vacuous zero convolution. -/
theorem one_germ_convolution_term_ne_zero :
    (∑ ξ ∈ ({0} : Finset ℝ),
      germAt (1 : ℚ⟦ℝ⟧) ξ * germAt (1 : ℚ⟦ℝ⟧) (0 - ξ)) ≠ 0 := by
  have h : germAt (1 : ℚ⟦ℝ⟧) 0 = 1 := by
    rw [germAt_apply]
    change toGerm (translatedTruncation ((1 : Series ℚ) : ℚ⟦ℝ⟧) 0) = 1
    rw [translatedTruncation_zero, map_one]
  have hg : (1 : Germ ℚ) ≠ 0 := by
    intro hz
    have heq : toGerm (1 : Series ℚ) = toGerm 0 := by simpa using hz
    have hv := ordinalValue_eq_of_sub_mem_negativeMonomialIdeal
      (toGerm_eq_toGerm_iff.mp heq)
    simp [ordinalValue_one, ordinalValue_zero] at hv
  simpa only [Finset.sum_singleton, sub_zero, h, one_mul] using hg

variable {ι : Type w} {wt : ι → NatOrdinal} {x : ι → PrincipalSubring K}

/-- Bounds only at nonzero germ products suffice: the finite sum uses exactly those cutoffs. -/
theorem polynomial_convolution_from_nonzero_bounds (σ : Lifts wt x)
    (hx : IsMinimalSystem (principalGrading K) wt x) {α : NatOrdinal}
    (hinj : ∀ β < α, InjectiveAt K wt x β) {u v : Series K} {γ : ℝ}
    (hprod : ordinalValue (translatedTruncation ((u * v : Series K) : K⟦ℝ⟧) γ) < ω^ α)
    (hterm : ∀ ξ : ℝ,
      germAt (u : K⟦ℝ⟧) ξ * germAt (v : K⟦ℝ⟧) (γ - ξ) ≠ 0 →
      ordinalValue (translatedTruncation (u : K⟦ℝ⟧) ξ) < ω^ α ∧
      ordinalValue (translatedTruncation (v : K⟦ℝ⟧) (γ - ξ)) < ω^ α ∧
      DegreeLT wt (σ.pol hx α (translatedTruncation (u : K⟦ℝ⟧) ξ) *
        σ.pol hx α (translatedTruncation (v : K⟦ℝ⟧) (γ - ξ))) α) :
    ∃ S : Finset ℝ,
      (∀ ξ : ℝ, ξ ∈ S ↔
        germAt (u : K⟦ℝ⟧) ξ * germAt (v : K⟦ℝ⟧) (γ - ξ) ≠ 0) ∧
      σ.pol hx α (translatedTruncation ((u * v : Series K) : K⟦ℝ⟧) γ) =
        ∑ ξ ∈ S, σ.pol hx α (translatedTruncation (u : K⟦ℝ⟧) ξ) *
          σ.pol hx α (translatedTruncation (v : K⟦ℝ⟧) (γ - ξ)) := by
  classical
  let S := (convolutionIndex (u : K⟦ℝ⟧) (v : K⟦ℝ⟧) γ).filter fun ξ ↦
    germAt (u : K⟦ℝ⟧) ξ * germAt (v : K⟦ℝ⟧) (γ - ξ) ≠ 0
  have hS : ∀ ξ : ℝ, germAt (u : K⟦ℝ⟧) ξ * germAt (v : K⟦ℝ⟧) (γ - ξ) ≠ 0 → ξ ∈ S := by
    intro ξ hξ
    refine Finset.mem_filter.mpr ⟨?_, hξ⟩
    by_contra hnot
    rw [mem_convolutionIndex, not_and_or] at hnot
    rcases hnot with h | h
    · exact hξ (by rw [germAt_eq_zero_of_not_mem_closure_support h, zero_mul])
    · exact hξ (by rw [germAt_eq_zero_of_not_mem_closure_support h, mul_zero])
  refine ⟨S, fun ξ ↦ ⟨fun hξ ↦ (Finset.mem_filter.mp hξ).2, hS ξ⟩, ?_⟩
  exact σ.pol_translatedTruncation_mul_eq_sum_of_nonzero_terms hx hinj hS hprod
    fun ξ hξ ↦ hterm ξ (Finset.mem_filter.mp hξ).2

end Tests
