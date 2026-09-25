/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceColorClassIndependence
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceMeasurability
public import LeanPool.CoarseGraining.Homogenization.Probability.IndependentSums.Rosenthal.Corollaries

/-!
# Real-moment bounds on one source scale-color class

This file assembles source locality and source P2 into the independent-sum
input required by the real-exponent Rosenthal corollary, for one scale-color
class of descendants.
-/

@[expose] public section

namespace Homogenization.Book.Ch04

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

/-- Color-class assembly lemma: source-local centered summands on one
descendant scale-color class satisfy the uniform real-exponent Rosenthal
bound under source unit-range dependence. -/
theorem integral_abs_finsetSum_rpow_rpow_inv_le_rosenthal_uniform_descendantsAtScaleScaleColorClass_of_sourceUnitRangeDependentLaw
    {d : ℕ} {Q : TriadicCube d} {k : ℤ} {c : ScaleColor d k}
    {P : SourceCoeffLaw d} [IsProbabilityMeasure P] {p K : ℝ}
    (hP : SourceUnitRangeDependentLaw P) (hp : 2 ≤ p) (hK_nonneg : 0 ≤ K)
    (X : TriadicCube d → Source.Coarse.Carrier d → ℝ)
    (hX_local :
      ∀ R ∈ descendantsAtScaleScaleColorClass Q k c,
        IsSourceLocalRandomVariable (cubeSet R) (measurableSet_cubeSet R) (X R))
    (hLp_int :
      ∀ R ∈ descendantsAtScaleScaleColorClass Q k c,
        Integrable (fun a => |X R a| ^ p) P)
    (hXmean :
      ∀ R ∈ descendantsAtScaleScaleColorClass Q k c, ∫ a, X R a ∂P = 0)
    (hK :
      ∀ R ∈ descendantsAtScaleScaleColorClass Q k c,
        (∫ a, |X R a| ^ p ∂P) ^ p⁻¹ ≤ K) :
    (∫ a, |∑ R ∈ descendantsAtScaleScaleColorClass Q k c, X R a| ^ p ∂P) ^ p⁻¹ ≤
      2 * p * (((descendantsAtScaleScaleColorClass Q k c).card : ℝ) ^ p⁻¹ * K) +
        4 * _root_.Homogenization.IndependentSums.rosenthalBennettIntegralConst *
          (Real.sqrt p * (Real.sqrt ((descendantsAtScaleScaleColorClass Q k c).card : ℝ) * K)) := by
  let S : Finset (TriadicCube d) := descendantsAtScaleScaleColorClass Q k c
  by_cases hS : S.Nonempty
  · let Y : {R : TriadicCube d // R ∈ S} → Source.Coarse.Carrier d → ℝ :=
      fun R => X R.1
    have h_indep : iIndepFun Y P := by
      exact iIndepFun_descendantsAtScaleScaleColorClass_of_sourceUnitRangeDependentLaw
        (Q := Q) (k := k) (c := c) (P := P) hP
        (fun R => hX_local R.1 R.2)
    have h_meas : ∀ R, Measurable (Y R) := by
      intro R
      exact (hX_local R.1 R.2).measurable
    have hLp_intY : ∀ R ∈ S.attach, Integrable (fun a => |Y R a| ^ p) P := by
      intro R _
      exact hLp_int R.1 R.2
    have hXmeanY : ∀ R ∈ S.attach, ∫ a, Y R a ∂P = 0 := by
      intro R _
      exact hXmean R.1 R.2
    have hKY : ∀ R ∈ S.attach, (∫ a, |Y R a| ^ p ∂P) ^ p⁻¹ ≤ K := by
      intro R _
      exact hK R.1 R.2
    have hS_attach : S.attach.Nonempty := by
      simpa using hS
    have hsum_eq :
        (fun a => ∑ R ∈ S.attach, Y R a) = fun a => ∑ R ∈ S, X R a := by
      funext a
      simpa [Y] using (Finset.sum_attach (s := S) (f := fun R => X R a))
    have hRosenthal :=
      _root_.Homogenization.IndependentSums.integral_abs_finsetSum_rpow_rpow_inv_le_rosenthal_uniform_polynomial_of_iIndepFun_of_integral_eq_zero
        (μ := P) (X := Y) (s := S.attach) (p := p) (K := K)
        hS_attach hp hK_nonneg h_indep h_meas hLp_intY hXmeanY hKY
    change
      (∫ a, |(fun a => ∑ R ∈ S.attach, Y R a) a| ^ p ∂P) ^ p⁻¹ ≤ _ at hRosenthal
    rw [hsum_eq] at hRosenthal
    simpa [S] using hRosenthal
  · have hS_empty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    have hp_pos : 0 < p := by linarith
    have hp_inv_pos : 0 < p⁻¹ := inv_pos.mpr hp_pos
    simp [S, hS_empty, Real.zero_rpow (ne_of_gt hp_pos),
      Real.zero_rpow (ne_of_gt hp_inv_pos)]

end

end Homogenization.Book.Ch04
