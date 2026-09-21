/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch04.PartitionAverageConstants
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceColorClassMoments
import LeanPool.CoarseGraining.Homogenization.Probability.IndependentSums.MomentCalculus

/-!
# Real-moment bounds for source descendant sums

This internal assembly layer combines real-exponent Rosenthal bounds on
source scale-color classes into a bound over all descendants.
-/

namespace Homogenization.Book.Ch04

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

/-- Source-local centered descendants satisfy the real-exponent uniform
Rosenthal bound after aggregation over all scale-color classes. -/
theorem integral_abs_finsetSum_rpow_rpow_inv_le_rosenthal_uniform_descendantsAtScale_of_sourceUnitRangeDependentLaw
    {d : ℕ} {Q : TriadicCube d} {k : ℤ}
    {P : SourceCoeffLaw d} [IsProbabilityMeasure P] {p K : ℝ}
    (hP : SourceUnitRangeDependentLaw P)
    (hp : 2 ≤ p) (hK_nonneg : 0 ≤ K)
    (X : TriadicCube d → Source.Coarse.Carrier d → ℝ)
    (hX_local :
      ∀ R ∈ descendantsAtScale Q k,
        IsSourceLocalRandomVariable (cubeSet R) (measurableSet_cubeSet R) (X R))
    (hLp_int :
      ∀ R ∈ descendantsAtScale Q k, Integrable (fun a => |X R a| ^ p) P)
    (hXmean :
      ∀ R ∈ descendantsAtScale Q k, ∫ a, X R a ∂P = 0)
    (hK :
      ∀ R ∈ descendantsAtScale Q k,
        (∫ a, |X R a| ^ p ∂P) ^ p⁻¹ ≤ K) :
    (∫ a, |∑ R ∈ descendantsAtScale Q k, X R a| ^ p ∂P) ^ p⁻¹ ≤
      rosenthalDescendantsAtScaleRpowLpConst d k p *
          ((descendantsAtScale Q k).card : ℝ) ^ p⁻¹ * K +
        rosenthalDescendantsAtScaleRpowSqrtConst d k p *
          Real.sqrt ((descendantsAtScale Q k).card : ℝ) * K := by
  let colors : Finset (ScaleColor d k) :=
    (descendantsAtScale Q k).image (cubeScaleColor k)
  let Y : ScaleColor d k → Source.Coarse.Carrier d → ℝ :=
    fun c a => ∑ R ∈ descendantsAtScaleScaleColorClass Q k c, X R a
  have hp_one : 1 ≤ p := le_trans (by norm_num) hp
  have hY_meas : ∀ c ∈ colors, Measurable (Y c) := by
    intro c hc
    simpa [Y] using
      (Finset.measurable_sum (descendantsAtScaleScaleColorClass Q k c)
        (fun R hR =>
          (hX_local R (mem_descendantsAtScaleScaleColorClass_iff.mp hR).1).measurable))
  have hY_int :
      ∀ c ∈ colors, Integrable (fun a => |Y c a| ^ p) P := by
    intro c hc
    simpa [Y] using
      (_root_.Homogenization.IndependentSums.integrable_abs_finsetSum_rpow
        (μ := P) (f := X) (s := descendantsAtScaleScaleColorClass Q k c) hp_one
        (fun R hR =>
          (hX_local R (mem_descendantsAtScaleScaleColorClass_iff.mp hR).1).measurable)
        (fun R hR => hLp_int R (mem_descendantsAtScaleScaleColorClass_iff.mp hR).1))
  have hY :
      ∀ c ∈ colors,
        (∫ a, |Y c a| ^ p ∂P) ^ p⁻¹ ≤
          2 * p * (((descendantsAtScaleScaleColorClass Q k c).card : ℝ) ^ p⁻¹ * K) +
            4 * rosenthalBennettIntegralConst *
              (Real.sqrt p *
                (Real.sqrt ((descendantsAtScaleScaleColorClass Q k c).card : ℝ) * K)) := by
    intro c hc
    simpa [Y] using
      (integral_abs_finsetSum_rpow_rpow_inv_le_rosenthal_uniform_descendantsAtScaleScaleColorClass_of_sourceUnitRangeDependentLaw
        (Q := Q) (k := k) (c := c) (P := P) hP hp hK_nonneg X
        (fun R hR => hX_local R (mem_descendantsAtScaleScaleColorClass_iff.mp hR).1)
        (fun R hR => hLp_int R (mem_descendantsAtScaleScaleColorClass_iff.mp hR).1)
        (fun R hR => hXmean R (mem_descendantsAtScaleScaleColorClass_iff.mp hR).1)
        (fun R hR => hK R (mem_descendantsAtScaleScaleColorClass_iff.mp hR).1))
  have hsum :
      (∫ a, |∑ c ∈ colors, Y c a| ^ p ∂P) ^ p⁻¹ ≤
        ∑ c ∈ colors, (∫ a, |Y c a| ^ p ∂P) ^ p⁻¹ := by
    exact _root_.Homogenization.IndependentSums.integral_abs_finsetSum_rpow_rpow_inv_le_sum
      (μ := P) hp_one hY_meas hY_int
  have hsum_eq :
      (fun a => ∑ c ∈ colors, Y c a) =
        fun a => ∑ R ∈ descendantsAtScale Q k, X R a := by
    funext a
    calc
      ∑ c ∈ colors, Y c a =
          ∑ c ∈ colors, ∑ R ∈ descendantsAtScaleScaleColorClass Q k c, X R a := by
            refine Finset.sum_congr rfl fun c hc => ?_
            simp [Y]
      _ = ∑ R ∈ colors.biUnion (descendantsAtScaleScaleColorClass Q k), X R a := by
            symm
            exact Finset.sum_biUnion fun c hc c' hc' hne =>
              disjoint_descendantsAtScaleScaleColorClass_of_ne Q k hne
      _ = ∑ R ∈ descendantsAtScale Q k, X R a := by
            rw [show colors.biUnion (descendantsAtScaleScaleColorClass Q k) =
              descendantsAtScale Q k by
              simpa [colors] using descendantsAtScale_eq_biUnion_image_cubeScaleColor Q k]
  have hsum_card_eq :
      ∑ c ∈ colors, ((descendantsAtScaleScaleColorClass Q k c).card : ℝ) =
        ((descendantsAtScale Q k).card : ℝ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast (card_descendantsAtScale_eq_sum_card_scaleColorClass_image Q k).symm
  have hcolors_card_le :
      (colors.card : ℝ) ≤ (((scaleColorPeriod k) ^ d : ℕ) : ℝ) := by
    exact_mod_cast (card_image_cubeScaleColor_descendantsAtScale_le Q k)
  have hexp_nonneg : 0 ≤ 1 - p⁻¹ := by
    have hpinv_le_one : p⁻¹ ≤ 1 := by
      exact inv_le_one_of_one_le₀ hp_one
    linarith
  have hcolors_card_rpow_le :
      (colors.card : ℝ) ^ (1 - p⁻¹) ≤
        (((scaleColorPeriod k) ^ d : ℕ) : ℝ) ^ (1 - p⁻¹) := by
    exact Real.rpow_le_rpow (by positivity) hcolors_card_le hexp_nonneg
  have hsum_rpow_le :
      ∑ c ∈ colors, ((descendantsAtScaleScaleColorClass Q k c).card : ℝ) ^ p⁻¹ ≤
        (((scaleColorPeriod k) ^ d : ℕ) : ℝ) ^ (1 - p⁻¹) *
          ((descendantsAtScale Q k).card : ℝ) ^ p⁻¹ := by
    have hbase :=
      _root_.Homogenization.IndependentSums.sum_rpow_inv_le_card_rpow_mul_rpow_sum
        (s := colors) (p := p)
        (f := fun c => ((descendantsAtScaleScaleColorClass Q k c).card : ℝ))
        hp_one (by
          intro c hc
          positivity)
    rw [hsum_card_eq] at hbase
    exact hbase.trans (mul_le_mul_of_nonneg_right hcolors_card_rpow_le (by positivity))
  have hsqrt_sum_le :
      ∑ c ∈ colors, Real.sqrt ((descendantsAtScaleScaleColorClass Q k c).card : ℝ) ≤
        Real.sqrt (((scaleColorPeriod k) ^ d : ℕ) : ℝ) *
          Real.sqrt ((descendantsAtScale Q k).card : ℝ) := by
    have hbase :
        ∑ c ∈ colors, Real.sqrt ((descendantsAtScaleScaleColorClass Q k c).card : ℝ) ≤
          Real.sqrt (colors.card : ℝ) *
            Real.sqrt ((descendantsAtScale Q k).card : ℝ) := by
      simpa [hsum_card_eq] using
        (Real.sum_sqrt_mul_sqrt_le
          (s := colors) (f := fun _ => (1 : ℝ))
          (g := fun c => ((descendantsAtScaleScaleColorClass Q k c).card : ℝ))
          (hf := fun c => by positivity) (hg := fun c => by positivity))
    exact hbase.trans
      (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hcolors_card_le) (by positivity))
  have hA_sum :
      ∑ c ∈ colors,
          2 * p * (((descendantsAtScaleScaleColorClass Q k c).card : ℝ) ^ p⁻¹ * K) ≤
        rosenthalDescendantsAtScaleRpowLpConst d k p *
          ((descendantsAtScale Q k).card : ℝ) ^ p⁻¹ * K := by
    calc
      ∑ c ∈ colors,
          2 * p * (((descendantsAtScaleScaleColorClass Q k c).card : ℝ) ^ p⁻¹ * K) =
          (2 * p * K) *
            ∑ c ∈ colors, ((descendantsAtScaleScaleColorClass Q k c).card : ℝ) ^ p⁻¹ := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun c hc => ?_
              ring
      _ ≤ 2 * p *
            ((((scaleColorPeriod k) ^ d : ℕ) : ℝ) ^ (1 - p⁻¹) *
              ((descendantsAtScale Q k).card : ℝ) ^ p⁻¹) * K := by
              have hmul := mul_le_mul_of_nonneg_left hsum_rpow_le (by positivity : 0 ≤ 2 * p * K)
              simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
      _ = rosenthalDescendantsAtScaleRpowLpConst d k p *
            ((descendantsAtScale Q k).card : ℝ) ^ p⁻¹ * K := by
              rw [rosenthalDescendantsAtScaleRpowLpConst]
              ring_nf
  have hB_sum :
      ∑ c ∈ colors,
          4 * rosenthalBennettIntegralConst *
            (Real.sqrt p *
              (Real.sqrt ((descendantsAtScaleScaleColorClass Q k c).card : ℝ) * K)) ≤
        rosenthalDescendantsAtScaleRpowSqrtConst d k p *
          Real.sqrt ((descendantsAtScale Q k).card : ℝ) * K := by
    have hRB_nonneg : 0 ≤ rosenthalBennettIntegralConst := by
      dsimp [rosenthalBennettIntegralConst, IndependentSums.rosenthalBennettIntegralConst]
      positivity
    calc
      ∑ c ∈ colors,
          4 * rosenthalBennettIntegralConst *
            (Real.sqrt p *
              (Real.sqrt ((descendantsAtScaleScaleColorClass Q k c).card : ℝ) * K)) =
          (4 * rosenthalBennettIntegralConst * Real.sqrt p * K) *
            ∑ c ∈ colors, Real.sqrt ((descendantsAtScaleScaleColorClass Q k c).card : ℝ) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun c hc => ?_
              ring
      _ ≤ 4 * rosenthalBennettIntegralConst *
            (Real.sqrt p *
              ((Real.sqrt ((((scaleColorPeriod k) ^ d : ℕ) : ℝ)) *
                Real.sqrt ((descendantsAtScale Q k).card : ℝ)) * K)) := by
              have hmul := mul_le_mul_of_nonneg_left hsqrt_sum_le
                (by positivity : 0 ≤ 4 * rosenthalBennettIntegralConst * Real.sqrt p * K)
              simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
      _ = rosenthalDescendantsAtScaleRpowSqrtConst d k p *
            Real.sqrt ((descendantsAtScale Q k).card : ℝ) * K := by
              simp [rosenthalDescendantsAtScaleRpowSqrtConst]
              ring
  calc
    (∫ a, |∑ R ∈ descendantsAtScale Q k, X R a| ^ p ∂P) ^ p⁻¹ =
        (∫ a, |∑ c ∈ colors, Y c a| ^ p ∂P) ^ p⁻¹ := by
          congr 1
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun a => by
            have hpoint := congrArg (fun F : Source.Coarse.Carrier d → ℝ => |F a| ^ p) hsum_eq
            simpa using hpoint.symm
    _ ≤ ∑ c ∈ colors, (∫ a, |Y c a| ^ p ∂P) ^ p⁻¹ := hsum
    _ ≤ ∑ c ∈ colors,
          (2 * p * (((descendantsAtScaleScaleColorClass Q k c).card : ℝ) ^ p⁻¹ * K) +
            4 * rosenthalBennettIntegralConst *
              (Real.sqrt p *
                (Real.sqrt ((descendantsAtScaleScaleColorClass Q k c).card : ℝ) * K))) := by
          exact Finset.sum_le_sum fun c hc => hY c hc
    _ = (∑ c ∈ colors,
          2 * p * (((descendantsAtScaleScaleColorClass Q k c).card : ℝ) ^ p⁻¹ * K)) +
        (∑ c ∈ colors,
          4 * rosenthalBennettIntegralConst *
            (Real.sqrt p *
              (Real.sqrt ((descendantsAtScaleScaleColorClass Q k c).card : ℝ) * K))) := by
          rw [Finset.sum_add_distrib]
    _ ≤ rosenthalDescendantsAtScaleRpowLpConst d k p *
          ((descendantsAtScale Q k).card : ℝ) ^ p⁻¹ * K +
        rosenthalDescendantsAtScaleRpowSqrtConst d k p *
          Real.sqrt ((descendantsAtScale Q k).card : ℝ) * K :=
      add_le_add hA_sum hB_sum

end

end Homogenization.Book.Ch04
