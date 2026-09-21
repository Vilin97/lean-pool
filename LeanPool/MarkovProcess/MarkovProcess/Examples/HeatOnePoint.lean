/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Examples.HeatSemigroup
import LeanPool.MarkovProcess.MarkovProcess.Kernel.OnePointConservative
import LeanPool.MarkovProcess.MarkovProcess.Killed.GluingLocal

/-!
# The compactified heat process

The heat resolvent represents the heat semigroup again
(`kernelSemigroup_heatResolvent`), so its one-point extension moves a live starting point by the
Gaussian law and never reaches the added point.  In the metric determined by the exhaustion
`x ↦ 1 / (1 + |x|)` the distance of two points is at most `2` and the distance of two live points
is at most their distance on the line, so the fourth-moment estimate of the Gaussian law gives
the local Kolmogorov criterion on the compactification
(`hasLocalKolmogorovMoments_onePointKernelSemigroup_heatResolvent`).

This assembles the regularity data from which the continuous-path process of the compactified
heat semigroup is formed (`onePointRegularHeatResolvent`), the witness that those data are
available for a genuine example.  Because the heat semigroup is conservative, the compactified
process started at a live point almost surely never reaches the added point
(`ae_exitTime_eq_top_heatResolvent`).
-/

open MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

namespace MarkovProcess

/-- **The heat resolvent represents the heat semigroup.** -/
theorem kernelSemigroup_heatResolvent : heatResolvent.kernelSemigroup = heatSemigroup :=
  isFellerKernelSemigroup_heatSemigroup.kernelSemigroup_positiveC0ContractiveResolvent

section Metric

/-- In the exhaustion metric of the line the compactification has diameter at most `2`. -/
theorem dist_le_two_heatExhaustion (z w : OnePoint ℝ) :
    letI := OnePoint.exhaustionMetricSpace heatExhaustion continuous_heatExhaustion
      heatExhaustion_pos lipschitzWith_one_heatExhaustion isCompact_heatExhaustion_superlevel
    dist z w ≤ 2 := by
  let := OnePoint.exhaustionMetricSpace heatExhaustion continuous_heatExhaustion
    heatExhaustion_pos lipschitzWith_one_heatExhaustion isCompact_heatExhaustion_superlevel
  induction z using OnePoint.rec with
  | infty =>
      induction w using OnePoint.rec with
      | infty =>
          rw [dist_self]
          norm_num
      | coe y =>
          have hdist : dist (OnePoint.infty : OnePoint ℝ) (y : OnePoint ℝ) = heatExhaustion y := by
            rw [dist_comm]
            rfl
          rw [hdist]
          exact le_trans (heatExhaustion_le_one y) (by norm_num)
  | coe x =>
      induction w using OnePoint.rec with
      | infty =>
          have hdist : dist (x : OnePoint ℝ) (OnePoint.infty : OnePoint ℝ) = heatExhaustion x :=
            rfl
          rw [hdist]
          exact le_trans (heatExhaustion_le_one x) (by norm_num)
      | coe y =>
          have hdist : dist (x : OnePoint ℝ) (y : OnePoint ℝ) =
              min (dist x y) (heatExhaustion x + heatExhaustion y) := rfl
          rw [hdist]
          refine le_trans (min_le_right _ _) ?_
          have hsum : heatExhaustion x + heatExhaustion y ≤ 1 + 1 :=
            add_le_add (heatExhaustion_le_one x) (heatExhaustion_le_one y)
          linarith only [hsum]

/-- In the exhaustion metric of the line the distance of two live points is at most their
distance on the line. -/
theorem edist_coe_coe_le_heatExhaustion (x y : ℝ) :
    letI := OnePoint.exhaustionMetricSpace heatExhaustion continuous_heatExhaustion
      heatExhaustion_pos lipschitzWith_one_heatExhaustion isCompact_heatExhaustion_superlevel
    edist (x : OnePoint ℝ) (y : OnePoint ℝ) ≤ edist x y := by
  let := OnePoint.exhaustionMetricSpace heatExhaustion continuous_heatExhaustion
    heatExhaustion_pos lipschitzWith_one_heatExhaustion isCompact_heatExhaustion_superlevel
  rw [edist_dist, edist_dist]
  exact ENNReal.ofReal_le_ofReal
    (OnePoint.exhaustionMetricSpace_dist_coe_coe_le heatExhaustion continuous_heatExhaustion
      heatExhaustion_pos lipschitzWith_one_heatExhaustion isCompact_heatExhaustion_superlevel x y)

end Metric

section Moments

/-- **The compactified heat semigroup satisfies the local Kolmogorov criterion** in the
exhaustion metric, with the Gaussian fourth moment and the diameter bound as constants. -/
theorem hasLocalKolmogorovMoments_onePointKernelSemigroup_heatResolvent :
    letI := OnePoint.exhaustionMetricSpace heatExhaustion continuous_heatExhaustion
      heatExhaustion_pos lipschitzWith_one_heatExhaustion isCompact_heatExhaustion_superlevel
    heatResolvent.onePointKernelSemigroup.HasLocalKolmogorovMoments 4 2
      gaussianFourthMoment 16 := by
  let := OnePoint.exhaustionMetricSpace heatExhaustion continuous_heatExhaustion
    heatExhaustion_pos lipschitzWith_one_heatExhaustion isCompact_heatExhaustion_superlevel
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · intro h _hh z
    induction z using OnePoint.rec with
    | infty =>
        rw [heatResolvent.onePointKernelSemigroup_absorbing h, lintegral_dirac]
        simp only [edist_self, ENNReal.rpow_ofNat, ne_eq, OfNat.ofNat_ne_zero,
          not_false_eq_true, zero_pow, coe_gaussianFourthMoment, zero_le]
    | coe x =>
        have hmass : heatSemigroup h x Set.univ = 1 := isConservative_heatSemigroup h x
        have hlaw : heatResolvent.onePointKernelSemigroup h (x : OnePoint ℝ) =
            (heatSemigroup h x).map ((↑) : ℝ → OnePoint ℝ) := by
          rw [heatResolvent.onePointKernelSemigroup_apply_coe h x, kernelSemigroup_heatResolvent,
            hmass, tsub_self, zero_smul, add_zero]
        have hmeas : Measurable fun z : OnePoint ℝ ↦ edist z (x : OnePoint ℝ) ^ (4 : ℝ) :=
          (measurable_edist_left (x := (x : OnePoint ℝ))).pow_const 4
        rw [hlaw, lintegral_map hmeas OnePoint.continuous_coe.measurable]
        refine le_trans (lintegral_mono fun y ↦ ?_) (hasKolmogorovMoments_heatSemigroup.2.2 h x)
        exact ENNReal.rpow_le_rpow (edist_coe_coe_le_heatExhaustion y x) (by norm_num)
  · intro y z
    have hdist : edist z y ≤ 2 := by
      rw [edist_dist]
      calc ENNReal.ofReal (dist z y) ≤ ENNReal.ofReal 2 :=
            ENNReal.ofReal_le_ofReal (dist_le_two_heatExhaustion z y)
        _ = 2 := by
            rw [show (2 : ℝ) = ((2 : ℝ≥0) : ℝ) by norm_num, ENNReal.ofReal_coe_nnreal]
            rfl
    calc edist z y ^ (4 : ℝ) ≤ (2 : ℝ≥0∞) ^ (4 : ℝ) :=
          ENNReal.rpow_le_rpow hdist (by norm_num)
      _ = 16 := by
          rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
          norm_num
      _ = ((16 : ℝ≥0) : ℝ≥0∞) := by norm_num

end Moments

/-- **The regularity data of the compactified heat process**: the exhaustion `1 / (1 + |x|)` and
the Kolmogorov regularity which its metric gives the compactified heat semigroup. -/
def onePointRegularHeatResolvent : heatResolvent.OnePointRegular where
  rho := heatExhaustion
  continuous_rho := continuous_heatExhaustion
  rho_pos := heatExhaustion_pos
  lipschitz_rho := lipschitzWith_one_heatExhaustion
  isCompact_superlevel := isCompact_heatExhaustion_superlevel
  kolmogorovRegular := by
    let := OnePoint.exhaustionMetricSpace heatExhaustion continuous_heatExhaustion
      heatExhaustion_pos lipschitzWith_one_heatExhaustion isCompact_heatExhaustion_superlevel
    let : CompleteSpace (OnePoint ℝ) :=
      completeSpace_of_isComplete_univ isCompact_univ.isComplete
    exact SubMarkovKernelSemigroup.KolmogorovRegular.of_hasKolmogorovMoments _
      heatResolvent.isConservative_onePointKernelSemigroup
      (hasLocalKolmogorovMoments_onePointKernelSemigroup_heatResolvent.toHasKolmogorovMoments
        heatResolvent.isConservative_onePointKernelSemigroup)

/-- **The compactified heat process almost surely never reaches the added point.**  The heat
semigroup is conservative, so the shift times its kernel resolvent of the constant observable one
is one, which is the criterion for no escape. -/
theorem ae_exitTime_eq_top_heatResolvent (x : ℝ) :
    letI := onePointRegularHeatResolvent.metricSpace
    letI := onePointRegularHeatResolvent.completeSpace
    ∀ᵐ omega ∂SubMarkovKernelSemigroup.IsConservative.continuousProcess
        heatResolvent.onePointKernelSemigroup
        heatResolvent.isConservative_onePointKernelSemigroup (x : OnePoint ℝ),
      ContinuousPath.exitTime (Set.range ((↑) : ℝ → OnePoint ℝ)) omega = ⊤ :=
  onePointRegularHeatResolvent.ae_exitTime_eq_top one_pos x (by
    rw [kernelSemigroup_heatResolvent]
    exact isConservative_heatSemigroup.ofReal_mul_kernelResolvent_one one_pos x)

end MarkovProcess
