/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.PotentialFiniteness
public import LeanPool.CaffarelliKohnNirenberg.Core.HeatPotential.MorreySources
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Minkowski

/-!
# Morrey cell estimates for the first velocity-improvement round

The first round of the velocity improvement of `prop:bootstrap`
starts from `u ∈ M^{3,25/3}` and must place the heat-slot source in
`M^{6/5,25/11}` and the derivative-slot source in `M^{3,25/6}`.  Both slots
are produced from a bounded multiplier applied to a field whose Morrey norm
is known on a metric ball, so the estimates below are stated for abstract
exponents: a lowering step for the pair of exponents, and the local
integrability that a finite Morrey norm supplies.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Metric
open scoped ENNReal NNReal
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

noncomputable section

namespace CKN.Core.Step4

/-- Lowering both Morrey exponents of a field supported in a parabolic
cylinder keeps the seminorm finite: the integrability exponent drops from
`P₀` to `P` on the bounded cells, and the Morrey exponent drops from `θ₀` to
`θ` because the field vanishes outside the cylinder. -/
theorem morreyNorm_lt_top_of_lower_exponents
    {P P₀ θ θ₀ : ℝ} {B : Set ParabolicPoint}
    {z₀ : ParabolicPoint} {R : ℝ} {g : ParabolicPoint → ℝ}
    (hP : 1 ≤ P) (hPP₀ : P ≤ P₀) (hP₀θ₀ : P₀ ≤ θ₀)
    (hPθ : P ≤ θ) (hθθ₀ : θ ≤ θ₀) (hR : 0 < R)
    (hB : B ⊆ parabolicCylinder z₀.1 z₀.2 R)
    (hAE : AEMeasurable g volume) (hzero : ∀ w ∉ B, g w = 0)
    (hN : morreyNorm P₀ θ₀ g < ∞) :
    morreyNorm P θ g < ∞ := by
  have hlowP := morreyNorm_lower_integrability (p' := P) (p := P₀)
    (q := θ₀) hP hPP₀ hP₀θ₀ hAE
  have hlowPN : morreyNorm P θ₀ g < ∞ := hlowP.trans_lt (ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg
      (sub_nonneg.mpr (one_div_le_one_div_of_le
        (lt_of_lt_of_le zero_lt_one hP) hPP₀))
      Integration.volume_parabolicCylinder_lt_top.ne) hN)
  have hsupp : ∀ w ∉ parabolicCylinder z₀.1 z₀.2 R, g w = 0 := by
    intro w hw
    exact hzero w (fun hBw => hw (hB hBw))
  have hle := morreyNorm_lower_morrey_exponent
    (p := P) (q := θ₀) (q' := θ) hP
      (hPP₀.trans hP₀θ₀) hPθ hθθ₀ hR hsupp
  exact hle.trans_lt (ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5)
        (sub_nonneg.mpr (one_div_le_one_div_of_le
          (lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hP) hPθ) hθθ₀)))
      ENNReal.ofReal_ne_top) hlowPN)

/-- A field with finite metric-ball Morrey seminorm on a parabolic ball is
integrable there: the integrability exponent may be lowered to one, and the
resulting Morrey bound controls the integral over the ball. -/
theorem integrableOn_ball_of_morreyBallNorm
    {P τ r : ℝ} {z : ParabolicPoint} {f : ParabolicPoint → ℝ}
    (hP : 1 ≤ P) (hPτ : P ≤ τ) (hr : 0 < r)
    (hf : AEMeasurable f (volume.restrict (Metric.ball z r)))
    (hN : morreyBallNorm P τ ((Metric.ball z r).indicator f) < ∞) :
    IntegrableOn f (Metric.ball z r) := by
  have hfi : AEMeasurable ((Metric.ball z r).indicator f) volume :=
    (aemeasurable_indicator_iff Metric.isOpen_ball.measurableSet).mpr hf
  have hc := (morreyNorm_le_morreyBallNorm (by linarith only [hP]) hPτ _).trans_lt hN
  have hl := morreyNorm_lower_integrability (p' := (1 : ℝ)) (by norm_num) hP hPτ hfi
  have hfinite : morreyNorm 1 τ ((Metric.ball z r).indicator f) < ∞ :=
    hl.trans_lt (ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg
        (by simpa only [div_one] using
          sub_nonneg.mpr (one_div_le_one_div_of_le zero_lt_one hP))
        Integration.volume_parabolicCylinder_lt_top.ne) hc)
  have hi := CKN.Core.Endgame.source_power_integral_lt_top (P := (1 : ℝ)) (by norm_num)
    (R := 2 * r) (z₀ := (z.1, z.2 + r ^ 2)) (by positivity) hfi hfinite
    (fun w hw => indicator_of_notMem
      (fun hm => hw (metricBall_subset_parabolicCylinder_doubled z hr hm)) f)
  simp only [ENNReal.rpow_one] at hi
  have hi' : Integrable ((Metric.ball z r).indicator f) volume := by
    have ht := CKN.Core.HeatPotential.integrableOn_of_abs_integrable
      (S := Set.univ) hfi
      (by simpa only [Measure.restrict_univ] using hi)
    simpa only [IntegrableOn, Measure.restrict_univ] using ht
  exact (integrable_indicator_iff Metric.isOpen_ball.measurableSet).mp hi'

end CKN.Core.Step4
