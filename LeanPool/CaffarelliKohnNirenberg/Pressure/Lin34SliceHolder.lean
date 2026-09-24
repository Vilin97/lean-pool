/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsUnconditionalConstants

/-!
# Lin34 Slice Holder

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-!
# The Hölder steps of Proposition `prop:lin34`

Proposition `prop:lin34` of `paper/ckn.tex` turns a bound for an `L¹` integral
over a spatial ball into a bound for an `L^{3/2}` integral (display
`eq:lin34-pointwise`). The step is Hölder's inequality on the ball, with the
volume `(4π/3) ρ³` of the ball producing the prefactor. This file isolates that
analytic step.

* `lin34_ball_integral_le_rpow_three_halves` bounds `∫ g` over `vec3Ball x₀ ρ`
  by `(4π/3)^{1/3} ρ` times the `(2/3)`-power of the `L^{3/2}` integral of `g`.
-/

/-- The total mass of the measure restricted to a Euclidean ball:
`(volume.restrict (vec3Ball x₀ ρ)) Set.univ = ofReal ((4π/3) ρ³)`. This is the
volume of the ball, as computed in `pressure_volume_ball`. -/
private lemma volume_restrict_vec3Ball_univ {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ) :
    (volume.restrict (vec3Ball x₀ ρ)) Set.univ =
      ENNReal.ofReal ((4 * Real.pi / 3) * ρ ^ (3 : ℕ)) := by
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
  exact pressure_volume_ball hρ

/-- The `(1/3)`-power of the total mass of a Euclidean ball is
`(4π/3)^{1/3} ρ`. -/
private lemma volume_restrict_vec3Ball_toReal_one_third {x₀ : Vec3} {ρ : ℝ}
    (hρ : 0 < ρ) :
    ((volume.restrict (vec3Ball x₀ ρ)) Set.univ).toReal ^ (1 / 3 : ℝ) =
      (4 * Real.pi / 3) ^ (1 / 3 : ℝ) * ρ := by
  rw [volume_restrict_vec3Ball_univ hρ,
    ENNReal.toReal_ofReal (by positivity),
    Real.mul_rpow (by positivity) (pow_nonneg hρ.le 3),
    ← Real.rpow_natCast_mul hρ.le 3 (1 / 3 : ℝ),
    show ((3 : ℕ) : ℝ) * (1 / 3) = 1 by norm_num, Real.rpow_one]

/-- Hölder's inequality on a finite measure space, with exponents `2/3` and
`1/3`: the `L¹` integral of a nonnegative function is bounded by the `(1/3)`-power
of the total mass times the `(2/3)`-power of its `L^{3/2}` integral. -/
private lemma integral_le_volume_rpow_three_halves {μ : Measure Vec3}
    [IsFiniteMeasure μ] {g : Vec3 → ℝ}
    (hg : AEMeasurable g μ) (hg0 : ∀ y, 0 ≤ g y)
    (hXfin : ∫⁻ y, ENNReal.ofReal (g y ^ (3 / 2 : ℝ)) ∂μ < ⊤) :
    ∫ y, g y ∂μ ≤
      (μ Set.univ).toReal ^ (1 / 3 : ℝ) *
        (∫ y, g y ^ (3 / 2 : ℝ) ∂μ) ^ (2 / 3 : ℝ) := by
  have hmul : AEMeasurable (fun y => g y ^ (3 / 2 : ℝ)) μ := hg.pow_const (3 / 2)
  have hF : AEMeasurable (fun y => ENNReal.ofReal (g y ^ (3 / 2 : ℝ))) μ :=
    hmul.ennreal_ofReal
  have hOne : AEMeasurable (fun _ : Vec3 => (1 : ℝ≥0∞)) μ := aemeasurable_const
  have hHolder := ENNReal.lintegral_mul_norm_pow_le hF hOne
    (show (0 : ℝ) ≤ 2 / 3 by norm_num) (show (0 : ℝ) ≤ 1 / 3 by norm_num)
    (show (2 : ℝ) / 3 + 1 / 3 = 1 by norm_num)
  have hLHS : ∫⁻ y, ENNReal.ofReal (g y ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) *
        (1 : ℝ≥0∞) ^ (1 / 3 : ℝ) ∂μ = ∫⁻ y, ENNReal.ofReal (g y) ∂μ := by
    apply lintegral_congr
    intro y
    rw [ENNReal.one_rpow, mul_one,
      ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (hg0 y) (3 / 2))
        (show (0 : ℝ) ≤ 2 / 3 by norm_num),
      ← Real.rpow_mul (hg0 y), show (3 : ℝ) / 2 * (2 / 3) = 1 by norm_num,
      Real.rpow_one]
  rw [hLHS, lintegral_one] at hHolder
  have hRfin : (∫⁻ y, ENNReal.ofReal (g y ^ (3 / 2 : ℝ)) ∂μ) ^ (2 / 3 : ℝ) *
        (μ Set.univ) ^ (1 / 3 : ℝ) ≠ ⊤ :=
    (ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hXfin.ne)
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        (IsFiniteMeasure.measure_univ_lt_top.ne))).ne
  have htoReal := ENNReal.toReal_mono hRfin hHolder
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow] at htoReal
  rw [← integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hg0)
        hg.aestronglyMeasurable,
      ← integral_eq_lintegral_of_nonneg_ae
        (Eventually.of_forall (fun y => Real.rpow_nonneg (hg0 y) (3 / 2)))
        hmul.aestronglyMeasurable] at htoReal
  rw [mul_comm] at htoReal
  exact htoReal

/-- The first Hölder step of `prop:lin34` (display `eq:lin34-pointwise`): for a
nonnegative `g` with integrable `g^{3/2}` on the ball `vec3Ball x₀ ρ`, the `L¹`
integral of `g` over the ball is bounded by `(4π/3)^{1/3} ρ` times the
`(2/3)`-power of the `L^{3/2}` integral of `g`. -/
theorem lin34_ball_integral_le_rpow_three_halves
    {g : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hg : AEMeasurable g (volume.restrict (vec3Ball x₀ ρ)))
    (hg0 : ∀ y, 0 ≤ g y)
    (hint : Integrable (fun y => g y ^ (3 / 2 : ℝ))
      (volume.restrict (vec3Ball x₀ ρ))) :
    ∫ y in vec3Ball x₀ ρ, g y ≤
      (4 * Real.pi / 3) ^ (1 / 3 : ℝ) * ρ *
        (∫ y in vec3Ball x₀ ρ, g y ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
  have htop : volume (vec3Ball x₀ ρ) < ⊤ := by
    rw [pressure_volume_ball hρ]
    exact ENNReal.ofReal_lt_top
  have : IsFiniteMeasure (volume.restrict (vec3Ball x₀ ρ)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]; exact htop⟩
  have hXfin : ∫⁻ y, ENNReal.ofReal (g y ^ (3 / 2 : ℝ))
      ∂(volume.restrict (vec3Ball x₀ ρ)) < ⊤ := by
    have hne := (lintegral_ofReal_ne_top_iff_integrable
      (f := fun y => g y ^ (3 / 2 : ℝ)) hint.aestronglyMeasurable
      (Eventually.of_forall (fun y => Real.rpow_nonneg (hg0 y) (3 / 2)))).mpr hint
    exact lt_top_iff_ne_top.mpr hne
  have hmain := integral_le_volume_rpow_three_halves
    (μ := volume.restrict (vec3Ball x₀ ρ)) hg hg0 hXfin
  rw [volume_restrict_vec3Ball_toReal_one_third (x₀ := x₀) hρ] at hmain
  exact hmain

end CKN
