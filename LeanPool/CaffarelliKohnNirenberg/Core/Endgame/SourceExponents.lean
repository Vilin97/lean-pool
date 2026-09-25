/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Parameters
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Minkowski
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays

/-!
# Source Exponents

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey


noncomputable section

namespace CKN.Core.Endgame

/-- The heat-source exponent is exactly the minimum of the force exponent
and the exponent obtained after the velocity improvement. -/
theorem heat_source_exponent_eq {q : ℝ} (hq : 5 / 2 < q) :
    stepTheta₀ (stepGamma₀ q) = min q (25 / 9 : ℝ) := by
  have hq0 : 0 < q := by linarith only [hq]
  by_cases hqle : q ≤ 25 / 9
  · have hdiv : (9 / 5 : ℝ) ≤ 5 / q := by
      rw [le_div_iff₀ hq0]
      linarith only [hqle]
    have hmin : 2 - 5 / q ≤ (1 / 5 : ℝ) := by linarith only [hdiv]
    rw [stepTheta₀, stepGamma₀, min_eq_left hmin, min_eq_left hqle]
    field_simp
    ring
  · have hdiv : 5 / q ≤ (9 / 5 : ℝ) := by
      rw [div_le_iff₀ hq0]
      linarith only [not_le.mp hqle]
    have hmin : (1 / 5 : ℝ) ≤ 2 - 5 / q := by linarith only [hdiv]
    rw [stepTheta₀, stepGamma₀, min_eq_right hmin,
      min_eq_right (le_of_not_ge hqle)]
    norm_num

/-- The derivative-source exponent may be lowered from the initial velocity
Morrey exponent on a bounded support. -/
theorem derivative_source_exponent_le (q : ℝ) :
    stepTheta₁ (stepGamma₀ q) ≤ (25 / 3 : ℝ) := by
  have hg := stepGamma₀_le_fifth q
  have hd : 0 < 1 - stepGamma₀ q := by linarith only [hg]
  rw [stepTheta₁, div_le_iff₀ hd]
  linarith only [hg]

/-- Bounded-support source norms at the paper's exponents supply precisely
the quantitative bounds required by the heat Hölder theorem. -/
theorem source_norm_bounds_at_holder_exponents
    (q R : ℝ) (KF KG : ℝ≥0∞) (hq : 5 / 2 < q) (hR : 0 < R)
    {z₀ : ParabolicPoint}
    {F : ParabolicPoint → Vec3} {G : Fin 3 → ParabolicPoint → Vec3}
    (hF : ∀ i, morreyNorm (6 / 5 : ℝ) (min q (25 / 9 : ℝ))
      (fun z => F z i) ≤ KF)
    (hG : ∀ j i, morreyNorm (6 / 5 : ℝ) (25 / 3 : ℝ)
      (fun z => G j z i) ≤ KG)
    (hsupp : ∀ j i, ∀ z ∉ parabolicCylinder z₀.1 z₀.2 R, G j z i = 0) :
    (∀ i, morreyNorm (6 / 5 : ℝ) (stepTheta₀ (stepGamma₀ q))
      (fun z => F z i) ≤ KF) ∧
    (∀ j i, morreyNorm (6 / 5 : ℝ) (stepTheta₁ (stepGamma₀ q))
      (fun z => G j z i) ≤
        ENNReal.ofReal R ^ (5 * (1 / stepTheta₁ (stepGamma₀ q) - 3 / 25)) * KG) := by
  refine ⟨?_, ?_⟩
  · simpa only [heat_source_exponent_eq hq] using hF
  · intro j i
    have hθ := stepTheta₁_gt_five (stepGamma₀_pos hq) (stepGamma₀_lt_one q)
    have hbound := morreyNorm_lower_morrey_exponent (p := (6 / 5 : ℝ))
      (q := (25 / 3 : ℝ)) (q' := stepTheta₁ (stepGamma₀ q))
      (by norm_num) (by norm_num) (by linarith only [hθ])
      (derivative_source_exponent_le q) hR (hsupp j i)
    norm_num only [show (1 / (25 / 3) : ℝ) = 3 / 25 by norm_num] at hbound
    exact hbound.trans (mul_le_mul_of_nonneg_left (hG j i) (by positivity))

/-- A symmetric ball support gives the same exponent conversion with the
explicit radius factor from a containing backward cylinder. -/
theorem source_norm_bounds_at_holder_exponents_on_ball
    (q R : ℝ) (KF KG : ℝ≥0∞) (hq : 5 / 2 < q) (hR : 0 < R)
    {z₀ : ParabolicPoint}
    {F : ParabolicPoint → Vec3} {G : Fin 3 → ParabolicPoint → Vec3}
    (hF : ∀ i, morreyNorm (6 / 5 : ℝ) (min q (25 / 9 : ℝ))
      (fun z => F z i) ≤ KF)
    (hG : ∀ j i, morreyNorm (6 / 5 : ℝ) (25 / 3 : ℝ)
      (fun z => G j z i) ≤ KG)
    (hsupp : ∀ j i, ∀ z ∉ Metric.ball z₀ R, G j z i = 0) :
    (∀ i, morreyNorm (6 / 5 : ℝ) (stepTheta₀ (stepGamma₀ q))
      (fun z => F z i) ≤ KF) ∧
    (∀ j i, morreyNorm (6 / 5 : ℝ) (stepTheta₁ (stepGamma₀ q))
      (fun z => G j z i) ≤
        ENNReal.ofReal (2 * R) ^
          (5 * (1 / stepTheta₁ (stepGamma₀ q) - 3 / 25)) * KG) := by
  apply source_norm_bounds_at_holder_exponents q (2 * R) KF KG hq (by positivity)
    (z₀ := (z₀.1, z₀.2 + R ^ 2)) hF hG
  intro j i z hz
  exact hsupp j i z (fun hmem => hz
    (metricBall_subset_parabolicCylinder_doubled z₀ hR hmem))

/-- On the unit support cylinder the change of derivative-source exponent
does not enlarge either numerical source bound. -/
theorem source_norm_bounds_at_holder_exponents_unit
    (q : ℝ) (KF KG : ℝ≥0∞) (hq : 5 / 2 < q)
    {F : ParabolicPoint → Vec3} {G : Fin 3 → ParabolicPoint → Vec3}
    (hF : ∀ i, morreyNorm (6 / 5 : ℝ) (min q (25 / 9 : ℝ))
      (fun z => F z i) ≤ KF)
    (hG : ∀ j i, morreyNorm (6 / 5 : ℝ) (25 / 3 : ℝ)
      (fun z => G j z i) ≤ KG)
    (hsupp : ∀ j i, ∀ z ∉ parabolicCylinder (0 : Vec3) 0 1, G j z i = 0) :
    (∀ i, morreyNorm (6 / 5 : ℝ) (stepTheta₀ (stepGamma₀ q))
      (fun z => F z i) ≤ KF) ∧
    (∀ j i, morreyNorm (6 / 5 : ℝ) (stepTheta₁ (stepGamma₀ q))
      (fun z => G j z i) ≤ KG) := by
  simpa only [ENNReal.ofReal_one, ENNReal.one_rpow, one_mul] using
    source_norm_bounds_at_holder_exponents q 1 KF KG hq one_pos
      (z₀ := ((0 : Vec3), (0 : ℝ))) (F := F) (G := G) hF hG hsupp

/-- Bounded-support source norms at the paper's exponents supply precisely
the exponents required by the heat Hölder theorem. -/
theorem source_norms_at_holder_exponents
    {q R : ℝ} (hq : 5 / 2 < q) (hR : 0 < R)
    {z₀ : ParabolicPoint}
    {F : ParabolicPoint → Vec3} {G : Fin 3 → ParabolicPoint → Vec3}
    (hF : ∀ i, morreyNorm (6 / 5 : ℝ) (min q (25 / 9 : ℝ))
      (fun z => F z i) < ∞)
    (hG : ∀ j i, morreyNorm (6 / 5 : ℝ) (25 / 3 : ℝ)
      (fun z => G j z i) < ∞)
    (hsupp : ∀ j i, ∀ z ∉ parabolicCylinder z₀.1 z₀.2 R, G j z i = 0) :
    (∀ i, morreyNorm (6 / 5 : ℝ) (stepTheta₀ (stepGamma₀ q))
      (fun z => F z i) < ∞) ∧
    (∀ j i, morreyNorm (6 / 5 : ℝ) (stepTheta₁ (stepGamma₀ q))
      (fun z => G j z i) < ∞) := by
  refine ⟨?_, ?_⟩
  · simpa only [heat_source_exponent_eq hq] using hF
  · intro j i
    have hθ := stepTheta₁_gt_five (stepGamma₀_pos hq) (stepGamma₀_lt_one q)
    have hbound := morreyNorm_lower_morrey_exponent (p := (6 / 5 : ℝ))
      (q := (25 / 3 : ℝ)) (q' := stepTheta₁ (stepGamma₀ q))
      (by norm_num) (by norm_num) (by linarith only [hθ])
      (derivative_source_exponent_le q) hR (hsupp j i)
    apply hbound.trans_lt
    apply ENNReal.mul_lt_top
    · exact ENNReal.rpow_lt_top_of_nonneg
        (mul_nonneg (by norm_num) (sub_nonneg.mpr
          (one_div_le_one_div_of_le (by linarith only [hθ])
            (derivative_source_exponent_le q)))) ENNReal.ofReal_ne_top
    · exact hG j i

end CKN.Core.Endgame
