/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.GoodLambdaStopping

/-! # Good Lambda Large Scale -/

namespace Homogenization

open scoped ENNReal NNReal BigOperators Topology
open Filter MeasureTheory Set

noncomputable section

namespace CubeCalderonZygmund

/-!
# Large-scale inputs for continuous good-`λ` stopping radii

The elementary estimates here isolate the only global input in the
continuous-radius stopping construction.  A global squared mass bounds every
normalized ball energy above a fixed positive scale; consequently the usual
last-crossing construction may stop before that scale while retaining its
last-exit certificate all the way to the ambient radius.
-/

/-- A global squared mass bounds every normalized closed-ball `L²` energy at
scales at least `rho`. -/
theorem closedBallL2Energy_le_globalIntegral {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] (f : Vec d → F)
    (hf : Integrable (fun y => ‖f y‖ ^ (2 : ℕ)) volume) (x : Vec d)
    {rho s : ℝ} (hrho : 0 < rho) (hrhos : rho ≤ s) :
    closedBallL2Energy f x s ≤ ((2 * rho) ^ d)⁻¹ *
      ∫ y, ‖f y‖ ^ (2 : ℕ) ∂volume := by
  let B : Set (Vec d) := Metric.closedBall x s
  have hs : 0 < s := lt_of_lt_of_le hrho hrhos
  have hlocal : ∫ y in B, ‖f y‖ ^ (2 : ℕ) ∂volume ≤
      ∫ y, ‖f y‖ ^ (2 : ℕ) ∂volume := by
    exact MeasureTheory.integral_mono_measure (μ := volume.restrict B) (ν := volume)
      Measure.restrict_le_self (ae_of_all _ fun _ => sq_nonneg _) hf
  have hglobal_nonneg : 0 ≤ ∫ y, ‖f y‖ ^ (2 : ℕ) ∂volume :=
    MeasureTheory.integral_nonneg fun _ => sq_nonneg _
  have hbase : 2 * rho ≤ 2 * s := by nlinarith
  have hpow : (2 * rho) ^ d ≤ (2 * s) ^ d :=
    pow_le_pow_left₀ (by positivity) hbase d
  have hpow_rho_pos : 0 < (2 * rho) ^ d := by positivity
  have hpow_s_pos : 0 < (2 * s) ^ d := by positivity
  have hinv : ((2 * s) ^ d)⁻¹ ≤ ((2 * rho) ^ d)⁻¹ :=
    (inv_le_inv₀ hpow_s_pos hpow_rho_pos).2 hpow
  calc
    closedBallL2Energy f x s = ((2 * s) ^ d)⁻¹ *
        ∫ y in B, ‖f y‖ ^ (2 : ℕ) ∂volume := by rfl
    _ ≤ ((2 * s) ^ d)⁻¹ * ∫ y, ‖f y‖ ^ (2 : ℕ) ∂volume :=
      mul_le_mul_of_nonneg_left hlocal (inv_nonneg.mpr hpow_s_pos.le)
    _ ≤ ((2 * rho) ^ d)⁻¹ * ∫ y, ‖f y‖ ^ (2 : ℕ) ∂volume :=
      mul_le_mul_of_nonneg_right hinv hglobal_nonneg

/-- The good-`λ` combined energy is uniformly controlled at scales at least
`rho` by the correspondingly weighted global squared mass. -/
theorem goodLambdaCombinedEnergy_le_globalIntegral {d : ℕ} {F G : Type*}
    [NormedAddCommGroup F] [NormedAddCommGroup G]
    (f : Vec d → F) (g : Vec d → G) (ε : ℝ)
    (hf : Integrable (fun y => ‖f y‖ ^ (2 : ℕ)) volume)
    (hg : Integrable (fun y => ‖g y‖ ^ (2 : ℕ)) volume) (x : Vec d)
    {rho s : ℝ} (hrho : 0 < rho) (hrhos : rho ≤ s) :
    goodLambdaCombinedEnergy f g ε x s ≤ Real.sqrt (((2 * rho) ^ d)⁻¹ *
      ((∫ y, ‖f y‖ ^ (2 : ℕ) ∂volume) +
        (ε⁻¹) ^ (2 : ℕ) * ∫ y, ‖g y‖ ^ (2 : ℕ) ∂volume)) := by
  rw [goodLambdaCombinedEnergy]
  apply Real.sqrt_le_sqrt
  have hf_bound := closedBallL2Energy_le_globalIntegral f hf x hrho hrhos
  have hg_bound := closedBallL2Energy_le_globalIntegral g hg x hrho hrhos
  calc
    closedBallL2Energy f x s + (ε⁻¹) ^ (2 : ℕ) * closedBallL2Energy g x s ≤
        ((2 * rho) ^ d)⁻¹ * ∫ y, ‖f y‖ ^ (2 : ℕ) ∂volume +
          (ε⁻¹) ^ (2 : ℕ) *
            (((2 * rho) ^ d)⁻¹ * ∫ y, ‖g y‖ ^ (2 : ℕ) ∂volume) :=
      add_le_add hf_bound (mul_le_mul_of_nonneg_left hg_bound (sq_nonneg _))
    _ = ((2 * rho) ^ d)⁻¹ *
        ((∫ y, ‖f y‖ ^ (2 : ℕ) ∂volume) +
          (ε⁻¹) ^ (2 : ℕ) * ∫ y, ‖g y‖ ^ (2 : ℕ) ∂volume) := by ring

/-- A local last crossing before `rho` remains a last exit through `R` when
the combined energy is uniformly below the level on the large-scale interval.
This is the stopping certificate used after the global-mass estimate fixes a
large scale. -/
theorem exists_stoppingRadius_goodLambdaCombinedEnergy_of_largeScaleBound
    {d : ℕ} [NeZero d] {F G : Type*}
    [NormedAddCommGroup F] [NormedAddCommGroup G]
    (f : Vec d → F) (g : Vec d → G) (ε : ℝ)
    (hf : Integrable (fun y => ‖f y‖ ^ 2) volume)
    (hg : Integrable (fun y => ‖g y‖ ^ 2) volume) (x : Vec d)
    {level rho R : ℝ} (hrho : 0 < rho)
    (hlimit : Tendsto (fun r => goodLambdaCombinedEnergy f g ε x r) (𝓝[>] 0)
      (𝓝 (Real.sqrt (‖f x‖ ^ 2 + (ε⁻¹) ^ (2 : ℕ) * ‖g x‖ ^ 2))))
    (hpoint : level < Real.sqrt (‖f x‖ ^ 2 + (ε⁻¹) ^ (2 : ℕ) * ‖g x‖ ^ 2))
    (hrho_bound : goodLambdaCombinedEnergy f g ε x rho ≤ level)
    (hlarge : ∀ s ∈ Icc rho R, goodLambdaCombinedEnergy f g ε x s ≤ level) :
    ∃ r, 0 < r ∧ r ≤ rho ∧ goodLambdaCombinedEnergy f g ε x r = level ∧
      ∀ s ∈ Icc r R, goodLambdaCombinedEnergy f g ε x s ≤ level := by
  obtain ⟨r, hr, hrho', hstop, hlast⟩ :=
    exists_stoppingRadius_goodLambdaCombinedEnergy f g ε hf hg x hrho hlimit hpoint hrho_bound
  refine ⟨r, hr, hrho', hstop, ?_⟩
  intro s hs
  by_cases hs_rho : s ≤ rho
  · exact hlast s ⟨hs.1, hs_rho⟩
  · exact hlarge s ⟨le_of_lt (lt_of_not_ge hs_rho), hs.2⟩

end CubeCalderonZygmund

end

end Homogenization
