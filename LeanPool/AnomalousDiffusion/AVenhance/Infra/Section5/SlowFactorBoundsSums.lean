/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SlowFactorBoundsShifts

/-! Finite coordinate contractions and cutoff scalars preserve the averaged
analytic envelope. -/

@[expose] public section

noncomputable section
open scoped ContDiff ENNReal
open MeasureTheory Homogenization AVenhance.FaaDiBruno
open AVenhance.Infra.Section4 AVenhance.Infra.Ergodic AVenhance.Infra.Torus
namespace AVenhance.Infra.Section5

theorem slowWord_sum {ι : Type*} (s : Finset ι) (f : ι → Vec 2 → ℝ)
    (hf : ∀ i ∈ s, ContDiff ℝ ∞ (f i)) (w : List (Fin 2)) :
    amnrSpaceWord w (∑ i ∈ s, f i) = ∑ i ∈ s, amnrSpaceWord w (f i) := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    rw [amnrSpaceWord, ih]
    funext x
    rw [fderiv_sum (fun i hi => (slowWord_smooth (hf i hi) w).differentiable (by simp) x)]
    simp only [sum_apply, amnrSpaceWord]
    rw [Finset.sum_fn]

theorem slowFactor_sum_eLpNorm_le {ι : Type*} (s : Finset ι) (f : ι → Vec 2 → ℝ)
    (hf : ∀ i ∈ s, ContDiff ℝ ∞ (f i)) {F L : ℝ}
    {p : ℝ≥0∞} (hp : 1 ≤ p) (μ : Measure (Vec 2))
    (hb : ∀ i ∈ s, ∀ w, eLpNorm (amnrSpaceWord w (f i)) p μ ≤
      ENNReal.ofReal (F * w.length.factorial * L ^ w.length)) (w : List (Fin 2)) :
    eLpNorm (amnrSpaceWord w (∑ i ∈ s, f i)) p μ ≤
      ENNReal.ofReal ((s.card : ℝ) * F * w.length.factorial * L ^ w.length) := by
  rw [slowWord_sum s f hf]
  calc
    _ ≤ ∑ i ∈ s, eLpNorm (amnrSpaceWord w (f i)) p μ := eLpNorm_sum_le hp
    _ ≤ ∑ _i ∈ s, ENNReal.ofReal (F * w.length.factorial * L ^ w.length) :=
      Finset.sum_le_sum fun i hi => hb i hi w
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

/-- A time-only cutoff with magnitude at most one does not increase any jet. -/
theorem slowFactor_cutoff_eLpNorm_le {f : Vec 2 → ℝ} {F L ξ : ℝ}
    (hξ : |ξ| ≤ 1) (p : ℝ≥0∞) (μ : Measure (Vec 2))
    (hb : ∀ w, eLpNorm (amnrSpaceWord w f) p μ ≤
      ENNReal.ofReal (F * w.length.factorial * L ^ w.length)) (w : List (Fin 2)) :
    eLpNorm (amnrSpaceWord w (ξ • f)) p μ ≤
      ENNReal.ofReal (F * w.length.factorial * L ^ w.length) := by
  rw [amnrSpaceWord_const_smul, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs]
  calc
    _ ≤ ENNReal.ofReal 1 * eLpNorm (amnrSpaceWord w f) p μ :=
      mul_le_mul_left (ENNReal.ofReal_le_ofReal hξ) _
    _ ≤ _ := by simpa using hb w

end AVenhance.Infra.Section5
