/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Slice
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Short-time Hölder estimates

This file records the time-integration estimates used on backward parabolic
intervals.  The right-hand side uses Mathlib's extended-valued `eLpNorm'`,
which agrees with the usual `L^p` norm when the latter is finite and keeps the
statements valid without an extra integrability hypothesis.
-/

public section

open Set MeasureTheory
open scoped ENNReal


noncomputable section

namespace CKN

/-- Backward time interval of parabolic length `r ^ 2` ending at `t`. -/
def backwardInterval (t r : ℝ) : Set ℝ := Ioc (t - r ^ 2) t

private lemma backwardInterval_subset {t r ρ : ℝ} (hr : 0 < r)
    (hrr : r ≤ ρ / 2) :
    backwardInterval t r ⊆ backwardInterval t ρ := by
  unfold backwardInterval
  apply Ioc_subset_Ioc
  · have hρ : 0 ≤ ρ := by
      have : 0 ≤ ρ / 2 := le_of_lt (lt_of_lt_of_le hr hrr)
      linarith only [this]
    have hrr' : 2 * r ≤ ρ := by
      simpa only [mul_comm] using
        ((le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hrr)
    have hrr'' : r ≤ ρ := by nlinarith only [hr, hrr']
    have hrsq : r ^ 2 ≤ ρ ^ 2 := by
      apply (sq_le_sq₀ (le_of_lt hr) hρ).2
      exact hrr''
    linarith only [hrsq]
  · exact le_rfl

private lemma time_holder_integral_bound {t r ρ a b : ℝ}
    (hr : 0 < r) (hrr : r ≤ ρ / 2)
    (hab : a.HolderConjugate b)
    {g : ℝ → ℝ}
    (hg : AEStronglyMeasurable g
      (volume.restrict (backwardInterval t ρ)))
    (_ : 0 ≤ᵐ[volume.restrict (backwardInterval t ρ)] g) :
    (∫⁻ s in backwardInterval t r,
        ENNReal.ofReal (g s) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) ≤
        (∫⁻ s in backwardInterval t ρ,
        ENNReal.ofReal (g s) ^ (3 * a / 2)) ^ (2 / (3 * a)) *
        (ENNReal.ofReal r) ^ (4 / (3 * b)) := by
  let μr : Measure ℝ := volume.restrict (backwardInterval t r)
  let μρ : Measure ℝ := volume.restrict (backwardInterval t ρ)
  let F : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (g s) ^ (3 / 2 : ℝ)
  have hgr : AEStronglyMeasurable g μr := by
    exact hg.mono_measure (MeasureTheory.Measure.restrict_mono_set volume
      (backwardInterval_subset hr hrr))
  have hF : AEMeasurable F μr := by
    exact (hgr.aemeasurable.ennreal_ofReal).pow_const (3 / 2 : ℝ)
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq μr hab hF
    (aemeasurable_const : AEMeasurable (fun _ : ℝ => (1 : ℝ≥0∞)) μr)
  have hholder' : (∫⁻ s, F s ∂μr) ≤
      (∫⁻ s, F s ^ a ∂μr) ^ (1 / a) *
        (μr Set.univ) ^ (1 / b) := by
    simpa only [Pi.mul_apply, mul_one, ENNReal.one_rpow, one_mul,
      lintegral_const] using hholder
  have hpower : (∫⁻ s, F s ∂μr) ^ (2 / 3 : ℝ) ≤
      ((∫⁻ s, F s ^ a ∂μr) ^ (1 / a) *
        (μr Set.univ) ^ (1 / b)) ^ (2 / 3 : ℝ) :=
    ENNReal.rpow_le_rpow hholder' (by norm_num)
  have hpower' : (∫⁻ s, F s ∂μr) ^ (2 / 3 : ℝ) ≤
      (∫⁻ s, F s ^ a ∂μr) ^ (2 / (3 * a)) *
        (μr Set.univ) ^ (2 / (3 * b)) := by
    calc
      _ ≤ ((∫⁻ s, F s ^ a ∂μr) ^ (1 / a) *
          (μr Set.univ) ^ (1 / b)) ^ (2 / 3 : ℝ) := hpower
      _ = (∫⁻ s, F s ^ a ∂μr) ^ (2 / (3 * a)) *
          (μr Set.univ) ^ (2 / (3 * b)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
        rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        congr 1 <;> field_simp
  have hleft : (∫⁻ s in backwardInterval t r,
      ENNReal.ofReal (g s) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) =
      (∫⁻ s, F s ∂μr) ^ (2 / 3 : ℝ) := by
    rfl
  have hFpower : ∀ s, F s ^ a = ENNReal.ofReal (g s) ^ (3 * a / 2) := by
    intro s
    rw [← ENNReal.rpow_mul]
    congr 1
    ring
  have hglobal : (∫⁻ s, F s ^ a ∂μr) ≤
      ∫⁻ s, ENNReal.ofReal (g s) ^ (3 * a / 2) ∂μρ := by
    calc
      (∫⁻ s, F s ^ a ∂μr) ≤
          ∫⁻ s, F s ^ a ∂μρ :=
        MeasureTheory.lintegral_mono'
          (MeasureTheory.Measure.restrict_mono_set volume
            (backwardInterval_subset hr hrr)) le_rfl
      _ = ∫⁻ s, ENNReal.ofReal (g s) ^ (3 * a / 2) ∂μρ := by
        apply MeasureTheory.lintegral_congr
        exact hFpower
  have hglobal' : (∫⁻ s, F s ^ a ∂μr) ^ (2 / (3 * a)) ≤
      (∫⁻ s, ENNReal.ofReal (g s) ^ (3 * a / 2) ∂μρ) ^
        (2 / (3 * a)) :=
    ENNReal.rpow_le_rpow hglobal (by
      have ha : 0 < a := hab.pos
      positivity)
  have hmeasure : μr Set.univ = ENNReal.ofReal (r ^ 2) := by
    simp [μr, backwardInterval, Real.volume_Ioc]
  have hrpow : (μr Set.univ) ^ (2 / (3 * b)) =
      (ENNReal.ofReal r) ^ (2 * (2 / (3 * b))) := by
    rw [hmeasure, ENNReal.ofReal_pow (le_of_lt hr) 2]
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    congr 1
  rw [hleft] at *
  calc
    (∫⁻ s, F s ∂μr) ^ (2 / 3 : ℝ) ≤
        (∫⁻ s, F s ^ a ∂μr) ^ (2 / (3 * a)) *
          (μr Set.univ) ^ (2 / (3 * b)) := hpower'
    _ ≤ (∫⁻ s, ENNReal.ofReal (g s) ^ (3 * a / 2) ∂μρ) ^
          (2 / (3 * a)) * (μr Set.univ) ^ (2 / (3 * b)) := by
      gcongr
    _ = (∫⁻ s in backwardInterval t ρ,
          ENNReal.ofReal (g s) ^ (3 * a / 2)) ^ (2 / (3 * a)) *
      (ENNReal.ofReal r) ^ (4 / (3 * b)) := by
      rw [hrpow]
      simp only [μρ]
      congr 1
      ring_nf

private lemma lintegral_ofReal_rpow_eq_enorm_rpow {μ : Measure ℝ}
    {g : ℝ → ℝ} (hgn : 0 ≤ᵐ[μ] g) (p : ℝ) :
    (∫⁻ s, ENNReal.ofReal (g s) ^ p ∂μ) =
      ∫⁻ s, ‖g s‖ₑ ^ p ∂μ := by
  apply MeasureTheory.lintegral_congr_ae
  filter_upwards [hgn] with s hs
  rw [Real.enorm_eq_ofReal hs]

/-- Hölder's inequality on a short backward interval, in the two forms used
in the pressure estimates. -/
theorem time_holder {t₀ r ρ : ℝ} (hr : 0 < r) (hrr : r ≤ ρ / 2)
    {g : ℝ → ℝ}
    (hg : AEStronglyMeasurable g
      (volume.restrict (Ioc (t₀ - ρ ^ 2) t₀)))
    (hgn : 0 ≤ᵐ[volume.restrict (Ioc (t₀ - ρ ^ 2) t₀)] g) :
    (∫⁻ s in Ioc (t₀ - r ^ 2) t₀,
        ENNReal.ofReal (g s) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) ≤
        (ENNReal.ofReal r) ^ (1 / 3 : ℝ) *
          eLpNorm' g 2 (volume.restrict (Ioc (t₀ - ρ ^ 2) t₀)) ∧
      (∫⁻ s in Ioc (t₀ - r ^ 2) t₀,
        ENNReal.ofReal (g s) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) ≤
        eLpNorm' g (3 / 2 : ℝ)
          (volume.restrict (Ioc (t₀ - ρ ^ 2) t₀)) := by
  have hfirst := time_holder_integral_bound (t := t₀) (r := r) (ρ := ρ)
    (a := (4 / 3 : ℝ)) (b := 4) hr hrr
    (by
      rw [Real.holderConjugate_iff]
      constructor <;> norm_num)
    hg hgn
  have hsecond :
      (∫⁻ s in Ioc (t₀ - r ^ 2) t₀,
          ENNReal.ofReal (g s) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) ≤
        (∫⁻ s in Ioc (t₀ - ρ ^ 2) t₀,
          ENNReal.ofReal (g s) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
    apply ENNReal.rpow_le_rpow
    · apply MeasureTheory.lintegral_mono'
        (MeasureTheory.Measure.restrict_mono_set volume (by
          exact backwardInterval_subset hr hrr))
      exact le_rfl
    · norm_num
  have hnorm₂ := lintegral_ofReal_rpow_eq_enorm_rpow hgn (2 : ℝ)
  have hnorm₃₂ := lintegral_ofReal_rpow_eq_enorm_rpow hgn (3 / 2 : ℝ)
  constructor
  · calc
      (∫⁻ s in Ioc (t₀ - r ^ 2) t₀,
          ENNReal.ofReal (g s) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) ≤
      (∫⁻ s in Ioc (t₀ - ρ ^ 2) t₀,
            ENNReal.ofReal (g s) ^ (3 * (4 / 3 : ℝ) / 2)) ^
              (2 / (3 * (4 / 3 : ℝ))) *
            (ENNReal.ofReal r) ^ (4 / (3 * 4 : ℝ)) := hfirst
      _ = (ENNReal.ofReal r) ^ (1 / 3 : ℝ) *
          eLpNorm' g 2 (volume.restrict (Ioc (t₀ - ρ ^ 2) t₀)) := by
        rw [show 3 * (4 / 3 : ℝ) / 2 = 2 by norm_num,
          show 2 / (3 * (4 / 3 : ℝ)) = (1 / 2 : ℝ) by norm_num,
          show 4 / (3 * 4 : ℝ) = (1 / 3 : ℝ) by norm_num]
        rw [hnorm₂]
        simp only [eLpNorm'_eq_lintegral_enorm]
        exact mul_comm _ _
  · calc
      (∫⁻ s in Ioc (t₀ - r ^ 2) t₀,
          ENNReal.ofReal (g s) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) ≤
          (∫⁻ s in Ioc (t₀ - ρ ^ 2) t₀,
            ENNReal.ofReal (g s) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := hsecond
      _ = eLpNorm' g (3 / 2 : ℝ)
          (volume.restrict (Ioc (t₀ - ρ ^ 2) t₀)) := by
        rw [hnorm₃₂]
        simp only [eLpNorm'_eq_lintegral_enorm]
        congr 1
        ring_nf

/-- Hölder's inequality on a short backward interval with an arbitrary
exponent `q ≥ 3/2`. -/
theorem time_holder_q {t₀ r ρ q : ℝ} (hr : 0 < r) (hrr : r ≤ ρ / 2)
    (hq : 3 / 2 ≤ q)
    {g : ℝ → ℝ}
    (hg : AEStronglyMeasurable g
      (volume.restrict (Ioc (t₀ - ρ ^ 2) t₀)))
    (hgn : 0 ≤ᵐ[volume.restrict (Ioc (t₀ - ρ ^ 2) t₀)] g) :
    (∫⁻ s in Ioc (t₀ - r ^ 2) t₀,
        ENNReal.ofReal (g s) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) ≤
      (ENNReal.ofReal r) ^ (2 * (2 / 3 - 1 / q)) *
        eLpNorm' g q (volume.restrict (Ioc (t₀ - ρ ^ 2) t₀)) := by
  by_cases hqeq : q = 3 / 2
  · subst q
    have h := (time_holder hr hrr hg hgn).2
    have hexp : 2 * (2 / 3 - 1 / (3 / 2 : ℝ)) = 0 := by norm_num
    rw [hexp, ENNReal.rpow_zero, one_mul]
    exact h
  · have hqgt : 3 / 2 < q := lt_of_le_of_ne hq (Ne.symm hqeq)
    have hqpos : 0 < q := by linarith only [hqgt]
    let a : ℝ := 2 * q / 3
    let b : ℝ := 2 * q / (2 * q - 3)
    have hden : 2 * q - 3 ≠ 0 := by linarith only [hqgt]
    have hab : a.HolderConjugate b := by
      rw [Real.holderConjugate_iff]
      constructor
      · dsimp [a]
        linarith only [hqgt]
      · dsimp [a, b]
        field_simp [hqpos.ne', hden]
        ring_nf
    have h := time_holder_integral_bound (t := t₀) (r := r) (ρ := ρ)
      (a := a) (b := b) hr hrr hab hg hgn
    have hnormq := lintegral_ofReal_rpow_eq_enorm_rpow hgn q
    calc
      (∫⁻ s in Ioc (t₀ - r ^ 2) t₀,
          ENNReal.ofReal (g s) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) ≤
          (∫⁻ s in Ioc (t₀ - ρ ^ 2) t₀,
            ENNReal.ofReal (g s) ^ (3 * a / 2)) ^ (2 / (3 * a)) *
            (ENNReal.ofReal r) ^ (4 / (3 * b)) := h
      _ = (ENNReal.ofReal r) ^ (2 * (2 / 3 - 1 / q)) *
          eLpNorm' g q (volume.restrict (Ioc (t₀ - ρ ^ 2) t₀)) := by
        have haexp : 3 * a / 2 = q := by
          dsimp [a]
          ring_nf
        have hroot : 2 / (3 * a) = 1 / q := by
          dsimp [a]
          field_simp [hqpos.ne']
        have hradius : 4 / (3 * b) = 2 * (2 / 3 - 1 / q) := by
          dsimp [b]
          field_simp [hqpos.ne', hden]
          ring_nf
        rw [haexp, hroot, hradius, hnormq]
        simp only [eLpNorm'_eq_lintegral_enorm]
        exact mul_comm _ _

end CKN
