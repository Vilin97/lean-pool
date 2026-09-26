/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Basic

/-!
# Bounded-support Morrey inclusions

This module records the change of Morrey exponent available for functions
supported in one parabolic cylinder.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Metric
open scoped ENNReal NNReal Topology


noncomputable section

namespace CKN.Foundation.Parabolic.Morrey

private lemma morreyCell_bounded_support {p q q' : ℝ} (hp : 0 < p)
    (hpq : p ≤ q) (hpq' : p ≤ q') (hq'q : q' ≤ q)
    {f : ParabolicPoint → ℝ}
    {z₀ : ParabolicPoint} {R : ℝ} (hR : 0 < R)
    (hsupp : ∀ w ∉ parabolicCylinder z₀.1 z₀.2 R, f w = 0)
    (z : ParabolicPoint) {r : ℝ} (hr : 0 < r) :
    morreyCell p q' f z r ≤
      (ENNReal.ofReal R) ^ (5 * (1 / q' - 1 / q)) *
        morreyNorm p q f := by
  let A : ℝ≥0∞ := ENNReal.ofReal r
  let B : ℝ≥0∞ := ENNReal.ofReal R
  let δ : ℝ := 5 * (1 / q' - 1 / q)
  let α : ℝ := 5 * (1 - p / q) / p
  let α' : ℝ := 5 * (1 - p / q') / p
  have hpq0 : 0 < q := lt_of_lt_of_le hp hpq
  have hpq'0 : 0 < q' := lt_of_lt_of_le hp hpq'
  have hδ : 0 ≤ δ := by
    dsimp [δ]
    exact mul_nonneg (by norm_num) (sub_nonneg.mpr
      (one_div_le_one_div_of_le hpq'0 hq'q))
  have hα' : 0 ≤ α' := by
    dsimp [α']
    exact div_nonneg (mul_nonneg (by norm_num)
      (sub_nonneg.mpr ((div_le_one hpq'0).2 hpq'))) hp.le
  have hA : A ≠ 0 := (ENNReal.ofReal_pos.mpr hr).ne'
  have hAtop : A ≠ ∞ := ENNReal.ofReal_ne_top
  have hB : B ≠ 0 := (ENNReal.ofReal_pos.mpr hR).ne'
  have hBtop : B ≠ ∞ := ENNReal.ofReal_ne_top
  have hαrel : α = α' + δ := by
    dsimp [α, α', δ]
    field_simp [hp.ne', hpq0.ne', hpq'0.ne']
    ring
  have hnorm : morreyCell p q f z₀ R ≤ morreyNorm p q f := by
    unfold morreyNorm
    exact le_iSup_of_le z₀
      (le_iSup (fun s : {s : ℝ // 0 < s} => morreyCell p q f z₀ s.1) ⟨R, hR⟩)
  by_cases hsmall : r ≤ R
  · have hArB : A ≤ B := ENNReal.ofReal_le_ofReal hsmall
    have hpow : A ^ δ ≤ B ^ δ := ENNReal.rpow_le_rpow hArB hδ
    have hcell : morreyCell p q' f z r = A ^ δ * morreyCell p q f z r := by
      unfold morreyCell
      dsimp [A, δ, α, α']
      change A ^ (-α') * (cylinderPowerIntegral p f z r) ^ (1 / p) =
        A ^ δ * (A ^ (-α) * (cylinderPowerIntegral p f z r) ^ (1 / p))
      rw [show -α' = δ + (-α) by linarith only [hαrel],
        ENNReal.rpow_add _ _ hA hAtop]
      ac_rfl
    have hnormz : morreyCell p q f z r ≤ morreyNorm p q f := by
      unfold morreyNorm
      exact le_iSup_of_le z
        (le_iSup (fun s : {s : ℝ // 0 < s} => morreyCell p q f z s.1) ⟨r, hr⟩)
    rw [hcell]
    exact (mul_le_mul_right hnormz _).trans
      (mul_le_mul_left hpow _)
  · have hlarge : R ≤ r := le_of_not_ge hsmall
    have hArB : B ≤ A := ENNReal.ofReal_le_ofReal hlarge
    have hglobal : cylinderPowerIntegral p f z r ≤
        cylinderPowerIntegral p f z₀ R := by
      have hsupport : Function.support (fun w => ENNReal.ofReal |f w| ^ p) ⊆
          parabolicCylinder z₀.1 z₀.2 R := by
        intro w hw
        by_contra hnot
        apply hw
        change ENNReal.ofReal |f w| ^ p = 0
        rw [hsupp w hnot, abs_zero, ENNReal.ofReal_zero,
          ENNReal.zero_rpow_of_pos hp]
      have htotal : (∫⁻ w, ENNReal.ofReal |f w| ^ p) =
          cylinderPowerIntegral p f z₀ R := by
        symm
        exact setLIntegral_eq_of_support_subset hsupport
      exact (lintegral_mono' Measure.restrict_le_self le_rfl).trans_eq htotal
    have hroot : (cylinderPowerIntegral p f z r) ^ (1 / p) ≤
        B ^ α * morreyNorm p q f := by
      have hroot' := ENNReal.rpow_le_rpow hglobal (one_div_nonneg.mpr hp.le)
      have hnorm' := mul_le_mul_right hnorm (B ^ α)
      have hcancel : B ^ α * B ^ (-α) = 1 := by
          rw [← ENNReal.rpow_add _ _ hB hBtop, add_neg_cancel, ENNReal.rpow_zero]
      calc
        (cylinderPowerIntegral p f z r) ^ (1 / p) ≤
            (cylinderPowerIntegral p f z₀ R) ^ (1 / p) := hroot'
        _ ≤ B ^ α * morreyNorm p q f := by
          rw [show (cylinderPowerIntegral p f z₀ R) ^ (1 / p) =
              B ^ α * (B ^ (-α) * (cylinderPowerIntegral p f z₀ R) ^ (1 / p)) by
                rw [← mul_assoc, hcancel, one_mul]]
          exact hnorm'
    have hcoef : A ^ (-α') * B ^ α ≤ B ^ δ := by
      have hratio : A ^ (-α') * B ^ α' ≤ 1 := by
        have hpow : B ^ α' ≤ A ^ α' := ENNReal.rpow_le_rpow hArB hα'
        have hcancel : A ^ (-α') * A ^ α' = 1 := by
          rw [← ENNReal.rpow_add _ _ hA hAtop, neg_add_cancel, ENNReal.rpow_zero]
        calc
          A ^ (-α') * B ^ α' ≤ A ^ (-α') * A ^ α' :=
            mul_le_mul_right hpow _
          _ = 1 := hcancel
      rw [show A ^ (-α') * B ^ α = B ^ δ *
          (A ^ (-α') * B ^ α') by
            rw [hαrel, ENNReal.rpow_add _ _ hB hBtop]
            ac_rfl]
      simpa [mul_comm] using (mul_le_mul_left hratio (B ^ δ))
    unfold morreyCell
    calc
      A ^ (-α') * (cylinderPowerIntegral p f z r) ^ (1 / p) ≤
          A ^ (-α') * (B ^ α * morreyNorm p q f) :=
        mul_le_mul_right hroot _
      _ ≤ B ^ δ * morreyNorm p q f := by
        calc
          _ = (A ^ (-α') * B ^ α) * morreyNorm p q f := by ac_rfl
          _ ≤ _ := mul_le_mul_left hcoef _

/-- A bounded-support function has the lower Morrey exponent at an explicit scale cost. -/
theorem morreyNorm_bounded_support {p q q' : ℝ} (hp : 1 ≤ p)
    (hpq : p ≤ q) (hpq' : p ≤ q') (hq'q : q' ≤ q)
    {f : ParabolicPoint → ℝ}
    {z₀ : ParabolicPoint} {R : ℝ} (hR : 0 < R)
    (hsupp : ∀ w ∉ parabolicCylinder z₀.1 z₀.2 R, f w = 0) :
    morreyNorm p q' f ≤
      (ENNReal.ofReal R) ^ (5 * (1 / q' - 1 / q)) *
        morreyNorm p q f := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  unfold morreyNorm
  refine iSup_le fun z => iSup_le fun r => ?_
  exact morreyCell_bounded_support hp0 hpq hpq' hq'q hR hsupp z r.2

end CKN.Foundation.Parabolic.Morrey
