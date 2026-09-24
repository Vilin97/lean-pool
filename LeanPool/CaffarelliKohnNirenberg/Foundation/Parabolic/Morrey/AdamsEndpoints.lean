/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Adams

/-!
# Adams Endpoints

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Metric
open scoped ENNReal NNReal Topology


noncomputable section

namespace CKN.Foundation.Parabolic.Morrey

private theorem ae_eq_zero_of_ball_integrals
    {f : ParabolicPoint → ℝ} (hf : AEMeasurable f volume)
    (z : ParabolicPoint)
    (hzero : ∀ {R : ℝ}, 0 < R →
      (∫⁻ w in Metric.ball z R, ENNReal.ofReal |f w|) = 0) :
    f =ᵐ[volume] 0 := by
  have hballs : ∀ n : ℕ, ∀ᵐ w ∂volume,
      w ∈ Metric.ball z ((n : ℝ) + 1) → f w = 0 := by
    intro n
    apply (ae_restrict_iff' measurableSet_ball).mp
    have hAE := (lintegral_eq_zero_iff'
      (hf.norm.ennreal_ofReal.restrict)).mp
        (hzero (R := (n : ℝ) + 1) (by positivity))
    filter_upwards [hAE] with w hw
    have hw' : |f w| = 0 := by simpa using hw
    exact abs_eq_zero.mp hw'
  have hall : ∀ᵐ w ∂volume, ∀ n : ℕ,
      w ∈ Metric.ball z ((n : ℝ) + 1) → f w = 0 :=
    ae_all_iff.mpr hballs
  filter_upwards [hall] with w hw
  obtain ⟨n, hn⟩ := exists_nat_gt (dist w z)
  exact hw n (by
    change dist w z < (n : ℝ) + 1
    exact lt_trans hn (by norm_num))

/-- A potential vanishes when its input vanishes almost everywhere. -/
theorem parabolicRieszPotential_eq_zero_of_ae_eq_zero
    {β : ℝ} {f : ParabolicPoint → ℝ} (hzero : f =ᵐ[volume] 0)
    (z : ParabolicPoint) :
    parabolicRieszPotential β f z = 0 := by
  unfold parabolicRieszPotential
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [hzero] with w hw
  simp [hw]

private theorem cylinder_integral_eq_zero_of_morreyNorm_eq_zero
    {q : ℝ} (_ : 1 ≤ q) {f : ParabolicPoint → ℝ}
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hN : morreyNorm 1 q f = 0) :
    cylinderPowerIntegral 1 f z r = 0 := by
  have hcell : morreyCell 1 q f z r ≤ morreyNorm 1 q f := by
    unfold morreyNorm
    exact le_iSup_of_le z (le_iSup_of_le ⟨r, hr⟩ le_rfl)
  have hcell0 : morreyCell 1 q f z r = 0 :=
    bot_unique (hcell.trans_eq hN)
  have hfactor : (ENNReal.ofReal r) ^ (-(5 * (1 - 1 / q) / 1)) ≠ 0 :=
    (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hr) ENNReal.ofReal_ne_top).ne'
  rw [morreyCell] at hcell0
  have hroot : (cylinderPowerIntegral 1 f z r) ^ ((1 : ℝ) / 1) = 0 :=
    (mul_eq_zero.mp hcell0).resolve_left hfactor
  simpa using hroot

/-- A zero first-index Morrey seminorm forces global almost-everywhere vanishing. -/
theorem ae_eq_zero_of_morreyNorm_eq_zero
    {q : ℝ} (hq : 1 ≤ q) {f : ParabolicPoint → ℝ}
    (hf : AEMeasurable f volume) (hN : morreyNorm 1 q f = 0) :
    f =ᵐ[volume] 0 := by
  apply ae_eq_zero_of_ball_integrals hf
  on_goal 1 => intro R hR
  on_goal 1 => let T : ℝ := (2 * R) ^ 2 / 2
  on_goal 1 =>
    have hball := metricBall_subset_parabolicCylinder
      (x := (0 : Vec3)) (t := T) (r := 2 * R) (by positivity)
  on_goal 1 =>
    have hcenter : ((0 : Vec3), T - (2 * R) ^ 2 / 2) = (0, 0) := by
      dsimp [T]
      congr 1
      ring_nf
  on_goal 1 => have hradius : (2 * R) / 2 = R := by ring_nf
  on_goal 1 => rw [hcenter, hradius] at hball
  on_goal 1 =>
    have hcyl := cylinder_integral_eq_zero_of_morreyNorm_eq_zero hq (by positivity)
      (hN := hN) (z := ((0 : Vec3), T)) (r := 2 * R)
  on_goal 1 =>
    have hcyl' : (∫⁻ w in parabolicCylinder 0 T (2 * R),
        ENNReal.ofReal |f w|) = 0 := by
      unfold cylinderPowerIntegral at hcyl
      simpa using hcyl
  exact le_antisymm ((lintegral_mono_set hball).trans_eq hcyl') bot_le

/-- The near-field geometric constant is strictly positive. -/
theorem parabolicHedbergNearConstant_pos {β : ℝ} :
    0 < parabolicHedbergNearConstant β := by
  unfold parabolicHedbergNearConstant
  have hvol : 0 < volume (parabolicCylinder 0 0 1) :=
    Integration.volume_parabolicCylinder_pos (by norm_num)
  have hfactor : 0 < ENNReal.ofReal (2 ^ 5) *
      (ENNReal.ofReal (2 ^ 5) * volume (parabolicCylinder 0 0 1)) := by
    exact ENNReal.mul_pos (by positivity)
      (ENNReal.mul_pos (by positivity) hvol.ne').ne'
  have hterm : 0 < ENNReal.ofReal
      (((2 : ℝ) ^ (Int.negSucc 0 : ℝ)) ^ β) := by
    positivity
  have hsum : ENNReal.ofReal
      (((2 : ℝ) ^ (Int.negSucc 0 : ℝ)) ^ β) ≤
      ∑' n : ℕ, ENNReal.ofReal (((2 : ℝ) ^ (Int.negSucc n : ℝ)) ^ β) :=
    ENNReal.le_tsum (f := fun n : ℕ =>
      ENNReal.ofReal (((2 : ℝ) ^ (Int.negSucc n : ℝ)) ^ β)) 0
  exact ENNReal.mul_pos hfactor.ne' (lt_of_lt_of_le hterm hsum).ne'

/-- Hedberg's pointwise estimate, including zero and infinite endpoint data. -/
theorem parabolicRieszPotential_hedberg'
    {β q : ℝ} (hβ : 0 < β) (hβ5 : β < 5) (hq : 1 ≤ q)
    (hβq : β * q < 5) {f : ParabolicPoint → ℝ}
    (hf : AEMeasurable f volume) {M : ParabolicPoint → ℝ≥0∞}
    (hM : IsParabolicMaximalMajorant f M) (z : ParabolicPoint) :
    parabolicRieszPotential β f z ≤
      (parabolicHedbergNearConstant β + parabolicTailKernelConstant β q) *
        M z ^ (1 - β * q / 5) * (morreyNorm 1 q f) ^ (β * q / 5) := by
  have hκ : 0 < β * q / 5 := by positivity
  have hlam : 0 < 1 - β * q / 5 := by
    exact sub_pos.mpr ((div_lt_one (by norm_num : (0 : ℝ) < 5)).2 hβq)
  have hC0 : parabolicHedbergNearConstant β +
      parabolicTailKernelConstant β q ≠ 0 := by
    have hpos : 0 < parabolicHedbergNearConstant β +
        parabolicTailKernelConstant β q :=
      add_pos_of_pos_of_nonneg (parabolicHedbergNearConstant_pos (β := β)) bot_le
    exact hpos.ne'
  by_cases hM0 : M z = 0
  · have hfzero : f =ᵐ[volume] 0 := ae_eq_zero_of_ball_integrals hf z (by
      intro R hR
      have hball := hM z R hR
      rw [hM0, zero_mul] at hball
      exact le_antisymm hball bot_le)
    rw [parabolicRieszPotential_eq_zero_of_ae_eq_zero hfzero z]
    simp [hM0, ENNReal.zero_rpow_of_pos hlam]
  by_cases hN0 : morreyNorm 1 q f = 0
  · have hfzero := ae_eq_zero_of_morreyNorm_eq_zero hq hf hN0
    rw [parabolicRieszPotential_eq_zero_of_ae_eq_zero hfzero z]
    simp [hN0, ENNReal.zero_rpow_of_pos hκ]
  by_cases hMtop : M z = ∞
  · have hNpow0 : (morreyNorm 1 q f) ^ (β * q / 5) ≠ 0 := by
      intro hpow
      apply hN0
      exact (ENNReal.rpow_eq_zero_iff_of_pos hκ).mp hpow
    have hRhs :
        (parabolicHedbergNearConstant β + parabolicTailKernelConstant β q) *
          M z ^ (1 - β * q / 5) * (morreyNorm 1 q f) ^ (β * q / 5) = ∞ := by
      rw [hMtop, ENNReal.top_rpow_of_pos hlam, ENNReal.mul_top hC0,
        ENNReal.top_mul hNpow0]
    exact hRhs ▸ le_top
  by_cases hNtop : morreyNorm 1 q f = ∞
  · have hMpow0 : M z ^ (1 - β * q / 5) ≠ 0 := by
      intro hpow
      apply hM0
      exact (ENNReal.rpow_eq_zero_iff_of_pos hlam).mp hpow
    have hleft : (parabolicHedbergNearConstant β +
        parabolicTailKernelConstant β q) * M z ^ (1 - β * q / 5) ≠ 0 :=
      mul_ne_zero hC0 hMpow0
    have hRhs :
        (parabolicHedbergNearConstant β + parabolicTailKernelConstant β q) *
          M z ^ (1 - β * q / 5) * (morreyNorm 1 q f) ^ (β * q / 5) = ∞ := by
      rw [hNtop, ENNReal.top_rpow_of_pos hκ, ENNReal.mul_top hleft]
    exact hRhs ▸ le_top
  exact parabolicRieszPotential_hedberg hβ hβ5 hq hβq hf hM z hM0 hMtop hN0 hNtop

end CKN.Foundation.Parabolic.Morrey
