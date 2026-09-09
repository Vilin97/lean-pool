/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanCutoffCurlBound
import LeanPool.NavierStokesAndEuler.Euler.LpSmoothApproximation
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! The ordinary three-dimensional H¹ product estimate. The homogeneous
L⁶ inequality is extended from compact fields by genuine cutoff limits;
the L⁴ bound and product estimate therefore require no support hypothesis. -/

@[expose] public section


noncomputable section

namespace EulerOrdinarySobolev

open MeasureTheory Filter EulerSmoothLimit EulerLpTranslation EulerMeanCutoffCurl
open scoped ContDiff Topology ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem eLpNorm_six_le (f : Space → V) (hf : ContDiff ℝ ∞ f)
    (hL : MemLp f 2 volume) (hD : MemLp (fderiv ℝ f) 2 volume) :
    eLpNorm f 6 volume ≤ (sobolevConstant : ℝ≥0∞)*eLpNorm (fderiv ℝ f) 2 volume := by
  have hd (n : ℕ) : eLpNorm (fderiv ℝ (cutoffField f n)) 2 volume =
      ENNReal.ofReal ‖cutoffDerivativeLp f hf n‖ := by
    rw [ofReal_norm,Lp.enorm_def]
    exact (eLpNorm_congr_ae (cutoffDerivativeLp_ae f hf n)).symm
  have hb (n : ℕ) : eLpNorm (cutoffField f n) 6 volume ≤
      (sobolevConstant : ℝ≥0∞)*ENNReal.ofReal ‖cutoffDerivativeLp f hf n‖ := by
    rw [← hd]
    exact eLpNorm_le_eLpNorm_fderiv_of_eq_inner (volume : Measure Space)
      ((cutoffField_smooth f hf n).of_le (by simp)) (cutoffField_compact f n)
      (p := 2) (p' := 6) (by norm_num) (by simp [Space]) (by norm_num [Space])
  have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (cutoffDerivativeLp_tendsto f hf hL hD).norm
  have hc : Tendsto
      (fun n => (sobolevConstant : ℝ≥0∞)*ENNReal.ofReal ‖cutoffDerivativeLp f hf n‖)
      atTop (𝓝 ((sobolevConstant : ℝ≥0∞)*ENNReal.ofReal ‖hD.toLp (fderiv ℝ f)‖)) :=
    (ENNReal.continuous_const_mul (by
        simp : (sobolevConstant : ℝ≥0∞) ≠ ⊤)).continuousAt.tendsto.comp ht
  calc
    _ ≤ atTop.liminf (fun n => eLpNorm (cutoffField f n) 6 volume) :=
      Lp.eLpNorm_lim_le_liminf_eLpNorm
        (fun n => (cutoffField_smooth f hf n).continuous.aestronglyMeasurable) f
        (Eventually.of_forall (cutoffField_tendsto f))
    _ ≤ atTop.liminf
        (fun n => (sobolevConstant : ℝ≥0∞)*ENNReal.ofReal ‖cutoffDerivativeLp f hf n‖) :=
      liminf_le_liminf (Eventually.of_forall hb)
    _ = (sobolevConstant : ℝ≥0∞)*ENNReal.ofReal ‖hD.toLp (fderiv ℝ f)‖ := hc.liminf_eq
    _ = _ := by rw [ofReal_norm,Lp.enorm_toLp]

theorem memLp_six (f : Space → V) (hf : ContDiff ℝ ∞ f)
    (hL : MemLp f 2 volume) (hD : MemLp (fderiv ℝ f) 2 volume) : MemLp f 6 volume :=
  ⟨hf.continuous.aestronglyMeasurable,(eLpNorm_six_le f hf hL hD).trans_lt (by finiteness)⟩

theorem norm_six_le (f : Space → V) (hf : ContDiff ℝ ∞ f)
    (hL : MemLp f 2 volume) (hD : MemLp (fderiv ℝ f) 2 volume) :
    (eLpNorm f 6 volume).toReal ≤ (sobolevConstant : ℝ)*(eLpNorm (fderiv ℝ f) 2 volume).toReal := by
  have h := ENNReal.toReal_mono (by finiteness) (eLpNorm_six_le f hf hL hD)
  simpa only [ENNReal.toReal_mul,ENNReal.coe_toReal] using h

section Interpolation

variable {E : Type*} [NormedAddCommGroup E]

theorem cube_memLp {f : Space → E} (h6 : MemLp f 6 volume) :
    MemLp (fun x => ‖f x‖^3) 2 volume := by
  have h := h6.norm_rpow_div (3 : ℝ≥0∞)
  have he : (6 : ℝ≥0∞)/3=2 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_div]
  rw [he] at h
  norm_num at h
  exact h

theorem cube_norm {f : Space → E} (h6 : MemLp f 6 volume) :
    lpNorm (fun x => ‖f x‖^3) 2 volume=(lpNorm f 6 volume)^3 := by
  have he := eLpNorm_norm_rpow (μ := (volume : Measure Space)) (p := 2) f (q := 3) (by norm_num)
  norm_num at he
  rw [← toReal_eLpNorm (cube_memLp h6).aestronglyMeasurable,he,ENNReal.toReal_pow,
    toReal_eLpNorm h6.aestronglyMeasurable]

private theorem square_domination (a z : ℝ) (ha : 0 < a) (hz : 0 ≤ z) :
    z^2 ≤ a*z+a⁻¹*z^3 := by
  have h : a*z^2 ≤ a^2*z+z^3 := by
    nlinarith [mul_nonneg hz (sq_nonneg (z-a))]
  have he : a*z+a⁻¹*z^3=(a^2*z+z^3)/a := by field_simp
  rw [he]
  apply (le_div_iff₀ ha).mpr
  nlinarith

theorem square_memLp {f : Space → E} (h2 : MemLp f 2 volume) (h6 : MemLp f 6 volume) :
    MemLp (fun x => ‖f x‖^2) 2 volume := by
  apply (h2.norm.add (cube_memLp h6)).of_le (h2.aestronglyMeasurable.norm.pow 2)
  filter_upwards with x
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have h := square_domination 1 ‖f x‖ (by norm_num) (norm_nonneg _)
  simpa only [one_mul,inv_one,Pi.add_apply,Pi.pow_apply,Real.norm_eq_abs,
    abs_of_nonneg (add_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) 3))] using h

theorem square_norm_scaled {f : Space → E} (h2 : MemLp f 2 volume) (h6 : MemLp f 6 volume)
    (a : ℝ) (ha : 0 < a) :
    lpNorm (fun x => ‖f x‖^2) 2 volume ≤ a*lpNorm f 2 volume+a⁻¹*(lpNorm f 6 volume)^3 := by
  have hA := h2.norm.const_smul a
  have hB := (cube_memLp h6).const_smul a⁻¹
  have hp : lpNorm (fun x => ‖f x‖^2) 2 volume ≤
      lpNorm (a • (fun x => ‖f x‖)+a⁻¹ • (fun x => ‖f x‖^3)) 2 volume := by
    apply lpNorm_mono_real (hA.add hB)
    intro x
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact square_domination a ‖f x‖ ha (norm_nonneg _)
  apply hp.trans
  have hn := lpNorm_add_le hA (g := a⁻¹ • (fun x => ‖f x‖^3)) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  simpa only [lpNorm_const_smul,coe_nnnorm,Real.norm_eq_abs,abs_of_pos ha,
    abs_of_pos (inv_pos.mpr ha),lpNorm_norm h2.aestronglyMeasurable,cube_norm h6] using hn

theorem square_norm_le_two {f : Space → E} (h2 : MemLp f 2 volume) (h6 : MemLp f 6 volume)
    (a : ℝ) (ha : 0 ≤ a) (h2a : lpNorm f 2 volume ≤ a) (h6a : lpNorm f 6 volume ≤ a) :
    lpNorm (fun x => ‖f x‖^2) 2 volume ≤ 2*a^2 := by
  rcases ha.eq_or_lt with rfl | ha
  · have h20 : lpNorm f 2 volume=0 := le_antisymm h2a lpNorm_nonneg
    have h60 : lpNorm f 6 volume=0 := le_antisymm h6a lpNorm_nonneg
    simpa only [h20,h60,mul_zero,zero_pow (by decide : 3 ≠ 0),add_zero,
      zero_pow (by decide : 2 ≠ 0)] using square_norm_scaled h2 h6 1 zero_lt_one
  · have h := square_norm_scaled h2 h6 a ha
    have hpow := pow_le_pow_left₀ (show 0 ≤ lpNorm f 6 volume from lpNorm_nonneg) h6a 3
    apply h.trans
    calc
      _ ≤ a*a+a⁻¹*a^3 := add_le_add
        (mul_le_mul_of_nonneg_left h2a ha.le)
        (mul_le_mul_of_nonneg_left hpow (inv_nonneg.mpr ha.le))
      _ = _ := by field_simp; ring

theorem memLp_four {f : Space → E} (h2 : MemLp f 2 volume) (h6 : MemLp f 6 volume) :
    MemLp f 4 volume := by
  have h := (memLp_norm_rpow_iff (p := (4 : ℝ≥0∞)) (q := (2 : ℝ≥0∞))
    h2.aestronglyMeasurable (by norm_num) (by norm_num)).mp
  have he : (4 : ℝ≥0∞)/2=2 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_div]
  rw [he] at h
  norm_num at h
  exact h (square_memLp h2 h6)

theorem norm_four_sq {f : Space → E} (h2 : MemLp f 2 volume) (h6 : MemLp f 6 volume) :
    (lpNorm f 4 volume)^2=lpNorm (fun x => ‖f x‖^2) 2 volume := by
  have he := eLpNorm_norm_rpow (μ := (volume : Measure Space)) (p := 2) f (q := 2) (by norm_num)
  norm_num at he
  rw [← toReal_eLpNorm (square_memLp h2 h6).aestronglyMeasurable,he,ENNReal.toReal_pow,
    toReal_eLpNorm (memLp_four h2 h6).aestronglyMeasurable]

theorem norm_four_le_two {f : Space → E} (h2 : MemLp f 2 volume) (h6 : MemLp f 6 volume)
    (a : ℝ) (ha : 0 ≤ a) (h2a : lpNorm f 2 volume ≤ a) (h6a : lpNorm f 6 volume ≤ a) :
    lpNorm f 4 volume ≤ 2*a := by
  have h := square_norm_le_two h2 h6 a ha h2a h6a
  rw [← norm_four_sq h2 h6] at h
  nlinarith [show 0 ≤ lpNorm f 4 volume from lpNorm_nonneg]

end Interpolation

theorem smooth_four_bound (f : Space → V) (hf : ContDiff ℝ ∞ f)
    (hL : MemLp f 2 volume) (hD : MemLp (fderiv ℝ f) 2 volume) :
    MemLp f 4 volume ∧ lpNorm f 4 volume ≤
      2*(lpNorm f 2 volume+(sobolevConstant : ℝ)*lpNorm (fderiv ℝ f) 2 volume) := by
  have h6 := memLp_six f hf hL hD
  have h6b : lpNorm f 6 volume ≤ (sobolevConstant : ℝ)*lpNorm (fderiv ℝ f) 2 volume := by
    simpa only [toReal_eLpNorm hf.continuous.aestronglyMeasurable,
      toReal_eLpNorm hD.aestronglyMeasurable] using norm_six_le f hf hL hD
  refine ⟨memLp_four hL h6,norm_four_le_two hL h6 _
    (add_nonneg lpNorm_nonneg (mul_nonneg sobolevConstant.coe_nonneg lpNorm_nonneg)) ?_ ?_⟩
  · exact le_add_of_nonneg_right (mul_nonneg sobolevConstant.coe_nonneg lpNorm_nonneg)
  · exact h6b.trans (le_add_of_nonneg_left lpNorm_nonneg)

theorem smooth_product_h1 (f : Space → ℝ) (g : Space → V)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfL : MemLp f 2 volume) (hgL : MemLp g 2 volume)
    (hfD : MemLp (fderiv ℝ f) 2 volume) (hgD : MemLp (fderiv ℝ g) 2 volume) :
    MemLp (fun x => f x • g x) 2 volume ∧
      lpNorm (fun x => f x • g x) 2 volume ≤
        4*(lpNorm f 2 volume+(sobolevConstant : ℝ)*lpNorm (fderiv ℝ f) 2 volume) *
          (lpNorm g 2 volume+(sobolevConstant : ℝ)*lpNorm (fderiv ℝ g) 2 volume) := by
  let : ENNReal.HolderTriple 4 4 2 := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_add,ENNReal.toReal_inv]⟩
  have h4f := smooth_four_bound f hf hfL hfD
  have h4g := smooth_four_bound g hg hgL hgD
  refine ⟨h4g.1.smul h4f.1,?_⟩
  calc
    _ ≤ lpNorm (fun x => ‖f x‖*‖g x‖) 2 volume := by
      apply lpNorm_mono_real (h4g.1.norm.mul' h4f.1.norm)
      intro x
      exact (norm_smul (f x) (g x)).le
    _ ≤ lpNorm f 4 volume*lpNorm g 4 volume := lpNorm_norm_mul_le h4f.1 h4g.1
    _ ≤ (2*(lpNorm f 2 volume+(sobolevConstant : ℝ)*lpNorm (fderiv ℝ f) 2 volume)) *
        (2*(lpNorm g 2 volume+(sobolevConstant : ℝ)*lpNorm (fderiv ℝ g) 2 volume)) :=
      mul_le_mul h4f.2 h4g.2 lpNorm_nonneg
        (mul_nonneg (by norm_num) (add_nonneg lpNorm_nonneg
          (mul_nonneg sobolevConstant.coe_nonneg lpNorm_nonneg)))
    _ = _ := by ring

end EulerOrdinarySobolev
