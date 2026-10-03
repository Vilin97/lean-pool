/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.SpatialPrimitive
public import Mathlib.Analysis.Calculus.MeanValue

/-! Source spatial primitive estimates for the stream velocity. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- Coordinate bounds control the operator norm in the fixed two-dimensional
sup norm, with the explicit dimension factor. -/
theorem amnr_clm_norm_le_two_basis {L : Vec 2 →L[ℝ] ℝ} {B : ℝ}
    (hB : 0 ≤ B) (h0 : ‖L (basisVec 0)‖ ≤ B) (h1 : ‖L (basisVec 1)‖ ≤ B) :
    ‖L‖ ≤ 2 * B := by
  apply L.opNorm_le_bound (by positivity)
  intro v
  have hv : v = v 0 • basisVec 0 + v 1 • basisVec 1 := by
    funext i
    fin_cases i <;> simp [basisVec_apply]
  calc
    ‖L v‖ = ‖v 0 • L (basisVec 0) + v 1 • L (basisVec 1)‖ := by
      conv_lhs => rw [hv, map_add, map_smul, map_smul]
    _ ≤ |v 0| * ‖L (basisVec 0)‖ + |v 1| * ‖L (basisVec 1)‖ := by
      simpa only [norm_smul, Real.norm_eq_abs] using norm_add_le
        (v 0 • L (basisVec 0)) (v 1 • L (basisVec 1))
    _ ≤ ‖v‖ * B + ‖v‖ * B := by
      apply add_le_add
      · exact mul_le_mul (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v (0 : Fin 2))
          h0 (norm_nonneg _) (norm_nonneg _)
      · exact mul_le_mul (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v (1 : Fin 2))
          h1 (norm_nonneg _) (norm_nonneg _)
    _ = (2 * B) * ‖v‖ := by ring

/-- A smooth scalar's gradient coordinates inherit a Lipschitz bound from
its actual Hessian coordinate bounds. -/
theorem amnr_gradient_lipschitz_of_hessian {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {B : ℝ} (hB : 0 ≤ B)
    (hH : ∀ (x : Vec 2) (J : Fin 2 → Fin 2),
      ‖iteratedFDeriv ℝ 2 f x (fun j => basisVec (J j))‖ ≤ B) (i : Fin 2) :
    LipschitzWith (2 * B).toNNReal (fun x => AVenhance.spaceGrad f x i) := by
  have hdf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hg : Differentiable ℝ (fun x => fderiv ℝ f x (basisVec i)) :=
    (hdf.clm_apply (contDiff_const : ContDiff ℝ 1 (fun _ : Vec 2 => basisVec i))).differentiable
      (by norm_num)
  apply lipschitzWith_of_nnnorm_fderiv_le hg
  intro x
  apply NNReal.coe_le_coe.mp
  rw [coe_nnnorm, Real.coe_toNNReal _ (by positivity)]
  have hj (j : Fin 2) :
      ‖fderiv ℝ (fun y => fderiv ℝ f y (basisVec i)) x (basisVec j)‖ ≤ B := by
    have h := fderiv_clm_apply (hdf.differentiable (by norm_num) x)
      (differentiableAt_const (basisVec i))
    have he := congrArg (fun L : Vec 2 →L[ℝ] ℝ => L (basisVec j)) h
    have heq : fderiv ℝ (fun y => fderiv ℝ f y (basisVec i)) x (basisVec j) =
        iteratedFDeriv ℝ 2 f x (fun k => basisVec (if k = 0 then j else i)) := by
      simpa [iteratedFDeriv_two_apply] using he
    rw [heq]
    exact hH x _
  exact amnr_clm_norm_le_two_basis hB (hj 0) (hj 1)

/-- Rotation of the gradient preserves its coordinate Lipschitz bound. -/
theorem amnr_streamVel_lipschitz_of_hessian {φ : ℝ → Vec 2 → ℝ} (t : ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) (φ t)) {B : ℝ} (hB : 0 ≤ B)
    (hH : ∀ (x : Vec 2) (J : Fin 2 → Fin 2),
      ‖iteratedFDeriv ℝ 2 (φ t) x (fun j => basisVec (J j))‖ ≤ B)
    (x y : Vec 2) :
    ‖AVenhance.streamVel φ t x - AVenhance.streamVel φ t y‖ ≤ 2 * B * ‖x - y‖ := by
  have hcoef : 0 ≤ 2 * B := by positivity
  have hi (i : Fin 2) : ‖AVenhance.spaceGrad (φ t) x i - AVenhance.spaceGrad (φ t) y i‖ ≤
      2 * B * ‖x - y‖ := by
    have h := (amnr_gradient_lipschitz_of_hessian hf hB hH i).dist_le_mul x y
    simpa only [dist_eq_norm, Real.coe_toNNReal _ hcoef] using h
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hcoef (norm_nonneg _))).mpr
  intro i
  fin_cases i
  · have heq : (AVenhance.streamVel φ t x - AVenhance.streamVel φ t y) 0 =
        -(AVenhance.spaceGrad (φ t) x 1 - AVenhance.spaceGrad (φ t) y 1) := by
      simp [AVenhance.streamVel, AVenhance.sigmaMat, dotProduct,
        Fin.sum_univ_two]
      ring
    change ‖(AVenhance.streamVel φ t x - AVenhance.streamVel φ t y) (0 : Fin 2)‖ ≤ _
    rw [heq, norm_neg]
    exact hi 1
  · simpa [AVenhance.streamVel, AVenhance.sigmaMat, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] using hi 0

/-- The source stream-regularity seminorm gives the velocity's spatial Lipschitz estimate.
No derivative estimate for the velocity is assumed. -/
theorem amnr_streamVel_lipschitz_of_A3 {β C : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (hreg : AVenhance.StreamRegularityBounds C I Φ) {m : ℕ} (hm : 1 ≤ m)
    (t : ℝ) (x y : Vec 2) :
    ‖AVenhance.streamVel (Φ m) t x - AVenhance.streamVel (Φ m) t y‖ ≤
      ((2 : ℝ) ^ 20 * AVenhance.a β I.Λ m) * ‖x - y‖ := by
  have ha := AVenhance.Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
    (m := m)
  have hs : ContDiff ℝ (⊤ : ℕ∞) (Φ m t) :=
    (AVenhance.streamSeq_isAdmissible hΦ m).1.comp (contDiff_const.prodMk contDiff_id)
  have hh := amnr_streamVel_lipschitz_of_hessian t hs
    (show 0 ≤ (2 : ℝ) ^ 19 * AVenhance.a β I.Λ m from by positivity)
    (amnr_stream_hessian_le_of_A3 I hΦ hreg hm t) x y
  convert hh using 1
  ring

/-- The actual pulled-back flow gradient is bounded by two on the cutoff
window, from the source stream-regularity estimates, uniformly in the level and cutoff index. -/
theorem amnr_flowGrad_abs_le_two_of_A3_ge_two {β C : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (hreg : AVenhance.StreamRegularityBounds C I Φ) {m : ℕ} (hm : 2 ≤ m)
    (l : ℤ) (t : ℝ) (x : Vec 2)
    (ht : |t - (l : ℝ) * AVenhance.tauPP β I.Λ m| ≤
      AVenhance.tauPP β I.Λ m / 2 + AVenhance.tauP β I.Λ m) (k p : Fin 2) :
    |I.flowGrad hΦ m l t x k p| ≤ 2 := by
  have hx := amnr_flowGrad_abs_le_on_cutoff_window I hΦ (by omega : 1 ≤ m)
    (C := (2 : ℝ) ^ 20) (by positivity)
    (amnr_streamVel_lipschitz_of_A3 I hΦ hreg (by omega : 1 ≤ m - 1)) l t x ht k p
  refine hx.trans ?_
  norm_num only [zpow_neg, zpow_natCast, Nat.reducePow]
  have he := Real.exp_le_two_add_div_two_sub (x := (1 : ℝ) / 32) (by norm_num) (by norm_num)
  norm_num at he ⊢
  exact he.trans (by norm_num)

/-- The base stream has zero velocity, so its actual flow-gradient entries
are bounded by one by the same characterized-flow estimate. -/
theorem amnr_flowGrad_one_abs_le_one {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (l : ℤ) (t : ℝ) (x : Vec 2) (k p : Fin 2) :
    |I.flowGrad hΦ 1 l t x k p| ≤ 1 := by
  have hL : ∀ t x y,
      ‖AVenhance.streamVel (Φ (1 - 1)) t x - AVenhance.streamVel (Φ (1 - 1)) t y‖ ≤
        (0 : ℝ) * ‖x - y‖ := by
    intro t x y
    rw [show 1 - 1 = (0 : ℕ) by omega, hΦ.1]
    have hzero : AVenhance.spaceGrad (fun _ : Vec 2 => (0 : ℝ)) = 0 := by
      funext z i
      change fderiv ℝ (fun _ : Vec 2 => (0 : ℝ)) z (basisVec i) = 0
      rw [fderiv_const_apply]
      rfl
    simp only [AVenhance.streamVel, hzero, Pi.zero_apply, Matrix.mulVec_zero, sub_self,
      norm_zero, zero_mul, le_refl]
  have hh := amnr_flowGrad_abs_le_of_lipschitz I hΦ 1 hL l t x k p
  simpa only [zero_mul, Real.exp_zero] using hh

/-- Uniform primitive flow size on every actual cutoff window, including
the zero-stream base scale. -/
theorem amnr_flowGrad_abs_le_two_of_A3 {β C : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (hreg : AVenhance.StreamRegularityBounds C I Φ) {m : ℕ} (hm : 1 ≤ m)
    (l : ℤ) (t : ℝ) (x : Vec 2)
    (ht : |t - (l : ℝ) * AVenhance.tauPP β I.Λ m| ≤
      AVenhance.tauPP β I.Λ m / 2 + AVenhance.tauP β I.Λ m) (k p : Fin 2) :
    |I.flowGrad hΦ m l t x k p| ≤ 2 := by
  by_cases hbase : m = 1
  · subst m
    exact (amnr_flowGrad_one_abs_le_one I hΦ l t x k p).trans (by norm_num)
  · exact amnr_flowGrad_abs_le_two_of_A3_ge_two I hΦ hreg (by omega) l t x ht k p

end AVenhance.Infra.Section4
