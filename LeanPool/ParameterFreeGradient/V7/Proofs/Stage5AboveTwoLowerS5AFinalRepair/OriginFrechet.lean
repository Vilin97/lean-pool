/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerS5ARepair.KernelAmbientHessian
public import LeanPool.ParameterFreeGradient.O3.Stage2RouteB
public import LeanPool.ParameterFreeGradient.O3.Stage2RouteC
public import Mathlib.Analysis.InnerProductSpace.NormPow

/-!
The kernel gradient is Fréchet differentiable at the origin with zero derivative.
-/

@[expose] public section

open scoped BigOperators
open Asymptotics

namespace V7.Stage5AboveTwoLower.S5AFinalRepair

open S5ARepair

/-- Dependency-pure copy of the exact dual norm calculation for the power
duality map.  This uses only the shared Stage-2 geometry, not an obsolete
above-two trial or machine. -/
lemma lpNorm_powerDualityMap {r : ℝ} (hr : 1 < r) {d : ℕ} (x : Point d) :
    O3.lpNorm (O3.conjugateExponent r) (O3.powerDualityMap r x) =
      O3.lpNorm r x ^ (r - 1) := by
  have hpower : O3.lpPower (O3.conjugateExponent r) (O3.powerDualityMap r x) =
      O3.lpPower r x := by
    unfold O3.lpPower O3.powerDualityMap
    apply Finset.sum_congr rfl
    intro i _
    rw [O3.Stage2RouteB.abs_powerDuality_coordinate hr]
    rw [← Real.rpow_mul (abs_nonneg (x i))]
    rw [O3.Stage2RouteB.mul_conjugateExponent_sub_one hr]
  unfold O3.lpNorm
  rw [hpower]
  have hbase : 0 ≤ O3.lpPower r x := O3.lpPower_nonneg r x
  have hr0 : r ≠ 0 := by linarith
  have hr10 : r - 1 ≠ 0 := by linarith
  rw [show 1 / O3.conjugateExponent r = (r - 1) / r by
    rw [O3.conjugateExponent_eq]
    field_simp [hr0, hr10]]
  rw [show (r - 1) / r = (1 / r) * (r - 1) by ring]
  exact Real.rpow_mul hbase _ _

/-- Every coordinate is bounded by the literal finite-dimensional `ell_s`
norm. -/
lemma norm_apply_le_lpNorm {s : ℝ} (hs : 1 ≤ s) {d : ℕ}
    (x : Point d) (i : Fin d) : |x i| ≤ O3.lpNorm s x := by
  let _ : Fact (1 ≤ ENNReal.ofReal s) :=
    ⟨ENNReal.one_le_ofReal.mpr hs⟩
  have h := PiLp.norm_apply_le
    (WithLp.toLp (ENNReal.ofReal s) x :
      PiLp (ENNReal.ofReal s) (fun _ : Fin d ↦ ℝ)) i
  rw [O3.Stage2RouteC.lpNorm_eq_piLpNorm hs x]
  simpa [Real.norm_eq_abs] using h

/-- The ambient product norm is bounded by the literal finite-dimensional
`ell_s` norm. -/
lemma norm_le_lpNorm {s : ℝ} (hs : 1 ≤ s) {d : ℕ} (x : Point d) :
    ‖x‖ ≤ O3.lpNorm s x := by
  apply (pi_norm_le_iff_of_nonneg (O3.lpNorm_nonneg s x)).2
  intro i
  simpa [Real.norm_eq_abs] using norm_apply_le_lpNorm hs x i

/-- Explicit finite-dimensional comparison constant between the ambient
product norm and the literal `ell_s` norm. -/
noncomputable def lpAmbientConstant (s : ℝ) (d : ℕ) : ℝ :=
  ↑(NNReal.rpow (d : NNReal)
    (1 / ENNReal.ofReal s).toReal)

lemma lpAmbientConstant_nonneg (s : ℝ) (d : ℕ) :
    0 ≤ lpAmbientConstant s d := by
  exact NNReal.zero_le_coe

/-- The literal `ell_s` norm is bounded by a fixed multiple of the ambient
product norm.  The multiplier is the explicit Lipschitz constant of the
canonical finite-dimensional `PiLp` transport. -/
lemma lpNorm_le_ambientConstant {s : ℝ} (hs : 1 ≤ s) {d : ℕ} (x : Point d) :
    O3.lpNorm s x ≤
      lpAmbientConstant s d * ‖x‖ := by
  let _ : Fact (1 ≤ ENNReal.ofReal s) :=
    ⟨ENNReal.one_le_ofReal.mpr hs⟩
  have hT := PiLp.lipschitzWith_toLp (ENNReal.ofReal s)
    (fun _ : Fin d ↦ ℝ) x (0 : Point d)
  have hfin :
      (↑((Fintype.card (Fin d) : NNReal) ^
          (1 / ENNReal.ofReal s).toReal) : ENNReal) * edist x 0 ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by simp) (edist_ne_top _ _)
  simp only [edist_dist, dist_zero_right] at hT
  have hreal := ENNReal.toReal_mono (by simpa only [edist_dist, dist_zero_right] using hfin) hT
  change O3.lpNorm s x ≤ lpAmbientConstant s d * ‖x‖
  rw [O3.Stage2RouteC.lpNorm_eq_piLpNorm hs]
  simpa [lpAmbientConstant, ENNReal.toReal_mul, NNReal.coe_rpow] using hreal

/-- Exact dual norm of the concrete kernel gradient. -/
lemma lpNorm_kernelGradientVector {r theta : ℝ} (hr : 2 < r)
    (htheta : 1 < theta) {d : ℕ} (x : Point d) :
    O3.lpNorm (O3.conjugateExponent r) (kernelGradientVector r theta x) =
      4 * theta * O3.lpNorm r x ^ (2 * theta - 1) := by
  by_cases hx : x = 0
  · subst x
    have hJ : O3.powerDualityMap r (0 : Point d) = 0 := by
      ext i
      simp [O3.powerDualityMap]
    rw [kernelGradientVector, hJ, smul_zero]
    rw [O3.lpNorm_zero (lt_trans zero_lt_one
      (O3.one_lt_conjugateExponent (by linarith : 1 < r)))]
    rw [O3.lpNorm_zero (by linarith : 0 < r)]
    rw [Real.zero_rpow (by linarith : 2 * theta - 1 ≠ 0)]
    ring
  · have hn : 0 < O3.lpNorm r x := O3.lpNorm_pos_of_ne_zero hx
    have hpow := O3.Stage2RouteB.lpNorm_rpow_eq_lpPower
      (p := r) (by linarith : r ≠ 0) x
    change O3.lpNorm (O3.conjugateExponent r)
      (fun i ↦ (4 * theta * O3.lpPower r x ^ (2 * theta / r - 1)) *
        O3.powerDualityMap r x i) = _
    rw [O3.Stage2RouteB.lpNorm_scalar_mul
      (O3.one_lt_conjugateExponent (by linarith : 1 < r) |>.trans' zero_lt_one)]
    rw [lpNorm_powerDualityMap (by linarith : 1 < r)]
    rw [abs_mul, abs_of_pos (mul_pos (by positivity) (by linarith : 0 < theta))]
    rw [abs_of_nonneg (Real.rpow_nonneg (O3.lpPower_nonneg r x) _)]
    rw [← hpow]
    rw [← Real.rpow_mul hn.le]
    rw [mul_assoc, ← Real.rpow_add hn]
    congr 1
    field_simp [ne_of_gt (by linarith : 0 < r)]
    ring

/-- Uniform ambient growth of the kernel gradient.  The negative-looking
power of `lpPower` has disappeared before this estimate is used at the
origin. -/
lemma norm_kernelGradientVector_le {r theta : ℝ} (hr : 2 < r)
    (htheta : 1 < theta) {d : ℕ} (x : Point d) :
    ‖kernelGradientVector r theta x‖ ≤
      4 * theta * O3.lpNorm r x ^ (2 * theta - 1) := by
  have hq : 1 ≤ O3.conjugateExponent r :=
    (O3.one_lt_conjugateExponent (by linarith : 1 < r)).le
  exact (norm_le_lpNorm hq _).trans_eq
    (lpNorm_kernelGradientVector hr htheta x)

/-- For any normed real vector space, a real power of the norm with exponent
strictly larger than one is little-o of the identity at the origin. -/
lemma norm_rpow_isLittleO_id {E : Type*} [NormedAddCommGroup E]
     {a : ℝ} (ha : 1 < a) :
    (fun x : E ↦ ‖x‖ ^ a) =o[nhds 0] (fun x : E ↦ x) := by
  have hpos : 0 < a - 1 := sub_pos.mpr ha
  calc
    (fun x : E ↦ ‖x‖ ^ a) =
        (fun x : E ↦ ‖x‖ * ‖x‖ ^ (a - 1)) := by
          funext x
          rw [← Real.rpow_one_add' (norm_nonneg x) (by positivity)]
          ring_nf
    _ =o[nhds 0] (fun x : E ↦ ‖x‖ * 1) := by
      refine (isBigO_refl _ _).mul_isLittleO <|
        (isLittleO_const_iff (by simp)).mpr ?_
      convert! continuousAt_id.norm.rpow_const (.inr hpos.le) |>.tendsto
      simp [hpos.ne']
    _ =O[nhds 0] (fun x : E ↦ x) := by
      simpa only [mul_one] using
        (isBigO_norm_left.mpr (isBigO_refl (fun x : E ↦ x) (nhds 0)))

/-- The gradient is genuinely Fréchet differentiable at the origin with zero
derivative.  This is the first hard gate of the final S5-A repair. -/
theorem hasFDerivAt_kernelGradientVector_zero {r theta : ℝ}
    (hr : 2 < r) (htheta : 1 < theta) (htr : 2 * theta < r) {d : ℕ} :
    HasFDerivAt (kernelGradientVector (d := d) r theta)
      (kernelHessian (d := d) r theta 0) 0 := by
  have ha : 1 < 2 * theta - 1 := by linarith
  have hzeroG : kernelGradientVector r theta (0 : Point d) = 0 := by
    have he : 2 * theta / r - 1 ≠ 0 := by
      have hr0 : 0 < r := by linarith
      rw [ne_eq, sub_eq_zero, div_eq_one_iff_eq (ne_of_gt hr0)]
      linarith
    simp [kernelGradientVector,
      O3.lpPower_zero (by linarith : r ≠ 0), Real.zero_rpow he]
  have hzeroH : kernelHessian r theta (0 : Point d) = 0 := by
    have he1 : 2 * theta / r - 1 ≠ 0 := by
      have hr0 : 0 < r := by linarith
      rw [ne_eq, sub_eq_zero, div_eq_one_iff_eq (ne_of_gt hr0)]
      linarith
    have he2 : r - 2 ≠ 0 := by linarith
    ext h i
    simp [kernelHessian, kernelHessianCoord, lpPowerFDeriv,
      pairingCLM, O3.lpPower_zero (by linarith : r ≠ 0),
      O3.Experimental.scalarJ, Real.zero_rpow he1, Real.zero_rpow he2]
  rw [hzeroH]
  have hbig :
      (kernelGradientVector (d := d) r theta) =O[nhds 0]
        (fun x : Point d ↦ ‖x‖ ^ (2 * theta - 1)) :=
    IsBigO.of_bound (4 * theta *
        lpAmbientConstant r d ^ (2 * theta - 1))
      (Filter.Eventually.of_forall fun x : Point d ↦ by
        have hlp := lpNorm_le_ambientConstant (d := d)
          (by linarith : 1 ≤ r) x
        have hrpow := Real.rpow_le_rpow (O3.lpNorm_nonneg r x) hlp
          (by linarith : 0 ≤ 2 * theta - 1)
        have hgrad := norm_kernelGradientVector_le hr htheta x
        rw [Real.norm_rpow_of_nonneg (norm_nonneg x)]
        calc
          ‖kernelGradientVector r theta x‖ ≤
              4 * theta * O3.lpNorm r x ^ (2 * theta - 1) := hgrad
          _ ≤ 4 * theta *
              (lpAmbientConstant r d * ‖x‖) ^
                  (2 * theta - 1) := by gcongr
          _ = (4 * theta *
              lpAmbientConstant r d ^ (2 * theta - 1)) *
                ‖x‖ ^ (2 * theta - 1) := by
                  rw [Real.mul_rpow (lpAmbientConstant_nonneg r d)
                    (norm_nonneg x)]
                  ring
          _ = (4 * theta *
              lpAmbientConstant r d ^ (2 * theta - 1)) *
                ‖‖x‖‖ ^ (2 * theta - 1) := by rw [norm_norm])
  have hlittle :
      (kernelGradientVector (d := d) r theta) =o[nhds 0]
        (fun x : Point d ↦ x) :=
    hbig.trans_isLittleO (norm_rpow_isLittleO_id (E := Point d) ha)
  exact HasFDerivAt.of_isLittleO (by
    simpa [hzeroG] using hlittle)

end V7.Stage5AboveTwoLower.S5AFinalRepair
