/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerS5A2Envelope.SymmetryEquivariance

/-!
Construction of the smoothing kernel with its explicit regularity and curvature guarantees.
-/

@[expose] public section

namespace V7.Stage5AboveTwoLowerS5A2Envelope

open Stage5AboveTwoLower
open Stage5AboveTwoLower.S5ARepair
open Stage5AboveTwoLower.S5AGlobalC2
open Stage5AboveTwoLowerResume

lemma repairMpd_pos {p : ℝ} {d : ℕ} (hp : 2 < p) (hd : 2 ≤ d) :
    0 < repairMpd p d := by
  unfold repairMpd
  split_ifs
  · positivity
  · have hlog : 0 < Real.log d := Real.log_pos (by exact_mod_cast
      (lt_of_lt_of_le (by decide : 1 < 2) hd))
    positivity

lemma repairMpd_universal_bound {p : ℝ} {d : ℕ}
    (hp : 2 < p) (hd : 2 ≤ d) :
    repairMpd p d ≤
      (15 * Real.exp (2 / 3)) * min p (Real.log d) := by
  have hlog : 0 < Real.log d := Real.log_pos (by exact_mod_cast
    (lt_of_lt_of_le (by decide : 1 < 2) hd))
  have hexp : 1 ≤ Real.exp (2 / 3 : ℝ) := Real.one_le_exp (by norm_num)
  unfold repairMpd
  split_ifs with hregime
  · by_cases hsmall : p ≤ Real.log d
    · rw [min_eq_left hsmall]
      nlinarith [mul_le_mul_of_nonneg_right hexp (by linarith : 0 ≤ p)]
    · rw [min_eq_right (le_of_not_ge hsmall)]
      have hpLog : p ≤ 3 * Real.log d := hregime
      nlinarith [mul_le_mul_of_nonneg_right hexp hlog.le]
  · have hle : Real.log d ≤ p := by
      have : 3 * Real.log d < p := lt_of_not_ge hregime
      linarith
    rw [min_eq_right hle]

/-- Every frozen clause except no clause: the concrete repaired data now
satisfies the full `SmoothingKernelAssumptions` carrier. -/
theorem repairKernel_assumptions {p : ℝ} {d : ℕ}
    (hp : 2 < p) (hd : 2 ≤ d) :
    SmoothingKernelAssumptions (repairKernel p d) := by
  let r := kernelR0 p d
  let theta := repairTheta p d
  have hr : 2 < r := two_lt_kernelR0 hp hd
  have hrp : r ≤ p := min_le_left _ _
  have ht : 1 < theta := one_lt_repairTheta hp hd
  have htUpper : theta < 5 / 4 :=
    (repairTheta_lt_101_div_100 hp hd).trans (by norm_num)
  have htr : 2 * theta < r := two_mul_repairTheta_lt_kernelR0 hp hd
  refine ⟨repairMpd_pos hp hd,
    lowerKernelPhi_convex (by linarith : 1 ≤ r) ht,
    contDiff_two_lowerKernelPhi hr ht htr,
    lowerKernelPhi_coordinateGradient hr ht htr,
    fun x ↦ hasFDerivAt_kernelGradientVector hr ht htr x,
    lowerKernelPhi_nonneg,
    lowerKernelPhi_zero (by linarith) (by linarith),
    kernelGradientVector_zero hr ht htr,
    ?_, ?_, repairKernel_phi_signed_invariant hp hd,
    repairKernel_value_realization, ?_,
    repairKernel_exactPairLocality hp hd,
    repairKernel_smooth_value_signed_equivariant hp hd⟩
  · intro x hx
    have hb := lowerKernelPhi_radial (by linarith : 1 ≤ r) hrp ht x (by rw [hx])
    simpa [repairKernel] using hb
  · intro x e hx
    simpa [repairKernel, repairMpd] using
      (repair_kernelHessian_unit_bound hp hd x e hx)
  · intro chi hchi ell hconv hlip
    refine ⟨repairKernel_coordinateGradient hp hd chi hchi ell hconv hlip,
      ?_, repairKernel_smooth hp hd chi hchi ell hconv hlip⟩
    intro x
    simpa [repairKernel, repairSelectedOracle] using
      (localSmoothingValue_bounds_lowerKernelPhi
        (repairKernelBase p d) hr hrp ht htr hchi rfl ell hlip x)

/-- The exact raw Hessian formula exported by the construction. -/
lemma repairKernel_raw_hessian_bound {p : ℝ} {d : ℕ}
    (hp : 2 < p) (hd : 2 ≤ d) :
    ∀ x e,
      pairing e ((repairKernel p d).hessian x e) ≤
        4 * repairTheta p d * (kernelR0 p d - 1) *
          (lpNorm (kernelR0 p d) x) ^ (2 * repairTheta p d - 2) *
          (lpNorm (kernelR0 p d) e) ^ (2 : ℕ) := by
  intro x e
  exact kernelHessian_quadratic_bound (two_lt_kernelR0 hp hd)
    (one_lt_repairTheta hp hd) (two_mul_repairTheta_lt_kernelR0 hp hd) x e

end V7.Stage5AboveTwoLowerS5A2Envelope

namespace V7

open Stage5AboveTwoLower
open Stage5AboveTwoLower.S5ARepair
open Stage5AboveTwoLowerS5A2Envelope

/-- Full Stage-5 S5-A kernel construction. -/
theorem smoothingKernelConstruction : SmoothingKernelConstructionStatement := by
  let C : ℝ := 15 * Real.exp (2 / 3)
  refine ⟨C, by positivity, ?_⟩
  intro p hp d hd
  refine ⟨kernelR0 p d, repairTheta p d, repairKernel p d,
    rfl, one_lt_repairTheta hp hd,
    two_mul_repairTheta_lt_kernelR0 hp hd, rfl,
    repairKernel_assumptions hp hd,
    repairKernel_raw_hessian_bound hp hd, ?_, ?_⟩
  · rfl
  · exact repairMpd_universal_bound hp hd

end V7
