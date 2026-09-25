/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerS5A2Envelope.EnvelopeDerivative

/-!
Assembly of the selected envelope oracle and its coordinate-gradient and smoothness proofs.
-/

@[expose] public section

namespace V7.Stage5AboveTwoLowerS5A2Envelope

open Stage5AboveTwoLower
open Stage5AboveTwoLower.S5ARepair
open Stage5AboveTwoLower.S5AFinalRepair
open Stage5AboveTwoLower.S5AGlobalC2
open Stage5AboveTwoLowerResume

/-- The explicit curvature bound for the constructed smoothing kernel. -/
noncomputable def repairMpd (p : ℝ) (d : ℕ) : ℝ :=
  if p ≤ 3 * Real.log d then 5 * p
  else 15 * Real.exp (2 / 3) * Real.log d

/-- The constant zero oracle used in the preliminary kernel data. -/
noncomputable def dormantOracle (d : ℕ) : PairOracle d :=
  { value := fun _ ↦ 0, gradient := fun _ ↦ 0 }

/-- Nonrecursive concrete kernel data used to formulate and select minimizers.
Its dormant `smooth` field is never used in the infimal cost. -/
noncomputable def repairKernelBase (p : ℝ) (d : ℕ) :
    SmoothingKernelData p d :=
  { phi := lowerKernelPhi (kernelR0 p d) (repairTheta p d)
    gradPhi := kernelGradientVector (kernelR0 p d) (repairTheta p d)
    hessian := kernelHessian (kernelR0 p d) (repairTheta p d)
    Mpd := repairMpd p d
    smooth := fun _ _ ↦ dormantOracle d }

/-- The infimal smoothing value paired with the selected envelope gradient. -/
noncomputable def repairSelectedOracle (p : ℝ) (d : ℕ)
    (chi : ℝ) (ell : Point d → ℝ) : PairOracle d :=
  { value := localSmoothingValue (repairKernelBase p d) chi ell
    gradient := selectedEnvelopeGradient (repairKernelBase p d) chi ell }

/-- Final kernel data: its smooth oracle is the literal infimal value paired
with the selected primal-envelope gradient. -/
noncomputable def repairKernel (p : ℝ) (d : ℕ) :
    SmoothingKernelData p d :=
  { phi := lowerKernelPhi (kernelR0 p d) (repairTheta p d)
    gradPhi := kernelGradientVector (kernelR0 p d) (repairTheta p d)
    hessian := kernelHessian (kernelR0 p d) (repairTheta p d)
    Mpd := repairMpd p d
    smooth := repairSelectedOracle p d }

lemma repairMpd_nonneg {p : ℝ} {d : ℕ} (hp : 2 < p) (hd : 2 ≤ d) :
    0 ≤ repairMpd p d := by
  unfold repairMpd
  split_ifs
  · positivity
  · have hlog : 0 < Real.log d := Real.log_pos (by exact_mod_cast
      (lt_of_lt_of_le (by decide : 1 < 2) hd))
    positivity

lemma selectedDisplacement_concrete_spec {p : ℝ} {d : ℕ}
    (hp : 2 < p) (hd : 2 ≤ d) {chi : ℝ} (hchi : 0 < chi)
    (ell : Point d → ℝ) (hlip : IsOneLipschitz p ell) (x : Point d) :
    IsInfimalMinimizer (repairKernelBase p d) chi ell x
        (selectedDisplacement (repairKernelBase p d) chi ell x) ∧
      lpNorm p (selectedDisplacement (repairKernelBase p d) chi ell x) ≤
        chi - chi / 4 := by
  apply selectedDisplacement_spec
  exact exists_infimal_minimizer_lowerKernelPhi_with_margin
    (repairKernelBase p d) (two_lt_kernelR0 hp hd)
    (min_le_left _ _) (one_lt_repairTheta hp hd)
    ((repairTheta_lt_101_div_100 hp hd).trans (by norm_num))
    (two_mul_repairTheta_lt_kernelR0 hp hd) hchi rfl ell hlip x

lemma selectedDisplacement_scaled_unit {p : ℝ} {d : ℕ}
    (hp : 2 < p) (hd : 2 ≤ d) {chi : ℝ} (hchi : 0 < chi)
    (ell : Point d → ℝ) (hlip : IsOneLipschitz p ell) (x : Point d) :
    lpNorm p ((1 / chi) •
      selectedDisplacement (repairKernelBase p d) chi ell x) ≤ 1 := by
  have hs := (selectedDisplacement_concrete_spec hp hd hchi ell hlip x).2
  change O3.lpNorm p ((1 / chi) •
    selectedDisplacement (repairKernelBase p d) chi ell x) ≤ 1
  rw [O3.Stage2RouteC.lpNorm_smul (by linarith : 1 ≤ p),
    abs_of_pos (one_div_pos.mpr hchi)]
  rw [div_mul_eq_mul_div, div_le_one hchi]
  linarith

lemma repairSelectedGradient_support {p : ℝ} {d : ℕ}
    (hp : 2 < p) (hd : 2 ≤ d) {chi : ℝ} (hchi : 0 < chi)
    (ell : Point d → ℝ) (hconv : O3.IsConvexObjective ell)
    (hlip : IsOneLipschitz p ell) (x y : Point d) :
    localSmoothingValue (repairKernelBase p d) chi ell x +
        O3.pairing
          (selectedEnvelopeGradient (repairKernelBase p d) chi ell x) (y - x) ≤
      localSmoothingValue (repairKernelBase p d) chi ell y := by
  exact localSmoothingValue_supporting_of_minimizers
    (repairKernelBase p d) hchi ell hconv
    (lowerKernelPhi_convex (by linarith [two_lt_kernelR0 hp hd] : 1 ≤ kernelR0 p d)
      (one_lt_repairTheta hp hd))
    (lowerKernelPhi_coordinateGradient (two_lt_kernelR0 hp hd)
      (one_lt_repairTheta hp hd)
      (two_mul_repairTheta_lt_kernelR0 hp hd))
    (selectedDisplacement_concrete_spec hp hd hchi ell hlip x).1
    (selectedDisplacement_concrete_spec hp hd hchi ell hlip y).1

lemma repairSelectedGradient_lipschitz {p : ℝ} {d : ℕ}
    (hp : 2 < p) (hd : 2 ≤ d) {chi : ℝ} (hchi : 0 < chi)
    (ell : Point d → ℝ) (hconv : O3.IsConvexObjective ell)
    (hlip : IsOneLipschitz p ell) (x y : Point d) :
    lpNorm (conjugateExponent p)
        (selectedEnvelopeGradient (repairKernelBase p d) chi ell x -
          selectedEnvelopeGradient (repairKernelBase p d) chi ell y) ≤
      (repairMpd p d / chi) * lpNorm p (x - y) := by
  have hcoco : KernelCocoerciveOnUnit p (repairMpd p d)
      (repairKernelBase p d).gradPhi := by
    simpa [repairMpd, repairKernelBase] using
      (repair_kernelGradient_cocoercive hp hd)
  have h := minimizer_kernel_gradient_lipschitz (repairKernelBase p d)
    (by linarith : 1 < p) hchi (repairMpd_nonneg hp hd) ell hconv
    (lowerKernelPhi_coordinateGradient (two_lt_kernelR0 hp hd)
      (one_lt_repairTheta hp hd)
      (two_mul_repairTheta_lt_kernelR0 hp hd)) hcoco
    (selectedDisplacement_concrete_spec hp hd hchi ell hlip x).1
    (selectedDisplacement_concrete_spec hp hd hchi ell hlip y).1
    (selectedDisplacement_scaled_unit hp hd hchi ell hlip x)
    (selectedDisplacement_scaled_unit hp hd hchi ell hlip y)
  have hneg :
      selectedEnvelopeGradient (repairKernelBase p d) chi ell x -
        selectedEnvelopeGradient (repairKernelBase p d) chi ell y =
      -((repairKernelBase p d).gradPhi
          ((1 / chi) • selectedDisplacement (repairKernelBase p d) chi ell x) -
        (repairKernelBase p d).gradPhi
          ((1 / chi) • selectedDisplacement (repairKernelBase p d) chi ell y)) := by
    simp only [selectedEnvelopeGradient]
    module
  rw [hneg]
  let D : Point d :=
    (repairKernelBase p d).gradPhi
        ((1 / chi) • selectedDisplacement (repairKernelBase p d) chi ell x) -
      (repairKernelBase p d).gradPhi
        ((1 / chi) • selectedDisplacement (repairKernelBase p d) chi ell y)
  have hnormNeg : lpNorm (conjugateExponent p) (-D) =
      lpNorm (conjugateExponent p) D := by
    rw [show -D = (-1 : ℝ) • D by module]
    change O3.lpNorm (O3.conjugateExponent p) ((-1 : ℝ) • D) =
      O3.lpNorm (O3.conjugateExponent p) D
    rw [O3.Stage2RouteC.lpNorm_smul
      (O3.one_lt_conjugateExponent (by linarith : 1 < p)).le]
    norm_num
  change lpNorm (conjugateExponent p) (-D) ≤ _
  rw [hnormNeg]
  exact h

lemma hasFDerivAt_repairSelectedValue {p : ℝ} {d : ℕ}
    (hp : 2 < p) (hd : 2 ≤ d) {chi : ℝ} (hchi : 0 < chi)
    (ell : Point d → ℝ) (hconv : O3.IsConvexObjective ell)
    (hlip : IsOneLipschitz p ell) (x : Point d) :
    HasFDerivAt (repairSelectedOracle p d chi ell).value
      (pairingCLM ((repairSelectedOracle p d chi ell).gradient x)) x := by
  apply hasFDerivAt_of_global_support_and_lp_lipschitz
    (by linarith : 1 < p) (div_nonneg (repairMpd_nonneg hp hd) hchi.le)
  · exact fun a b ↦ repairSelectedGradient_support hp hd hchi ell hconv hlip a b
  · exact fun a b ↦ repairSelectedGradient_lipschitz hp hd hchi ell hconv hlip a b

lemma repairSelectedOracle_coordinateGradient {p : ℝ} {d : ℕ}
    (hp : 2 < p) (hd : 2 ≤ d) {chi : ℝ} (hchi : 0 < chi)
    (ell : Point d → ℝ) (hconv : O3.IsConvexObjective ell)
    (hlip : IsOneLipschitz p ell) :
    O3.IsCoordinateGradient (repairSelectedOracle p d chi ell).value
      (repairSelectedOracle p d chi ell).gradient := by
  intro x
  have h := hasFDerivAt_repairSelectedValue hp hd hchi ell hconv hlip x
  exact ⟨h.differentiableAt, fun v ↦ by
    rw [h.fderiv]
    exact pairingCLM_apply _ _⟩

lemma repairSelectedOracle_smooth {p : ℝ} {d : ℕ}
    (hp : 2 < p) (hd : 2 ≤ d) {chi : ℝ} (hchi : 0 < chi)
    (ell : Point d → ℝ) (hconv : O3.IsConvexObjective ell)
    (hlip : IsOneLipschitz p ell) :
    IsLpSmooth p (repairMpd p d / chi) (repairSelectedOracle p d chi ell) := by
  exact fun x y ↦ repairSelectedGradient_lipschitz hp hd hchi ell hconv hlip x y

end V7.Stage5AboveTwoLowerS5A2Envelope
