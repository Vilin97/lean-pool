/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.JacobianJetBounds

/-! Preserve the exact spatial radius in the all-order fixed-equation induction. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- Normalize the initial and trajectory states by the same positive radius.
The derivative equation retains its constant initial-data operator. -/
theorem amnrNormalizedJacobian_fixed_equation {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Q : E → F} {A : F → F →L[ℝ] F}
    (hQ : ContDiff ℝ (⊤ : ℕ∞) Q) {ε : ℝ} (hε : 0 < ε)
    (R : E →L[ℝ] F)
    (heq : ∀ y, fderiv ℝ Q y = R + (A (Q y)).comp (fderiv ℝ Q y)) (x : E) :
    fderiv ℝ (fun y => ε⁻¹ • Q (ε • y)) x =
      R + (A (ε • (ε⁻¹ • Q (ε • x)))).comp
        (fderiv ℝ (fun y => ε⁻¹ • Q (ε • y)) x) := by
  have hd : fderiv ℝ (fun y => ε⁻¹ • Q (ε • y)) x = fderiv ℝ Q (ε • x) := by
    rw [fderiv_fun_const_smul (f := fun y => Q (ε • y))
      ((hQ.comp (contDiff_id.const_smul ε)).differentiable (by simp) x), fderiv_comp_smul,
          smul_smul,
      inv_mul_cancel₀ hε.ne', one_smul]
  rw [hd, smul_smul, mul_inv_cancel₀ hε.ne', one_smul]
  exact heq (ε • x)

/-- Radius normalization loses no extra spatial derivative: the `(n+1)`-st
solution derivative has exactly radius `ε⁻ⁿ`. -/
theorem amnrJacobianJet_norm_le_of_scaled_fixed_equation {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Q : E → F} {A : F → F →L[ℝ] F}
    (hQ : ContDiff ℝ (⊤ : ℕ∞) Q) (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (R : E →L[ℝ] F) (hR : ‖R‖ ≤ 1)
    (heq : ∀ y, fderiv ℝ Q y = R + (A (Q y)).comp (fderiv ℝ Q y))
    {ε : ℝ} (hε : 0 < ε) (x : E) (hsmall : ‖A (Q x)‖ ≤ 1 / 2)
    {C : ℝ} {N : ℕ}
    (hprimitive : ∀ i, i ≤ N → ‖iteratedFDeriv ℝ i A (Q x)‖ ≤ C * ε⁻¹ ^ i)
    (n : ℕ) (hbudget : n ≤ N) :
    ‖iteratedFDeriv ℝ (n + 1) Q x‖ ≤ amnrJacobianJetConstant C n * ε⁻¹ ^ n := by
  let Qn := fun y : E => ε⁻¹ • Q (ε • y)
  let An := fun y : F => A (ε • y)
  have hQn : ContDiff ℝ (⊤ : ℕ∞) Qn :=
    (hQ.comp (contDiff_id.const_smul ε)).const_smul ε⁻¹
  have hAn : ContDiff ℝ (⊤ : ℕ∞) An := hA.comp (contDiff_id.const_smul ε)
  have hx : ε • (ε⁻¹ • x) = x := by rw [smul_smul, mul_inv_cancel₀ hε.ne', one_smul]
  have hval : ε • Qn (ε⁻¹ • x) = Q x := by
    dsimp [Qn]
    rw [hx, smul_smul, mul_inv_cancel₀ hε.ne', one_smul]
  have hpn : ∀ i, i ≤ N → ‖iteratedFDeriv ℝ i An (Qn (ε⁻¹ • x))‖ ≤ C := by
    intro i hi
    change ‖iteratedFDeriv ℝ i (fun y => A (ε • y)) (Qn (ε⁻¹ • x))‖ ≤ C
    rw [iteratedFDeriv_comp_const_smul ε (hA.of_le (by simp)), norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hε.le i), hval]
    have hc : ε ^ i * (C * ε⁻¹ ^ i) = C := by
      rw [← mul_assoc]
      calc
        ε ^ i * C * ε⁻¹ ^ i = C * (ε * ε⁻¹) ^ i := by rw [mul_pow]; ring
        _ = C := by rw [mul_inv_cancel₀ hε.ne', one_pow, mul_one]
    exact (mul_le_mul_of_nonneg_left (hprimitive i hi) (pow_nonneg hε.le i)).trans_eq hc
  have hsn : ‖An (Qn (ε⁻¹ • x))‖ ≤ 1 / 2 := by
    change ‖A (ε • Qn (ε⁻¹ • x))‖ ≤ _
    rw [hval]
    exact hsmall
  have hh := amnrJacobianJet_norm_le_of_fixed_equation hQn hAn R hR
    (amnrNormalizedJacobian_fixed_equation hQ hε R heq) (ε⁻¹ • x) hsn hpn n hbudget
  have hfd : fderiv ℝ Qn = fun y => fderiv ℝ Q (ε • y) := by
    funext y
    dsimp [Qn]
    rw [fderiv_fun_const_smul (f := fun y => Q (ε • y))
      ((hQ.comp (contDiff_id.const_smul ε)).differentiable (by simp) y), fderiv_comp_smul,
          smul_smul,
      inv_mul_cancel₀ hε.ne', one_smul]
  rw [hfd, iteratedFDeriv_comp_const_smul ε
    ((hQ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).of_le (by simp))] at hh
  simp only [] at hh
  rw [hx,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hε.le n),
    norm_iteratedFDeriv_fderiv] at hh
  have hi := mul_le_mul_of_nonneg_left hh (pow_nonneg (inv_nonneg.mpr hε.le) n)
  have hc : ε⁻¹ ^ n * (ε ^ n * ‖iteratedFDeriv ℝ (n + 1) Q x‖) =
      ‖iteratedFDeriv ℝ (n + 1) Q x‖ := by
    rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hε.ne', one_pow, one_mul]
  rw [hc] at hi
  exact hi.trans_eq (mul_comm _ _)

end AVenhance.Infra.Section4
