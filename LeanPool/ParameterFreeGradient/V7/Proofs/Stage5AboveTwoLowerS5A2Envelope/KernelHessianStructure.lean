/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerS5A2Envelope.ConditionalSmoothness
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

namespace V7.Stage5AboveTwoLowerS5A2Envelope

open Stage5AboveTwoLower
open Stage5AboveTwoLower.S5ARepair
open Stage5AboveTwoLower.S5AGlobalC2

/-- Symmetry of the concrete Hessian, obtained from the actual second
Fréchet derivative rather than from an asserted matrix property. -/
lemma kernelHessian_pairing_symmetric {r theta : ℝ}
    (hr : 2 < r) (htheta : 1 < theta) (htr : 2 * theta < r)
    {d : ℕ} (x e f : Point d) :
    O3.pairing e (kernelHessian r theta x f) =
      O3.pairing f (kernelHessian r theta x e) := by
  have hs := second_derivative_symmetric
    (f := lowerKernelPhi (d := d) r theta)
    (f' := kernelFDeriv (d := d) r theta)
    (f'' := kernelFDerivDerivative (d := d) r theta x)
    (fun y ↦ hasFDerivAt_lowerKernelPhi hr htheta htr y)
    (hasFDerivAt_kernelFDeriv hr htheta htr x) f e
  simpa [kernelFDerivDerivative, pairingCLMCLM_apply, pairingCLM_apply,
    O3.pairing_comm] using hs

/-- Positive semidefiniteness of the concrete Hessian.  Convexity makes the
first derivative along every affine line monotone; differentiating that
monotone scalar function gives the Hessian quadratic form. -/
lemma kernelHessian_quadratic_nonneg {r theta : ℝ}
    (hr : 2 < r) (htheta : 1 < theta) (htr : 2 * theta < r)
    {d : ℕ} (x e : Point d) :
    0 ≤ O3.pairing e (kernelHessian r theta x e) := by
  let line : ℝ → ℝ :=
    O3.Stage3Anchor.objectiveLine (lowerKernelPhi (d := d) r theta) x (x + e)
  let lineGrad : ℝ → ℝ := fun t ↦
    O3.pairing (kernelGradientVector r theta
      (AffineMap.lineMap x (x + e) t)) e
  have hconvLine : ConvexOn ℝ Set.univ line := by
    have hc := (lowerKernelPhi_convex (d := d)
      (by linarith : 1 ≤ r) htheta).comp_affineMap
        (AffineMap.lineMap x (x + e))
    change ConvexOn ℝ Set.univ
      ((lowerKernelPhi (d := d) r theta) ∘ AffineMap.lineMap x (x + e))
    simpa only [Set.preimage_univ] using hc
  have hlineDeriv (t : ℝ) : HasDerivAt line (lineGrad t) t := by
    have h := O3.Stage3Anchor.hasDerivAt_objectiveLine
      (lowerKernelPhi_coordinateGradient (d := d) hr htheta htr) x (x + e) t
    simpa [line, lineGrad] using h
  have hmonoDeriv : Monotone (deriv line) := by
    have hm := hconvLine.monotoneOn_deriv
      (fun t _ ↦ (hlineDeriv t).differentiableAt)
    intro a b hab
    exact hm (Set.mem_univ a) (Set.mem_univ b) hab
  have hderivEq : deriv line = lineGrad := by
    funext t
    exact (hlineDeriv t).deriv
  have hmonoGrad : Monotone lineGrad := by
    rw [← hderivEq]
    exact hmonoDeriv
  have hsecond : HasDerivAt lineGrad
      (O3.pairing (kernelHessian r theta x e) e) 0 := by
    have hpath := AffineMap.hasDerivAt_lineMap
      (a := x) (b := x + e) (x := (0 : ℝ))
    have hgRaw := (hasFDerivAt_kernelGradientVector hr htheta htr
      (AffineMap.lineMap x (x + e) 0)).comp 0 hpath.hasFDerivAt
    have hg : HasFDerivAt
        (kernelGradientVector r theta ∘ AffineMap.lineMap x (x + e))
        ((kernelHessian r theta x).comp
          (ContinuousLinearMap.toSpanSingleton ℝ e)) 0 := by
      simpa using hgRaw
    have hp := (pairingCLM e).hasFDerivAt.comp 0 hg
    simpa [lineGrad, Function.comp_def, pairingCLM_apply,
      ContinuousLinearMap.toSpanSingleton_apply, O3.pairing_comm] using
        hp.hasDerivAt
  have hn := hmonoGrad.deriv_nonneg (x := (0 : ℝ))
  rw [hsecond.deriv] at hn
  simpa [O3.pairing_comm] using hn

/-- Cauchy--Schwarz for a symmetric positive-semidefinite Hessian form.  This
is the local algebraic wheel needed to retain the exact Banach-space constant
without passing through the ambient Euclidean operator norm. -/
lemma psd_pairing_cauchy_schwarz (H : Point d →L[ℝ] Point d)
    (hsymm : ∀ e f, O3.pairing e (H f) = O3.pairing f (H e))
    (hpos : ∀ e, 0 ≤ O3.pairing e (H e)) (e f : Point d) :
    O3.pairing e (H f) ^ (2 : ℕ) ≤
      O3.pairing e (H e) * O3.pairing f (H f) := by
  let A : ℝ := O3.pairing e (H e)
  let C : ℝ := O3.pairing f (H f)
  let X : ℝ := O3.pairing e (H f)
  have hA : 0 ≤ A := hpos e
  have hC : 0 ≤ C := hpos f
  have hquad (u v : Point d) (t : ℝ) :
      O3.pairing (u + t • v) (H (u + t • v)) =
        O3.pairing u (H u) +
          t * O3.pairing u (H v) +
          t * O3.pairing v (H u) +
          t ^ (2 : ℕ) * O3.pairing v (H v) := by
    simp only [map_add, map_smul, O3.pairing, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rcases hA.eq_or_lt with hAzero | hApos
  · rcases hC.eq_or_lt with hCzero | hCpos
    · have hplus := hpos (e + f)
      have hminus := hpos (e - f)
      have hp : O3.pairing (e + f) (H (e + f)) =
          O3.pairing e (H e) + O3.pairing e (H f) +
            O3.pairing f (H e) + O3.pairing f (H f) := by
        simpa using hquad e f 1
      have hm : O3.pairing (e - f) (H (e - f)) =
          O3.pairing e (H e) - O3.pairing e (H f) -
            O3.pairing f (H e) + O3.pairing f (H f) := by
        have h := hquad e (-f) 1
        simpa [sub_eq_add_neg, O3.pairing, hsymm] using h
      have hsym := hsymm e f
      dsimp [A, C, X] at hAzero hCzero ⊢
      rw [hp] at hplus
      rw [hm] at hminus
      nlinarith
    · let t : ℝ := -(X / C)
      have hz := hpos (e + t • f)
      rw [hquad] at hz
      have hsym := hsymm e f
      have hform : O3.pairing e (H e) +
            t * O3.pairing e (H f) +
            t * O3.pairing f (H e) +
            t ^ (2 : ℕ) * O3.pairing f (H f) =
          A - X ^ (2 : ℕ) / C := by
        dsimp [A, C, X, t]
        rw [hsym]
        field_simp [hCpos.ne']
        ring
      rw [hform] at hz
      have hdiv : X ^ (2 : ℕ) / C ≤ A := by linarith
      have hm := (div_le_iff₀ hCpos).mp hdiv
      dsimp [A, C, X] at hm ⊢
      nlinarith
  · let t : ℝ := -(X / A)
    have hz := hpos (f + t • e)
    rw [hquad] at hz
    have hsym := hsymm e f
    have hform : O3.pairing f (H f) +
          t * O3.pairing f (H e) +
          t * O3.pairing e (H f) +
          t ^ (2 : ℕ) * O3.pairing e (H e) =
        C - X ^ (2 : ℕ) / A := by
      dsimp [A, C, X, t]
      rw [← hsym]
      field_simp [hApos.ne']
      ring
    rw [hform] at hz
    have hdiv : X ^ (2 : ℕ) / A ≤ C := by linarith
    have hm := (div_le_iff₀ hApos).mp hdiv
    dsimp [A, C, X] at hm ⊢
    nlinarith

/-- Pointwise Hessian Cauchy--Schwarz for the concrete kernel. -/
lemma kernelHessian_cauchy_schwarz {r theta : ℝ}
    (hr : 2 < r) (htheta : 1 < theta) (htr : 2 * theta < r)
    {d : ℕ} (x e f : Point d) :
    O3.pairing e (kernelHessian r theta x f) ^ (2 : ℕ) ≤
      O3.pairing e (kernelHessian r theta x e) *
        O3.pairing f (kernelHessian r theta x f) := by
  exact psd_pairing_cauchy_schwarz (kernelHessian r theta x)
    (kernelHessian_pairing_symmetric hr htheta htr x)
    (kernelHessian_quadratic_nonneg hr htheta htr x) e f

end V7.Stage5AboveTwoLowerS5A2Envelope
