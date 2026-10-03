/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.IsThetaAnalytic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.HMinusOneErgodicCore
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.FrozenBridge

/-! # bridge analyticity to Fourier derivative bounds

This module connects the ordered directional derivative bounds to the
coordinate derivative bounds used by the existing Parseval tail estimate. -/

@[expose] public section

noncomputable section

open MeasureTheory
open Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance.Infra.Torus
open AVenhance.Infra.Ergodic

/-- Iterate real differentiation in a fixed spatial coordinate. -/
def AnalyticTail.realCoordIter (i : Fin 2) : ℕ → (Vec 2 → ℝ) → Vec 2 → ℝ
  | 0, f => f
  | n + 1, f => fun x => fderiv ℝ (AnalyticTail.realCoordIter i n f) x (basisVec i)

theorem AnalyticTail.realCoordIter_contDiff_top (i : Fin 2) (n : ℕ)
    {f : Vec 2 → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (AnalyticTail.realCoordIter i n f) := by
  induction n with
  | zero => simpa [AnalyticTail.realCoordIter] using hf
  | succ n ih =>
      have h := ih.contDiff_fderiv_apply (m := ∞) (by simp)
      have hc : ContDiff ℝ ∞ (fun x : Vec 2 => (x, basisVec i)) :=
        contDiff_id.prodMk contDiff_const
      convert h.comp hc using 1
      ext x
      rfl

theorem AnalyticTail.realCoordIter_eq_iteratedFDeriv
    (i : Fin 2) {f : Vec 2 → ℝ} (hf : ContDiff ℝ ∞ f) :
    ∀ n (x : Vec 2),
    AnalyticTail.realCoordIter i n f x =
      iteratedFDeriv ℝ n f x (fun _ : Fin n => basisVec i) := by
  intro n
  induction n with
  | zero =>
      intro x
      rfl
  | succ n ih =>
      intro x
      rw [AnalyticTail.realCoordIter, iteratedFDeriv_succ_apply_left]
      have htail : Fin.tail (fun _ : Fin (n + 1) => basisVec i) =
          (fun _ : Fin n => basisVec i) := by
        funext j
        rfl
      rw [htail]
      have hiter : ContDiff ℝ 1 (iteratedFDeriv ℝ n f) :=
        hf.iteratedFDeriv_right (i := n) (m := 1)
          (n := (⊤ : ℕ∞)) (by simp)
      have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ n f) x :=
        (hiter.differentiable (by norm_num)) x
      have hcontract :
          (fun y : Vec 2 =>
            iteratedFDeriv ℝ n f y (fun _ : Fin n => basisVec i)) =
            AnalyticTail.realCoordIter i n f := by
        funext y
        exact (ih y).symm
      have hderiv := congrArg
        (fun q : Vec 2 → ℝ => fderiv ℝ q x (basisVec i)) hcontract
      change fderiv ℝ (AnalyticTail.realCoordIter i n f) x (basisVec i) = _
      have happly := fderiv_continuousMultilinear_apply_const_apply hdiff
        (fun _ : Fin n => basisVec i) (basisVec i)
      exact hderiv.symm.trans happly

theorem AnalyticTail.coordDerivIter_realToComplex
    (i : Fin 2) {f : Vec 2 → ℝ} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    coordDerivIter i n (realToComplex f) =
      fun x => (AnalyticTail.realCoordIter i n f x : ℂ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      funext x
      rw [coordDerivIter, ih]
      have hreal := AnalyticTail.realCoordIter_contDiff_top i n hf
      have hcast :
          (fun y => (AnalyticTail.realCoordIter i n f y : ℂ)) =
            realToComplex (AnalyticTail.realCoordIter i n f) := rfl
      rw [hcast, coordDeriv_realToComplex (hreal.of_le (by simp))]
      simp [AVenhance.spaceGrad, AnalyticTail.realCoordIter]

end AVenhance.Infra.Section5.RelativeError

end
