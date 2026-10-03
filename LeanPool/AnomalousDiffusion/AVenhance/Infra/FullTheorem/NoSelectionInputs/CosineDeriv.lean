/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.NoSelectionInputs.CosineIntegral
public import LeanPool.AnomalousDiffusion.Homogenization.Sobolev.WeakDerivatives
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! # Iterated derivatives of `x ↦ c cos(a x₀)` -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance.Infra.FullTheorem.NoSelectionInputs

open AVenhance

theorem iteratedDeriv_cos_mul (a c : ℝ) (k : ℕ) :
    iteratedDeriv k (fun s : ℝ => c * Real.cos (a * s)) =
      fun s => c * a ^ k * Real.cos (a * s + k * (Real.pi / 2)) := by
  induction k with
  | zero => funext s; simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext s
    have hd : HasDerivAt (fun s : ℝ => c * a ^ k * Real.cos (a * s + k * (Real.pi / 2)))
        (c * a ^ k * (-Real.sin (a * s + k * (Real.pi / 2)) * a)) s := by
      have h1 : HasDerivAt (fun s : ℝ => a * s + k * (Real.pi / 2)) a s := by
        simpa using ((hasDerivAt_id s).const_mul a).add_const (k * (Real.pi / 2))
      exact (h1.cos).const_mul (c * a ^ k)
    rw [hd.deriv]
    have : a * s + ((k + 1 : ℕ) : ℝ) * (Real.pi / 2) =
        (a * s + k * (Real.pi / 2)) + Real.pi / 2 := by push_cast; ring
    rw [this, Real.cos_add_pi_div_two, pow_succ]
    ring

theorem contDiff_cosDatum (c a : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => c * Real.cos (a * x 0)) := by
  have h0 : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => x 0) := contDiff_apply ℝ ℝ 0
  exact contDiff_const.mul (Real.contDiff_cos.comp (contDiff_const.mul h0))

theorem iteratedFDeriv_cosDatum (c a : ℝ) (k : ℕ) (x : Vec 2) (m : Fin k → Vec 2) :
    iteratedFDeriv ℝ k (fun x : Vec 2 => c * Real.cos (a * x 0)) x m =
      (∏ j, m j 0) * (c * a ^ k * Real.cos (a * x 0 + k * (Real.pi / 2))) := by
  let p : Vec 2 →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  have hh : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => c * Real.cos (a * s)) :=
    contDiff_const.mul (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id))
  have e : (fun x : Vec 2 => c * Real.cos (a * x 0)) =
      (fun s : ℝ => c * Real.cos (a * s)) ∘ p := rfl
  rw [e, p.iteratedFDeriv_comp_right hh x (by simp)]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, iteratedDeriv_cos_mul]
  simp [p, smul_eq_mul]

theorem prod_basisVec_zero {k : ℕ} (i : Fin k → Fin 2) :
    (∏ j, (basisVec (i j) : Vec 2) 0) = if ∀ j, i j = 0 then 1 else 0 := by
  simp only [basisVec_apply]
  by_cases h : ∀ j, i j = 0
  · simp [h]
  · have h' := h
    push Not at h'
    obtain ⟨j, hj⟩ := h'
    simp only [h, ↓reduceIte]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [Ne.symm hj])

end AVenhance.Infra.FullTheorem.NoSelectionInputs
