/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FlowCoefficientBounds

/-! Operator bounds extracted from actual source coordinate derivatives. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- On the actual `Vec 2` carrier, an `n`-linear operator costs at most
`2^n` times the largest coordinate evaluation. The target may be any normed
real space, including a higher derivative operator space. -/
theorem amnr_multilinear_norm_le_two_pow_basis {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (n : ℕ)
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin n => Vec 2) F)
    {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ α : Fin n → Fin 2, ‖L (fun j => basisVec (α j))‖ ≤ B) :
    ‖L‖ ≤ (2 : ℝ) ^ n * B := by
  induction n with
  | zero =>
    simpa using h (fun j => Fin.elim0 j)
  | succ n ih =>
    let C := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => Vec 2) F
    have hnorm : ‖L‖ = ‖C L‖ := (C.norm_map L).symm
    rw [hnorm]
    have hpoint (i : Fin 2) : ‖C L (basisVec i)‖ ≤ (2 : ℝ) ^ n * B := by
      apply ih (C L (basisVec i))
      intro α
      have hh := h (Fin.cons i α)
      change ‖L (Fin.cons (basisVec i) (fun j => basisVec (α j)))‖ ≤ B
      convert hh using 2
      congr 1
      funext j
      refine Fin.cases rfl (fun _ => rfl) j
    exact (amnr_clm_norm_le_two_basis_general (by positivity) hpoint).trans_eq (by
      rw [pow_succ]
      ring)

/-- Tuple-indexed spatial words give the actual iterated derivative without
introducing a separate higher-derivative carrier. -/
theorem amnrSpaceWord_ofFn_eq_iteratedFDeriv {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) (α : Fin n → Fin 2) :
    amnrSpaceWord (List.ofFn α) f =
      fun x => iteratedFDeriv ℝ n f x (fun j => basisVec (α j)) := by
  induction n with
  | zero =>
    funext x
    simp only [List.ofFn_zero, amnrSpaceWord, iteratedFDeriv_zero_apply]
  | succ n ih =>
    rw [List.ofFn_succ, amnrSpaceWord, ih]
    funext x
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ n f) x :=
      hf.differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top n) x
    exact (hd.iteratedFDeriv_succ_apply_left' (m := fun j => basisVec (α j))).symm

/-- Coordinate spatial-word bounds control the norm of the actual iterated
Frechet derivative, uniformly over every derivative order. -/
theorem amnr_iteratedFDeriv_norm_le_of_spatial_words {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) (x : Vec 2) {B : ℝ} (hB : 0 ≤ B)
    (hword : ∀ α : List (Fin 2), α.length = n → |amnrSpaceWord α f x| ≤ B) :
    ‖iteratedFDeriv ℝ n f x‖ ≤ (2 : ℝ) ^ n * B := by
  apply amnr_multilinear_norm_le_two_pow_basis n _ hB
  intro α
  have hh := hword (List.ofFn α) (List.length_ofFn)
  rw [amnrSpaceWord_ofFn_eq_iteratedFDeriv hf] at hh
  simpa only [Real.norm_eq_abs] using hh

end AVenhance.Infra.Section4
