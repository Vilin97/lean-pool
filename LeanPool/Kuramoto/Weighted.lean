/-
Copyright (c) 2026 Ben Cassie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Cassie
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import LeanPool.Kuramoto.GradientFlow

/-!
# Weighted Kuramoto model

The weighted Kuramoto potential and vector field, where coupling strengths are given by a
matrix `W`. For the gradient identity the coupling matrix is assumed symmetric.
-/

open Real Finset

/-- The weighted Kuramoto potential
`V = -(K / 2) ∑_{i,j} W i j * cos (θ_j - θ_i)`. -/
noncomputable def weightedKuramotoV (K : ℝ) (N : ℕ) (W : Fin N → Fin N → ℝ)
    (θ : Fin N → ℝ) : ℝ :=
  -(K / 2) * ∑ i : Fin N, ∑ j : Fin N, W i j * Real.cos (θ j - θ i)

/-- The weighted Kuramoto force on oscillator `i`,
`F_i = K ∑_j W i j * sin (θ_j - θ_i)`. -/
noncomputable def weightedKuramotoF (K : ℝ) (N : ℕ) (W : Fin N → Fin N → ℝ)
    (i : Fin N) (θ : Fin N → ℝ) : ℝ :=
  K * ∑ j : Fin N, W i j * Real.sin (θ j - θ i)

private lemma hasDerivAt_update_apply {N : ℕ} (θ : Fin N → ℝ) (i j : Fin N) :
    HasDerivAt (fun x : ℝ => Function.update θ i x j)
      (if j = i then 1 else 0) (θ i) := by
  by_cases h : j = i
  · subst j
    simpa [Function.update_self] using
      (hasDerivAt_id' (θ i) : HasDerivAt (fun x : ℝ => x) 1 (θ i))
  · simpa [h, Function.update_of_ne h] using hasDerivAt_const (θ i) (θ j)

private lemma hasDerivAt_cos_update_sub {N : ℕ} (θ : Fin N → ℝ) (i a b : Fin N) :
    HasDerivAt
      (fun x : ℝ => Real.cos (Function.update θ i x b - Function.update θ i x a))
      (-Real.sin (θ b - θ a) * ((if b = i then 1 else 0) - (if a = i then 1 else 0)))
      (θ i) := by
  have hb := hasDerivAt_update_apply θ i b
  have ha := hasDerivAt_update_apply θ i a
  have hsub :
      HasDerivAt
        ((fun x : ℝ => Function.update θ i x b) -
          fun x : ℝ => Function.update θ i x a)
        ((if b = i then 1 else 0) - (if a = i then 1 else 0))
        (θ i) := by
    exact hb.sub ha
  have hcos := hsub.cos
  simpa [Pi.sub_apply, Function.update_eq_self] using hcos

private noncomputable def pairDeriv {N : ℕ} (θ : Fin N → ℝ) (i a b : Fin N) : ℝ :=
  -Real.sin (θ b - θ a) * ((if b = i then 1 else 0) - (if a = i then 1 else 0))

private lemma weighted_pairDeriv_sum_eq {N : ℕ} (W : Fin N → Fin N → ℝ)
    (hW : ∀ i j, W i j = W j i) (θ : Fin N → ℝ) (i : Fin N) :
    (∑ a : Fin N, ∑ b : Fin N, W a b * pairDeriv θ i a b)
      = 2 * ∑ j : Fin N, W i j * Real.sin (θ j - θ i) := by
  classical
  have hinner (a : Fin N) :
      (∑ b : Fin N, W a b * pairDeriv θ i a b)
        = W a i * Real.sin (θ a - θ i)
          + if a = i then ∑ b : Fin N, W a b * Real.sin (θ b - θ a) else 0 := by
    by_cases ha : a = i
    · subst a
      have hsum :
          (∑ b : Fin N, W i b * pairDeriv θ i i b)
            = ∑ b : Fin N, W i b * Real.sin (θ b - θ i) := by
        apply Finset.sum_congr rfl
        intro b hb
        by_cases hbi : b = i
        · subst b
          simp [pairDeriv]
        · simp [pairDeriv, hbi]
      simpa using hsum
    · have hsin : -Real.sin (θ i - θ a) = Real.sin (θ a - θ i) := by
        have harg : θ i - θ a = -(θ a - θ i) := by ring
        rw [harg, Real.sin_neg]
        ring
      simp only [pairDeriv, ha, ↓reduceIte, sub_zero, mul_ite, mul_one, mul_zero, mul_neg,
        sum_ite_eq', mem_univ, add_zero]
      rw [← hsin]
      ring
  have hsym :
      (∑ a : Fin N, W a i * Real.sin (θ a - θ i))
        = ∑ a : Fin N, W i a * Real.sin (θ a - θ i) := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [hW a i]
  calc
    (∑ a : Fin N, ∑ b : Fin N, W a b * pairDeriv θ i a b)
        = ∑ a : Fin N,
            (W a i * Real.sin (θ a - θ i)
              + if a = i then ∑ b : Fin N, W a b * Real.sin (θ b - θ a) else 0) := by
          simp [hinner]
    _ = (∑ a : Fin N, W a i * Real.sin (θ a - θ i))
          + ∑ a : Fin N,
              (if a = i then ∑ b : Fin N, W a b * Real.sin (θ b - θ a) else 0) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ a : Fin N, W a i * Real.sin (θ a - θ i))
          + ∑ b : Fin N, W i b * Real.sin (θ b - θ i) := by
          simp
    _ = (∑ a : Fin N, W i a * Real.sin (θ a - θ i))
          + ∑ b : Fin N, W i b * Real.sin (θ b - θ i) := by
          rw [hsym]
    _ = 2 * ∑ j : Fin N, W i j * Real.sin (θ j - θ i) := by
          ring

lemma weighted_gradient_identity
    (K : ℝ) (N : ℕ) (W : Fin N → Fin N → ℝ) (hW : ∀ i j, W i j = W j i)
    (θ : Fin N → ℝ) (i : Fin N) :
    weightedKuramotoF K N W i θ =
      -(deriv (fun x => weightedKuramotoV K N W (Function.update θ i x)) (θ i)) := by
  have hsum :
      HasDerivAt
        (fun x : ℝ =>
          ∑ a : Fin N, ∑ b : Fin N,
            W a b * Real.cos (Function.update θ i x b - Function.update θ i x a))
        (∑ a : Fin N, ∑ b : Fin N, W a b * pairDeriv θ i a b)
        (θ i) := by
    have hsum' :
        HasDerivAt
        (∑ a : Fin N, fun x : ℝ =>
          ∑ b : Fin N,
            W a b * Real.cos (Function.update θ i x b - Function.update θ i x a))
        (∑ a : Fin N, ∑ b : Fin N, W a b * pairDeriv θ i a b)
        (θ i) := by
      apply HasDerivAt.sum
      intro a ha
      have hinner' :
          HasDerivAt
            (∑ b : Fin N, fun x : ℝ =>
              W a b * Real.cos (Function.update θ i x b - Function.update θ i x a))
            (∑ b : Fin N, W a b * pairDeriv θ i a b)
            (θ i) := by
        apply HasDerivAt.sum
        intro b hb
        simpa [pairDeriv] using
          (hasDerivAt_cos_update_sub θ i a b).const_mul (W a b)
      exact hinner'.congr_of_eventuallyEq
        (Filter.Eventually.of_forall (by intro x; simp))
    exact hsum'.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (by intro x; simp))
  have hV :
      HasDerivAt
        (fun x : ℝ => weightedKuramotoV K N W (Function.update θ i x))
        (-(K / 2) * (∑ a : Fin N, ∑ b : Fin N, W a b * pairDeriv θ i a b))
        (θ i) := by
    simpa [weightedKuramotoV] using hsum.const_mul (-(K / 2))
  have hderiv :
      deriv (fun x : ℝ => weightedKuramotoV K N W (Function.update θ i x)) (θ i)
        = -(K / 2) * (∑ a : Fin N, ∑ b : Fin N, W a b * pairDeriv θ i a b) :=
    hV.deriv
  rw [hderiv, weighted_pairDeriv_sum_eq W hW θ i]
  simp [weightedKuramotoF]
  ring

lemma weightedKuramotoV_symm_cancel
    (K : ℝ) (N : ℕ) (W : Fin N → Fin N → ℝ) (hW : ∀ i j, W i j = W j i)
    (θ : Fin N → ℝ) :
    ∑ i : Fin N, weightedKuramotoF K N W i θ * weightedKuramotoF K N W i θ =
    -(∑ i : Fin N, weightedKuramotoF K N W i θ *
        deriv (fun x => weightedKuramotoV K N W (Function.update θ i x)) (θ i)) := by
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hgrad := weighted_gradient_identity K N W hW θ i
  have hderiv :
      deriv (fun x => weightedKuramotoV K N W (Function.update θ i x)) (θ i)
        = -weightedKuramotoF K N W i θ := by
    linarith
  rw [hderiv]
  ring

theorem weighted_lyapunov_descent
    (K : ℝ) (_hK : 0 < K) (N : ℕ) (W : Fin N → Fin N → ℝ) (hW : ∀ i j, W i j = W j i)
    (θ : Fin N → ℝ) :
    ∑ i : Fin N, weightedKuramotoF K N W i θ *
        deriv (fun x => weightedKuramotoV K N W (Function.update θ i x)) (θ i) ≤ 0 := by
  apply Finset.sum_nonpos
  intro i hi
  have hgrad := weighted_gradient_identity K N W hW θ i
  have hderiv :
      deriv (fun x => weightedKuramotoV K N W (Function.update θ i x)) (θ i)
        = -weightedKuramotoF K N W i θ := by
    linarith
  rw [hderiv]
  nlinarith [sq_nonneg (weightedKuramotoF K N W i θ)]
