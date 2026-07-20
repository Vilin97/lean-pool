/-
Copyright (c) 2026 Ben Cassie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Cassie
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import LeanPool.Kuramoto.OrderParameter

/-!
# Kuramoto gradient flow

The Kuramoto potential `kuramotoV` and force field `kuramotoF`, together with the
gradient identity expressing the force as the negative phase-derivative of the potential.
-/

open Real Finset

/-- The Kuramoto potential `V = -(K / (2N)) ∑_{i,j} cos (θ_j - θ_i)`. -/
noncomputable def kuramotoV (K : ℝ) (N : ℕ) (θ : Fin N → ℝ) : ℝ :=
  -(K / (2 * N)) * ∑ i : Fin N, ∑ j : Fin N, Real.cos (θ j - θ i)

/-- The Kuramoto force on oscillator `i`, `F_i = (K / N) ∑_j sin (θ_j - θ_i)`. -/
noncomputable def kuramotoF (K : ℝ) (N : ℕ) (i : Fin N) (θ : Fin N → ℝ) : ℝ :=
  (K / N) * ∑ j : Fin N, Real.sin (θ j - θ i)

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

private lemma pairDeriv_sum_eq {N : ℕ} (θ : Fin N → ℝ) (i : Fin N) :
    (∑ a : Fin N, ∑ b : Fin N, pairDeriv θ i a b)
      = 2 * ∑ j : Fin N, Real.sin (θ j - θ i) := by
  classical
  have hinner (a : Fin N) :
      (∑ b : Fin N, pairDeriv θ i a b)
        = Real.sin (θ a - θ i)
          + if a = i then ∑ b : Fin N, Real.sin (θ b - θ a) else 0 := by
    by_cases ha : a = i
    · subst a
      have hsum :
          (∑ b : Fin N, pairDeriv θ i i b)
            = ∑ b : Fin N, Real.sin (θ b - θ i) := by
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
      simp [pairDeriv, ha, hsin]
  calc
    (∑ a : Fin N, ∑ b : Fin N, pairDeriv θ i a b)
        = ∑ a : Fin N,
            (Real.sin (θ a - θ i)
              + if a = i then ∑ b : Fin N, Real.sin (θ b - θ a) else 0) := by
          simp [hinner]
    _ = (∑ a : Fin N, Real.sin (θ a - θ i))
          + ∑ a : Fin N, (if a = i then ∑ b : Fin N, Real.sin (θ b - θ a) else 0) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ a : Fin N, Real.sin (θ a - θ i))
          + ∑ b : Fin N, Real.sin (θ b - θ i) := by
          simp
    _ = 2 * ∑ j : Fin N, Real.sin (θ j - θ i) := by
          ring

theorem kuramoto_gradient_identity
    (K : ℝ) (N : ℕ) (hN : 0 < N) (hK : 0 < K)
    (θ : Fin N → ℝ) (i : Fin N) :
    kuramotoF K N i θ = -(deriv (fun x => kuramotoV K N (Function.update θ i x)) (θ i)) := by
  have hsum :
      HasDerivAt
        (fun x : ℝ =>
          ∑ a : Fin N, ∑ b : Fin N,
            Real.cos (Function.update θ i x b - Function.update θ i x a))
        (∑ a : Fin N, ∑ b : Fin N, pairDeriv θ i a b)
        (θ i) := by
    have hsum' :
        HasDerivAt
        (∑ a : Fin N, fun x : ℝ =>
          ∑ b : Fin N, Real.cos (Function.update θ i x b - Function.update θ i x a))
        (∑ a : Fin N, ∑ b : Fin N, pairDeriv θ i a b)
        (θ i) := by
      apply HasDerivAt.sum
      intro a ha
      have hinner' :
          HasDerivAt
            (∑ b : Fin N, fun x : ℝ =>
              Real.cos (Function.update θ i x b - Function.update θ i x a))
            (∑ b : Fin N, pairDeriv θ i a b)
            (θ i) := by
        apply HasDerivAt.sum
        intro b hb
        simpa [pairDeriv] using hasDerivAt_cos_update_sub θ i a b
      exact hinner'.congr_of_eventuallyEq
        (Filter.Eventually.of_forall (by intro x; simp))
    exact hsum'.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (by intro x; simp))
  have hV :
      HasDerivAt
        (fun x : ℝ => kuramotoV K N (Function.update θ i x))
        (-(K / (2 * N)) * (∑ a : Fin N, ∑ b : Fin N, pairDeriv θ i a b))
        (θ i) := by
    simpa [kuramotoV] using hsum.const_mul (-(K / (2 * (N : ℝ))))
  have hderiv :
      deriv (fun x : ℝ => kuramotoV K N (Function.update θ i x)) (θ i)
        = -(K / (2 * N)) * (∑ a : Fin N, ∑ b : Fin N, pairDeriv θ i a b) :=
    hV.deriv
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [hderiv, pairDeriv_sum_eq]
  simp [kuramotoF]
  field_simp [hN']
