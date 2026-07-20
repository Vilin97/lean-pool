/-
Copyright (c) 2026 Ben Cassie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Cassie
-/

import LeanPool.Kuramoto.Weighted
import LeanPool.Kuramoto.Hebbian

/-!
# Connections between the models

Relations between the weighted Kuramoto potential and the Hebbian Lyapunov function: with
zero weight regularisation they coincide, and the Hebbian penalty is convex in each weight.
-/

open Real Finset

/-- With zero weight regularisation, the Hebbian Lyapunov function is exactly the weighted
Kuramoto potential under the full double-sum convention used here. -/
lemma hebbianL_zero_lam_eq_weighted
    (K : ℝ) (N : ℕ) (W : Fin N → Fin N → ℝ) (_hW : ∀ i j, W i j = W j i)
    (θ : Fin N → ℝ) :
    hebbianL K 0 N W θ = weightedKuramotoV K N W θ := by
  simp [hebbianL]

private lemma hebbianUpdateWeight_self {N : ℕ} (W : Fin N → Fin N → ℝ)
    (i j : Fin N) (x : ℝ) :
    hebbianUpdateWeight W i j x i j = x := by
  simp [hebbianUpdateWeight, Function.update_self]

private lemma hebbianUpdateWeight_update_same {N : ℕ} (W : Fin N → Fin N → ℝ)
    (i j : Fin N) (x y : ℝ) :
    hebbianUpdateWeight (hebbianUpdateWeight W i j x) i j y =
      hebbianUpdateWeight W i j y := by
  funext a b
  by_cases ha : a = i
  · subst a
    by_cases hb : b = j
    · subst b
      simp [hebbianUpdateWeight, Function.update_self]
    · simp [hebbianUpdateWeight, hb, Function.update_self]
  · simp [hebbianUpdateWeight, ha]

private lemma hebbianL_weight_entry_deriv
    (K lam : ℝ) (N : ℕ) (W : Fin N → Fin N → ℝ)
    (θ : Fin N → ℝ) (i j : Fin N) (x : ℝ) :
    deriv (fun y => hebbianL K lam N (hebbianUpdateWeight W i j y) θ) x =
      lam * x - (K / 2) * Real.cos (θ j - θ i) := by
  have hgrad :=
    hebbian_weight_gradient_identity K lam N (hebbianUpdateWeight W i j x) θ i j
  have hpoint : hebbianUpdateWeight W i j x i j = x :=
    hebbianUpdateWeight_self W i j x
  have hfun :
      (fun y => hebbianL K lam N
        (hebbianUpdateWeight (hebbianUpdateWeight W i j x) i j y) θ)
        = fun y => hebbianL K lam N (hebbianUpdateWeight W i j y) θ := by
    funext y
    rw [hebbianUpdateWeight_update_same W i j x y]
  rw [hfun, hpoint] at hgrad
  rw [← neg_eq_iff_eq_neg] at hgrad
  rw [← hgrad]
  simp [hebbianWeightF, hebbianUpdateWeight_self]

lemma hebbianL_convex_weight_entry
    (K lam : ℝ) (hlam : 0 < lam) (N : ℕ) (W : Fin N → Fin N → ℝ)
    (θ : Fin N → ℝ) (i j : Fin N) :
    0 < deriv (fun x => deriv (fun y => hebbianL K lam N (hebbianUpdateWeight W i j y) θ) x)
              (W i j) := by
  have hfun :
      (fun x => deriv (fun y => hebbianL K lam N (hebbianUpdateWeight W i j y) θ) x)
        = fun x => lam * x - (K / 2) * Real.cos (θ j - θ i) := by
    funext x
    exact hebbianL_weight_entry_deriv K lam N W θ i j x
  rw [hfun]
  have hderiv :
      deriv (fun x : ℝ => lam * x - (K / 2) * Real.cos (θ j - θ i)) (W i j) = lam := by
    have hshape :
        (fun x : ℝ => lam * x - (K / 2) * Real.cos (θ j - θ i))
          = fun x : ℝ => lam * x + -(K / 2) * Real.cos (θ j - θ i) := by
      funext x
      ring
    rw [hshape]
    rw [deriv_add_const]
    rw [deriv_const_mul]
    · simp
    · exact differentiableAt_id
  rw [hderiv]
  exact hlam
