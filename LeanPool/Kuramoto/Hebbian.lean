/-
Copyright (c) 2026 Ben Cassie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Cassie
-/

import LeanPool.Kuramoto.Weighted

/-!
# Hebbian phase/weight dynamics

A joint phase/weight Lyapunov function `hebbianL` with a Frobenius weight penalty, the
Hebbian weight flow `hebbianWeightF`, and the joint Lyapunov descent property.
-/

open Real Finset

/-- Update a single weight entry `W i j` to `x` (used to differentiate in that entry). -/
noncomputable def hebbianUpdateWeight {N : ℕ} (W : Fin N → Fin N → ℝ)
    (i j : Fin N) (x : ℝ) : Fin N → Fin N → ℝ :=
  Function.update W i (Function.update (W i) j x)

/-- Joint phase/weight Lyapunov function with a Frobenius weight penalty. -/
noncomputable def hebbianL (K lam : ℝ) (N : ℕ) (W : Fin N → Fin N → ℝ)
    (θ : Fin N → ℝ) : ℝ :=
  weightedKuramotoV K N W θ + (lam / 2) * ∑ i : Fin N, ∑ j : Fin N, W i j * W i j

/-- Unprojected Hebbian weight flow, the negative weight-gradient of `hebbianL`. -/
noncomputable def hebbianWeightF (K lam : ℝ) (N : ℕ) (W : Fin N → Fin N → ℝ)
    (θ : Fin N → ℝ) (i j : Fin N) : ℝ :=
  (K / 2) * Real.cos (θ j - θ i) - lam * W i j

private lemma hasDerivAt_hebbianUpdateWeight_apply {N : ℕ} (W : Fin N → Fin N → ℝ)
    (i j a b : Fin N) :
    HasDerivAt (fun x : ℝ => hebbianUpdateWeight W i j x a b)
      (if a = i ∧ b = j then 1 else 0) (W i j) := by
  by_cases ha : a = i
  · subst a
    by_cases hb : b = j
    · subst b
      simpa [hebbianUpdateWeight, Function.update_self] using
        (hasDerivAt_id' (W i j) : HasDerivAt (fun x : ℝ => x) 1 (W i j))
    · have hb' : j ≠ b := by exact Ne.symm hb
      simpa [hebbianUpdateWeight, hb, Function.update_self, Function.update_of_ne hb'] using
        hasDerivAt_const (W i j) (W i b)
  · have ha' : i ≠ a := by exact Ne.symm ha
    simpa [hebbianUpdateWeight, ha, Function.update_of_ne ha'] using
      hasDerivAt_const (W i j) (W a b)

private lemma weighted_potential_weight_deriv {N : ℕ} (K : ℝ) (W : Fin N → Fin N → ℝ)
    (θ : Fin N → ℝ) (i j : Fin N) :
    HasDerivAt
      (fun x : ℝ => weightedKuramotoV K N (hebbianUpdateWeight W i j x) θ)
      (-(K / 2) * Real.cos (θ j - θ i))
      (W i j) := by
  have hsum :
      HasDerivAt
        (fun x : ℝ =>
          ∑ a : Fin N, ∑ b : Fin N,
            hebbianUpdateWeight W i j x a b * Real.cos (θ b - θ a))
        (Real.cos (θ j - θ i))
        (W i j) := by
    have hsum' :
        HasDerivAt
          (∑ a : Fin N, fun x : ℝ =>
            ∑ b : Fin N, hebbianUpdateWeight W i j x a b * Real.cos (θ b - θ a))
          (∑ a : Fin N, ∑ b : Fin N,
            (if a = i ∧ b = j then 1 else 0) * Real.cos (θ b - θ a))
          (W i j) := by
      apply HasDerivAt.sum
      intro a ha
      have hinner :
          HasDerivAt
            (∑ b : Fin N, fun x : ℝ =>
              hebbianUpdateWeight W i j x a b * Real.cos (θ b - θ a))
            (∑ b : Fin N, (if a = i ∧ b = j then 1 else 0) * Real.cos (θ b - θ a))
            (W i j) := by
        apply HasDerivAt.sum
        intro b hb
        simpa using (hasDerivAt_hebbianUpdateWeight_apply W i j a b).mul_const
          (Real.cos (θ b - θ a))
      exact hinner.congr_of_eventuallyEq
        (Filter.Eventually.of_forall (by intro x; simp))
    have hcollapse :
        (∑ a : Fin N, ∑ b : Fin N,
          (if a = i ∧ b = j then 1 else 0) * Real.cos (θ b - θ a))
          = Real.cos (θ j - θ i) := by
      rw [Finset.sum_eq_single i]
      · rw [Finset.sum_eq_single j]
        · simp
        · intro b hb hbj
          simp [hbj]
        · intro hj
          simp at hj
      · intro a ha hai
        simp [hai]
      · intro hi
        simp at hi
    exact hsum'.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (by intro x; simp)) |>.congr_deriv hcollapse
  simpa [weightedKuramotoV] using hsum.const_mul (-(K / 2))

private lemma weight_penalty_deriv {N : ℕ} (lam : ℝ) (W : Fin N → Fin N → ℝ)
    (i j : Fin N) :
    HasDerivAt
      (fun x : ℝ =>
        (lam / 2) * ∑ a : Fin N, ∑ b : Fin N,
          hebbianUpdateWeight W i j x a b * hebbianUpdateWeight W i j x a b)
      (lam * W i j)
      (W i j) := by
  have hsum :
      HasDerivAt
        (fun x : ℝ =>
          ∑ a : Fin N, ∑ b : Fin N,
            hebbianUpdateWeight W i j x a b * hebbianUpdateWeight W i j x a b)
        (2 * W i j)
        (W i j) := by
    have hsum' :
        HasDerivAt
          (∑ a : Fin N, fun x : ℝ =>
            ∑ b : Fin N, hebbianUpdateWeight W i j x a b * hebbianUpdateWeight W i j x a b)
          (∑ a : Fin N, ∑ b : Fin N,
            ((if a = i ∧ b = j then 1 else 0) * W a b
              + W a b * (if a = i ∧ b = j then 1 else 0)))
          (W i j) := by
      apply HasDerivAt.sum
      intro a ha
      have hinner :
          HasDerivAt
            (∑ b : Fin N, fun x : ℝ =>
              hebbianUpdateWeight W i j x a b * hebbianUpdateWeight W i j x a b)
            (∑ b : Fin N,
              ((if a = i ∧ b = j then 1 else 0) * W a b
                + W a b * (if a = i ∧ b = j then 1 else 0)))
            (W i j) := by
        apply HasDerivAt.sum
        intro b hb
        have h := hasDerivAt_hebbianUpdateWeight_apply W i j a b
        have hmul := h.mul h
        simpa [hebbianUpdateWeight] using hmul.congr_of_eventuallyEq
          (Filter.Eventually.of_forall (by intro x; rfl))
      exact hinner.congr_of_eventuallyEq
        (Filter.Eventually.of_forall (by intro x; simp))
    have hcollapse :
        (∑ a : Fin N, ∑ b : Fin N,
          ((if a = i ∧ b = j then 1 else 0) * W a b
            + W a b * (if a = i ∧ b = j then 1 else 0)))
          = 2 * W i j := by
      rw [Finset.sum_eq_single i]
      · rw [Finset.sum_eq_single j]
        · simp
          ring_nf
        · intro b hb hbj
          simp [hbj]
        · intro hj
          simp at hj
      · intro a ha hai
        simp [hai]
      · intro hi
        simp at hi
    exact hsum'.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (by intro x; simp)) |>.congr_deriv hcollapse
  have hscaled := hsum.const_mul (lam / 2)
  have hval : lam * W i j = lam / 2 * (2 * W i j) := by ring
  rw [hval]
  exact hscaled

theorem hebbian_weight_gradient_identity
    (K lam : ℝ) (N : ℕ) (W : Fin N → Fin N → ℝ)
    (θ : Fin N → ℝ) (i j : Fin N) :
    hebbianWeightF K lam N W θ i j =
      -(deriv (fun x => hebbianL K lam N (hebbianUpdateWeight W i j x) θ) (W i j)) := by
  have hV := weighted_potential_weight_deriv K W θ i j
  have hP := weight_penalty_deriv lam W i j
  have hL :
      HasDerivAt
        (fun x : ℝ => hebbianL K lam N (hebbianUpdateWeight W i j x) θ)
        (-(K / 2) * Real.cos (θ j - θ i) + lam * W i j)
        (W i j) := by
    exact (hV.add hP).congr_of_eventuallyEq
      (Filter.Eventually.of_forall (by intro x; simp [hebbianL]))
  have hderiv :
      deriv (fun x : ℝ => hebbianL K lam N (hebbianUpdateWeight W i j x) θ) (W i j)
        = -(K / 2) * Real.cos (θ j - θ i) + lam * W i j :=
    hL.deriv
  rw [hderiv]
  simp [hebbianWeightF]
  ring

theorem hebbian_phase_gradient_identity
    (K lam : ℝ) (N : ℕ) (W : Fin N → Fin N → ℝ) (hW : ∀ i j, W i j = W j i)
    (θ : Fin N → ℝ) (i : Fin N) :
    weightedKuramotoF K N W i θ =
      -(deriv (fun x => hebbianL K lam N W (Function.update θ i x)) (θ i)) := by
  have hV := weighted_gradient_identity K N W hW θ i
  have hderivL :
      deriv (fun x => hebbianL K lam N W (Function.update θ i x)) (θ i)
        = deriv (fun x => weightedKuramotoV K N W (Function.update θ i x)) (θ i) := by
    simp [hebbianL]
  rw [hderivL]
  exact hV

theorem hebbian_joint_lyapunov_descent
    (K lam : ℝ) (N : ℕ) (W : Fin N → Fin N → ℝ) (hW : ∀ i j, W i j = W j i)
    (θ : Fin N → ℝ) :
    (∑ i : Fin N, weightedKuramotoF K N W i θ *
        deriv (fun x => hebbianL K lam N W (Function.update θ i x)) (θ i))
      + (∑ i : Fin N, ∑ j : Fin N, hebbianWeightF K lam N W θ i j *
        deriv (fun x => hebbianL K lam N (hebbianUpdateWeight W i j x) θ) (W i j)) ≤ 0 := by
  apply add_nonpos
  · apply Finset.sum_nonpos
    intro i hi
    have hgrad := hebbian_phase_gradient_identity K lam N W hW θ i
    have hderiv :
        deriv (fun x => hebbianL K lam N W (Function.update θ i x)) (θ i)
          = -weightedKuramotoF K N W i θ := by
      linarith
    rw [hderiv]
    nlinarith [sq_nonneg (weightedKuramotoF K N W i θ)]
  · apply Finset.sum_nonpos
    intro i hi
    apply Finset.sum_nonpos
    intro j hj
    have hgrad := hebbian_weight_gradient_identity K lam N W θ i j
    have hderiv :
        deriv (fun x => hebbianL K lam N (hebbianUpdateWeight W i j x) θ) (W i j)
          = -hebbianWeightF K lam N W θ i j := by
      linarith
    rw [hderiv]
    nlinarith [sq_nonneg (hebbianWeightF K lam N W θ i j)]
