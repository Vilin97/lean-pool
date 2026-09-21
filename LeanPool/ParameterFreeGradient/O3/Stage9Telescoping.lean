/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.O3.Foundation
import LeanPool.ParameterFreeGradient.O3.Stage2RouteC
import LeanPool.ParameterFreeGradient.O3.Stage2RouteD

/-!
# Stage 9: generic Euclidean telescoping algebra

These lemmas contain no OGM-G certificate assumption.  They expose the
recursively generated auxiliary `p` sequence and the exact polarization used
by the finite-data identity.
-/

open scoped BigOperators

namespace O3

noncomputable def stage9WeightedGradient {d : ℕ}
    (delta : ℕ → ℝ) (g : ℕ → Vec d) (k : ℕ) : Vec d :=
  ∑ j ∈ Finset.range k, delta j • g j

theorem pairing_finset_sum_left {d : ℕ} {α : Type*}
    (s : Finset α) (f : α → Vec d) (x : Vec d) :
    pairing (∑ i ∈ s, f i) x = ∑ i ∈ s, pairing (f i) x := by
  classical
  induction s using Finset.induction with
  | empty => simp [pairing]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [Stage2RouteD.pairing_add_left, ih]

theorem pairing_sub_left {d : ℕ} (x y z : Vec d) :
    pairing (x - y) z = pairing x z - pairing y z := by
  unfold pairing
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.sub_apply]
  ring

theorem pairing_neg_right' {d : ℕ} (x y : Vec d) :
    pairing x (-y) = -pairing x y := by
  exact pairing_neg_right x y

theorem stage9WeightedGradient_succ {d : ℕ}
    (delta : ℕ → ℝ) (g : ℕ → Vec d) (k : ℕ) :
    stage9WeightedGradient delta g (k + 1) =
      stage9WeightedGradient delta g k + delta k • g k := by
  simp [stage9WeightedGradient, Finset.sum_range_succ]

/-- Discrete summation by parts for the second pairing sum in the frozen
certificate. -/
theorem stage9_pairing_summation_by_parts {d : ℕ}
    (delta : ℕ → ℝ) (g v : ℕ → Vec d) : ∀ n,
    (∑ i ∈ Finset.range n,
        delta i * pairing (g i) (v n - v i)) =
      ∑ k ∈ Finset.range n,
        pairing (stage9WeightedGradient delta g (k + 1))
          (v (k + 1) - v k) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hshift :
          (∑ i ∈ Finset.range n,
              delta i * pairing (g i) (v (n + 1) - v i)) =
            (∑ i ∈ Finset.range n,
              delta i * pairing (g i) (v n - v i)) +
              pairing (stage9WeightedGradient delta g n)
                (v (n + 1) - v n) := by
        calc
          (∑ i ∈ Finset.range n,
              delta i * pairing (g i) (v (n + 1) - v i)) =
              ∑ i ∈ Finset.range n,
                (delta i * pairing (g i) (v n - v i) +
                  pairing (delta i • g i) (v (n + 1) - v n)) := by
                    apply Finset.sum_congr rfl
                    intro i _
                    have hvec : v (n + 1) - v i =
                        (v n - v i) + (v (n + 1) - v n) := by
                      funext j
                      simp only [Pi.sub_apply, Pi.add_apply]
                      ring
                    rw [hvec, Stage2RouteD.pairing_add_right,
                      Stage2RouteD.pairing_smul_left]
                    ring
          _ = (∑ i ∈ Finset.range n,
                delta i * pairing (g i) (v n - v i)) +
              ∑ i ∈ Finset.range n,
                pairing (delta i • g i) (v (n + 1) - v n) := by
                  rw [Finset.sum_add_distrib]
          _ = _ := by
            rw [← pairing_finset_sum_left]
            rfl
      rw [hshift, ih, stage9WeightedGradient_succ]
      rw [Stage2RouteD.pairing_add_left,
        Stage2RouteD.pairing_smul_left]
      ring

/-- The auxiliary sequence from the frozen OGM-G certificate. -/
noncomputable def stage9P {d : ℕ} (theta : ℕ → ℝ)
    (g : ℕ → Vec d) : ℕ → Vec d
  | 0 => 0
  | k + 1 => (1 - 1 / theta k) • stage9P theta g k +
      (1 / theta k) • g k

@[simp] theorem stage9P_zero {d : ℕ} (theta : ℕ → ℝ) (g : ℕ → Vec d) :
    stage9P theta g 0 = 0 := rfl

@[simp] theorem stage9P_succ {d : ℕ} (theta : ℕ → ℝ)
    (g : ℕ → Vec d) (k : ℕ) :
    stage9P theta g (k + 1) =
      (1 - 1 / theta k) • stage9P theta g k +
        (1 / theta k) • g k := rfl

theorem stage9P_one {d : ℕ} {theta : ℕ → ℝ} {g : ℕ → Vec d} :
    stage9P theta g 1 = (1 / theta 0) • g 0 := by
  simp [stage9P]

/-- Rearranged auxiliary recurrence, with every division justified. -/
theorem stage9P_gradient_eq {d : ℕ} {theta : ℕ → ℝ} {g : ℕ → Vec d}
    {k : ℕ} (hθ : theta k ≠ 0) :
    g k = theta k • stage9P theta g (k + 1) -
      (theta k - 1) • stage9P theta g k := by
  funext i
  simp only [stage9P_succ, Pi.sub_apply, Pi.smul_apply, Pi.add_apply,
    smul_eq_mul]
  field_simp [hθ]
  ring

/-- Since `theta_n=1`, the source endpoint is genuinely `p_(n+1)=g_n`. -/
theorem stage9P_endpoint {d : ℕ} {theta : ℕ → ℝ} {g : ℕ → Vec d}
    {n : ℕ} (hθn : theta n = 1) :
    stage9P theta g (n + 1) = g n := by
  rw [stage9P_succ, hθn]
  simp

/-- Literal `lpNorm 2` squared is the coordinate pairing with itself. -/
theorem lpNorm_two_sq_eq_pairing {d : ℕ} (x : Vec d) :
    (lpNorm 2 x) ^ (2 : ℕ) = pairing x x := by
  rw [Stage2RouteC.lpNorm_two_sq]
  unfold pairing
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Exact Euclidean polarization, still in the project's literal norm. -/
theorem pairing_sub_add_self {d : ℕ} (x y : Vec d) :
    pairing (x - y) (x + y) =
      (lpNorm 2 x) ^ (2 : ℕ) - (lpNorm 2 y) ^ (2 : ℕ) := by
  rw [lpNorm_two_sq_eq_pairing, lpNorm_two_sq_eq_pairing]
  unfold pairing
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.sub_apply, Pi.add_apply]
  ring

/-- The auxiliary recurrence converts the mixed product to a difference of
squares with the exact `theta_k^2` coefficient. -/
theorem stage9P_quadratic_step {d : ℕ} {theta : ℕ → ℝ}
    {g : ℕ → Vec d} {k : ℕ} (hθ : theta k ≠ 0) :
    theta k * pairing (stage9P theta g k - g k)
        (stage9P theta g k + stage9P theta g (k + 1)) =
      (theta k) ^ 2 *
        ((lpNorm 2 (stage9P theta g k)) ^ (2 : ℕ) -
          (lpNorm 2 (stage9P theta g (k + 1))) ^ (2 : ℕ)) := by
  have hg := stage9P_gradient_eq (theta := theta) (g := g) hθ
  have hsub : stage9P theta g k - g k =
      theta k • (stage9P theta g k - stage9P theta g (k + 1)) := by
    rw [hg]
    funext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsub, Stage2RouteD.pairing_smul_left,
    pairing_sub_add_self]
  ring

/-- The partial weighted gradient sum equals `kappa_k p_k` whenever the
two exact scalar coefficient recurrences hold. -/
theorem stage9_delta_gradient_sum {d : ℕ}
    (N : ℕ) (theta kappa delta : ℕ → ℝ) (g : ℕ → Vec d)
    (hθ : ∀ k, theta k ≠ 0)
    (hδ : ∀ k, k < N → delta k = kappa (k + 1) / theta k)
    (hκ : ∀ k, k < N →
      kappa k = kappa (k + 1) * (1 - 1 / theta k)) :
    ∀ k, k ≤ N → ∑ j ∈ Finset.range k, delta j • g j =
      kappa k • stage9P theta g k := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
      intro hk
      rw [Finset.sum_range_succ]
      rw [ih (by omega), hδ k (by omega), hκ k (by omega), stage9P_succ]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp [hθ k]

end O3
