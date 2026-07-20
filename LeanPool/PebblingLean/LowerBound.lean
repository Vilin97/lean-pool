/-
Copyright (c) 2026 Lior Pachter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lior Pachter
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import LeanPool.PebblingLean.Hypercube
import LeanPool.PebblingLean.Weight

/-!
# Lower-bound infrastructure for hypercubes

This file starts the formal version of the weight-function lower bound.  The
main result here is the first inequality in the paper's lower-bound proof:
for a solvable distribution on `Q_n`, every target has initial weight at least
one, and hence the sum of all target weights is at least `|Q_n|`.
-/

namespace PebblingLean

namespace Hypercube

open Pebbling

/-- For the hypercube, any target reachable from `D` has initial weight at least
one with respect to that target. -/
theorem one_le_weight_of_canReach {n : ℕ} {D : Pebbling (HypercubeVertex n)}
    {target : HypercubeVertex n}
    (hcan : CanReach (graph n) D target) :
    1 ≤ weight dist D target := by
  exact Pebbling.one_le_weight_of_canReach (G := graph n) (dist := dist)
    (D := D) (target := target) hcan (dist_self target)
    (fun {u v} h => dist_adj_le_succ (t := target) h)

/-- A solvable distribution has target weight at least one for every target. -/
theorem one_le_weight_of_solvable {n : ℕ} {D : Pebbling (HypercubeVertex n)}
    (hsolv : Solvable (graph n) D) (target : HypercubeVertex n) :
    1 ≤ weight dist D target :=
  one_le_weight_of_canReach (D := D) (target := target) (hsolv target)

/-- Summing the target-wise lower bound over all targets gives
`|Q_n| ≤ ∑_t W_t(D)`. -/
theorem card_le_sum_weight_of_solvable {n : ℕ} {D : Pebbling (HypercubeVertex n)}
    (hsolv : Solvable (graph n) D) :
    (Fintype.card (HypercubeVertex n) : ℚ) ≤
      ∑ target : HypercubeVertex n, weight dist D target := by
  calc
    (Fintype.card (HypercubeVertex n) : ℚ)
        = ∑ _target : HypercubeVertex n, (1 : ℚ) := by
          simp
    _ ≤ ∑ target : HypercubeVertex n, weight dist D target := by
          exact Finset.sum_le_sum fun target _ =>
            one_le_weight_of_solvable (D := D) hsolv target

/-- The finite-subset identity behind the inner hypercube weight sum. -/
theorem sum_invPow_card_finsets (n : ℕ) :
    (∑ s : Finset (Fin n), (1 : ℚ) / (2 : ℚ) ^ s.card) = ((3 : ℚ) / 2) ^ n := by
  classical
  have h := Finset.prod_add (s := (Finset.univ : Finset (Fin n)))
    (f := fun _ : Fin n => (1 : ℚ) / 2) (g := fun _ : Fin n => (1 : ℚ))
  norm_num [Finset.prod_const, Finset.powerset_univ, div_eq_mul_inv, mul_comm, mul_left_comm,
    mul_assoc, add_comm, add_left_comm, add_assoc] at h
  calc
    (∑ s : Finset (Fin n), (1 : ℚ) / (2 : ℚ) ^ s.card) = (2 ^ n : ℚ)⁻¹ * 3 ^ n := by
      simpa [div_eq_mul_inv] using h.symm
    _ = ((3 : ℚ) / 2) ^ n := by
      rw [div_pow]
      ring

/-- For a fixed hypercube vertex `base`, the sum of one-pebble weights over all
targets is `(3/2)^n`. -/
theorem sum_unitWeight (n : ℕ) (base : HypercubeVertex n) :
    (∑ target : HypercubeVertex n, unitWeight dist target base) = ((3 : ℚ) / 2) ^ n := by
  classical
  calc
    (∑ target : HypercubeVertex n, unitWeight dist target base)
        = ∑ s : Finset (Fin n), (1 : ℚ) / (2 : ℚ) ^ s.card := by
          simpa [unitWeight, dist_comm, dist_eq_card_diffSet, diffSetEquiv,
            Equiv.coe_fn_mk] using
            ((diffSetEquiv base).sum_comp
              (fun s : Finset (Fin n) => (1 : ℚ) / (2 : ℚ) ^ s.card))
    _ = ((3 : ℚ) / 2) ^ n := sum_invPow_card_finsets n

/-- The double sum of weights factors as `|D| * (3/2)^n`. -/
theorem sum_weight_eq_size_mul {n : ℕ} (D : Pebbling (HypercubeVertex n)) :
    (∑ target : HypercubeVertex n, weight dist D target)
      = (size D : ℚ) * ((3 : ℚ) / 2) ^ n := by
  classical
  calc
    (∑ target : HypercubeVertex n, weight dist D target)
        = ∑ target : HypercubeVertex n,
            ∑ u : HypercubeVertex n, (D u : ℚ) * unitWeight dist target u := by
          rfl
    _ = ∑ u : HypercubeVertex n,
            ∑ target : HypercubeVertex n, (D u : ℚ) * unitWeight dist target u := by
          exact Finset.sum_comm
    _ = ∑ u : HypercubeVertex n,
            (D u : ℚ) * (∑ target : HypercubeVertex n, unitWeight dist target u) := by
          simp [Finset.mul_sum]
    _ = ∑ u : HypercubeVertex n, (D u : ℚ) * ((3 : ℚ) / 2) ^ n := by
          simp [sum_unitWeight]
    _ = (size D : ℚ) * ((3 : ℚ) / 2) ^ n := by
          simp [size, Finset.sum_mul]

/-- Formal version of the averaged weight inequality
`|Q_n| ≤ |D| (3/2)^n` for every solvable distribution `D`. -/
theorem card_le_size_mul_of_solvable {n : ℕ} {D : Pebbling (HypercubeVertex n)}
    (hsolv : Solvable (graph n) D) :
    (Fintype.card (HypercubeVertex n) : ℚ) ≤
      (size D : ℚ) * ((3 : ℚ) / 2) ^ n := by
  exact (card_le_sum_weight_of_solvable (D := D) hsolv).trans_eq
    (sum_weight_eq_size_mul D)

/-- The lower bound in the paper's usual rational form:
every solvable distribution on `Q_n` has at least `(4/3)^n` pebbles. -/
theorem lower_bound_size_of_solvable {n : ℕ} {D : Pebbling (HypercubeVertex n)}
    (hsolv : Solvable (graph n) D) :
    ((4 : ℚ) / 3) ^ n ≤ (size D : ℚ) := by
  have h := card_le_size_mul_of_solvable (D := D) hsolv
  simp only [card_vertex, Nat.cast_pow, Nat.cast_ofNat] at h
  have hpos : 0 < ((3 : ℚ) / 2) ^ n := by positivity
  have hdiv : ((2 : ℚ) ^ n) / (((3 : ℚ) / 2) ^ n) ≤ (size D : ℚ) := by
    exact (div_le_iff₀ hpos).mpr h
  have heq : ((4 : ℚ) / 3) ^ n = ((2 : ℚ) ^ n) / (((3 : ℚ) / 2) ^ n) := by
    rw [show (4 : ℚ) = 2 ^ 2 by norm_num]
    rw [div_pow, div_pow]
    field_simp
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  simpa [heq]

/-- Lower bound for any specified solvable size. -/
theorem lower_bound_of_hasSolvableSize {n k : ℕ}
    (h : HasSolvableSize (graph n) k) :
    ((4 : ℚ) / 3) ^ n ≤ (k : ℚ) := by
  rcases h with ⟨D, hsize, hsolv⟩
  rw [← hsize]
  exact lower_bound_size_of_solvable hsolv

/-- Lower bound for any `k` certified as the optimal pebbling number. -/
theorem lower_bound_of_isOptimalNumber {n k : ℕ}
    (hopt : IsOptimalNumber (graph n) k) :
    ((4 : ℚ) / 3) ^ n ≤ (k : ℚ) :=
  lower_bound_of_hasSolvableSize hopt.1

end Hypercube

end PebblingLean
