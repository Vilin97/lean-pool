/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.CounterexampleMainTerm

/-!
# Identification of the stationary kernel main term

The packet estimate produces phases `e(λ(x-j)²)`, whereas the Bohr argument
uses `e(2λjx)`.  For dyadic (hence integer) `λ`, the `λj²` phase is one and
the sign change is complex conjugation.  This file records the exact identity,
so the two finite sums have precisely the same norm.
-/

open Set
open scoped ComplexConjugate

namespace QuadraticCarleson


theorem phase_neg (a : ℝ) : phase (-a) = conj (phase a) := by
  rw [phase, phase, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem conj_phase (a : ℝ) : conj (phase a) = phase (-a) :=
  (phase_neg a).symm

private theorem dyadic_quadratic_phase_expand (n j : ℕ) (x : ℝ) :
    phase ((2 ^ n : ℝ) * (x - j) ^ 2) =
      phase ((2 ^ n : ℝ) * x ^ 2) * phase (-(2 * (2 ^ n : ℝ) * j * x)) := by
  have harg : (2 ^ n : ℝ) * (x - j) ^ 2 =
      (2 ^ n : ℝ) * x ^ 2 + (-(2 * (2 ^ n : ℝ) * j * x)) +
        (((2 ^ n * j ^ 2 : ℕ) : ℤ) : ℝ) := by
    push_cast
    ring
  rw [harg, phase_add, phase_add, phase_int, mul_one]

/-- Exact complex identity between the stationary kernel main term and a
unit phase times the conjugate of the Bohr harmonic sum. -/
theorem stationaryKernelMain_eq_phase_mul_conj_harmonicPhaseSum
    {N n : ℕ} {L x : ℝ} {k : ℤ}
    (hN : 100 ≤ N) (hk : (k, n) ∈ paperMainTermIndices N L) :
    (1 / (N : ℂ)) * ∑ j ∈ Finset.Icc (k.toNat + 1) N,
        phase ((2 ^ n : ℝ) * (x - j) ^ 2) / ((x - j : ℝ) : ℂ) =
      phase ((2 ^ n : ℝ) * x ^ 2) *
        conj (harmonicPhaseSum N k.toNat ((2 ^ n : ℕ) : ℤ) (x - k)) := by
  rw [harmonicPhaseSum_paperMainTerm_eq hN hk]
  simp only [map_mul, map_div₀, map_sum, Complex.conj_ofReal,
    conj_phase, one_div]
  have hconjN : conj ((N : ℂ)⁻¹) = (N : ℂ)⁻¹ := by simp
  rw [hconjN, ← mul_assoc]
  rw [Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [dyadic_quadratic_phase_expand]
  ring

/-- In particular the stationary kernel sum has exactly the norm controlled
from below on the translated Bohr set. -/
theorem norm_stationaryKernelMain_eq_harmonicPhaseSum
    {N n : ℕ} {L x : ℝ} {k : ℤ}
    (hN : 100 ≤ N) (hk : (k, n) ∈ paperMainTermIndices N L) :
    ‖(1 / (N : ℂ)) * ∑ j ∈ Finset.Icc (k.toNat + 1) N,
        phase ((2 ^ n : ℝ) * (x - j) ^ 2) / ((x - j : ℝ) : ℂ)‖ =
      ‖harmonicPhaseSum N k.toNat ((2 ^ n : ℕ) : ℤ) (x - k)‖ := by
  rw [stationaryKernelMain_eq_phase_mul_conj_harmonicPhaseSum hN hk,
    norm_mul, norm_phase, Complex.norm_conj, one_mul]

end QuadraticCarleson
