/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Family
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Shared definitions used across the development.
Arithmetic: `colVal`, `allocCost`, `GreedyBound` (the proof notes, Lemma 4 in allocation form).
Analytic: `Rfun`, `wfun`, `heineIntegrand`, `HeineBound` (the proof notes, 5.2 in bound form). -/

public section

open Polynomial
open scoped BigOperators

namespace Zeta32
noncomputable section

/-- Column value `c_b = 4 N_b − C_b + [b = 0] − 2` of the proof notes, §3, with
`N_b = #{1 ≤ i ≤ n : i ≡ b}` and `C_b = #{1 ≤ j ≤ 5n : j ≡ b}` modulo `p`. -/
@[expose]
def colVal (n p b : ℕ) : ℤ :=
  4 * (((Finset.Icc 1 n).filter (fun i => i % p = b)).card : ℤ)
    - (((Finset.Icc 1 (5*n)).filter (fun j => j % p = b)).card : ℤ)
    + (if b = 0 then 1 else 0) - 2

/-- Cost of taking the first `k b` entries `c_b, c_b + 2, …` of every column `b < p`. -/
@[expose]
def allocCost (n p : ℕ) (k : ℕ → ℕ) : ℤ :=
  ∑ b ∈ Finset.range p, ((k b : ℤ) * colVal n p b + (k b : ℤ) * ((k b : ℤ) - 1))

/-- the proof notes, Lemma 4 in allocation form: some allocation of the `h = 3n` picks bounds every
nonzero coefficient of `Q r n` from below `p`-adically (the greedy allocation does). -/
@[expose]
def GreedyBound (r : ℚ) (n p : ℕ) : Prop :=
  ∃ k : ℕ → ℕ, (∑ b ∈ Finset.range p, k b) = 3*n ∧
    ∀ i, (Q r n).coeff i ≠ 0 → ((allocCost n p k : ℤ) : ℚ) ≤ (padicValRat p ((Q r n).coeff i) : ℚ)

/-- `R_n(t) = D_n(t)^4 / D_{5n}(t)` as a complex function. -/
@[expose]
def Rfun (n : ℕ) (t : ℂ) : ℂ :=
  (∏ j ∈ Finset.Icc 1 n, (t + j))^4 / ∏ j ∈ Finset.Icc 1 (5*n), (t + j)

/-- The kernel `w(y) = (π/2) sech²(πy) (2r − 2πi tanh πy)` of the proof notes, 5.1. -/
@[expose]
def wfun (r : ℚ) (y : ℝ) : ℂ :=
  ((Real.pi / 2 / Real.cosh (Real.pi * y) ^ 2 : ℝ) : ℂ) *
    (2 * (r : ℂ) - 2 * Real.pi * Complex.I * (Real.tanh (Real.pi * y) : ℂ))

/-- `∏_l |(t R_n)(t_l) w(y_l)| · Δ(y)²` with `t_l = 1/2 + i y_l`, `h = 3n`. -/
@[expose]
def heineIntegrand (r : ℚ) (n : ℕ) (y : Fin (3 * n) → ℝ) : ℝ :=
  (∏ l, ‖((1/2 : ℂ) + Complex.I * (y l)) * Rfun n ((1/2 : ℂ) + Complex.I * (y l)) * wfun r (y l)‖) *
    ∏ l, ∏ l' ∈ Finset.univ.filter (fun l' => l < l'), (y l - y l') ^ 2

/-- the proof notes, 5.2 (Heine), in the bound form used by 5.3. -/
@[expose]
def HeineBound (r : ℚ) (n : ℕ) : Prop :=
  |Polynomial.aeval (Cr r) (Q r n)| ≤ (1 / ((3*n).factorial : ℝ)) * ∫ y, heineIntegrand r n y

end
end Zeta32
