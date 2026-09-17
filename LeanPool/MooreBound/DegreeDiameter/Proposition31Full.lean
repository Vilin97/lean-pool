/-
Copyright (c) 2026 Wouter Cames van Batenburg, Samuel Korsky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Cames van Batenburg, Samuel Korsky
-/

import LeanPool.MooreBound.DegreeDiameter.Proposition31Asymptotics

/-!
# Complete form of Proposition 3.1

This module gives one declaration containing every finite and asymptotic
clause of Proposition 3.1.  The finite clauses retain the exact multiplication
identity as well as its natural-division consequence.  Both limits in equation
(9) concern the same concrete prime-power graph and use its actual common
degree, not merely the displayed upper bound.

Lean Pool port of wewantmoore commit d59bd80ea93fabb9faf769e790ab47692645e022.
The port adds a namespace and adapts proofs to the current Mathlib APIs and repository style.
-/

namespace MooreBound

open Filter Topology

namespace DegreeDiameter

/-- The finite claims of Proposition 3.1 for the concrete graph over the
chosen field of cardinality `q`.

The named fields expose the five claims in the paper: regularity with the
actual common degree, the exact order in multiplication and division form
(equation (6)), the sharp degree cap (equation (7)), and exact extended
diameter (equation (8)). -/
structure Proposition31FiniteClaims (q : PrimePowerIndex) (k : ℕ) : Prop where
  /-- The graph is regular of its actual common degree. -/
  regularity : ∀ P : Proposition31Vertex (PrimePowerField q) k,
    Nat.card ((Proposition31Graph (PrimePowerField q) k).neighborSet P) =
      proposition31PrimePowerDegree k q
  /-- Equation (6), before taking natural-number division. -/
  order_mul : proposition31PrimePowerOrder k q * (q.1 + 1) ^ k =
    qFactorial q.1 (2 * k + 1)
  /-- Equation (6), in the displayed natural-division form. -/
  order_eq : proposition31PrimePowerOrder k q =
    qFactorial q.1 (2 * k + 1) / (q.1 + 1) ^ k
  /-- Equation (7), with the actual degree on the left. -/
  degree_le_cap :
    proposition31PrimePowerDegree k q ≤ proposition31DegreeCap q.1 k
  /-- Equation (8), as equality of extended diameters. -/
  ediam_eq :
    (Proposition31Graph (PrimePowerField q) k).ediam = (k : ℕ∞)

/-- The finite part of Proposition 3.1, repackaged under a named proposition. -/
theorem proposition31_finite_claims (q : PrimePowerIndex)
    (k : ℕ) (hk : 0 < k) : Proposition31FiniteClaims q k := by
  have hp := proposition_3_1_for_prime_power q k hk
  exact
    { regularity := hp.1
      order_mul := hp.2.1
      order_eq := hp.2.2.1
      degree_le_cap := by
        simpa only [proposition31DegreeCap, proposition31Amplitude] using
          hp.2.2.2.1
      ediam_eq := hp.2.2.2.2 }

/-- **Proposition 3.1 (complete formal statement).**

For every prime-power field order, the concrete halved-flag graph satisfies
all finite claims in equations (6)--(8).  As the field order tends to infinity
through all prime powers, its actual degree divided by the cap and its exact
order divided by the `k`-th power of that actual degree both tend to one, as in
equation (9). -/
theorem proposition_3_1 (k : ℕ) (hk : 0 < k) :
    (∀ q : PrimePowerIndex, Proposition31FiniteClaims q k) ∧
    Tendsto
      (fun q : PrimePowerIndex ↦
        (proposition31PrimePowerDegree k q : ℝ) /
          (proposition31DegreeCap q.1 k : ℝ))
      atTop (nhds 1) ∧
    Tendsto
      (fun q : PrimePowerIndex ↦
        (proposition31PrimePowerOrder k q : ℝ) /
          (proposition31PrimePowerDegree k q : ℝ) ^ k)
      atTop (nhds 1) := by
  exact ⟨fun q ↦ proposition31_finite_claims q k hk,
    proposition31_degree_div_cap_tendsto_one k hk,
    proposition31_order_div_degree_pow_tendsto_one k hk⟩

/-- Consequence of the two asymptotic clauses of Proposition 3.1.

This is the exact algebraic bridge used in the proof of Theorem 1.1.  It is
proved from the bundled declaration `proposition_3_1`, rather than by invoking
the independently available cap-normalized limit.  Pointwise, after the
nonzero denominators have been discharged, the identity is

`N / K^k = (N / Δ^k) * (Δ / K)^k`. -/
theorem proposition31_order_div_cap_pow_tendsto_one_from_proposition_3_1
    (k : ℕ) (hk : 0 < k) :
    Tendsto
      (fun q : PrimePowerIndex ↦
        (proposition31PrimePowerOrder k q : ℝ) /
          (proposition31DegreeCap q.1 k : ℝ) ^ k)
      atTop (nhds 1) := by
  have hP31 := proposition_3_1 k hk
  have hdegree := hP31.2.1
  have horder := hP31.2.2
  have hproduct :
      Tendsto
        (fun q : PrimePowerIndex ↦
          (proposition31PrimePowerOrder k q : ℝ) /
              (proposition31PrimePowerDegree k q : ℝ) ^ k *
            ((proposition31PrimePowerDegree k q : ℝ) /
              (proposition31DegreeCap q.1 k : ℝ)) ^ k)
        atTop (nhds 1) := by
    simpa only [one_pow, one_mul] using horder.mul (hdegree.pow k)
  have hdegreePos : ∀ᶠ q : PrimePowerIndex in atTop,
      0 < (proposition31PrimePowerDegree k q : ℝ) /
        (proposition31DegreeCap q.1 k : ℝ) :=
    hdegree.eventually (Ioi_mem_nhds zero_lt_one)
  refine hproduct.congr' ?_
  filter_upwards [hdegreePos] with q hratioPos
  have hcap : (proposition31DegreeCap q.1 k : ℝ) ≠ 0 := by
    intro hzero
    rw [hzero, div_zero] at hratioPos
    exact (lt_irrefl 0) hratioPos
  have hdegreeNe : (proposition31PrimePowerDegree k q : ℝ) ≠ 0 := by
    intro hzero
    rw [hzero, zero_div] at hratioPos
    exact (lt_irrefl 0) hratioPos
  rw [div_pow]
  field_simp [hcap, hdegreeNe]

end DegreeDiameter

end MooreBound
