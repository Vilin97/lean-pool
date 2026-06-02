/-
Copyright (c) 2026 Math Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Math Inc
-/
import Mathlib.Algebra.Notation.Indicator
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Basic definitions for primitive sets above `x`

This file introduces the core objects used throughout the development: the arithmetic sums
appearing in the analytic estimates, the entry weights and normalization data `b_x`, `B_x`,
and `μ_x`, and the abstract Markov-layer interface used for the visit-probability argument.

## Main definitions

* `PrimitiveSet`
* `mertensPartialSum`
* `tailSum`
* `ry`
* `entryWeight`
* `normalizationConstant`
* `initialDistribution`
* `MarkovLayer`
-/

open scoped ArithmeticFunction BigOperators

namespace PrimitiveSetsAboveX

/-- The primitive-set predicate used throughout the local development. -/
def PrimitiveSet (A : Set ℕ) : Prop :=
  ∀ ⦃m n : ℕ⦄, m ∈ A → n ∈ A → m ∣ n → m = n

/-- Partial sums of `Λ(q) / q`. -/
noncomputable def mertensPartialSum (t : ℕ) : ℝ :=
  (Finset.Icc 1 t).sum fun q => Λ q / (q : ℝ)

/-- The logarithmic tail sum `T(m, y)` used in the normalization estimates. -/
noncomputable def tailSum (m y : ℕ) : ℝ :=
  ∑' q : ℕ,
    if y ≤ q then
      Λ q / ((q : ℝ) * (Real.log ((m * q : ℕ) : ℝ)) ^ 2)
    else 0

/-- The quantity `R_Y(m)` introduced in the proof of the main theorem. -/
noncomputable def ry (Y m : ℕ) : ℝ :=
  ∑' q : ℕ,
    if Y ≤ q then
      (Real.log (m : ℝ) / (Real.log ((m * q : ℕ) : ℝ)) ^ 2) * (Λ q / (q : ℝ))
    else 0

/-- The transition weight `p(m, mq)` of the sub-Markov chain. -/
noncomputable def transitionWeight (Y m q : ℕ) : ℝ :=
  if Y ≤ q then
    (Real.log (m : ℝ) / (Real.log ((m * q : ℕ) : ℝ)) ^ 2) * (Λ q / (q : ℝ))
  else 0

/-- The entry weight `b_x(n)` used to define the initial distribution of the chain. -/
noncomputable def entryWeight (x Y n : ℕ) : ℝ :=
  1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2) *
    (((n.divisors.filter (fun q => q < Y)).sum fun q => Λ q) +
      ((n.divisors.filter (fun q => Y ≤ q ∧ n / q < x)).sum fun q => Λ q))

/-- The normalizing constant `B_x`. -/
noncomputable def normalizationConstant (x Y : ℕ) : ℝ :=
  ∑' n : ℕ, if x ≤ n then entryWeight x Y n else 0

/-- The normalized initial distribution `μ_x(n) = b_x(n) / B_x`. -/
noncomputable def initialDistribution (x Y n : ℕ) : ℝ :=
  entryWeight x Y n / normalizationConstant x Y

/--
An abstract sub-Markov layer on the state space `n ≥ x`, together with a candidate
visit-probability function satisfying the last-jump recurrence.
-/
structure MarkovLayer (x Y : ℕ) where
  /-- The transition weights satisfy the required sub-Markov row-sum bound. -/
  transitionSubMarkov :
    ∀ ⦃m : ℕ⦄, x ≤ m → (∑' q : ℕ, transitionWeight Y m q) ≤ 1
  /-- The probability that the chain ever visits `n` when started from `μ_x`. -/
  visitProbability : ℕ → ℝ
  /-- The last-jump recurrence for the visiting probabilities. -/
  visitProbabilityRecurrence :
    ∀ ⦃n : ℕ⦄, x ≤ n →
      visitProbability n =
        initialDistribution x Y n +
          ∑' q : ℕ,
            if Y ≤ q ∧ q ∣ n ∧ x ≤ n / q then
              visitProbability (n / q) * transitionWeight Y (n / q) q
            else 0

end PrimitiveSetsAboveX
