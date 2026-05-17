/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# KL Divergence and Finite PMFs

Pure mathematical infrastructure for probability mass functions over finite types,
KL divergence, cross-entropy, and expected values. No learning-theory types.

## Main definitions

- `FinitePMF` : a probability mass function over a finite type
- `klDivFinitePMF` : KL divergence between two FinitePMFs
- `crossEntropyFinitePMF` : cross-entropy H(Q, P)
- `expectFinitePMF` : expected value E_{h~Q}[f(h)]
- `HasPositivePrior` : typeclass for PMFs with strictly positive weights

## References

- Cover & Thomas, "Elements of Information Theory", Chapter 2
-/

open Finset

/-- A probability mass function over a finite type.
    Named FinitePMF to avoid conflict with Mathlib's PMF. -/
structure FinitePMF (H : Type*) [Fintype H] where
  /-- Probability assigned to each point. -/
  prob : H → ℝ
  prob_nonneg : ∀ h, 0 ≤ prob h
  prob_sum_one : ∑ h : H, prob h = 1

/-- KL divergence between two FinitePMFs over a finite type.
    KL(Q‖P) = ∑_h Q(h) · log(Q(h)/P(h)).
    Convention: 0 · log(0/p) = 0. -/
noncomputable def klDivFinitePMF {H : Type*} [Fintype H]
    (Q P : FinitePMF H) : ℝ :=
  ∑ h : H, if Q.prob h = 0 then 0
    else Q.prob h * Real.log (Q.prob h / P.prob h)

/-- Cross-entropy: ∑_h Q(h) · log(1/P(h)).
    Equals KL(Q‖P) + H(Q) where H(Q) is Shannon entropy. -/
noncomputable def crossEntropyFinitePMF {H : Type*} [Fintype H]
    (Q P : FinitePMF H) : ℝ :=
  ∑ h : H, if Q.prob h = 0 then 0
    else Q.prob h * Real.log (1 / P.prob h)

/-- Expected value of a real-valued function under a FinitePMF. -/
noncomputable def expectFinitePMF {H : Type*} [Fintype H]
    (Q : FinitePMF H) (f : H → ℝ) : ℝ :=
  ∑ h : H, Q.prob h * f h

/-- Typeclass asserting that a FinitePMF has strictly positive weights. -/
class HasPositivePrior {H : Type*} [Fintype H] (P : FinitePMF H) : Prop where
  pos : ∀ h, 0 < P.prob h
