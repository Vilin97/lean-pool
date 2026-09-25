/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceExhaustion

/-!
# Pressure Gradient Origin Clause Exhaustion

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open Set Metric

noncomputable section

namespace CKN.Core.Step4

/-!
# Exhausting an open order-connected set of times by compact order-connected sets

A set `I ⊆ ℝ` that is open and order-connected is the increasing union of compact
order-connected subsets, and every compact subset of `I` is already contained in one of
them. Concretely, for each `n : ℕ` we take the points whose `1 / (n + 1)`-neighbourhood
lies in `I` and which themselves lie in the ambient interval `[-n, n]`, and then we close
that set. Each stage is compact, order-connected, contained in `I`, the stages increase,
their union is all of `I`, and compact subsets are absorbed because a compact subset of an
open set has a positive Lebesgue number.

This is the elementary device that turns a local, bounded-time construction on an open
order-connected time interval into a construction on the whole interval: every compact
piece of the interval is contained in a single compact stage.
-/

/-- The raw (pre-closure) `n`-th stage of the exhaustion of `I`: points in the ambient
interval `[-n, n]` whose closed `1 / (n + 1)`-ball is contained in `I`. -/
def originClauseCore (I : Set ℝ) (n : ℕ) : Set ℝ :=
  OriginInstance.exhaustionCore I n

/-- An open order-connected interval has an increasing compact exhaustion. -/
theorem originClauseTimeExhaustion {I : Set ℝ}
    (hopen : IsOpen I) (hord : I.OrdConnected) :
    ∃ J : ℕ → Set ℝ,
      Monotone J ∧
      (∀ n, (J n).OrdConnected) ∧
      (∀ n, IsCompact (J n)) ∧
      (∀ n, J n ⊆ I) ∧
      (⋃ n, J n) = I ∧
      (∀ T : Set ℝ, IsCompact T → T ⊆ I → ∃ n, T ⊆ J n) :=
  OriginInstance.exists_compact_ordConnected_exhaustion hopen hord

end CKN.Core.Step4
