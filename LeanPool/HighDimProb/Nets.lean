/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import Mathlib.Topology.MetricSpace.CoveringNumbers
import LeanPool.HighDimProb.Basic

/-!
# Nets and separated sets

Wrappers in this file reuse Mathlib's metric covering and separated-set APIs.
Real radii are converted to nonnegative radii by `Real.toNNReal`.

Verified Wikipedia reference:
https://en.wikipedia.org/wiki/Covering_number
-/

namespace HighDimProb

open scoped NNReal ENNReal

/--
Nonnegative Mathlib radius associated to a real radius.

Formula reference: covering numbers are parameterized by a radius/scale
epsilon; see https://en.wikipedia.org/wiki/Covering_number
-/
abbrev epsilonRadius (eps : Real) : NNReal :=
  Real.toNNReal eps

/-- Extended nonnegative Mathlib radius associated to a real radius. -/
abbrev epsilonERadius (eps : Real) : ENNReal :=
  (epsilonRadius eps : ENNReal)

/--
`N` is an `eps`-net/cover for `K`, using Mathlib's `Metric.IsCover`.

Formula reference: an epsilon-net covers a set by balls of radius epsilon; see
https://en.wikipedia.org/wiki/Covering_number

Mathlib's cover predicate allows centers in `N` to lie outside `K`.
-/
abbrev IsEpsilonNet {alpha : Type*} [PseudoMetricSpace alpha]
    (K N : Set alpha) (eps : Real) : Prop :=
  Metric.IsCover (epsilonRadius eps) K N

/--
Internal `eps`-net: a Mathlib cover whose centers lie in `K`.

Formula reference: this is the internal-center version of an epsilon cover; see
https://en.wikipedia.org/wiki/Covering_number
-/
abbrev IsInternalEpsilonNet {alpha : Type*} [PseudoMetricSpace alpha]
    (K N : Set alpha) (eps : Real) : Prop :=
  Set.Subset N K ∧ IsEpsilonNet K N eps

/--
A set is `eps`-separated, using Mathlib's `Metric.IsSeparated`.

Formula reference: packing/separated sets are dual to covering-number bounds;
see https://en.wikipedia.org/wiki/Covering_number
-/
abbrev IsEpsilonSeparated {alpha : Type*} [PseudoMetricSpace alpha]
    (N : Set alpha) (eps : Real) : Prop :=
  Metric.IsSeparated (epsilonERadius eps) N

/--
Single-point maximality for an internal `epsilon`-separated subset of `K`.

This is the book-facing notion used in the elementary proof that a maximal
separated set is a net: no point of `K` outside `N` can be inserted while
preserving separation.
-/
abbrev MaximalEpsilonSeparatedIn {alpha : Type*} [PseudoMetricSpace alpha]
    (K N : Set alpha) (eps : Real) : Prop :=
  Set.Subset N K ∧ IsEpsilonSeparated N eps ∧
    ∀ x, x ∈ K -> x ∉ N -> ¬ IsEpsilonSeparated (insert x N) eps

theorem isEpsilonNet_iff {alpha : Type*} [PseudoMetricSpace alpha]
    (K N : Set alpha) (eps : Real) :
    Iff (IsEpsilonNet K N eps) (Metric.IsCover (epsilonRadius eps) K N) :=
  Iff.rfl

theorem isInternalEpsilonNet_iff {alpha : Type*} [PseudoMetricSpace alpha]
    (K N : Set alpha) (eps : Real) :
    Iff (IsInternalEpsilonNet K N eps)
      (Set.Subset N K ∧ IsEpsilonNet K N eps) :=
  Iff.rfl

theorem isEpsilonSeparated_iff {alpha : Type*} [PseudoMetricSpace alpha]
    (N : Set alpha) (eps : Real) :
    Iff (IsEpsilonSeparated N eps)
      (Metric.IsSeparated (epsilonERadius eps) N) :=
  Iff.rfl

/--
A single-point maximal internal `epsilon`-separated subset of `K` is an
internal `epsilon`-net for `K`.
-/
theorem isInternalEpsilonNet_of_maximalEpsilonSeparatedIn {alpha : Type*}
    [PseudoMetricSpace alpha] {K N : Set alpha} {eps : Real}
    (hN : MaximalEpsilonSeparatedIn K N eps) :
    IsInternalEpsilonNet K N eps := by
  refine And.intro hN.1 ?_
  intro x hxK
  by_cases hxN : x ∈ N
  · exact ⟨x, hxN, by simp⟩
  · by_contra hcover
    have hfar : ∀ y, y ∈ N -> epsilonERadius eps < edist x y := by
      intro y hyN
      have hnot : ¬ edist x y ≤ (epsilonRadius eps : ENNReal) := by
        intro hle
        exact hcover ⟨y, hyN, hle⟩
      simpa [epsilonERadius] using not_le.mp hnot
    have hinsert : IsEpsilonSeparated (insert x N) eps := by
      exact (Metric.isSeparated_insert_of_notMem
        (ε := epsilonERadius eps) (s := N) (x := x) hxN).2
          ⟨hN.2.1, hfar⟩
    exact hN.2.2 x hxK hxN hinsert

end HighDimProb
