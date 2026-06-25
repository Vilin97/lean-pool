/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.MetricEntropy

/-!
# Metric entropy theorem statement specifications

This module records typechecked `Prop` targets for covering, packing, and
epsilon-net results. These are specifications only, not proved theorems.

Verified Wikipedia reference:
https://en.wikipedia.org/wiki/Covering_number
-/

namespace HighDimProb

/--
Statement target: a maximal epsilon-separated subset of `K` is an internal
epsilon-net for `K`.
-/
abbrev maximalSeparatedNetStatement {alpha : Type*} [PseudoMetricSpace alpha]
    (K N : Set alpha) (eps : Real) : Prop :=
  MaximalEpsilonSeparatedIn K N eps ->
    IsInternalEpsilonNet K N eps

/--
Statement target: an internal epsilon-net gives an upper bound for the
covering number by its cardinality.

Formula reference: an explicit epsilon-net bounds the covering number by the
number of centers; see https://en.wikipedia.org/wiki/Covering_number
-/
abbrev epsilonNetCoveringNumberStatement {alpha : Type*} [PseudoMetricSpace alpha]
    (K N : Set alpha) (eps : Real) : Prop :=
  0 < eps ->
    Set.Subset N K ->
    IsEpsilonNet K N eps ->
    coveringNumber K eps <= N.encard

/--
Statement target: packing and covering numbers bound each other at related
radii.

Formula reference: packing-covering comparisons are standard metric entropy
estimates based on epsilon-separated sets and epsilon-covers; see
https://en.wikipedia.org/wiki/Covering_number
-/
abbrev packingCoveringInequalityStatement {alpha : Type*} [PseudoMetricSpace alpha]
    (K : Set alpha) (eps : Real) : Prop :=
  0 < eps ->
    And
      (packingNumber K (2 * eps) <= coveringNumber K eps)
      (coveringNumber K eps <= packingNumber K eps)

end HighDimProb
