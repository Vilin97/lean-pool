/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.ResidualPoint
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

import LeanPool.ConwayRefinement.ConwayRefinement.Topology.Order.PWOSumset

/-!
# Residual points form a well-ordered set

Berarducci, Remark 6.3: the translated truncation `b^{|γ}` lies in `J` unless `γ` belongs to the
order-topological closure of the support of `b`, so it is nonzero modulo `J` only for `γ` ranging
over a well-ordered set. Since a residual point has translated truncation of nonzero ordinal
value, the residual-point set is contained in that closure and is therefore partially well
ordered.

The two inputs are the vanishing of a germ outside the closed support, which is an elementary
metric argument, and the fact that the closure of a partially well-ordered set of reals is again
partially well ordered.
-/

universe v

public noncomputable section

open HahnSeries

namespace Berarducci

variable {K : Type v} [Field K]

/-- Residual points lie in the closure of the support. -/
theorem residualPointSet_subset_closure_support (b : SeriesWithOrdinalValueAboveOne K) :
    residualPointSet b ⊆ closure (b.1 : K⟦ℝ⟧).support := by
  intro γ hγ
  by_contra hmem
  exact translatedTruncation_not_mem_negativeMonomialIdeal_of_mem_residualPointSet hγ
    (translatedTruncation_mem_negativeMonomialIdeal_of_not_mem_closure_support hmem)

/-- Berarducci, Remark 6.3: the residual-point set is partially well ordered. -/
theorem residualPointSet_isPWO (b : SeriesWithOrdinalValueAboveOne K) :
    (residualPointSet b).IsPWO :=
  (Set.isPWO_closure (b.1 : K⟦ℝ⟧).isPWO_support).mono
    (residualPointSet_subset_closure_support b)

end Berarducci
