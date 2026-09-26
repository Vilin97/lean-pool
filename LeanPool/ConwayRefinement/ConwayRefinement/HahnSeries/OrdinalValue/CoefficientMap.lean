/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueSupport
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.NonpositiveCoefficientMap

/-!
# Ordinal value under coefficient extension

An embedding of coefficient fields preserves the support and hence the ordinal value of a
nonpositive Hahn series.
-/

universe v w

open scoped HahnSeries

namespace Berarducci

open HahnSeries.Nonpositive

public section

/-- Coefficient extension along a field embedding preserves the ordinal value. -/
theorem ordinalValue_nonpositiveCoefficientMap {K : Type v} {E : Type w}
    [Field K] [Field E] (f : K →+* E) (u : HahnSeries.Nonpositive ℝ K) :
    ordinalValue (nonpositiveCoefficientMap f u) = ordinalValue u :=
  le_antisymm
    (ordinalValue_le_of_support_subset _ _ (support_nonpositiveCoefficientMap f u).subset)
    (ordinalValue_le_of_support_subset _ _ (support_nonpositiveCoefficientMap f u).superset)

end

end Berarducci
