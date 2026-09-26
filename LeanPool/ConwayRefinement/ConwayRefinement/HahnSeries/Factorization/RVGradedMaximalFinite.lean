/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.MaximalFinite
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.RVMaximalFinite

import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.AssociatedGradedDivisibility

/-!
# Maximal finite-support divisors under the RV-to-graded embedding

The canonical multiplicative embedding of degree RV into the associated graded ring preserves
and reflects divisibility. Consequently it also preserves the intrinsic maximal finite-support
divisor class.
-/

open scoped HahnSeries

universe v

namespace Berarducci

public noncomputable section

open HahnSeries.Nonpositive

variable {K : Type v} [Field K] [CharZero K]

/-- A maximal finite-support divisor class of an RV element is equivalently a maximal
finite-support divisor class of its canonical image in the associated graded ring. -/
theorem isRVMaximalFiniteSupportDivisor_iff_isGradedMaximalFiniteSupportDivisor (B : HahnDegreeRV K)
    (a : Associates (FiniteSupportRing (K := K))) :
    IsRVMaximalFiniteSupportDivisor B a ↔
      IsGradedMaximalFiniteSupportDivisor
        ((degreeValuation K).rvInitialFormHom B) a := by
  let w := degreeValuation K
  rw [isRVMaximalFiniteSupportDivisor_iff,
    isGradedMaximalFiniteSupportDivisor_iff]
  constructor <;> intro h q
  · rw [h q]
    have htransport :=
      w.rv_dvd_iff_associatedGraded_dvd (finiteSupportRVEmbedding K q) B
    have hfinite :
        w.rvInitialFormHom (finiteSupportRVEmbedding K q) =
          finiteSupportGradedEmbedding K q := by
      calc
        w.rvInitialFormHom (finiteSupportRVEmbedding K q) =
            ((w.rvEquivHomogeneous (finiteSupportRVEmbedding K q) :
              w.HomogeneousClasses) : w.AssociatedGraded) := by
          rw [w.rvEquivHomogeneous_apply, w.coe_rvHomogeneous]
        _ = finiteSupportGradedEmbedding K q := by
          simpa only [w] using
            coe_rvEquivHomogeneous_finiteSupportRVEmbedding q
    rw [hfinite] at htransport
    exact htransport
  · rw [h q]
    have htransport :=
      w.rv_dvd_iff_associatedGraded_dvd (finiteSupportRVEmbedding K q) B
    have hfinite :
        w.rvInitialFormHom (finiteSupportRVEmbedding K q) =
          finiteSupportGradedEmbedding K q := by
      calc
        w.rvInitialFormHom (finiteSupportRVEmbedding K q) =
            ((w.rvEquivHomogeneous (finiteSupportRVEmbedding K q) :
              w.HomogeneousClasses) : w.AssociatedGraded) := by
          rw [w.rvEquivHomogeneous_apply, w.coe_rvHomogeneous]
        _ = finiteSupportGradedEmbedding K q := by
          simpa only [w] using
            coe_rvEquivHomogeneous_finiteSupportRVEmbedding q
    rw [hfinite] at htransport
    exact htransport.symm

end

end Berarducci
