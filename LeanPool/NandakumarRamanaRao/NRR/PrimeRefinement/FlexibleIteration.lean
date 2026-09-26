/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.PrimeRefinement.Iteration
/-!
# Model-independent prime-refinement iteration

The shared iteration and partition assembly live in `Iteration`. This module retains the
model-independent public implication interface used by the obstruction proof.
-/

@[expose] public section

open MeasureTheory

namespace NRR

open Geometry

/-- Public implication form of the Avvakumov--Akopyan--Karasev theorem.  The conclusion for every
positive number of pieces follows formally from the single prime-refinement separator theorem. -/
theorem avvakumov_akopyan_karasev_flexible
    (H : FlexiblePrimeRefinementTheorem) :
    ∀ (K : Geometry.ConvexBody Plane) (n : ℕ), 0 < n →
      ∃ P : ConvexPartition K n, P.IsFair := by
  intro K n hn
  exact exists_fair_partition_of_flexiblePrimeRefinement H K n hn


end NRR
