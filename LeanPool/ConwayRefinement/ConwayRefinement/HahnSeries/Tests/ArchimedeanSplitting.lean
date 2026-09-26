/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.ArchimedeanSplitting

/-!
# API checks for the Hahn-series Archimedean splitting

The check is polymorphic in independent stratum and ball coordinates and verifies that a monomial
on their sum becomes a nested monomial coefficient at exactly those two coordinates. In
particular, it certifies the dominant-then-infinitesimal orientation without unfolding either
equivalence.
-/

public noncomputable section

namespace Tests

open FiniteArchimedeanClass

variable {K M : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
variable [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]
variable [Module K M] [IsOrderedModule K M]

open HahnEmbedding in
theorem archimedeanSeriesSplitting_monomial_coeff
    (u : ArchimedeanStrata K M) (c : FiniteArchimedeanClass M)
    (s : u.stratum c) (b : ball K c) :
    ((HahnSeries.archimedeanSplitRingEquiv u c
      (HahnSeries.single
        (ArchimedeanStrata.stratumLexBallEquivClosedBall u c (toLex (s, b))) (13 : ℤ))).coeff
        s).coeff b = 13 := by
  rw [HahnSeries.archimedeanSplitRingEquiv_coeff]
  simp

end Tests
