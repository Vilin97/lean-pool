/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Order.Module.ArchimedeanBallSplitting
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.DomainEquiv
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Iterate

/-!
# Hahn-series splitting along an Archimedean class

The ordered splitting of a closed Archimedean ball reindexes Hahn series on that ball as Hahn
series on a lexicographic product. Flattening in reverse then presents them as iterated Hahn
series: the chosen stratum is the outer, dominant exponent and the open ball is the inner,
infinitesimal exponent.
-/

public noncomputable section

namespace HahnSeries

open FiniteArchimedeanClass

variable {R K M : Type*} [Semiring R]
variable [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
variable [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]
variable [Module K M] [IsOrderedModule K M]

/-- Hahn series on a closed Archimedean ball as iterated Hahn series, with the chosen stratum
as the outer exponent and the open ball as the coefficient-series exponent. -/
def archimedeanSplitRingEquiv (u : HahnEmbedding.ArchimedeanStrata K M)
    (c : FiniteArchimedeanClass M) :
    R⟦closedBall K c⟧ ≃+* (R⟦ball K c⟧)⟦u.stratum c⟧ :=
  (embDomainRingEquiv
    (HahnEmbedding.ArchimedeanStrata.closedBallEquivStratumLexBall u c)).trans
      iterateRingEquiv.symm

@[simp]
theorem archimedeanSplitRingEquiv_coeff
    (u : HahnEmbedding.ArchimedeanStrata K M) (c : FiniteArchimedeanClass M)
    (x : R⟦closedBall K c⟧) (s : u.stratum c) (b : ball K c) :
    ((archimedeanSplitRingEquiv u c x).coeff s).coeff b =
      x.coeff (HahnEmbedding.ArchimedeanStrata.stratumLexBallEquivClosedBall u c
        (toLex (s, b))) := by
  apply (iterateRingEquiv_coeff (archimedeanSplitRingEquiv u c x) s b).symm.trans
  change (iterateRingEquiv
    (iterateRingEquiv.symm
      (embDomainRingEquiv
        (HahnEmbedding.ArchimedeanStrata.closedBallEquivStratumLexBall u c) x))).coeff
      (toLex (s, b)) = _
  rw [RingEquiv.apply_symm_apply]
  have h := embDomainRingEquiv_coeff
    (R := R)
    (HahnEmbedding.ArchimedeanStrata.closedBallEquivStratumLexBall u c) x
    (HahnEmbedding.ArchimedeanStrata.stratumLexBallEquivClosedBall u c (toLex (s, b)))
  rw [HahnEmbedding.ArchimedeanStrata.closedBallEquivStratumLexBall_stratumLexBallEquivClosedBall]
    at h
  exact h

end HahnSeries
