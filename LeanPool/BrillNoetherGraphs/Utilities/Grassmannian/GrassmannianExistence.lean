/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Grassmannian.GrassmannianShift
public import LeanPool.BrillNoetherGraphs.Utilities.Grassmannian.OnceMarked

/-!
# Grassmannian transmission existence: the universal interface

`GrassmannianTransmissionExistence` and its equivalence with the once-marked
Brill--Noether statement, rehomed from `GrassmannianLowGenus.lean` (which
imports this file and keeps the genus-bounded consequences) so that the
genus-generic transmission layer does not depend on the low-genus census.
-/

@[expose] public section

namespace Utilities

/-- Every shifted Grassmannian transmission problem allowed by the genus has
a witness.  The second mark is retained because it belongs to the
transmission presentation, although the Grassmannian locus depends only on
the first mark up to existence. -/
def GrassmannianTransmissionExistence
    (G : CFGraph) (u v : G.V) : Prop :=
  ∀ lambda : YoungDiagram,
    (lambda.card : ℤ) ≤ genus G →
      ∀ chi : ℤ,
        TransmissionExists G u v (shiftedGrassmannianPerm lambda chi)

/-- The universal Grassmannian transmission statement is exactly the
once-marked Brill--Noether statement. -/
theorem grassmannianTransmissionExistence_iff_onceMarkedBNExistence
    {G : CFGraph} (hG : graphConnected G) (u v : G.V) :
    GrassmannianTransmissionExistence G u v ↔
      OnceMarkedBNExistence G u := by
  constructor
  · intro hTransmission lambda hSize
    exact (transmissionExists_shiftedGrassmannianPerm_iff_onceMarkedBNExists
      hG u v lambda 0).mp (hTransmission lambda hSize 0)
  · intro hMarked lambda hSize chi
    exact (transmissionExists_shiftedGrassmannianPerm_iff_onceMarkedBNExists
      hG u v lambda chi).mpr (hMarked lambda hSize)

end Utilities
