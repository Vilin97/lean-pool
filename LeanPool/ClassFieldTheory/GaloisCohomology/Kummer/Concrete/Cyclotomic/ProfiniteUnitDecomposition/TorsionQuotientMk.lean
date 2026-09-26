/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.TorsionQuotientEquiv
/-!
# Evaluation of the torsion-quotient equivalence
-/

@[expose] public section

open scoped Topology

noncomputable
section

namespace KummerTheory

open ClassFormation

/-- The torsion-quotient equivalence evaluates a quotient class by
taking the genuine torsion-free coordinate of the chosen product
decomposition.  This is the commuting square needed to pass between an
actual cyclotomic character and the `ZHat`-coordinate of its torsion
fixed field. -/
@[simp]
theorem torsionQuotientEquivOfZHatMulDecomposition_mk
    (G T : Type*) [CommGroup G] [CommGroup T]
    [TopologicalSpace G] [TopologicalSpace T]
    [IsTopologicalGroup G] [IsTopologicalGroup T]
    [CompactSpace G]
    (E : G ≃ₜ* Multiplicative ZHat × T)
    (hT : Dense (CommGroup.torsion T : Set T))
    (g : G) :
    torsionQuotientEquivOfZHatMulDecomposition
        G T E hT (QuotientGroup.mk g) =
      (E g).1 := by
  rfl

end KummerTheory
