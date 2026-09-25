/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.TorsionQuotientMk
/-!
# The cyclotomic profinite-unit torsion quotient
-/

@[expose] public section

open scoped Topology

noncomputable section

namespace KummerTheory

open ClassFormation

/-- Cyclotomic-character form of the torsion decomposition: quotienting `ℤ̂ˣ` by
the closure of its torsion subgroup leaves one copy of `ℤ̂`. -/
noncomputable def zHatUnitsTorsionQuotientEquiv :
    ZHatˣ ⧸ (CommGroup.torsion ZHatˣ).topologicalClosure ≃ₜ*
      Multiplicative ZHat :=
  torsionQuotientEquivOfZHatMulDecomposition
    ZHatˣ CyclotomicFinitePart
      zHatUnitsDecomposition
        dense_torsion_cyclotomicFinitePart

end KummerTheory
