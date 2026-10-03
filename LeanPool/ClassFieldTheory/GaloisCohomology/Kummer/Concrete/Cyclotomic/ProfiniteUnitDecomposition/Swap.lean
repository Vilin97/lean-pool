/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.Gather
/-!
# Compiled final swap stage of the profinite-unit decomposition
-/

@[expose] public section

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup renaming
  continuousMulEquivProdComm →
    continuousMulEquivProdComm


open scoped Topology

noncomputable
section

namespace KummerTheory.ProfiniteUnitDecomposition.Internal

open ClassFormation

/-- Swap the collected free and finite coordinates. -/
noncomputable def freeFiniteSwap :
    CyclotomicFinitePart × Multiplicative ZHat ≃ₜ*
      Multiplicative ZHat × CyclotomicFinitePart :=
  continuousMulEquivProdComm
    CyclotomicFinitePart (Multiplicative ZHat)

end KummerTheory.ProfiniteUnitDecomposition.Internal
