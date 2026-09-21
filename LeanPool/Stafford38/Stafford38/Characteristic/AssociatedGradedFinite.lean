/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Characteristic.AssociatedGradedModule
import LeanPool.Stafford38.Stafford38.Characteristic.SquareZeroLocalizedExactness

/-!
# Finiteness of the actual order-associated graded module

The actual associated graded quotient is cyclic over the commutative symbol
ring.  This file records the resulting `Module.Finite` instance and feeds it
to the already checked minimal-prime localization theorem.  No Noetherian,
trace, or involutivity conclusion is hidden in the construction.
-/

namespace Stafford38.Characteristic.AssociatedGradedFinite

open Stafford38.Characteristic
open Stafford38.CharacteristicAssociatedGradedModule
open Stafford38.CharacteristicConcreteSquareZeroTraceData
open Stafford38.Characteristic.SquareZeroLocalizedExactness
open Stafford38.EulerSurjectivity
open Stafford38.WeylIteratedEquivalence

noncomputable section

universe u

variable (k : Type u) [Field k]
variable {n : ℕ}

/-- The cyclic presentation map from the symbol ring to the literal external
direct sum associated graded module. -/
def generatorMap (I : RightIdeal (PresentedWeyl k n)) :
    SymbolRing k n →ₗ[SymbolRing k n] OrderAssociatedGradedModule k I :=
  LinearMap.toSpanSingleton (SymbolRing k n)
    (OrderAssociatedGradedModule k I)
    (orderAssociatedGradedGenerator k I)

/-- Cyclicity of the actual associated graded object is surjectivity of its
literal one-generator presentation map. -/
theorem generatorMap_surjective (I : RightIdeal (PresentedWeyl k n)) :
    Function.Surjective (generatorMap k I) := by
  intro q
  obtain ⟨P, hP⟩ := exists_smul_orderAssociatedGradedGenerator k I q
  exact ⟨P, by simpa [generatorMap, LinearMap.toSpanSingleton_apply] using hP⟩

/-- The literal order-associated graded quotient is finite over the symbol
ring, with one generator. -/
noncomputable instance orderAssociatedGradedModule_finite
    (I : RightIdeal (PresentedWeyl k n)) :
    Module.Finite (SymbolRing k n) (OrderAssociatedGradedModule k I) :=
  Module.Finite.of_surjective (generatorMap k I) (generatorMap_surjective k I)

/-- Concrete minimal-prime localization package with no unproduced finiteness
hypothesis: exact two-jet specialization, nontrivial localized fibre, and
finite length all hold at a minimal prime over the actual annihilator. -/
theorem exists_minimalPrimeLocalizedExactnessAndFiniteLength
    [IsNoetherianRing (SymbolRing k n)]
    (I : RightIdeal (PresentedWeyl k n))
    (P : Ideal (SymbolRing k n)) [P.IsPrime]
    (hP : P ∈
      (Module.annihilator (SymbolRing k n)
        (OrderAssociatedGradedModule k I)).minimalPrimes) :
    ∃ h : OreLocalization.OreSet
        (OppositeDenominators (filteredQuotientTwoJetTraceData k I)
          P.primeCompl),
      LocalizedExactnessFor (filteredQuotientTwoJetTraceData k I)
          P.primeCompl h ∧
        Nontrivial
          (LocalizedModule P.primeCompl (OrderAssociatedGradedModule k I)) ∧
        IsFiniteLength (Localization P.primeCompl)
          (LocalizedModule P.primeCompl
            (OrderAssociatedGradedModule k I)) :=
  SquareZeroLocalizedExactness.exists_minimalPrimeLocalizedExactnessAndFiniteLength
    (filteredQuotientTwoJetTraceData k I) P hP


end

end Stafford38.Characteristic.AssociatedGradedFinite
