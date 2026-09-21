/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalKoszulContradiction
import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalGabberInvolutivityInterface
import LeanPool.Stafford38.Stafford38.Geometry.ExactDivisorialVisibleFrameExistence
import LeanPool.Stafford38.Stafford38.PaperInputs
import LeanPool.Stafford38.Stafford38.Geometry.GeneralCoisotropicCanonicalAdapter

/-! The paper's three assembly interfaces and both universal statements are
proved from Lean and Mathlib without project or literature axioms. The final
canonical-support proof uses the general coisotropic-set theorem.

## References and proof context

[Sta78] J. T. Stafford, *Module Structure of Weyl Algebras*, Journal of the London Mathematical Society (2) 18 (1978), 429–442.
https://doi.org/10.1112/jlms/s2-18.3.429

Conjecture 3.8, p. 438, is the source problem. This project proves the general case and exact-degree strengthening. See docs/literature.md for the imported involutivity and visible-frame route.
-/

namespace Stafford38.FoundationClosure

universe u

theorem canonicalNoncharacteristicSupportAvoidance :
    PaperInputs.CanonicalNoncharacteristicSupportAvoidance.{u} := by
  intro k _ _ _ n N d hN hd
  exact Characteristic.CanonicalKoszulContradiction.canonical_support_avoidance
    k n N d hN hd

def inputs : PaperInputs.Inputs.{u} where
  noncharacteristicApplication := canonicalNoncharacteristicSupportAvoidance
  residueExtensionSymbolControl :=
    Characteristic.CanonicalGabberInvolutivityInterface.canonicalResidueExtensionSymbolControl_of_associatedGradedRadical
      Characteristic.GabberGlobalAssembly.weylAssociatedGradedRadicalInvolutivity
  higherDimensionalVisibleDivisorFrameProduction :=
    Geometry.ExactDivisorialVisibleFrameExistence.higherDimensionalCanonicalVisibleDivisorFrameProduction

theorem canonicalSupportVanishingViaGeneralCoisotropic :
    UniversalAssembly.CanonicalSupportVanishing.{u} := by
  let hunit : CanonicalSupportVanishingReduction.CanonicalStrictUnitCoordinatePreimage.{u} := by
    intro k _ _ _ n N d hN hd
    exact SpecializedNoncharacteristicEquality.strictUnitCoordinatePreimage_of_transposedSupport_disjoint_axis
      k n N d (canonicalNoncharacteristicSupportAvoidance k n N d hN hd)
  exact Weyl.FilteredScalarLifting.canonicalSupportDescent
    (Geometry.GeneralCoisotropicCanonicalAdapter.algebraicallyClosedCanonicalSupportVanishing_of_generalCoisotropic
      hunit)

end Stafford38.FoundationClosure

namespace Stafford38

universe u

theorem universalStatement : UniversalStatement.{u} :=
  UniversalAssembly.universalStatement_of_canonicalSupportVanishing
    FoundationClosure.canonicalSupportVanishingViaGeneralCoisotropic

theorem universalFixedSourceStatement : FixedSource.UniversalFixedSourceStatement.{u} :=
  FixedSource.universalFixedSourceStatement_of_canonicalSupportVanishing
    FoundationClosure.canonicalSupportVanishingViaGeneralCoisotropic


end Stafford38
