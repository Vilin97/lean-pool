/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.FieldTheory.Galois.Basic
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.PrimeComparison
/-!
# Intrinsic Frobenius Artin comparison

This module identifies the canonical local Artin homomorphism of an actual
finite fixed-field extension with its ambient fixed-field norm-residue symbol.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation
open scoped ValuativeRel

section IntrinsicFixedFieldArtinComparison

variable
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : FiniteAbstractField
      Gal(SeparableClosure K / K))
    (J : ClosedSubgroup Gal(SeparableClosure K / K))
    (hJH : J.toSubgroup ≤ H.field.toSubgroup)
    [hJnormal : (extensionSubgroup H.field J hJH).Normal]
    [hJfinite : Finite
      (H.field.toSubgroup ⧸ extensionSubgroup H.field J hJH)]

local instance intrinsicFixedFieldArtin_absoluteFinite :
    Finite
      ((baseField
        Gal(SeparableClosure K / K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K / K))
          H.field (le_baseField H.field)) :=
  H.finite

/-- The canonical local Artin homomorphism of the actual finite fixed-field
extension agrees with the ambient fixed-field norm-residue symbol.  The proof
uses the given valuation-preserving equivalence of separable closures to
construct actual norm-class representatives. -/
theorem
    intrinsicFixedFieldLocalArtinMonoidHom_eq_abstractFixedFieldNormResidueSymbol
    (e : intrinsicFixedFieldSeparableClosureEquiv K H) :
    intrinsicFixedFieldLocalArtinMonoidHom K H J hJH =
      abstractFixedFieldNormResidueSymbol
        K (SeparableClosure K)
        (localResidueDatum K)
        (localHenselianValuation K)
        (separableClosureUnits_isClassFormation K)
        H.field J hJH := by
  apply AddMonoidHom.ext
  intro a
  let aF :
      (abstractFixedField K (SeparableClosure K) H.field)ˣ :=
    Additive.toMul a
  obtain ⟨x, hnormClass, hprime⟩ :=
    exists_intrinsicFixedFieldNormClassRepresentative
      K H J hJH e aF
  have hambientSame :
      abstractFixedFieldNormResidueSymbol
          K (SeparableClosure K)
          (localResidueDatum K)
          (localHenselianValuation K)
          (separableClosureUnits_isClassFormation K)
          H.field J hJH (Additive.ofMul aF) =
        abstractFixedFieldNormResidueSymbol
          K (SeparableClosure K)
          (localResidueDatum K)
          (localHenselianValuation K)
          (separableClosureUnits_isClassFormation K)
          H.field J hJH (Additive.ofMul x) :=
    abstractFixedFieldNormResidueSymbol_eq_of_normClass_eq
      K (SeparableClosure K)
      (localResidueDatum K)
      (localHenselianValuation K)
      (separableClosureUnits_isClassFormation K)
      H.field J hJH aF x hnormClass
  change
    intrinsicFixedFieldLocalArtinMonoidHom
      K H J hJH (Additive.ofMul aF) =
      abstractFixedFieldNormResidueSymbol
        K (SeparableClosure K)
        (localResidueDatum K)
        (localHenselianValuation K)
        (separableClosureUnits_isClassFormation K)
        H.field J hJH (Additive.ofMul aF)
  calc
    intrinsicFixedFieldLocalArtinMonoidHom
        K H J hJH (Additive.ofMul aF) =
        abstractFixedFieldNormResidueSymbol
          K (SeparableClosure K)
          (localResidueDatum K)
          (localHenselianValuation K)
          (separableClosureUnits_isClassFormation K)
          H.field J hJH (Additive.ofMul x) :=
      hprime.symm
    _ = abstractFixedFieldNormResidueSymbol
          K (SeparableClosure K)
          (localResidueDatum K)
          (localHenselianValuation K)
          (separableClosureUnits_isClassFormation K)
          H.field J hJH (Additive.ofMul aF) :=
      hambientSame.symm

end IntrinsicFixedFieldArtinComparison

end LocalClassFieldTheory
