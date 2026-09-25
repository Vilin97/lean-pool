/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.MaximalUnramifiedSymbol
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Main
public import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.IntegralRepUniverse
/-!
# Abstract reciprocity, maximal-unramified reciprocity

The maximal-unramified norm-residue symbol is realized by the
valuation--Frobenius map whose restriction to every finite unramified
extension is the inverse of the unramified norm-quotient equivalence.  This file first proves that
finite compatibility and then records the two formulas.
-/

@[expose] public section

noncomputable
section

namespace ClassFormation

open ClassFormation CyclicCohomology KummerTheory

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

namespace ValuationData

/-- On every finite unramified quotient, the maximal-unramified symbol is
the inverse of the actual reciprocity equivalence of the unramified norm-quotient equivalence.
This is the inverse-limit compatibility used to define the infinite symbol. -/
theorem maximalUnramifiedNormResidueSymbol_finiteRestriction
    (v : ValuationData D A) (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field)
    (hUnramified : L.IsUnramified D) :
    letI : Finite (K.field.toSubgroup ⧸
        extensionSubgroup K.field L.field L.below) := L.finite
    ∀ a : ambientFixedAddSubgroup A K.field,
    Additive.ofMul
        (DegreeData.finiteUnramifiedRestriction D
          (K.toFiniteResidueAbstractField D) L hUnramified
          (maximalUnramifiedNormResidueSymbol v K a).toMul) =
      (v.unramifiedReciprocityEquiv hAxiom
        K L.field L.below hUnramified).symm
        (finiteNormClass A K.field L.field L.below a) := by
  let : Finite (K.field.toSubgroup ⧸
      extensionSubgroup K.field L.field L.below) := L.finite
  intro a
  exact (maximalUnramifiedNormResidueSymbol_finiteRestriction_of_generator v hAxiom
    K L hUnramified
      (D.finiteReciprocityHom A v hAxiom K L.field L.below)
      (v.unramifiedReciprocity_frobenius_image hAxiom
        K L.field L.below hUnramified) a).symm

/-- For a finite unramified extension, the restriction of the
maximal-unramified norm-residue symbol is exactly the finite abstract
norm-residue symbol.  This is the source-level bridge from maximal
unramified reciprocity to the finite reciprocity theorem. -/
theorem normResidueSymbol_finiteNormClass_eq_maximalUnramifiedRestriction
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field)
    (hUnramified : L.IsUnramified D)
    (a : ambientFixedAddSubgroup A K.field) :
    letI : Finite
        (K.field.toSubgroup ⧸
          extensionSubgroup K.field L.field L.below) := L.finite
    D.normResidueSymbol A v hcf K L
        (finiteNormClass A K.field L.field L.below a) =
      Additive.ofMul
        (Abelianization.of
          (DegreeData.finiteUnramifiedRestriction D
            (K.toFiniteResidueAbstractField D) L hUnramified
            (maximalUnramifiedNormResidueSymbol v K a).toMul)) := by
  let : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field L.field L.below) := L.finite
  let hAxiom :=
    v.classFieldAxiom_implies_unramifiedUnitCohomology hcf
  let q :=
    DegreeData.finiteUnramifiedRestriction D
      (K.toFiniteResidueAbstractField D) L hUnramified
      (maximalUnramifiedNormResidueSymbol v K a).toMul
  have hrestriction :=
    maximalUnramifiedNormResidueSymbol_finiteRestriction
      v hAxiom K L hUnramified a
  have hreciprocity :
      v.unramifiedReciprocityEquiv hAxiom
          K L.field L.below hUnramified
          (Additive.ofMul q) =
        finiteNormClass A K.field L.field L.below a := by
    calc
      _ =
          v.unramifiedReciprocityEquiv hAxiom
            K L.field L.below hUnramified
            ((v.unramifiedReciprocityEquiv hAxiom
              K L.field L.below hUnramified).symm
              (finiteNormClass A K.field L.field L.below a)) :=
        congrArg
          (v.unramifiedReciprocityEquiv hAxiom
            K L.field L.below hUnramified)
          hrestriction
      _ = _ :=
        (v.unramifiedReciprocityEquiv hAxiom
          K L.field L.below hUnramified).apply_symm_apply _
  have hfinite : D.finiteReciprocityHom A v hAxiom K L.field L.below
        (Additive.ofMul q) = finiteNormClass A K.field L.field L.below a :=
    (v.unramifiedReciprocityEquiv_apply hAxiom K L.field L.below hUnramified
      (Additive.ofMul q)).symm.trans hreciprocity
  exact (congrArg (D.normResidueSymbol A v hcf K L) hfinite.symm).trans
    (D.normResidueSymbol_finiteReciprocityHom A v hcf K L q)

end ValuationData

end ClassFormation
