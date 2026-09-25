/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ClassField
/-!
# Profinite reciprocity facade

This module specializes the three principal finite reciprocity endpoints to a
bundled profinite group.  The bundle supplies the ambient topology, compactness,
separation, and total disconnectedness instances required by the generic
theorems.
-/

@[expose] public section

noncomputable
section

namespace ClassFormation.Profinite

open CyclicCohomology KummerTheory

/-- The finite abelian norm-subgroup classification for a bundled profinite
group.  This is the thin specialization of the existing generic order
isomorphism; the profinite bundle supplies all ambient topological instances. -/
noncomputable def normSubgroupOrderIso
    (P : ProfiniteGrp) {D : DegreeData P} {A : Rep ℤ P}
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    (K : FiniteAbstractField P) :
    FiniteAbelianSubextension K.field ≃o
      (FiniteAbelianSubextension.NormOpenAddSubgroup A K.field)ᵒᵈ :=
  FiniteAbelianSubextension.normSubgroupOrderIso v hcf K

/-- The class field attached to a norm-open subgroup for a bundled profinite
group.  This thin specialization consumes the profinite norm-subgroup facade,
so callers do not enumerate ambient topological instances. -/
noncomputable def classField
    (P : ProfiniteGrp) {D : DegreeData P} {A : Rep ℤ P}
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    (K : FiniteAbstractField P)
    (N : FiniteAbelianSubextension.NormOpenAddSubgroup A K.field) :
    FiniteAbelianSubextension K.field :=
  (normSubgroupOrderIso P v hcf K).symm (OrderDual.toDual N)

/-- The finite norm-residue symbol for a bundled profinite group.  This is the
thin specialization of the existing generic symbol; the profinite bundle
supplies all ambient topological instances. -/
noncomputable def normResidueSymbol
    (P : ProfiniteGrp) (D : DegreeData P) (A : Rep ℤ P)
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    (K : FiniteAbstractField P) (L : FiniteGaloisSubextension K.field) :
    letI : Finite
        (K.field.toSubgroup ⧸
          extensionSubgroup K.field L.field L.below) := L.finite
    FiniteNormQuotient A K.field L.field L.below ≃+
      Additive (Abelianization L.extensionQuotient) :=
  D.normResidueSymbol A v hcf K L

end ClassFormation.Profinite
