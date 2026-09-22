/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ConcreteReciprocityCanonical
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TopologicalReciprocity
/-!
# Conjugation naturality of finite local reciprocity

Two realizations of a finite Galois extension inside the fixed separable
closure are related by conjugation. This module transports that conjugation
to the actual Galois group, records the algebraic norm-residue square, and
bundles the resulting map on the topological abelianization continuously.
-/

noncomputable section

namespace LocalClassFieldTheory

open scoped ValuativeRel
open LocalFieldTheory

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- Conjugation between two separable-closure realizations, transported to
the abelianization of the actual relative Galois group. -/
noncomputable def abelianizedGaloisConjugationOfEmbeddings
    (i j : L →ₐ[K] SeparableClosure K) :
    Abelianization (Gal(L/K)) ≃* Abelianization (Gal(L/K)) :=
  (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i).abelianizationCongr.symm.trans
    ((finiteGaloisConjugationOfEmbeddings K L i j).abelianizationCongr.trans
      (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L j).abelianizationCongr)

/-- After both realizations are identified with the actual extension, the
transported conjugation is the identity on the abelianization. -/
theorem abelianizedGaloisConjugationOfEmbeddings_eq_refl
    (i j : L →ₐ[K] SeparableClosure K) :
    abelianizedGaloisConjugationOfEmbeddings K L i j =
      MulEquiv.refl (Abelianization (Gal(L/K))) := by
  apply MulEquiv.ext
  intro z
  change
    (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L j).abelianizationCongr
        ((finiteGaloisConjugationOfEmbeddings K L i j).abelianizationCongr
          ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L
            i).abelianizationCongr.symm z)) =
      z
  exact
    (finiteGaloisAbstractQuotientEquivGaloisGroup_conjugation
        K L i j
        ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
          K L i).abelianizationCongr.symm z)).trans
      ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
        K L i).abelianizationCongr.apply_symm_apply z)

/-- Algebraic conjugation naturality for the norm-residue symbols computed
from two explicit realizations of the same finite Galois extension. -/
theorem concreteNormResidueSymbolOfEmbedding_conjugation
    (i j : L →ₐ[K] SeparableClosure K)
    (D : ClassFormation.DegreeData (Gal(SeparableClosure K/K)))
    (v : ClassFormation.ValuationData D
      (galoisAmbientUnitsRep K (SeparableClosure K)))
    (hcf : ClassFormation.SatisfiesClassFieldAxiom
      (galoisAmbientUnitsRep K (SeparableClosure K))) :
    (abelianizedGaloisConjugationOfEmbeddings K L i j).toMonoidHom.comp
        (concreteNormResidueSymbolOfEmbedding K L i D v hcf) =
      concreteNormResidueSymbolOfEmbedding K L j D v hcf := by
  rw [abelianizedGaloisConjugationOfEmbeddings_eq_refl]
  change concreteNormResidueSymbolOfEmbedding K L i D v hcf =
    concreteNormResidueSymbolOfEmbedding K L j D v hcf
  unfold concreteNormResidueSymbolOfEmbedding
  rw [concreteReciprocityEquivOfEmbedding_eq K L i j D v hcf]

section LocalAlgebraic

variable [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Field-facing algebraic form of the second naturality diagram for the
canonical local class formation. -/
theorem localArtinMonoidHom_conjugation
    (i j : L →ₐ[K] SeparableClosure K) :
    (abelianizedGaloisConjugationOfEmbeddings K L i j).toMonoidHom.comp
        (concreteNormResidueSymbolOfEmbedding K L i
          (localResidueDatum K) (localHenselianValuation K)
          (separableClosureUnits_isClassFormation K)) =
      concreteNormResidueSymbolOfEmbedding K L j
        (localResidueDatum K) (localHenselianValuation K)
        (separableClosureUnits_isClassFormation K) :=
  concreteNormResidueSymbolOfEmbedding_conjugation K L i j
    (localResidueDatum K) (localHenselianValuation K)
    (separableClosureUnits_isClassFormation K)
end LocalAlgebraic


/-- The conjugation of two realizations, bundled continuously on the
topological abelianization of the finite Krull Galois group. -/
noncomputable def topologicalAbelianizationConjugationOfEmbeddings
    (i j : L →ₐ[K] SeparableClosure K) :
    TopologicalAbelianization (Gal(L/K)) ≃ₜ*
      TopologicalAbelianization (Gal(L/K)) := by
  letI : DiscreteTopology (TopologicalAbelianization (Gal(L/K))) :=
    QuotientGroup.discreteTopology (isOpen_discrete _)
  let e : TopologicalAbelianization (Gal(L/K)) ≃*
      TopologicalAbelianization (Gal(L/K)) :=
    (topologicalAbelianizationFiniteEquiv K L).symm.trans
      ((abelianizedGaloisConjugationOfEmbeddings K L i j).trans
        (topologicalAbelianizationFiniteEquiv K L))
  exact
    { e with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

/-- Forgetting topology identifies the bundled conjugation with the
algebraic conjugation through the finite abelianization comparison. -/
theorem topologicalAbelianizationConjugationOfEmbeddings_toMonoidHom
    (i j : L →ₐ[K] SeparableClosure K) :
    (topologicalAbelianizationFiniteEquiv K L).symm.toMonoidHom.comp
        (topologicalAbelianizationConjugationOfEmbeddings K L i j).toMonoidHom =
      (abelianizedGaloisConjugationOfEmbeddings K L i j).toMonoidHom.comp
        (topologicalAbelianizationFiniteEquiv K L).symm.toMonoidHom := by
  ext x
  rfl

section LocalContinuous

variable [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The continuous local Artin map is equivariant for conjugation between
two realizations of the finite Galois extension. -/
theorem localArtinMap_conjugation
    (i j : L →ₐ[K] SeparableClosure K) :
    (ContinuousMonoidHom.toContinuousMonoidHom
        (topologicalAbelianizationConjugationOfEmbeddings K L i j)).comp
        (localArtinMap K L) =
      localArtinMap K L := by
  apply ContinuousMonoidHom.ext
  intro x
  change
    (topologicalAbelianizationFiniteEquiv K L)
        ((abelianizedGaloisConjugationOfEmbeddings K L i j)
          ((topologicalAbelianizationFiniteEquiv K L).symm
            (localArtinMap K L x))) =
      localArtinMap K L x
  rw [abelianizedGaloisConjugationOfEmbeddings_eq_refl]
  exact (topologicalAbelianizationFiniteEquiv K L).apply_symm_apply _

end LocalContinuous

end LocalClassFieldTheory
