/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Galois.AbsoluteAbelianization
/-!
# Relative topological abelianization

For a possibly infinite Galois extension `M/F`, this file identifies the
topological abelianization of `Gal(M/F)` with the Galois group of the
intermediate field fixed by the closed commutator subgroup.
-/

open scoped IsMulCommutative

noncomputable section

universe u v

namespace ClassFieldTower.Martinet

variable (F : Type u) (M : Type v)
variable [Field F] [Field M] [Algebra F M] [IsGalois F M]

/-- Closed commutator subgroup of a relative, possibly infinite, Galois
group. -/
def relativeCommutatorClosure : ClosedSubgroup Gal(M/F) where
  toSubgroup := (commutator Gal(M/F)).topologicalClosure
  isClosed' := Subgroup.isClosed_topologicalClosure _

local instance relativeCommutatorClosure_normal :
    (relativeCommutatorClosure F M).Normal := by
  change ((commutator Gal(M/F)).topologicalClosure).Normal
  infer_instance

/-- Maximal abelian intermediate field of a relative Galois extension. -/
def relativeMaximalAbelianSubextension : IntermediateField F M :=
  IntermediateField.fixedField (relativeCommutatorClosure F M).toSubgroup

/-- The relative maximal abelian subextension is Galois. -/
theorem relativeMaximalAbelianSubextension_isGalois :
    IsGalois F (relativeMaximalAbelianSubextension F M) := by
  apply (InfiniteGalois.normal_iff_isGalois
    (relativeMaximalAbelianSubextension F M)).1
  change (IntermediateField.fixedField
    (relativeCommutatorClosure F M).toSubgroup).fixingSubgroup.Normal
  rw [InfiniteGalois.fixingSubgroup_fixedField
    (relativeCommutatorClosure F M)]
  infer_instance

local instance relativeMaximalAbelianSubextension.instIsGalois :
    IsGalois F (relativeMaximalAbelianSubextension F M) :=
  relativeMaximalAbelianSubextension_isGalois F M

/-- Algebraic quotient equivalence for relative abelianization. -/
noncomputable def relativeAbelianizationMulEquiv :
    TopologicalAbelianization Gal(M/F) ≃*
      Gal(relativeMaximalAbelianSubextension F M/F) :=
  InfiniteGalois.normalAutEquivQuotient (relativeCommutatorClosure F M)

/-- The quotient equivalence sends a class to restriction. -/
@[simp]
theorem relativeAbelianizationMulEquiv_mk (sigma : Gal(M/F)) :
    relativeAbelianizationMulEquiv F M (QuotientGroup.mk sigma) =
      AlgEquiv.restrictNormalHom (relativeMaximalAbelianSubextension F M) sigma :=
  rfl

/-- The algebraic relative-abelianization equivalence is continuous. -/
theorem relativeAbelianizationMulEquiv_continuous :
    Continuous (relativeAbelianizationMulEquiv F M) := by
  apply (QuotientGroup.isQuotientMap_mk
    (relativeCommutatorClosure F M).toSubgroup).continuous_iff.2
  refine (InfiniteGalois.restrictNormalHom_continuous
    (relativeMaximalAbelianSubextension F M)).congr ?_
  intro sigma
  exact (relativeAbelianizationMulEquiv_mk F M sigma).symm

/-- The topological abelianization is the Galois group of the maximal
relative abelian subfield. -/
noncomputable def relativeTopologicalAbelianizationEquiv :
    TopologicalAbelianization Gal(M/F) ≃ₜ*
      Gal(relativeMaximalAbelianSubextension F M/F) := by
  let h := Continuous.homeoOfEquivCompactToT2
    (relativeAbelianizationMulEquiv_continuous F M)
  exact
    { toMulEquiv := relativeAbelianizationMulEquiv F M
      continuous_toFun := h.continuous
      continuous_invFun := h.symm.continuous }

end ClassFieldTower.Martinet
