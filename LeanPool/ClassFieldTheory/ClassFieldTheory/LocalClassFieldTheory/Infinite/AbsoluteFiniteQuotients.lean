/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Infinite.AbsoluteGaloisAbelianization
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.NormResidueNaturality
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits
/-!
# Finite quotients of the absolute abelianized Galois group

Every open normal subgroup of the profinite topological abelianization of
the absolute Galois group determines a finite abelian subextension of the
fixed separable closure.  The corresponding finite quotient is canonically
identified, as a topological group, with the actual Galois group of that
subextension.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory

variable (K : Type) [Field K]

/-- The absolute topological abelianization, regarded as a stable profinite
group. -/
noncomputable def localAbsoluteAbelianProfinite : ProfiniteGrp :=
  ProfiniteGrp.of
    (TopologicalAbelianization (intrinsicAbsoluteGalois K))

/-- The profinite absolute abelianization carries the commutative group structure of the
topological abelianization. -/
local instance localAbsoluteAbelianProfiniteCommGroup :
    CommGroup (localAbsoluteAbelianProfinite K) := by
  change CommGroup (TopologicalAbelianization (intrinsicAbsoluteGalois K))
  infer_instance

/-- The quotient map from the absolute Galois group to its topological
abelianization. -/
def localAbsoluteAbelianizationQuotientMap :
    intrinsicAbsoluteGalois K →*
      localAbsoluteAbelianProfinite K :=
  QuotientGroup.mk'
    (commutator (intrinsicAbsoluteGalois K)).topologicalClosure

/-- The open normal preimage in the absolute Galois group of an open normal
subgroup of its topological abelianization. -/
def absoluteFiniteQuotientPreimage
    (N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K)) :
    OpenNormalSubgroup (intrinsicAbsoluteGalois K) where
  toSubgroup := N.toSubgroup.comap
    (localAbsoluteAbelianizationQuotientMap K)
  isOpen' := N.isOpen'.preimage QuotientGroup.continuous_mk
  isNormal' := by infer_instance

/-- The same preimage, packaged as a closed subgroup for infinite Galois
correspondence. -/
def absoluteFiniteQuotientClosedPreimage
    (N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K)) :
    ClosedSubgroup (intrinsicAbsoluteGalois K) where
  toSubgroup := (absoluteFiniteQuotientPreimage K N).toSubgroup
  isClosed' := Subgroup.isClosed_of_isOpen _
    (absoluteFiniteQuotientPreimage K N).isOpen'

/-- The closed preimage of an open normal subgroup in the abelianization is normal. -/
instance absoluteFiniteQuotientClosedPreimage_normal
    (N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K)) :
    (absoluteFiniteQuotientClosedPreimage K N).Normal := by
  change (absoluteFiniteQuotientPreimage K N).toSubgroup.Normal
  infer_instance

/-- The finite subextension cut out by an open normal subgroup of the
absolute topological abelianization. -/
def absoluteFiniteQuotientField
    (N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K)) :
    IntermediateField K (SeparableClosure K) :=
  IntermediateField.fixedField
    (absoluteFiniteQuotientPreimage K N).toSubgroup

/-- The fixed field attached to an open finite abelian quotient is Galois over `K`. -/
instance absoluteFiniteQuotientField_isGalois
    (N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K)) :
    IsGalois K (absoluteFiniteQuotientField K N) := by
  apply (InfiniteGalois.normal_iff_isGalois
    (absoluteFiniteQuotientField K N)).1
  change
    (IntermediateField.fixedField
      (absoluteFiniteQuotientClosedPreimage K N).toSubgroup).fixingSubgroup.Normal
  rw [InfiniteGalois.fixingSubgroup_fixedField
    (absoluteFiniteQuotientClosedPreimage K N)]
  infer_instance

/-- The fixed field attached to an open finite quotient is finite-dimensional over `K`. -/
instance absoluteFiniteQuotientField_finiteDimensional
    (N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K)) :
    FiniteDimensional K (absoluteFiniteQuotientField K N) := by
  apply (InfiniteGalois.isOpen_iff_finite
    (absoluteFiniteQuotientField K N)).1
  change IsOpen
    ((IntermediateField.fixedField
      (absoluteFiniteQuotientClosedPreimage K N).toSubgroup).fixingSubgroup :
      Set (intrinsicAbsoluteGalois K))
  rw [InfiniteGalois.fixingSubgroup_fixedField
    (absoluteFiniteQuotientClosedPreimage K N)]
  exact (absoluteFiniteQuotientPreimage K N).isOpen'

/-- The topological commutator closure is contained in every pulled-back
open normal subgroup. -/
theorem localAbsoluteCommutatorClosure_le_finiteQuotientPreimage
    (N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K)) :
    (commutator (intrinsicAbsoluteGalois K)).topologicalClosure ≤
      (absoluteFiniteQuotientPreimage K N).toSubgroup := by
  intro σ hσ
  change localAbsoluteAbelianizationQuotientMap K σ ∈ N
  have hmk : localAbsoluteAbelianizationQuotientMap K σ = 1 :=
    (QuotientGroup.eq_one_iff σ).2 hσ
  rw [hmk]
  exact N.one_mem

/-- Pullback followed by image under the abelianization quotient recovers
the original open normal subgroup. -/
theorem finiteQuotientPreimage_map_eq
    (N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K)) :
    (absoluteFiniteQuotientPreimage K N).toSubgroup.map
        (localAbsoluteAbelianizationQuotientMap K) =
      N.toSubgroup := by
  change
    (N.toSubgroup.comap (localAbsoluteAbelianizationQuotientMap K)).map
        (localAbsoluteAbelianizationQuotientMap K) = N.toSubgroup
  exact Subgroup.map_comap_eq_self_of_surjective
    (QuotientGroup.mk'_surjective
      (commutator (intrinsicAbsoluteGalois K)).topologicalClosure)
    N.toSubgroup

/-- Mapping the quotient preimage into the abelianization produces a normal subgroup. -/
instance absoluteFiniteQuotientPreimageMap_normal
    (N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K)) :
    ((absoluteFiniteQuotientPreimage K N).toSubgroup.map
      (localAbsoluteAbelianizationQuotientMap K)).Normal := by
  rw [finiteQuotientPreimage_map_eq K N]
  exact N.isNormal'

/-- The algebraic finite quotient identification, obtained from the third
isomorphism theorem and infinite Galois correspondence. -/
noncomputable def absoluteFiniteQuotientMulEquiv
    (N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K)) :
    localAbsoluteAbelianProfinite K ⧸ N.toSubgroup ≃*
      Gal(absoluteFiniteQuotientField K N/K) :=
  (QuotientGroup.quotientMulEquivOfEq
      (finiteQuotientPreimage_map_eq K N).symm).trans
    ((QuotientGroup.quotientQuotientEquivQuotient
      (commutator (intrinsicAbsoluteGalois K)).topologicalClosure
      (absoluteFiniteQuotientPreimage K N).toSubgroup
      (localAbsoluteCommutatorClosure_le_finiteQuotientPreimage K N)).trans
        (InfiniteGalois.normalAutEquivQuotient
          (absoluteFiniteQuotientClosedPreimage K N)))

/-- The canonical topological finite quotient identification. -/
noncomputable def absoluteFiniteQuotientEquiv
    (N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K)) :
    localAbsoluteAbelianProfinite K ⧸ N.toSubgroup ≃ₜ*
      Gal(absoluteFiniteQuotientField K N/K) := by
  letI : DiscreteTopology
      (localAbsoluteAbelianProfinite K ⧸ N.toSubgroup) :=
    QuotientGroup.discreteTopology N.isOpen'
  exact
    { absoluteFiniteQuotientMulEquiv K N with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

/-- On representatives, the finite quotient identification is literal
restriction to the corresponding fixed field. -/
@[simp]
theorem absoluteFiniteQuotientEquiv_mk_mk
    (N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K))
    (σ : intrinsicAbsoluteGalois K) :
    absoluteFiniteQuotientEquiv K N
        (QuotientGroup.mk
          (QuotientGroup.mk σ : localAbsoluteAbelianProfinite K)) =
      AlgEquiv.restrictNormalHom (absoluteFiniteQuotientField K N) σ := by
  let q := QuotientGroup.quotientQuotientEquivQuotient
    (commutator (intrinsicAbsoluteGalois K)).topologicalClosure
    (absoluteFiniteQuotientPreimage K N).toSubgroup
    (localAbsoluteCommutatorClosure_le_finiteQuotientPreimage K N)
  let e := InfiniteGalois.normalAutEquivQuotient
    (absoluteFiniteQuotientClosedPreimage K N)
  have hcast := QuotientGroup.quotientMulEquivOfEq_mk
    (finiteQuotientPreimage_map_eq K N).symm
    (QuotientGroup.mk σ : localAbsoluteAbelianProfinite K)
  have hquot := QuotientGroup.quotientQuotientEquivQuotientAux_mk_mk
    (commutator (intrinsicAbsoluteGalois K)).topologicalClosure
    (absoluteFiniteQuotientPreimage K N).toSubgroup
    (localAbsoluteCommutatorClosure_le_finiteQuotientPreimage K N) σ
  have hrestrict := InfiniteGalois.normalAutEquivQuotient_apply
    (absoluteFiniteQuotientClosedPreimage K N) σ
  exact (congrArg (fun z => e (q z)) hcast).trans
    ((congrArg e hquot).trans hrestrict)

/-- The fixed field attached to a finite quotient of the abelianization is abelian Galois. -/
instance absoluteFiniteQuotientField_isAbelianGalois
    (N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K)) :
    IsAbelianGalois K (absoluteFiniteQuotientField K N) := by
  let : N.toSubgroup.Normal := N.isNormal'
  have hquotient_comm
      (x y : localAbsoluteAbelianProfinite K ⧸ N.toSubgroup) :
      x * y = y * x := by
    refine QuotientGroup.induction_on x ?_
    intro a
    refine QuotientGroup.induction_on y ?_
    intro b
    change QuotientGroup.mk (a * b) = QuotientGroup.mk (b * a)
    have hab : a * b = b * a := mul_comm _ _
    exact congrArg QuotientGroup.mk hab
  refine { is_comm.comm := fun σ τ => ?_ }
  · exact (absoluteFiniteQuotientEquiv K N).symm.injective (by
      simp only [map_mul]
      exact hquotient_comm
        ((absoluteFiniteQuotientEquiv K N).symm σ)
        ((absoluteFiniteQuotientEquiv K N).symm τ))

end LocalClassFieldTheory
