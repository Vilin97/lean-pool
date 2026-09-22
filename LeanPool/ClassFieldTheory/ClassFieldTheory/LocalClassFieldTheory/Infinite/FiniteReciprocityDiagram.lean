/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Infinite.AbsoluteArtin
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormSubgroupFunctoriality
/-!
# Finite reciprocity as an isomorphism of diagrams

The open normal subgroups of the absolute abelianized Galois group index
three covariant finite diagrams: its finite quotients, the corresponding
finite abelian Galois groups, and the corresponding norm quotients.  This
file packages the canonical finite-stage identifications as natural
isomorphisms.
-/

noncomputable section

open CategoryTheory

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
private abbrev AbsoluteFiniteIndex :=
  OpenNormalSubgroup (localAbsoluteAbelianProfinite K)

/-- Norm quotients in the finite reciprocity diagram carry their quotient topologies from
base-field units. -/
noncomputable local instance finiteDiagramNormQuotientTopologicalSpace
    (E L : Type) [Field E] [Field L] [Algebra E L]
    [TopologicalSpace E] :
    TopologicalSpace (NormQuotient E L) := by
  change TopologicalSpace (Eˣ ⧸ localNormSubgroup E L)
  infer_instance

local instance finiteDiagramNormQuotientIsTopologicalGroup
    (L : Type) [Field L] [Algebra K L] :
    IsTopologicalGroup (NormQuotient K L) := by
  change IsTopologicalGroup (Kˣ ⧸ localNormSubgroup K L)
  infer_instance

/-- The finite quotients of the absolute abelianized Galois group, carrying
their quotient topologies and the canonical quotient transition maps. -/
noncomputable def absoluteFiniteQuotientDiagram :
    AbsoluteFiniteIndex K ⥤ ProfiniteGrp where
  obj N := ProfiniteGrp.of
    (localAbsoluteAbelianProfinite K ⧸ N.toSubgroup)
  map f := ProfiniteGrp.ofHom <|
    absoluteFiniteQuotientTransition (leOfHom f)
  map_id N := by
    apply ProfiniteGrp.hom_ext
    apply ContinuousMonoidHom.ext
    intro x
    refine QuotientGroup.induction_on x ?_
    intro x
    rfl
  map_comp {X Y Z} f g := by
    apply ProfiniteGrp.hom_ext
    apply ContinuousMonoidHom.ext
    intro x
    refine QuotientGroup.induction_on x ?_
    intro x
    rfl
/-- The finite abelian Galois groups cut out by open normal subgroups of the
absolute abelianized Galois group, with restriction as transition map. -/
noncomputable def finiteAbelianGaloisDiagram :
    AbsoluteFiniteIndex K ⥤ ProfiniteGrp where
  obj N := ProfiniteGrp.of
    (Gal(absoluteFiniteQuotientField K N/K))
  map {N M} f := ProfiniteGrp.ofHom <|
    intermediateFieldRestrictContinuous K
      (absoluteFiniteQuotientField K M)
      (absoluteFiniteQuotientField K N)
      (absoluteFiniteQuotientField_antitone (leOfHom f))
  map_id N := by
    apply ProfiniteGrp.hom_ext
    apply ContinuousMonoidHom.ext
    intro sigma
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    exact intermediateFieldRestrictNormalHom_apply_val
      (absoluteFiniteQuotientField K N)
      (absoluteFiniteQuotientField K N) le_rfl sigma x
  map_comp {N M L} f g := by
    apply ProfiniteGrp.hom_ext
    apply ContinuousMonoidHom.ext
    intro sigma
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    change
      (absoluteFiniteQuotientField K L).val
        (intermediateFieldRestrictNormalHom
          (absoluteFiniteQuotientField K L)
          (absoluteFiniteQuotientField K N) _ sigma x) =
      (absoluteFiniteQuotientField K L).val
        (intermediateFieldRestrictNormalHom
          (absoluteFiniteQuotientField K L)
          (absoluteFiniteQuotientField K M) _
          (intermediateFieldRestrictNormalHom
            (absoluteFiniteQuotientField K M)
            (absoluteFiniteQuotientField K N) _ sigma) x)
    rw [intermediateFieldRestrictNormalHom_apply_val]
    rw [intermediateFieldRestrictNormalHom_apply_val]
    rw [intermediateFieldRestrictNormalHom_apply_val]
    apply congrArg (fun y : absoluteFiniteQuotientField K N =>
      (absoluteFiniteQuotientField K N).val (sigma y))
    apply Subtype.ext
    rfl

/-- At every finite stage, the quotient of the absolute abelianized Galois
group is canonically the Galois group of its fixed field; these
identifications commute with all transition maps. -/
noncomputable def absoluteFiniteQuotientNaturalIso :
    absoluteFiniteQuotientDiagram K ≅ finiteAbelianGaloisDiagram K :=
  NatIso.ofComponents
    (fun N => ProfiniteGrp.ContinuousMulEquiv.toProfiniteGrpIso
      (absoluteFiniteQuotientEquiv K N))
    (fun {N M} f => by
      apply ProfiniteGrp.hom_ext
      apply ContinuousMonoidHom.ext
      intro x
      exact DFunLike.congr_fun
        (absoluteFiniteQuotientEquiv_transition
          (K := K) (leOfHom f)).symm x)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- Inclusion of open normal subgroups gives the corresponding inclusion of
finite norm subgroups. -/
theorem absoluteFiniteNormSubgroup_mono
    {N M : AbsoluteFiniteIndex K} (hNM : N ≤ M) :
    localNormSubgroup K (absoluteFiniteQuotientField K N) ≤
      localNormSubgroup K (absoluteFiniteQuotientField K M) := by
  let E := absoluteFiniteQuotientField K M
  let F := absoluteFiniteQuotientField K N
  let hEF : E ≤ F :=
    absoluteFiniteQuotientField_antitone (K := K) hNM
  let EAlgebra : Algebra E F :=
    RingHom.toAlgebra (IntermediateField.inclusion hEF).toRingHom
  let : SMul E F :=
    @Algebra.toSMul _ _ _ _ EAlgebra
  let : Module E F :=
    @Algebra.toModule _ _ _ _ EAlgebra
  let : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional E F := FiniteDimensional.right K E F
  change localNormSubgroup K F ≤ localNormSubgroup K E
  exact LocalFieldTheory.normSubgroup_le_of_tower K E F

/-- The first isomorphism theorem for a finite coordinate of the absolute
Artin map, with its kernel identified with the corresponding norm subgroup. -/
noncomputable def absoluteFiniteArtinQuotientEquiv
    (N : AbsoluteFiniteIndex K) :
    NormQuotient K (absoluteFiniteQuotientField K N) ≃ₜ*
      (localAbsoluteAbelianProfinite K ⧸ N.toSubgroup) := by
  letI : DiscreteTopology
      (NormQuotient K (absoluteFiniteQuotientField K N)) :=
    normQuotient_discrete K (absoluteFiniteQuotientField K N)
  letI : DiscreteTopology
      (localAbsoluteAbelianProfinite K ⧸ N.toSubgroup) :=
    QuotientGroup.discreteTopology N.isOpen'
  let e : NormQuotient K (absoluteFiniteQuotientField K N) ≃*
      (localAbsoluteAbelianProfinite K ⧸ N.toSubgroup) :=
    normQuotientEquivOfSurjective
      (absoluteFiniteArtinMap K N).toMonoidHom
      (absoluteFiniteArtinMap_surjective K N)
      (absoluteFiniteArtinMap_ker K N)
  exact
    { e with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

/-- States the theorem `absoluteFiniteArtinQuotientEquiv_mk`. -/
@[simp]
theorem absoluteFiniteArtinQuotientEquiv_mk
    (N : AbsoluteFiniteIndex K) (a : Kˣ) :
    absoluteFiniteArtinQuotientEquiv K N
        (normClass K
          (absoluteFiniteQuotientField K N) a) =
      absoluteFiniteArtinMap K N a := by
  exact normQuotientEquivOfSurjective_normClass
    (absoluteFiniteArtinMap K N).toMonoidHom
    (absoluteFiniteArtinMap_surjective K N)
    (absoluteFiniteArtinMap_ker K N) a

/-- The transition map on norm quotients induced by a tower of fixed fields. -/
noncomputable def normQuotientTransition
    {N M : AbsoluteFiniteIndex K} (hNM : N ≤ M) :
    NormQuotient K (absoluteFiniteQuotientField K N) →ₜ*
      NormQuotient K (absoluteFiniteQuotientField K M) := by
  letI : DiscreteTopology
      (NormQuotient K (absoluteFiniteQuotientField K N)) :=
    normQuotient_discrete K (absoluteFiniteQuotientField K N)
  let f : NormQuotient K (absoluteFiniteQuotientField K N) →*
      NormQuotient K (absoluteFiniteQuotientField K M) :=
    normQuotientMapOfLE K
      (absoluteFiniteQuotientField K N)
      (absoluteFiniteQuotientField K M)
      (absoluteFiniteNormSubgroup_mono K hNM)
  exact
    { f with
      continuous_toFun := continuous_of_discreteTopology }

/-- States the theorem `normQuotientTransition_mk`. -/
@[simp]
theorem normQuotientTransition_mk
    {N M : AbsoluteFiniteIndex K} (hNM : N ≤ M) (a : Kˣ) :
    normQuotientTransition K hNM
        (normClass K
          (absoluteFiniteQuotientField K N) a) =
      normClass K
        (absoluteFiniteQuotientField K M) a := by
  exact normQuotientMapOfLE_normClass K
    (absoluteFiniteQuotientField K N)
    (absoluteFiniteQuotientField K M)
    (absoluteFiniteNormSubgroup_mono K hNM) a

/-- The finite norm quotients indexed by open normal subgroups, with the
canonical quotient maps induced by inclusions of norm subgroups. -/
noncomputable def normQuotientDiagram :
    AbsoluteFiniteIndex K ⥤ ProfiniteGrp where
  obj N := ProfiniteGrp.ofContinuousMulEquiv
    (G := (absoluteFiniteQuotientDiagram K).obj N)
    (absoluteFiniteArtinQuotientEquiv K N).symm
  map f := ConcreteCategory.ofHom (C := ProfiniteGrp)
    (normQuotientTransition K (leOfHom f))
  map_id N := by
    apply ProfiniteGrp.hom_ext
    apply ContinuousMonoidHom.ext
    intro x
    change normQuotientTransition K (leOfHom (𝟙 N)) x = x
    refine NormQuotient.inductionOn
      (K := K) (L := absoluteFiniteQuotientField K N)
      (motive := fun q =>
        normQuotientTransition K (leOfHom (𝟙 N)) q = q) x ?_
    intro a
    exact normQuotientTransition_mk K (leOfHom (𝟙 N)) a
  map_comp f g := by
    apply ProfiniteGrp.hom_ext
    apply ContinuousMonoidHom.ext
    intro x
    refine NormQuotient.inductionOn
      (K := K)
      (motive := fun q =>
        normQuotientTransition K (leOfHom (f ≫ g)) q =
          normQuotientTransition K (leOfHom g)
            (normQuotientTransition K (leOfHom f) q)) x ?_
    intro a
    rw [normQuotientTransition_mk, normQuotientTransition_mk,
      normQuotientTransition_mk]

/-- The finite Artin first-isomorphism identifications form a natural
isomorphism from norm quotients to finite absolute Galois quotients. -/
noncomputable def finiteArtinQuotientNaturalIso :
    normQuotientDiagram K ≅ absoluteFiniteQuotientDiagram K :=
  NatIso.ofComponents
    (fun N => by
      let e :
          ((normQuotientDiagram K).obj N : Type) ≃ₜ*
            ((absoluteFiniteQuotientDiagram K).obj N : Type) :=
        { (absoluteFiniteArtinQuotientEquiv K N) with
          continuous_toFun := by
            change Continuous (absoluteFiniteArtinQuotientEquiv K N)
            exact (absoluteFiniteArtinQuotientEquiv K N).continuous
          continuous_invFun := by
            change Continuous (absoluteFiniteArtinQuotientEquiv K N).symm
            exact (absoluteFiniteArtinQuotientEquiv K N).symm.continuous }
      exact ProfiniteGrp.ContinuousMulEquiv.toProfiniteGrpIso e)
    (fun {N M} f => by
      apply ProfiniteGrp.hom_ext
      apply ContinuousMonoidHom.ext
      intro x
      refine QuotientGroup.induction_on x ?_
      intro a
      simp only
      change absoluteFiniteArtinQuotientEquiv K M
          (normQuotientTransition K (leOfHom f)
            (normClass K
              (absoluteFiniteQuotientField K N) a)) =
        absoluteFiniteQuotientTransition (leOfHom f)
          (absoluteFiniteArtinQuotientEquiv K N
            (normClass K
              (absoluteFiniteQuotientField K N) a))
      rw [normQuotientTransition_mk]
      rw [absoluteFiniteArtinQuotientEquiv_mk]
      rw [absoluteFiniteArtinQuotientEquiv_mk]
      exact DFunLike.congr_fun
        (absoluteFiniteArtinMap_transition
          (K := K) (leOfHom f)).symm a)

/-- Finite local reciprocity, simultaneously at every open finite quotient:
norm quotients are naturally isomorphic to the corresponding finite abelian
Galois groups. -/
noncomputable def finiteReciprocityNaturalIso :
    normQuotientDiagram K ≅ finiteAbelianGaloisDiagram K :=
  (finiteArtinQuotientNaturalIso K).trans
    (absoluteFiniteQuotientNaturalIso K)


end LocalClassFieldTheory

end
