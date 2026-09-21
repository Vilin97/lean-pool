/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Infinite.AbsoluteFiniteQuotientTransitions
/-!
# The absolute local Artin map from compatible finite quotients

Finite local reciprocity supplies a surjective Artin map at every open
finite quotient of the absolute topological abelianization.  This module
assembles those maps into the absolute Artin map and records its finite-stage
compatibility.
-/

noncomputable section

open CategoryTheory

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The finite Artin coordinate at an open normal subgroup of the absolute
topological abelianization. -/
noncomputable def absoluteFiniteArtinMap
    (N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K)) :
    Kˣ →ₜ* (localAbsoluteAbelianProfinite K ⧸ N.toSubgroup) :=
  (ContinuousMonoidHom.toContinuousMonoidHom
      (absoluteFiniteQuotientEquiv K N).symm).comp
    (abelianLocalArtinMap K (absoluteFiniteQuotientField K N))

/-- Every finite coordinate of the absolute Artin map is onto. -/
theorem absoluteFiniteArtinMap_surjective
    (N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K)) :
    Function.Surjective (absoluteFiniteArtinMap K N) :=
  (absoluteFiniteQuotientEquiv K N).symm.surjective.comp
    (abelianLocalArtinMap_surjective K
      (absoluteFiniteQuotientField K N))

/-- The kernel of a finite absolute Artin coordinate is the ordinary norm
subgroup of its corresponding finite abelian fixed field. -/
theorem absoluteFiniteArtinMap_ker
    (N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K)) :
    (absoluteFiniteArtinMap K N).toMonoidHom.ker =
      localNormSubgroup K (absoluteFiniteQuotientField K N) := by
  rw [← abelianLocalArtinMap_ker K (absoluteFiniteQuotientField K N)]
  ext a
  simp only [MonoidHom.mem_ker, absoluteFiniteArtinMap]
  constructor
  · intro ha
    apply (absoluteFiniteQuotientEquiv K N).symm.injective
    simpa using ha
  · intro ha
    simpa using congrArg (absoluteFiniteQuotientEquiv K N).symm ha

/-- Finite absolute Artin coordinates commute with quotient transition. -/
theorem absoluteFiniteArtinMap_transition
    {N M : OpenNormalSubgroup (localAbsoluteAbelianProfinite K)}
    (hNM : N ≤ M) :
    (absoluteFiniteQuotientTransition hNM).comp
        (absoluteFiniteArtinMap K N) =
      absoluteFiniteArtinMap K M := by
  apply ContinuousMonoidHom.ext
  intro a
  apply (absoluteFiniteQuotientEquiv K M).injective
  change
    absoluteFiniteQuotientEquiv K M
        (absoluteFiniteQuotientTransition hNM
          ((absoluteFiniteQuotientEquiv K N).symm
            (abelianLocalArtinMap K
              (absoluteFiniteQuotientField K N) a))) =
      absoluteFiniteQuotientEquiv K M
        ((absoluteFiniteQuotientEquiv K M).symm
          (abelianLocalArtinMap K
            (absoluteFiniteQuotientField K M) a))
  calc
    _ = intermediateFieldRestrictContinuous K
          (absoluteFiniteQuotientField K M)
          (absoluteFiniteQuotientField K N)
          (absoluteFiniteQuotientField_antitone hNM)
          (absoluteFiniteQuotientEquiv K N
            ((absoluteFiniteQuotientEquiv K N).symm
              (abelianLocalArtinMap K
                (absoluteFiniteQuotientField K N) a))) := by
        exact (DFunLike.congr_fun
          (absoluteFiniteQuotientEquiv_transition (K := K) hNM)
          ((absoluteFiniteQuotientEquiv K N).symm
            (abelianLocalArtinMap K
              (absoluteFiniteQuotientField K N) a))).symm
    _ = intermediateFieldRestrictContinuous K
          (absoluteFiniteQuotientField K M)
          (absoluteFiniteQuotientField K N)
          (absoluteFiniteQuotientField_antitone hNM)
          (abelianLocalArtinMap K
            (absoluteFiniteQuotientField K N) a) := by
        rw [(absoluteFiniteQuotientEquiv K N).apply_symm_apply]
    _ = abelianLocalArtinMap K
          (absoluteFiniteQuotientField K M) a :=
        DFunLike.congr_fun
          (abelianLocalArtinMap_restrict K
            (absoluteFiniteQuotientField K M)
            (absoluteFiniteQuotientField K N)
            (absoluteFiniteQuotientField_antitone hNM)) a
    _ = _ := by
        rw [(absoluteFiniteQuotientEquiv K M).apply_symm_apply]

/-- The compatible cone of finite Artin coordinates, valued in the inverse
limit of all open finite quotients of the absolute abelianized Galois group. -/
noncomputable def absoluteFiniteArtinLimit : ProfiniteGrp :=
  ProfiniteGrp.limit
    ((localAbsoluteAbelianProfinite K).toFiniteQuotientFunctor ⋙
      forget₂ FiniteGrp ProfiniteGrp)

/-- The topological abelianization of the absolute Galois group is
canonically the inverse limit of all of its finite quotients. -/
noncomputable def absoluteGaloisAbelianizationLimitEquiv :
    localAbsoluteAbelianProfinite K ≃ₜ*
      absoluteFiniteArtinLimit K :=
  ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor
    (localAbsoluteAbelianProfinite K)

/-- Defines `absoluteFiniteArtinLimitMap`. -/
noncomputable def absoluteFiniteArtinLimitMap :
    Kˣ →ₜ* (absoluteFiniteArtinLimit K : Type) where
  toFun a :=
    ⟨fun N => absoluteFiniteArtinMap K N a, by
      intro N M i
      change
        absoluteFiniteQuotientTransition (K := K)
            (CategoryTheory.leOfHom i)
            (absoluteFiniteArtinMap K N a) =
          absoluteFiniteArtinMap K M a
      exact DFunLike.congr_fun
        (absoluteFiniteArtinMap_transition K
          (CategoryTheory.leOfHom i)) a⟩
  map_one' := by
    apply Subtype.ext
    funext N
    exact (absoluteFiniteArtinMap K N).map_one
  map_mul' x y := by
    apply Subtype.ext
    funext N
    exact (absoluteFiniteArtinMap K N).map_mul x y
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro N
    let : DiscreteTopology
        (localAbsoluteAbelianProfinite K ⧸ N.toSubgroup) :=
      QuotientGroup.discreteTopology N.isOpen'
    let q :
        (localAbsoluteAbelianProfinite K ⧸ N.toSubgroup) →ₜ*
          (((localAbsoluteAbelianProfinite K).toFiniteQuotientFunctor ⋙
            forget₂ FiniteGrp ProfiniteGrp).obj N : Type) :=
      { toFun := id
        map_one' := rfl
        map_mul' := by intro x y; rfl
        continuous_toFun := continuous_of_discreteTopology }
    exact q.continuous_toFun.comp
      (absoluteFiniteArtinMap K N).continuous_toFun

/-- States the theorem `absoluteFiniteArtinLimitMap_apply`. -/
@[simp]
theorem absoluteFiniteArtinLimitMap_apply
    (N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K)) (a : Kˣ) :
    (absoluteFiniteArtinLimitMap K a).1 N =
      absoluteFiniteArtinMap K N a :=
  rfl

/-- Surjectivity at every finite Artin coordinate makes the assembled cone
dense in the inverse limit. -/
theorem absoluteFiniteArtinLimitMap_denseRange :
    DenseRange (absoluteFiniteArtinLimitMap K) := by
  apply dense_iff_inter_open.mpr
  rintro U ⟨s, hsO, hsv⟩ ⟨⟨spc, hspc⟩, uDefaultSpec⟩
  rw [← hsv] at uDefaultSpec
  rcases (isOpen_pi_iff.mp hsO) _ uDefaultSpec with ⟨J, fJ, hJ1, hJ2⟩
  let M := iInf (fun (j : J) => j.1.1.1)
  have hM : M.Normal :=
    Subgroup.normal_iInf_normal fun j => j.1.isNormal'
  have hMOpen :
      IsOpen (M : Set (localAbsoluteAbelianProfinite K)) := by
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun i => i.1.1.isOpen'
  let m : OpenNormalSubgroup (localAbsoluteAbelianProfinite K) :=
    { M with isOpen' := hMOpen }
  rcases absoluteFiniteArtinMap_surjective K m (spc m) with
    ⟨origin, horigin⟩
  use absoluteFiniteArtinLimitMap K origin
  refine ⟨?_, origin, rfl⟩
  rw [← hsv]
  apply hJ2
  intro a a_in_J
  let M_to_Na : m ⟶ a :=
    (iInf_le (fun (j : J) => j.1.1.1) ⟨a, a_in_J⟩).hom
  rw [← (absoluteFiniteArtinLimitMap K origin).property M_to_Na]
  change
    ((localAbsoluteAbelianProfinite K).toFiniteQuotientFunctor ⋙
      forget₂ FiniteGrp ProfiniteGrp).map M_to_Na
        (absoluteFiniteArtinMap K m origin) ∈ _
  rw [horigin]
  exact Set.mem_of_eq_of_mem (hspc M_to_Na) (hJ1 a a_in_J).2

/-- The absolute local Artin map into the topological abelianization of the
absolute Galois group of the fixed separable closure. -/
noncomputable def separableAbsoluteLocalArtinMap :
    Kˣ →ₜ* localAbsoluteAbelianProfinite K :=
  ((absoluteGaloisAbelianizationLimitEquiv K).symm :
      _ →ₜ* localAbsoluteAbelianProfinite K).comp
    (absoluteFiniteArtinLimitMap K)

/-- Projection of the absolute local Artin map to an open finite quotient is
the corresponding finite local Artin coordinate. -/
@[simp]
theorem separableAbsoluteLocalArtinMap_finiteProjection
    (N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K)) (a : Kˣ) :
    QuotientGroup.mk' N.toSubgroup
        (separableAbsoluteLocalArtinMap K a) =
      absoluteFiniteArtinMap K N a := by
  let e := absoluteGaloisAbelianizationLimitEquiv K
  let y := absoluteFiniteArtinLimitMap K a
  have h := congrArg (fun z => z.1 N) (e.apply_symm_apply y)
  change
    QuotientGroup.mk' N.toSubgroup (e.symm y) =
      absoluteFiniteArtinMap K N a at h
  simpa [separableAbsoluteLocalArtinMap, e, y] using h

/-- The absolute local Artin map has dense image. -/
theorem separableAbsoluteLocalArtinMap_denseRange :
    DenseRange (separableAbsoluteLocalArtinMap K) := by
  let e := absoluteGaloisAbelianizationLimitEquiv K
  change DenseRange
    (fun a => e.symm (absoluteFiniteArtinLimitMap K a))
  exact e.symm.surjective.denseRange.comp
    (absoluteFiniteArtinLimitMap_denseRange K) e.symm.continuous

end LocalClassFieldTheory
