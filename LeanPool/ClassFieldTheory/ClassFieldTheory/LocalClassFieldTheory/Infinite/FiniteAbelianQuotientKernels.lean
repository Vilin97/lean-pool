/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Infinite.AbsoluteArtin
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Infinite.ProfiniteCompletionCriteria
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.Classification
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData
/-!
# Kernels attached to finite abelian subextensions

Every finite abelian subextension of the fixed separable closure determines
an open normal subgroup of the absolute topological abelianization.  This
module identifies its pullback along the absolute Artin map with the ordinary
norm subgroup.  The finite local existence theorem then shows that these
pullbacks are cofinal among the open finite-index subgroups of the local
multiplicative group.
-/

@[expose] public section

noncomputable section

namespace LocalClassFieldTheory

open scoped IsMulCommutative

open LocalFieldTheory RamificationTheory
open ClassFormation CyclicCohomology

variable (K : Type) [Field K]

/-- Restriction from the absolute topological abelianization to the Galois
group of a finite abelian subextension. -/
noncomputable def absoluteAbelianRestriction
    (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [IsAbelianGalois K E] :
    localAbsoluteAbelianProfinite K →ₜ* Gal(E/K) := by
  let r : intrinsicAbsoluteGalois K →* Gal(E/K) :=
    AlgEquiv.restrictNormalHom E
  have hcomm : commutator (intrinsicAbsoluteGalois K) ≤ r.ker :=
    Abelianization.commutator_subset_ker r
  have hkerClosed : IsClosed (r.ker : Set (intrinsicAbsoluteGalois K)) := by
    rw [IntermediateField.restrictNormalHom_ker]
    exact IntermediateField.fixingSubgroup_isClosed E
  have hclosure :
      (commutator (intrinsicAbsoluteGalois K)).topologicalClosure ≤ r.ker :=
    (commutator (intrinsicAbsoluteGalois K)).topologicalClosure_minimal
      hcomm hkerClosed
  let q : localAbsoluteAbelianProfinite K →* Gal(E/K) :=
    QuotientGroup.lift
      (commutator (intrinsicAbsoluteGalois K)).topologicalClosure r
      (fun σ hσ ↦ MonoidHom.mem_ker.mp (hclosure hσ))
  exact
    { q with
      continuous_toFun := by
        apply (QuotientGroup.isQuotientMap_mk
          (commutator (intrinsicAbsoluteGalois K)).topologicalClosure).continuous_iff.2
        refine (InfiniteGalois.restrictNormalHom_continuous E).congr ?_
        intro σ
        rfl }

/-- States the theorem `absoluteAbelianRestriction_mk`. -/
@[simp]
theorem absoluteAbelianRestriction_mk
    (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [IsAbelianGalois K E]
    (σ : intrinsicAbsoluteGalois K) :
    absoluteAbelianRestriction K E
        (QuotientGroup.mk σ : localAbsoluteAbelianProfinite K) =
      AlgEquiv.restrictNormalHom E σ :=
  rfl

/-- Restriction to a finite Galois subextension is onto after passing to the
absolute topological abelianization. -/
theorem absoluteAbelianRestriction_surjective
    (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [IsAbelianGalois K E] :
    Function.Surjective (absoluteAbelianRestriction K E) := by
  intro τ
  rcases AlgEquiv.restrictNormalHom_surjective
      (F := K) (K₁ := E) (E := SeparableClosure K) τ with ⟨σ, rfl⟩
  exact ⟨QuotientGroup.mk σ, absoluteAbelianRestriction_mk K E σ⟩

/-- The open normal kernel attached to a finite abelian subextension. -/
noncomputable def absoluteAbelianRestrictionKernel
    (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [IsAbelianGalois K E] :
    OpenNormalSubgroup (localAbsoluteAbelianProfinite K) where
  toOpenSubgroup :=
    { toSubgroup := (absoluteAbelianRestriction K E).toMonoidHom.ker
      isOpen' := by
        change IsOpen ((absoluteAbelianRestriction K E) ⁻¹' {1})
        exact (isOpen_discrete {1}).preimage
          (absoluteAbelianRestriction K E).continuous_toFun }
  isNormal' := by infer_instance

/-- States the theorem `mem_absoluteAbelianRestrictionKernel_iff`. -/
@[simp]
theorem mem_absoluteAbelianRestrictionKernel_iff
    (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [IsAbelianGalois K E]
    (x : localAbsoluteAbelianProfinite K) :
    x ∈ absoluteAbelianRestrictionKernel K E ↔
      absoluteAbelianRestriction K E x = 1 :=
  Iff.rfl

/-- Pulling the restriction kernel back to the absolute Galois group gives
the fixing subgroup of the original finite subextension. -/
theorem absoluteFiniteQuotientPreimage_restrictionKernel
    (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [IsAbelianGalois K E] :
    (absoluteFiniteQuotientPreimage K
      (absoluteAbelianRestrictionKernel K E)).toSubgroup =
        E.fixingSubgroup := by
  ext σ
  change absoluteAbelianRestriction K E
      (QuotientGroup.mk σ : localAbsoluteAbelianProfinite K) = 1 ↔
    σ ∈ E.fixingSubgroup
  rw [absoluteAbelianRestriction_mk,
    ← IntermediateField.restrictNormalHom_ker E]
  rfl

/-- The finite field cut out by the restriction kernel is the original
finite abelian subextension. -/
theorem absoluteFiniteQuotientField_restrictionKernel
    (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [IsAbelianGalois K E] :
    absoluteFiniteQuotientField K (absoluteAbelianRestrictionKernel K E) = E := by
  change IntermediateField.fixedField
      (absoluteFiniteQuotientPreimage K
        (absoluteAbelianRestrictionKernel K E)).toSubgroup = E
  rw [absoluteFiniteQuotientPreimage_restrictionKernel,
    InfiniteGalois.fixedField_fixingSubgroup]

section LocalField

variable [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Pulling a finite restriction kernel back along the absolute local Artin
map gives exactly the norm subgroup of that finite abelian extension. -/
theorem separableAbsoluteLocalArtinMap_preimage_restrictionKernel
    (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [IsAbelianGalois K E] :
    (topologicalProfiniteCompletionPreimageIndex
      (localAbsoluteAbelianProfinite K)
      (separableAbsoluteLocalArtinMap K)
      (absoluteAbelianRestrictionKernel K E)).toOpenNormalSubgroup.toSubgroup =
        localNormSubgroup K E := by
  let N := absoluteAbelianRestrictionKernel K E
  ext a
  change separableAbsoluteLocalArtinMap K a ∈ N ↔
    a ∈ localNormSubgroup K E
  have hfield : absoluteFiniteQuotientField K N = E := by
    dsimp only [N]
    exact absoluteFiniteQuotientField_restrictionKernel K E
  constructor
  · intro ha
    have hfinite : absoluteFiniteArtinMap K N a = 1 := by
      rw [← separableAbsoluteLocalArtinMap_finiteProjection K N a]
      exact (QuotientGroup.eq_one_iff
        (separableAbsoluteLocalArtinMap K a)).2 ha
    have hker : a ∈ (absoluteFiniteArtinMap K N).toMonoidHom.ker :=
      MonoidHom.mem_ker.mpr hfinite
    rw [absoluteFiniteArtinMap_ker, hfield] at hker
    exact hker
  · intro ha
    have hker : a ∈ (absoluteFiniteArtinMap K N).toMonoidHom.ker := by
      rw [absoluteFiniteArtinMap_ker, hfield]
      exact ha
    apply (QuotientGroup.eq_one_iff
      (separableAbsoluteLocalArtinMap K a)).mp
    calc
      (QuotientGroup.mk (separableAbsoluteLocalArtinMap K a) :
          localAbsoluteAbelianProfinite K ⧸ N.toSubgroup) =
        absoluteFiniteArtinMap K N a :=
          separableAbsoluteLocalArtinMap_finiteProjection K N a
      _ = 1 := MonoidHom.mem_ker.mp hker

/-- The pullbacks of finite abelian restriction kernels are cofinal among
the open finite-index normal subgroups of `Kˣ`.  This is the arithmetic
input for injectivity of the canonical map from the topological profinite
completion. -/
theorem separableAbsoluteLocalArtinMap_preimage_cofinal
    (H : OpenFiniteIndexNormalSubgroup Kˣ) :
    ∃ N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K),
      topologicalProfiniteCompletionPreimageIndex
        (localAbsoluteAbelianProfinite K)
        (separableAbsoluteLocalArtinMap K) N ≤ H := by
  let Hnative : OpenFiniteIndexSubgroup K :=
    ⟨H.toOpenNormalSubgroup.toSubgroup,
      H.toOpenNormalSubgroup.isOpen', H.finiteIndex'⟩
  rcases finiteAbelianNormSubgroupMap_surjective K Hnative with ⟨L, hL⟩
  let E : IntermediateField K (SeparableClosure K) :=
    abstractFixedField K (SeparableClosure K) L.field
  let : Finite ((baseField (intrinsicAbsoluteGalois K)).toSubgroup ⧸
      extensionSubgroup (baseField (intrinsicAbsoluteGalois K)) L.field
        (le_baseField L.field)) :=
    finiteAbelianSubextension_finite_over_absoluteBase K L
  let : FiniteDimensional K E :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) L.field inferInstance
  let : IsAbelianGalois K E :=
    finiteAbelianSubextension_fixedField_isAbelianGalois K L
  refine ⟨absoluteAbelianRestrictionKernel K E, ?_⟩
  change
    (topologicalProfiniteCompletionPreimageIndex
      (localAbsoluteAbelianProfinite K)
      (separableAbsoluteLocalArtinMap K)
      (absoluteAbelianRestrictionKernel K E)).toOpenNormalSubgroup.toSubgroup ≤
        H.toOpenNormalSubgroup.toSubgroup
  rw [separableAbsoluteLocalArtinMap_preimage_restrictionKernel]
  have hsubgroup :
      localNormSubgroup K E = H.toOpenNormalSubgroup.toSubgroup := by
    simpa only [finiteAbelianNormSubgroupMap, finiteAbelianNormSubgroup,
      Hnative, E] using
        congrArg OpenFiniteIndexSubgroup.subgroup hL
  rw [hsubgroup]

end LocalField

end LocalClassFieldTheory
