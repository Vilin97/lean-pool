/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Infinite.FiniteAbelianQuotientKernels
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Infinite.LocalMultiplicativeCompletion
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Infinite.AbsoluteArtin
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Infinite.AbsoluteGaloisAbelianization
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Infinite.TopologicalAbelianizationCongr
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.FiniteExtensionCorrespondence
/-!
# Profinite local reciprocity

The absolute Artin map constructed from the compatible finite reciprocity
maps is transported from the fixed separable closure to Mathlib's usual
algebraic-closure absolute Galois group.  Its canonical extension to the
topological profinite completion is then automatically onto.  Injectivity
is supplied by the arithmetic cofinality consequence of the finite local
existence theorem.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Restriction to the separable closure gives the canonical topological
identification between the usual and separable absolute Galois groups. -/
noncomputable def standardToSeparableAbsoluteGaloisEquiv :
    _root_.Field.absoluteGaloisGroup K ≃ₜ* intrinsicAbsoluteGalois K :=
  RamificationTheory.Field.absoluteGaloisGroup.separableClosureContinuousMulEquiv K

/-- The induced canonical identification from the separable absolute
topological abelianization to Mathlib's usual one. -/
noncomputable def separableToStandardAbsoluteAbelianizationEquiv :
    TopologicalAbelianization (intrinsicAbsoluteGalois K) ≃ₜ*
      _root_.Field.absoluteGaloisGroupAbelianization K :=
  (topologicalAbelianizationCongr
    (standardToSeparableAbsoluteGaloisEquiv K)).symm

/-- The separable model makes the standard absolute abelianization totally disconnected. -/
noncomputable instance standardLocalAbsoluteAbelianization_totallyDisconnectedSpace :
    TotallyDisconnectedSpace
      (_root_.Field.absoluteGaloisGroupAbelianization K) :=
  Homeomorph.totallyDisconnectedSpace
    (separableToStandardAbsoluteAbelianizationEquiv K).toHomeomorph

/-- The standard absolute abelianization is compact via the separable-model equivalence. -/
noncomputable instance standardLocalAbsoluteAbelianization_compactSpace :
    CompactSpace (_root_.Field.absoluteGaloisGroupAbelianization K) :=
  Homeomorph.compactSpace
    (separableToStandardAbsoluteAbelianizationEquiv K).toHomeomorph

/-- The standard absolute abelianization is Hausdorff via the separable-model equivalence. -/
noncomputable instance standardLocalAbsoluteAbelianization_t2Space :
    T2Space (_root_.Field.absoluteGaloisGroupAbelianization K) :=
  by
    have htarget : T2Space Gal(localMaximalAbelianExtension K/K) :=
      krullTopology_t2
    have hsource : T2Space
        (TopologicalAbelianization (intrinsicAbsoluteGalois K)) :=
      @Homeomorph.t2Space _ _ _ _ htarget
        (localAbsoluteAbelianizationEquiv K).symm.toHomeomorph
    exact @Homeomorph.t2Space _ _ _ _ hsource
      (separableToStandardAbsoluteAbelianizationEquiv K).toHomeomorph

/-- The usual absolute Galois topological abelianization, packaged as a stable
profinite group. -/
noncomputable def standardLocalAbsoluteAbelianProfinite
    (K : Type) [Field K] : ProfiniteGrp :=
  ProfiniteGrp.of (_root_.Field.absoluteGaloisGroupAbelianization K)

/-- The canonical extension of the separable absolute Artin map to the
open-finite-quotient completion of the local multiplicative group. -/
noncomputable def separableProfiniteLocalReciprocityHom :
    TopologicalProfiniteCompletion Kˣ →ₜ*
      localAbsoluteAbelianProfinite K :=
  topologicalProfiniteCompletionLift
    (localAbsoluteAbelianProfinite K)
    (separableAbsoluteLocalArtinMap K)

/-- The separable reciprocity lift agrees with the Artin map on canonical completion points. -/
@[simp]
theorem separableProfiniteLocalReciprocityHom_map (a : Kˣ) :
    separableProfiniteLocalReciprocityHom K
        (topologicalProfiniteCompletionMap Kˣ a) =
      separableAbsoluteLocalArtinMap K a :=
  topologicalProfiniteCompletionLift_map
    (localAbsoluteAbelianProfinite K)
    (separableAbsoluteLocalArtinMap K) a

/-- Composing the separable reciprocity lift with the completion map recovers the Artin map. -/
@[simp]
theorem separableProfiniteLocalReciprocityHom_comp_completionMap :
    (separableProfiniteLocalReciprocityHom K).comp
        (topologicalProfiniteCompletionMap Kˣ) =
      separableAbsoluteLocalArtinMap K :=
  topologicalProfiniteCompletionLift_comp_map
    (localAbsoluteAbelianProfinite K)
    (separableAbsoluteLocalArtinMap K)

/-- The separable profinite reciprocity homomorphism is onto. -/
theorem separableProfiniteLocalReciprocityHom_surjective :
    Function.Surjective (separableProfiniteLocalReciprocityHom K) :=
  topologicalProfiniteCompletionLift_surjective_of_denseRange
    (localAbsoluteAbelianProfinite K)
    (separableAbsoluteLocalArtinMap K)
    (separableAbsoluteLocalArtinMap_denseRange K)

/-- Finite local existence makes the separable profinite reciprocity
homomorphism one-to-one. -/
theorem separableProfiniteLocalReciprocityHom_injective :
    Function.Injective (separableProfiniteLocalReciprocityHom K) :=
  topologicalProfiniteCompletionLift_injective_of_preimage_cofinal
    (localAbsoluteAbelianProfinite K)
    (separableAbsoluteLocalArtinMap K)
    (separableAbsoluteLocalArtinMap_preimage_cofinal K)

/-- Profinite local reciprocity for the fixed separable closure. -/
noncomputable def separableProfiniteLocalReciprocity :
    TopologicalProfiniteCompletion Kˣ ≃ₜ*
      localAbsoluteAbelianProfinite K :=
  { Continuous.homeoOfEquivCompactToT2
      (f := Equiv.ofBijective
        (separableProfiniteLocalReciprocityHom K)
        ⟨separableProfiniteLocalReciprocityHom_injective K,
          separableProfiniteLocalReciprocityHom_surjective K⟩)
      (separableProfiniteLocalReciprocityHom K).continuous_toFun with
    map_mul' := (separableProfiniteLocalReciprocityHom K).map_mul }

/-- The separable reciprocity equivalence has the same underlying map as its lifted homomorphism. -/
@[simp]
theorem separableProfiniteLocalReciprocity_apply
    (x : TopologicalProfiniteCompletion Kˣ) :
    separableProfiniteLocalReciprocity K x =
      separableProfiniteLocalReciprocityHom K x :=
  rfl

/-- The forward transport from the separable to the usual absolute
topological abelianization, as a continuous homomorphism. -/
noncomputable def separableToStandardAbsoluteAbelianizationHom :
    localAbsoluteAbelianProfinite K →ₜ*
      standardLocalAbsoluteAbelianProfinite K :=
  ContinuousMonoidHom.toContinuousMonoidHom
    (separableToStandardAbsoluteAbelianizationEquiv K)

/-- The absolute local Artin map with Mathlib's usual algebraic-closure
absolute Galois group as target. -/
noncomputable def absoluteLocalArtinMap :
    Kˣ →ₜ* standardLocalAbsoluteAbelianProfinite K :=
  (separableToStandardAbsoluteAbelianizationHom K).comp
    (separableAbsoluteLocalArtinMap K)

/-- Transporting the separable Artin map to the standard model gives the absolute Artin map. -/
@[simp]
theorem separableToStandardAbsoluteAbelianizationEquiv_symm_artinMap
    (a : Kˣ) :
    (separableToStandardAbsoluteAbelianizationEquiv K).symm
        (absoluteLocalArtinMap K a) =
      separableAbsoluteLocalArtinMap K a := by
  change
    (separableToStandardAbsoluteAbelianizationEquiv K).symm
        (separableToStandardAbsoluteAbelianizationEquiv K
          (separableAbsoluteLocalArtinMap K a)) =
      separableAbsoluteLocalArtinMap K a
  exact (separableToStandardAbsoluteAbelianizationEquiv K).symm_apply_apply _

/-- The usual absolute local Artin map has dense image. -/
theorem absoluteLocalArtinMap_denseRange :
    DenseRange (absoluteLocalArtinMap K) := by
  let e := separableToStandardAbsoluteAbelianizationEquiv K
  change DenseRange (fun a => e (separableAbsoluteLocalArtinMap K a))
  exact e.surjective.denseRange.comp
    (separableAbsoluteLocalArtinMap_denseRange K) e.continuous

/-- The canonical homomorphism from the topological profinite completion of
`K×` to the usual absolute Galois topological abelianization. -/
noncomputable def profiniteLocalReciprocityHom :
    TopologicalProfiniteCompletion Kˣ →ₜ*
      standardLocalAbsoluteAbelianProfinite K :=
  topologicalProfiniteCompletionLift
    (standardLocalAbsoluteAbelianProfinite K) (absoluteLocalArtinMap K)

/-- The standard reciprocity lift agrees with the absolute Artin map on canonical completion
points. -/
@[simp]
theorem profiniteLocalReciprocityHom_map (a : Kˣ) :
    profiniteLocalReciprocityHom K
        (topologicalProfiniteCompletionMap Kˣ a) =
      absoluteLocalArtinMap K a :=
  topologicalProfiniteCompletionLift_map
    (standardLocalAbsoluteAbelianProfinite K) (absoluteLocalArtinMap K) a

/-- The profinite reciprocity homomorphism extends the absolute Artin map. -/
@[simp]
theorem profiniteLocalReciprocityHom_comp_completionMap :
    (profiniteLocalReciprocityHom K).comp
        (topologicalProfiniteCompletionMap Kˣ) =
      absoluteLocalArtinMap K :=
  topologicalProfiniteCompletionLift_comp_map
    (standardLocalAbsoluteAbelianProfinite K) (absoluteLocalArtinMap K)

/-- Dense range of the absolute Artin map and compactness of the completion
make the profinite reciprocity homomorphism onto. -/
theorem profiniteLocalReciprocityHom_surjective :
    Function.Surjective (profiniteLocalReciprocityHom K) :=
  topologicalProfiniteCompletionLift_surjective_of_denseRange
    (standardLocalAbsoluteAbelianProfinite K) (absoluteLocalArtinMap K)
      (absoluteLocalArtinMap_denseRange K)

/-- Finite target projections agree with projection of the absolute Artin
map on the dense copy of `K×`. -/
theorem profiniteLocalReciprocityHom_finiteProjection_map
    (N : OpenNormalSubgroup (standardLocalAbsoluteAbelianProfinite K))
    (a : Kˣ) :
    topologicalProfiniteCompletionFiniteProjection
        (standardLocalAbsoluteAbelianProfinite K) (absoluteLocalArtinMap K) N
        (topologicalProfiniteCompletionMap Kˣ a) =
      QuotientGroup.mk' N.toSubgroup (absoluteLocalArtinMap K a) :=
  topologicalProfiniteCompletionFiniteProjection_map
    (standardLocalAbsoluteAbelianProfinite K) (absoluteLocalArtinMap K) N a

/-- The profinite reciprocity homomorphism is the unique continuous
homomorphism extending the absolute local Artin map. -/
theorem profiniteLocalReciprocityHom_unique
    (f : TopologicalProfiniteCompletion Kˣ →ₜ*
      standardLocalAbsoluteAbelianProfinite K)
    (hf : f.comp (topologicalProfiniteCompletionMap Kˣ) =
      absoluteLocalArtinMap K) :
    f = profiniteLocalReciprocityHom K :=
  topologicalProfiniteCompletionLift_unique
    (standardLocalAbsoluteAbelianProfinite K) (absoluteLocalArtinMap K) f hf

/-- The canonical lift to the usual absolute abelianization is transport of
the corresponding separable lift. -/
theorem profiniteLocalReciprocityHom_eq_transport :
    profiniteLocalReciprocityHom K =
      (separableToStandardAbsoluteAbelianizationHom K).comp
        (separableProfiniteLocalReciprocityHom K) := by
  symm
  apply profiniteLocalReciprocityHom_unique K
  apply ContinuousMonoidHom.ext
  intro a
  change
    separableToStandardAbsoluteAbelianizationEquiv K
        (separableProfiniteLocalReciprocityHom K
          (topologicalProfiniteCompletionMap Kˣ a)) =
      absoluteLocalArtinMap K a
  rw [separableProfiniteLocalReciprocityHom_map]
  rfl

/-- The canonical lift to the usual absolute abelianization is one-to-one. -/
theorem profiniteLocalReciprocityHom_injective :
    Function.Injective (profiniteLocalReciprocityHom K) := by
  rw [profiniteLocalReciprocityHom_eq_transport K]
  exact (separableToStandardAbsoluteAbelianizationEquiv K).injective.comp
    (separableProfiniteLocalReciprocityHom_injective K)

/-- **Profinite local reciprocity.** The topological profinite completion of
the local multiplicative group is canonically continuously isomorphic to the
topological abelianization of Mathlib's usual absolute Galois group. -/
noncomputable def profiniteLocalReciprocity :
    TopologicalProfiniteCompletion Kˣ ≃ₜ*
      standardLocalAbsoluteAbelianProfinite K :=
  { Continuous.homeoOfEquivCompactToT2
      (f := Equiv.ofBijective
        (profiniteLocalReciprocityHom K)
        ⟨profiniteLocalReciprocityHom_injective K,
          profiniteLocalReciprocityHom_surjective K⟩)
      (profiniteLocalReciprocityHom K).continuous_toFun with
    map_mul' := (profiniteLocalReciprocityHom K).map_mul }

/-- The standard reciprocity equivalence has the same underlying map as its lifted homomorphism. -/
@[simp]
theorem profiniteLocalReciprocity_apply
    (x : TopologicalProfiniteCompletion Kˣ) :
    profiniteLocalReciprocity K x =
      profiniteLocalReciprocityHom K x :=
  rfl

/-- Profinite reciprocity restricts to the absolute local Artin map on the
dense copy of the local multiplicative group. -/
theorem profiniteLocalReciprocity_completionMap (a : Kˣ) :
    profiniteLocalReciprocity K
        (topologicalProfiniteCompletionMap Kˣ a) =
      absoluteLocalArtinMap K a :=
  profiniteLocalReciprocityHom_map K a

/-- The absolute local Artin map is injective. -/
theorem absoluteLocalArtinMap_injective :
    Function.Injective (absoluteLocalArtinMap K) := by
  intro x y hxy
  apply topologicalProfiniteCompletionMap_injective_localField K
  apply (profiniteLocalReciprocity K).injective
  rw [profiniteLocalReciprocity_completionMap,
    profiniteLocalReciprocity_completionMap]
  exact hxy

/-- Every finite quotient projection of profinite reciprocity is the finite
projection canonically induced by the absolute local Artin map. -/
theorem profiniteLocalReciprocity_finiteProjection
    (N : OpenNormalSubgroup (standardLocalAbsoluteAbelianProfinite K))
    (x : TopologicalProfiniteCompletion Kˣ) :
    QuotientGroup.mk' N.toSubgroup (profiniteLocalReciprocity K x) =
      topologicalProfiniteCompletionFiniteProjection
        (standardLocalAbsoluteAbelianProfinite K) (absoluteLocalArtinMap K) N x := by
  let lhs : TopologicalProfiniteCompletion Kˣ →
      (((standardLocalAbsoluteAbelianProfinite K).toFiniteQuotientFunctor ⋙
        forget₂ FiniteGrp ProfiniteGrp).obj N : Type) :=
    fun y => QuotientGroup.mk' N.toSubgroup (profiniteLocalReciprocity K y)
  let rhs : TopologicalProfiniteCompletion Kˣ →
      (((standardLocalAbsoluteAbelianProfinite K).toFiniteQuotientFunctor ⋙
        forget₂ FiniteGrp ProfiniteGrp).obj N : Type) :=
    fun y => topologicalProfiniteCompletionFiniteProjection
      (standardLocalAbsoluteAbelianProfinite K) (absoluteLocalArtinMap K) N y
  have hlhs : Continuous lhs := by
    let : DiscreteTopology
        (standardLocalAbsoluteAbelianProfinite K ⧸ N.toSubgroup) :=
      QuotientGroup.discreteTopology N.isOpen'
    let q :
        (standardLocalAbsoluteAbelianProfinite K ⧸ N.toSubgroup) →ₜ*
          (((standardLocalAbsoluteAbelianProfinite K).toFiniteQuotientFunctor ⋙
            forget₂ FiniteGrp ProfiniteGrp).obj N : Type) :=
      { toFun := id
        map_one' := rfl
        map_mul' := by intro a b; rfl
        continuous_toFun := continuous_of_discreteTopology }
    exact q.continuous_toFun.comp
      (QuotientGroup.continuous_mk.comp
        (profiniteLocalReciprocity K).continuous)
  have hrhs : Continuous rhs :=
    (topologicalProfiniteCompletionFiniteProjection
      (standardLocalAbsoluteAbelianProfinite K)
      (absoluteLocalArtinMap K) N).continuous_toFun
  have heq : lhs = rhs :=
    (topologicalProfiniteCompletionMap_denseRange Kˣ).equalizer
      hlhs hrhs <| by
        funext a
        change
          QuotientGroup.mk' N.toSubgroup
              (profiniteLocalReciprocity K
                (topologicalProfiniteCompletionMap Kˣ a)) =
            topologicalProfiniteCompletionFiniteProjection
              (standardLocalAbsoluteAbelianProfinite K)
              (absoluteLocalArtinMap K) N
              (topologicalProfiniteCompletionMap Kˣ a)
        rw [profiniteLocalReciprocity_completionMap,
          profiniteLocalReciprocityHom_finiteProjection_map]
  exact congrFun heq x

/-- Profinite local reciprocity is the unique continuous multiplicative
equivalence whose composite with the completion map is the absolute Artin
map. -/
theorem profiniteLocalReciprocity_unique
    (e : TopologicalProfiniteCompletion Kˣ ≃ₜ*
      standardLocalAbsoluteAbelianProfinite K)
    (he : (ContinuousMonoidHom.toContinuousMonoidHom e).comp
        (topologicalProfiniteCompletionMap Kˣ) =
      absoluteLocalArtinMap K) :
    e = profiniteLocalReciprocity K := by
  apply ContinuousMulEquiv.ext
  intro x
  have hhom := profiniteLocalReciprocityHom_unique K
    (ContinuousMonoidHom.toContinuousMonoidHom e) he
  exact DFunLike.congr_fun hhom x

/-- Mathlib's absolute Galois abelianization is canonically the inverse limit
of its finite quotients, after transport from the fixed separable closure. -/
noncomputable def standardAbsoluteGaloisAbelianizationLimitEquiv :
    ContinuousMulEquiv (standardLocalAbsoluteAbelianProfinite K)
      (absoluteFiniteArtinLimit K) :=
  (separableToStandardAbsoluteAbelianizationEquiv K).symm.trans
    (absoluteGaloisAbelianizationLimitEquiv K)

/-- Every finite projection of the absolute Artin map is its corresponding
finite local Artin coordinate after canonical transport to the separable
closure model. -/
theorem absoluteLocalArtinMap_finiteProjection
    (N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K))
    (a : Units K) :
    QuotientGroup.mk' N.toSubgroup
        ((separableToStandardAbsoluteAbelianizationEquiv K).symm
          (absoluteLocalArtinMap K a)) =
      absoluteFiniteArtinMap K N a := by
  rw [separableToStandardAbsoluteAbelianizationEquiv_symm_artinMap]
  exact separableAbsoluteLocalArtinMap_finiteProjection K N a

end LocalClassFieldTheory
