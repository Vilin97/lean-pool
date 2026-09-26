/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Analysis.OpenMapping
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.CommonExtension
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.FunctionSpace
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.IdentityPrinciple

/-!
# Restriction and continuous extension of holomorphic maps

Restriction is a continuous linear map, injective from a connected larger domain when the
smaller domain is nonempty. When it is surjective, its inverse is continuous for the
compact-open topology, by the Fréchet open-mapping argument for complete metrizable topological
vector spaces. Reference: [Scheidemann][Scheidemann2005] (2005), Proposition 2.1.3 and Exercise
2.1.13.

## Main results

`holomorphicRestrictCLM` is restriction as a continuous linear map.
`exists_holomorphicRestrictionEquiv` is a compact-open isomorphism when restriction is
bijective. `HolomorphicAlgebra` is the scalar holomorphic algebra, with
`holomorphicRestrictAlgHom` and `holomorphicRestrictionAlgEquiv` as the algebraic restriction
maps. `exists_holomorphicAlgebraEquiv_of_commonExtension` is an algebra isomorphism from a
common extension domain.

## References

* [V. Scheidemann, *Introduction to Complex Analysis in Several Variables*][Scheidemann2005]
-/

public noncomputable section

open Set

namespace SeveralComplexVariables

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {U V : TopologicalSpace.Opens E}

/-- Restriction as a continuous complex-linear operator between compact-open spaces. -/
@[expose] def holomorphicRestrictCLM (hVU : V ≤ U) : HolomorphicMap U F →L[ℂ] HolomorphicMap V F
  where
  toFun := holomorphicRestrict hVU
  map_add' := by intro f g; rfl
  map_smul' := by intro c f; rfl
  cont := continuous_holomorphicRestrict hVU

/-- An ambient extension theorem makes restriction surjective on the bundled spaces. -/
theorem holomorphicRestrict_surjective (hVU : V ≤ U)
    (hext : ∀ f : E → F, AnalyticOnNhd ℂ f V →
      ∃ g, AnalyticOnNhd ℂ g U ∧ EqOn g f V) :
    Function.Surjective (holomorphicRestrict (F := F) hVU) := by
  intro f
  obtain ⟨g, hg, heq⟩ := hext (openExtension V f.val) f.property
  let G : HolomorphicMap U F := ⟨⟨fun z => g z, hg.continuousOn.domRestrict⟩,
    hg.congr U.isOpen (fun z hz => by rw [openExtension_apply U _ hz]; rfl)⟩
  refine ⟨G, ?_⟩
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  exact (heq z.property).trans (openExtension_coe V f.val z)

/-- On a connected larger domain, restriction to a nonempty open subset is injective. -/
theorem holomorphicRestrict_injective (hVU : V ≤ U)
    (hc : IsPreconnected (U : Set E)) (hne : (V : Set E).Nonempty) :
    Function.Injective (holomorphicRestrict (F := F) hVU) := by
  intro f g he
  have hEq : EqOn (openExtension U f.val) (openExtension U g.val) V := by
    intro z hz
    have h := congrArg (fun k : HolomorphicMap V F => k.val ⟨z, hz⟩) he
    rw [openExtension_apply U _ (hVU hz), openExtension_apply U _ (hVU hz)]
    exact h
  obtain ⟨z, hz⟩ := hne
  have hAll := f.property.eqOn_of_preconnected_of_eventuallyEq g.property hc (hVU hz)
    (Filter.mem_of_superset (V.isOpen.mem_nhds hz) hEq)
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  simpa only [openExtension_coe] using hAll z.property

/-- Restriction to a dense open subset is injective, without connectedness or nonemptiness
assumptions on either domain. Continuity of the holomorphic representatives suffices. -/
theorem holomorphicRestrict_injective_of_subset_closure (hVU : V ≤ U)
    (hd : (U : Set E) ⊆ closure (V : Set E)) :
    Function.Injective (holomorphicRestrict (F := F) hVU) := by
  intro f g he
  have hEq : EqOn (openExtension U f.val) (openExtension U g.val) V := by
    intro z hz
    have h := congrArg (fun k : HolomorphicMap V F => k.val ⟨z, hz⟩) he
    rw [openExtension_apply U _ (hVU hz), openExtension_apply U _ (hVU hz)]
    exact h
  have hAll := hEq.of_subset_closure f.property.continuousOn g.property.continuousOn hVU hd
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  simpa only [openExtension_coe] using hAll z.property

/-- Surjective restriction is a continuous linear equivalence under the identity-theorem hypotheses,
by the open-mapping theorem for complete metrizable compact-open spaces. Banach-valued targets
need not be finite dimensional. -/
theorem exists_holomorphicRestrictionEquiv [FiniteDimensional ℂ E] [CompleteSpace F] (hVU : V ≤ U)
    (hc : IsPreconnected (U : Set E)) (hne : (V : Set E).Nonempty)
    (hs : Function.Surjective (holomorphicRestrict (F := F) hVU)) :
    ∃ e : HolomorphicMap U F ≃L[ℂ] HolomorphicMap V F,
      (e : HolomorphicMap U F → HolomorphicMap V F) = holomorphicRestrict hVU := by
  let : ProperSpace E := FiniteDimensional.proper ℂ E
  let : SecondCountableTopology E := (Module.finBasis ℂ
    E).equivFunL.toHomeomorph.secondCountableTopology
  let : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  let : LocallyCompactSpace V := V.isOpen.locallyCompactSpace
  have : (uniformity C(U, F)).IsCountablyGenerated := inferInstance
  have : (uniformity C(V, F)).IsCountablyGenerated := inferInstance
  have : (uniformity (HolomorphicMap U F)).IsCountablyGenerated :=
    Filter.comap.isCountablyGenerated _ _
  have : (uniformity (HolomorphicMap V F)).IsCountablyGenerated :=
    Filter.comap.isCountablyGenerated _ _
  let : PseudoMetricSpace (HolomorphicMap U F) := UniformSpace.pseudoMetricSpace _
  let : PseudoMetricSpace (HolomorphicMap V F) := UniformSpace.pseudoMetricSpace _
  let e := LinearEquiv.ofBijective (holomorphicRestrictCLM (F := F) hVU).toLinearMap
    ⟨holomorphicRestrict_injective hVU hc hne, hs⟩
  have hopen := ContinuousLinearMap.isOpenMap_of_surjective_complete (holomorphicRestrictCLM (F :=
    F) hVU) hs
  exact ⟨ContinuousLinearEquiv.ofIsHomeomorph e
    ⟨continuous_holomorphicRestrict hVU,
      hopen, e.bijective⟩, rfl⟩

/-- Scalar holomorphic functions form a subalgebra of continuous functions. -/
@[expose, reducible]
def holomorphicSubalgebra (U : TopologicalSpace.Opens E) : Subalgebra ℂ C(U, ℂ) where
  carrier := (holomorphicSubmodule (F := ℂ) U : Set C(U, ℂ))
  zero_mem' := (holomorphicSubmodule U).zero_mem
  add_mem' := (holomorphicSubmodule U).add_mem
  mul_mem' := by
    intro f g hf hg
    apply AnalyticOnNhd.congr U.isOpen (hf.mul hg)
    intro z hz
    simp [openExtension_apply U _ hz]
  algebraMap_mem' := by
    intro c
    apply AnalyticOnNhd.congr U.isOpen (analyticOnNhd_const (v := c))
    intro z hz
    simp [openExtension_apply U _ hz]

/-- The scalar holomorphic algebra has the same underlying type as the holomorphic space. -/
abbrev HolomorphicAlgebra (U : TopologicalSpace.Opens E) : Type _ := ↥(holomorphicSubalgebra U)

/-- Restriction preserves multiplication and constants as well as linear operations. -/
@[expose] def holomorphicRestrictAlgHom (hVU : V ≤ U) : HolomorphicAlgebra U →ₐ[ℂ]
  HolomorphicAlgebra V where
  toFun := holomorphicRestrict hVU
  map_zero' := rfl
  map_one' := rfl
  map_add' := by intros; rfl
  map_mul' := by intros; rfl
  commutes' := by intros; rfl

/-- The algebra homomorphism has the same underlying function as ordinary restriction. -/
@[simp] theorem holomorphicRestrictAlgHom_coe (hVU : V ≤ U) :
    (holomorphicRestrictAlgHom hVU : HolomorphicAlgebra U → HolomorphicAlgebra V) =
      holomorphicRestrict hVU := rfl

/-- The algebraic restriction equivalence associated to surjectivity. Its continuity in both
directions is supplied by `exists_holomorphicRestrictionEquiv`. -/
@[expose] def holomorphicRestrictionAlgEquiv (hVU : V ≤ U)
    (hc : IsPreconnected (U : Set E)) (hne : (V : Set E).Nonempty)
    (hs : Function.Surjective (holomorphicRestrict (F := ℂ) hVU)) :
    HolomorphicAlgebra U ≃ₐ[ℂ] HolomorphicAlgebra V :=
  AlgEquiv.ofBijective (holomorphicRestrictAlgHom hVU)
    ⟨holomorphicRestrict_injective hVU hc hne, hs⟩

/-- The scalar algebra equivalence is continuous in both directions for the compact-open topology,
using the Fréchet open-mapping theorem for inverse continuity. -/
theorem continuous_holomorphicRestrictionAlgEquiv [FiniteDimensional ℂ E] (hVU : V ≤ U)
    (hc : IsPreconnected (U : Set E)) (hne : (V : Set E).Nonempty)
    (hs : Function.Surjective (holomorphicRestrict (F := ℂ) hVU)) :
    Continuous (holomorphicRestrictionAlgEquiv hVU hc hne hs) ∧
      Continuous (holomorphicRestrictionAlgEquiv hVU hc hne hs).symm := by
  obtain ⟨e, he⟩ := exists_holomorphicRestrictionEquiv hVU hc hne hs
  refine ⟨continuous_holomorphicRestrict hVU, ?_⟩
  have hsymm : (fun f : HolomorphicAlgebra V =>
      (holomorphicRestrictionAlgEquiv hVU hc hne hs).symm f) =
      (fun f : HolomorphicAlgebra V => e.symm f) := by
    funext f
    apply e.injective
    rw [ContinuousLinearEquiv.apply_symm_apply, he]
    exact (holomorphicRestrictionAlgEquiv hVU hc hne hs).apply_symm_apply f
  change Continuous (fun f : HolomorphicAlgebra V =>
    (holomorphicRestrictionAlgEquiv hVU hc hne hs).symm f)
  rw [hsymm]
  exact e.symm.continuous

/-- A common scalar extension pair gives an isomorphism of topological holomorphic algebras. The
connected larger set and nonempty smaller set ensure uniqueness. -/
theorem exists_holomorphicAlgebraEquiv_of_commonExtension [FiniteDimensional ℂ E]
    (h : IsCommonAnalyticExtension (V : Set E) (U : Set E))
    (hc : IsPreconnected (U : Set E)) (hne : (V : Set E).Nonempty) :
    ∃ e : HolomorphicAlgebra U ≃ₐ[ℂ] HolomorphicAlgebra V,
      (e : HolomorphicAlgebra U → HolomorphicAlgebra V) = holomorphicRestrict (F := ℂ) h.subset ∧
      Continuous e ∧ Continuous e.symm := by
  have hs := holomorphicRestrict_surjective h.subset (fun _ hf => h.exists_extension hf)
  exact ⟨holomorphicRestrictionAlgEquiv h.subset hc hne hs, rfl,
    continuous_holomorphicRestrictionAlgEquiv h.subset hc hne hs⟩

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
