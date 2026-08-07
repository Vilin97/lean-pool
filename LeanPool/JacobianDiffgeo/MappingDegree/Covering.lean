/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

/-
Blueprint unit: mapping-degree. `F` is a covering map away from the (finite) branch locus.
-/
import LeanPool.JacobianDiffgeo.MappingDegree.Ramification
import Mathlib.Topology.Covering.Basic

/-!
# Covering structure off the branch locus

* `RS.exists_openPartialHomeomorph_coe_eq` — at an unramified point, the local homeomorphism
  from local-multiplicity's Forster 2.5 export upgrades to one whose coercion is literally `F`
  (mathlib's covering constructor needs `⇑φ = F` on the nose, not just `EqOn` on the source).
* `RS.isCoveringMapOn_compl_branchLocus` — `F` is a covering map on `(branchLocus F)ᶜ`
  (`Mathlib`'s `IsCoveringMapOn.of_openPartialHomeomorph`: compact T2 source, T2 target, local
  homeomorphism at every point of the fiber ⇒ evenly covered).
* `RS.isEvenlyCovered_of_isRegularValue` — the covering statement specialized to a single
  regular value.

Downstream may further compose with mathlib's `IsCoveringMapOn.isCoveringMap_restrictPreimage`
(`Topology/Covering/Basic.lean`) for a genuine `IsCoveringMap` of the subtype restriction, and
with `Topology/Homotopy/Lifting.lean` for path/homotopy lifting — no extra exports needed here.
-/

open Filter Set Function
open scoped ContDiff Manifold Topology

namespace RS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {F : X → Y}

/-- Rebuild an `OpenPartialHomeomorph` with a globally-specified `toFun` that agrees with the
original on its source: all `PartialEquiv`/`OpenPartialHomeomorph` axioms quantify only over
`source`/`target`, so the pointwise agreement transports every field. Private plumbing for
`exists_openPartialHomeomorph_coe_eq`. -/
private def copyOfEqOn {F : X → Y} (ψ : OpenPartialHomeomorph X Y)
    (hEq : ∀ z ∈ ψ.source, ψ z = F z) : OpenPartialHomeomorph X Y :=
  have hEq' : ∀ z ∈ ψ.source, ψ.toFun z = F z := hEq
  { toFun := F
    invFun := ψ.invFun
    source := ψ.source
    target := ψ.target
    map_source' := fun x hx ↦ by rw [← hEq' x hx]; exact ψ.map_source' hx
    map_target' := ψ.map_target'
    left_inv' := fun x hx ↦ by
      have h := ψ.left_inv' hx
      rwa [hEq' x hx] at h
    right_inv' := fun y hy ↦ by
      have hsrc := ψ.map_target' hy
      have h := ψ.right_inv' hy
      rwa [hEq' _ hsrc] at h
    open_source := ψ.open_source
    open_target := ψ.open_target
    continuousOn_toFun := ψ.continuousOn_toFun.congr (fun z hz ↦ (hEq' z hz).symm)
    continuousOn_invFun := ψ.continuousOn_invFun }

omit [T2Space X] [CompactSpace X] in
/-- Multiplicity-1 points admit an `OpenPartialHomeomorph` whose coercion is literally `F` (the
coe-exact upgrade of local-multiplicity's Forster 2.5 export; mathlib's covering constructor
requires `⇑φ = F` on the nose). -/
theorem exists_openPartialHomeomorph_coe_eq (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hne : ¬ ∃ c, ∀ x, F x = c) {x : X} (h1 : ¬ IsRamifiedAt F x) :
    ∃ φ : OpenPartialHomeomorph X Y, x ∈ φ.source ∧ ⇑φ = F := by
  have hmult : multiplicity F x = 1 := by
    have h2 := one_le_multiplicity_of_not_const hF hne x
    unfold IsRamifiedAt at h1
    omega
  obtain ⟨ψ, hxψ, hEq⟩ := exists_openPartialHomeomorph_of_multiplicity_eq_one (hF x)
    (not_eventuallyConst hF hne x) hmult
  exact ⟨copyOfEqOn ψ hEq, hxψ, rfl⟩

/-- `F` is a covering map away from the (finite) branch locus. -/
theorem isCoveringMapOn_compl_branchLocus (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hne : ¬ ∃ c, ∀ x, F x = c) : IsCoveringMapOn F (branchLocus F)ᶜ := by
  apply IsCoveringMapOn.of_isLocalHomeomorphOn hF.continuous
  intro x hx
  obtain ⟨φ, hxφ, hφ⟩ :=
    exists_openPartialHomeomorph_coe_eq hF hne (x := x) (fun hram ↦ hx ⟨x, hram, rfl⟩)
  exact ⟨φ, hxφ, hφ.symm⟩

/-- The covering statement specialized to a single regular value. -/
theorem isEvenlyCovered_of_isRegularValue (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hne : ¬ ∃ c, ∀ x, F x = c) {y : Y} (hy : IsRegularValue F y) :
    IsEvenlyCovered F y (F ⁻¹' {y}) :=
  isCoveringMapOn_compl_branchLocus hF hne y ((isRegularValue_iff_notMem_branchLocus F y).mp hy)

end RS
