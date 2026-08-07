/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

/-
Blueprint unit: mapping-degree. Ramification and branch loci are finite; regular values.
-/
import LeanPool.JacobianDiffgeo.MappingDegree.Basics

/-!
# Ramification locus, branch locus, regular values

* `RS.ramificationLocus F` (points with `multiplicity ≥ 2`), `RS.branchLocus F` (their images),
  `RS.IsRegularValue F y` (no ramification point in the fiber).
* Finiteness (Forster 4.23-adjacent): `RS.isClosed_ramificationLocus`,
  `RS.isDiscrete_ramificationLocus`, `RS.ramificationLocus_finite`, `RS.branchLocus_finite`.
* Regular values: `RS.isRegularValue_iff_notMem_branchLocus`,
  `RS.multiplicity_eq_one_of_isRegularValue`, cofiniteness
  `RS.setOf_isRegularValue_mem_cofinite`, density `RS.dense_setOf_isRegularValue`, and
  existence `RS.exists_isRegularValue`.
-/

open Filter Set Function
open scoped ContDiff Manifold Topology

namespace RS

/-! ### Definitions (minimal instances) -/

section Defs

variable {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y]

/-- Points where `F` is ramified (local multiplicity `≥ 2`, CC4's `IsRamifiedAt`). -/
def ramificationLocus (F : X → Y) : Set X := {x | IsRamifiedAt F x}

/-- Branch values (critical values): images of ramification points. -/
def branchLocus (F : X → Y) : Set Y := F '' ramificationLocus F

/-- `y` is a regular value iff every point of its fiber is unramified. (For holomorphic
nonconstant `F` this is equivalent to `y ∉ branchLocus F`, and then every fiber point has
multiplicity exactly `1`.) Values NOT attained are regular (empty fiber) — harmless, since for
nonconstant `F` every value is attained. -/
def IsRegularValue (F : X → Y) (y : Y) : Prop := ∀ x ∈ F ⁻¹' {y}, ¬ IsRamifiedAt F x

theorem mem_ramificationLocus_iff {F : X → Y} {x : X} :
    x ∈ ramificationLocus F ↔ 2 ≤ multiplicity F x := Iff.rfl

/-- Pure set algebra: regular values are exactly the non-branch values. -/
theorem isRegularValue_iff_notMem_branchLocus (F : X → Y) (y : Y) :
    IsRegularValue F y ↔ y ∉ branchLocus F := by
  constructor
  · rintro h ⟨x, hx, rfl⟩
    exact h x rfl hx
  · intro h x hxy hram
    exact h ⟨x, hram, hxy⟩

end Defs

/-! ### Finiteness (standing surface hypotheses) -/

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {F : X → Y}

omit [T2Space X] [CompactSpace X] in
/-- Ramification is isolated: near any point (off the point itself) `F` is unramified. -/
theorem eventually_notMem_ramificationLocus (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hne : ¬ ∃ c, ∀ x, F x = c) (x : X) :
    ∀ᶠ z in 𝓝[≠] x, z ∉ ramificationLocus F := by
  filter_upwards [eventually_multiplicity_eq_one (hF x) (not_eventuallyConst hF hne x)]
    with z hz hmem
  have h2 : 2 ≤ multiplicity F z := hmem
  omega

omit [T2Space X] [CompactSpace X] in
theorem isClosed_ramificationLocus (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hne : ¬ ∃ c, ∀ x, F x = c) : IsClosed (ramificationLocus F) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  have h := eventually_notMem_ramificationLocus hF hne x
  rw [eventually_nhdsWithin_iff] at h
  filter_upwards [h] with z hz
  rcases eq_or_ne z x with rfl | hzx
  · exact hx
  · exact hz (by simpa using hzx)

omit [T2Space X] [CompactSpace X] in
theorem isDiscrete_ramificationLocus (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hne : ¬ ∃ c, ∀ x, F x = c) : IsDiscrete (ramificationLocus F) := by
  rw [isDiscrete_iff_nhdsNE]
  intro x _
  rw [inf_principal_eq_bot]
  exact eventually_notMem_ramificationLocus hF hne x

omit [T2Space X] in
theorem ramificationLocus_finite (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hne : ¬ ∃ c, ∀ x, F x = c) : (ramificationLocus F).Finite :=
  (isClosed_ramificationLocus hF hne).isCompact.finite (isDiscrete_ramificationLocus hF hne)

omit [T2Space X] in
theorem branchLocus_finite (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hne : ¬ ∃ c, ∀ x, F x = c) : (branchLocus F).Finite :=
  (ramificationLocus_finite hF hne).image F

omit [T2Space X] [CompactSpace X] in
/-- Over a regular value every fiber point has multiplicity exactly `1`. -/
theorem multiplicity_eq_one_of_isRegularValue (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hne : ¬ ∃ c, ∀ x, F x = c) {y : Y} (hy : IsRegularValue F y) {x : X}
    (hx : F x = y) : multiplicity F x = 1 := by
  have h1 := one_le_multiplicity_of_not_const hF hne x
  have h2 : ¬ 2 ≤ multiplicity F x := hy x hx
  omega

omit [T2Space X] in
/-- Regular values are cofinite. -/
theorem setOf_isRegularValue_mem_cofinite (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hne : ¬ ∃ c, ∀ x, F x = c) : {y | IsRegularValue F y} ∈ Filter.cofinite := by
  rw [Filter.mem_cofinite]
  apply (branchLocus_finite hF hne).subset
  intro y hy
  simp only [mem_compl_iff, mem_ofPred_eq] at hy
  by_contra hnb
  exact hy ((isRegularValue_iff_notMem_branchLocus F y).mpr hnb)

omit [T2Space X] in
/-- Regular values are dense (`Y` is perfect and T1, so finite sets have empty interior). -/
theorem dense_setOf_isRegularValue (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hne : ¬ ∃ c, ∀ x, F x = c) : Dense {y | IsRegularValue F y} := by
  have hd : Dense (branchLocus F)ᶜ := by
    rw [← interior_eq_empty_iff_dense_compl, Set.eq_empty_iff_forall_notMem]
    intro y hy
    exact infinite_of_mem_nhds y (mem_interior_iff_mem_nhds.mp hy) (branchLocus_finite hF hne)
  exact hd.mono fun y hy ↦ (isRegularValue_iff_notMem_branchLocus F y).mpr hy

omit [T2Space X] in
theorem exists_isRegularValue [Nonempty Y] (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hne : ¬ ∃ c, ∀ x, F x = c) : ∃ y, IsRegularValue F y :=
  (dense_setOf_isRegularValue hF hne).nonempty

end RS
