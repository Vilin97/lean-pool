/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Cech.Cochains

/-!
# `H⁰(𝒰,D) ≃ L(D)` (CC8, proof plan §6.1)

Unit: cech-cohomology (`docs/design/cech-cohomology.md` §4.3).

* `toC0`: restriction of a relative section to the cover, landing in `ker d0`.
* `h0EquivLinSysOn`: `H⁰(𝒰,D) ≃ Γ(Ω, O_D)` — CC8's "definitionally easy" `H⁰ = L(D)`.
* `h0Equiv`: the global form `H⁰(𝒰,D) ≃ L(D)` for covers of `X`.
-/

open scoped ContDiff Manifold
open Set TopologicalSpace RS.Cech

namespace RS.Cech

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (D : RS.Divisor X) {Ω : Opens X} (𝒰 : FinCover Ω)

/-- Restriction of a relative section to the cover. -/
noncomputable def toC0 : RS.LinSysOn D (Ω : Set X) →ₗ[ℂ] C0 D 𝒰 :=
  LinearMap.pi fun i => LinSysOn.restrictL D (𝒰.le_base i)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem toC0_apply (φ : RS.LinSysOn D (Ω : Set X)) (i : Fin 𝒰.n) :
    toC0 D 𝒰 φ i = LinSysOn.restrictL D (𝒰.le_base i) φ := rfl

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem toC0_mem_ker (φ : RS.LinSysOn D (Ω : Set X)) :
    toC0 D 𝒰 φ ∈ LinearMap.ker (d0 D 𝒰) := by
  rw [LinearMap.mem_ker]
  funext p
  change LinSysOn.restrictL D inf_le_right (LinSysOn.restrictL D (𝒰.le_base p.2) φ) -
      LinSysOn.restrictL D inf_le_left (LinSysOn.restrictL D (𝒰.le_base p.1) φ) = 0
  rw [restrictL_restrictL D (𝒰.le_base p.2) inf_le_right (inf_le_right.trans (𝒰.le_base p.2)),
    restrictL_restrictL D (𝒰.le_base p.1) inf_le_left (inf_le_left.trans (𝒰.le_base p.1))]
  exact sub_self _

/-- `toC0`, corestricted to land in `ker d0`. -/
noncomputable def toC0' : RS.LinSysOn D (Ω : Set X) →ₗ[ℂ] LinearMap.ker (d0 D 𝒰) :=
  LinearMap.codRestrict _ (toC0 D 𝒰) (toC0_mem_ker D 𝒰)

omit [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- The cover's members exhaust `Ω` (as sets). -/
theorem iUnion_U_eq : (⋃ i, (𝒰.U i : Set X)) = (Ω : Set X) := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset fun i => 𝒰.le_base i
  · intro x hx
    obtain ⟨i, hi⟩ := 𝒰.covers x hx
    exact Set.mem_iUnion.2 ⟨i, hi⟩

theorem toC0'_injective : Function.Injective (toC0' D 𝒰) := by
  intro φ1 φ2 heq
  have hcomp : ∀ i, LinSysOn.restrictL D (𝒰.le_base i) φ1 = LinSysOn.restrictL D (𝒰.le_base i) φ2 :=
      by
    intro i
    have := congrArg (fun x => (x : LinearMap.ker (d0 D 𝒰)).1 i) heq
    simpa [toC0', toC0_apply] using this
  apply Subtype.ext
  set e := MeroGermOn.congrSet (iUnion_U_eq 𝒰).symm with he_def
  have key : e (φ1 : RS.MeroGermOn X (Ω : Set X)) = e (φ2 : RS.MeroGermOn X (Ω : Set X)) := by
    apply RS.MeroGermOn.glue_unique (fun i => (𝒰.U i).2)
    intro i
    have h1 : RS.MeroGermOn.restrict (Set.subset_iUnion (fun i => (𝒰.U i : Set X)) i)
        (e (φ1 : RS.MeroGermOn X (Ω : Set X))) =
        RS.MeroGermOn.restrict (𝒰.le_base i) (φ1 : RS.MeroGermOn X (Ω : Set X)) := by
      change RS.MeroGermOn.restrict _ (RS.MeroGermOn.restrict _ _) = _
      rw [RS.MeroGermOn.restrict_restrict]
    have h2 : RS.MeroGermOn.restrict (Set.subset_iUnion (fun i => (𝒰.U i : Set X)) i)
        (e (φ2 : RS.MeroGermOn X (Ω : Set X))) =
        RS.MeroGermOn.restrict (𝒰.le_base i) (φ2 : RS.MeroGermOn X (Ω : Set X)) := by
      change RS.MeroGermOn.restrict _ (RS.MeroGermOn.restrict _ _) = _
      rw [RS.MeroGermOn.restrict_restrict]
    rw [h1, h2]
    exact congrArg Subtype.val (hcomp i)
  exact e.injective key

theorem toC0'_surjective : Function.Surjective (toC0' D 𝒰) := by
  intro f
  set g : ∀ i, RS.MeroGermOn X (𝒰.U i : Set X) := fun i => (f.1 i : RS.MeroGermOn X (𝒰.U i : Set X))
    with hg_def
  have hcompat : ∀ i j, RS.MeroGermOn.restrict
      (Set.inter_subset_left : (𝒰.U i : Set X) ∩ 𝒰.U j ⊆ 𝒰.U i)
      (g i) = RS.MeroGermOn.restrict (Set.inter_subset_right : (𝒰.U i : Set X) ∩ 𝒰.U j ⊆ 𝒰.U j)
          (g j) := by
    intro i j
    have hd0 : d0 D 𝒰 f.1 = 0 := f.2
    have hcomp := congrFun hd0 (i, j)
    rw [d0_apply, Pi.zero_apply, sub_eq_zero] at hcomp
    exact (congrArg Subtype.val hcomp).symm
  obtain ⟨Φ, hΦ⟩ := RS.MeroGermOn.exists_glue (fun i => (𝒰.U i).2) g hcompat
  set e := MeroGermOn.congrSet (iUnion_U_eq 𝒰) with he_def
  have hΦmem : e Φ ∈ RS.LinSysOn D (Ω : Set X) := by
    apply (RS.mem_linSysOn_iff_of_isOpen Ω.2).2
    intro x hx
    obtain ⟨i, hi⟩ := 𝒰.covers x hx
    have hrestr : RS.MeroGermOn.restrict (𝒰.le_base i) (e Φ) = g i := by
      change RS.MeroGermOn.restrict (𝒰.le_base i) (RS.MeroGermOn.restrict _ Φ) = g i
      exact (RS.MeroGermOn.restrict_restrict _ _ Φ).trans (hΦ i)
    have hord := RS.MeroGermOn.ord_restrict (𝒰.le_base i) (𝒰.U i).2 Ω.2 hi (e Φ)
    rw [hrestr] at hord
    rw [← hord]
    exact (RS.mem_linSysOn_iff_of_isOpen (𝒰.U i).2).1 (f.1 i).2 x hi
  refine ⟨⟨e Φ, hΦmem⟩, ?_⟩
  apply Subtype.ext
  funext i
  change LinSysOn.restrictL D (𝒰.le_base i) ⟨e Φ, hΦmem⟩ = f.1 i
  apply Subtype.ext
  change RS.MeroGermOn.restrict (𝒰.le_base i) (e Φ) = g i
  change RS.MeroGermOn.restrict (𝒰.le_base i) (RS.MeroGermOn.restrict _ Φ) = g i
  exact (RS.MeroGermOn.restrict_restrict _ _ Φ).trans (hΦ i)

theorem toC0'_bijective : Function.Bijective (toC0' D 𝒰) :=
  ⟨toC0'_injective D 𝒰, toC0'_surjective D 𝒰⟩

/-- `H⁰(𝒰,D) ≃ Γ(Ω,O_D)` (CC8's "definitionally easy" `H⁰ = L(D)`, relativized to `Ω`). -/
noncomputable def h0EquivLinSysOn : LinearMap.ker (d0 D 𝒰) ≃ₗ[ℂ] RS.LinSysOn D (Ω : Set X) :=
  (LinearEquiv.ofBijective (toC0' D 𝒰) (toC0'_bijective D 𝒰)).symm

@[simp] theorem h0EquivLinSysOn_symm_apply (φ : RS.LinSysOn D (Ω : Set X)) (i : Fin 𝒰.n) :
    ((h0EquivLinSysOn D 𝒰).symm φ : C0 D 𝒰) i = LinSysOn.restrictL D (𝒰.le_base i) φ := by
  change ((toC0' D 𝒰) φ : C0 D 𝒰) i = _
  rfl

theorem h0EquivLinSysOn_symm_apply_ord (φ : RS.LinSysOn D (Ω : Set X)) (i : Fin 𝒰.n) {x : X}
    (hx : x ∈ 𝒰.U i) :
    (((h0EquivLinSysOn D 𝒰).symm φ : C0 D 𝒰) i : RS.MeroGermOn X (𝒰.U i : Set X)).ord x =
      (φ : RS.MeroGermOn X (Ω : Set X)).ord x := by
  rw [h0EquivLinSysOn_symm_apply]
  exact ord_restrictL D (𝒰.le_base i) hx φ

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- The absolute `LinSysOn D univ` and `LinSys D` are the same submodule (`Opens.coe_top` is
`rfl`, so only the `IsOpen`-gate needs unfolding). -/
theorem linSysOn_top_eq_linSys : RS.LinSysOn D ((⊤ : Opens X) : Set X) = RS.LinSys D := by
  apply Submodule.ext
  intro φ
  constructor
  · intro h x
    exact (RS.mem_linSysOn_iff_of_isOpen isOpen_univ).1 h x (Set.mem_univ x)
  · intro h
    exact (RS.mem_linSysOn_iff_of_isOpen isOpen_univ).2 (fun x _ => h x)

/-- Global form: `H⁰(𝒰,D) ≃ L(D)` for covers of `X`. -/
noncomputable def h0Equiv (𝒰 : FinCover (⊤ : Opens X)) :
    LinearMap.ker (d0 D 𝒰) ≃ₗ[ℂ] RS.LinSys D :=
  (h0EquivLinSysOn D 𝒰).trans (LinearEquiv.ofEq _ _ (linSysOn_top_eq_linSys D))

end RS.Cech
