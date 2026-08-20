/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie and Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.ChartExtraction
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

/-!
# Punctured surface charts

The disk and half-disk models used by the Moise construction remain path-connected after
deleting finitely many points.  The disk case transports the corresponding theorem for the
Euclidean plane through `Homeomorph.unitBall`.  For a half-disk, we delete the finite preimage
under the fold from the doubled disk, connect there, and fold the resulting path back.

These local results are the input for proving that a connected surface remains connected after
deleting a finite set.  That theorem, in turn, rules out multiple dual components in a completed
surface triangulation.
-/

open Set Topology

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

/-- Fold the open unit disk onto the open half-disk. -/
def foldDiskToHalfDisk :
    ChartKind.disk.modelRegion → ChartKind.halfDisk.modelRegion :=
  fun p => ⟨(foldPlaneToHalfSpace p).1, by
    constructor
    · have hp : (p : Plane) ∈ Metric.ball 0 1 := by
        exact p.2
      simpa only [Metric.mem_ball, dist_zero_right, norm_foldPlaneToHalfSpace] using hp
    · exact (foldPlaneToHalfSpace p).2⟩

/-- Folding the disk onto the half-disk is continuous. -/
theorem continuous_foldDiskToHalfDisk : Continuous foldDiskToHalfDisk := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val.comp
    (continuous_foldPlaneToHalfSpace.comp continuous_subtype_val)

/-- The inverse image of a finite set under the disk fold is finite.  Each fiber is contained in
the two-point set consisting of a point and its reflection across the boundary line. -/
theorem finite_preimage_foldDiskToHalfDisk
    (s : Set ChartKind.halfDisk.modelRegion) (hs : s.Finite) :
    (foldDiskToHalfDisk ⁻¹' s).Finite := by
  apply hs.preimage'
  intro q hq
  let candidates : Set Plane := {q.1, reflectAcrossHalfPlaneBoundary q.1}
  have hcandidates : candidates.Finite := by
    exact (Set.finite_singleton _).insert _
  have hpreCandidates :
      ((Subtype.val : ChartKind.disk.modelRegion → Plane) ⁻¹' candidates).Finite :=
    Set.Finite.preimage Subtype.val_injective.injOn hcandidates
  apply hpreCandidates.subset
  intro p hp
  change foldDiskToHalfDisk p = q at hp
  have hval : (foldPlaneToHalfSpace (p : Plane)).1 = (q : Plane) :=
    congrArg Subtype.val hp
  have h0 : |(p : Plane) 0| = (q : Plane) 0 := by
    simpa [foldPlaneToHalfSpace] using congrArg (fun z : Plane => z 0) hval
  have h1 : (p : Plane) 1 = (q : Plane) 1 := by
    simpa [foldPlaneToHalfSpace] using congrArg (fun z : Plane => z 1) hval
  have hq0 : 0 ≤ (q : Plane) 0 := q.2.2
  rcases (abs_eq hq0).mp h0 with hpos | hneg
  · change (p : Plane) ∈ candidates
    exact Set.mem_insert_iff.mpr (Or.inl (plane_ext hpos h1))
  · change (p : Plane) ∈ candidates
    apply Set.mem_insert_iff.mpr
    right
    apply Set.mem_singleton_iff.mpr
    apply plane_ext
    · simpa [reflectAcrossHalfPlaneBoundary] using hneg
    · simpa [reflectAcrossHalfPlaneBoundary] using h1

/-- Folding the disk onto the half-disk is surjective. -/
theorem surjective_foldDiskToHalfDisk :
    Function.Surjective foldDiskToHalfDisk := by
  intro q
  let p : ChartKind.disk.modelRegion := ⟨q.1, by
    simpa [ChartKind.modelRegion] using q.2.1⟩
  refine ⟨p, Subtype.ext ?_⟩
  apply plane_ext
  · simp [foldDiskToHalfDisk, foldPlaneToHalfSpace, abs_of_nonneg q.2.2, p]
  · simp [foldDiskToHalfDisk, foldPlaneToHalfSpace, p]

/-- An open disk with finitely many points deleted is path-connected. -/
theorem diskModel_compl_finite_isPathConnected
    (s : Set ChartKind.disk.modelRegion) (hs : s.Finite) :
    IsPathConnected sᶜ := by
  let e : Plane ≃ₜ ChartKind.disk.modelRegion := Homeomorph.unitBall
  rw [← e.isPathConnected_preimage]
  rw [preimage_compl]
  apply Set.Countable.isPathConnected_compl_of_one_lt_rank
  · apply Module.one_lt_rank_of_one_lt_finrank
    simp [Plane]
  · exact (Set.Finite.preimage e.injective.injOn hs).countable

/-- An open half-disk with finitely many points deleted is path-connected. -/
theorem halfDiskModel_compl_finite_isPathConnected
    (s : Set ChartKind.halfDisk.modelRegion) (hs : s.Finite) :
    IsPathConnected sᶜ := by
  have hpre : (foldDiskToHalfDisk ⁻¹' s).Finite :=
    finite_preimage_foldDiskToHalfDisk s hs
  have hpath :
      IsPathConnected ((foldDiskToHalfDisk ⁻¹' s)ᶜ) :=
    diskModel_compl_finite_isPathConnected _ hpre
  have himage := hpath.image continuous_foldDiskToHalfDisk
  rw [← preimage_compl,
    Set.image_preimage_eq _ surjective_foldDiskToHalfDisk] at himage
  exact himage

/-- Either Moise chart model remains path-connected after deleting finitely many points. -/
theorem ChartKind.isPathConnected_compl_finite
    (k : ChartKind) (s : Set k.modelRegion) (hs : s.Finite) :
    IsPathConnected sᶜ := by
  cases k with
  | disk => exact diskModel_compl_finite_isPathConnected s hs
  | halfDisk => exact halfDiskModel_compl_finite_isPathConnected s hs

/-- The underlying planar model region remains path-connected after deleting a finite ambient
set. -/
theorem ChartKind.isPathConnected_modelRegion_diff_finite
    (k : ChartKind) (s : Set Plane) (hs : s.Finite) :
    IsPathConnected (k.modelRegion \ s) := by
  let t : Set k.modelRegion :=
    (Subtype.val : k.modelRegion → Plane) ⁻¹' s
  have ht : t.Finite :=
    Set.Finite.preimage Subtype.val_injective.injOn hs
  have hpath : IsPathConnected tᶜ :=
    k.isPathConnected_compl_finite t ht
  have himage := hpath.image continuous_subtype_val
  convert himage using 1
  ext x
  simp [t]

namespace MoiseChart

variable {S : Type*} [TopologicalSpace S] (c : MoiseChart S)

/-- A Moise chart domain, as a subtype, remains path-connected after deleting finitely many
points. -/
theorem isPathConnected_compl_finite_subtype
    (s : Set c.domain) (hs : s.Finite) :
    IsPathConnected sᶜ := by
  let t : Set c.kind.modelRegion := c.chart.symm ⁻¹' s
  have ht : t.Finite :=
    Set.Finite.preimage c.chart.symm.injective.injOn hs
  have hmodel : IsPathConnected tᶜ :=
    c.kind.isPathConnected_compl_finite t ht
  have hpre : IsPathConnected (c.chart ⁻¹' tᶜ) :=
    c.chart.isPathConnected_preimage.mpr hmodel
  have heq : c.chart ⁻¹' t = s := by
    ext x
    simp [t]
  rw [preimage_compl, heq] at hpre
  exact hpre

/-- The ambient chart domain remains path-connected after deleting a finite subset of the
surface. -/
theorem isPathConnected_domain_diff_finite
    (s : Set S) (hs : s.Finite) :
    IsPathConnected (c.domain \ s) := by
  let t : Set c.domain := (Subtype.val : c.domain → S) ⁻¹' s
  have ht : t.Finite :=
    Set.Finite.preimage Subtype.val_injective.injOn hs
  have hpath : IsPathConnected tᶜ :=
    c.isPathConnected_compl_finite_subtype t ht
  have himage := hpath.image continuous_subtype_val
  convert himage using 1
  ext x
  simp [t]

end MoiseChart

/-- A connected T1 space stays connected after deleting a finite set if every deleted point has
an open neighborhood whose complement of the whole finite set is path-connected.

For a putative separation of the complement, each deleted point is assigned to the unique side
containing its punctured neighborhood.  Restoring the assigned points then produces two disjoint
open sets covering the original connected space. -/
theorem isConnected_compl_finite_of_locally_pathConnected
    {S : Type*} [TopologicalSpace S] [T1Space S] [ConnectedSpace S]
    {F : Set S} (hF : F.Finite)
    (hlocal : ∀ p ∈ F, ∃ U : Set S,
      IsOpen U ∧ p ∈ U ∧ IsPathConnected (U \ F)) :
    IsConnected Fᶜ := by
  classical
  by_cases hFempty : F = ∅
  · simpa [hFempty] using
      (isConnected_univ : IsConnected (Set.univ : Set S))
  have hcomplNonempty : Fᶜ.Nonempty := by
    obtain ⟨p, hpF⟩ := Set.nonempty_iff_ne_empty.mpr hFempty
    obtain ⟨U, _hUopen, _hpU, hpath⟩ := hlocal p hpF
    obtain ⟨x, _hxU, hxF⟩ := hpath.nonempty
    exact ⟨x, hxF⟩
  refine ⟨hcomplNonempty, ?_⟩
  intro u v hu hv hcover hUne hVne
  by_contra hinter
  let A : Set S := Fᶜ ∩ u
  let B : Set S := Fᶜ ∩ v
  have hAopen : IsOpen A := hF.isClosed.isOpen_compl.inter hu
  have hBopen : IsOpen B := hF.isClosed.isOpen_compl.inter hv
  have hABcover : Fᶜ ⊆ A ∪ B := by
    intro x hx
    rcases hcover hx with hxu | hxv
    · exact Or.inl ⟨hx, hxu⟩
    · exact Or.inr ⟨hx, hxv⟩
  have hABdisjoint : Disjoint A B := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    exact hinter ⟨x, hxA.1, hxA.2, hxB.2⟩
  choose U hUopen hpU hUpath using
    fun p : F ↦ hlocal p.1 p.2
  have hside (p : F) :
      U p \ F ⊆ A ∨ U p \ F ⊆ B := by
    obtain ⟨x, hx⟩ := (hUpath p).nonempty
    rcases hABcover hx.2 with hxA | hxB
    · left
      exact (hUpath p).isConnected.isPreconnected.subset_left_of_subset_union
        hAopen hBopen hABdisjoint
        (fun _ hy ↦ hABcover hy.2) ⟨x, hx, hxA⟩
    · right
      exact (hUpath p).isConnected.isPreconnected.subset_right_of_subset_union
        hAopen hBopen hABdisjoint
        (fun _ hy ↦ hABcover hy.2) ⟨x, hx, hxB⟩
  let Left (p : F) : Prop := U p \ F ⊆ A
  have hright (p : F) (hp : ¬Left p) :
      U p \ F ⊆ B :=
    (hside p).resolve_left hp
  let W (p : F) : Set S := U p \ (F \ {p.1})
  have hWopen (p : F) : IsOpen (W p) := by
    exact (hUopen p).inter (hF.sdiff |>.isClosed.isOpen_compl)
  have hpW (p : F) : p.1 ∈ W p := by
    refine ⟨hpU p, ?_⟩
    rintro ⟨_, hpne⟩
    exact hpne rfl
  have eq_center_of_mem_W_of_mem_F (p : F) {x : S}
      (hxW : x ∈ W p) (hxF : x ∈ F) :
      x = p.1 := by
    by_contra hxp
    apply hxW.2
    exact ⟨hxF, by simpa using hxp⟩
  let L : Set S := {x | ∃ p : F, Left p ∧ x = p.1}
  let R : Set S := {x | ∃ p : F, ¬Left p ∧ x = p.1}
  let A' : Set S := A ∪ L
  let B' : Set S := B ∪ R
  have hA'open : IsOpen A' := by
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    rcases hx with hxA | ⟨p, hpLeft, rfl⟩
    · exact ⟨A, Set.subset_union_left, hAopen, hxA⟩
    · refine ⟨W p, ?_, hWopen p, hpW p⟩
      intro y hyW
      by_cases hyF : y ∈ F
      · right
        exact ⟨p, hpLeft, eq_center_of_mem_W_of_mem_F p hyW hyF⟩
      · left
        exact hpLeft ⟨hyW.1, hyF⟩
  have hB'open : IsOpen B' := by
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    rcases hx with hxB | ⟨p, hpLeft, rfl⟩
    · exact ⟨B, Set.subset_union_left, hBopen, hxB⟩
    · refine ⟨W p, ?_, hWopen p, hpW p⟩
      intro y hyW
      by_cases hyF : y ∈ F
      · right
        exact ⟨p, hpLeft, eq_center_of_mem_W_of_mem_F p hyW hyF⟩
      · left
        exact hright p hpLeft ⟨hyW.1, hyF⟩
  have hA'B'disjoint : Disjoint A' B' := by
    rw [Set.disjoint_left]
    intro x hxA' hxB'
    rcases hxA' with hxA | ⟨p, hpLeft, hp⟩
    · rcases hxB' with hxB | ⟨q, _hqLeft, hq⟩
      · exact Set.disjoint_left.mp hABdisjoint hxA hxB
      · exact hxA.1 (hq ▸ q.2)
    · rcases hxB' with hxB | ⟨q, hqLeft, hq⟩
      · exact hxB.1 (hp ▸ p.2)
      · apply hqLeft
        have hpq : p = q := by
          apply Subtype.ext
          exact hp.symm.trans hq
        simpa [hpq] using hpLeft
  have hA'B'cover : (Set.univ : Set S) ⊆ A' ∪ B' := by
    intro x _
    by_cases hxF : x ∈ F
    · let p : F := ⟨x, hxF⟩
      by_cases hpLeft : Left p
      · exact Or.inl (Or.inr ⟨p, hpLeft, rfl⟩)
      · exact Or.inr (Or.inr ⟨p, hpLeft, rfl⟩)
    · rcases hABcover hxF with hxA | hxB
      · exact Or.inl (Or.inl hxA)
      · exact Or.inr (Or.inl hxB)
  have hA'ne : ((Set.univ : Set S) ∩ A').Nonempty := by
    obtain ⟨x, hxF, hxu⟩ := hUne
    exact ⟨x, Set.mem_univ x, Or.inl ⟨hxF, hxu⟩⟩
  have hB'ne : ((Set.univ : Set S) ∩ B').Nonempty := by
    obtain ⟨x, hxF, hxv⟩ := hVne
    exact ⟨x, Set.mem_univ x, Or.inl ⟨hxF, hxv⟩⟩
  obtain ⟨x, _, hxA', hxB'⟩ := isPreconnected_univ
    A' B' hA'open hB'open hA'B'cover hA'ne hB'ne
  exact Set.disjoint_left.mp hA'B'disjoint hxA' hxB'

/-- A connected surface charted on the Euclidean half-plane remains connected after deleting
finitely many points. -/
theorem isConnected_compl_finite_surface
    {S : Type*} [TopologicalSpace S] [T1Space S] [ConnectedSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    {F : Set S} (hF : F.Finite) :
    IsConnected Fᶜ := by
  apply isConnected_compl_finite_of_locally_pathConnected hF
  intro p hpF
  obtain ⟨c, _hfaithful, hcore⟩ :=
    exists_moiseChart_core_mem_nhds S p
  refine ⟨c.domain, c.isOpen_domain, ?_,
    c.isPathConnected_domain_diff_finite F hF⟩
  exact c.core_subset_domain (mem_of_mem_nhds hcore)

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
