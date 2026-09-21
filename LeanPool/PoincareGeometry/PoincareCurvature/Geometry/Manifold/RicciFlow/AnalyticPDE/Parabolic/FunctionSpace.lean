/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.ParabolicHolder
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.ContinuousMap.Compact
/-!
# Parabolic Holder function spaces

This module packages the parabolic `C^{0,α}` predicate as a linear function
space and gives the basic compact-piece readouts used by later Schauder and
Banach-chart constructions.  The norms and Schauder estimates are intentionally
not asserted here; this file only records the algebraic function-space layer
that follows from the existing Holder API.
-/

@[expose] public noncomputable section

open Set
open scoped Topology NNReal

namespace RicciFlow
namespace AnalyticPDE

/-- Product compact pieces in time-space, built from one compact time set and a spatial compact
family.  These are the canonical pieces used to restrict parabolic compact readouts to fixed-time
spatial readouts. -/
def timeSpaceProductCompactFamily {X κ : Type*} [TopologicalSpace X]
    (Kt : TopologicalSpace.Compacts ℝ) (Kx : κ → TopologicalSpace.Compacts X) :
    κ → TopologicalSpace.Compacts (ℝ × X) :=
  fun i => ⟨(Kt : Set ℝ) ×ˢ (Kx i : Set X), Kt.isCompact.prod (Kx i).isCompact⟩

@[simp]
theorem mem_timeSpaceProductCompactFamily {X κ : Type*} [TopologicalSpace X]
    (Kt : TopologicalSpace.Compacts ℝ) (Kx : κ → TopologicalSpace.Compacts X)
    {i : κ} {z : ℝ × X} :
    z ∈ (timeSpaceProductCompactFamily Kt Kx i : Set (ℝ × X)) ↔
      z.1 ∈ (Kt : Set ℝ) ∧ z.2 ∈ (Kx i : Set X) :=
  Iff.rfl

/-- Product compact pieces are contained in a time-space domain if every requested time and spatial
compact point is contained in that domain. -/
theorem timeSpaceProductCompactFamily_subset_of_forall_mem {X κ : Type*} [TopologicalSpace X]
    (Kt : TopologicalSpace.Compacts ℝ) (Kx : κ → TopologicalSpace.Compacts X)
    {s : Set (ℝ × X)}
    (h : ∀ τ, τ ∈ (Kt : Set ℝ) → ∀ i (x : Kx i), (τ, x.1) ∈ s) :
    ∀ i, (timeSpaceProductCompactFamily Kt Kx i : Set (ℝ × X)) ⊆ s := by
  intro i z hz
  exact h z.1 hz.1 i ⟨z.2, hz.2⟩

/-- The product compact family covers each spatial compact on every time in the chosen compact time
set. -/
theorem timeSpaceProductCompactFamily_covers_timeSlice {X κ : Type*} [TopologicalSpace X]
    (Kt : TopologicalSpace.Compacts ℝ) (Kx : κ → TopologicalSpace.Compacts X) :
    ∀ τ, τ ∈ (Kt : Set ℝ) → ∀ i (x : Kx i),
      ∃ j, (τ, x.1) ∈ (timeSpaceProductCompactFamily Kt Kx j : Set (ℝ × X)) := by
  intro τ hτ i x
  exact ⟨i, hτ, x.2⟩

/-- The union of product compact pieces is the product of the time compact with the union of the
spatial compact pieces. -/
theorem iUnion_timeSpaceProductCompactFamily_eq_prod_iUnion {X κ : Type*}
    [TopologicalSpace X]
    (Kt : TopologicalSpace.Compacts ℝ) (Kx : κ → TopologicalSpace.Compacts X) :
    (⋃ i, (timeSpaceProductCompactFamily Kt Kx i : Set (ℝ × X))) =
      (Kt : Set ℝ) ×ˢ (⋃ i, (Kx i : Set X)) := by
  ext z
  constructor
  · intro hz
    rcases mem_iUnion.1 hz with ⟨i, hzi⟩
    exact ⟨hzi.1, mem_iUnion.2 ⟨i, hzi.2⟩⟩
  · intro hz
    rcases mem_iUnion.1 hz.2 with ⟨i, hxi⟩
    exact mem_iUnion.2 ⟨i, hz.1, hxi⟩

/-- If a spatial set is covered by the spatial compact family, then the corresponding time-space
product is covered by the product compact family. -/
theorem timeSpaceProductCompactFamily_product_subset_iUnion_of_subset {X κ : Type*}
    [TopologicalSpace X]
    (Kt : TopologicalSpace.Compacts ℝ) (Kx : κ → TopologicalSpace.Compacts X)
    {U : Set X} (hU : U ⊆ ⋃ i, (Kx i : Set X)) :
    (Kt : Set ℝ) ×ˢ U ⊆
      ⋃ i, (timeSpaceProductCompactFamily Kt Kx i : Set (ℝ × X)) := by
  intro z hz
  rcases mem_iUnion.1 (hU hz.2) with ⟨i, hxi⟩
  exact mem_iUnion.2 ⟨i, hz.1, hxi⟩

/-- If the spatial compact family covers all space, then the product compact family covers the
whole product of the time compact with space. -/
theorem iUnion_timeSpaceProductCompactFamily_eq_prod_univ_of_iUnion_eq_univ {X κ : Type*}
    [TopologicalSpace X]
    (Kt : TopologicalSpace.Compacts ℝ) (Kx : κ → TopologicalSpace.Compacts X)
    (hcover : (⋃ i, (Kx i : Set X)) = Set.univ) :
    (⋃ i, (timeSpaceProductCompactFamily Kt Kx i : Set (ℝ × X))) =
      (Kt : Set ℝ) ×ˢ Set.univ := by
  rw [iUnion_timeSpaceProductCompactFamily_eq_prod_iUnion, hcover]

/-- The compact interval `[t₀, T]` as a compact time set. -/
def timeIccCompact (t₀ T : ℝ) : TopologicalSpace.Compacts ℝ :=
  ⟨Icc t₀ T, isCompact_Icc⟩

@[simp]
theorem mem_timeIccCompact {t₀ T τ : ℝ} :
    τ ∈ (timeIccCompact t₀ T : Set ℝ) ↔ τ ∈ Icc t₀ T :=
  Iff.rfl

/-- Product compact pieces over a closed time interval and a spatial compact family. -/
def timeSpaceIccCompactFamily {X κ : Type*} [TopologicalSpace X]
    (t₀ T : ℝ) (Kx : κ → TopologicalSpace.Compacts X) :
    κ → TopologicalSpace.Compacts (ℝ × X) :=
  timeSpaceProductCompactFamily (timeIccCompact t₀ T) Kx

@[simp]
theorem mem_timeSpaceIccCompactFamily {X κ : Type*} [TopologicalSpace X]
    (t₀ T : ℝ) (Kx : κ → TopologicalSpace.Compacts X)
    {i : κ} {z : ℝ × X} :
    z ∈ (timeSpaceIccCompactFamily t₀ T Kx i : Set (ℝ × X)) ↔
      z.1 ∈ Icc t₀ T ∧ z.2 ∈ (Kx i : Set X) :=
  Iff.rfl

/-- Interval product compact pieces are contained in a time-space domain if every interval time and
spatial compact point is contained in that domain. -/
theorem timeSpaceIccCompactFamily_subset_of_forall_mem {X κ : Type*} [TopologicalSpace X]
    (t₀ T : ℝ) (Kx : κ → TopologicalSpace.Compacts X)
    {s : Set (ℝ × X)}
    (h : ∀ τ, τ ∈ Icc t₀ T → ∀ i (x : Kx i), (τ, x.1) ∈ s) :
    ∀ i, (timeSpaceIccCompactFamily t₀ T Kx i : Set (ℝ × X)) ⊆ s := by
  exact timeSpaceProductCompactFamily_subset_of_forall_mem
    (timeIccCompact t₀ T) Kx h

/-- Interval product compact pieces cover each spatial compact on every time in the interval. -/
theorem timeSpaceIccCompactFamily_covers_timeSlice {X κ : Type*} [TopologicalSpace X]
    (t₀ T : ℝ) (Kx : κ → TopologicalSpace.Compacts X) :
    ∀ τ, τ ∈ Icc t₀ T → ∀ i (x : Kx i),
      ∃ j, (τ, x.1) ∈ (timeSpaceIccCompactFamily t₀ T Kx j : Set (ℝ × X)) := by
  exact timeSpaceProductCompactFamily_covers_timeSlice (timeIccCompact t₀ T) Kx

/-- The union of interval product compact pieces is the interval product of the union of the
spatial compact pieces. -/
theorem iUnion_timeSpaceIccCompactFamily_eq_Icc_prod_iUnion {X κ : Type*}
    [TopologicalSpace X]
    (t₀ T : ℝ) (Kx : κ → TopologicalSpace.Compacts X) :
    (⋃ i, (timeSpaceIccCompactFamily t₀ T Kx i : Set (ℝ × X))) =
      Icc t₀ T ×ˢ (⋃ i, (Kx i : Set X)) := by
  exact iUnion_timeSpaceProductCompactFamily_eq_prod_iUnion (timeIccCompact t₀ T) Kx

/-- If a spatial set is covered by the spatial compact family, then the corresponding closed
time-interval product is covered by the interval product compact family. -/
theorem timeSpaceIccCompactFamily_Icc_product_subset_iUnion_of_subset {X κ : Type*}
    [TopologicalSpace X]
    (t₀ T : ℝ) (Kx : κ → TopologicalSpace.Compacts X)
    {U : Set X} (hU : U ⊆ ⋃ i, (Kx i : Set X)) :
    Icc t₀ T ×ˢ U ⊆
      ⋃ i, (timeSpaceIccCompactFamily t₀ T Kx i : Set (ℝ × X)) := by
  exact timeSpaceProductCompactFamily_product_subset_iUnion_of_subset
    (timeIccCompact t₀ T) Kx hU

/-- If the spatial compact family covers all space, then the interval product compact family covers
the whole closed time-interval product. -/
theorem iUnion_timeSpaceIccCompactFamily_eq_Icc_prod_univ_of_iUnion_eq_univ {X κ : Type*}
    [TopologicalSpace X]
    (t₀ T : ℝ) (Kx : κ → TopologicalSpace.Compacts X)
    (hcover : (⋃ i, (Kx i : Set X)) = Set.univ) :
    (⋃ i, (timeSpaceIccCompactFamily t₀ T Kx i : Set (ℝ × X))) =
      Icc t₀ T ×ˢ Set.univ := by
  rw [iUnion_timeSpaceIccCompactFamily_eq_Icc_prod_iUnion, hcover]

/-- Single-radius parabolic `C^{0,α}` control.  The radius `N` dominates the sum of a sup
constant and a Holder constant.  This is the closed-ball predicate for the eventual
`C^{0,α}` norm, kept constructive so later estimates can choose explicit constants. -/
def ParabolicC0AlphaNormLe {X E : Type*} [PseudoMetricSpace X] [NormedAddCommGroup E]
    (N α : ℝ) (u : ℝ × X → E) (s : Set (ℝ × X)) : Prop :=
  ∃ B ≥ 0, ∃ H ≥ 0, B + H ≤ N ∧ ParabolicC0AlphaWith B H α u s

namespace ParabolicC0AlphaNormLe

variable {X E : Type*} [PseudoMetricSpace X] [NormedAddCommGroup E]
variable {N N₁ N₂ α : ℝ} {u v : ℝ × X → E} {s t : Set (ℝ × X)}

theorem nonneg (h : ParabolicC0AlphaNormLe N α u s) : 0 ≤ N := by
  rcases h with ⟨B, hB, H, hH, hBH, _⟩
  exact (add_nonneg hB hH).trans hBH

theorem c0AlphaOn (h : ParabolicC0AlphaNormLe N α u s) :
    ParabolicC0AlphaOn α u s := by
  rcases h with ⟨B, hB, H, hH, _, hBH⟩
  exact ⟨B, hB, H, hH, hBH⟩

theorem c0AlphaWith_self (h : ParabolicC0AlphaNormLe N α u s) :
    ParabolicC0AlphaWith N N α u s := by
  rcases h with ⟨B, hB, H, hH, hsum, hBH⟩
  have hB_le : B ≤ N := by linarith
  have hH_le : H ≤ N := by linarith
  exact hBH.mono_const hB_le hH_le

theorem holder (h : ParabolicC0AlphaNormLe N α u s) :
    ParabolicHolderWith N α u s :=
  h.c0AlphaWith_self.holder

theorem congr (h : ParabolicC0AlphaNormLe N α u s) (huv : EqOn v u s) :
    ParabolicC0AlphaNormLe N α v s := by
  rcases h with ⟨B, hB, H, hH, hsum, hBH⟩
  refine ⟨B, hB, H, hH, hsum, ?_⟩
  exact ⟨
    (fun {_p} hp => by
      simpa [huv hp] using hBH.bounded hp),
    (fun {_p} hp {_q} hq => by
      simpa [huv hp, huv hq] using hBH.holder hp hq)⟩

/-- The single radius controls the pointwise norm on the domain. -/
theorem norm_le (h : ParabolicC0AlphaNormLe N α u s) ⦃z : ℝ × X⦄ (hz : z ∈ s) :
    ‖u z‖ ≤ N := by
  rcases h with ⟨B, hB, H, hH, hsum, hBH⟩
  have hB_le : B ≤ N := by linarith
  exact (hBH.bounded hz).trans hB_le

/-- A single-radius parabolic `C^{0,α}` bound gives the corresponding time-slice Holder
estimate with the parabolic half exponent. -/
theorem time_slice_half_exponent (h : ParabolicC0AlphaNormLe N α u s)
    {t τ : ℝ} {x : X} (ht : (t, x) ∈ s) (hτ : (τ, x) ∈ s) :
    ‖u (t, x) - u (τ, x)‖ ≤ N * |t - τ| ^ (α / 2) :=
  h.holder.time_slice_half_exponent ht hτ

/-- A single-radius parabolic `C^{0,α}` bound restricts to ordinary spatial Holder control on
each fixed-time slice. -/
theorem space_slice (h : ParabolicC0AlphaNormLe N α u s)
    {t : ℝ} {x y : X} (hx : (t, x) ∈ s) (hy : (t, y) ∈ s) :
    ‖u (t, x) - u (t, y)‖ ≤ N * (dist x y) ^ α :=
  h.holder.space_slice hx hy

/-- Product-domain pointwise readout of a single-radius parabolic `C^{0,α}` bound. -/
theorem norm_le_of_prod_subset (h : ParabolicC0AlphaNormLe N α u s)
    {timeSet : Set ℝ} {spaceSet : Set X} (hst : timeSet ×ˢ spaceSet ⊆ s)
    {t : ℝ} (ht : t ∈ timeSet) {x : X} (hx : x ∈ spaceSet) :
    ‖u (t, x)‖ ≤ N :=
  h.norm_le (hst ⟨ht, hx⟩)

/-- Product-domain time-slice readout of a single-radius parabolic `C^{0,α}` bound. -/
theorem time_slice_half_exponent_of_prod_subset (h : ParabolicC0AlphaNormLe N α u s)
    {timeSet : Set ℝ} {spaceSet : Set X} (hst : timeSet ×ˢ spaceSet ⊆ s)
    {t τ : ℝ} (ht : t ∈ timeSet) (hτ : τ ∈ timeSet)
    {x : X} (hx : x ∈ spaceSet) :
    ‖u (t, x) - u (τ, x)‖ ≤ N * |t - τ| ^ (α / 2) :=
  h.time_slice_half_exponent (hst ⟨ht, hx⟩) (hst ⟨hτ, hx⟩)

/-- Product-domain fixed-time spatial Holder readout of a single-radius parabolic `C^{0,α}`
bound. -/
theorem space_slice_of_prod_subset (h : ParabolicC0AlphaNormLe N α u s)
    {timeSet : Set ℝ} {spaceSet : Set X} (hst : timeSet ×ˢ spaceSet ⊆ s)
    {t : ℝ} (ht : t ∈ timeSet) {x y : X} (hx : x ∈ spaceSet) (hy : y ∈ spaceSet) :
    ‖u (t, x) - u (t, y)‖ ≤ N * (dist x y) ^ α :=
  h.space_slice (hst ⟨ht, hx⟩) (hst ⟨ht, hy⟩)

/-- A single-radius bound on a difference gives the corresponding pointwise distance bound. -/
theorem dist_le_of_sub (h : ParabolicC0AlphaNormLe N α (fun z => u z - v z) s)
    ⦃z : ℝ × X⦄ (hz : z ∈ s) :
    dist (u z) (v z) ≤ N := by
  simpa [dist_eq_norm] using h.norm_le hz

/-- A single-radius bound on a difference puts each value in the closed ball
around the corresponding comparison value. -/
theorem mem_closedBall_of_sub (h : ParabolicC0AlphaNormLe N α (fun z => u z - v z) s)
    ⦃z : ℝ × X⦄ (hz : z ∈ s) :
    u z ∈ Metric.closedBall (v z) N := by
  simpa [Metric.mem_closedBall] using h.dist_le_of_sub hz

/-- Symmetric closed-ball readout from a single-radius difference bound. -/
theorem mem_closedBall_symm_of_sub
    (h : ParabolicC0AlphaNormLe N α (fun z => u z - v z) s)
    ⦃z : ℝ × X⦄ (hz : z ∈ s) :
    v z ∈ Metric.closedBall (u z) N := by
  simpa [Metric.mem_closedBall, dist_comm] using h.dist_le_of_sub hz

/-- Product-domain pointwise distance readout of a single-radius difference
bound. -/
theorem dist_le_of_sub_prod_subset
    (h : ParabolicC0AlphaNormLe N α (fun z => u z - v z) s)
    {timeSet : Set ℝ} {spaceSet : Set X} (hst : timeSet ×ˢ spaceSet ⊆ s)
    {t : ℝ} (ht : t ∈ timeSet) {x : X} (hx : x ∈ spaceSet) :
    dist (u (t, x)) (v (t, x)) ≤ N :=
  h.dist_le_of_sub (hst ⟨ht, hx⟩)

/-- Product-domain closed-ball readout of a single-radius difference bound. -/
theorem mem_closedBall_of_sub_prod_subset
    (h : ParabolicC0AlphaNormLe N α (fun z => u z - v z) s)
    {timeSet : Set ℝ} {spaceSet : Set X} (hst : timeSet ×ˢ spaceSet ⊆ s)
    {t : ℝ} (ht : t ∈ timeSet) {x : X} (hx : x ∈ spaceSet) :
    u (t, x) ∈ Metric.closedBall (v (t, x)) N :=
  h.mem_closedBall_of_sub (hst ⟨ht, hx⟩)

/-- Componentwise `C^{0,α}` difference controls with radii linear in a shared scalar give a
pointwise finite-Pi norm difference bound with the summed component radius. -/
theorem pi_norm_sub_le_sum_mul_of_entries {ι F : Type*} [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {R : ℝ} {K : ι → ℝ} {u v : ℝ × X → ι → F}
    (hK : ∀ i, 0 ≤ K i) (hR : 0 ≤ R)
    (h : ∀ i, ParabolicC0AlphaNormLe (K i * R) α
      (fun z => u z i - v z i) s)
    ⦃z : ℝ × X⦄ (hz : z ∈ s) :
    ‖u z - v z‖ ≤ (∑ i, K i) * R := by
  have hsum_nonneg : 0 ≤ ∑ i, K i :=
    Finset.sum_nonneg fun i _hi => hK i
  have htarget_nonneg : 0 ≤ (∑ i, K i) * R :=
    mul_nonneg hsum_nonneg hR
  refine (pi_norm_le_iff_of_nonneg htarget_nonneg).2 fun i => ?_
  have hentry : ‖u z i - v z i‖ ≤ K i * R := by
    simpa [dist_eq_norm] using (h i).dist_le_of_sub hz
  have hentry_le_sum : K i ≤ ∑ i, K i :=
    Finset.single_le_sum (fun i' _hi' => hK i') (Finset.mem_univ i)
  exact (by
    simpa [Pi.sub_apply] using hentry.trans (mul_le_mul_of_nonneg_right hentry_le_sum hR))

/-- Componentwise `C^{0,α}` difference controls with radii linear in a shared scalar give a
pointwise finite-Pi distance bound with the summed component radius. -/
theorem pi_dist_le_sum_mul_of_entries {ι F : Type*} [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {R : ℝ} {K : ι → ℝ} {u v : ℝ × X → ι → F}
    (hK : ∀ i, 0 ≤ K i) (hR : 0 ≤ R)
    (h : ∀ i, ParabolicC0AlphaNormLe (K i * R) α
      (fun z => u z i - v z i) s)
    ⦃z : ℝ × X⦄ (hz : z ∈ s) :
    dist (u z) (v z) ≤ (∑ i, K i) * R := by
  simpa [dist_eq_norm] using
    pi_norm_sub_le_sum_mul_of_entries
      (X := X) (α := α) (s := s) hK hR h hz

/-- Product-domain finite-Pi distance bound from componentwise `C^{0,α}` difference
controls with radii linear in a shared scalar. -/
theorem pi_dist_le_sum_mul_of_entries_prod_subset {ι F : Type*} [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {R : ℝ} {K : ι → ℝ} {u v : ℝ × X → ι → F}
    (hK : ∀ i, 0 ≤ K i) (hR : 0 ≤ R)
    (h : ∀ i, ParabolicC0AlphaNormLe (K i * R) α
      (fun z => u z i - v z i) s)
    {timeSet : Set ℝ} {spaceSet : Set X} (hst : timeSet ×ˢ spaceSet ⊆ s)
    {t : ℝ} (ht : t ∈ timeSet) {x : X} (hx : x ∈ spaceSet) :
    dist (u (t, x)) (v (t, x)) ≤ (∑ i, K i) * R :=
  pi_dist_le_sum_mul_of_entries
    (X := X) (α := α) (s := s) hK hR h (hst ⟨ht, hx⟩)

/-- Componentwise `C^{0,α}` difference controls with radii linear in a shared
scalar give a finite-Pi closed-ball membership bound. -/
theorem pi_mem_closedBall_sum_mul_of_entries {ι F : Type*} [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {R : ℝ} {K : ι → ℝ} {u v : ℝ × X → ι → F}
    (hK : ∀ i, 0 ≤ K i) (hR : 0 ≤ R)
    (h : ∀ i, ParabolicC0AlphaNormLe (K i * R) α
      (fun z => u z i - v z i) s)
    ⦃z : ℝ × X⦄ (hz : z ∈ s) :
    u z ∈ Metric.closedBall (v z) ((∑ i, K i) * R) := by
  simpa [Metric.mem_closedBall] using
    pi_dist_le_sum_mul_of_entries
      (X := X) (α := α) (s := s) hK hR h hz

/-- Componentwise `C^{0,α}` difference controls with radii linear in a shared
scalar give the symmetric finite-Pi closed-ball membership bound. -/
theorem pi_mem_closedBall_symm_sum_mul_of_entries {ι F : Type*} [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {R : ℝ} {K : ι → ℝ} {u v : ℝ × X → ι → F}
    (hK : ∀ i, 0 ≤ K i) (hR : 0 ≤ R)
    (h : ∀ i, ParabolicC0AlphaNormLe (K i * R) α
      (fun z => u z i - v z i) s)
    ⦃z : ℝ × X⦄ (hz : z ∈ s) :
    v z ∈ Metric.closedBall (u z) ((∑ i, K i) * R) := by
  simpa [Metric.mem_closedBall, dist_comm] using
    pi_dist_le_sum_mul_of_entries
      (X := X) (α := α) (s := s) hK hR h hz

/-- Product-domain finite-Pi closed-ball membership bound from componentwise
`C^{0,α}` difference controls. -/
theorem pi_mem_closedBall_sum_mul_of_entries_prod_subset {ι F : Type*} [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {R : ℝ} {K : ι → ℝ} {u v : ℝ × X → ι → F}
    (hK : ∀ i, 0 ≤ K i) (hR : 0 ≤ R)
    (h : ∀ i, ParabolicC0AlphaNormLe (K i * R) α
      (fun z => u z i - v z i) s)
    {timeSet : Set ℝ} {spaceSet : Set X} (hst : timeSet ×ˢ spaceSet ⊆ s)
    {t : ℝ} (ht : t ∈ timeSet) {x : X} (hx : x ∈ spaceSet) :
    u (t, x) ∈ Metric.closedBall (v (t, x)) ((∑ i, K i) * R) :=
  pi_mem_closedBall_sum_mul_of_entries
    (X := X) (α := α) (s := s) hK hR h (hst ⟨ht, hx⟩)

/-- Product-domain symmetric finite-Pi closed-ball membership bound from componentwise
`C^{0,α}` difference controls. -/
theorem pi_mem_closedBall_symm_sum_mul_of_entries_prod_subset {ι F : Type*} [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {R : ℝ} {K : ι → ℝ} {u v : ℝ × X → ι → F}
    (hK : ∀ i, 0 ≤ K i) (hR : 0 ≤ R)
    (h : ∀ i, ParabolicC0AlphaNormLe (K i * R) α
      (fun z => u z i - v z i) s)
    {timeSet : Set ℝ} {spaceSet : Set X} (hst : timeSet ×ˢ spaceSet ⊆ s)
    {t : ℝ} (ht : t ∈ timeSet) {x : X} (hx : x ∈ spaceSet) :
    v (t, x) ∈ Metric.closedBall (u (t, x)) ((∑ i, K i) * R) :=
  pi_mem_closedBall_symm_sum_mul_of_entries
    (X := X) (α := α) (s := s) hK hR h (hst ⟨ht, hx⟩)

theorem of_c0AlphaWith {B H : ℝ} (hB : 0 ≤ B) (hH : 0 ≤ H)
    (h : ParabolicC0AlphaWith B H α u s) :
    ParabolicC0AlphaNormLe (B + H) α u s :=
  ⟨B, hB, H, hH, le_rfl, h⟩

theorem exists_of_c0AlphaOn (h : ParabolicC0AlphaOn α u s) :
    ∃ N ≥ 0, ParabolicC0AlphaNormLe N α u s := by
  rcases h with ⟨B, hB, H, hH, hBH⟩
  exact ⟨B + H, add_nonneg hB hH, of_c0AlphaWith hB hH hBH⟩

theorem mono_const (h : ParabolicC0AlphaNormLe N₁ α u s) (hNN : N₁ ≤ N₂) :
    ParabolicC0AlphaNormLe N₂ α u s := by
  rcases h with ⟨B, hB, H, hH, hsum, hBH⟩
  exact ⟨B, hB, H, hH, hsum.trans hNN, hBH⟩

theorem mono_set (h : ParabolicC0AlphaNormLe N α u s) (hst : t ⊆ s) :
    ParabolicC0AlphaNormLe N α u t := by
  rcases h with ⟨B, hB, H, hH, hsum, hBH⟩
  exact ⟨B, hB, H, hH, hsum, hBH.mono_set hst⟩

theorem zero :
    ParabolicC0AlphaNormLe 0 α (fun _ : ℝ × X => (0 : E)) s := by
  refine ⟨0, le_rfl, 0, le_rfl, by simp, ?_⟩
  simpa using
    (ParabolicC0AlphaWith.const (X := X) (E := E) (α := α) (s := s) (0 : E)
      (by simp) le_rfl)

theorem const (c : E) :
    ParabolicC0AlphaNormLe ‖c‖ α (fun _ : ℝ × X => c) s := by
  refine ⟨‖c‖, norm_nonneg c, 0, le_rfl, by simp, ?_⟩
  exact ParabolicC0AlphaWith.const (X := X) (α := α) (s := s) c le_rfl le_rfl

theorem add (hu : ParabolicC0AlphaNormLe N₁ α u s)
    (hv : ParabolicC0AlphaNormLe N₂ α v s) :
    ParabolicC0AlphaNormLe (N₁ + N₂) α (fun z => u z + v z) s := by
  rcases hu with ⟨Bu, hBu, Hu, hHu, hu_sum, hu_ctrl⟩
  rcases hv with ⟨Bv, hBv, Hv, hHv, hv_sum, hv_ctrl⟩
  refine ⟨Bu + Bv, add_nonneg hBu hBv, Hu + Hv, add_nonneg hHu hHv, ?_,
    hu_ctrl.add hv_ctrl⟩
  linarith

theorem finset_sum {ι : Type*} (S : Finset ι) {N : ι → ℝ}
    {u : ι → ℝ × X → E}
    (h : ∀ i ∈ S, ParabolicC0AlphaNormLe (N i) α (u i) s) :
    ParabolicC0AlphaNormLe (∑ i ∈ S, N i) α
      (fun z => ∑ i ∈ S, u i z) s := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simpa using (zero (X := X) (E := E) (α := α) (s := s))
  | insert a S ha ih =>
      have ha_ctrl : ParabolicC0AlphaNormLe (N a) α (u a) s := h a (by simp)
      have hS_ctrl : ParabolicC0AlphaNormLe (∑ i ∈ S, N i) α
          (fun z => ∑ i ∈ S, u i z) s := by
        exact ih fun i hi => h i (by simp [hi])
      have hadd := add ha_ctrl hS_ctrl
      simpa [Finset.sum_insert, ha] using hadd

theorem neg (hu : ParabolicC0AlphaNormLe N α u s) :
    ParabolicC0AlphaNormLe N α (fun z => -u z) s := by
  rcases hu with ⟨B, hB, H, hH, hsum, hctrl⟩
  exact ⟨B, hB, H, hH, hsum, hctrl.neg⟩

theorem sub (hu : ParabolicC0AlphaNormLe N₁ α u s)
    (hv : ParabolicC0AlphaNormLe N₂ α v s) :
    ParabolicC0AlphaNormLe (N₁ + N₂) α (fun z => u z - v z) s := by
  rcases hu with ⟨Bu, hBu, Hu, hHu, hu_sum, hu_ctrl⟩
  rcases hv with ⟨Bv, hBv, Hv, hHv, hv_sum, hv_ctrl⟩
  refine ⟨Bu + Bv, add_nonneg hBu hBv, Hu + Hv, add_nonneg hHu hHv, ?_,
    hu_ctrl.sub hv_ctrl⟩
  linarith

theorem norm (hu : ParabolicC0AlphaNormLe N α u s) :
    ParabolicC0AlphaNormLe N α (fun z => ‖u z‖) s := by
  rcases hu with ⟨B, hB, H, hH, hsum, hctrl⟩
  exact ⟨B, hB, H, hH, hsum, hctrl.norm⟩

theorem smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
    (c : 𝕜) (hu : ParabolicC0AlphaNormLe N α u s) :
    ParabolicC0AlphaNormLe (‖c‖ * N) α (fun z => c • u z) s := by
  rcases hu with ⟨B, hB, H, hH, hsum, hctrl⟩
  refine ⟨‖c‖ * B, mul_nonneg (norm_nonneg c) hB,
    ‖c‖ * H, mul_nonneg (norm_nonneg c) hH, ?_, hctrl.smul c⟩
  calc
    ‖c‖ * B + ‖c‖ * H = ‖c‖ * (B + H) := by ring
    _ ≤ ‖c‖ * N := mul_le_mul_of_nonneg_left hsum (norm_nonneg c)

theorem continuousLinearMap {F : Type*} [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (hu : ParabolicC0AlphaNormLe N α u s) :
    ParabolicC0AlphaNormLe (‖L‖ * N) α (fun z => L (u z)) s := by
  rcases hu with ⟨B, hB, H, hH, hsum, hctrl⟩
  refine ⟨‖L‖ * B, mul_nonneg (norm_nonneg L) hB,
    ‖L‖ * H, mul_nonneg (norm_nonneg L) hH, ?_, hctrl.continuousLinearMap L⟩
  calc
    ‖L‖ * B + ‖L‖ * H = ‖L‖ * (B + H) := by ring
    _ ≤ ‖L‖ * N := mul_le_mul_of_nonneg_left hsum (norm_nonneg L)

theorem linearIsometryEquiv {F : Type*} [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E ≃ₗᵢ[ℝ] F) (hu : ParabolicC0AlphaNormLe N α u s) :
    ParabolicC0AlphaNormLe N α (fun z => L (u z)) s := by
  rcases hu with ⟨B, hB, H, hH, hsum, hctrl⟩
  refine ⟨B, hB, H, hH, hsum, ?_⟩
  constructor
  · intro p hp
    simpa [L.norm_map] using hctrl.1 hp
  · intro p hp q hq
    calc
      ‖L (u p) - L (u q)‖ = ‖L (u p - u q)‖ := by
        rw [map_sub]
      _ = ‖u p - u q‖ := L.norm_map (u p - u q)
      _ ≤ H * (parabolicDistance p q) ^ α := hctrl.2 hp hq

theorem pi {ι F : Type*} [Fintype ι] [NormedAddCommGroup F]
    {N : ι → ℝ} {u : ℝ × X → ι → F}
    (h : ∀ i, ParabolicC0AlphaNormLe (N i) α (fun z => u z i) s) :
    ParabolicC0AlphaNormLe (∑ i, N i) α u s := by
  classical
  choose B hB H hH hsum hctrl using h
  refine ⟨∑ i, B i, Finset.sum_nonneg fun i _ => hB i,
    ∑ i, H i, Finset.sum_nonneg fun i _ => hH i, ?_,
    ParabolicC0AlphaWith.pi (X := X) (E := F) (α := α) (s := s)
      (B := B) (H := H) hB hH hctrl⟩
  calc
    (∑ i, B i) + ∑ i, H i = ∑ i, (B i + H i) := by
      rw [Finset.sum_add_distrib]
    _ ≤ ∑ i, N i := Finset.sum_le_sum fun i _ => hsum i

theorem prod {F : Type*} [NormedAddCommGroup F] {v : ℝ × X → F}
    (hu : ParabolicC0AlphaNormLe N₁ α u s)
    (hv : ParabolicC0AlphaNormLe N₂ α v s) :
    ParabolicC0AlphaNormLe (N₁ + N₂) α (fun z => (u z, v z)) s := by
  rcases hu with ⟨Bu, hBu, Hu, hHu, hu_sum, hu_ctrl⟩
  rcases hv with ⟨Bv, hBv, Hv, hHv, hv_sum, hv_ctrl⟩
  refine ⟨max Bu Bv, hBu.trans (le_max_left Bu Bv),
    max Hu Hv, hHu.trans (le_max_left Hu Hv), ?_, hu_ctrl.prod hv_ctrl⟩
  have hBmax : max Bu Bv ≤ Bu + Bv := by
    exact max_le (le_add_of_nonneg_right hBv) (le_add_of_nonneg_left hBu)
  have hHmax : max Hu Hv ≤ Hu + Hv := by
    exact max_le (le_add_of_nonneg_right hHv) (le_add_of_nonneg_left hHu)
  linarith

theorem mul {A : Type*} [NormedRing A] {N₁ N₂ α : ℝ}
    {u v : ℝ × X → A} {s : Set (ℝ × X)}
    (hu : ParabolicC0AlphaNormLe N₁ α u s)
    (hv : ParabolicC0AlphaNormLe N₂ α v s) :
    ParabolicC0AlphaNormLe (N₁ * N₂) α (fun z => u z * v z) s := by
  rcases hu with ⟨Bu, hBu, Hu, hHu, hu_sum, hu_ctrl⟩
  rcases hv with ⟨Bv, hBv, Hv, hHv, hv_sum, hv_ctrl⟩
  have hNu : 0 ≤ N₁ := (add_nonneg hBu hHu).trans hu_sum
  refine ⟨Bu * Bv, mul_nonneg hBu hBv, Bu * Hv + Bv * Hu,
    add_nonneg (mul_nonneg hBu hHv) (mul_nonneg hBv hHu), ?_,
    hu_ctrl.mul hv_ctrl hBu⟩
  have hleft :
      Bu * Bv + (Bu * Hv + Bv * Hu) ≤ (Bu + Hu) * (Bv + Hv) := by
    nlinarith [mul_nonneg hHu hHv]
  have hright : (Bu + Hu) * (Bv + Hv) ≤ N₁ * N₂ :=
    mul_le_mul hu_sum hv_sum (add_nonneg hBv hHv) hNu
  exact hleft.trans hright

theorem smul_fun {𝕜 F : Type*} [NormedField 𝕜] [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {N₁ N₂ α : ℝ}
    {a : ℝ × X → 𝕜} {u : ℝ × X → F} {s : Set (ℝ × X)}
    (ha : ParabolicC0AlphaNormLe N₁ α a s)
    (hu : ParabolicC0AlphaNormLe N₂ α u s) :
    ParabolicC0AlphaNormLe (N₁ * N₂) α (fun z => a z • u z) s := by
  rcases ha with ⟨Ba, hBa, Ha, hHa, ha_sum, ha_ctrl⟩
  rcases hu with ⟨Bu, hBu, Hu, hHu, hu_sum, hu_ctrl⟩
  have hNa : 0 ≤ N₁ := (add_nonneg hBa hHa).trans ha_sum
  refine ⟨Ba * Bu, mul_nonneg hBa hBu, Ba * Hu + Bu * Ha,
    add_nonneg (mul_nonneg hBa hHu) (mul_nonneg hBu hHa), ?_,
    ha_ctrl.smul_fun hu_ctrl hBa⟩
  have hleft : Ba * Bu + (Ba * Hu + Bu * Ha) ≤ (Ba + Ha) * (Bu + Hu) := by
    nlinarith [mul_nonneg hHa hHu]
  have hright : (Ba + Ha) * (Bu + Hu) ≤ N₁ * N₂ :=
    mul_le_mul ha_sum hu_sum (add_nonneg hBu hHu) hNa
  exact hleft.trans hright

theorem mul_sub_mul {A : Type*} [NormedRing A]
    {Nu Nv Ndu Ndv α : ℝ} {u u' v v' : ℝ × X → A} {s : Set (ℝ × X)}
    (hu : ParabolicC0AlphaNormLe Nu α u s)
    (hv' : ParabolicC0AlphaNormLe Nv α v' s)
    (hdu : ParabolicC0AlphaNormLe Ndu α (fun z => u z - u' z) s)
    (hdv : ParabolicC0AlphaNormLe Ndv α (fun z => v z - v' z) s) :
    ParabolicC0AlphaNormLe (Nu * Ndv + Ndu * Nv) α
      (fun z => u z * v z - u' z * v' z) s := by
  rcases hu with ⟨Bu, hBu, Hu, hHu, hu_sum, hu_ctrl⟩
  rcases hv' with ⟨Bv, hBv, Hv, hHv, hv_sum, hv_ctrl⟩
  rcases hdu with ⟨Bdu, hBdu, Hdu, hHdu, hdu_sum, hdu_ctrl⟩
  rcases hdv with ⟨Bdv, hBdv, Hdv, hHdv, hdv_sum, hdv_ctrl⟩
  refine ⟨Bu * Bdv + Bdu * Bv,
    add_nonneg (mul_nonneg hBu hBdv) (mul_nonneg hBdu hBv),
    (Bu * Hdv + Bdv * Hu) + (Bdu * Hv + Bv * Hdu), ?_, ?_,
    hu_ctrl.mul_sub_mul hv_ctrl hdu_ctrl hdv_ctrl hBu hBdu⟩
  · exact add_nonneg
      (add_nonneg (mul_nonneg hBu hHdv) (mul_nonneg hBdv hHu))
      (add_nonneg (mul_nonneg hBdu hHv) (mul_nonneg hBv hHdu))
  · have hNu : 0 ≤ Nu := (add_nonneg hBu hHu).trans hu_sum
    have hNdu : 0 ≤ Ndu := (add_nonneg hBdu hHdu).trans hdu_sum
    have hleft :
        (Bu * Bdv + Bdu * Bv) +
            ((Bu * Hdv + Bdv * Hu) + (Bdu * Hv + Bv * Hdu)) ≤
          (Bu + Hu) * (Bdv + Hdv) + (Bdu + Hdu) * (Bv + Hv) := by
      nlinarith [mul_nonneg hHu hHdv, mul_nonneg hHdu hHv]
    have hright₁ : (Bu + Hu) * (Bdv + Hdv) ≤ Nu * Ndv :=
      mul_le_mul hu_sum hdv_sum (add_nonneg hBdv hHdv) hNu
    have hright₂ : (Bdu + Hdu) * (Bv + Hv) ≤ Ndu * Nv :=
      mul_le_mul hdu_sum hv_sum (add_nonneg hBv hHv) hNdu
    linarith

theorem inv {𝕜 : Type*} [NormedField 𝕜] {a : ℝ × X → 𝕜} {δ N α : ℝ}
    {s : Set (ℝ × X)}
    (ha : ParabolicC0AlphaNormLe N α a s) (hδpos : 0 < δ)
    (hδ : ∀ ⦃p : ℝ × X⦄, p ∈ s → δ ≤ ‖a p‖) :
    ParabolicC0AlphaNormLe (δ⁻¹ + δ⁻¹ * N * δ⁻¹) α (fun z => (a z)⁻¹) s := by
  rcases ha with ⟨B, hB, H, hH, hsum, hctrl⟩
  have hδnn : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδpos.le
  refine ⟨δ⁻¹, hδnn, δ⁻¹ * H * δ⁻¹,
    mul_nonneg (mul_nonneg hδnn hH) hδnn, ?_, hctrl.inv hδpos hδ⟩
  have hH_le_N : H ≤ N := by linarith
  have hholder_le : δ⁻¹ * H * δ⁻¹ ≤ δ⁻¹ * N * δ⁻¹ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hH_le_N hδnn) hδnn
  linarith

theorem inv_sub_inv {𝕜 : Type*} [NormedField 𝕜]
    {a b : ℝ × X → 𝕜} {Na Nb Nd δ α : ℝ} {s : Set (ℝ × X)}
    (ha : ParabolicC0AlphaNormLe Na α a s)
    (hb : ParabolicC0AlphaNormLe Nb α b s)
    (hdiff : ParabolicC0AlphaNormLe Nd α (fun z => a z - b z) s)
    (hδpos : 0 < δ)
    (hδa : ∀ ⦃p : ℝ × X⦄, p ∈ s → δ ≤ ‖a p‖)
    (hδb : ∀ ⦃p : ℝ × X⦄, p ∈ s → δ ≤ ‖b p‖) :
    ParabolicC0AlphaNormLe
      (ParabolicC0AlphaWith.invSubBoundConst δ Nd +
        ParabolicC0AlphaWith.invSubHolderConst δ Na Nb Nd Nd)
      α (fun z => (a z)⁻¹ - (b z)⁻¹) s := by
  rcases ha with ⟨Ba, hBa, Ha, hHa, ha_sum, ha_ctrl⟩
  rcases hb with ⟨Bb, hBb, Hb, hHb, hb_sum, hb_ctrl⟩
  rcases hdiff with ⟨Bd, hBd, Hd, hHd, hdiff_sum, hdiff_ctrl⟩
  have hδnn : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδpos.le
  have hNa : 0 ≤ Na := (add_nonneg hBa hHa).trans ha_sum
  have hNb : 0 ≤ Nb := (add_nonneg hBb hHb).trans hb_sum
  have hNd : 0 ≤ Nd := (add_nonneg hBd hHd).trans hdiff_sum
  have hHa_le : Ha ≤ Na := by linarith
  have hHb_le : Hb ≤ Nb := by linarith
  have hBd_le : Bd ≤ Nd := by linarith
  have hHd_le : Hd ≤ Nd := by linarith
  have hBterm :
      (δ⁻¹ * Bd) * δ⁻¹ ≤ (δ⁻¹ * Nd) * δ⁻¹ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBd_le hδnn) hδnn
  have hHb_factor :
      δ⁻¹ * Hb * δ⁻¹ ≤ δ⁻¹ * Nb * δ⁻¹ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hHb_le hδnn) hδnn
  have hHterm₁ :
      (δ⁻¹ * Bd) * (δ⁻¹ * Hb * δ⁻¹) ≤
        (δ⁻¹ * Nd) * (δ⁻¹ * Nb * δ⁻¹) := by
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hBd_le hδnn) hHb_factor
      (mul_nonneg (mul_nonneg hδnn hHb) hδnn) (mul_nonneg hδnn hNd)
  have hHd_factor : δ⁻¹ * Hd ≤ δ⁻¹ * Nd :=
    mul_le_mul_of_nonneg_left hHd_le hδnn
  have hHa_factor :
      δ⁻¹ * Ha * δ⁻¹ ≤ δ⁻¹ * Na * δ⁻¹ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hHa_le hδnn) hδnn
  have hHterm₂_inner :
      δ⁻¹ * Hd + Bd * (δ⁻¹ * Ha * δ⁻¹) ≤
        δ⁻¹ * Nd + Nd * (δ⁻¹ * Na * δ⁻¹) := by
    refine add_le_add hHd_factor ?_
    exact mul_le_mul hBd_le hHa_factor
      (mul_nonneg (mul_nonneg hδnn hHa) hδnn) hNd
  have hHterm₂ :
      δ⁻¹ * (δ⁻¹ * Hd + Bd * (δ⁻¹ * Ha * δ⁻¹)) ≤
        δ⁻¹ * (δ⁻¹ * Nd + Nd * (δ⁻¹ * Na * δ⁻¹)) :=
    mul_le_mul_of_nonneg_left hHterm₂_inner hδnn
  refine ⟨ParabolicC0AlphaWith.invSubBoundConst δ Bd,
    ParabolicC0AlphaWith.invSubBoundConst_nonneg hδpos hBd,
    ParabolicC0AlphaWith.invSubHolderConst δ Ha Hb Bd Hd,
    ParabolicC0AlphaWith.invSubHolderConst_nonneg hδpos hHa hHb hBd hHd, ?_,
    ha_ctrl.inv_sub_inv hb_ctrl hdiff_ctrl hδpos hδa hδb hBd⟩
  dsimp [ParabolicC0AlphaWith.invSubBoundConst,
    ParabolicC0AlphaWith.invSubHolderConst]
  linarith

theorem div {𝕜 : Type*} [NormedField 𝕜] {a b : ℝ × X → 𝕜}
    {N₁ N₂ δ α : ℝ} {s : Set (ℝ × X)}
    (ha : ParabolicC0AlphaNormLe N₁ α a s)
    (hb : ParabolicC0AlphaNormLe N₂ α b s)
    (hδpos : 0 < δ) (hδ : ∀ ⦃p : ℝ × X⦄, p ∈ s → δ ≤ ‖b p‖) :
    ParabolicC0AlphaNormLe
      (N₁ * δ⁻¹ + (N₁ * (δ⁻¹ * N₂ * δ⁻¹) + δ⁻¹ * N₁)) α
      (fun z => a z / b z) s := by
  rcases ha with ⟨Ba, hBa, Ha, hHa, ha_sum, ha_ctrl⟩
  rcases hb with ⟨Bb, hBb, Hb, hHb, hb_sum, hb_ctrl⟩
  have hδnn : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδpos.le
  have hN₁ : 0 ≤ N₁ := (add_nonneg hBa hHa).trans ha_sum
  have hN₂ : 0 ≤ N₂ := (add_nonneg hBb hHb).trans hb_sum
  have hBa_le : Ba ≤ N₁ := by linarith
  have hHa_le : Ha ≤ N₁ := by linarith
  have hHb_le : Hb ≤ N₂ := by linarith
  refine ⟨Ba * δ⁻¹, mul_nonneg hBa hδnn,
    Ba * (δ⁻¹ * Hb * δ⁻¹) + δ⁻¹ * Ha, ?_, ?_,
    ha_ctrl.div hb_ctrl hBa hδpos hδ⟩
  · exact add_nonneg
      (mul_nonneg hBa (mul_nonneg (mul_nonneg hδnn hHb) hδnn))
      (mul_nonneg hδnn hHa)
  · have hBterm : Ba * δ⁻¹ ≤ N₁ * δ⁻¹ :=
      mul_le_mul_of_nonneg_right hBa_le hδnn
    have hHb_factor : δ⁻¹ * Hb * δ⁻¹ ≤ δ⁻¹ * N₂ * δ⁻¹ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hHb_le hδnn) hδnn
    have hHterm₁ : Ba * (δ⁻¹ * Hb * δ⁻¹) ≤ N₁ * (δ⁻¹ * N₂ * δ⁻¹) := by
      exact mul_le_mul hBa_le hHb_factor
        (mul_nonneg (mul_nonneg hδnn hHb) hδnn) hN₁
    have hHterm₂ : δ⁻¹ * Ha ≤ δ⁻¹ * N₁ :=
      mul_le_mul_of_nonneg_left hHa_le hδnn
    linarith

theorem continuousLinearMap₂ {F G : Type*} [NormedAddCommGroup F]
    [NormedAddCommGroup G] [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G]
    {N₁ N₂ α : ℝ} {v : ℝ × X → F} {s : Set (ℝ × X)}
    (L : E →L[ℝ] F →L[ℝ] G)
    (hu : ParabolicC0AlphaNormLe N₁ α u s)
    (hv : ParabolicC0AlphaNormLe N₂ α v s) :
    ParabolicC0AlphaNormLe (‖L‖ * N₁ * N₂) α (fun z => L (u z) (v z)) s := by
  rcases hu with ⟨Bu, hBu, Hu, hHu, hu_sum, hu_ctrl⟩
  rcases hv with ⟨Bv, hBv, Hv, hHv, hv_sum, hv_ctrl⟩
  have hNu : 0 ≤ N₁ := (add_nonneg hBu hHu).trans hu_sum
  refine ⟨‖L‖ * Bu * Bv, mul_nonneg (mul_nonneg (norm_nonneg L) hBu) hBv,
    ‖L‖ * (Bu * Hv + Bv * Hu),
    mul_nonneg (norm_nonneg L)
      (add_nonneg (mul_nonneg hBu hHv) (mul_nonneg hBv hHu)), ?_,
    hu_ctrl.continuousLinearMap₂ L hv_ctrl hBu⟩
  have hleft : Bu * Bv + (Bu * Hv + Bv * Hu) ≤ (Bu + Hu) * (Bv + Hv) := by
    nlinarith [mul_nonneg hHu hHv]
  have hright : (Bu + Hu) * (Bv + Hv) ≤ N₁ * N₂ :=
    mul_le_mul hu_sum hv_sum (add_nonneg hBv hHv) hNu
  calc
    ‖L‖ * Bu * Bv + ‖L‖ * (Bu * Hv + Bv * Hu) =
        ‖L‖ * (Bu * Bv + (Bu * Hv + Bv * Hu)) := by ring
    _ ≤ ‖L‖ * ((Bu + Hu) * (Bv + Hv)) :=
        mul_le_mul_of_nonneg_left hleft (norm_nonneg L)
    _ ≤ ‖L‖ * (N₁ * N₂) := mul_le_mul_of_nonneg_left hright (norm_nonneg L)
    _ = ‖L‖ * N₁ * N₂ := by ring

theorem continuousLinearMap₂_sub {F G : Type*} [NormedAddCommGroup F]
    [NormedAddCommGroup G] [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G]
    (L : E →L[ℝ] F →L[ℝ] G)
    {Nu Nv Ndu Ndv α : ℝ} {u u' : ℝ × X → E} {v v' : ℝ × X → F}
    {s : Set (ℝ × X)}
    (hu : ParabolicC0AlphaNormLe Nu α u s)
    (hv' : ParabolicC0AlphaNormLe Nv α v' s)
    (hdu : ParabolicC0AlphaNormLe Ndu α (fun z => u z - u' z) s)
    (hdv : ParabolicC0AlphaNormLe Ndv α (fun z => v z - v' z) s) :
    ParabolicC0AlphaNormLe (‖L‖ * (Nu * Ndv + Ndu * Nv)) α
      (fun z => L (u z) (v z) - L (u' z) (v' z)) s := by
  rcases hu with ⟨Bu, hBu, Hu, hHu, hu_sum, hu_ctrl⟩
  rcases hv' with ⟨Bv, hBv, Hv, hHv, hv_sum, hv_ctrl⟩
  rcases hdu with ⟨Bdu, hBdu, Hdu, hHdu, hdu_sum, hdu_ctrl⟩
  rcases hdv with ⟨Bdv, hBdv, Hdv, hHdv, hdv_sum, hdv_ctrl⟩
  refine ⟨‖L‖ * Bu * Bdv + ‖L‖ * Bdu * Bv, ?_,
    ‖L‖ * (Bu * Hdv + Bdv * Hu) + ‖L‖ * (Bdu * Hv + Bv * Hdu), ?_, ?_,
    hu_ctrl.continuousLinearMap₂_sub L hv_ctrl hdu_ctrl hdv_ctrl hBu hBdu⟩
  · exact add_nonneg
      (mul_nonneg (mul_nonneg (norm_nonneg L) hBu) hBdv)
      (mul_nonneg (mul_nonneg (norm_nonneg L) hBdu) hBv)
  · exact add_nonneg
      (mul_nonneg (norm_nonneg L)
        (add_nonneg (mul_nonneg hBu hHdv) (mul_nonneg hBdv hHu)))
      (mul_nonneg (norm_nonneg L)
        (add_nonneg (mul_nonneg hBdu hHv) (mul_nonneg hBv hHdu)))
  · have hNu : 0 ≤ Nu := (add_nonneg hBu hHu).trans hu_sum
    have hNdu : 0 ≤ Ndu := (add_nonneg hBdu hHdu).trans hdu_sum
    have hleft :
        (Bu * Bdv + Bdu * Bv) +
            ((Bu * Hdv + Bdv * Hu) + (Bdu * Hv + Bv * Hdu)) ≤
          (Bu + Hu) * (Bdv + Hdv) + (Bdu + Hdu) * (Bv + Hv) := by
      nlinarith [mul_nonneg hHu hHdv, mul_nonneg hHdu hHv]
    have hright₁ : (Bu + Hu) * (Bdv + Hdv) ≤ Nu * Ndv :=
      mul_le_mul hu_sum hdv_sum (add_nonneg hBdv hHdv) hNu
    have hright₂ : (Bdu + Hdu) * (Bv + Hv) ≤ Ndu * Nv :=
      mul_le_mul hdu_sum hv_sum (add_nonneg hBv hHv) hNdu
    calc
      (‖L‖ * Bu * Bdv + ‖L‖ * Bdu * Bv) +
          (‖L‖ * (Bu * Hdv + Bdv * Hu) + ‖L‖ * (Bdu * Hv + Bv * Hdu)) =
        ‖L‖ *
          ((Bu * Bdv + Bdu * Bv) +
            ((Bu * Hdv + Bdv * Hu) + (Bdu * Hv + Bv * Hdu))) := by ring
      _ ≤ ‖L‖ * ((Bu + Hu) * (Bdv + Hdv) + (Bdu + Hdu) * (Bv + Hv)) :=
        mul_le_mul_of_nonneg_left hleft (norm_nonneg L)
      _ ≤ ‖L‖ * (Nu * Ndv + Ndu * Nv) :=
        mul_le_mul_of_nonneg_left (add_le_add hright₁ hright₂) (norm_nonneg L)

theorem continuousLinearMap_apply {F : Type*} [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {NA Nv α : ℝ} {A : ℝ × X → E →L[ℝ] F} {v : ℝ × X → E}
    {s : Set (ℝ × X)}
    (hA : ParabolicC0AlphaNormLe NA α A s)
    (hv : ParabolicC0AlphaNormLe Nv α v s) :
    ParabolicC0AlphaNormLe (NA * Nv) α (fun z => A z (v z)) s := by
  rcases hA with ⟨BA, hBA, HA, hHA, hA_sum, hA_ctrl⟩
  rcases hv with ⟨Bv, hBv, Hv, hHv, hv_sum, hv_ctrl⟩
  have hNA : 0 ≤ NA := (add_nonneg hBA hHA).trans hA_sum
  refine ⟨BA * Bv, mul_nonneg hBA hBv, BA * Hv + Bv * HA,
    add_nonneg (mul_nonneg hBA hHv) (mul_nonneg hBv hHA), ?_,
    hA_ctrl.continuousLinearMap_apply hv_ctrl hBA⟩
  have hleft : BA * Bv + (BA * Hv + Bv * HA) ≤ (BA + HA) * (Bv + Hv) := by
    nlinarith [mul_nonneg hHA hHv]
  have hright : (BA + HA) * (Bv + Hv) ≤ NA * Nv :=
    mul_le_mul hA_sum hv_sum (add_nonneg hBv hHv) hNA
  exact hleft.trans hright

theorem continuousLinearMap_apply_sub {F : Type*} [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {NA Nv NAd Nvd α : ℝ} {A A' : ℝ × X → E →L[ℝ] F}
    {v v' : ℝ × X → E} {s : Set (ℝ × X)}
    (hA : ParabolicC0AlphaNormLe NA α A s)
    (hv' : ParabolicC0AlphaNormLe Nv α v' s)
    (hAdiff : ParabolicC0AlphaNormLe NAd α (fun z => A z - A' z) s)
    (hvdiff : ParabolicC0AlphaNormLe Nvd α (fun z => v z - v' z) s) :
    ParabolicC0AlphaNormLe (NA * Nvd + NAd * Nv) α
      (fun z => A z (v z) - A' z (v' z)) s := by
  rcases hA with ⟨BA, hBA, HA, hHA, hA_sum, hA_ctrl⟩
  rcases hv' with ⟨Bv, hBv, Hv, hHv, hv_sum, hv_ctrl⟩
  rcases hAdiff with ⟨BAd, hBAd, HAd, hHAd, hAd_sum, hAd_ctrl⟩
  rcases hvdiff with ⟨Bvd, hBvd, Hvd, hHvd, hvd_sum, hvd_ctrl⟩
  refine ⟨BA * Bvd + BAd * Bv,
    add_nonneg (mul_nonneg hBA hBvd) (mul_nonneg hBAd hBv),
    (BA * Hvd + Bvd * HA) + (BAd * Hv + Bv * HAd), ?_, ?_,
    hA_ctrl.continuousLinearMap_apply_sub hv_ctrl hAd_ctrl hvd_ctrl hBA hBAd⟩
  · exact add_nonneg
      (add_nonneg (mul_nonneg hBA hHvd) (mul_nonneg hBvd hHA))
      (add_nonneg (mul_nonneg hBAd hHv) (mul_nonneg hBv hHAd))
  · have hNA : 0 ≤ NA := (add_nonneg hBA hHA).trans hA_sum
    have hNAd : 0 ≤ NAd := (add_nonneg hBAd hHAd).trans hAd_sum
    have hleft :
        (BA * Bvd + BAd * Bv) +
            ((BA * Hvd + Bvd * HA) + (BAd * Hv + Bv * HAd)) ≤
          (BA + HA) * (Bvd + Hvd) + (BAd + HAd) * (Bv + Hv) := by
      nlinarith [mul_nonneg hHA hHvd, mul_nonneg hHAd hHv]
    have hright₁ : (BA + HA) * (Bvd + Hvd) ≤ NA * Nvd :=
      mul_le_mul hA_sum hvd_sum (add_nonneg hBvd hHvd) hNA
    have hright₂ : (BAd + HAd) * (Bv + Hv) ≤ NAd * Nv :=
      mul_le_mul hAd_sum hv_sum (add_nonneg hBv hHv) hNAd
    linarith

theorem comp_lipschitzOnWith {F : Type*} [NormedAddCommGroup F]
    {Bφ : ℝ} {K : ℝ≥0} {φ : E → F}
    (hu : ParabolicC0AlphaNormLe N α u s) (hBφ : 0 ≤ Bφ)
    (hφB : ∀ y ∈ u '' s, ‖φ y‖ ≤ Bφ)
    (hφL : LipschitzOnWith K φ (u '' s)) :
    ParabolicC0AlphaNormLe (Bφ + (K : ℝ) * N) α (fun z => φ (u z)) s := by
  rcases hu with ⟨B, hB, H, hH, hsum, hctrl⟩
  refine ⟨Bφ, hBφ, (K : ℝ) * H, mul_nonneg (NNReal.coe_nonneg K) hH, ?_,
    hctrl.comp_lipschitzOnWith hφB hφL⟩
  have hH_le_N : H ≤ N := by linarith
  have hKH_le_KN : (K : ℝ) * H ≤ (K : ℝ) * N :=
    mul_le_mul_of_nonneg_left hH_le_N (NNReal.coe_nonneg K)
  linarith

theorem comp_lipschitzOnWith_of_closedBall {F : Type*} [NormedAddCommGroup F]
    {Bφ : ℝ} {K : ℝ≥0} {φ : E → F}
    (hu : ParabolicC0AlphaNormLe N α u s) (hBφ : 0 ≤ Bφ)
    (hφB : ∀ y ∈ Metric.closedBall (0 : E) N, ‖φ y‖ ≤ Bφ)
    (hφL : LipschitzOnWith K φ (Metric.closedBall (0 : E) N)) :
    ParabolicC0AlphaNormLe (Bφ + (K : ℝ) * N) α (fun z => φ (u z)) s := by
  rcases hu with ⟨B, hB, H, hH, hsum, hctrl⟩
  have hB_le_N : B ≤ N := by linarith
  refine ⟨Bφ, hBφ, (K : ℝ) * H, mul_nonneg (NNReal.coe_nonneg K) hH, ?_, ?_⟩
  · have hH_le_N : H ≤ N := by linarith
    have hKH_le_KN : (K : ℝ) * H ≤ (K : ℝ) * N :=
      mul_le_mul_of_nonneg_left hH_le_N (NNReal.coe_nonneg K)
    linarith
  · exact hctrl.comp_lipschitzOnWith_of_closedBall
      (fun y hy => hφB y (Metric.closedBall_subset_closedBall hB_le_N hy))
      (hφL.mono (Metric.closedBall_subset_closedBall hB_le_N))

theorem comp_lipschitzOnWith_of_closedBall_auto_bound {F : Type*} [NormedAddCommGroup F]
    {K : ℝ≥0} {φ : E → F}
    (hu : ParabolicC0AlphaNormLe N α u s)
    (hφL : LipschitzOnWith K φ (Metric.closedBall (0 : E) N)) :
    ParabolicC0AlphaNormLe (‖φ (0 : E)‖ + (K : ℝ) * N) α
      (fun z => φ (u z)) s := by
  rcases hu with ⟨B, hB, H, hH, hsum, hctrl⟩
  have hB_le_N : B ≤ N := by linarith
  refine ⟨‖φ (0 : E)‖ + (K : ℝ) * B,
    add_nonneg (norm_nonneg _) (mul_nonneg (NNReal.coe_nonneg K) hB),
    (K : ℝ) * H, mul_nonneg (NNReal.coe_nonneg K) hH, ?_, ?_⟩
  · calc
      ‖φ (0 : E)‖ + (K : ℝ) * B + (K : ℝ) * H =
          ‖φ (0 : E)‖ + (K : ℝ) * (B + H) := by ring
      _ ≤ ‖φ (0 : E)‖ + (K : ℝ) * N := by
          have hmul : (K : ℝ) * (B + H) ≤ (K : ℝ) * N :=
            mul_le_mul_of_nonneg_left hsum (NNReal.coe_nonneg K)
          linarith
  · exact hctrl.comp_lipschitzOnWith_of_closedBall_auto_bound hB
      (hφL.mono (Metric.closedBall_subset_closedBall hB_le_N))

theorem comp_lipschitzWith {F : Type*} [NormedAddCommGroup F]
    {Bφ : ℝ} {K : ℝ≥0} {φ : E → F}
    (hu : ParabolicC0AlphaNormLe N α u s) (hBφ : 0 ≤ Bφ)
    (hφB : ∀ y ∈ u '' s, ‖φ y‖ ≤ Bφ) (hφ : LipschitzWith K φ) :
    ParabolicC0AlphaNormLe (Bφ + (K : ℝ) * N) α (fun z => φ (u z)) s :=
  hu.comp_lipschitzOnWith hBφ hφB hφ.lipschitzOnWith

theorem continuousOn (h : ParabolicC0AlphaNormLe N α u s) (hα : 0 < α) :
    ContinuousOn u s :=
  h.c0AlphaOn.continuousOn hα

theorem uniformContinuousOn (h : ParabolicC0AlphaNormLe N α u s) (hα : 0 < α) :
    UniformContinuousOn u s :=
  h.c0AlphaOn.uniformContinuousOn hα

end ParabolicC0AlphaNormLe

/-- Scalar multiples and sums of parabolic `C^{0,α}` functions form a real submodule of all
time-space functions. -/
def parabolicC0AlphaSubmodule
    (X E : Type*) [PseudoMetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α : ℝ) (s : Set (ℝ × X)) : Submodule ℝ ((ℝ × X) → E) where
  carrier := {u | ParabolicC0AlphaOn α u s}
  zero_mem' := by
    change ParabolicC0AlphaOn α (fun _ : ℝ × X => (0 : E)) s
    exact ParabolicC0AlphaOn.const (X := X) (α := α) (s := s) (0 : E)
  add_mem' := by
    intro u v hu hv
    change ParabolicC0AlphaOn α (fun z => u z + v z) s
    exact ParabolicC0AlphaOn.add (X := X) (α := α) (s := s) hu hv
  smul_mem' := by
    intro c u hu
    change ParabolicC0AlphaOn α (fun z => c • u z) s
    exact ParabolicC0AlphaOn.smul (X := X) (α := α) (s := s) (𝕜 := ℝ) c hu

namespace parabolicC0AlphaSubmodule

variable {X E : Type*} [PseudoMetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {α : ℝ} {s t : Set (ℝ × X)}

instance :
    CoeFun (parabolicC0AlphaSubmodule X E α s) (fun _ => (ℝ × X) → E) :=
  ⟨fun u => u.1⟩

@[simp]
theorem mem_iff {u : (ℝ × X) → E} :
    u ∈ parabolicC0AlphaSubmodule X E α s ↔ ParabolicC0AlphaOn α u s :=
  Iff.rfl

/-- Restriction to a smaller set as a linear map between parabolic Holder function spaces. -/
def restrictLinearMap (hst : t ⊆ s) :
    parabolicC0AlphaSubmodule X E α s →ₗ[ℝ] parabolicC0AlphaSubmodule X E α t where
  toFun u := ⟨u.1, u.2.mono_set hst⟩
  map_add' := by
    intro u v
    ext z
    simp
  map_smul' := by
    intro c u
    ext z
    simp

@[simp]
theorem restrictLinearMap_apply (hst : t ⊆ s)
    (u : parabolicC0AlphaSubmodule X E α s) (z : ℝ × X) :
    restrictLinearMap (X := X) (E := E) (α := α) hst u z = u z :=
  rfl

/-- Compose parabolic `C^{0,α}` functions with a continuous linear value map. -/
def continuousLinearMap {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) :
    parabolicC0AlphaSubmodule X E α s →ₗ[ℝ] parabolicC0AlphaSubmodule X F α s where
  toFun u := ⟨fun z => L (u z), u.2.continuousLinearMap L⟩
  map_add' := by
    intro u v
    ext z
    simp
  map_smul' := by
    intro c u
    ext z
    simp

@[simp]
theorem continuousLinearMap_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (u : parabolicC0AlphaSubmodule X E α s) (z : ℝ × X) :
    continuousLinearMap (X := X) (E := E) (α := α) (s := s) L u z = L (u z) :=
  rfl

/-- Product-valued pairing of two parabolic `C^{0,α}` submodule elements. -/
def prodLinearMap {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    parabolicC0AlphaSubmodule X E α s × parabolicC0AlphaSubmodule X F α s →ₗ[ℝ]
      parabolicC0AlphaSubmodule X (E × F) α s where
  toFun u := ⟨fun z => (u.1 z, u.2 z), u.1.2.prod u.2.2⟩
  map_add' := by
    intro u v
    ext z <;> rfl
  map_smul' := by
    intro c u
    ext z <;> rfl

@[simp]
theorem prodLinearMap_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : parabolicC0AlphaSubmodule X E α s × parabolicC0AlphaSubmodule X F α s)
    (z : ℝ × X) :
    prodLinearMap (X := X) (E := E) (α := α) (s := s) u z = (u.1 z, u.2 z) :=
  rfl

/-- Coordinate projection from a finite Pi-valued parabolic `C^{0,α}` submodule. -/
def piApplyLinearMap {ι F : Type*} [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (i : ι) :
    parabolicC0AlphaSubmodule X (ι → F) α s →ₗ[ℝ]
      parabolicC0AlphaSubmodule X F α s :=
  continuousLinearMap (X := X) (E := ι → F) (α := α) (s := s)
    (ContinuousLinearMap.proj i : (ι → F) →L[ℝ] F)

@[simp]
theorem piApplyLinearMap_apply {ι F : Type*} [Fintype ι] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (i : ι) (u : parabolicC0AlphaSubmodule X (ι → F) α s)
    (z : ℝ × X) :
    piApplyLinearMap (X := X) (α := α) (s := s) i u z = u z i :=
  rfl

/-- Assemble a finite Pi-valued parabolic `C^{0,α}` submodule element from its components. -/
def piOfComponentsLinearMap {ι F : Type*} [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    (ι → parabolicC0AlphaSubmodule X F α s) →ₗ[ℝ]
      parabolicC0AlphaSubmodule X (ι → F) α s where
  toFun u := ⟨fun z i => u i z, ParabolicC0AlphaOn.pi fun i => (u i).2⟩
  map_add' := by
    intro u v
    ext z i
    rfl
  map_smul' := by
    intro c u
    ext z i
    rfl

@[simp]
theorem piOfComponentsLinearMap_apply {ι F : Type*} [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : ι → parabolicC0AlphaSubmodule X F α s) (z : ℝ × X) (i : ι) :
    piOfComponentsLinearMap (X := X) (α := α) (s := s) u z i = u i z :=
  rfl

/-- Read a parabolic `C^{0,α}` function as a continuous map on a compact time-space piece. -/
def toContinuousMap {K : TopologicalSpace.Compacts (ℝ × X)}
    (hK : (K : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (u : parabolicC0AlphaSubmodule X E α s) : C(K, E) where
  toFun z := u z.1
  continuous_toFun := by
    have hu_cont : ContinuousOn u.1 s := u.2.continuousOn hα
    exact continuousOn_iff_continuous_restrict.mp (hu_cont.mono hK)

@[simp]
theorem toContinuousMap_apply {K : TopologicalSpace.Compacts (ℝ × X)}
    (hK : (K : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (u : parabolicC0AlphaSubmodule X E α s) (z : K) :
    toContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα u z = u z.1 :=
  rfl

/-- Compact-piece readout of a parabolic `C^{0,α}` function as a linear map. -/
def toContinuousMapLinearMap {K : TopologicalSpace.Compacts (ℝ × X)}
    (hK : (K : Set (ℝ × X)) ⊆ s) (hα : 0 < α) :
    parabolicC0AlphaSubmodule X E α s →ₗ[ℝ] C(K, E) where
  toFun := toContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα
  map_add' := by
    intro u v
    ext z
    rfl
  map_smul' := by
    intro c u
    ext z
    rfl

@[simp]
theorem toContinuousMapLinearMap_apply {K : TopologicalSpace.Compacts (ℝ × X)}
    (hK : (K : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (u : parabolicC0AlphaSubmodule X E α s) :
    toContinuousMapLinearMap (X := X) (E := E) (α := α) (s := s) hK hα u =
      toContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα u :=
  rfl

/-- A single-radius `C^{0,α}` bound on a difference controls the compact readout sup norm. -/
theorem norm_toContinuousMap_sub_le_of_normLe {K : TopologicalSpace.Compacts (ℝ × X)}
    (hK : (K : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {N : ℝ} {u v : parabolicC0AlphaSubmodule X E α s}
    (h : ParabolicC0AlphaNormLe N α (fun z => u z - v z) s) :
    ‖toContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα u -
        toContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα v‖ ≤ N := by
  rcases h with ⟨B, hB, H, hH, hsum, hctrl⟩
  have hN : 0 ≤ N := (add_nonneg hB hH).trans hsum
  have hB_le_N : B ≤ N := by linarith
  refine (ContinuousMap.norm_le
    (f := toContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα u -
      toContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα v) hN).mpr ?_
  intro z
  have hz : z.1 ∈ s := hK z.2
  calc
    ‖(toContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα u -
        toContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα v) z‖ =
        ‖u z.1 - v z.1‖ := by
          rfl
    _ ≤ B := hctrl.bounded hz
    _ ≤ N := hB_le_N

/-- Componentwise `C^{0,α}` difference controls with radii linear in a shared scalar control the
compact readout sup norm of a finite Pi-valued parabolic function. -/
theorem norm_toContinuousMap_pi_sub_le_sum_mul_of_entries
    {Kc : TopologicalSpace.Compacts (ℝ × X)}
    (hKc : (Kc : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {ι F : Type*} [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {R : ℝ} {K : ι → ℝ}
    {u v : parabolicC0AlphaSubmodule X (ι → F) α s}
    (hK_nonneg : ∀ i, 0 ≤ K i) (hR : 0 ≤ R)
    (h : ∀ i, ParabolicC0AlphaNormLe (K i * R) α
      (fun z => u z i - v z i) s) :
    ‖toContinuousMap (X := X) (E := ι → F) (α := α) (s := s) hKc hα u -
        toContinuousMap (X := X) (E := ι → F) (α := α) (s := s) hKc hα v‖ ≤
      (∑ i, K i) * R := by
  have hsum_nonneg : 0 ≤ ∑ i, K i :=
    Finset.sum_nonneg fun i _hi => hK_nonneg i
  have htarget_nonneg : 0 ≤ (∑ i, K i) * R :=
    mul_nonneg hsum_nonneg hR
  refine (ContinuousMap.norm_le
    (f := toContinuousMap (X := X) (E := ι → F) (α := α) (s := s) hKc hα u -
      toContinuousMap (X := X) (E := ι → F) (α := α) (s := s) hKc hα v)
    htarget_nonneg).mpr ?_
  intro z
  have hz : z.1 ∈ s := hKc z.2
  calc
    ‖(toContinuousMap (X := X) (E := ι → F) (α := α) (s := s) hKc hα u -
        toContinuousMap (X := X) (E := ι → F) (α := α) (s := s) hKc hα v) z‖ =
        ‖u z.1 - v z.1‖ := by
          rfl
    _ ≤ (∑ i, K i) * R :=
        ParabolicC0AlphaNormLe.pi_norm_sub_le_sum_mul_of_entries
          (X := X) (α := α) (s := s) hK_nonneg hR h hz

/-- A sup-bound on a difference controls the compact readout sup norm.  This lower-level
readout is useful when an estimate gives only the `C⁰` part of the parabolic norm. -/
theorem norm_toContinuousMap_sub_le_of_bounded {K : TopologicalSpace.Compacts (ℝ × X)}
    (hK : (K : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {N : ℝ} (hN : 0 ≤ N) {u v : parabolicC0AlphaSubmodule X E α s}
    (h : ParabolicBoundedWith N (fun z => u z - v z) s) :
    ‖toContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα u -
        toContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα v‖ ≤ N := by
  refine (ContinuousMap.norm_le
    (f := toContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα u -
      toContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα v) hN).mpr ?_
  intro z
  have hz : z.1 ∈ s := hK z.2
  calc
    ‖(toContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα u -
        toContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα v) z‖ =
        ‖u z.1 - v z.1‖ := by
          rfl
    _ ≤ N := h hz

/-- Pairwise single-radius `C^{0,α}` difference estimates give a Lipschitz estimate for one
compact-piece readout. -/
theorem lipschitzOnWith_toContinuousMap_of_normLe_sub {Y : Type*} [PseudoMetricSpace Y]
    {K : TopologicalSpace.Compacts (ℝ × X)}
    (hK : (K : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {stateSet : Set Y} {L : ℝ≥0} {A : Y → parabolicC0AlphaSubmodule X E α s}
    (h : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ParabolicC0AlphaNormLe ((L : ℝ) * dist u v) α (fun z => A u z - A v z) s) :
    LipschitzOnWith L
      (fun u : Y => toContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα (A u))
      stateSet := by
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro u hu v hv
  have hnorm := norm_toContinuousMap_sub_le_of_normLe
    (X := X) (E := E) (α := α) (s := s) hK hα (h hu hv)
  simpa [dist_eq_norm] using hnorm

/-- Componentwise `C^{0,α}` difference estimates with finite Pi constants give a Lipschitz
estimate for one compact readout of a finite Pi-valued parabolic function. -/
theorem lipschitzOnWith_toContinuousMap_pi_of_component_normLe_sub
    {Y ι F : Type*} [PseudoMetricSpace Y] [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Kc : TopologicalSpace.Compacts (ℝ × X)}
    (hKc : (Kc : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {stateSet : Set Y} (K : ι → ℝ≥0)
    {A : Y → parabolicC0AlphaSubmodule X (ι → F) α s}
    (h : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ i,
      ParabolicC0AlphaNormLe ((K i : ℝ) * dist u v) α
        (fun z => A u z i - A v z i) s) :
    LipschitzOnWith (∑ i, K i)
      (fun u : Y =>
        toContinuousMap (X := X) (E := ι → F) (α := α) (s := s) hKc hα (A u))
      stateSet := by
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro u hu v hv
  have hnorm := norm_toContinuousMap_pi_sub_le_sum_mul_of_entries
    (X := X) (α := α) (s := s) hKc hα
    (K := fun i => (K i : ℝ)) (R := dist u v)
    (fun i => NNReal.coe_nonneg (K i)) dist_nonneg (fun i => h hu hv i)
  simpa [dist_eq_norm, NNReal.coe_sum] using hnorm

/-- Pairwise sup-bound difference estimates give a Lipschitz estimate for one compact-piece
readout. -/
theorem lipschitzOnWith_toContinuousMap_of_bounded_sub {Y : Type*} [PseudoMetricSpace Y]
    {K : TopologicalSpace.Compacts (ℝ × X)}
    (hK : (K : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {stateSet : Set Y} {L : ℝ≥0} {A : Y → parabolicC0AlphaSubmodule X E α s}
    (h : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ParabolicBoundedWith ((L : ℝ) * dist u v) (fun z => A u z - A v z) s) :
    LipschitzOnWith L
      (fun u : Y => toContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα (A u))
      stateSet := by
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro u hu v hv
  have hnorm := norm_toContinuousMap_sub_le_of_bounded
    (X := X) (E := E) (α := α) (s := s) hK hα
    (mul_nonneg (NNReal.coe_nonneg L) dist_nonneg) (h hu hv)
  simpa [dist_eq_norm] using hnorm

/-- Read a parabolic `C^{0,α}` function on every compact piece of a chosen cover. -/
def toCompactCoordFamily {κ : Type*} (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (u : parabolicC0AlphaSubmodule X E α s) : ∀ i, C(Kc i, E) :=
  fun i => toContinuousMap (X := X) (E := E) (α := α) (s := s) (hKc i) hα u

@[simp]
theorem toCompactCoordFamily_apply {κ : Type*}
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (u : parabolicC0AlphaSubmodule X E α s) (i : κ) (z : Kc i) :
    toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα u i z =
      u z.1 :=
  rfl

/-- Finite-cover coordinate readout as a linear map into the product of compact continuous-map
pieces. -/
def toCompactCoordFamilyLinearMap {κ : Type*}
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α) :
    parabolicC0AlphaSubmodule X E α s →ₗ[ℝ] (∀ i, C(Kc i, E)) where
  toFun := toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα
  map_add' := by
    intro u v
    ext i z
    simp [toCompactCoordFamily, toContinuousMap]
  map_smul' := by
    intro c u
    ext i z
    simp [toCompactCoordFamily, toContinuousMap]

@[simp]
theorem toCompactCoordFamilyLinearMap_apply {κ : Type*}
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (u : parabolicC0AlphaSubmodule X E α s) :
    toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα u =
      toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα u :=
  rfl

/-- A single-radius `C^{0,α}` bound on a difference controls each compact-family readout. -/
theorem norm_toCompactCoordFamily_sub_le_of_normLe {κ : Type*}
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {N : ℝ} {u v : parabolicC0AlphaSubmodule X E α s}
    (h : ParabolicC0AlphaNormLe N α (fun z => u z - v z) s) (i : κ) :
    ‖toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα u i -
        toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα v i‖ ≤ N :=
  norm_toContinuousMap_sub_le_of_normLe
    (X := X) (E := E) (α := α) (s := s) (hKc i) hα h

/-- A sup-bound on a difference controls each compact-family readout. -/
theorem norm_toCompactCoordFamily_sub_le_of_bounded {κ : Type*}
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {N : ℝ} (hN : 0 ≤ N) {u v : parabolicC0AlphaSubmodule X E α s}
    (h : ParabolicBoundedWith N (fun z => u z - v z) s) (i : κ) :
    ‖toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα u i -
        toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα v i‖ ≤ N :=
  norm_toContinuousMap_sub_le_of_bounded
    (X := X) (E := E) (α := α) (s := s) (hKc i) hα hN h

/-- A single-radius `C^{0,α}` difference bound controls the finite product of compact-family
readouts in the product sup norm. -/
theorem norm_toCompactCoordFamily_family_sub_le_of_normLe {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {N : ℝ} {u v : parabolicC0AlphaSubmodule X E α s}
    (h : ParabolicC0AlphaNormLe N α (fun z => u z - v z) s) :
    ‖toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα u -
        toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα v‖ ≤ N := by
  refine (pi_norm_le_iff_of_nonneg h.nonneg).2 fun i => ?_
  exact norm_toCompactCoordFamily_sub_le_of_normLe
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα h i

/-- Componentwise `C^{0,α}` difference controls with radii linear in a shared scalar control the
finite product of compact-family readouts for finite Pi-valued parabolic functions. -/
theorem norm_toCompactCoordFamily_pi_family_sub_le_sum_mul_of_entries {κ ι F : Type*}
    [Fintype κ] [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {R : ℝ} {K : ι → ℝ}
    {u v : parabolicC0AlphaSubmodule X (ι → F) α s}
    (hK_nonneg : ∀ i, 0 ≤ K i) (hR : 0 ≤ R)
    (h : ∀ i, ParabolicC0AlphaNormLe (K i * R) α
      (fun z => u z i - v z i) s) :
    ‖toCompactCoordFamily (X := X) (E := ι → F) (α := α) (s := s)
        Kc hKc hα u -
      toCompactCoordFamily (X := X) (E := ι → F) (α := α) (s := s)
        Kc hKc hα v‖ ≤
      (∑ i, K i) * R := by
  have hsum_nonneg : 0 ≤ ∑ i, K i :=
    Finset.sum_nonneg fun i _hi => hK_nonneg i
  have htarget_nonneg : 0 ≤ (∑ i, K i) * R :=
    mul_nonneg hsum_nonneg hR
  refine (pi_norm_le_iff_of_nonneg htarget_nonneg).2 fun i => ?_
  exact norm_toContinuousMap_pi_sub_le_sum_mul_of_entries
    (X := X) (α := α) (s := s) (hKc i) hα hK_nonneg hR h

/-- A sup-bound on a difference controls the finite product of compact-family readouts in the
product sup norm. -/
theorem norm_toCompactCoordFamily_family_sub_le_of_bounded {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {N : ℝ} (hN : 0 ≤ N) {u v : parabolicC0AlphaSubmodule X E α s}
    (h : ParabolicBoundedWith N (fun z => u z - v z) s) :
    ‖toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα u -
        toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα v‖ ≤ N := by
  refine (pi_norm_le_iff_of_nonneg hN).2 fun i => ?_
  exact norm_toCompactCoordFamily_sub_le_of_bounded
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα hN h i

/-- Pairwise single-radius `C^{0,α}` difference estimates give a Lipschitz estimate for the
finite product of compact-family readouts. -/
theorem lipschitzOnWith_toCompactCoordFamily_of_normLe_sub {Y κ : Type*}
    [PseudoMetricSpace Y] [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {stateSet : Set Y} {L : ℝ≥0} {A : Y → parabolicC0AlphaSubmodule X E α s}
    (h : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ParabolicC0AlphaNormLe ((L : ℝ) * dist u v) α (fun z => A u z - A v z) s) :
    LipschitzOnWith L
      (fun u : Y =>
        toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα (A u))
      stateSet := by
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro u hu v hv
  have hnorm := norm_toCompactCoordFamily_family_sub_le_of_normLe
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα (h hu hv)
  simpa [dist_eq_norm] using hnorm

/-- Componentwise `C^{0,α}` difference estimates with finite Pi constants give a Lipschitz
estimate for the finite compact-family readout of a finite Pi-valued parabolic function. -/
theorem lipschitzOnWith_toCompactCoordFamily_pi_of_component_normLe_sub
    {Y κ ι F : Type*} [PseudoMetricSpace Y] [Fintype κ] [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {stateSet : Set Y} (K : ι → ℝ≥0)
    {A : Y → parabolicC0AlphaSubmodule X (ι → F) α s}
    (h : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ i,
      ParabolicC0AlphaNormLe ((K i : ℝ) * dist u v) α
        (fun z => A u z i - A v z i) s) :
    LipschitzOnWith (∑ i, K i)
      (fun u : Y =>
        toCompactCoordFamily (X := X) (E := ι → F) (α := α) (s := s)
          Kc hKc hα (A u))
      stateSet := by
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro u hu v hv
  have hnorm := norm_toCompactCoordFamily_pi_family_sub_le_sum_mul_of_entries
    (X := X) (α := α) (s := s) Kc hKc hα
    (K := fun i => (K i : ℝ)) (R := dist u v)
    (fun i => NNReal.coe_nonneg (K i)) dist_nonneg (fun i => h hu hv i)
  simpa [dist_eq_norm, NNReal.coe_sum] using hnorm

/-- Pairwise sup-bound difference estimates give a Lipschitz estimate for the finite product of
compact-family readouts. -/
theorem lipschitzOnWith_toCompactCoordFamily_of_bounded_sub {Y κ : Type*}
    [PseudoMetricSpace Y] [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {stateSet : Set Y} {L : ℝ≥0} {A : Y → parabolicC0AlphaSubmodule X E α s}
    (h : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ParabolicBoundedWith ((L : ℝ) * dist u v) (fun z => A u z - A v z) s) :
    LipschitzOnWith L
      (fun u : Y =>
        toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα (A u))
      stateSet := by
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro u hu v hv
  have hnorm := norm_toCompactCoordFamily_family_sub_le_of_bounded
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα
    (mul_nonneg (NNReal.coe_nonneg L) dist_nonneg) (h hu hv)
  simpa [dist_eq_norm] using hnorm

/-- A finite compact-family readout Lipschitz estimate gives pointwise compact-coordinate
distance estimates. -/
theorem forall_compactCoord_dist_le_of_toCompactCoordFamily_lipschitzOnWith {Y κ : Type*}
    [PseudoMetricSpace Y] [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {stateSet : Set Y} {L : ℝ≥0} {A : Y → parabolicC0AlphaSubmodule X E α s}
    (h : LipschitzOnWith L
      (fun u : Y =>
        toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα (A u))
      stateSet) :
    ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ i (z : Kc i),
      dist
        (toCompactCoordFamily (X := X) (E := E) (α := α) (s := s)
          Kc hKc hα (A u) i z)
        (toCompactCoordFamily (X := X) (E := E) (α := α) (s := s)
          Kc hKc hα (A v) i z)
        ≤ (L : ℝ) * dist u v := by
  intro u hu v hv i z
  have hC : 0 ≤ (L : ℝ) * dist u v :=
    mul_nonneg (NNReal.coe_nonneg L) dist_nonneg
  have hdist := h.dist_le_mul u hu v hv
  have hi :
      dist
        (toCompactCoordFamily (X := X) (E := E) (α := α) (s := s)
          Kc hKc hα (A u) i)
        (toCompactCoordFamily (X := X) (E := E) (α := α) (s := s)
          Kc hKc hα (A v) i)
        ≤ (L : ℝ) * dist u v :=
    (dist_pi_le_iff hC).1 hdist i
  exact (ContinuousMap.dist_le hC).1 hi z

/-- A global time-space compact-family cover covers every requested fixed-time spatial slice. -/
theorem timeSlice_spatial_cover_of_iUnion_eq_univ {κ ι : Type*}
    (Kdom : ι → TopologicalSpace.Compacts (ℝ × X))
    (Kx : κ → TopologicalSpace.Compacts X)
    {timeSet : Set ℝ}
    (hcover : (⋃ j, (Kdom j : Set (ℝ × X))) = Set.univ) :
    ∀ τ, τ ∈ timeSet → ∀ i (x : Kx i),
      ∃ j, (τ, x.1) ∈ (Kdom j : Set (ℝ × X)) := by
  intro τ _hτ i x
  have hz : (τ, x.1) ∈ ⋃ j, (Kdom j : Set (ℝ × X)) := by
    simp [hcover]
  exact Set.mem_iUnion.mp hz

/-- Pointwise compact-coordinate estimates on time-space compact pieces give fixed-time spatial
readout estimates whenever the selected time-space pieces cover each requested time slice.  This is
the bridge from parabolic compact readouts to spatial coordinate hypotheses in Banach chart
handoffs. -/
theorem forall_timeSlice_spatial_dist_le_of_forall_compactCoord_dist_le {Y κ ι : Type*}
    [PseudoMetricSpace Y]
    (Kdom : ι → TopologicalSpace.Compacts (ℝ × X))
    (hKdom : ∀ j, (Kdom j : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (Kx : κ → TopologicalSpace.Compacts X)
    {timeSet : Set ℝ} {stateSet : Set Y} {K : ℝ}
    {A : ℝ → Y → parabolicC0AlphaSubmodule X E α s}
    (hcompact : ∀ τ, τ ∈ timeSet → ∀ ⦃u : Y⦄, u ∈ stateSet →
      ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ j (z : Kdom j),
        dist
          (toCompactCoordFamily (X := X) (E := E) (α := α) (s := s)
            Kdom hKdom hα (A τ u) j z)
          (toCompactCoordFamily (X := X) (E := E) (α := α) (s := s)
            Kdom hKdom hα (A τ v) j z)
          ≤ K * dist u v)
    (hcover : ∀ τ, τ ∈ timeSet → ∀ i (x : Kx i),
      ∃ j, (τ, x.1) ∈ (Kdom j : Set (ℝ × X))) :
    ∀ τ, τ ∈ timeSet → ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ∀ i (x : Kx i),
        dist (A τ u (τ, x.1)) (A τ v (τ, x.1)) ≤ K * dist u v := by
  intro τ hτ u hu v hv i x
  rcases hcover τ hτ i x with ⟨j, hzmem⟩
  let z : Kdom j := ⟨(τ, x.1), hzmem⟩
  have hz := hcompact τ hτ hu hv j z
  simpa [z] using hz

/-- A time-dependent finite compact-family readout Lipschitz estimate gives fixed-time spatial
readout estimates whenever the time-space compact pieces cover each requested time slice. -/
theorem forall_timeSlice_spatial_dist_le_of_toCompactCoordFamily_lipschitzOnWith
    {Y κ ι : Type*} [PseudoMetricSpace Y] [Fintype ι]
    (Kdom : ι → TopologicalSpace.Compacts (ℝ × X))
    (hKdom : ∀ j, (Kdom j : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (Kx : κ → TopologicalSpace.Compacts X)
    {timeSet : Set ℝ} {stateSet : Set Y} {L : ℝ≥0}
    {A : ℝ → Y → parabolicC0AlphaSubmodule X E α s}
    (hLip : ∀ τ, τ ∈ timeSet →
      LipschitzOnWith L
        (fun u : Y =>
          toCompactCoordFamily (X := X) (E := E) (α := α) (s := s)
            Kdom hKdom hα (A τ u))
        stateSet)
    (hcover : ∀ τ, τ ∈ timeSet → ∀ i (x : Kx i),
      ∃ j, (τ, x.1) ∈ (Kdom j : Set (ℝ × X))) :
    ∀ τ, τ ∈ timeSet → ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ∀ i (x : Kx i),
        dist (A τ u (τ, x.1)) (A τ v (τ, x.1)) ≤ (L : ℝ) * dist u v := by
  refine forall_timeSlice_spatial_dist_le_of_forall_compactCoord_dist_le
    (X := X) (E := E) (α := α) (s := s)
    Kdom hKdom hα Kx
    (A := A) (K := (L : ℝ)) ?_ hcover
  intro τ hτ
  exact forall_compactCoord_dist_le_of_toCompactCoordFamily_lipschitzOnWith
    (X := X) (E := E) (α := α) (s := s) Kdom hKdom hα (hLip τ hτ)

/-- Pointwise compact-coordinate estimates on a global time-space compact-family cover give
fixed-time spatial readout estimates on every requested spatial slice. -/
theorem forall_timeSlice_spatial_dist_le_of_forall_compactCoord_dist_le_ofCover
    {Y κ ι : Type*} [PseudoMetricSpace Y]
    (Kdom : ι → TopologicalSpace.Compacts (ℝ × X))
    (hKdom : ∀ j, (Kdom j : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (Kx : κ → TopologicalSpace.Compacts X)
    {timeSet : Set ℝ} {stateSet : Set Y} {K : ℝ}
    {A : ℝ → Y → parabolicC0AlphaSubmodule X E α s}
    (hcompact : ∀ τ, τ ∈ timeSet → ∀ ⦃u : Y⦄, u ∈ stateSet →
      ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ j (z : Kdom j),
        dist
          (toCompactCoordFamily (X := X) (E := E) (α := α) (s := s)
            Kdom hKdom hα (A τ u) j z)
          (toCompactCoordFamily (X := X) (E := E) (α := α) (s := s)
            Kdom hKdom hα (A τ v) j z)
          ≤ K * dist u v)
    (hcover : (⋃ j, (Kdom j : Set (ℝ × X))) = Set.univ) :
    ∀ τ, τ ∈ timeSet → ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ∀ i (x : Kx i),
        dist (A τ u (τ, x.1)) (A τ v (τ, x.1)) ≤ K * dist u v :=
  forall_timeSlice_spatial_dist_le_of_forall_compactCoord_dist_le
    (X := X) (E := E) (α := α) (s := s)
    Kdom hKdom hα Kx hcompact
    (timeSlice_spatial_cover_of_iUnion_eq_univ
      (X := X) Kdom Kx (timeSet := timeSet) hcover)

/-- A time-dependent finite compact-family readout Lipschitz estimate on a global time-space cover
gives fixed-time spatial readout estimates on every requested spatial slice. -/
theorem forall_timeSlice_spatial_dist_le_of_toCompactCoordFamily_lipschitzOnWith_ofCover
    {Y κ ι : Type*} [PseudoMetricSpace Y] [Fintype ι]
    (Kdom : ι → TopologicalSpace.Compacts (ℝ × X))
    (hKdom : ∀ j, (Kdom j : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (Kx : κ → TopologicalSpace.Compacts X)
    {timeSet : Set ℝ} {stateSet : Set Y} {L : ℝ≥0}
    {A : ℝ → Y → parabolicC0AlphaSubmodule X E α s}
    (hLip : ∀ τ, τ ∈ timeSet →
      LipschitzOnWith L
        (fun u : Y =>
          toCompactCoordFamily (X := X) (E := E) (α := α) (s := s)
            Kdom hKdom hα (A τ u))
        stateSet)
    (hcover : (⋃ j, (Kdom j : Set (ℝ × X))) = Set.univ) :
    ∀ τ, τ ∈ timeSet → ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ∀ i (x : Kx i),
        dist (A τ u (τ, x.1)) (A τ v (τ, x.1)) ≤ (L : ℝ) * dist u v :=
  forall_timeSlice_spatial_dist_le_of_toCompactCoordFamily_lipschitzOnWith
    (X := X) (E := E) (α := α) (s := s)
    Kdom hKdom hα Kx hLip
    (timeSlice_spatial_cover_of_iUnion_eq_univ
      (X := X) Kdom Kx (timeSet := timeSet) hcover)

/-- The linear compact-family readout inherits the same finite product sup-norm estimate. -/
theorem norm_toCompactCoordFamilyLinearMap_sub_le_of_normLe {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {N : ℝ} {u v : parabolicC0AlphaSubmodule X E α s}
    (h : ParabolicC0AlphaNormLe N α (fun z => u z - v z) s) :
    ‖toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα u -
      toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα v‖ ≤ N := by
  simpa using norm_toCompactCoordFamily_family_sub_le_of_normLe
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα h

/-- The linear finite-cover readout inherits the finite-Pi componentwise summed-radius
estimate. -/
theorem norm_toCompactCoordFamilyLinearMap_pi_sub_le_sum_mul_of_entries
    {κ ι F : Type*} [Fintype κ] [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {R : ℝ} {K : ι → ℝ}
    {u v : parabolicC0AlphaSubmodule X (ι → F) α s}
    (hK_nonneg : ∀ i, 0 ≤ K i) (hR : 0 ≤ R)
    (h : ∀ i, ParabolicC0AlphaNormLe (K i * R) α
      (fun z => u z i - v z i) s) :
    ‖toCompactCoordFamilyLinearMap (X := X) (E := ι → F) (α := α) (s := s)
        Kc hKc hα u -
      toCompactCoordFamilyLinearMap (X := X) (E := ι → F) (α := α) (s := s)
        Kc hKc hα v‖ ≤
      (∑ i, K i) * R := by
  simpa using norm_toCompactCoordFamily_pi_family_sub_le_sum_mul_of_entries
    (X := X) (α := α) (s := s) Kc hKc hα hK_nonneg hR h

/-- The linear compact-family readout inherits the same finite product sup-norm estimate from a
sup-bound on the difference. -/
theorem norm_toCompactCoordFamilyLinearMap_sub_le_of_bounded {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {N : ℝ} (hN : 0 ≤ N) {u v : parabolicC0AlphaSubmodule X E α s}
    (h : ParabolicBoundedWith N (fun z => u z - v z) s) :
    ‖toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα u -
      toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα v‖ ≤ N := by
  simpa using norm_toCompactCoordFamily_family_sub_le_of_bounded
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα hN h

/-- Pairwise single-radius `C^{0,α}` difference estimates give a Lipschitz estimate for the
linear finite-cover readout. -/
theorem lipschitzOnWith_toCompactCoordFamilyLinearMap_of_normLe_sub {Y κ : Type*}
    [PseudoMetricSpace Y] [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {stateSet : Set Y} {L : ℝ≥0} {A : Y → parabolicC0AlphaSubmodule X E α s}
    (h : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ParabolicC0AlphaNormLe ((L : ℝ) * dist u v) α (fun z => A u z - A v z) s) :
    LipschitzOnWith L
      (fun u : Y =>
        toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
          Kc hKc hα (A u))
      stateSet := by
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro u hu v hv
  have hnorm := norm_toCompactCoordFamilyLinearMap_sub_le_of_normLe
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα (h hu hv)
  simpa [dist_eq_norm] using hnorm

/-- Componentwise `C^{0,α}` difference estimates with finite Pi constants give a Lipschitz
estimate for the linear finite-cover readout of a finite Pi-valued parabolic function. -/
theorem lipschitzOnWith_toCompactCoordFamilyLinearMap_pi_of_component_normLe_sub
    {Y κ ι F : Type*} [PseudoMetricSpace Y] [Fintype κ] [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {stateSet : Set Y} (K : ι → ℝ≥0)
    {A : Y → parabolicC0AlphaSubmodule X (ι → F) α s}
    (h : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ i,
      ParabolicC0AlphaNormLe ((K i : ℝ) * dist u v) α
        (fun z => A u z i - A v z i) s) :
    LipschitzOnWith (∑ i, K i)
      (fun u : Y =>
        toCompactCoordFamilyLinearMap (X := X) (E := ι → F) (α := α) (s := s)
          Kc hKc hα (A u))
      stateSet := by
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro u hu v hv
  have hnorm := norm_toCompactCoordFamilyLinearMap_pi_sub_le_sum_mul_of_entries
    (X := X) (α := α) (s := s) Kc hKc hα
    (K := fun i => (K i : ℝ)) (R := dist u v)
    (fun i => NNReal.coe_nonneg (K i)) dist_nonneg (fun i => h hu hv i)
  simpa [dist_eq_norm, NNReal.coe_sum] using hnorm

/-- Pairwise sup-bound difference estimates give a Lipschitz estimate for the linear finite-cover
readout. -/
theorem lipschitzOnWith_toCompactCoordFamilyLinearMap_of_bounded_sub {Y κ : Type*}
    [PseudoMetricSpace Y] [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {stateSet : Set Y} {L : ℝ≥0} {A : Y → parabolicC0AlphaSubmodule X E α s}
    (h : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ParabolicBoundedWith ((L : ℝ) * dist u v) (fun z => A u z - A v z) s) :
    LipschitzOnWith L
      (fun u : Y =>
        toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
          Kc hKc hα (A u))
      stateSet := by
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro u hu v hv
  have hnorm := norm_toCompactCoordFamilyLinearMap_sub_le_of_bounded
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα
    (mul_nonneg (NNReal.coe_nonneg L) dist_nonneg) (h hu hv)
  simpa [dist_eq_norm] using hnorm

/-- Equality of all compact-piece readouts identifies the two functions on any covered subset. -/
theorem eqOn_subset_of_toCompactCoordFamily_eq {κ : Type*}
    {Kc : κ → TopologicalSpace.Compacts (ℝ × X)}
    {hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s} {hα : 0 < α}
    {t : Set (ℝ × X)} (hcover : t ⊆ ⋃ i, (Kc i : Set (ℝ × X)))
    {u v : parabolicC0AlphaSubmodule X E α s}
    (h :
      toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα u =
        toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα v) :
    EqOn u v t := by
  intro z hz
  rcases mem_iUnion.mp (hcover hz) with ⟨i, hzi⟩
  have hz_eq :
      toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα u i ⟨z, hzi⟩ =
        toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα v i ⟨z, hzi⟩ := by
    rw [h]
  simpa using hz_eq

/-- Equality of all compact-piece readouts identifies the two functions on the covered set. -/
theorem eqOn_of_toCompactCoordFamily_eq {κ : Type*}
    {Kc : κ → TopologicalSpace.Compacts (ℝ × X)}
    {hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s} {hα : 0 < α}
    (hcover : s ⊆ ⋃ i, (Kc i : Set (ℝ × X)))
    {u v : parabolicC0AlphaSubmodule X E α s}
    (h :
      toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα u =
        toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα v) :
    EqOn u v s :=
  eqOn_subset_of_toCompactCoordFamily_eq
    (X := X) (E := E) (α := α) (s := s) hcover h

/-- Product compact readouts determine functions on `Kt × U` whenever `U` is covered by the
spatial compact family. -/
theorem eqOn_timeSpaceProduct_of_toCompactCoordFamily_eq {κ : Type*}
    (Kt : TopologicalSpace.Compacts ℝ) (Kx : κ → TopologicalSpace.Compacts X)
    {hKc : ∀ i, (timeSpaceProductCompactFamily Kt Kx i : Set (ℝ × X)) ⊆ s}
    {hα : 0 < α} {U : Set X} (hU : U ⊆ ⋃ i, (Kx i : Set X))
    {u v : parabolicC0AlphaSubmodule X E α s}
    (h :
      toCompactCoordFamily (X := X) (E := E) (α := α) (s := s)
          (timeSpaceProductCompactFamily Kt Kx) hKc hα u =
        toCompactCoordFamily (X := X) (E := E) (α := α) (s := s)
          (timeSpaceProductCompactFamily Kt Kx) hKc hα v) :
    EqOn u v ((Kt : Set ℝ) ×ˢ U) :=
  eqOn_subset_of_toCompactCoordFamily_eq
    (X := X) (E := E) (α := α) (s := s)
    (Kc := timeSpaceProductCompactFamily Kt Kx) (hKc := hKc) (hα := hα)
    (timeSpaceProductCompactFamily_product_subset_iUnion_of_subset Kt Kx hU) h

/-- Interval product compact readouts determine functions on `Icc t₀ T × U` whenever `U` is
covered by the spatial compact family. -/
theorem eqOn_timeSpaceIccProduct_of_toCompactCoordFamily_eq {κ : Type*}
    (t₀ T : ℝ) (Kx : κ → TopologicalSpace.Compacts X)
    {hKc : ∀ i, (timeSpaceIccCompactFamily t₀ T Kx i : Set (ℝ × X)) ⊆ s}
    {hα : 0 < α} {U : Set X} (hU : U ⊆ ⋃ i, (Kx i : Set X))
    {u v : parabolicC0AlphaSubmodule X E α s}
    (h :
      toCompactCoordFamily (X := X) (E := E) (α := α) (s := s)
          (timeSpaceIccCompactFamily t₀ T Kx) hKc hα u =
        toCompactCoordFamily (X := X) (E := E) (α := α) (s := s)
          (timeSpaceIccCompactFamily t₀ T Kx) hKc hα v) :
    EqOn u v (Icc t₀ T ×ˢ U) :=
  eqOn_timeSpaceProduct_of_toCompactCoordFamily_eq
    (X := X) (E := E) (α := α) (s := s)
    (timeIccCompact t₀ T) Kx (hKc := hKc) (hα := hα) hU h

/-- Compact-piece readout is injective when the chosen compact pieces cover all time-space. -/
theorem toCompactCoordFamily_injective_of_iUnion_eq_univ {κ : Type*}
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ) :
    Function.Injective
      (toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα) := by
  intro u v h
  ext z
  have hzcover : z ∈ ⋃ i, (Kc i : Set (ℝ × X)) := by
    simp [hcover]
  rcases mem_iUnion.mp hzcover with ⟨i, hzi⟩
  have hz_eq :
      toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα u i ⟨z, hzi⟩ =
        toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα v i ⟨z, hzi⟩ := by
    rw [h]
  simpa using hz_eq

/-- The finite-cover value readout product target is complete when the value
model is complete. This is only completeness of the ambient compact-readout
target, not of the induced readout-image carrier. -/
theorem finiteCoverValueReadoutTarget_completeSpace {κ : Type*}
    [Fintype κ] [CompleteSpace E]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X)) :
    CompleteSpace (∀ i, C(Kc i, E)) := by
  letI : (i : κ) → CompleteSpace C(Kc i, E) := fun i =>
    (completeSpace_congr
      (ContinuousMap.isUniformEmbedding_equivBoundedOfCompact (Kc i) E)).2 inferInstance
  infer_instance

/-- The finite compact-family value readout induces a seminormed additive-group structure on the
lower parabolic submodule.  This is only a finite-cover readout norm; it is separated only when the
chosen compact pieces determine the underlying functions. -/
@[reducible] noncomputable def finiteCoverValueSeminormedAddCommGroup {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α) :
    SeminormedAddCommGroup (parabolicC0AlphaSubmodule X E α s) :=
  SeminormedAddCommGroup.induced
    (parabolicC0AlphaSubmodule X E α s) (∀ i, C(Kc i, E))
    (toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
      Kc hKc hα)

/-- The same finite compact-family value readout makes the lower parabolic submodule a seminormed
real vector space. -/
@[reducible] noncomputable def finiteCoverValueNormedSpace {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α) :
    @NormedSpace ℝ (parabolicC0AlphaSubmodule X E α s) _
      (finiteCoverValueSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα) :=
  NormedSpace.induced ℝ
    (parabolicC0AlphaSubmodule X E α s) (∀ i, C(Kc i, E))
    (toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
      Kc hKc hα)

/-- If the compact pieces cover all time-space, the finite compact-family readout norm is separated
and gives a genuine normed additive-group structure. -/
@[reducible] noncomputable def finiteCoverValueNormedAddCommGroupOfCover {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ) :
    NormedAddCommGroup (parabolicC0AlphaSubmodule X E α s) :=
  NormedAddCommGroup.induced
    (parabolicC0AlphaSubmodule X E α s) (∀ i, C(Kc i, E))
    (toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
      Kc hKc hα)
    (toCompactCoordFamily_injective_of_iUnion_eq_univ
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα hcover)

/-- The real vector-space structure paired with
`finiteCoverValueNormedAddCommGroupOfCover`. -/
@[reducible] noncomputable def finiteCoverValueNormedSpaceOfCover {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ) :
    @NormedSpace ℝ (parabolicC0AlphaSubmodule X E α s) _
      (finiteCoverValueNormedAddCommGroupOfCover
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα hcover).toSeminormedAddCommGroup :=
  finiteCoverValueNormedSpace (X := X) (E := E) (α := α) (s := s) Kc hKc hα

/-- With the finite-cover seminormed structure, the norm is definitionally the compact-family
readout norm. -/
theorem finiteCoverValue_norm_eq {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (u : parabolicC0AlphaSubmodule X E α s) :
    letI : SeminormedAddCommGroup (parabolicC0AlphaSubmodule X E α s) :=
      finiteCoverValueSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα
    ‖u‖ =
      ‖toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα u‖ :=
  rfl

/-- With the finite-cover seminormed structure, distance is definitionally the compact-family
readout distance. -/
theorem finiteCoverValue_dist_eq {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (u v : parabolicC0AlphaSubmodule X E α s) :
    letI : SeminormedAddCommGroup (parabolicC0AlphaSubmodule X E α s) :=
      finiteCoverValueSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα
    dist u v =
      dist
        (toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
          Kc hKc hα u)
        (toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
          Kc hKc hα v) :=
  rfl

/-- With the separated all-cover finite-cover value normed structure, the norm is
definitionally the compact-family readout norm. -/
theorem finiteCoverValue_norm_eq_ofCover {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ)
    (u : parabolicC0AlphaSubmodule X E α s) :
    letI : NormedAddCommGroup (parabolicC0AlphaSubmodule X E α s) :=
      finiteCoverValueNormedAddCommGroupOfCover
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα hcover
    ‖u‖ =
      ‖toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα u‖ :=
  rfl

/-- With the separated all-cover finite-cover value normed structure, distance is
definitionally the compact-family readout distance. -/
theorem finiteCoverValue_dist_eq_ofCover {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ)
    (u v : parabolicC0AlphaSubmodule X E α s) :
    letI : NormedAddCommGroup (parabolicC0AlphaSubmodule X E α s) :=
      finiteCoverValueNormedAddCommGroupOfCover
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα hcover
    dist u v =
      dist
        (toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
          Kc hKc hα u)
        (toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
          Kc hKc hα v) :=
  rfl

/-- A `C^{0,α}` norm-ball difference controls the induced finite-cover value distance. -/
theorem finiteCoverValue_dist_le_of_normLe_sub {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {N : ℝ} {u v : parabolicC0AlphaSubmodule X E α s}
    (h : ParabolicC0AlphaNormLe N α (fun z => u z - v z) s) :
    letI : SeminormedAddCommGroup (parabolicC0AlphaSubmodule X E α s) :=
      finiteCoverValueSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα
    dist u v ≤ N := by
  letI : SeminormedAddCommGroup (parabolicC0AlphaSubmodule X E α s) :=
    finiteCoverValueSeminormedAddCommGroup
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα
  rw [finiteCoverValue_dist_eq (X := X) (E := E) (α := α) (s := s)
    Kc hKc hα u v]
  simpa [dist_eq_norm] using
    norm_toCompactCoordFamilyLinearMap_sub_le_of_normLe
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα h

/-- A `C^{0,α}` norm-ball difference gives finite-cover value closed-ball membership. -/
theorem finiteCoverValue_mem_closedBall_of_normLe_sub {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {N : ℝ} {u v : parabolicC0AlphaSubmodule X E α s}
    (h : ParabolicC0AlphaNormLe N α (fun z => u z - v z) s) :
    letI : SeminormedAddCommGroup (parabolicC0AlphaSubmodule X E α s) :=
      finiteCoverValueSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα
    u ∈ Metric.closedBall v N := by
  letI : SeminormedAddCommGroup (parabolicC0AlphaSubmodule X E α s) :=
    finiteCoverValueSeminormedAddCommGroup
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα
  simpa [Metric.mem_closedBall] using
    finiteCoverValue_dist_le_of_normLe_sub
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα h

/-- Symmetric finite-cover value closed-ball membership from a `C^{0,α}` difference bound. -/
theorem finiteCoverValue_mem_closedBall_symm_of_normLe_sub {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {N : ℝ} {u v : parabolicC0AlphaSubmodule X E α s}
    (h : ParabolicC0AlphaNormLe N α (fun z => u z - v z) s) :
    letI : SeminormedAddCommGroup (parabolicC0AlphaSubmodule X E α s) :=
      finiteCoverValueSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα
    v ∈ Metric.closedBall u N := by
  letI : SeminormedAddCommGroup (parabolicC0AlphaSubmodule X E α s) :=
    finiteCoverValueSeminormedAddCommGroup
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα
  simpa [Metric.mem_closedBall, dist_comm] using
    finiteCoverValue_dist_le_of_normLe_sub
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα h

/-- Componentwise `C^{0,α}` difference controls with finite-Pi constants control the induced
finite-cover value distance. -/
theorem finiteCoverValue_dist_le_pi_of_component_normLe_sub
    {κ ι F : Type*} [Fintype κ] [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {R : ℝ} {K : ι → ℝ}
    {u v : parabolicC0AlphaSubmodule X (ι → F) α s}
    (hK_nonneg : ∀ i, 0 ≤ K i) (hR : 0 ≤ R)
    (h : ∀ i, ParabolicC0AlphaNormLe (K i * R) α
      (fun z => u z i - v z i) s) :
    letI : SeminormedAddCommGroup (parabolicC0AlphaSubmodule X (ι → F) α s) :=
      finiteCoverValueSeminormedAddCommGroup
        (X := X) (E := ι → F) (α := α) (s := s) Kc hKc hα
    dist u v ≤ (∑ i, K i) * R := by
  letI : SeminormedAddCommGroup (parabolicC0AlphaSubmodule X (ι → F) α s) :=
    finiteCoverValueSeminormedAddCommGroup
      (X := X) (E := ι → F) (α := α) (s := s) Kc hKc hα
  rw [finiteCoverValue_dist_eq (X := X) (E := ι → F) (α := α) (s := s)
    Kc hKc hα u v]
  simpa [dist_eq_norm] using
    norm_toCompactCoordFamilyLinearMap_pi_sub_le_sum_mul_of_entries
      (X := X) (α := α) (s := s) Kc hKc hα hK_nonneg hR h

/-- Componentwise `C^{0,α}` finite-Pi bounds give induced finite-cover value closed-ball
membership. -/
theorem finiteCoverValue_mem_closedBall_pi_of_component_normLe_sub
    {κ ι F : Type*} [Fintype κ] [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {R : ℝ} {K : ι → ℝ}
    {u v : parabolicC0AlphaSubmodule X (ι → F) α s}
    (hK_nonneg : ∀ i, 0 ≤ K i) (hR : 0 ≤ R)
    (h : ∀ i, ParabolicC0AlphaNormLe (K i * R) α
      (fun z => u z i - v z i) s) :
    letI : SeminormedAddCommGroup (parabolicC0AlphaSubmodule X (ι → F) α s) :=
      finiteCoverValueSeminormedAddCommGroup
        (X := X) (E := ι → F) (α := α) (s := s) Kc hKc hα
    u ∈ Metric.closedBall v ((∑ i, K i) * R) := by
  letI : SeminormedAddCommGroup (parabolicC0AlphaSubmodule X (ι → F) α s) :=
    finiteCoverValueSeminormedAddCommGroup
      (X := X) (E := ι → F) (α := α) (s := s) Kc hKc hα
  simpa [Metric.mem_closedBall] using
    finiteCoverValue_dist_le_pi_of_component_normLe_sub
      (X := X) (α := α) (s := s) Kc hKc hα hK_nonneg hR h

/-- Symmetric induced finite-cover value closed-ball membership from componentwise finite-Pi
`C^{0,α}` bounds. -/
theorem finiteCoverValue_mem_closedBall_symm_pi_of_component_normLe_sub
    {κ ι F : Type*} [Fintype κ] [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {R : ℝ} {K : ι → ℝ}
    {u v : parabolicC0AlphaSubmodule X (ι → F) α s}
    (hK_nonneg : ∀ i, 0 ≤ K i) (hR : 0 ≤ R)
    (h : ∀ i, ParabolicC0AlphaNormLe (K i * R) α
      (fun z => u z i - v z i) s) :
    letI : SeminormedAddCommGroup (parabolicC0AlphaSubmodule X (ι → F) α s) :=
      finiteCoverValueSeminormedAddCommGroup
        (X := X) (E := ι → F) (α := α) (s := s) Kc hKc hα
    v ∈ Metric.closedBall u ((∑ i, K i) * R) := by
  letI : SeminormedAddCommGroup (parabolicC0AlphaSubmodule X (ι → F) α s) :=
    finiteCoverValueSeminormedAddCommGroup
      (X := X) (E := ι → F) (α := α) (s := s) Kc hKc hα
  simpa [Metric.mem_closedBall, dist_comm] using
    finiteCoverValue_dist_le_pi_of_component_normLe_sub
      (X := X) (α := α) (s := s) Kc hKc hα hK_nonneg hR h

/-- A `C^{0,α}` norm-ball difference controls the separated all-cover finite-cover value
distance. -/
theorem finiteCoverValue_dist_le_of_normLe_sub_ofCover {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ)
    {N : ℝ} {u v : parabolicC0AlphaSubmodule X E α s}
    (h : ParabolicC0AlphaNormLe N α (fun z => u z - v z) s) :
    letI : NormedAddCommGroup (parabolicC0AlphaSubmodule X E α s) :=
      finiteCoverValueNormedAddCommGroupOfCover
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα hcover
    dist u v ≤ N := by
  letI : NormedAddCommGroup (parabolicC0AlphaSubmodule X E α s) :=
    finiteCoverValueNormedAddCommGroupOfCover
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα hcover
  rw [finiteCoverValue_dist_eq_ofCover (X := X) (E := E) (α := α) (s := s)
    Kc hKc hα hcover u v]
  simpa [dist_eq_norm] using
    norm_toCompactCoordFamilyLinearMap_sub_le_of_normLe
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα h

/-- A `C^{0,α}` norm-ball difference gives separated all-cover finite-cover value closed-ball
membership. -/
theorem finiteCoverValue_mem_closedBall_of_normLe_sub_ofCover {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ)
    {N : ℝ} {u v : parabolicC0AlphaSubmodule X E α s}
    (h : ParabolicC0AlphaNormLe N α (fun z => u z - v z) s) :
    letI : NormedAddCommGroup (parabolicC0AlphaSubmodule X E α s) :=
      finiteCoverValueNormedAddCommGroupOfCover
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα hcover
    u ∈ Metric.closedBall v N := by
  letI : NormedAddCommGroup (parabolicC0AlphaSubmodule X E α s) :=
    finiteCoverValueNormedAddCommGroupOfCover
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα hcover
  simpa [Metric.mem_closedBall] using
    finiteCoverValue_dist_le_of_normLe_sub_ofCover
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα hcover h

/-- Symmetric separated all-cover finite-cover value closed-ball membership from a `C^{0,α}`
difference bound. -/
theorem finiteCoverValue_mem_closedBall_symm_of_normLe_sub_ofCover {κ : Type*}
    [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ)
    {N : ℝ} {u v : parabolicC0AlphaSubmodule X E α s}
    (h : ParabolicC0AlphaNormLe N α (fun z => u z - v z) s) :
    letI : NormedAddCommGroup (parabolicC0AlphaSubmodule X E α s) :=
      finiteCoverValueNormedAddCommGroupOfCover
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα hcover
    v ∈ Metric.closedBall u N := by
  letI : NormedAddCommGroup (parabolicC0AlphaSubmodule X E α s) :=
    finiteCoverValueNormedAddCommGroupOfCover
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα hcover
  simpa [Metric.mem_closedBall, dist_comm] using
    finiteCoverValue_dist_le_of_normLe_sub_ofCover
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα hcover h

/-- Componentwise `C^{0,α}` difference controls with finite-Pi constants control the separated
all-cover finite-cover value distance. -/
theorem finiteCoverValue_dist_le_pi_of_component_normLe_sub_ofCover
    {κ ι F : Type*} [Fintype κ] [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ)
    {R : ℝ} {K : ι → ℝ}
    {u v : parabolicC0AlphaSubmodule X (ι → F) α s}
    (hK_nonneg : ∀ i, 0 ≤ K i) (hR : 0 ≤ R)
    (h : ∀ i, ParabolicC0AlphaNormLe (K i * R) α
      (fun z => u z i - v z i) s) :
    letI : NormedAddCommGroup (parabolicC0AlphaSubmodule X (ι → F) α s) :=
      finiteCoverValueNormedAddCommGroupOfCover
        (X := X) (E := ι → F) (α := α) (s := s) Kc hKc hα hcover
    dist u v ≤ (∑ i, K i) * R := by
  letI : NormedAddCommGroup (parabolicC0AlphaSubmodule X (ι → F) α s) :=
    finiteCoverValueNormedAddCommGroupOfCover
      (X := X) (E := ι → F) (α := α) (s := s) Kc hKc hα hcover
  rw [finiteCoverValue_dist_eq_ofCover (X := X) (E := ι → F) (α := α) (s := s)
    Kc hKc hα hcover u v]
  simpa [dist_eq_norm] using
    norm_toCompactCoordFamilyLinearMap_pi_sub_le_sum_mul_of_entries
      (X := X) (α := α) (s := s) Kc hKc hα hK_nonneg hR h

/-- Componentwise finite-Pi `C^{0,α}` bounds give separated all-cover finite-cover value
closed-ball membership. -/
theorem finiteCoverValue_mem_closedBall_pi_of_component_normLe_sub_ofCover
    {κ ι F : Type*} [Fintype κ] [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ)
    {R : ℝ} {K : ι → ℝ}
    {u v : parabolicC0AlphaSubmodule X (ι → F) α s}
    (hK_nonneg : ∀ i, 0 ≤ K i) (hR : 0 ≤ R)
    (h : ∀ i, ParabolicC0AlphaNormLe (K i * R) α
      (fun z => u z i - v z i) s) :
    letI : NormedAddCommGroup (parabolicC0AlphaSubmodule X (ι → F) α s) :=
      finiteCoverValueNormedAddCommGroupOfCover
        (X := X) (E := ι → F) (α := α) (s := s) Kc hKc hα hcover
    u ∈ Metric.closedBall v ((∑ i, K i) * R) := by
  letI : NormedAddCommGroup (parabolicC0AlphaSubmodule X (ι → F) α s) :=
    finiteCoverValueNormedAddCommGroupOfCover
      (X := X) (E := ι → F) (α := α) (s := s) Kc hKc hα hcover
  simpa [Metric.mem_closedBall] using
    finiteCoverValue_dist_le_pi_of_component_normLe_sub_ofCover
      (X := X) (α := α) (s := s) Kc hKc hα hcover hK_nonneg hR h

/-- Symmetric separated all-cover finite-cover value closed-ball membership from componentwise
finite-Pi `C^{0,α}` bounds. -/
theorem finiteCoverValue_mem_closedBall_symm_pi_of_component_normLe_sub_ofCover
    {κ ι F : Type*} [Fintype κ] [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ)
    {R : ℝ} {K : ι → ℝ}
    {u v : parabolicC0AlphaSubmodule X (ι → F) α s}
    (hK_nonneg : ∀ i, 0 ≤ K i) (hR : 0 ≤ R)
    (h : ∀ i, ParabolicC0AlphaNormLe (K i * R) α
      (fun z => u z i - v z i) s) :
    letI : NormedAddCommGroup (parabolicC0AlphaSubmodule X (ι → F) α s) :=
      finiteCoverValueNormedAddCommGroupOfCover
        (X := X) (E := ι → F) (α := α) (s := s) Kc hKc hα hcover
    v ∈ Metric.closedBall u ((∑ i, K i) * R) := by
  letI : NormedAddCommGroup (parabolicC0AlphaSubmodule X (ι → F) α s) :=
    finiteCoverValueNormedAddCommGroupOfCover
      (X := X) (E := ι → F) (α := α) (s := s) Kc hKc hα hcover
  simpa [Metric.mem_closedBall, dist_comm] using
    finiteCoverValue_dist_le_pi_of_component_normLe_sub_ofCover
      (X := X) (α := α) (s := s) Kc hKc hα hcover hK_nonneg hR h

/-- Pairwise componentwise `C^{0,α}` estimates give a Lipschitz estimate in the induced
finite-cover value seminorm. -/
theorem lipschitzOnWith_finiteCoverValue_pi_of_component_normLe_sub
    {Y κ ι F : Type*} [PseudoMetricSpace Y] [Fintype κ] [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {stateSet : Set Y} {K : ι → ℝ≥0}
    {A : Y → parabolicC0AlphaSubmodule X (ι → F) α s}
    (h : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ i,
      ParabolicC0AlphaNormLe ((K i : ℝ) * dist u v) α
        (fun z => A u z i - A v z i) s) :
    letI : SeminormedAddCommGroup (parabolicC0AlphaSubmodule X (ι → F) α s) :=
      finiteCoverValueSeminormedAddCommGroup
        (X := X) (E := ι → F) (α := α) (s := s) Kc hKc hα
    LipschitzOnWith (∑ i, K i) A stateSet := by
  letI : SeminormedAddCommGroup (parabolicC0AlphaSubmodule X (ι → F) α s) :=
    finiteCoverValueSeminormedAddCommGroup
      (X := X) (E := ι → F) (α := α) (s := s) Kc hKc hα
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro u hu v hv
  have hdist :
      dist (A u) (A v) ≤ (∑ i, (K i : ℝ)) * dist u v :=
    finiteCoverValue_dist_le_pi_of_component_normLe_sub
      (X := X) (α := α) (s := s) Kc hKc hα
      (R := dist u v) (K := fun i => (K i : ℝ)) (u := A u) (v := A v)
      (fun i => (K i).2) dist_nonneg (h hu hv)
  simpa [NNReal.coe_sum] using hdist

/-- Pairwise componentwise `C^{0,α}` estimates give a Lipschitz estimate in the separated
all-cover finite-cover value norm. -/
theorem lipschitzOnWith_finiteCoverValue_pi_of_component_normLe_sub_ofCover
    {Y κ ι F : Type*} [PseudoMetricSpace Y] [Fintype κ] [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ)
    {stateSet : Set Y} {K : ι → ℝ≥0}
    {A : Y → parabolicC0AlphaSubmodule X (ι → F) α s}
    (h : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ i,
      ParabolicC0AlphaNormLe ((K i : ℝ) * dist u v) α
        (fun z => A u z i - A v z i) s) :
    letI : NormedAddCommGroup (parabolicC0AlphaSubmodule X (ι → F) α s) :=
      finiteCoverValueNormedAddCommGroupOfCover
        (X := X) (E := ι → F) (α := α) (s := s) Kc hKc hα hcover
    LipschitzOnWith (∑ i, K i) A stateSet := by
  letI : NormedAddCommGroup (parabolicC0AlphaSubmodule X (ι → F) α s) :=
    finiteCoverValueNormedAddCommGroupOfCover
      (X := X) (E := ι → F) (α := α) (s := s) Kc hKc hα hcover
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro u hu v hv
  have hdist :
      dist (A u) (A v) ≤ (∑ i, (K i : ℝ)) * dist u v :=
    finiteCoverValue_dist_le_pi_of_component_normLe_sub_ofCover
      (X := X) (α := α) (s := s) Kc hKc hα hcover
      (R := dist u v) (K := fun i => (K i : ℝ)) (u := A u) (v := A v)
      (fun i => (K i).2) dist_nonneg (h hu hv)
  simpa [NNReal.coe_sum] using hdist

/-- The finite-cover value readout is an isometry for its induced seminormed structure. -/
theorem finiteCoverValue_readout_isometry {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α) :
    letI : SeminormedAddCommGroup (parabolicC0AlphaSubmodule X E α s) :=
      finiteCoverValueSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα
    Isometry
      (fun u : parabolicC0AlphaSubmodule X E α s =>
        toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
          Kc hKc hα u) := by
  letI : SeminormedAddCommGroup (parabolicC0AlphaSubmodule X E α s) :=
    finiteCoverValueSeminormedAddCommGroup
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα
  exact Isometry.of_dist_eq fun u v =>
    (finiteCoverValue_dist_eq (X := X) (E := E) (α := α) (s := s)
      Kc hKc hα u v).symm

/-- The finite-cover value readout is nonexpansive for its induced seminormed structure. -/
theorem finiteCoverValue_readout_dist_le {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (u v : parabolicC0AlphaSubmodule X E α s) :
    letI : SeminormedAddCommGroup (parabolicC0AlphaSubmodule X E α s) :=
      finiteCoverValueSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα
    dist
      (toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα u)
      (toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα v) ≤ dist u v := by
  letI : SeminormedAddCommGroup (parabolicC0AlphaSubmodule X E α s) :=
    finiteCoverValueSeminormedAddCommGroup
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα
  rw [finiteCoverValue_dist_eq (X := X) (E := E) (α := α) (s := s)
    Kc hKc hα u v]

/-- The finite-cover value readout is `1`-Lipschitz for its induced seminormed structure. -/
theorem finiteCoverValue_readout_lipschitzOnWith {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (stateSet : Set (parabolicC0AlphaSubmodule X E α s)) :
    letI : SeminormedAddCommGroup (parabolicC0AlphaSubmodule X E α s) :=
      finiteCoverValueSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα
    LipschitzOnWith 1
      (fun u : parabolicC0AlphaSubmodule X E α s =>
        toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
          Kc hKc hα u)
      stateSet := by
  letI : SeminormedAddCommGroup (parabolicC0AlphaSubmodule X E α s) :=
    finiteCoverValueSeminormedAddCommGroup
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα
  refine LipschitzOnWith.of_dist_le_mul
    (α := parabolicC0AlphaSubmodule X E α s) (β := ∀ i, C(Kc i, E))
    (K := (1 : ℝ≥0)) (s := stateSet)
    (f := fun u : parabolicC0AlphaSubmodule X E α s =>
      toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα u) ?_
  intro u _hu v _hv
  simpa [one_mul] using
    finiteCoverValue_readout_dist_le
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα u v

/-- For the separated all-cover norm, the finite-cover value readout is an isometry. -/
theorem finiteCoverValue_readout_isometry_ofCover {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ) :
    letI : NormedAddCommGroup (parabolicC0AlphaSubmodule X E α s) :=
      finiteCoverValueNormedAddCommGroupOfCover
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα hcover
    Isometry
      (fun u : parabolicC0AlphaSubmodule X E α s =>
        toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
          Kc hKc hα u) := by
  letI : NormedAddCommGroup (parabolicC0AlphaSubmodule X E α s) :=
    finiteCoverValueNormedAddCommGroupOfCover
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα hcover
  exact Isometry.of_dist_eq fun u v =>
    (finiteCoverValue_dist_eq_ofCover
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα hcover u v).symm

/-- For the separated all-cover norm, the finite-cover value readout is nonexpansive. -/
theorem finiteCoverValue_readout_dist_le_ofCover {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ)
    (u v : parabolicC0AlphaSubmodule X E α s) :
    letI : NormedAddCommGroup (parabolicC0AlphaSubmodule X E α s) :=
      finiteCoverValueNormedAddCommGroupOfCover
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα hcover
    dist
      (toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα u)
      (toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα v) ≤ dist u v := by
  letI : NormedAddCommGroup (parabolicC0AlphaSubmodule X E α s) :=
    finiteCoverValueNormedAddCommGroupOfCover
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα hcover
  rw [finiteCoverValue_dist_eq_ofCover (X := X) (E := E) (α := α) (s := s)
    Kc hKc hα hcover u v]

/-- For the separated all-cover norm, the finite-cover value readout is `1`-Lipschitz on any
state set. -/
theorem finiteCoverValue_readout_lipschitzOnWith_ofCover {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ)
    (stateSet : Set (parabolicC0AlphaSubmodule X E α s)) :
    letI : NormedAddCommGroup (parabolicC0AlphaSubmodule X E α s) :=
      finiteCoverValueNormedAddCommGroupOfCover
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα hcover
    LipschitzOnWith 1
      (fun u : parabolicC0AlphaSubmodule X E α s =>
        toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
          Kc hKc hα u)
      stateSet := by
  letI : NormedAddCommGroup (parabolicC0AlphaSubmodule X E α s) :=
    finiteCoverValueNormedAddCommGroupOfCover
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα hcover
  refine LipschitzOnWith.of_dist_le_mul
    (α := parabolicC0AlphaSubmodule X E α s) (β := ∀ i, C(Kc i, E))
    (K := (1 : ℝ≥0)) (s := stateSet)
    (f := fun u : parabolicC0AlphaSubmodule X E α s =>
      toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα u) ?_
  intro u _hu v _hv
  simpa [one_mul] using
    finiteCoverValue_readout_dist_le_ofCover
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα hcover u v

/-- Fixed-time spatial value readout estimate for the finite-cover value seminorm, after the
time-space compact pieces cover the requested spatial slices. -/
theorem finiteCoverValue_timeSlice_spatial_dist_le
    {η κ : Type*} [Fintype κ]
    (Kdom : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKdom : ∀ j, (Kdom j : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (Kx : η → TopologicalSpace.Compacts X)
    {timeSet : Set ℝ}
    (stateSet : Set (parabolicC0AlphaSubmodule X E α s))
    (hcover : ∀ τ, τ ∈ timeSet → ∀ i (x : Kx i),
      ∃ j, (τ, x.1) ∈ (Kdom j : Set (ℝ × X))) :
    letI : SeminormedAddCommGroup (parabolicC0AlphaSubmodule X E α s) :=
      finiteCoverValueSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kdom hKdom hα
    ∀ τ, τ ∈ timeSet → ∀ ⦃u : parabolicC0AlphaSubmodule X E α s⦄,
      u ∈ stateSet → ∀ ⦃v : parabolicC0AlphaSubmodule X E α s⦄, v ∈ stateSet →
        ∀ i (x : Kx i), dist (u (τ, x.1)) (v (τ, x.1)) ≤ dist u v := by
  letI : SeminormedAddCommGroup (parabolicC0AlphaSubmodule X E α s) :=
    finiteCoverValueSeminormedAddCommGroup
      (X := X) (E := E) (α := α) (s := s) Kdom hKdom hα
  have hLip : ∀ τ, τ ∈ timeSet →
      LipschitzOnWith (1 : ℝ≥0)
        (fun u : parabolicC0AlphaSubmodule X E α s =>
          toCompactCoordFamily (X := X) (E := E) (α := α) (s := s)
            Kdom hKdom hα u)
        stateSet := by
    intro _τ _hτ
    simpa using
      finiteCoverValue_readout_lipschitzOnWith
        (X := X) (E := E) (α := α) (s := s) Kdom hKdom hα stateSet
  have h := forall_timeSlice_spatial_dist_le_of_toCompactCoordFamily_lipschitzOnWith
    (X := X) (E := E) (α := α) (s := s)
    Kdom hKdom hα Kx (timeSet := timeSet) (stateSet := stateSet)
    (A := fun _τ u => u) hLip hcover
  simpa [one_mul] using h

/-- Fixed-time spatial value readout estimate for the separated all-cover finite-cover value
norm. -/
theorem finiteCoverValue_timeSlice_spatial_dist_le_ofCover
    {η κ : Type*} [Fintype κ]
    (Kdom : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKdom : ∀ j, (Kdom j : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (Kx : η → TopologicalSpace.Compacts X)
    {timeSet : Set ℝ}
    (hcover : (⋃ j, (Kdom j : Set (ℝ × X))) = Set.univ)
    (stateSet : Set (parabolicC0AlphaSubmodule X E α s)) :
    letI : NormedAddCommGroup (parabolicC0AlphaSubmodule X E α s) :=
      finiteCoverValueNormedAddCommGroupOfCover
        (X := X) (E := E) (α := α) (s := s) Kdom hKdom hα hcover
    ∀ τ, τ ∈ timeSet → ∀ ⦃u : parabolicC0AlphaSubmodule X E α s⦄,
      u ∈ stateSet → ∀ ⦃v : parabolicC0AlphaSubmodule X E α s⦄, v ∈ stateSet →
        ∀ i (x : Kx i), dist (u (τ, x.1)) (v (τ, x.1)) ≤ dist u v := by
  letI : NormedAddCommGroup (parabolicC0AlphaSubmodule X E α s) :=
    finiteCoverValueNormedAddCommGroupOfCover
      (X := X) (E := E) (α := α) (s := s) Kdom hKdom hα hcover
  have hLip : ∀ τ, τ ∈ timeSet →
      LipschitzOnWith (1 : ℝ≥0)
        (fun u : parabolicC0AlphaSubmodule X E α s =>
          toCompactCoordFamily (X := X) (E := E) (α := α) (s := s)
            Kdom hKdom hα u)
        stateSet := by
    intro _τ _hτ
    simpa using
      finiteCoverValue_readout_lipschitzOnWith_ofCover
        (X := X) (E := E) (α := α) (s := s) Kdom hKdom hα hcover stateSet
  have h := forall_timeSlice_spatial_dist_le_of_toCompactCoordFamily_lipschitzOnWith_ofCover
    (X := X) (E := E) (α := α) (s := s)
    Kdom hKdom hα Kx (timeSet := timeSet) (stateSet := stateSet)
    (A := fun _τ u => u) hLip hcover
  simpa [one_mul] using h

/-- The parabolic `C^{0,α}` norm packaged as a bundled `AddGroupSeminorm` on the submodule of
parabolic `C^{0,α}` functions: it satisfies `toFun 0 = 0`, the triangle inequality, and negation
invariance.  This is the bundled seminorm underlying the parabolic `C^{0,α}` (semi)normed space. -/
noncomputable def addGroupSeminorm (α : ℝ) (s : Set (ℝ × X)) :
    AddGroupSeminorm (parabolicC0AlphaSubmodule X E α s) where
  toFun u := parabolicC0AlphaNorm α u.1 s
  map_zero' := by
    change parabolicC0AlphaNorm α (fun _ : ℝ × X => (0 : E)) s = 0
    exact parabolicC0AlphaNorm_zero α s
  add_le' u v := by
    change parabolicC0AlphaNorm α (fun z => u.1 z + v.1 z) s ≤
      parabolicC0AlphaNorm α u.1 s + parabolicC0AlphaNorm α v.1 s
    exact parabolicC0AlphaNorm_add_le u.2 v.2
  neg' u := by
    change parabolicC0AlphaNorm α (fun z => -u.1 z) s =
      parabolicC0AlphaNorm α u.1 s
    exact parabolicC0AlphaNorm_neg α u.1 s

/-- The bundled parabolic `C^{0,α}` `AddGroupSeminorm` evaluates to the parabolic `C^{0,α}` norm
of the underlying function. -/
@[simp]
theorem addGroupSeminorm_apply (α : ℝ) (s : Set (ℝ × X))
    (u : parabolicC0AlphaSubmodule X E α s) :
    addGroupSeminorm α s u = parabolicC0AlphaNorm α u.1 s :=
  rfl

/-- The parabolic `C^{0,α}` norm packaged as a genuine real-scalar `Seminorm` on the submodule of
parabolic `C^{0,α}` functions: it adds scalar homogeneity `‖c • u‖ = ‖c‖ ‖u‖` to the additive
seminorm axioms.  This is the bundled `Seminorm ℝ` underlying the `NormedSpace ℝ` structure of the
parabolic Hölder space. -/
noncomputable def seminorm (α : ℝ) (s : Set (ℝ × X)) :
    Seminorm ℝ (parabolicC0AlphaSubmodule X E α s) :=
  { addGroupSeminorm α s with
    smul' := fun c u => by
      change parabolicC0AlphaNorm α (fun z => c • u.1 z) s =
        ‖c‖ * parabolicC0AlphaNorm α u.1 s
      exact parabolicC0AlphaNorm_const_smul c u.2 }

/-- The bundled parabolic `C^{0,α}` `Seminorm` evaluates to the parabolic `C^{0,α}` norm of the
underlying function. -/
@[simp]
theorem seminorm_apply (α : ℝ) (s : Set (ℝ × X))
    (u : parabolicC0AlphaSubmodule X E α s) :
    seminorm α s u = parabolicC0AlphaNorm α u.1 s :=
  rfl

/-- The parabolic `C^{0,α}` seminormed additive-group structure on the submodule of parabolic
`C^{0,α}` functions, built from the bundled `AddGroupSeminorm`.  Under this structure the norm is
`‖u‖ = parabolicC0AlphaNorm α u.1 s`.  It is supplied as a `def` (not a global instance) because
the underlying function-space subtype already carries the pointwise product topology; the honest
separated `NormedAddCommGroup`/`CompleteSpace` Banach instances belong on a dedicated type synonym
that isolates the parabolic Hölder topology. -/
@[reducible] noncomputable def seminormedAddCommGroup (α : ℝ) (s : Set (ℝ × X)) :
    SeminormedAddCommGroup (parabolicC0AlphaSubmodule X E α s) :=
  AddGroupSeminorm.toSeminormedAddCommGroup (addGroupSeminorm α s)

/-- Under the parabolic `C^{0,α}` seminormed structure, the norm of a bundled function is its
parabolic `C^{0,α}` norm. -/
theorem seminormedAddCommGroup_norm (α : ℝ) (s : Set (ℝ × X))
    (u : parabolicC0AlphaSubmodule X E α s) :
    (seminormedAddCommGroup α s).toNorm.norm u = parabolicC0AlphaNorm α u.1 s :=
  rfl

/-- Under the parabolic `C^{0,α}` seminormed structure, distance between two bundled functions is
the parabolic `C^{0,α}` norm of their pointwise difference. -/
theorem seminormedAddCommGroup_dist (α : ℝ) (s : Set (ℝ × X))
    (u v : parabolicC0AlphaSubmodule X E α s) :
    letI := seminormedAddCommGroup (X := X) (E := E) α s
    dist u v = parabolicC0AlphaNorm α (fun z => u.1 z - v.1 z) s := by
  letI := seminormedAddCommGroup (X := X) (E := E) α s
  rw [dist_eq_norm]
  change parabolicC0AlphaNorm α (fun z => u.1 z - v.1 z) s = _
  rfl

/-- **Completeness of the parabolic `C^{0,α}` seminormed space.**  Under the bundled parabolic
`C^{0,α}` seminormed structure, every `C^{0,α}`-norm-Cauchy sequence of parabolic `C^{0,α}` functions
converges in the `C^{0,α}` norm to a parabolic `C^{0,α}` function.  This is the completeness half of
the parabolic Hölder Banach space, packaged as a `CompleteSpace` fact for the seminormed submodule;
it is assembled from `Metric.complete_of_cauchySeq_tendsto` and the sequential completeness
`exists_parabolicC0AlphaOn_tendsto_of_cauchy`.  (The structure is a genuine `NormedAddCommGroup`
once the underlying functions are determined by their restriction to `s`, e.g. on a type synonym or
after a quotient; completeness holds already at the seminormed level.) -/
theorem completeSpace [CompleteSpace E] (α : ℝ) (s : Set (ℝ × X)) :
    @CompleteSpace (parabolicC0AlphaSubmodule X E α s)
      (seminormedAddCommGroup (X := X) (E := E) α s).toPseudoMetricSpace.toUniformSpace := by
  letI := seminormedAddCommGroup (X := X) (E := E) α s
  refine @Metric.complete_of_cauchySeq_tendsto (parabolicC0AlphaSubmodule X E α s) _ ?_
  intro u hu
  rw [Metric.cauchySeq_iff] at hu
  have hf : ∀ n, ParabolicC0AlphaOn α ((u n : ℝ × X → E)) s := fun n => (u n).2
  have hcauchy : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      parabolicC0AlphaNorm α (fun z => (u m : ℝ × X → E) z - (u n : ℝ × X → E) z) s ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hu ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    have h := hN m hm n hn
    rw [seminormedAddCommGroup_dist] at h
    exact h.le
  obtain ⟨g, hg_class, hg_conv⟩ :=
    exists_parabolicC0AlphaOn_tendsto_of_cauchy hf hcauchy
  refine ⟨⟨g, hg_class⟩, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := hg_conv (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  rw [seminormedAddCommGroup_dist]
  exact lt_of_le_of_lt (hN n hn) (by linarith)

/-- **The parabolic `C^{0,α}` seminormed structure is a seminormed real vector space.**  Scalar
multiplication is norm-compatible (`‖c • u‖ ≤ ‖c‖ ‖u‖`, in fact with equality), so the parabolic
`C^{0,α}` seminorm structure carries a `NormedSpace ℝ`.  Combined with `completeSpace` this exhibits
the parabolic Hölder space as a complete seminormed `ℝ`-vector space (a semi-Banach space); it
becomes a genuine Banach space once the underlying functions are separated by their restriction to
`s`. -/
noncomputable def normedSpace (α : ℝ) (s : Set (ℝ × X)) :
    @NormedSpace ℝ (parabolicC0AlphaSubmodule X E α s) _
      (seminormedAddCommGroup (X := X) (E := E) α s) :=
  letI := seminormedAddCommGroup (X := X) (E := E) α s
  { (inferInstance : Module ℝ (parabolicC0AlphaSubmodule X E α s)) with
    norm_smul_le := fun c u => by
      have hbound := parabolicC0AlphaNorm_const_smul_le
        (X := X) (E := E) (𝕜 := ℝ) (α := α) (s := s) c u.2
      change parabolicC0AlphaNorm α (fun z => c • u.1 z) s ≤
        ‖c‖ * parabolicC0AlphaNorm α u.1 s
      exact hbound }

end parabolicC0AlphaSubmodule

end AnalyticPDE
end RicciFlow
