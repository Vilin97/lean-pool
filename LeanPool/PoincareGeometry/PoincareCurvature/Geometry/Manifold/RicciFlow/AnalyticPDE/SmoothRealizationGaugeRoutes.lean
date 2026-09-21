/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.SmoothRealization
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.Diffeomorph3FlowTimeDerivative
/-!
# Raw-gauge routes from smooth Ricci-DeTurck realizations

This thin module keeps the heavy smooth-realization construction unchanged and
adds endpoint projections that explicitly pass through the raw identity `C^3`
gauge-flow and named scalar time-derivative interfaces.
-/

@[expose] public noncomputable section

open Set
open scoped Bundle Manifold ContDiff NNReal Topology

namespace RicciFlow
namespace AnalyticPDE
namespace MetricLocusEvolution

open PoincareCurvature.Bundle.Trivialization
open PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace

variable {M : Type*} [TopologicalSpace M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

local notation "BilF" => (F →L[ℝ] F →L[ℝ] ℝ)

local instance gaugeRoutesBilFNormedAddCommGroup : NormedAddCommGroup BilF :=
  (inferInstance : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ))

local instance gaugeRoutesBilFNormedSpace : NormedSpace ℝ BilF :=
  (inferInstance : NormedSpace ℝ (F →L[ℝ] F →L[ℝ] ℝ))

private theorem continuousMap_moving_eval_sub_const_hasDerivWithinAt
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : ℝ → C(K, E)} {u' : C(K, E)} {s : Set ℝ} {t : ℝ}
    (hu : HasDerivWithinAt u u' s t)
    {x : ℝ → K} (hx : Filter.Tendsto x (𝓝[s] t) (𝓝 (x t))) :
    HasDerivWithinAt (fun τ : ℝ ↦ u τ (x τ) - u t (x τ)) (u' (x t)) s t := by
  have hrem :
      (fun τ : ℝ ↦ (u τ - u t - (τ - t) • u') (x τ)) =o[𝓝[s] t]
        fun τ : ℝ ↦ τ - t := by
    refine Asymptotics.IsLittleO.of_bound ?_
    intro c hc
    filter_upwards [Asymptotics.IsLittleO.bound hu.isLittleO hc] with τ hτ
    exact (ContinuousMap.norm_coe_le_norm (u τ - u t - (τ - t) • u') (x τ)).trans hτ
  have hderiv_eval_tendsto :
      Filter.Tendsto (fun τ : ℝ ↦ u' (x τ) - u' (x t)) (𝓝[s] t) (𝓝 0) := by
    have hu'_tendsto :
        Filter.Tendsto (fun y : K ↦ u' y) (𝓝 (x t)) (𝓝 (u' (x t))) :=
      map_continuousAt u' (x t)
    have hconst :
        Filter.Tendsto (fun _ : ℝ ↦ u' (x t)) (𝓝[s] t) (𝓝 (u' (x t))) :=
      tendsto_const_nhds
    simpa using (hu'_tendsto.comp hx).sub hconst
  have hderiv_eval :
      (fun τ : ℝ ↦ u' (x τ) - u' (x t)) =o[𝓝[s] t]
        fun _ : ℝ ↦ (1 : ℝ) :=
    (Asymptotics.isLittleO_one_iff ℝ).2 hderiv_eval_tendsto
  have htime :
      (fun τ : ℝ ↦ τ - t) =O[𝓝[s] t] fun τ : ℝ ↦ τ - t :=
    Asymptotics.isBigO_refl _ _
  have hmove :
      (fun τ : ℝ ↦ (τ - t) • (u' (x τ) - u' (x t))) =o[𝓝[s] t]
        fun τ : ℝ ↦ τ - t := by
    simpa using htime.smul_isLittleO hderiv_eval
  have htotal :
      (fun τ : ℝ ↦
        (u τ - u t - (τ - t) • u') (x τ) +
          (τ - t) • (u' (x τ) - u' (x t))) =o[𝓝[s] t]
        fun τ : ℝ ↦ τ - t :=
    hrem.add hmove
  refine HasDerivWithinAt.of_isLittleO ?_
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, smul_sub] using htotal

private theorem continuousMap_moving_eval_sub_const_hasDerivAt
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : ℝ → C(K, E)} {u' : C(K, E)} {t : ℝ}
    (hu : HasDerivAt u u' t)
    {x : ℝ → K} (hx : Filter.Tendsto x (𝓝 t) (𝓝 (x t))) :
    HasDerivAt (fun τ : ℝ ↦ u τ (x τ) - u t (x τ)) (u' (x t)) t := by
  rw [← hasDerivWithinAt_univ] at hu ⊢
  exact continuousMap_moving_eval_sub_const_hasDerivWithinAt hu (by simpa using hx)

section MovingCoordinateHelpers

variable {W : M → Type*} [TopologicalSpace (_root_.Bundle.TotalSpace F W)]
  [∀ x, TopologicalSpace (W x)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)]
  [FiberBundle F W] [VectorBundle ℝ F W]

local notation "BilW" => (_root_.Bundle.BilinearFormBundle (V := W))

private theorem coordBilinearFormReadoutMap_timeDifference_hasDerivAt_of_mem_Ioo_forGaugeRoutes
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ → ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover)}
    {t₀ : ℝ}
    {g₀ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover}
    (sol : BanachEvolutionLocalSolutionIn A stateSet t₀ g₀)
    (i : κ) {x : ℝ → Kc i}
    {t : ℝ} (ht : t ∈ Ioo t₀ sol.terminalTime)
    (hx : Filter.Tendsto x (𝓝 t) (𝓝 (x t))) :
    HasDerivAt
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
          (sol.curve τ)).1 i (x τ) -
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
          (sol.curve t)).1 i (x τ))
      ((equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
          (A t (sol.curve t))).1 i (x t)) t := by
  let L :
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
          et Kc hKc Ko hKo hKoEq hcover →L[ℝ] C(Kc i, BilF) :=
    (ContinuousLinearMap.proj i).comp
      (((compatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) et Kc hKc Ko hKo).subtypeL).comp
        (toCompatibleCoordFamilySubmoduleContinuousLinearMap
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover))
  have hcomponent :
      HasDerivAt (fun τ : ℝ ↦ L (sol.curve τ)) (L (A t (sol.curve t))) t :=
    BanachEvolutionLocalSolutionIn.continuousLinearMap_hasDerivAt_of_mem_Ioo
      (F := A) (stateSet := stateSet) L sol ht
  simpa [L] using continuousMap_moving_eval_sub_const_hasDerivAt hcomponent hx

private theorem coordBilinearFormReadoutMap_timeDifference_hasDerivWithinAt_Ici_of_mem_Ico_forGaugeRoutes
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ → ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover)}
    {t₀ : ℝ}
    {g₀ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover}
    (sol : BanachEvolutionLocalSolutionIn A stateSet t₀ g₀)
    (i : κ) {x : ℝ → Kc i}
    {t : ℝ} (ht : t ∈ Ico t₀ sol.terminalTime)
    (hx : Filter.Tendsto x (𝓝[Ici t] t) (𝓝 (x t))) :
    HasDerivWithinAt
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
          (sol.curve τ)).1 i (x τ) -
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
          (sol.curve t)).1 i (x τ))
      ((equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
          (A t (sol.curve t))).1 i (x t)) (Ici t) t := by
  let L :
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
          et Kc hKc Ko hKo hKoEq hcover →L[ℝ] C(Kc i, BilF) :=
    (ContinuousLinearMap.proj i).comp
      (((compatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) et Kc hKc Ko hKo).subtypeL).comp
        (toCompatibleCoordFamilySubmoduleContinuousLinearMap
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover))
  have hcomponent :
      HasDerivWithinAt (fun τ : ℝ ↦ L (sol.curve τ))
        (L (A t (sol.curve t))) (Ici t) t :=
    BanachEvolutionLocalSolutionIn.continuousLinearMap_hasDerivWithinAt_Ici_of_mem_Ico
      (F := A) (stateSet := stateSet) L sol ht
  simpa [L] using continuousMap_moving_eval_sub_const_hasDerivWithinAt hcomponent hx

end MovingCoordinateHelpers

private noncomputable def compactCurveOfEventuallyMem
    (K : Set M) (y : ℝ → M) (t : ℝ) (hy_t : y t ∈ K) : ℝ → K :=
  by
    classical
    exact fun τ ↦ if hτ : y τ ∈ K then ⟨y τ, hτ⟩ else ⟨y t, hy_t⟩

private theorem compactCurveOfEventuallyMem_eventually_val_eq
    {K : Set M} {y : ℝ → M} {t : ℝ} {hy_t : y t ∈ K}
    {l : Filter ℝ} (hmem : ∀ᶠ τ in l, y τ ∈ K) :
    (fun τ : ℝ ↦ (compactCurveOfEventuallyMem K y t hy_t τ).1) =ᶠ[l] y := by
  filter_upwards [hmem] with τ hτ
  simp [compactCurveOfEventuallyMem, hτ]

private theorem compactCurveOfEventuallyMem_tendsto
    {K : Set M} {y : ℝ → M} {t : ℝ} {hy_t : y t ∈ K}
    {l : Filter ℝ}
    (hy : Filter.Tendsto y l (𝓝 (y t)))
    (hmem : ∀ᶠ τ in l, y τ ∈ K) :
    Filter.Tendsto (compactCurveOfEventuallyMem K y t hy_t)
      l (𝓝 (compactCurveOfEventuallyMem K y t hy_t t)) := by
  rw [tendsto_subtype_rng]
  have htarget :
      (compactCurveOfEventuallyMem K y t hy_t t).1 = y t := by
    simp [compactCurveOfEventuallyMem, hy_t]
  rw [htarget]
  exact Filter.Tendsto.congr'
    (compactCurveOfEventuallyMem_eventually_val_eq (K := K) (y := y) (t := t)
      (hy_t := hy_t) hmem).symm hy

private theorem eventually_mem_of_tendsto_of_mem_interior
    {K : Set M} {y : ℝ → M} {t : ℝ} {l : Filter ℝ}
    (hy : Filter.Tendsto y l (𝓝 (y t)))
    (hmem : y t ∈ interior K) :
    ∀ᶠ τ in l, y τ ∈ K := by
  filter_upwards [hy (isOpen_interior.mem_nhds hmem)] with τ hτ
  exact interior_subset hτ

/-- A point in the interior of a compact-cover piece and in an open target
patch admits a smaller compact neighborhood contained in both.  This is the
topological selection step needed by the target-centered gauge readout. -/
private theorem exists_compact_subset_interior_inter_open
    [LocallyCompactSpace M] {p : M} {K₀ U : Set M}
    (hpK : p ∈ interior K₀) (hUopen : IsOpen U) (hpU : p ∈ U) :
    ∃ K : TopologicalSpace.Compacts M,
      p ∈ interior (K : Set M) ∧ (K : Set M) ⊆ K₀ ∧ (K : Set M) ⊆ U := by
  rcases exists_compact_subset (hU := isOpen_interior.inter hUopen)
      (hx := ⟨hpK, hpU⟩) with ⟨K, hKcompact, hpKint, hKsub⟩
  refine ⟨⟨K, hKcompact⟩, hpKint, ?_, ?_⟩
  · intro y hy
    exact interior_subset (hKsub hy).1
  · intro y hy
    exact (hKsub hy).2

/-- If the interiors of a compact family cover and the target patch is open,
one can choose both the compact-family index and a smaller compact neighborhood
inside the selected family member and the target patch. -/
theorem exists_compact_subset_interior_cover_inter_open
    [LocallyCompactSpace M] {ι : Type*} {Kc : ι → TopologicalSpace.Compacts M}
    {p : M} {U : Set M}
    (hcover_int : (⋃ i, interior (Kc i : Set M)) = Set.univ)
    (hUopen : IsOpen U) (hpU : p ∈ U) :
    ∃ (i : ι) (K : TopologicalSpace.Compacts M),
      p ∈ interior (K : Set M) ∧
        (K : Set M) ⊆ (Kc i : Set M) ∧ (K : Set M) ⊆ U := by
  have hpcover : p ∈ ⋃ i, interior (Kc i : Set M) := by
    rw [hcover_int]
    exact Set.mem_univ p
  rcases Set.mem_iUnion.mp hpcover with ⟨i, hpKc⟩
  rcases exists_compact_subset_interior_inter_open
      (M := M) (p := p) (K₀ := (Kc i : Set M)) (U := U)
      hpKc hUopen hpU with
    ⟨K, hpK, hKsubKc, hKsubU⟩
  exact ⟨i, K, hpK, hKsubKc, hKsubU⟩

/-- An interior-covering compact family is, in particular, an ordinary compact
cover.  This keeps stronger cover data compatible with the existing
finite-cover section-space APIs. -/
theorem iUnion_compacts_eq_univ_of_iUnion_interior_eq_univ
    {X : Type*} [TopologicalSpace X] {ι : Type*} {Kc : ι → TopologicalSpace.Compacts X}
    (hcover_int : (⋃ i, interior (Kc i : Set X)) = Set.univ) :
    (⋃ i, (Kc i : Set X)) = Set.univ := by
  refine eq_univ_of_univ_subset ?_
  intro x _hx
  have hx : x ∈ ⋃ i, interior (Kc i : Set X) := by
    rw [hcover_int]
    exact Set.mem_univ x
  rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
  exact Set.mem_iUnion.mpr ⟨i, interior_subset hxi⟩

/-- A finite cover of the whole space by compact sets makes the whole space
compact.  Existing finite-cover chart hypotheses therefore carry compactness
as data, even when no `CompactSpace` instance has been installed. -/
theorem isCompact_univ_of_finite_compact_cover
    {X : Type*} [TopologicalSpace X] {ι : Type*} [Finite ι]
    (Kc : ι → TopologicalSpace.Compacts X)
    (hcover : (⋃ i, (Kc i : Set X)) = Set.univ) :
    IsCompact (Set.univ : Set X) := by
  simpa [hcover] using
    (isCompact_iUnion (f := fun i ↦ (Kc i : Set X)) fun i ↦ (Kc i).isCompact)

/-- Instance-valued version of
`isCompact_univ_of_finite_compact_cover`. -/
theorem compactSpace_of_finite_compact_cover
    {X : Type*} [TopologicalSpace X] {ι : Type*} [Finite ι]
    (Kc : ι → TopologicalSpace.Compacts X)
    (hcover : (⋃ i, (Kc i : Set X)) = Set.univ) :
    CompactSpace X :=
  isCompact_univ_iff.1 (isCompact_univ_of_finite_compact_cover Kc hcover)

/-- A finite open cover of a compact set admits compact cores subordinate to
the open patches whose interiors still cover the original compact set.  This
is the cover-level topological input needed to replace plain compact cover
membership by interior compact-cover membership. -/
theorem exists_compacts_interior_cover_of_finite_open_cover
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    {ι : Type*} [Finite ι] {s : Set X} {U : ι → Set X}
    (hs : IsCompact s) (hUopen : ∀ i, IsOpen (U i))
    (hcover : s ⊆ ⋃ i, U i) :
    ∃ K : ι → TopologicalSpace.Compacts X,
      s ⊆ ⋃ i, interior (K i : Set X) ∧ ∀ i, (K i : Set X) ⊆ U i := by
  have hfinite : ∀ x ∈ s, {i | x ∈ U i}.Finite := by
    intro _x _hx
    exact Set.finite_univ.subset (by intro i _hi; exact Set.mem_univ i)
  rcases exists_subset_iUnion_closure_subset_t2space
      (s := s) (u := U) hs hUopen hfinite hcover with
    ⟨V, hVcover, hVopen, hVclosure, hVcompact⟩
  let K : ι → TopologicalSpace.Compacts X := fun i ↦ ⟨closure (V i), hVcompact i⟩
  refine ⟨K, ?_, ?_⟩
  · intro x hx
    rcases Set.mem_iUnion.mp (hVcover hx) with ⟨i, hxi⟩
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    change x ∈ interior (closure (V i))
    exact mem_interior_iff_mem_nhds.2
      (Filter.mem_of_superset ((hVopen i).mem_nhds hxi) subset_closure)
  · intro i
    change closure (V i) ⊆ U i
    exact hVclosure i

/-- Whole-space version of
`exists_compacts_interior_cover_of_finite_open_cover` for compact spaces. -/
theorem exists_compacts_interior_univ_cover_of_finite_open_cover
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [CompactSpace X]
    {ι : Type*} [Finite ι] {U : ι → Set X}
    (hUopen : ∀ i, IsOpen (U i)) (hcover : (⋃ i, U i) = Set.univ) :
    ∃ K : ι → TopologicalSpace.Compacts X,
      (⋃ i, interior (K i : Set X)) = Set.univ ∧ ∀ i, (K i : Set X) ⊆ U i := by
  have hcover' : (Set.univ : Set X) ⊆ ⋃ i, U i := by
    simpa [hcover]
  rcases exists_compacts_interior_cover_of_finite_open_cover
      (s := (Set.univ : Set X)) (U := U) isCompact_univ hUopen hcover' with
    ⟨K, hKcover, hKsub⟩
  exact ⟨K, eq_univ_of_univ_subset hKcover, hKsub⟩

/-- The canonical compact overlap family attached to a compact cover. -/
noncomputable def compactCoverIntersections
    {X : Type*} [TopologicalSpace X] [T2Space X] {ι : Type*}
    (Kc : ι → TopologicalSpace.Compacts X) :
    ι → ι → TopologicalSpace.Compacts X :=
  fun i j ↦ Kc i ⊓ Kc j

@[simp] theorem compactCoverIntersections_coe
    {X : Type*} [TopologicalSpace X] [T2Space X] {ι : Type*}
    (Kc : ι → TopologicalSpace.Compacts X) (i j : ι) :
    (compactCoverIntersections Kc i j : Set X) =
      (Kc i : Set X) ∩ (Kc j : Set X) := by
  rfl

/-- The canonical compact overlap family is subordinate to pairwise
intersections. -/
theorem compactCoverIntersections_subset
    {X : Type*} [TopologicalSpace X] [T2Space X] {ι : Type*}
    (Kc : ι → TopologicalSpace.Compacts X) :
    ∀ i j, (compactCoverIntersections Kc i j : Set X) ⊆
      (Kc i : Set X) ∩ (Kc j : Set X) := by
  intro i j x hx
  simpa [compactCoverIntersections] using hx

/-- The canonical compact overlap family is exactly the pairwise
intersection family expected by the finite-cover section-space API. -/
theorem compactCoverIntersections_eq
    {X : Type*} [TopologicalSpace X] [T2Space X] {ι : Type*}
    (Kc : ι → TopologicalSpace.Compacts X) :
    ∀ i j, (compactCoverIntersections Kc i j : Set X) =
      (Kc i : Set X) ∩ (Kc j : Set X) := by
  intro i j
  rfl

/-- An ordinary finite compact cover subordinate to finite open patches can be
replaced by a compact cover subordinate to the same patches whose interiors
cover the whole space.  The original compact cover supplies compactness of the
ambient space, so callers do not need a separate `CompactSpace` instance. -/
theorem exists_interior_compact_cover_subordinate_of_compact_cover
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    {ι : Type*} [Finite ι] {U : ι → Set X}
    (Kc₀ : ι → TopologicalSpace.Compacts X)
    (hKc₀ : ∀ i, (Kc₀ i : Set X) ⊆ U i)
    (hcover₀ : (⋃ i, (Kc₀ i : Set X)) = Set.univ)
    (hUopen : ∀ i, IsOpen (U i)) :
    ∃ Kc : ι → TopologicalSpace.Compacts X,
      (⋃ i, interior (Kc i : Set X)) = Set.univ ∧
        (⋃ i, (Kc i : Set X)) = Set.univ ∧ ∀ i, (Kc i : Set X) ⊆ U i := by
  letI : CompactSpace X := compactSpace_of_finite_compact_cover Kc₀ hcover₀
  have hUcover : (⋃ i, U i) = Set.univ := by
    refine eq_univ_of_univ_subset ?_
    intro x _hx
    have hxK : x ∈ ⋃ i, (Kc₀ i : Set X) := by
      rw [hcover₀]
      exact Set.mem_univ x
    rcases Set.mem_iUnion.mp hxK with ⟨i, hxi⟩
    exact Set.mem_iUnion.mpr ⟨i, hKc₀ i hxi⟩
  rcases exists_compacts_interior_univ_cover_of_finite_open_cover
      (U := U) hUopen hUcover with
    ⟨Kc, hcover_int, hKc⟩
  exact ⟨Kc, hcover_int,
    iUnion_compacts_eq_univ_of_iUnion_interior_eq_univ hcover_int, hKc⟩

/-- Full finite-cover refinement package: from an ordinary compact chart cover
subordinate to finite open patches, build an interior-covering compact cover
subordinate to the same patches together with the exact pairwise compact
overlaps required by the section-space compatibility API. -/
theorem exists_interior_compact_cover_with_intersections_of_compact_cover
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    {ι : Type*} [Finite ι] {U : ι → Set X}
    (Kc₀ : ι → TopologicalSpace.Compacts X)
    (hKc₀ : ∀ i, (Kc₀ i : Set X) ⊆ U i)
    (hcover₀ : (⋃ i, (Kc₀ i : Set X)) = Set.univ)
    (hUopen : ∀ i, IsOpen (U i)) :
    ∃ (Kc : ι → TopologicalSpace.Compacts X)
      (Ko : ι → ι → TopologicalSpace.Compacts X),
      (∀ i, (Kc i : Set X) ⊆ U i) ∧
        (∀ i j, (Ko i j : Set X) ⊆ (Kc i : Set X) ∩ (Kc j : Set X)) ∧
        (∀ i j, (Ko i j : Set X) = (Kc i : Set X) ∩ (Kc j : Set X)) ∧
        (⋃ i, interior (Kc i : Set X)) = Set.univ ∧
        (⋃ i, (Kc i : Set X)) = Set.univ := by
  rcases exists_interior_compact_cover_subordinate_of_compact_cover
      (U := U) Kc₀ hKc₀ hcover₀ hUopen with
    ⟨Kc, hcover_int, hcover, hKc⟩
  let Ko : ι → ι → TopologicalSpace.Compacts X := compactCoverIntersections Kc
  exact ⟨Kc, Ko, hKc,
    compactCoverIntersections_subset Kc,
    compactCoverIntersections_eq Kc,
    hcover_int, hcover⟩

/-- Trivialization-specialized refinement package.  An ordinary finite compact
cover subordinate to a finite family of trivialization base sets can be
replaced by an interior-covering compact cover subordinate to those same base
sets, with exact compact pairwise overlaps. -/
theorem exists_interior_compact_trivialization_cover_with_intersections_of_compact_cover
    {X Fiber Z : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [TopologicalSpace Fiber] [TopologicalSpace Z] {proj : Z → X}
    {ι : Type*} [Finite ι]
    (et : ι → _root_.Bundle.Trivialization Fiber proj)
    (Kc₀ : ι → TopologicalSpace.Compacts X)
    (hKc₀ : ∀ i, (Kc₀ i : Set X) ⊆ (et i).baseSet)
    (hcover₀ : (⋃ i, (Kc₀ i : Set X)) = Set.univ) :
    ∃ (Kc : ι → TopologicalSpace.Compacts X)
      (Ko : ι → ι → TopologicalSpace.Compacts X),
      (∀ i, (Kc i : Set X) ⊆ (et i).baseSet) ∧
        (∀ i j, (Ko i j : Set X) ⊆ (Kc i : Set X) ∩ (Kc j : Set X)) ∧
        (∀ i j, (Ko i j : Set X) = (Kc i : Set X) ∩ (Kc j : Set X)) ∧
        (⋃ i, interior (Kc i : Set X)) = Set.univ ∧
        (⋃ i, (Kc i : Set X)) = Set.univ :=
  exists_interior_compact_cover_with_intersections_of_compact_cover
    (U := fun i ↦ (et i).baseSet) Kc₀ hKc₀ hcover₀ fun i ↦ (et i).open_baseSet

private noncomputable def compactCurveOfEventuallyMemOnSet
    (K : Set M) (y : ℝ → M) (s : Set ℝ) (t : ℝ) (hy_t : y t ∈ K) : ℝ → K :=
  by
    classical
    exact fun τ ↦
      if hsτ : τ ∈ s then
        if hτ : y τ ∈ K then ⟨y τ, hτ⟩ else ⟨y t, hy_t⟩
      else
        ⟨y t, hy_t⟩

private theorem compactCurveOfEventuallyMemOnSet_eventually_val_eq
    {K : Set M} {y : ℝ → M} {s : Set ℝ} {t : ℝ} {hy_t : y t ∈ K}
    (hmem : ∀ᶠ τ in 𝓝[s] t, y τ ∈ K) :
    (fun τ : ℝ ↦ (compactCurveOfEventuallyMemOnSet K y s t hy_t τ).1)
      =ᶠ[𝓝[s] t] y := by
  filter_upwards [self_mem_nhdsWithin, hmem] with τ hsτ hτ
  simp [compactCurveOfEventuallyMemOnSet, hsτ, hτ]

private theorem compactCurveOfEventuallyMemOnSet_tendsto_Ici
    {K : Set M} {y : ℝ → M} {s : Set ℝ} {t : ℝ} {hy_t : y t ∈ K}
    (hts : t ∈ s)
    (hy : Filter.Tendsto y (𝓝[s] t) (𝓝 (y t)))
    (hmem : ∀ᶠ τ in 𝓝[s] t, y τ ∈ K) :
    Filter.Tendsto (compactCurveOfEventuallyMemOnSet K y s t hy_t)
      (𝓝[Ici t] t) (𝓝 (compactCurveOfEventuallyMemOnSet K y s t hy_t t)) := by
  rw [tendsto_subtype_rng]
  have htarget :
      (compactCurveOfEventuallyMemOnSet K y s t hy_t t).1 = y t := by
    simp [compactCurveOfEventuallyMemOnSet, hts, hy_t]
  rw [htarget]
  intro U hU
  have hytU : y t ∈ U := mem_of_mem_nhds hU
  have hpre : {τ : ℝ | y τ ∈ U} ∈ 𝓝[s] t := hy hU
  have hpre' : ∀ᶠ τ in 𝓝 t, τ ∈ s → y τ ∈ U :=
    mem_nhdsWithin_iff_eventually.mp hpre
  have hmem' : ∀ᶠ τ in 𝓝 t, τ ∈ s → y τ ∈ K :=
    mem_nhdsWithin_iff_eventually.mp hmem
  change
    {τ : ℝ | (compactCurveOfEventuallyMemOnSet K y s t hy_t τ).1 ∈ U} ∈
      𝓝[Ici t] t
  rw [mem_nhdsWithin_iff_eventually]
  filter_upwards [hpre', hmem'] with τ hpreτ hmemτ hτIci
  by_cases hsτ : τ ∈ s
  · have hτU : y τ ∈ U := hpreτ hsτ
    have hτK : y τ ∈ K := hmemτ hsτ
    simp [compactCurveOfEventuallyMemOnSet, hsτ, hτK, hτU]
  · simp [compactCurveOfEventuallyMemOnSet, hsτ, hytU]

section GlobalClosure

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
variable [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
variable [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
variable [IsManifold I (minSmoothness ℝ 3) M]
variable [IsManifold I ((2 : ℕ∞) + 1) M]
variable [CompleteSpace F]
variable {κ : Type*} [Finite κ] [T2Space M]
variable [FiniteDimensional ℝ F] [Nontrivial F]

/-- On the Picard interval and the genuine Riemannian-metric locus, the density-based
interval-scoped restricted symmetric carrier is the same as the interval chart's built-in
restricted symmetric carrier. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.restrictedSymmetricA_eq_restrictedSymmetricA_of_closure_smooth_spd_on_Icc_of_mem
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (rhs : SmoothSectionRHSIdentification
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover chart.A)
    (hclosure : ∀ s : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover,
      s ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover →
      (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover) ∈ closure
          ({u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover |
              u ∈ symmetricPositiveDefiniteLocus
                (M := M) (F := F) (W := (TangentSpace I : M → Type _))
                et Kc hKc Ko hKo hKoEq hcover ∧
              ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
                (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x))}))
    {t : ℝ} (ht : t ∈ Icc ivp.initialTime T)
    (x : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover)
    (hx : x ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
      (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover) :
    (chart.restrictedSymmetricA
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover) t x =
      (SmoothSectionRHSIdentification.restrictedSymmetricA_of_closure_smooth_spd_on_Icc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure
        (fun τ hτ => chart.lipschitzOn_Icc τ hτ)) t x := by
  apply Subtype.ext
  calc
    ((chart.restrictedSymmetricA
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover) t x :
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover) =
        chart.A t (x :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) := by
      exact chart.restrictedSymmetricA_coe_of_mem
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover t x hx
    _ =
        ((SmoothSectionRHSIdentification.restrictedSymmetricA_of_closure_smooth_spd_on_Icc
          (M := M) (F := F) (I := I)
          x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure
          (fun τ hτ => chart.lipschitzOn_Icc τ hτ)) t x :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) := by
      exact (SmoothSectionRHSIdentification.restrictedSymmetricA_of_closure_smooth_spd_on_Icc_coe_of_mem
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure
        (fun τ hτ => chart.lipschitzOn_Icc τ hτ) t ht x hx).symm

/-- Ambient-coordinate readout of
`TimeDependentGeometricRicciDeTurckBanachChartOnIcc.restrictedSymmetricA_eq_restrictedSymmetricA_of_closure_smooth_spd_on_Icc_of_mem`. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.restrictedSymmetricA_coe_eq_restrictedSymmetricA_of_closure_smooth_spd_on_Icc_of_mem
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (rhs : SmoothSectionRHSIdentification
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover chart.A)
    (hclosure : ∀ s : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover,
      s ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover →
      (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover) ∈ closure
          ({u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover |
              u ∈ symmetricPositiveDefiniteLocus
                (M := M) (F := F) (W := (TangentSpace I : M → Type _))
                et Kc hKc Ko hKo hKoEq hcover ∧
              ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
                (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x))}))
    {t : ℝ} (ht : t ∈ Icc ivp.initialTime T)
    (x : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover)
    (hx : x ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
      (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover) :
    ((chart.restrictedSymmetricA
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover) t x :
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover) =
      ((SmoothSectionRHSIdentification.restrictedSymmetricA_of_closure_smooth_spd_on_Icc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure
        (fun τ hτ => chart.lipschitzOn_Icc τ hτ)) t x :
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover) := by
  exact congrArg Subtype.val
    (chart.restrictedSymmetricA_eq_restrictedSymmetricA_of_closure_smooth_spd_on_Icc_of_mem
      (M := M) (F := F) (I := I) rhs hclosure ht x hx)

/-- Transport a state-preserving Banach solution of the interval-scoped density-based carrier to the
chart's built-in restricted symmetric carrier. The terminal-time hypothesis is exactly what restricts
the vector-field equality to the Picard interval, avoiding any false global identification outside
`Icc ivp.initialTime T`. -/
def TimeDependentGeometricRicciDeTurckBanachChartOnIcc.toRestrictedSymmetricA_banachEvolutionLocalSolutionIn_of_closure_smooth_spd_on_Icc
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (rhs : SmoothSectionRHSIdentification
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover chart.A)
    (hclosure : ∀ s : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover,
      s ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover →
      (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover) ∈ closure
          ({u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover |
              u ∈ symmetricPositiveDefiniteLocus
                (M := M) (F := F) (W := (TangentSpace I : M → Type _))
                et Kc hKc Ko hKo hKoEq hcover ∧
              ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
                (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x))}))
    (sol : BanachEvolutionLocalSolutionIn
      (SmoothSectionRHSIdentification.restrictedSymmetricA_of_closure_smooth_spd_on_Icc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure
        (fun τ hτ => chart.lipschitzOn_Icc τ hτ))
      (riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
      ivp.initialTime
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp))
    (hsolT : sol.terminalTime ≤ T) :
    BanachEvolutionLocalSolutionIn
      (chart.restrictedSymmetricA
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
      (riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
      ivp.initialTime
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) where
  terminalTime := sol.terminalTime
  initial_lt_terminal := sol.initial_lt_terminal
  curve := sol.curve
  initial_eq := sol.initial_eq
  equation := by
    intro t ht
    have htT : t ∈ Icc ivp.initialTime T := ⟨ht.1, le_trans ht.2 hsolT⟩
    have hEq :=
      chart.restrictedSymmetricA_eq_restrictedSymmetricA_of_closure_smooth_spd_on_Icc_of_mem
        (M := M) (F := F) (I := I) rhs hclosure htT (sol.curve t) (sol.mem_state ht)
    simpa [hEq] using sol.toBanachEvolutionLocalSolution.equation ht
  mem_state := sol.mem_state

/-- The Banach chart right-hand side differentiates the named
`metricBilinearCoordinateField` at the chart center for a smooth intrinsic
DeTurck realization.

This is the centered model-slot form of the finite-cover readout derivative
needed before a raw `C³` gauge-flow argument moves the base point. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_base_hasDerivAt_chartRHS_of_mem_Ioo
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (x0 : κ → M)
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {t : ℝ} (ht : t ∈ Ioo ivp.initialTime sol.terminalTime)
    (p : M) (uE vE : F) :
    HasDerivAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric p
          (τ, (extChartAt I p) p) uE vE)
      (A t (sol.curve t) p
        (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p uE)
        (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p vE)) t := by
  exact
    SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField_base_hasDerivAt_of_hasTimeDerivativeAt
      (I := I) (M := M)
      (realization.hasTimeDerivativeAt_chartRHS_of_mem_Ioo
        (M := M) (F := F) (I := I) x0 het ht)
      p uE vE

/-- Tangent-vector-slot version of
`metricBilinearCoordinateField_base_hasDerivAt_chartRHS_of_mem_Ioo`.

This exposes the same Banach chart right-hand side in the scalar shape used by
geometric gauge-pullback calculations. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_base_sourceTangentCoordinate_hasDerivAt_chartRHS_of_mem_Ioo
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (x0 : κ → M)
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {t : ℝ} (ht : t ∈ Ioo ivp.initialTime sol.terminalTime)
    (p : M) (u v : TangentSpace I p) :
    HasDerivAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric p
          (τ, (extChartAt I p) p)
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p u)
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p v))
      (A t (sol.curve t) p u v) t := by
  exact
    SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField_base_sourceTangentCoordinate_hasDerivAt_of_hasTimeDerivativeAt
      (I := I) (M := M)
       (realization.hasTimeDerivativeAt_chartRHS_of_mem_Ioo
         (M := M) (F := F) (I := I) x0 het ht)
       p u v

/-- One-sided endpoint version of
`metricBilinearCoordinateField_base_hasDerivAt_chartRHS_of_mem_Ioo`.

At every time in the closed-left/open-right Banach interval, the centered
metric-coordinate field has the Banach chart right-hand side as its right
derivative. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_base_hasDerivWithinAt_Ici_chartRHS_of_mem_Ico
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (x0 : κ → M)
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {t : ℝ} (ht : t ∈ Ico ivp.initialTime sol.terminalTime)
    (p : M) (uE vE : F) :
    HasDerivWithinAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric p
          (τ, (extChartAt I p) p) uE vE)
      (A t (sol.curve t) p
        (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p uE)
        (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p vE))
      (Ici t) t := by
  have hmetric :=
    realization.metric_hasDerivWithinAt_Ici_chartRHS_of_mem_Ico
      (M := M) (F := F) (I := I) x0 het ht p
      (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p uE)
      (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p vE)
  have hEq :
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric p
          (τ, (extChartAt I p) p) uE vE) =ᶠ[𝓝[Ici t] t]
        (fun τ : ℝ ↦ metricTensor (I := I) (M := M) realization.metric τ p
          (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p uE)
          (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p vE)) := by
    filter_upwards with τ
    rw [SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField_base_apply_eq_tangentVector]
    rfl
  have hEq_t :
      SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric p
          (t, (extChartAt I p) p) uE vE =
        metricTensor (I := I) (M := M) realization.metric t p
          (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p uE)
          (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p vE) := by
    rw [SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField_base_apply_eq_tangentVector]
    rfl
  exact hmetric.congr_of_eventuallyEq hEq hEq_t

/-- Tangent-vector-slot one-sided endpoint version of
`metricBilinearCoordinateField_base_hasDerivWithinAt_Ici_chartRHS_of_mem_Ico`. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_base_sourceTangentCoordinate_hasDerivWithinAt_Ici_chartRHS_of_mem_Ico
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (x0 : κ → M)
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {t : ℝ} (ht : t ∈ Ico ivp.initialTime sol.terminalTime)
    (p : M) (u v : TangentSpace I p) :
    HasDerivWithinAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric p
          (τ, (extChartAt I p) p)
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p u)
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p v))
      (A t (sol.curve t) p u v) (Ici t) t := by
  simpa using
    realization.metricBilinearCoordinateField_base_hasDerivWithinAt_Ici_chartRHS_of_mem_Ico
      (M := M) (F := F) (I := I) x0 het ht p
      (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p u)
      (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p v)

/-- One-sided endpoint version with a coordinate curve that is stationary at
the chart center along the right-time filter.

This is the smooth-realization counterpart of the raw within-filter stationary
center bridge: Banach chart callers may replace the literal center coordinate
by any model curve eventually equal to that center on `Ici t`. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_hasDerivWithinAt_Ici_chartRHS_of_eventuallyEq_center_of_mem_Ico
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (x0 : κ → M)
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {t : ℝ} (ht : t ∈ Ico ivp.initialTime sol.terminalTime)
    (p : M) {y : ℝ → F}
    (hy : y =ᶠ[𝓝[Ici t] t] fun _ : ℝ ↦ (extChartAt I p) p)
    (hy_t : y t = (extChartAt I p) p)
    (uE vE : F) :
    HasDerivWithinAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric p
          (τ, y τ) uE vE)
      (A t (sol.curve t) p
        (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p uE)
        (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p vE))
      (Ici t) t := by
  have hcenter :=
    realization.metricBilinearCoordinateField_base_hasDerivWithinAt_Ici_chartRHS_of_mem_Ico
      (M := M) (F := F) (I := I) x0 het ht p uE vE
  have hEq :
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric p
          (τ, y τ) uE vE) =ᶠ[𝓝[Ici t] t]
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric p
          (τ, (extChartAt I p) p) uE vE) := by
    filter_upwards [hy] with τ hτ
    rw [hτ]
  exact hcenter.congr_of_eventuallyEq hEq (by rw [hy_t])

/-- Tangent-vector-slot version of
`metricBilinearCoordinateField_hasDerivWithinAt_Ici_chartRHS_of_eventuallyEq_center_of_mem_Ico`.
-/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_sourceTangentCoordinate_hasDerivWithinAt_Ici_chartRHS_of_eventuallyEq_center_of_mem_Ico
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (x0 : κ → M)
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {t : ℝ} (ht : t ∈ Ico ivp.initialTime sol.terminalTime)
    (p : M) {y : ℝ → F}
    (hy : y =ᶠ[𝓝[Ici t] t] fun _ : ℝ ↦ (extChartAt I p) p)
    (hy_t : y t = (extChartAt I p) p)
    (u v : TangentSpace I p) :
    HasDerivWithinAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric p
          (τ, y τ)
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p u)
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p v))
      (A t (sol.curve t) p u v) (Ici t) t := by
  simpa using
    realization.metricBilinearCoordinateField_hasDerivWithinAt_Ici_chartRHS_of_eventuallyEq_center_of_mem_Ico
      (M := M) (F := F) (I := I) x0 het ht p hy hy_t
      (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p u)
      (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p v)

/-- A finite-cover bilinear coordinate readout of a smooth metric section is the
named raw metric-coordinate field centered at the same preferred
trivialization point. -/
theorem metric_coordBilinearFormReadoutMap_eq_metricBilinearCoordinateField
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (g : MetricFamily (I := I) (M := M)) (τ : ℝ) (i : κ) (x : Kc i) :
    (equivCompatibleCoordFamilySubmodule
      (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover
      (⟨(g τ).toContinuousRiemannianMetric.toSection,
        (g τ).toContinuousRiemannianMetric.continuous_toSection⟩ :
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover)).1 i x =
      SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
        (I := I) (M := M) g (x0 i)
        (τ, (extChartAt I (x0 i)) x.1) := by
  ext uE vE
  let TM := (TangentSpace I : M → Type _)
  have hKpref :
      (Kc i : Set M) ⊆
        (trivializationAt BilF
          (_root_.Bundle.BilinearFormBundle (V := TM)) (x0 i)).baseSet := by
    simpa [TM, het i] using hKc i
  have hxbase : x.1 ∈ (trivializationAt F TM (x0 i)).baseSet := by
    simpa [TM] using hKpref x.2
  have hsrc_ext : x.1 ∈ (extChartAt I (x0 i)).source := by
    simpa [TM, extChartAt_source] using hxbase
  have hy :
      (extChartAt I (x0 i)).symm ((extChartAt I (x0 i)) x.1) = x.1 := by
    exact PartialEquiv.left_inv _ hsrc_ext
  change
    (et i ⟨x.1, (g τ).inner x.1⟩).2 uE vE =
      SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
        (I := I) (M := M) g (x0 i)
        (τ, (extChartAt I (x0 i)) x.1) uE vE
  rw [het i]
  change
    (ContinuousLinearMap.inCoordinates F TM (F →L[ℝ] ℝ) (fun y : M => TM y →L[ℝ] ℝ)
      (x0 i) x.1 (x0 i) x.1 ((g τ).inner x.1) uE) vE =
    SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
      (I := I) (M := M) g (x0 i)
      (τ, (extChartAt I (x0 i)) x.1) uE vE
  change
    (ContinuousLinearMap.inCoordinates F TM (F →L[ℝ] ℝ) (fun y : M => TM y →L[ℝ] ℝ)
      (x0 i) x.1 (x0 i) x.1 ((g τ).inner x.1) uE) vE =
    (ContinuousLinearMap.inCoordinates F TM (F →L[ℝ] ℝ) (fun y : M => TM y →L[ℝ] ℝ)
      (x0 i)
      ((extChartAt I (x0 i)).symm ((extChartAt I (x0 i)) x.1))
      (x0 i)
      ((extChartAt I (x0 i)).symm ((extChartAt I (x0 i)) x.1))
      ((g τ).inner ((extChartAt I (x0 i)).symm ((extChartAt I (x0 i)) x.1))) uE) vE
  rw [hy]

/-- Read a finite-cover section on a smaller compact set, then change the
bilinear-form coordinates to the preferred trivialization centered at `p`.

This is the finite-cover readout used when the raw gauge calculation is
centered at an arbitrary moving point rather than at the fixed cover center
`x0 i`. -/
noncomputable def targetBilinearCoordReadoutContinuousLinearMap
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (p : M) (i : κ) (K : TopologicalSpace.Compacts M)
    (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
    (hK_sub_target : (K : Set M) ⊆
      (trivializationAt BilF
        (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) p).baseSet) :
    ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover →L[ℝ] C(K, BilF) :=
  (coordChangeContinuousLinearMap
    (𝕜 := ℝ) (F := BilF)
    (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
    (e := et i)
    (e' := trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) p)
    K
    (fun _ hx ↦ ⟨hKc i (hK_sub_Kc hx), hK_sub_target hx⟩)).comp
    ((restrictToCompactContinuousLinearMap
      (𝕜 := ℝ) (F := BilF) (hKL := hK_sub_Kc)).comp
      ((ContinuousLinearMap.proj i).comp
        (((compatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) et Kc hKc Ko hKo).subtypeL).comp
          (toCompatibleCoordFamilySubmoduleContinuousLinearMap
            (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover))))

/-- The target-centered compact readout is the ordinary coordinate readout of
the reconstructed section in the target trivialization. -/
private theorem targetBilinearCoordReadoutContinuousLinearMap_apply_eq_coordContinuousMap
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (p : M) (i : κ) (K : TopologicalSpace.Compacts M)
    (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
    (hK_sub_target : (K : Set M) ⊆
      (trivializationAt BilF
        (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) p).baseSet)
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)
    (x : K) :
    targetBilinearCoordReadoutContinuousLinearMap
        (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
        (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
        p i K hK_sub_Kc hK_sub_target s x =
      coordContinuousMap
        (e := trivializationAt BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) p)
        (s := fun y : M ↦ s y)
        K hK_sub_target s.continuous_toFun.continuousOn x := by
  let TM := (TangentSpace I : M → Type _)
  let eTarget :=
    trivializationAt BilF (_root_.Bundle.BilinearFormBundle (V := TM)) p
  have hsource :
      restrictToCompact hK_sub_Kc
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := TM))
            et Kc hKc Ko hKo hKoEq hcover s).1 i) =
        coordContinuousMap
          (e := et i) (s := fun y : M ↦ s y)
          K (fun _ hx ↦ hKc i (hK_sub_Kc hx))
          s.continuous_toFun.continuousOn := by
    ext y
    simp [equivCompatibleCoordFamilySubmodule, toSubtype,
      continuousSectionEquivCompatibleCoordFamilySubmodule,
      continuousSectionEquivCompatibleCoordFamily, compatibleCoordFamilyEquivSubmodule,
      compatibleCoordFamilyOfSection, coordFamilyOfSection, TM]
  calc
    targetBilinearCoordReadoutContinuousLinearMap
        (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
        (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
        p i K hK_sub_Kc hK_sub_target s x
        =
      coordChangeContinuousMap
        (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := TM))
        (e := et i) (e' := eTarget) K
        (fun _ hx ↦ ⟨hKc i (hK_sub_Kc hx), hK_sub_target hx⟩)
        (restrictToCompact hK_sub_Kc
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := TM))
            et Kc hKc Ko hKo hKoEq hcover s).1 i)) x := by
          rfl
    _ =
      coordChangeContinuousMap
        (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := TM))
        (e := et i) (e' := eTarget) K
        (fun _ hx ↦ ⟨hKc i (hK_sub_Kc hx), hK_sub_target hx⟩)
        (coordContinuousMap
          (e := et i) (s := fun y : M ↦ s y)
          K (fun _ hx ↦ hKc i (hK_sub_Kc hx))
          s.continuous_toFun.continuousOn) x := by
          rw [hsource]
    _ =
      coordContinuousMap
        (e := eTarget) (s := fun y : M ↦ s y)
        K hK_sub_target s.continuous_toFun.continuousOn x := by
          exact congrArg (fun f : C(K, BilF) ↦ f x)
            (coordContinuousMap_coordChangeL
              (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := TM))
              (e := et i) (e' := eTarget) (s := fun y : M ↦ s y)
              K (fun _ hx ↦ ⟨hKc i (hK_sub_Kc hx), hK_sub_target hx⟩)
              s.continuous_toFun.continuousOn s.continuous_toFun.continuousOn)

/-- A target-centered compact readout of a smooth metric section is the named
raw metric-coordinate field centered at that target point. -/
theorem metric_targetBilinearCoordReadout_eq_metricBilinearCoordinateField
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (g : MetricFamily (I := I) (M := M)) (τ : ℝ)
    (p : M) (i : κ) (K : TopologicalSpace.Compacts M)
    (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
    (hK_sub_target : (K : Set M) ⊆
      (trivializationAt BilF
        (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) p).baseSet)
    (x : K) :
    targetBilinearCoordReadoutContinuousLinearMap
        (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
        (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
        p i K hK_sub_Kc hK_sub_target
        (⟨(g τ).toContinuousRiemannianMetric.toSection,
          (g τ).toContinuousRiemannianMetric.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) x =
      SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
        (I := I) (M := M) g p (τ, (extChartAt I p) x.1) := by
  rw [targetBilinearCoordReadoutContinuousLinearMap_apply_eq_coordContinuousMap
    (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
    (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
    p i K hK_sub_Kc hK_sub_target]
  ext uE vE
  let TM := (TangentSpace I : M → Type _)
  have hxbase :
      x.1 ∈ (trivializationAt BilF
        (_root_.Bundle.BilinearFormBundle (V := TM)) p).baseSet :=
    hK_sub_target x.2
  have hsrc_ext : x.1 ∈ (extChartAt I p).source := by
    simpa [TM, extChartAt_source] using hxbase
  have hy : (extChartAt I p).symm ((extChartAt I p) x.1) = x.1 := by
    exact PartialEquiv.left_inv _ hsrc_ext
  change
    (ContinuousLinearMap.inCoordinates F TM (F →L[ℝ] ℝ) (fun y : M => TM y →L[ℝ] ℝ)
      p x.1 p x.1 ((g τ).inner x.1) uE) vE =
    SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
      (I := I) (M := M) g p (τ, (extChartAt I p) x.1) uE vE
  change
    (ContinuousLinearMap.inCoordinates F TM (F →L[ℝ] ℝ) (fun y : M => TM y →L[ℝ] ℝ)
      p x.1 p x.1 ((g τ).inner x.1) uE) vE =
    (ContinuousLinearMap.inCoordinates F TM (F →L[ℝ] ℝ) (fun y : M => TM y →L[ℝ] ℝ)
      p
      ((extChartAt I p).symm ((extChartAt I p) x.1))
      p
      ((extChartAt I p).symm ((extChartAt I p) x.1))
      ((g τ).inner ((extChartAt I p).symm ((extChartAt I p) x.1))) uE) vE
  rw [hy]

/-- At the target center, the target-centered compact readout of an arbitrary
bilinear-form section is just the section evaluated on the corresponding
target-centered tangent coordinates. -/
theorem targetBilinearCoordReadoutContinuousLinearMap_apply_self_eq
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (p : M) (i : κ) (K : TopologicalSpace.Compacts M)
    (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
    (hK_sub_target : (K : Set M) ⊆
      (trivializationAt BilF
        (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) p).baseSet)
    (hpK : p ∈ (K : Set M))
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)
    (uE vE : F) :
    targetBilinearCoordReadoutContinuousLinearMap
        (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
        (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
        p i K hK_sub_Kc hK_sub_target s (⟨p, hpK⟩ : K) uE vE =
      s p
        (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p uE)
        (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p vE) := by
  rw [targetBilinearCoordReadoutContinuousLinearMap_apply_eq_coordContinuousMap
    (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
    (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
    p i K hK_sub_Kc hK_sub_target]
  let TM := (TangentSpace I : M → Type _)
  change
    (ContinuousLinearMap.inCoordinates F TM (F →L[ℝ] ℝ) (fun y : M => TM y →L[ℝ] ℝ)
      p p p p (s p) uE) vE =
      s p
        (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p uE)
        (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p vE)
  erw [_root_.Bundle.trivializationAt_bilinearFormBundle_apply_eq
    (F := F) (W := TM) (x0 := p) (x := p)
    (FiberBundle.mem_baseSet_trivializationAt' p) (s p) uE vE]
  rfl

/-- Interior moving-point time-difference derivative for the raw
metric-coordinate field, obtained from the Banach section norm through the
preferred finite-cover coordinate chart. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_timeDifference_hasDerivAt_of_coord_mem_Ioo
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (i : κ) {x : ℝ → Kc i}
    {t : ℝ} (ht : t ∈ Ioo ivp.initialTime sol.terminalTime)
    (hx : Filter.Tendsto x (𝓝 t) (𝓝 (x t))) :
    HasDerivAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric (x0 i)
          (τ, (extChartAt I (x0 i)) (x τ).1) -
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric (x0 i)
          (t, (extChartAt I (x0 i)) (x τ).1))
      ((equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (A t (sol.curve t))).1 i (x t)) t := by
  have hproj :
      HasDerivAt
        (fun τ : ℝ ↦
          (equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover
            (sol.curve τ)).1 i (x τ) -
          (equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover
            (sol.curve t)).1 i (x τ))
        ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover
            (A t (sol.curve t))).1 i (x t)) t :=
    coordBilinearFormReadoutMap_timeDifference_hasDerivAt_of_mem_Ioo_forGaugeRoutes
      (M := M) (F := F) (W := (TangentSpace I : M → Type _)) sol i ht hx
  have hmetric_curve :
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (⟨(realization.metric τ).toContinuousRiemannianMetric.toSection,
            (realization.metric τ).toContinuousRiemannianMetric.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover)).1 i (x τ) -
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (⟨(realization.metric t).toContinuousRiemannianMetric.toSection,
            (realization.metric t).toContinuousRiemannianMetric.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover)).1 i (x τ)) =ᶠ[𝓝 t]
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (sol.curve τ)).1 i (x τ) -
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (sol.curve t)).1 i (x τ)) := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with τ hτ
    rw [realization.metric_toContinuousSection_eq_curve hτ,
      realization.metric_toContinuousSection_eq_curve (Ioo_subset_Icc_self ht)]
  have hmetric_coord := hproj.congr_of_eventuallyEq hmetric_curve
  have hEq :
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric (x0 i)
          (τ, (extChartAt I (x0 i)) (x τ).1) -
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric (x0 i)
          (t, (extChartAt I (x0 i)) (x τ).1)) =ᶠ[𝓝 t]
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (⟨(realization.metric τ).toContinuousRiemannianMetric.toSection,
            (realization.metric τ).toContinuousRiemannianMetric.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover)).1 i (x τ) -
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (⟨(realization.metric t).toContinuousRiemannianMetric.toSection,
            (realization.metric t).toContinuousRiemannianMetric.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover)).1 i (x τ)) := by
    filter_upwards with τ
    rw [← metric_coordBilinearFormReadoutMap_eq_metricBilinearCoordinateField
        (I := I) (M := M) (F := F) het realization.metric τ i (x τ),
      ← metric_coordBilinearFormReadoutMap_eq_metricBilinearCoordinateField
        (I := I) (M := M) (F := F) het realization.metric t i (x τ)]
  exact hmetric_coord.congr_of_eventuallyEq hEq

/-- One-sided endpoint version of
`metricBilinearCoordinateField_timeDifference_hasDerivAt_of_coord_mem_Ioo`. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_timeDifference_hasDerivWithinAt_Ici_of_coord_mem_Ico
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (i : κ) {x : ℝ → Kc i}
    {t : ℝ} (ht : t ∈ Ico ivp.initialTime sol.terminalTime)
    (hx : Filter.Tendsto x (𝓝[Ici t] t) (𝓝 (x t))) :
    HasDerivWithinAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric (x0 i)
          (τ, (extChartAt I (x0 i)) (x τ).1) -
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric (x0 i)
          (t, (extChartAt I (x0 i)) (x τ).1))
      ((equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (A t (sol.curve t))).1 i (x t)) (Ici t) t := by
  have hproj :
      HasDerivWithinAt
        (fun τ : ℝ ↦
          (equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover
            (sol.curve τ)).1 i (x τ) -
          (equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover
            (sol.curve t)).1 i (x τ))
        ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover
            (A t (sol.curve t))).1 i (x t)) (Ici t) t :=
    coordBilinearFormReadoutMap_timeDifference_hasDerivWithinAt_Ici_of_mem_Ico_forGaugeRoutes
      (M := M) (F := F) (W := (TangentSpace I : M → Type _)) sol i ht hx
  have hmetric_curve :
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (⟨(realization.metric τ).toContinuousRiemannianMetric.toSection,
            (realization.metric τ).toContinuousRiemannianMetric.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover)).1 i (x τ) -
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (⟨(realization.metric t).toContinuousRiemannianMetric.toSection,
            (realization.metric t).toContinuousRiemannianMetric.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover)).1 i (x τ)) =ᶠ[𝓝[Ici t] t]
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (sol.curve τ)).1 i (x τ) -
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (sol.curve t)).1 i (x τ)) := by
    filter_upwards [Icc_mem_nhdsGE_of_mem ht] with τ hτ
    rw [realization.metric_toContinuousSection_eq_curve hτ,
      realization.metric_toContinuousSection_eq_curve (Ico_subset_Icc_self ht)]
  have hmetric_coord :=
    hproj.congr_of_eventuallyEq_of_mem hmetric_curve (Set.mem_Ici.mpr le_rfl)
  have hEq :
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric (x0 i)
          (τ, (extChartAt I (x0 i)) (x τ).1) -
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric (x0 i)
          (t, (extChartAt I (x0 i)) (x τ).1)) =ᶠ[𝓝[Ici t] t]
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (⟨(realization.metric τ).toContinuousRiemannianMetric.toSection,
            (realization.metric τ).toContinuousRiemannianMetric.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover)).1 i (x τ) -
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (⟨(realization.metric t).toContinuousRiemannianMetric.toSection,
            (realization.metric t).toContinuousRiemannianMetric.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover)).1 i (x τ)) := by
    filter_upwards with τ
    rw [← metric_coordBilinearFormReadoutMap_eq_metricBilinearCoordinateField
        (I := I) (M := M) (F := F) het realization.metric τ i (x τ),
      ← metric_coordBilinearFormReadoutMap_eq_metricBilinearCoordinateField
        (I := I) (M := M) (F := F) het realization.metric t i (x τ)]
  exact hmetric_coord.congr_of_eventuallyEq_of_mem hEq (Set.mem_Ici.mpr le_rfl)

/-- Interior moving-point time-difference derivative for the raw
metric-coordinate field centered at an arbitrary target point.  The Banach
section derivative is read from one finite-cover component after restriction
to a smaller compact set and coordinate change to the target trivialization. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_timeDifference_hasDerivAt_of_target_coord_mem_Ioo
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (p : M) (i : κ) (K : TopologicalSpace.Compacts M)
    (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
    (hK_sub_target : (K : Set M) ⊆
      (trivializationAt BilF
        (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) p).baseSet)
    {x : ℝ → K}
    {t : ℝ} (ht : t ∈ Ioo ivp.initialTime sol.terminalTime)
    (hx : Filter.Tendsto x (𝓝 t) (𝓝 (x t))) :
    HasDerivAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric p
          (τ, (extChartAt I p) (x τ).1) -
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric p
          (t, (extChartAt I p) (x τ).1))
      (targetBilinearCoordReadoutContinuousLinearMap
        (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
        (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
        p i K hK_sub_Kc hK_sub_target (A t (sol.curve t)) (x t)) t := by
  let L :
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover →L[ℝ] C(K, BilF) :=
    targetBilinearCoordReadoutContinuousLinearMap
      (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
      p i K hK_sub_Kc hK_sub_target
  have hcomponent :
      HasDerivAt (fun τ : ℝ ↦ L (sol.curve τ)) (L (A t (sol.curve t))) t :=
    BanachEvolutionLocalSolutionIn.continuousLinearMap_hasDerivAt_of_mem_Ioo
      (F := A) (stateSet := stateSet) L sol ht
  have hproj :
      HasDerivAt
        (fun τ : ℝ ↦ L (sol.curve τ) (x τ) - L (sol.curve t) (x τ))
        (L (A t (sol.curve t)) (x t)) t :=
    continuousMap_moving_eval_sub_const_hasDerivAt hcomponent hx
  have hmetric_curve :
      (fun τ : ℝ ↦
        L (⟨(realization.metric τ).toContinuousRiemannianMetric.toSection,
          (realization.metric τ).toContinuousRiemannianMetric.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) (x τ) -
        L (⟨(realization.metric t).toContinuousRiemannianMetric.toSection,
          (realization.metric t).toContinuousRiemannianMetric.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) (x τ)) =ᶠ[𝓝 t]
      (fun τ : ℝ ↦ L (sol.curve τ) (x τ) - L (sol.curve t) (x τ)) := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with τ hτ
    rw [realization.metric_toContinuousSection_eq_curve hτ,
      realization.metric_toContinuousSection_eq_curve (Ioo_subset_Icc_self ht)]
  have hmetric_coord := hproj.congr_of_eventuallyEq hmetric_curve
  have hEq :
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric p
          (τ, (extChartAt I p) (x τ).1) -
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric p
          (t, (extChartAt I p) (x τ).1)) =ᶠ[𝓝 t]
      (fun τ : ℝ ↦
        L (⟨(realization.metric τ).toContinuousRiemannianMetric.toSection,
          (realization.metric τ).toContinuousRiemannianMetric.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) (x τ) -
        L (⟨(realization.metric t).toContinuousRiemannianMetric.toSection,
          (realization.metric t).toContinuousRiemannianMetric.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) (x τ)) := by
    filter_upwards with τ
    rw [← metric_targetBilinearCoordReadout_eq_metricBilinearCoordinateField
        (I := I) (M := M) (F := F) (et := et) realization.metric τ p i K
        hK_sub_Kc hK_sub_target (x τ),
      ← metric_targetBilinearCoordReadout_eq_metricBilinearCoordinateField
        (I := I) (M := M) (F := F) (et := et) realization.metric t p i K
        hK_sub_Kc hK_sub_target (x τ)]
  simpa [L] using hmetric_coord.congr_of_eventuallyEq hEq

/-- One-sided endpoint version of
`metricBilinearCoordinateField_timeDifference_hasDerivAt_of_target_coord_mem_Ioo`. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_timeDifference_hasDerivWithinAt_Ici_of_target_coord_mem_Ico
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (p : M) (i : κ) (K : TopologicalSpace.Compacts M)
    (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
    (hK_sub_target : (K : Set M) ⊆
      (trivializationAt BilF
        (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) p).baseSet)
    {x : ℝ → K}
    {t : ℝ} (ht : t ∈ Ico ivp.initialTime sol.terminalTime)
    (hx : Filter.Tendsto x (𝓝[Ici t] t) (𝓝 (x t))) :
    HasDerivWithinAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric p
          (τ, (extChartAt I p) (x τ).1) -
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric p
          (t, (extChartAt I p) (x τ).1))
      (targetBilinearCoordReadoutContinuousLinearMap
        (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
        (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
        p i K hK_sub_Kc hK_sub_target (A t (sol.curve t)) (x t)) (Ici t) t := by
  let L :
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover →L[ℝ] C(K, BilF) :=
    targetBilinearCoordReadoutContinuousLinearMap
      (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
      p i K hK_sub_Kc hK_sub_target
  have hcomponent :
      HasDerivWithinAt (fun τ : ℝ ↦ L (sol.curve τ))
        (L (A t (sol.curve t))) (Ici t) t :=
    BanachEvolutionLocalSolutionIn.continuousLinearMap_hasDerivWithinAt_Ici_of_mem_Ico
      (F := A) (stateSet := stateSet) L sol ht
  have hproj :
      HasDerivWithinAt
        (fun τ : ℝ ↦ L (sol.curve τ) (x τ) - L (sol.curve t) (x τ))
        (L (A t (sol.curve t)) (x t)) (Ici t) t :=
    continuousMap_moving_eval_sub_const_hasDerivWithinAt hcomponent hx
  have hmetric_curve :
      (fun τ : ℝ ↦
        L (⟨(realization.metric τ).toContinuousRiemannianMetric.toSection,
          (realization.metric τ).toContinuousRiemannianMetric.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) (x τ) -
        L (⟨(realization.metric t).toContinuousRiemannianMetric.toSection,
          (realization.metric t).toContinuousRiemannianMetric.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) (x τ)) =ᶠ[𝓝[Ici t] t]
      (fun τ : ℝ ↦ L (sol.curve τ) (x τ) - L (sol.curve t) (x τ)) := by
    filter_upwards [Icc_mem_nhdsGE_of_mem ht] with τ hτ
    rw [realization.metric_toContinuousSection_eq_curve hτ,
      realization.metric_toContinuousSection_eq_curve (Ico_subset_Icc_self ht)]
  have hmetric_coord :=
    hproj.congr_of_eventuallyEq_of_mem hmetric_curve (Set.mem_Ici.mpr le_rfl)
  have hEq :
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric p
          (τ, (extChartAt I p) (x τ).1) -
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric p
          (t, (extChartAt I p) (x τ).1)) =ᶠ[𝓝[Ici t] t]
      (fun τ : ℝ ↦
        L (⟨(realization.metric τ).toContinuousRiemannianMetric.toSection,
          (realization.metric τ).toContinuousRiemannianMetric.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) (x τ) -
        L (⟨(realization.metric t).toContinuousRiemannianMetric.toSection,
          (realization.metric t).toContinuousRiemannianMetric.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) (x τ)) := by
    filter_upwards with τ
    rw [← metric_targetBilinearCoordReadout_eq_metricBilinearCoordinateField
        (I := I) (M := M) (F := F) (et := et) realization.metric τ p i K
        hK_sub_Kc hK_sub_target (x τ),
      ← metric_targetBilinearCoordReadout_eq_metricBilinearCoordinateField
        (I := I) (M := M) (F := F) (et := et) realization.metric t p i K
        hK_sub_Kc hK_sub_target (x τ)]
  simpa [L] using
    hmetric_coord.congr_of_eventuallyEq_of_mem hEq (Set.mem_Ici.mpr le_rfl)

/-- Full raw gauge-flow metric-coordinate derivative obtained from the Banach
moving time-difference bridge, once the gauge path has been represented in a
preferred compact coordinate chart centered at the time-`t` image. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_hasDerivAt_along_gauge_eval_of_coord_mem_Ioo
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (hs : s ∈ 𝓝 t)
    (ht : t ∈ Ioo ivp.initialTime sol.terminalTime)
    (i : κ) (x : M)
    (hcenter : x0 i = (G.maps3 t) x)
    {xK : ℝ → Kc i}
    (hxK : Filter.Tendsto xK (𝓝 t) (𝓝 (xK t)))
    (hxK_eval : (fun τ : ℝ ↦ (xK τ).1) =ᶠ[𝓝 t]
      fun τ : ℝ ↦ (G.maps3 τ) x) :
    HasDerivAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric ((G.maps3 t) x)
          (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)))
      (((equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (A t (sol.curve t))).1 i (xK t)) +
        (fderivWithin ℝ
          (fun yE : F ↦
            SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
              (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
          (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
          (X t ((G.maps3 t) x))) t := by
  have htime_coord :=
    realization.metricBilinearCoordinateField_timeDifference_hasDerivAt_of_coord_mem_Ioo
      (M := M) (F := F) (I := I) het i ht hxK
  have htime :
      HasDerivAt
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)) -
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (t, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)))
        ((equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (A t (sol.curve t))).1 i (xK t)) t := by
    have hEq :
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)) -
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (t, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x))) =ᶠ[𝓝 t]
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric (x0 i)
            (τ, (extChartAt I (x0 i)) (xK τ).1) -
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric (x0 i)
            (t, (extChartAt I (x0 i)) (xK τ).1)) := by
      filter_upwards [hxK_eval] with τ hτ
      rw [← hcenter, ← hτ]
    exact htime_coord.congr_of_eventuallyEq hEq
  simpa using
    SmoothSelfDiffeomorph3Family.Diffeomorph3GaugeFlowOn.metricBilinearCoordinateField_hasDerivAt_of_timeDifference_along_eval_self
      (I := I) (M := M) G hs realization.metric x htime

/-- Full raw gauge-flow metric-coordinate derivative from the target-centered
Banach readout.  This removes the fixed-cover center equality by reading the
Banach right-hand side through a compact set contained in both a finite-cover
piece and the target trivialization at the time-`t` gauge image. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_hasDerivAt_along_gauge_eval_of_target_coord_mem_Ioo
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (hs : s ∈ 𝓝 t)
    (ht : t ∈ Ioo ivp.initialTime sol.terminalTime)
    (i : κ) (K : TopologicalSpace.Compacts M) (x : M)
    (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
    (hK_sub_target : (K : Set M) ⊆
      (trivializationAt BilF
        (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        ((G.maps3 t) x)).baseSet)
    {xK : ℝ → K}
    (hxK : Filter.Tendsto xK (𝓝 t) (𝓝 (xK t)))
    (hxK_eval : (fun τ : ℝ ↦ (xK τ).1) =ᶠ[𝓝 t]
      fun τ : ℝ ↦ (G.maps3 τ) x) :
    HasDerivAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric ((G.maps3 t) x)
          (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)))
      ((targetBilinearCoordReadoutContinuousLinearMap
          (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
          (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
          ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target
          (A t (sol.curve t)) (xK t)) +
        (fderivWithin ℝ
          (fun yE : F ↦
            SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
              (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
          (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
          (X t ((G.maps3 t) x))) t := by
  have htime_coord :=
    realization.metricBilinearCoordinateField_timeDifference_hasDerivAt_of_target_coord_mem_Ioo
      (M := M) (F := F) (I := I)
      ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target ht hxK
  have htime :
      HasDerivAt
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)) -
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (t, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)))
        (targetBilinearCoordReadoutContinuousLinearMap
          (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
          (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
          ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target
          (A t (sol.curve t)) (xK t)) t := by
    have hEq :
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)) -
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (t, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x))) =ᶠ[𝓝 t]
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (τ, (extChartAt I ((G.maps3 t) x)) (xK τ).1) -
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (t, (extChartAt I ((G.maps3 t) x)) (xK τ).1)) := by
      filter_upwards [hxK_eval] with τ hτ
      rw [← hτ]
    exact htime_coord.congr_of_eventuallyEq hEq
  simpa using
    SmoothSelfDiffeomorph3Family.Diffeomorph3GaugeFlowOn.metricBilinearCoordinateField_hasDerivAt_of_timeDifference_along_eval_self
      (I := I) (M := M) G hs realization.metric x htime

/-- Open-interval target-centered raw gauge derivative from eventual membership
in the selected compact overlap piece. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_hasDerivAt_along_gauge_eval_of_eventually_mem_target_K_Ioo
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (hs : s ∈ 𝓝 t)
    (ht : t ∈ Ioo ivp.initialTime sol.terminalTime)
    (i : κ) (K : TopologicalSpace.Compacts M) (x : M)
    (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
    (hK_sub_target : (K : Set M) ⊆
      (trivializationAt BilF
        (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        ((G.maps3 t) x)).baseSet)
    (hmem_t : (G.maps3 t) x ∈ (K : Set M))
    (hmem : ∀ᶠ τ in 𝓝 t, (G.maps3 τ) x ∈ (K : Set M)) :
    HasDerivAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric ((G.maps3 t) x)
          (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)))
      ((targetBilinearCoordReadoutContinuousLinearMap
          (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
          (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
          ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target
          (A t (sol.curve t)) (⟨(G.maps3 t) x, hmem_t⟩ : K)) +
        (fderivWithin ℝ
          (fun yE : F ↦
            SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
              (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
          (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
          (X t ((G.maps3 t) x))) t := by
  let y : ℝ → M := fun τ ↦ (G.maps3 τ) x
  let xK : ℝ → K :=
    compactCurveOfEventuallyMem (K : Set M) y t hmem_t
  have hxK : Filter.Tendsto xK (𝓝 t) (𝓝 (xK t)) := by
    exact compactCurveOfEventuallyMem_tendsto
      (K := (K : Set M)) (y := y) (t := t) (hy_t := hmem_t)
      (G.continuousAt_eval hs x) hmem
  have hxK_eval : (fun τ : ℝ ↦ (xK τ).1) =ᶠ[𝓝 t]
      fun τ : ℝ ↦ (G.maps3 τ) x := by
    exact compactCurveOfEventuallyMem_eventually_val_eq
      (K := (K : Set M)) (y := y) (t := t) (hy_t := hmem_t) hmem
  have hmain :=
    realization.metricBilinearCoordinateField_hasDerivAt_along_gauge_eval_of_target_coord_mem_Ioo
      (M := M) (F := F) (I := I) G hs ht i K x hK_sub_Kc hK_sub_target
      hxK hxK_eval
  simpa [xK, y, compactCurveOfEventuallyMem, hmem_t] using hmain

/-- Open-interval target-centered raw gauge derivative from interior
membership in the selected compact overlap piece. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_hasDerivAt_along_gauge_eval_of_mem_interior_target_K_Ioo
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (hs : s ∈ 𝓝 t)
    (ht : t ∈ Ioo ivp.initialTime sol.terminalTime)
    (i : κ) (K : TopologicalSpace.Compacts M) (x : M)
    (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
    (hK_sub_target : (K : Set M) ⊆
      (trivializationAt BilF
        (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        ((G.maps3 t) x)).baseSet)
    (hmem_int : (G.maps3 t) x ∈ interior (K : Set M)) :
    HasDerivAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric ((G.maps3 t) x)
          (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)))
      ((targetBilinearCoordReadoutContinuousLinearMap
          (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
          (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
          ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target
          (A t (sol.curve t))
          (⟨(G.maps3 t) x, interior_subset hmem_int⟩ : K)) +
        (fderivWithin ℝ
          (fun yE : F ↦
            SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
              (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
          (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
          (X t ((G.maps3 t) x))) t := by
  have hmem_t : (G.maps3 t) x ∈ (K : Set M) := interior_subset hmem_int
  have hmem : ∀ᶠ τ in 𝓝 t, (G.maps3 τ) x ∈ (K : Set M) :=
    eventually_mem_of_tendsto_of_mem_interior (G.continuousAt_eval hs x) hmem_int
  exact
    realization.metricBilinearCoordinateField_hasDerivAt_along_gauge_eval_of_eventually_mem_target_K_Ioo
      (M := M) (F := F) (I := I) G hs ht i K x hK_sub_Kc hK_sub_target
      hmem_t hmem

/-- Open-interval target-centered raw gauge derivative with the compact
overlap piece selected internally.  The only finite-cover hypothesis is that
the time-`t` gauge point lies in the interior of the chosen compact cover
piece; local compactness of the finite-dimensional manifold supplies a smaller
compact neighborhood contained both in that cover piece and in the target
trivialization at the gauge point. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_hasDerivAt_along_gauge_eval_of_mem_interior_Kc_target_overlap_Ioo
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (hs : s ∈ 𝓝 t)
    (ht : t ∈ Ioo ivp.initialTime sol.terminalTime)
    (i : κ) (x : M)
    (hmem_int : (G.maps3 t) x ∈ interior (Kc i : Set M)) :
    ∃ (K : TopologicalSpace.Compacts M)
      (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
      (hK_sub_target : (K : Set M) ⊆
        (trivializationAt BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          ((G.maps3 t) x)).baseSet)
      (hKmem_int : (G.maps3 t) x ∈ interior (K : Set M)),
      HasDerivAt
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)))
        ((targetBilinearCoordReadoutContinuousLinearMap
            (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
            (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
            ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target
            (A t (sol.curve t))
            (⟨(G.maps3 t) x, interior_subset hKmem_int⟩ : K)) +
          (fderivWithin ℝ
            (fun yE : F ↦
              SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
                (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
            (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
            (X t ((G.maps3 t) x))) t := by
  haveI : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional (I := I)
  let p : M := (G.maps3 t) x
  let U : Set M :=
    (trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) p).baseSet
  have hpU : p ∈ U := by
    simpa [U] using
      (mem_baseSet_trivializationAt BilF
        (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) p)
  have hUopen : IsOpen U := by
    simpa [U] using
      (trivializationAt BilF
        (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) p).open_baseSet
  rcases exists_compact_subset_interior_inter_open
      (M := M) (p := p) (K₀ := (Kc i : Set M)) (U := U)
      (by simpa [p] using hmem_int) hUopen hpU with
    ⟨K, hKmem_int, hK_sub_Kc, hK_sub_U⟩
  have hK_sub_target : (K : Set M) ⊆
      (trivializationAt BilF
        (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        ((G.maps3 t) x)).baseSet := by
    simpa [p, U] using hK_sub_U
  have hKmem_int' : (G.maps3 t) x ∈ interior (K : Set M) := by
    simpa [p] using hKmem_int
  refine ⟨K, hK_sub_Kc, hK_sub_target, hKmem_int', ?_⟩
  simpa using
    realization.metricBilinearCoordinateField_hasDerivAt_along_gauge_eval_of_mem_interior_target_K_Ioo
      (M := M) (F := F) (I := I) G hs ht i K x hK_sub_Kc hK_sub_target hKmem_int'

/-- Open-interval target-centered raw gauge derivative from an
interior-covering compact family.  The wrapper selects both the finite-cover
index and the smaller compact overlap with the target trivialization at the
time-`t` gauge point. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_hasDerivAt_along_gauge_eval_of_interior_cover_target_overlap_Ioo
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (hcover_int : (⋃ i, interior (Kc i : Set M)) = Set.univ)
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (hs : s ∈ 𝓝 t)
    (ht : t ∈ Ioo ivp.initialTime sol.terminalTime)
    (x : M) :
    ∃ (i : κ) (K : TopologicalSpace.Compacts M)
      (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
      (hK_sub_target : (K : Set M) ⊆
        (trivializationAt BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          ((G.maps3 t) x)).baseSet)
      (hKmem_int : (G.maps3 t) x ∈ interior (K : Set M)),
      HasDerivAt
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)))
        ((targetBilinearCoordReadoutContinuousLinearMap
            (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
            (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
            ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target
            (A t (sol.curve t))
            (⟨(G.maps3 t) x, interior_subset hKmem_int⟩ : K)) +
          (fderivWithin ℝ
            (fun yE : F ↦
              SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
                (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
            (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
            (X t ((G.maps3 t) x))) t := by
  haveI : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional (I := I)
  let p : M := (G.maps3 t) x
  let U : Set M :=
    (trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) p).baseSet
  have hpU : p ∈ U := by
    simpa [U] using
      (mem_baseSet_trivializationAt BilF
        (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) p)
  have hUopen : IsOpen U := by
    simpa [U] using
      (trivializationAt BilF
        (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) p).open_baseSet
  rcases exists_compact_subset_interior_cover_inter_open
      (M := M) (p := p) (Kc := Kc) hcover_int hUopen hpU with
    ⟨i, K, hKmem_int, hK_sub_Kc, hK_sub_U⟩
  have hK_sub_target : (K : Set M) ⊆
      (trivializationAt BilF
        (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        ((G.maps3 t) x)).baseSet := by
    simpa [p, U] using hK_sub_U
  have hKmem_int' : (G.maps3 t) x ∈ interior (K : Set M) := by
    simpa [p] using hKmem_int
  refine ⟨i, K, hK_sub_Kc, hK_sub_target, hKmem_int', ?_⟩
  simpa using
    realization.metricBilinearCoordinateField_hasDerivAt_along_gauge_eval_of_mem_interior_target_K_Ioo
      (M := M) (F := F) (I := I) G hs ht i K x hK_sub_Kc hK_sub_target hKmem_int'

/-- Open-interval raw gauge-flow metric-coordinate derivative from eventual
membership in one preferred compact cover piece.  This builds the selected
compact chart curve internally from the eventual membership witness. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_hasDerivAt_along_gauge_eval_of_eventually_mem_Kc_Ioo
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (hs : s ∈ 𝓝 t)
    (ht : t ∈ Ioo ivp.initialTime sol.terminalTime)
    (i : κ) (x : M)
    (hcenter : x0 i = (G.maps3 t) x)
    (hmem_t : (G.maps3 t) x ∈ (Kc i : Set M))
    (hmem : ∀ᶠ τ in 𝓝 t, (G.maps3 τ) x ∈ (Kc i : Set M)) :
    HasDerivAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric ((G.maps3 t) x)
          (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)))
      (((equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (A t (sol.curve t))).1 i
          (⟨(G.maps3 t) x, hmem_t⟩ : Kc i)) +
        (fderivWithin ℝ
          (fun yE : F ↦
            SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
              (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
          (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
          (X t ((G.maps3 t) x))) t := by
  let y : ℝ → M := fun τ ↦ (G.maps3 τ) x
  let xK : ℝ → Kc i :=
    compactCurveOfEventuallyMem (Kc i : Set M) y t hmem_t
  have hxK : Filter.Tendsto xK (𝓝 t) (𝓝 (xK t)) := by
    exact compactCurveOfEventuallyMem_tendsto
      (K := (Kc i : Set M)) (y := y) (t := t) (hy_t := hmem_t)
      (G.continuousAt_eval hs x) hmem
  have hxK_eval : (fun τ : ℝ ↦ (xK τ).1) =ᶠ[𝓝 t]
      fun τ : ℝ ↦ (G.maps3 τ) x := by
    exact compactCurveOfEventuallyMem_eventually_val_eq
      (K := (Kc i : Set M)) (y := y) (t := t) (hy_t := hmem_t) hmem
  have hmain :=
    realization.metricBilinearCoordinateField_hasDerivAt_along_gauge_eval_of_coord_mem_Ioo
      (M := M) (F := F) (I := I) het G hs ht i x hcenter hxK hxK_eval
  simpa [xK, y, compactCurveOfEventuallyMem, hmem_t] using hmain

/-- Open-interval raw gauge-flow metric-coordinate derivative from membership
of the time-`t` gauge point in the interior of one compact cover piece.  The
interior hypothesis is exactly what turns continuity of the gauge orbit into
the eventual compact-membership witness used by
`metricBilinearCoordinateField_hasDerivAt_along_gauge_eval_of_eventually_mem_Kc_Ioo`. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_hasDerivAt_along_gauge_eval_of_mem_interior_Kc_Ioo
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (hs : s ∈ 𝓝 t)
    (ht : t ∈ Ioo ivp.initialTime sol.terminalTime)
    (i : κ) (x : M)
    (hcenter : x0 i = (G.maps3 t) x)
    (hmem_int : (G.maps3 t) x ∈ interior (Kc i : Set M)) :
    HasDerivAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric ((G.maps3 t) x)
          (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)))
      (((equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (A t (sol.curve t))).1 i
          (⟨(G.maps3 t) x, interior_subset hmem_int⟩ : Kc i)) +
        (fderivWithin ℝ
          (fun yE : F ↦
            SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
              (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
          (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
          (X t ((G.maps3 t) x))) t := by
  have hmem_t : (G.maps3 t) x ∈ (Kc i : Set M) := interior_subset hmem_int
  have hmem : ∀ᶠ τ in 𝓝 t, (G.maps3 τ) x ∈ (Kc i : Set M) :=
    eventually_mem_of_tendsto_of_mem_interior (G.continuousAt_eval hs x) hmem_int
  exact
    realization.metricBilinearCoordinateField_hasDerivAt_along_gauge_eval_of_eventually_mem_Kc_Ioo
      (M := M) (F := F) (I := I) het G hs ht i x hcenter hmem_t hmem

/-- Right-sided raw gauge-flow metric-coordinate derivative from the Banach
moving time-difference bridge.  The raw time set is allowed to be any set lying
to the right of `t`, matching the one-sided Banach derivative. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_hasDerivWithinAt_along_gauge_eval_of_coord_mem_Ico
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (htG : t ∈ s)
    (hs_sub : s ⊆ Ici t)
    (ht : t ∈ Ico ivp.initialTime sol.terminalTime)
    (i : κ) (x : M)
    (hcenter : x0 i = (G.maps3 t) x)
    {xK : ℝ → Kc i}
    (hxK : Filter.Tendsto xK (𝓝[Ici t] t) (𝓝 (xK t)))
    (hxK_eval : (fun τ : ℝ ↦ (xK τ).1) =ᶠ[𝓝[Ici t] t]
      fun τ : ℝ ↦ (G.maps3 τ) x) :
    HasDerivWithinAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric ((G.maps3 t) x)
          (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)))
      (((equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (A t (sol.curve t))).1 i (xK t)) +
        (fderivWithin ℝ
          (fun yE : F ↦
            SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
              (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
          (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
          (X t ((G.maps3 t) x))) s t := by
  have htime_coord :=
    realization.metricBilinearCoordinateField_timeDifference_hasDerivWithinAt_Ici_of_coord_mem_Ico
      (M := M) (F := F) (I := I) het i ht hxK
  have htime_Ici :
      HasDerivWithinAt
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)) -
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (t, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)))
        ((equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (A t (sol.curve t))).1 i (xK t)) (Ici t) t := by
    have hEq :
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)) -
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (t, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x))) =ᶠ[𝓝[Ici t] t]
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric (x0 i)
            (τ, (extChartAt I (x0 i)) (xK τ).1) -
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric (x0 i)
            (t, (extChartAt I (x0 i)) (xK τ).1)) := by
      filter_upwards [hxK_eval] with τ hτ
      rw [← hcenter, ← hτ]
    exact htime_coord.congr_of_eventuallyEq_of_mem hEq (Set.mem_Ici.mpr le_rfl)
  have htime_s := htime_Ici.mono hs_sub
  simpa using
    SmoothSelfDiffeomorph3Family.Diffeomorph3GaugeFlowOn.metricBilinearCoordinateField_hasDerivWithinAt_of_timeDifference_along_eval_self
      (I := I) (M := M) G htG realization.metric x htime_s

/-- Right-sided raw gauge-flow metric-coordinate derivative when the selected
compact chart curve agrees with the gauge orbit only relative to the raw time
set.  This form is useful for closed interval gauges: the Banach
time-difference is still taken on `Ici t`, while the final raw derivative is
only within `s`. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_hasDerivWithinAt_along_gauge_eval_of_coord_mem_timeSet_Ico
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (htG : t ∈ s)
    (hs_sub : s ⊆ Ici t)
    (ht : t ∈ Ico ivp.initialTime sol.terminalTime)
    (i : κ) (x : M)
    (hcenter : x0 i = (G.maps3 t) x)
    {xK : ℝ → Kc i}
    (hxK : Filter.Tendsto xK (𝓝[Ici t] t) (𝓝 (xK t)))
    (hxK_eval : (fun τ : ℝ ↦ (xK τ).1) =ᶠ[𝓝[s] t]
      fun τ : ℝ ↦ (G.maps3 τ) x) :
    HasDerivWithinAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric ((G.maps3 t) x)
          (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)))
      (((equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (A t (sol.curve t))).1 i (xK t)) +
        (fderivWithin ℝ
          (fun yE : F ↦
            SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
              (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
          (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
          (X t ((G.maps3 t) x))) s t := by
  have htime_coord :=
    realization.metricBilinearCoordinateField_timeDifference_hasDerivWithinAt_Ici_of_coord_mem_Ico
      (M := M) (F := F) (I := I) het i ht hxK
  have htime_coord_s := htime_coord.mono hs_sub
  have htime_s :
      HasDerivWithinAt
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)) -
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (t, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)))
        ((equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (A t (sol.curve t))).1 i (xK t)) s t := by
    have hEq :
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)) -
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (t, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x))) =ᶠ[𝓝[s] t]
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric (x0 i)
            (τ, (extChartAt I (x0 i)) (xK τ).1) -
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric (x0 i)
            (t, (extChartAt I (x0 i)) (xK τ).1)) := by
      filter_upwards [hxK_eval] with τ hτ
      rw [← hcenter, ← hτ]
    exact htime_coord_s.congr_of_eventuallyEq_of_mem hEq htG
  simpa using
    SmoothSelfDiffeomorph3Family.Diffeomorph3GaugeFlowOn.metricBilinearCoordinateField_hasDerivWithinAt_of_timeDifference_along_eval_self
      (I := I) (M := M) G htG realization.metric x htime_s

/-- Right-sided target-centered raw gauge-flow metric-coordinate derivative
when the selected compact curve agrees with the gauge orbit only relative to
the raw time set. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_hasDerivWithinAt_along_gauge_eval_of_target_coord_mem_timeSet_Ico
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (htG : t ∈ s)
    (hs_sub : s ⊆ Ici t)
    (ht : t ∈ Ico ivp.initialTime sol.terminalTime)
    (i : κ) (K : TopologicalSpace.Compacts M) (x : M)
    (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
    (hK_sub_target : (K : Set M) ⊆
      (trivializationAt BilF
        (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        ((G.maps3 t) x)).baseSet)
    {xK : ℝ → K}
    (hxK : Filter.Tendsto xK (𝓝[Ici t] t) (𝓝 (xK t)))
    (hxK_eval : (fun τ : ℝ ↦ (xK τ).1) =ᶠ[𝓝[s] t]
      fun τ : ℝ ↦ (G.maps3 τ) x) :
    HasDerivWithinAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric ((G.maps3 t) x)
          (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)))
      ((targetBilinearCoordReadoutContinuousLinearMap
          (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
          (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
          ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target
          (A t (sol.curve t)) (xK t)) +
        (fderivWithin ℝ
          (fun yE : F ↦
            SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
              (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
          (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
          (X t ((G.maps3 t) x))) s t := by
  have htime_coord :=
    realization.metricBilinearCoordinateField_timeDifference_hasDerivWithinAt_Ici_of_target_coord_mem_Ico
      (M := M) (F := F) (I := I)
      ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target ht hxK
  have htime_coord_s := htime_coord.mono hs_sub
  have htime_s :
      HasDerivWithinAt
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)) -
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (t, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)))
        (targetBilinearCoordReadoutContinuousLinearMap
          (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
          (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
          ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target
          (A t (sol.curve t)) (xK t)) s t := by
    have hEq :
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)) -
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (t, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x))) =ᶠ[𝓝[s] t]
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (τ, (extChartAt I ((G.maps3 t) x)) (xK τ).1) -
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (t, (extChartAt I ((G.maps3 t) x)) (xK τ).1)) := by
      filter_upwards [hxK_eval] with τ hτ
      rw [← hτ]
    exact htime_coord_s.congr_of_eventuallyEq_of_mem hEq htG
  simpa using
    SmoothSelfDiffeomorph3Family.Diffeomorph3GaugeFlowOn.metricBilinearCoordinateField_hasDerivWithinAt_of_timeDifference_along_eval_self
      (I := I) (M := M) G htG realization.metric x htime_s

/-- Right-sided target-centered raw gauge derivative from eventual membership
in the compact overlap piece, relative to the raw time set. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_hasDerivWithinAt_along_gauge_eval_of_eventually_mem_target_K_Ico
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (htG : t ∈ s)
    (hs_sub : s ⊆ Ici t)
    (ht : t ∈ Ico ivp.initialTime sol.terminalTime)
    (i : κ) (K : TopologicalSpace.Compacts M) (x : M)
    (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
    (hK_sub_target : (K : Set M) ⊆
      (trivializationAt BilF
        (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        ((G.maps3 t) x)).baseSet)
    (hmem_t : (G.maps3 t) x ∈ (K : Set M))
    (hmem : ∀ᶠ τ in 𝓝[s] t, (G.maps3 τ) x ∈ (K : Set M)) :
    HasDerivWithinAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric ((G.maps3 t) x)
          (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)))
      ((targetBilinearCoordReadoutContinuousLinearMap
          (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
          (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
          ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target
          (A t (sol.curve t)) (⟨(G.maps3 t) x, hmem_t⟩ : K)) +
        (fderivWithin ℝ
          (fun yE : F ↦
            SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
              (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
          (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
          (X t ((G.maps3 t) x))) s t := by
  let y : ℝ → M := fun τ ↦ (G.maps3 τ) x
  let xK : ℝ → K :=
    compactCurveOfEventuallyMemOnSet (K : Set M) y s t hmem_t
  have hxK : Filter.Tendsto xK (𝓝[Ici t] t) (𝓝 (xK t)) := by
    exact compactCurveOfEventuallyMemOnSet_tendsto_Ici
      (K := (K : Set M)) (y := y) (s := s) (t := t) (hy_t := hmem_t)
      htG (G.continuousWithinAt_eval htG x) hmem
  have hxK_eval : (fun τ : ℝ ↦ (xK τ).1) =ᶠ[𝓝[s] t]
      fun τ : ℝ ↦ (G.maps3 τ) x := by
    exact compactCurveOfEventuallyMemOnSet_eventually_val_eq
      (K := (K : Set M)) (y := y) (s := s) (t := t) (hy_t := hmem_t) hmem
  have hmain :=
    realization.metricBilinearCoordinateField_hasDerivWithinAt_along_gauge_eval_of_target_coord_mem_timeSet_Ico
      (M := M) (F := F) (I := I) G htG hs_sub ht i K x hK_sub_Kc hK_sub_target
      hxK hxK_eval
  simpa [xK, y, compactCurveOfEventuallyMemOnSet, htG, hmem_t] using hmain

/-- Right-sided target-centered raw gauge derivative from interior membership
in the compact overlap piece. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_hasDerivWithinAt_along_gauge_eval_of_mem_interior_target_K_Ico
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (htG : t ∈ s)
    (hs_sub : s ⊆ Ici t)
    (ht : t ∈ Ico ivp.initialTime sol.terminalTime)
    (i : κ) (K : TopologicalSpace.Compacts M) (x : M)
    (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
    (hK_sub_target : (K : Set M) ⊆
      (trivializationAt BilF
        (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        ((G.maps3 t) x)).baseSet)
    (hmem_int : (G.maps3 t) x ∈ interior (K : Set M)) :
    HasDerivWithinAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric ((G.maps3 t) x)
          (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)))
      ((targetBilinearCoordReadoutContinuousLinearMap
          (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
          (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
          ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target
          (A t (sol.curve t))
          (⟨(G.maps3 t) x, interior_subset hmem_int⟩ : K)) +
        (fderivWithin ℝ
          (fun yE : F ↦
            SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
              (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
          (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
          (X t ((G.maps3 t) x))) s t := by
  have hmem_t : (G.maps3 t) x ∈ (K : Set M) := interior_subset hmem_int
  have hmem : ∀ᶠ τ in 𝓝[s] t, (G.maps3 τ) x ∈ (K : Set M) :=
    eventually_mem_of_tendsto_of_mem_interior (G.continuousWithinAt_eval htG x) hmem_int
  exact
    realization.metricBilinearCoordinateField_hasDerivWithinAt_along_gauge_eval_of_eventually_mem_target_K_Ico
      (M := M) (F := F) (I := I) G htG hs_sub ht i K x hK_sub_Kc hK_sub_target
      hmem_t hmem

/-- Right-sided target-centered raw gauge derivative with the compact overlap
piece selected internally.  This is the endpoint analogue of
`metricBilinearCoordinateField_hasDerivAt_along_gauge_eval_of_mem_interior_Kc_target_overlap_Ioo`. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_hasDerivWithinAt_along_gauge_eval_of_mem_interior_Kc_target_overlap_Ico
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (htG : t ∈ s)
    (hs_sub : s ⊆ Ici t)
    (ht : t ∈ Ico ivp.initialTime sol.terminalTime)
    (i : κ) (x : M)
    (hmem_int : (G.maps3 t) x ∈ interior (Kc i : Set M)) :
    ∃ (K : TopologicalSpace.Compacts M)
      (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
      (hK_sub_target : (K : Set M) ⊆
        (trivializationAt BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          ((G.maps3 t) x)).baseSet)
      (hKmem_int : (G.maps3 t) x ∈ interior (K : Set M)),
      HasDerivWithinAt
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)))
        ((targetBilinearCoordReadoutContinuousLinearMap
            (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
            (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
            ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target
            (A t (sol.curve t))
            (⟨(G.maps3 t) x, interior_subset hKmem_int⟩ : K)) +
          (fderivWithin ℝ
            (fun yE : F ↦
              SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
                (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
            (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
            (X t ((G.maps3 t) x))) s t := by
  haveI : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional (I := I)
  let p : M := (G.maps3 t) x
  let U : Set M :=
    (trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) p).baseSet
  have hpU : p ∈ U := by
    simpa [U] using
      (mem_baseSet_trivializationAt BilF
        (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) p)
  have hUopen : IsOpen U := by
    simpa [U] using
      (trivializationAt BilF
        (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) p).open_baseSet
  rcases exists_compact_subset_interior_inter_open
      (M := M) (p := p) (K₀ := (Kc i : Set M)) (U := U)
      (by simpa [p] using hmem_int) hUopen hpU with
    ⟨K, hKmem_int, hK_sub_Kc, hK_sub_U⟩
  have hK_sub_target : (K : Set M) ⊆
      (trivializationAt BilF
        (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        ((G.maps3 t) x)).baseSet := by
    simpa [p, U] using hK_sub_U
  have hKmem_int' : (G.maps3 t) x ∈ interior (K : Set M) := by
    simpa [p] using hKmem_int
  refine ⟨K, hK_sub_Kc, hK_sub_target, hKmem_int', ?_⟩
  simpa using
    realization.metricBilinearCoordinateField_hasDerivWithinAt_along_gauge_eval_of_mem_interior_target_K_Ico
      (M := M) (F := F) (I := I) G htG hs_sub ht i K x hK_sub_Kc hK_sub_target
      hKmem_int'

/-- Right-sided target-centered raw gauge derivative from an interior-covering
compact family.  This is the endpoint analogue of
`metricBilinearCoordinateField_hasDerivAt_along_gauge_eval_of_interior_cover_target_overlap_Ioo`. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_hasDerivWithinAt_along_gauge_eval_of_interior_cover_target_overlap_Ico
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (hcover_int : (⋃ i, interior (Kc i : Set M)) = Set.univ)
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (htG : t ∈ s)
    (hs_sub : s ⊆ Ici t)
    (ht : t ∈ Ico ivp.initialTime sol.terminalTime)
    (x : M) :
    ∃ (i : κ) (K : TopologicalSpace.Compacts M)
      (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
      (hK_sub_target : (K : Set M) ⊆
        (trivializationAt BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          ((G.maps3 t) x)).baseSet)
      (hKmem_int : (G.maps3 t) x ∈ interior (K : Set M)),
      HasDerivWithinAt
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)))
        ((targetBilinearCoordReadoutContinuousLinearMap
            (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
            (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
            ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target
            (A t (sol.curve t))
            (⟨(G.maps3 t) x, interior_subset hKmem_int⟩ : K)) +
          (fderivWithin ℝ
            (fun yE : F ↦
              SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
                (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
            (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
            (X t ((G.maps3 t) x))) s t := by
  haveI : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional (I := I)
  let p : M := (G.maps3 t) x
  let U : Set M :=
    (trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) p).baseSet
  have hpU : p ∈ U := by
    simpa [U] using
      (mem_baseSet_trivializationAt BilF
        (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) p)
  have hUopen : IsOpen U := by
    simpa [U] using
      (trivializationAt BilF
        (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) p).open_baseSet
  rcases exists_compact_subset_interior_cover_inter_open
      (M := M) (p := p) (Kc := Kc) hcover_int hUopen hpU with
    ⟨i, K, hKmem_int, hK_sub_Kc, hK_sub_U⟩
  have hK_sub_target : (K : Set M) ⊆
      (trivializationAt BilF
        (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        ((G.maps3 t) x)).baseSet := by
    simpa [p, U] using hK_sub_U
  have hKmem_int' : (G.maps3 t) x ∈ interior (K : Set M) := by
    simpa [p] using hKmem_int
  refine ⟨i, K, hK_sub_Kc, hK_sub_target, hKmem_int', ?_⟩
  simpa using
    realization.metricBilinearCoordinateField_hasDerivWithinAt_along_gauge_eval_of_mem_interior_target_K_Ico
      (M := M) (F := F) (I := I) G htG hs_sub ht i K x hK_sub_Kc hK_sub_target
      hKmem_int'

/-- Interior-cover target-overlap scalar derivatives supply the concrete
component derivative package for a raw non-identity gauge, once the tangent-map
derivative and final scalar velocity identity are provided.

This is the first downstream consumer of
`metricBilinearCoordinateField_hasDerivAt_along_gauge_eval_of_interior_cover_target_overlap_Ioo`:
the finite-cover selector now feeds the named component API used by the
non-identity gauge-pullback time-regularity route. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.coordinatePullbackMetricComponentDerivativeOn_of_interior_cover_target_overlap_Ioo
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (hcover_int : (⋃ i, interior (Kc i : Set M)) = Set.univ)
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (hs : ∀ ⦃t : ℝ⦄, t ∈ s → s ∈ 𝓝 t)
    (hsIoo : s ⊆ Ioo ivp.initialTime sol.terminalTime)
    {gdot : MetricTensorFamily (I := I) (M := M)}
    (hA : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∃ D : F →L[ℝ] F,
        HasDerivAt
          (fun τ : ℝ ↦
            SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
              (I := I) (M := M) G.maps3 t τ x)
          (D.comp
            (SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
              (I := I) (M := M) G.maps3 t t x)) t)
    (hvalue : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ u v : TangentSpace I x,
      ∀ (i : κ) (K : TopologicalSpace.Compacts M)
        (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
        (hK_sub_target : (K : Set M) ⊆
          (trivializationAt BilF
            (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            ((G.maps3 t) x)).baseSet)
        (hKmem_int : (G.maps3 t) x ∈ interior (K : Set M))
        (D : F →L[ℝ] F),
        (let B' : F →L[ℝ] F →L[ℝ] ℝ :=
          (targetBilinearCoordReadoutContinuousLinearMap
            (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
            (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
            ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target
            (A t (sol.curve t))
            (⟨(G.maps3 t) x, interior_subset hKmem_int⟩ : K)) +
          (fderivWithin ℝ
            (fun yE : F ↦
              SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
                (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
            (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
            (X t ((G.maps3 t) x));
        B'
          (SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t t x
            (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) x u))
          (SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t t x
            (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) x v)) +
          SmoothSelfDiffeomorph3Family.pullbackMetricBilinearCoordinateMap
            (I := I) (M := M) G.maps3 realization.metric t t x
            (D (SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
              (I := I) (M := M) G.maps3 t t x
              (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) x u)))
            (SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
              (I := I) (M := M) G.maps3 t t x
              (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) x v)) +
          SmoothSelfDiffeomorph3Family.pullbackMetricBilinearCoordinateMap
            (I := I) (M := M) G.maps3 realization.metric t t x
            (SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
              (I := I) (M := M) G.maps3 t t x
              (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) x u))
            (D (SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
              (I := I) (M := M) G.maps3 t t x
              (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) x v))) =
        gdot t x u v)) :
    SmoothSelfDiffeomorph3Family.CoordinatePullbackMetricComponentDerivativeOn
      (I := I) (M := M) G.maps3 realization.metric gdot s := by
  intro t ht x u v
  obtain ⟨D, hD⟩ := hA ht x
  obtain ⟨i, K, hK_sub_Kc, hK_sub_target, hKmem_int, hmetric⟩ :=
    realization.metricBilinearCoordinateField_hasDerivAt_along_gauge_eval_of_interior_cover_target_overlap_Ioo
      (M := M) (F := F) (I := I) hcover_int G (hs ht) (hsIoo ht) x
  let B' : F →L[ℝ] F →L[ℝ] ℝ :=
    (targetBilinearCoordReadoutContinuousLinearMap
      (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
      ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target
      (A t (sol.curve t))
      (⟨(G.maps3 t) x, interior_subset hKmem_int⟩ : K)) +
    (fderivWithin ℝ
      (fun yE : F ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
      (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
      (X t ((G.maps3 t) x))
  refine ⟨B', D, ?_, hD, ?_⟩
  · have hB :
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricBilinearCoordinateMap
            (I := I) (M := M) G.maps3 realization.metric t τ x) =ᶠ[𝓝 t]
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x))) :=
      SmoothSelfDiffeomorph3Family.pullbackMetricBilinearCoordinateMap_eventuallyEq_metricBilinearCoordinateField
        (I := I) (M := M) G.maps3 realization.metric t x
        (G.eventually_mem_trivializationAt_eval (hs (t := t) ht) x)
    exact hmetric.congr_of_eventuallyEq hB
  · simpa [B'] using
      hvalue ht x u v i K hK_sub_Kc hK_sub_target hKmem_int D

/-- Interior-cover target-overlap scalar derivatives plus a variational tangent
map identification supply the concrete component derivative package, with the
remaining scalar identity stated in actual pushed-forward tangent-vector slots.

Compared with
`coordinatePullbackMetricComponentDerivativeOn_of_interior_cover_target_overlap_Ioo`,
this theorem fills the tangent-coordinate derivative from the selected
`VariationalLocalFlowSolution` and specializes the velocity contribution to
`Df t (α.flow (xE, t))`, so callers no longer have to provide an abstract
`hA` package or a scalar identity for every possible `D`. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.coordinatePullbackMetricComponentDerivativeOn_of_variationalTangentMap_interior_cover_target_overlap_Ioo_geometricValue
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (hcover_int : (⋃ i, interior (Kc i : Set M)) = Set.univ)
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (hs : ∀ ⦃t : ℝ⦄, t ∈ s → s ∈ 𝓝 t)
    (hsIoo : s ⊆ Ioo ivp.initialTime sol.terminalTime)
    {tmin tmax : ℝ} {τ₀ : Icc tmin tmax}
    {f : ℝ → F → F} {Df : ℝ → F → F →L[ℝ] F}
    {x₀ : F} {r : ℝ≥0}
    (α : ModelGaugeFlowODE.VariationalLocalFlowSolution f Df τ₀ x₀ r)
    (hsModel : s ⊆ Ioo tmin tmax)
    {gdot : MetricTensorFamily (I := I) (M := M)}
    (hA_eq : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∃ xE : F, xE ∈ Metric.closedBall x₀ r ∧
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ))
    (hvalue : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ u v : TangentSpace I x,
      ∀ (i : κ) (K : TopologicalSpace.Compacts M)
        (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
        (hK_sub_target : (K : Set M) ⊆
          (trivializationAt BilF
            (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            ((G.maps3 t) x)).baseSet)
        (hKmem_int : (G.maps3 t) x ∈ interior (K : Set M)),
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        (let B' : F →L[ℝ] F →L[ℝ] ℝ :=
          (targetBilinearCoordReadoutContinuousLinearMap
            (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
            (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
            ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target
            (A t (sol.curve t))
            (⟨(G.maps3 t) x, interior_subset hKmem_int⟩ : K)) +
          (fderivWithin ℝ
            (fun yE : F ↦
              SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
                (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
            (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
            (X t ((G.maps3 t) x));
        B'
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
            ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x u))
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
            ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x v)) +
          (realization.metric t).inner ((G.maps3 t) x)
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I)
              ((G.maps3 t) x)
              ((Df t (α.flow (xE, t)))
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
                  ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x u))))
            ((G.maps3 t).pushforwardTangent x v) +
          (realization.metric t).inner ((G.maps3 t) x)
            ((G.maps3 t).pushforwardTangent x u)
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I)
              ((G.maps3 t) x)
              ((Df t (α.flow (xE, t)))
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
                  ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x v)))) =
        gdot t x u v)) :
    SmoothSelfDiffeomorph3Family.CoordinatePullbackMetricComponentDerivativeOn
      (I := I) (M := M) G.maps3 realization.metric gdot s := by
  intro t ht x u v
  obtain ⟨xE, hxE, hAeq⟩ := hA_eq ht x
  obtain ⟨i, K, hK_sub_Kc, hK_sub_target, hKmem_int, hmetric⟩ :=
    realization.metricBilinearCoordinateField_hasDerivAt_along_gauge_eval_of_interior_cover_target_overlap_Ioo
      (M := M) (F := F) (I := I) hcover_int G (hs ht) (hsIoo ht) x
  let B' : F →L[ℝ] F →L[ℝ] ℝ :=
    (targetBilinearCoordReadoutContinuousLinearMap
      (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
      ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target
      (A t (sol.curve t))
      (⟨(G.maps3 t) x, interior_subset hKmem_int⟩ : K)) +
    (fderivWithin ℝ
      (fun yE : F ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
      (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
      (X t ((G.maps3 t) x))
  refine ⟨B', Df t (α.flow (xE, t)), ?_, ?_, ?_⟩
  · have hB :
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricBilinearCoordinateMap
            (I := I) (M := M) G.maps3 realization.metric t τ x) =ᶠ[𝓝 t]
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x))) :=
      SmoothSelfDiffeomorph3Family.pullbackMetricBilinearCoordinateMap_eventuallyEq_metricBilinearCoordinateField
        (I := I) (M := M) G.maps3 realization.metric t x
        (G.eventually_mem_trivializationAt_eval (hs (t := t) ht) x)
    exact hmetric.congr_of_eventuallyEq hB
  · exact
      SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap_hasDerivAt_of_variationalTangentMap
        (I := I) (M := M) (Φ := G.maps3) α hxE (hsModel ht) x hAeq
  · have hleft :
        SmoothSelfDiffeomorph3Family.pullbackMetricBilinearCoordinateMap
            (I := I) (M := M) G.maps3 realization.metric t t x
            ((Df t (α.flow (xE, t)))
              (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
                ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x u)))
            (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
              ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x v)) =
          (realization.metric t).inner ((G.maps3 t) x)
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I)
              ((G.maps3 t) x)
              ((Df t (α.flow (xE, t)))
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
                  ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x u))))
            ((G.maps3 t).pushforwardTangent x v) := by
      rw [SmoothSelfDiffeomorph3Family.pullbackMetricBilinearCoordinateMap_self_apply_eq]
      simp [SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate,
        SmoothSelfDiffeomorph3Family.sourceTangentCoordinate]
    have hright :
        SmoothSelfDiffeomorph3Family.pullbackMetricBilinearCoordinateMap
            (I := I) (M := M) G.maps3 realization.metric t t x
            (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
              ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x u))
            ((Df t (α.flow (xE, t)))
              (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
                ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x v))) =
          (realization.metric t).inner ((G.maps3 t) x)
            ((G.maps3 t).pushforwardTangent x u)
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I)
              ((G.maps3 t) x)
              ((Df t (α.flow (xE, t)))
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
                  ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x v)))) := by
      rw [SmoothSelfDiffeomorph3Family.pullbackMetricBilinearCoordinateMap_self_apply_eq]
      simp [SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate,
        SmoothSelfDiffeomorph3Family.sourceTangentCoordinate]
    rw [SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap_self_sourceTangentCoordinate_eq_targetCoordinate
        (I := I) (M := M) G.maps3 t x u,
      SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap_self_sourceTangentCoordinate_eq_targetCoordinate
        (I := I) (M := M) G.maps3 t x v,
      hleft, hright]
    simpa [B'] using
      hvalue ht x u v i K hK_sub_Kc hK_sub_target hKmem_int xE hxE hAeq

/-- Interior-cover target-overlap scalar derivatives plus local fixed-chart
`EqOn` gluing data for a variational model flow supply the concrete component
derivative package, with the remaining scalar identity stated in actual
pushed-forward tangent-vector slots.

This companion to
`coordinatePullbackMetricComponentDerivativeOn_of_variationalTangentMap_interior_cover_target_overlap_Ioo_geometricValue`
uses the fixed-chart `EqOn` tangent bridge to build the tangent-map
identification internally. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.coordinatePullbackMetricComponentDerivativeOn_of_variationalTangentMap_fixedChartModel_eqOn_interior_cover_target_overlap_Ioo_geometricValue
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (hcover_int : (⋃ i, interior (Kc i : Set M)) = Set.univ)
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (hs : ∀ ⦃t : ℝ⦄, t ∈ s → s ∈ 𝓝 t)
    (hsIoo : s ⊆ Ioo ivp.initialTime sol.terminalTime)
    {tmin tmax : ℝ} {τ₀ : Icc tmin tmax}
    {f : ℝ → F → F} {Df : ℝ → F → F →L[ℝ] F}
    {x₀ : F} {r : ℝ≥0}
    (α : ModelGaugeFlowODE.VariationalLocalFlowSolution f Df τ₀ x₀ r)
    (hsModel : s ⊆ Ioo tmin tmax)
    {gdot : MetricTensorFamily (I := I) (M := M)}
    (hA_model : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∃ xE : F, xE ∈ Metric.closedBall x₀ r ∧
        ∀ᶠ τ in 𝓝 t,
          (G.maps3 τ) x ∈ (extChartAt I ((G.maps3 t) x)).source ∧
            (∃ U : Set M,
              U ∈ 𝓝 x ∧
                EqOn
                  (fun z : M ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) z))
                  (fun z : M ↦ α.flow ((extChartAt I x) z, τ)) U) ∧
            HasFDerivWithinAt (fun y : F ↦ α.flow (y, τ))
              (α.tangent xE τ) (Set.range I) ((extChartAt I x) x))
    (hvalue : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ u v : TangentSpace I x,
      ∀ (i : κ) (K : TopologicalSpace.Compacts M)
        (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
        (hK_sub_target : (K : Set M) ⊆
          (trivializationAt BilF
            (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            ((G.maps3 t) x)).baseSet)
        (hKmem_int : (G.maps3 t) x ∈ interior (K : Set M)),
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        (let B' : F →L[ℝ] F →L[ℝ] ℝ :=
          (targetBilinearCoordReadoutContinuousLinearMap
            (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
            (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
            ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target
            (A t (sol.curve t))
            (⟨(G.maps3 t) x, interior_subset hKmem_int⟩ : K)) +
          (fderivWithin ℝ
            (fun yE : F ↦
              SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
                (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
            (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
            (X t ((G.maps3 t) x));
        B'
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
            ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x u))
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
            ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x v)) +
          (realization.metric t).inner ((G.maps3 t) x)
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I)
              ((G.maps3 t) x)
              ((Df t (α.flow (xE, t)))
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
                  ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x u))))
            ((G.maps3 t).pushforwardTangent x v) +
          (realization.metric t).inner ((G.maps3 t) x)
            ((G.maps3 t).pushforwardTangent x u)
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I)
              ((G.maps3 t) x)
              ((Df t (α.flow (xE, t)))
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
                  ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x v)))) =
        gdot t x u v)) :
    SmoothSelfDiffeomorph3Family.CoordinatePullbackMetricComponentDerivativeOn
      (I := I) (M := M) G.maps3 realization.metric gdot s := by
  have hA_eq : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∃ xE : F, xE ∈ Metric.closedBall x₀ r ∧
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) := by
    intro t ht x
    obtain ⟨xE, hxE, hmodel⟩ := hA_model ht x
    refine ⟨xE, hxE, ?_⟩
    exact
      SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap_eventuallyEq_of_eventually_eqOn_variationalFlow_hasFDerivWithinAt_fixedChart
        (I := I) (M := M) G.maps3 α t x xE hmodel
  exact
    realization.coordinatePullbackMetricComponentDerivativeOn_of_variationalTangentMap_interior_cover_target_overlap_Ioo_geometricValue
      (M := M) (F := F) (I := I) hcover_int G hs hsIoo α hsModel hA_eq hvalue

/-- Interior-cover target-overlap scalar derivatives plus readout-local gluing
data for a lifted variational model flow supply the concrete component
derivative package.

This is the form matched by Picard/local-gluing constructions before the
selected local readout has been pushed through the fixed target chart.  Source
membership in the fixed target chart is derived from the lifted equality and
target-chart membership. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.coordinatePullbackMetricComponentDerivativeOn_of_variationalTangentMap_readout_lifted_eqOn_interior_cover_target_overlap_Ioo_geometricValue
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (hcover_int : (⋃ i, interior (Kc i : Set M)) = Set.univ)
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (hs : ∀ ⦃t : ℝ⦄, t ∈ s → s ∈ 𝓝 t)
    (hsIoo : s ⊆ Ioo ivp.initialTime sol.terminalTime)
    {tmin tmax : ℝ} {τ₀ : Icc tmin tmax}
    {f : ℝ → F → F} {Df : ℝ → F → F →L[ℝ] F}
    {x₀ : F} {r : ℝ≥0}
    (α : ModelGaugeFlowODE.VariationalLocalFlowSolution f Df τ₀ x₀ r)
    (hsModel : s ⊆ Ioo tmin tmax)
    {gdot : MetricTensorFamily (I := I) (M := M)}
    (hA_readout : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∃ xE : F, xE ∈ Metric.closedBall x₀ r ∧
        ∃ Fₗ : ℝ → M → M,
          (∀ᶠ τ in 𝓝 t,
            HasFDerivWithinAt (fun y : F ↦ α.flow (y, τ))
              (α.tangent xE τ) (Set.range I) ((extChartAt I x) x)) ∧
          (∀ᶠ τ in 𝓝 t,
            ∃ U : Set M, U ∈ 𝓝 x ∧
              EqOn (fun z : M ↦ (G.maps3 τ) z) (Fₗ τ) U) ∧
          (∀ᶠ τ in 𝓝 t,
            ∃ V : Set M, V ∈ 𝓝 x ∧
              (∀ z ∈ V,
                α.flow ((extChartAt I x) z, τ) ∈
                  (extChartAt I ((G.maps3 t) x)).target) ∧
              EqOn (Fₗ τ)
                (fun z : M ↦ (extChartAt I ((G.maps3 t) x)).symm
                  (α.flow ((extChartAt I x) z, τ))) V))
    (hvalue : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ u v : TangentSpace I x,
      ∀ (i : κ) (K : TopologicalSpace.Compacts M)
        (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
        (hK_sub_target : (K : Set M) ⊆
          (trivializationAt BilF
            (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            ((G.maps3 t) x)).baseSet)
        (hKmem_int : (G.maps3 t) x ∈ interior (K : Set M)),
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        (let B' : F →L[ℝ] F →L[ℝ] ℝ :=
          (targetBilinearCoordReadoutContinuousLinearMap
            (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
            (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
            ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target
            (A t (sol.curve t))
            (⟨(G.maps3 t) x, interior_subset hKmem_int⟩ : K)) +
          (fderivWithin ℝ
            (fun yE : F ↦
              SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
                (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
            (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
            (X t ((G.maps3 t) x));
        B'
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
            ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x u))
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
            ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x v)) +
          (realization.metric t).inner ((G.maps3 t) x)
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I)
              ((G.maps3 t) x)
              ((Df t (α.flow (xE, t)))
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
                  ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x u))))
            ((G.maps3 t).pushforwardTangent x v) +
          (realization.metric t).inner ((G.maps3 t) x)
            ((G.maps3 t).pushforwardTangent x u)
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I)
              ((G.maps3 t) x)
              ((Df t (α.flow (xE, t)))
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
                  ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x v)))) =
        gdot t x u v)) :
    SmoothSelfDiffeomorph3Family.CoordinatePullbackMetricComponentDerivativeOn
      (I := I) (M := M) G.maps3 realization.metric gdot s := by
  refine
    realization.coordinatePullbackMetricComponentDerivativeOn_of_variationalTangentMap_fixedChartModel_eqOn_interior_cover_target_overlap_Ioo_geometricValue
      (M := M) (F := F) (I := I) hcover_int G hs hsIoo α hsModel ?_ hvalue
  intro t ht x
  obtain ⟨xE, hxE, Fₗ, hderiv, hreadout, hlift⟩ := hA_readout ht x
  refine ⟨xE, hxE, ?_⟩
  exact
    SmoothSelfDiffeomorph3Family.fixedChartModel_eventually_variational_source_exists_nhds_eqOn_hasFDerivWithinAt_of_eventually_readout_lifted_eqOn
      (I := I) (M := M) G.maps3 α t x xE Fₗ hderiv hreadout hlift

/-- Indexed-source-cover form of the readout-lifted variational component
route.

Compact gauge-flow constructions usually expose a finite source cover and a
selected local readout on the chosen cover element.  This adapter selects the
cover element for each base point, derives the lifted target-chart input from
Picard ball membership and the target-chart neighborhood condition, and then
enters the smooth-realization component route. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.coordinatePullbackMetricComponentDerivativeOn_of_variationalTangentMap_readout_mem_ball_iUnion_source_hasFDerivAt_lifted_eqOn_interior_cover_target_overlap_Ioo_geometricValue
    {ι : Type*}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (hcover_int : (⋃ i, interior (Kc i : Set M)) = Set.univ)
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (hs : ∀ ⦃t : ℝ⦄, t ∈ s → s ∈ 𝓝 t)
    (hsIoo : s ⊆ Ioo ivp.initialTime sol.terminalTime)
    {tmin tmax : ℝ} {τ₀ : Icc tmin tmax}
    {f : ℝ → F → F} {Df : ℝ → F → F →L[ℝ] F}
    {x₀ : F} {r : ℝ≥0}
    (α : ModelGaugeFlowODE.VariationalLocalFlowSolution f Df τ₀ x₀ r)
    (hsModel : s ⊆ Ioo tmin tmax)
    {gdot : MetricTensorFamily (I := I) (M := M)}
    (Fₗ : ι → ℝ → M → M)
    (U : ℝ → ι → Set M)
    (hsource_cover : ∀ ⦃t : ℝ⦄, t ∈ s → Set.univ ⊆ ⋃ i, U t i)
    (hreadout : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ i, ∀ x : M, x ∈ U t i →
        ∀ᶠ τ in 𝓝 t,
          ∃ W : Set M, W ∈ 𝓝 x ∧
            EqOn (fun z : M ↦ (G.maps3 τ) z) (Fₗ i τ) W)
    (hflow_deriv : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ ⦃xE : F⦄, xE ∈ Metric.ball x₀ r →
        ∀ᶠ τ in 𝓝 t,
          HasFDerivAt (fun y : F ↦ α.flow (y, τ))
            (α.tangent xE τ) xE)
    (hdata : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ i, ∀ x : M, x ∈ U t i →
        (extChartAt I x) x ∈ Metric.ball x₀ r ∧
        (extChartAt I ((G.maps3 t) x)).target ∈
          𝓝 (α.flow (((extChartAt I x) x), t)) ∧
        ∀ᶠ τ in 𝓝 t,
          ∃ W : Set M, W ∈ 𝓝 x ∧
            EqOn (Fₗ i τ)
              (fun z : M ↦ (extChartAt I ((G.maps3 t) x)).symm
                (α.flow ((extChartAt I x) z, τ))) W)
    (hvalue : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ u v : TangentSpace I x,
      ∀ (i : κ) (K : TopologicalSpace.Compacts M)
        (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
        (hK_sub_target : (K : Set M) ⊆
          (trivializationAt BilF
            (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            ((G.maps3 t) x)).baseSet)
        (hKmem_int : (G.maps3 t) x ∈ interior (K : Set M)),
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        (let B' : F →L[ℝ] F →L[ℝ] ℝ :=
          (targetBilinearCoordReadoutContinuousLinearMap
            (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
            (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
            ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target
            (A t (sol.curve t))
            (⟨(G.maps3 t) x, interior_subset hKmem_int⟩ : K)) +
          (fderivWithin ℝ
            (fun yE : F ↦
              SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
                (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
            (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
            (X t ((G.maps3 t) x));
        B'
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
            ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x u))
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
            ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x v)) +
          (realization.metric t).inner ((G.maps3 t) x)
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I)
              ((G.maps3 t) x)
              ((Df t (α.flow (xE, t)))
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
                  ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x u))))
            ((G.maps3 t).pushforwardTangent x v) +
          (realization.metric t).inner ((G.maps3 t) x)
            ((G.maps3 t).pushforwardTangent x u)
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I)
              ((G.maps3 t) x)
              ((Df t (α.flow (xE, t)))
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
                  ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x v)))) =
        gdot t x u v)) :
    SmoothSelfDiffeomorph3Family.CoordinatePullbackMetricComponentDerivativeOn
      (I := I) (M := M) G.maps3 realization.metric gdot s := by
  refine
    realization.coordinatePullbackMetricComponentDerivativeOn_of_variationalTangentMap_readout_lifted_eqOn_interior_cover_target_overlap_Ioo_geometricValue
      (M := M) (F := F) (I := I) hcover_int G hs hsIoo α hsModel ?_
      hvalue
  intro t ht x
  rcases Set.mem_iUnion.mp
      ((hsource_cover ht) (by trivial : x ∈ (Set.univ : Set M))) with
    ⟨i, hxi⟩
  obtain ⟨hxball, htarget_nhds, heq⟩ := hdata ht i x hxi
  refine ⟨(extChartAt I x) x, Metric.ball_subset_closedBall hxball, Fₗ i, ?_,
    hreadout ht i x hxi, ?_⟩
  · filter_upwards [hflow_deriv ht hxball] with τ hτ
    exact hτ.hasFDerivWithinAt
  · have htarget : ∀ᶠ τ in 𝓝 t,
        ∃ V : Set M, V ∈ 𝓝 x ∧
          ∀ z ∈ V,
            α.flow ((extChartAt I x) z, τ) ∈
              (extChartAt I ((G.maps3 t) x)).target := by
      have hcont : ContinuousAt α.flow (((extChartAt I x) x), t) := by
        simpa using
          (α.toContinuousLocalFlowSolution.flow_continuousAt_spaceTime_of_mem_ball_Ioo
            (x := (extChartAt I x) x) (t := t) hxball (hsModel ht))
      have hpair :
          ContinuousAt
            (fun p : M × ℝ ↦ ((extChartAt I x) p.1, p.2)) (x, t) := by
        simpa using
          (continuousAt_extChartAt (I := I) x).prodMap' continuousAt_id
      have hcomp :
          ContinuousAt
            (fun p : M × ℝ ↦ α.flow ((extChartAt I x) p.1, p.2)) (x, t) := by
        simpa [Function.comp_def] using
          ContinuousAt.comp (x := (x, t)) hcont hpair
      have hpre :
          (fun p : M × ℝ ↦ α.flow ((extChartAt I x) p.1, p.2)) ⁻¹'
              (extChartAt I ((G.maps3 t) x)).target ∈ 𝓝 (x, t) :=
        hcomp htarget_nhds
      rcases mem_nhds_prod_iff.mp hpre with ⟨V, hV, T, hT, hsub⟩
      filter_upwards [hT] with τ hτ
      refine ⟨V, hV, ?_⟩
      intro z hz
      exact hsub (Set.mk_mem_prod hz hτ)
    exact
      SmoothSelfDiffeomorph3Family.eventually_readout_lifted_eqOn_of_eventually_target_and_eqOn
        (I := I) (M := M) G.maps3 t x (Fₗ i)
        (fun τ y ↦ α.flow (y, τ)) htarget heq

/-- Readout-local lifted variational model-flow data gives tensor
time-regularity for the non-identity raw gauge pullback.

This is the tensor-level companion of
`coordinatePullbackMetricComponentDerivativeOn_of_variationalTangentMap_readout_lifted_eqOn_interior_cover_target_overlap_Ioo_geometricValue`:
the selected local readout and lifted model equality produce the component
package, and the raw gauge-flow coordinate/geometric equality promotes it to
`HasTimeDerivativeOn`. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.hasTimeDerivativeOn_of_variationalTangentMap_readout_lifted_eqOn_interior_cover_target_overlap_Ioo_geometricValue
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (hcover_int : (⋃ i, interior (Kc i : Set M)) = Set.univ)
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (hs : ∀ ⦃t : ℝ⦄, t ∈ s → s ∈ 𝓝 t)
    (hsIoo : s ⊆ Ioo ivp.initialTime sol.terminalTime)
    {tmin tmax : ℝ} {τ₀ : Icc tmin tmax}
    {f : ℝ → F → F} {Df : ℝ → F → F →L[ℝ] F}
    {x₀ : F} {r : ℝ≥0}
    (α : ModelGaugeFlowODE.VariationalLocalFlowSolution f Df τ₀ x₀ r)
    (hsModel : s ⊆ Ioo tmin tmax)
    {gdot : MetricTensorFamily (I := I) (M := M)}
    (hA_readout : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∃ xE : F, xE ∈ Metric.closedBall x₀ r ∧
        ∃ Fₗ : ℝ → M → M,
          (∀ᶠ τ in 𝓝 t,
            HasFDerivWithinAt (fun y : F ↦ α.flow (y, τ))
              (α.tangent xE τ) (Set.range I) ((extChartAt I x) x)) ∧
          (∀ᶠ τ in 𝓝 t,
            ∃ U : Set M, U ∈ 𝓝 x ∧
              EqOn (fun z : M ↦ (G.maps3 τ) z) (Fₗ τ) U) ∧
          (∀ᶠ τ in 𝓝 t,
            ∃ V : Set M, V ∈ 𝓝 x ∧
              (∀ z ∈ V,
                α.flow ((extChartAt I x) z, τ) ∈
                  (extChartAt I ((G.maps3 t) x)).target) ∧
              EqOn (Fₗ τ)
                (fun z : M ↦ (extChartAt I ((G.maps3 t) x)).symm
                  (α.flow ((extChartAt I x) z, τ))) V))
    (hvalue : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ u v : TangentSpace I x,
      ∀ (i : κ) (K : TopologicalSpace.Compacts M)
        (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
        (hK_sub_target : (K : Set M) ⊆
          (trivializationAt BilF
            (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            ((G.maps3 t) x)).baseSet)
        (hKmem_int : (G.maps3 t) x ∈ interior (K : Set M)),
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        (let B' : F →L[ℝ] F →L[ℝ] ℝ :=
          (targetBilinearCoordReadoutContinuousLinearMap
            (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
            (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
            ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target
            (A t (sol.curve t))
            (⟨(G.maps3 t) x, interior_subset hKmem_int⟩ : K)) +
          (fderivWithin ℝ
            (fun yE : F ↦
              SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
                (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
            (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
            (X t ((G.maps3 t) x));
        B'
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
            ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x u))
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
            ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x v)) +
          (realization.metric t).inner ((G.maps3 t) x)
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I)
              ((G.maps3 t) x)
              ((Df t (α.flow (xE, t)))
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
                  ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x u))))
            ((G.maps3 t).pushforwardTangent x v) +
          (realization.metric t).inner ((G.maps3 t) x)
            ((G.maps3 t).pushforwardTangent x u)
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I)
              ((G.maps3 t) x)
              ((Df t (α.flow (xE, t)))
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
                  ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x v)))) =
        gdot t x u v)) :
    HasTimeDerivativeOn (I := I) (M := M)
      (G.maps3.pullbackMetricFamily realization.metric) gdot s := by
  refine
    SmoothSelfDiffeomorph3Family.hasTimeDerivativeOn_of_coordinatePullbackMetricComponentDerivatives
      (I := I) (M := M)
      (realization.coordinatePullbackMetricComponentDerivativeOn_of_variationalTangentMap_readout_lifted_eqOn_interior_cover_target_overlap_Ioo_geometricValue
        (M := M) (F := F) (I := I) hcover_int G hs hsIoo α hsModel
        hA_readout hvalue) ?_
  intro t ht x u v
  exact G.eventuallyEq_geometric_pullbackMetricInnerCoordinateModel
    (I := I) (M := M) (t := t) (hs (t := t) ht) realization.metric x u v

/-- Tensor time-regularity companion of the indexed-source-cover
readout-lifted variational component route. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.hasTimeDerivativeOn_of_variationalTangentMap_readout_mem_ball_iUnion_source_hasFDerivAt_lifted_eqOn_interior_cover_target_overlap_Ioo_geometricValue
    {ι : Type*}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (hcover_int : (⋃ i, interior (Kc i : Set M)) = Set.univ)
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (hs : ∀ ⦃t : ℝ⦄, t ∈ s → s ∈ 𝓝 t)
    (hsIoo : s ⊆ Ioo ivp.initialTime sol.terminalTime)
    {tmin tmax : ℝ} {τ₀ : Icc tmin tmax}
    {f : ℝ → F → F} {Df : ℝ → F → F →L[ℝ] F}
    {x₀ : F} {r : ℝ≥0}
    (α : ModelGaugeFlowODE.VariationalLocalFlowSolution f Df τ₀ x₀ r)
    (hsModel : s ⊆ Ioo tmin tmax)
    {gdot : MetricTensorFamily (I := I) (M := M)}
    (Fₗ : ι → ℝ → M → M)
    (U : ℝ → ι → Set M)
    (hsource_cover : ∀ ⦃t : ℝ⦄, t ∈ s → Set.univ ⊆ ⋃ i, U t i)
    (hreadout : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ i, ∀ x : M, x ∈ U t i →
        ∀ᶠ τ in 𝓝 t,
          ∃ W : Set M, W ∈ 𝓝 x ∧
            EqOn (fun z : M ↦ (G.maps3 τ) z) (Fₗ i τ) W)
    (hflow_deriv : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ ⦃xE : F⦄, xE ∈ Metric.ball x₀ r →
        ∀ᶠ τ in 𝓝 t,
          HasFDerivAt (fun y : F ↦ α.flow (y, τ))
            (α.tangent xE τ) xE)
    (hdata : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ i, ∀ x : M, x ∈ U t i →
        (extChartAt I x) x ∈ Metric.ball x₀ r ∧
        (extChartAt I ((G.maps3 t) x)).target ∈
          𝓝 (α.flow (((extChartAt I x) x), t)) ∧
        ∀ᶠ τ in 𝓝 t,
          ∃ W : Set M, W ∈ 𝓝 x ∧
            EqOn (Fₗ i τ)
              (fun z : M ↦ (extChartAt I ((G.maps3 t) x)).symm
                (α.flow ((extChartAt I x) z, τ))) W)
    (hvalue : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ u v : TangentSpace I x,
      ∀ (i : κ) (K : TopologicalSpace.Compacts M)
        (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
        (hK_sub_target : (K : Set M) ⊆
          (trivializationAt BilF
            (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            ((G.maps3 t) x)).baseSet)
        (hKmem_int : (G.maps3 t) x ∈ interior (K : Set M)),
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        (let B' : F →L[ℝ] F →L[ℝ] ℝ :=
          (targetBilinearCoordReadoutContinuousLinearMap
            (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
            (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
            ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target
            (A t (sol.curve t))
            (⟨(G.maps3 t) x, interior_subset hKmem_int⟩ : K)) +
          (fderivWithin ℝ
            (fun yE : F ↦
              SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
                (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
            (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
            (X t ((G.maps3 t) x));
        B'
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
            ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x u))
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
            ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x v)) +
          (realization.metric t).inner ((G.maps3 t) x)
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I)
              ((G.maps3 t) x)
              ((Df t (α.flow (xE, t)))
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
                  ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x u))))
            ((G.maps3 t).pushforwardTangent x v) +
          (realization.metric t).inner ((G.maps3 t) x)
            ((G.maps3 t).pushforwardTangent x u)
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I)
              ((G.maps3 t) x)
              ((Df t (α.flow (xE, t)))
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
                  ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x v)))) =
        gdot t x u v)) :
    HasTimeDerivativeOn (I := I) (M := M)
      (G.maps3.pullbackMetricFamily realization.metric) gdot s := by
  refine
    SmoothSelfDiffeomorph3Family.hasTimeDerivativeOn_of_coordinatePullbackMetricComponentDerivatives
      (I := I) (M := M)
      (realization.coordinatePullbackMetricComponentDerivativeOn_of_variationalTangentMap_readout_mem_ball_iUnion_source_hasFDerivAt_lifted_eqOn_interior_cover_target_overlap_Ioo_geometricValue
        (M := M) (F := F) (I := I) hcover_int G hs hsIoo α hsModel Fₗ U
        hsource_cover hreadout hflow_deriv hdata hvalue) ?_
  intro t ht x u v
  exact G.eventuallyEq_geometric_pullbackMetricInnerCoordinateModel
    (I := I) (M := M) (t := t) (hs (t := t) ht) realization.metric x u v

/-- Closed-interval source-cover companion of
`hasTimeDerivativeOn_of_variationalTangentMap_readout_mem_ball_iUnion_source_hasFDerivAt_lifted_eqOn_interior_cover_target_overlap_Ioo_geometricValue`.

Compact selected gauge-flow witnesses keep the chosen finite source cover on
the closed Picard interval.  This wrapper restricts that cover to the open
active time set before invoking the smooth-realization readout route. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.hasTimeDerivativeOn_of_variationalTangentMap_readout_mem_ball_iUnion_Icc_cover_source_hasFDerivAt_lifted_eqOn_interior_cover_target_overlap_Ioo_geometricValue
    {ι : Type*}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (hcover_int : (⋃ i, interior (Kc i : Set M)) = Set.univ)
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (hs : ∀ ⦃t : ℝ⦄, t ∈ s → s ∈ 𝓝 t)
    (hsIoo : s ⊆ Ioo ivp.initialTime sol.terminalTime)
    {tmin tmax : ℝ} {τ₀ : Icc tmin tmax}
    {f : ℝ → F → F} {Df : ℝ → F → F →L[ℝ] F}
    {x₀ : F} {r : ℝ≥0}
    (α : ModelGaugeFlowODE.VariationalLocalFlowSolution f Df τ₀ x₀ r)
    (hsModel : s ⊆ Ioo tmin tmax)
    {gdot : MetricTensorFamily (I := I) (M := M)}
    (Fₗ : ι → ℝ → M → M)
    (U : ℝ → ι → Set M)
    (hsource_cover : ∀ ⦃t : ℝ⦄, t ∈ Icc tmin tmax → Set.univ ⊆ ⋃ i, U t i)
    (hreadout : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ i, ∀ x : M, x ∈ U t i →
        ∀ᶠ τ in 𝓝 t,
          ∃ W : Set M, W ∈ 𝓝 x ∧
            EqOn (fun z : M ↦ (G.maps3 τ) z) (Fₗ i τ) W)
    (hflow_deriv : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ ⦃xE : F⦄, xE ∈ Metric.ball x₀ r →
        ∀ᶠ τ in 𝓝 t,
          HasFDerivAt (fun y : F ↦ α.flow (y, τ))
            (α.tangent xE τ) xE)
    (hdata : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ i, ∀ x : M, x ∈ U t i →
        (extChartAt I x) x ∈ Metric.ball x₀ r ∧
        (extChartAt I ((G.maps3 t) x)).target ∈
          𝓝 (α.flow (((extChartAt I x) x), t)) ∧
        ∀ᶠ τ in 𝓝 t,
          ∃ W : Set M, W ∈ 𝓝 x ∧
            EqOn (Fₗ i τ)
              (fun z : M ↦ (extChartAt I ((G.maps3 t) x)).symm
                (α.flow ((extChartAt I x) z, τ))) W)
    (hvalue : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ u v : TangentSpace I x,
      ∀ (i : κ) (K : TopologicalSpace.Compacts M)
        (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
        (hK_sub_target : (K : Set M) ⊆
          (trivializationAt BilF
            (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            ((G.maps3 t) x)).baseSet)
        (hKmem_int : (G.maps3 t) x ∈ interior (K : Set M)),
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        (let B' : F →L[ℝ] F →L[ℝ] ℝ :=
          (targetBilinearCoordReadoutContinuousLinearMap
            (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
            (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
            ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target
            (A t (sol.curve t))
            (⟨(G.maps3 t) x, interior_subset hKmem_int⟩ : K)) +
          (fderivWithin ℝ
            (fun yE : F ↦
              SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
                (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
            (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
            (X t ((G.maps3 t) x));
        B'
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
            ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x u))
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
            ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x v)) +
          (realization.metric t).inner ((G.maps3 t) x)
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I)
              ((G.maps3 t) x)
              ((Df t (α.flow (xE, t)))
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
                  ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x u))))
            ((G.maps3 t).pushforwardTangent x v) +
          (realization.metric t).inner ((G.maps3 t) x)
            ((G.maps3 t).pushforwardTangent x u)
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I)
              ((G.maps3 t) x)
              ((Df t (α.flow (xE, t)))
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
                  ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x v)))) =
        gdot t x u v)) :
    HasTimeDerivativeOn (I := I) (M := M)
      (G.maps3.pullbackMetricFamily realization.metric) gdot s :=
  realization.hasTimeDerivativeOn_of_variationalTangentMap_readout_mem_ball_iUnion_source_hasFDerivAt_lifted_eqOn_interior_cover_target_overlap_Ioo_geometricValue
    (M := M) (F := F) (I := I) hcover_int G hs hsIoo α hsModel Fₗ U
    (fun {t} ht ↦ hsource_cover (t := t) (Ioo_subset_Icc_self (hsModel ht)))
    hreadout hflow_deriv hdata hvalue

/-- Closed-interval finite-cover smooth-realization route with the
state-preserving closed-ball Picard estimates supplying the model-flow
source-coordinate derivative. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.hasTimeDerivativeOn_ofProductStatePreservingComponentClosedBallContinuityEstimates_restrict_readout_mem_ball_iUnion_Icc_cover_lifted_eqOn_interior_cover_target_overlap_Ioo_geometricValue
    {ι : Type*}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (hcover_int : (⋃ i, interior (Kc i : Set M)) = Set.univ)
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (hs : ∀ ⦃t : ℝ⦄, t ∈ s → s ∈ 𝓝 t)
    (hsIoo : s ⊆ Ioo ivp.initialTime sol.terminalTime)
    {tmin tmax : ℝ} {tmin0 tmax0 : ℝ} {tbase : Icc tmin0 tmax0}
    {f : ℝ → F → F} {Df : ℝ → F → F →L[ℝ] F}
    {x₀ : F} {a R Kf KD Lf BA BD r : ℝ≥0}
    (hf_lip : ∀ t ∈ Icc tmin0 tmax0,
      LipschitzOnWith Kf (f t) (Metric.closedBall x₀ a))
    (hDf_lip : ∀ t ∈ Icc tmin0 tmax0,
      LipschitzOnWith KD (Df t) (Metric.closedBall x₀ a))
    (hf_bound : ∀ t ∈ Icc tmin0 tmax0, ∀ y ∈ Metric.closedBall x₀ a,
      ‖f t y‖ ≤ Lf)
    (hA_bound : ∀ A ∈ Metric.closedBall (1 : F →L[ℝ] F) a, ‖A‖₊ ≤ BA)
    (hD_bound : ∀ t ∈ Icc tmin0 tmax0, ∀ y ∈ Metric.closedBall x₀ a,
      ‖Df t y‖₊ ≤ BD)
    (hf_cont : ∀ y ∈ Metric.closedBall x₀ a,
      ContinuousOn (fun t : ℝ => f t y) (Icc tmin0 tmax0))
    (hDf_cont : ∀ y ∈ Metric.closedBall x₀ a,
      ContinuousOn (fun t : ℝ => Df t y) (Icc tmin0 tmax0))
    (hmul : (max Lf (BD * BA)) * max (tmax0 - tbase) (tbase - tmin0) ≤ a - R)
    (htime : Icc tmin tmax ⊆ Icc tmin0 tmax0)
    (htbase : (tbase : ℝ) ∈ Icc tmin tmax)
    (hr : r ≤ R)
    (hder : ∀ τ ∈ Icc tmin0 tmax0, ∀ z ∈ Metric.closedBall x₀ a,
      HasFDerivWithinAt (f τ) (Df τ z) (Metric.closedBall x₀ a) z)
    (α : ModelGaugeFlowODE.VariationalLocalFlowSolution f Df
      (⟨(tbase : ℝ), htbase⟩ : Icc tmin tmax) x₀ r)
    (hα : α =
      ModelGaugeFlowODE.VariationalLocalFlowSolution.ofProductStatePreservingComponentClosedBallContinuityEstimates_restrict
        (t₀ := tbase) hf_lip hDf_lip hf_bound hA_bound hD_bound
        hf_cont hDf_cont hmul htime htbase hr)
    (hsModel : s ⊆ Ioo tmin tmax)
    {gdot : MetricTensorFamily (I := I) (M := M)}
    (Fₗ : ι → ℝ → M → M)
    (U : ℝ → ι → Set M)
    (hsource_cover : ∀ ⦃t : ℝ⦄, t ∈ Icc tmin tmax → Set.univ ⊆ ⋃ i, U t i)
    (hreadout : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ i, ∀ x : M, x ∈ U t i →
        ∀ᶠ τ in 𝓝 t,
          ∃ W : Set M, W ∈ 𝓝 x ∧
            EqOn (fun z : M ↦ (G.maps3 τ) z) (Fₗ i τ) W)
    (hdata : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ i, ∀ x : M, x ∈ U t i →
        (extChartAt I x) x ∈ Metric.ball x₀ r ∧
        (extChartAt I ((G.maps3 t) x)).target ∈
          𝓝 (α.flow (((extChartAt I x) x), t)) ∧
        ∀ᶠ τ in 𝓝 t,
          ∃ W : Set M, W ∈ 𝓝 x ∧
            EqOn (Fₗ i τ)
              (fun z : M ↦ (extChartAt I ((G.maps3 t) x)).symm
                (α.flow ((extChartAt I x) z, τ))) W)
    (hvalue : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ u v : TangentSpace I x,
      ∀ (i : κ) (K : TopologicalSpace.Compacts M)
        (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
        (hK_sub_target : (K : Set M) ⊆
          (trivializationAt BilF
            (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            ((G.maps3 t) x)).baseSet)
        (hKmem_int : (G.maps3 t) x ∈ interior (K : Set M)),
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        (let B' : F →L[ℝ] F →L[ℝ] ℝ :=
          (targetBilinearCoordReadoutContinuousLinearMap
            (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
            (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
            ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target
            (A t (sol.curve t))
            (⟨(G.maps3 t) x, interior_subset hKmem_int⟩ : K)) +
          (fderivWithin ℝ
            (fun yE : F ↦
              SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
                (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
            (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
            (X t ((G.maps3 t) x));
        B'
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
            ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x u))
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
            ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x v)) +
          (realization.metric t).inner ((G.maps3 t) x)
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I)
              ((G.maps3 t) x)
              ((Df t (α.flow (xE, t)))
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
                  ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x u))))
            ((G.maps3 t).pushforwardTangent x v) +
          (realization.metric t).inner ((G.maps3 t) x)
            ((G.maps3 t).pushforwardTangent x u)
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I)
              ((G.maps3 t) x)
              ((Df t (α.flow (xE, t)))
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
                  ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x v)))) =
        gdot t x u v)) :
    HasTimeDerivativeOn (I := I) (M := M)
      (G.maps3.pullbackMetricFamily realization.metric) gdot s := by
  have hflow_deriv : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ ⦃xE : F⦄, xE ∈ Metric.ball x₀ r →
        ∀ᶠ τ in 𝓝 t,
          HasFDerivAt (fun y : F ↦ α.flow (y, τ))
            (α.tangent xE τ) xE := by
    have hsource : ∀ ⦃t : ℝ⦄, t ∈ Ioo tmin tmax →
        ∀ ⦃xE : F⦄, xE ∈ Metric.ball x₀ r →
          ∀ᶠ τ in 𝓝 t,
            HasFDerivAt (fun y : F ↦ α.flow (y, τ))
              (α.tangent xE τ) xE := by
      simpa [hα] using
        (ModelGaugeFlowODE.VariationalLocalFlowSolution.ofProductStatePreservingComponentClosedBallContinuityEstimates_restrict_source_eventually_flow_timeSlice_hasFDerivAt_of_hasFDerivWithinAt_Ioo_of_le_radius
          (t₀ := tbase) hf_lip hDf_lip hf_bound hA_bound hD_bound
          hf_cont hDf_cont hmul htime htbase hr hder)
    intro t ht xE hxE
    exact hsource (hsModel ht) hxE
  exact
    realization.hasTimeDerivativeOn_of_variationalTangentMap_readout_mem_ball_iUnion_Icc_cover_source_hasFDerivAt_lifted_eqOn_interior_cover_target_overlap_Ioo_geometricValue
      (M := M) (F := F) (I := I) hcover_int G hs hsIoo α hsModel Fₗ U
      hsource_cover hreadout hflow_deriv hdata hvalue

/-- Convert a chart-RHS identification with the intrinsic Ricci-DeTurck RHS into
the metric-velocity equality needed by the scalar gauge adapter. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricVelocity_eq_chartRHS_of_chartRHS_eq_intrinsic
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchartRHS_eq_intrinsic : ∀ ⦃t : ℝ⦄,
      t ∈ Icc ivp.initialTime sol.terminalTime → ∀ x : M,
        ∀ u v : TangentSpace I x,
          A t (sol.curve t) x u v =
            intrinsicRicciDeTurckRHS (I := I) (M := M)
              realization.metric realization.background t x u v) :
    ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime → ∀ x : M,
      ∀ u v : TangentSpace I x,
        realization.metricVelocity t x u v = A t (sol.curve t) x u v := by
  intro t ht x u v
  exact (realization.equation ht x u v).trans
    (hchartRHS_eq_intrinsic ht x u v).symm

/-- Pointwise scalar-value adapter for the readout/variational tangent-map
route.

The large non-identity gauge route asks for a scalar `hvalue` in local
coordinates.  This lemma reduces that obligation to two geometric identities:
the Banach chart RHS is the intrinsic Ricci-DeTurck RHS of the smooth
realization, and the spatial plus tangent-map coordinate terms equal the
negative DeTurck correction at the gauge image. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_correction
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    {tmin tmax : ℝ} {τ₀ : Icc tmin tmax}
    {f : ℝ → F → F} {Df : ℝ → F → F →L[ℝ] F}
    {x₀ : F} {r : ℝ≥0}
    (α : ModelGaugeFlowODE.VariationalLocalFlowSolution f Df τ₀ x₀ r)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      realization.metric realization.background (Icc ivp.initialTime sol.terminalTime)
      ivp.initialTime)
    (hgauge_maps : gauge3.maps = G.maps3)
    (hsIcc : s ⊆ Icc ivp.initialTime sol.terminalTime)
    (hchartRHS_eq_intrinsic : ∀ ⦃t : ℝ⦄,
      t ∈ Icc ivp.initialTime sol.terminalTime → ∀ x : M,
        ∀ u v : TangentSpace I x,
          A t (sol.curve t) x u v =
            intrinsicRicciDeTurckRHS (I := I) (M := M)
              realization.metric realization.background t x u v)
    (hcorrection : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ u v : TangentSpace I x,
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        (let p : M := (G.maps3 t) x
         let pu : TangentSpace I p := (G.maps3 t).pushforwardTangent x u
         let pv : TangentSpace I p := (G.maps3 t).pushforwardTangent x v
         let cu : F :=
          SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p pu
         let cv : F :=
          SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p pv
         (fderivWithin ℝ
            (fun yE : F ↦
              SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
                (I := I) (M := M) realization.metric p (t, yE))
            (Set.range I) ((extChartAt I p) p))
            (X t p) cu cv +
          (realization.metric t).inner p
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p
              ((Df t (α.flow (xE, t))) cu)) pv +
          (realization.metric t).inner p pu
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p
              ((Df t (α.flow (xE, t))) cv)) =
          -intrinsicDeTurckCorrection (I := I) (M := M)
            realization.metric realization.background t p pu pv)) :
    ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ u v : TangentSpace I x,
      ∀ (i : κ) (K : TopologicalSpace.Compacts M)
        (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
        (hK_sub_target : (K : Set M) ⊆
          (trivializationAt BilF
            (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            ((G.maps3 t) x)).baseSet)
        (hKmem_int : (G.maps3 t) x ∈ interior (K : Set M)),
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        (let B' : F →L[ℝ] F →L[ℝ] ℝ :=
          (targetBilinearCoordReadoutContinuousLinearMap
            (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
            (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
            ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target
            (A t (sol.curve t))
            (⟨(G.maps3 t) x, interior_subset hKmem_int⟩ : K)) +
          (fderivWithin ℝ
            (fun yE : F ↦
              SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
                (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
            (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
            (X t ((G.maps3 t) x));
        B'
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
            ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x u))
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
            ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x v)) +
          (realization.metric t).inner ((G.maps3 t) x)
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I)
              ((G.maps3 t) x)
              ((Df t (α.flow (xE, t)))
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
                  ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x u))))
            ((G.maps3 t).pushforwardTangent x v) +
          (realization.metric t).inner ((G.maps3 t) x)
            ((G.maps3 t).pushforwardTangent x u)
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I)
              ((G.maps3 t) x)
              ((Df t (α.flow (xE, t)))
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
                  ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x v)))) =
        realization.toIntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
          gauge3 t x u v) := by
  intro t ht x u v i K hK_sub_Kc hK_sub_target hKmem_int xE hxE hAeq
  let source := realization.toIntrinsicDeTurckLocalSolution
  let p : M := (G.maps3 t) x
  let pu : TangentSpace I p := (G.maps3 t).pushforwardTangent x u
  let pv : TangentSpace I p := (G.maps3 t).pushforwardTangent x v
  let cu : F := SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p pu
  let cv : F := SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p pv
  let Btime : F →L[ℝ] F →L[ℝ] ℝ :=
    targetBilinearCoordReadoutContinuousLinearMap
      (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
      p i K hK_sub_Kc hK_sub_target (A t (sol.curve t))
      (⟨p, interior_subset hKmem_int⟩ : K)
  let Bspace : F →L[ℝ] F →L[ℝ] ℝ :=
    (fderivWithin ℝ
      (fun yE : F ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric p (t, yE))
      (Set.range I) ((extChartAt I p) p)) (X t p)
  let left : ℝ :=
    (realization.metric t).inner p
      (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p
        ((Df t (α.flow (xE, t))) cu)) pv
  let right : ℝ :=
    (realization.metric t).inner p pu
      (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p
        ((Df t (α.flow (xE, t))) cv))
  let correction : ℝ :=
    intrinsicDeTurckCorrection (I := I) (M := M)
      realization.metric realization.background t p pu pv
  have hvelocity_eq_chartRHS :
      ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime → ∀ x : M,
        ∀ u v : TangentSpace I x,
          realization.metricVelocity t x u v = A t (sol.curve t) x u v :=
    realization.metricVelocity_eq_chartRHS_of_chartRHS_eq_intrinsic hchartRHS_eq_intrinsic
  have htarget : Btime cu cv = realization.metricVelocity t p pu pv := by
    calc
      Btime cu cv =
          A t (sol.curve t) p
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p cu)
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p cv) := by
        simpa [Btime, p, cu, cv] using
          targetBilinearCoordReadoutContinuousLinearMap_apply_self_eq
            (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
            (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
            p i K hK_sub_Kc hK_sub_target (interior_subset hKmem_int)
            (A t (sol.curve t)) cu cv
      _ = A t (sol.curve t) p pu pv := by
        simp [cu, cv]
      _ = realization.metricVelocity t p pu pv := by
        exact (hvelocity_eq_chartRHS (hsIcc ht) p pu pv).symm
  have hcorr : Bspace cu cv + left + right = -correction := by
    simpa [Bspace, left, right, correction, p, pu, pv, cu, cv] using
      hcorrection ht x u v xE hxE hAeq
  have hcorrected :
      source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3 t x u v =
        realization.metricVelocity t p pu pv - correction := by
    have hbase :
        source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3 t x u v =
          source.toIntrinsicDeTurckSolution.metricVelocity t ((gauge3.maps t) x)
              ((gauge3.maps t).pushforwardTangent x u)
              ((gauge3.maps t).pushforwardTangent x v) -
            intrinsicDeTurckCorrection (I := I) (M := M)
              source.toIntrinsicDeTurckSolution.metric
              source.toIntrinsicDeTurckSolution.background t
              ((gauge3.maps t) x)
              ((gauge3.maps t).pushforwardTangent x u)
              ((gauge3.maps t).pushforwardTangent x v) := by
      rw [IntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_apply]
      rw [source.pullbackSourceDeTurckCorrectionOfDiffeomorph3Gauge_eq_sourceDeTurckCorrection
        gauge3 t x u v]
    calc
      source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3 t x u v =
          source.toIntrinsicDeTurckSolution.metricVelocity t ((gauge3.maps t) x)
              ((gauge3.maps t).pushforwardTangent x u)
              ((gauge3.maps t).pushforwardTangent x v) -
            intrinsicDeTurckCorrection (I := I) (M := M)
              source.toIntrinsicDeTurckSolution.metric
              source.toIntrinsicDeTurckSolution.background t
              ((gauge3.maps t) x)
              ((gauge3.maps t).pushforwardTangent x u)
              ((gauge3.maps t).pushforwardTangent x v) := hbase
      _ = realization.metricVelocity t p pu pv - correction := by
        rw [hgauge_maps]
        simp [source, p, pu, pv, correction,
          BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution]
  change
    (let B' : F →L[ℝ] F →L[ℝ] ℝ := Btime + Bspace
     B' cu cv + left + right) =
      source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3 t x u v
  calc
    (let B' : F →L[ℝ] F →L[ℝ] ℝ := Btime + Bspace
     B' cu cv + left + right) =
        Btime cu cv + (Bspace cu cv + left + right) := by
      simp [Btime, Bspace]
      ring
    _ = realization.metricVelocity t p pu pv + (-correction) := by
      rw [htarget, hcorr]
    _ = realization.metricVelocity t p pu pv - correction := by
      ring
    _ = source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3 t x u v :=
      hcorrected.symm

/-- Pointwise scalar-value adapter whose spatial/tangent-map input is the
Lie-correction identity before applying the reverse DeTurck gauge sign.

This is the same endpoint as
`variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_correction`,
but callers only need to identify the coordinate chain-rule terms with the
Levi-Civita derivative of `intrinsicDeTurckGaugeField`; the sign/algebra
conversion to `-intrinsicDeTurckCorrection` is supplied by the raw gauge-flow
bridge. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_lieCorrection
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    {tmin tmax : ℝ} {τ₀ : Icc tmin tmax}
    {f : ℝ → F → F} {Df : ℝ → F → F →L[ℝ] F}
    {x₀ : F} {r : ℝ≥0}
    (α : ModelGaugeFlowODE.VariationalLocalFlowSolution f Df τ₀ x₀ r)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      realization.metric realization.background (Icc ivp.initialTime sol.terminalTime)
      ivp.initialTime)
    (hgauge_maps : gauge3.maps = G.maps3)
    (hsIcc : s ⊆ Icc ivp.initialTime sol.terminalTime)
    (hchartRHS_eq_intrinsic : ∀ ⦃t : ℝ⦄,
      t ∈ Icc ivp.initialTime sol.terminalTime → ∀ x : M,
        ∀ u v : TangentSpace I x,
          A t (sol.curve t) x u v =
            intrinsicRicciDeTurckRHS (I := I) (M := M)
              realization.metric realization.background t x u v)
    (hDeTurckVector_mdiff : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ p : M,
      MDiffAt (T%
        (intrinsicDeTurckVectorField (I := I) (M := M)
          realization.metric realization.background t)) p)
    (hlieCorrection : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ u v : TangentSpace I x,
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        (let p : M := (G.maps3 t) x
         let pu : TangentSpace I p := (G.maps3 t).pushforwardTangent x u
         let pv : TangentSpace I p := (G.maps3 t).pushforwardTangent x v
         let cu : F :=
          SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p pu
         let cv : F :=
          SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p pv
         (fderivWithin ℝ
            (fun yE : F ↦
              SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
                (I := I) (M := M) realization.metric p (t, yE))
            (Set.range I) ((extChartAt I p) p))
            (X t p) cu cv +
          (realization.metric t).inner p
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p
              ((Df t (α.flow (xE, t))) cu)) pv +
          (realization.metric t).inner p pu
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p
              ((Df t (α.flow (xE, t))) cv)) =
          (realization.metric t).inner p
            (((chosenLeviCivitaFamily (I := I) (M := M) realization.metric) t)
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                realization.metric realization.background t) p pu) pv +
          (realization.metric t).inner p pu
            (((chosenLeviCivitaFamily (I := I) (M := M) realization.metric) t)
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                realization.metric realization.background t) p pv))) :
    ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ u v : TangentSpace I x,
      ∀ (i : κ) (K : TopologicalSpace.Compacts M)
        (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
        (hK_sub_target : (K : Set M) ⊆
          (trivializationAt BilF
            (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            ((G.maps3 t) x)).baseSet)
        (hKmem_int : (G.maps3 t) x ∈ interior (K : Set M)),
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        (let B' : F →L[ℝ] F →L[ℝ] ℝ :=
          (targetBilinearCoordReadoutContinuousLinearMap
            (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
            (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
            ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target
            (A t (sol.curve t))
            (⟨(G.maps3 t) x, interior_subset hKmem_int⟩ : K)) +
          (fderivWithin ℝ
            (fun yE : F ↦
              SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
                (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
            (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
            (X t ((G.maps3 t) x));
        B'
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
            ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x u))
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
            ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x v)) +
          (realization.metric t).inner ((G.maps3 t) x)
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I)
              ((G.maps3 t) x)
              ((Df t (α.flow (xE, t)))
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
                  ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x u))))
            ((G.maps3 t).pushforwardTangent x v) +
          (realization.metric t).inner ((G.maps3 t) x)
            ((G.maps3 t).pushforwardTangent x u)
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I)
              ((G.maps3 t) x)
              ((Df t (α.flow (xE, t)))
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
                  ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x v)))) =
        realization.toIntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
          gauge3 t x u v) := by
  have hcorrection :
      ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
        ∀ u v : TangentSpace I x,
        ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
          (fun τ : ℝ ↦
            SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
              (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
            (fun τ : ℝ ↦ α.tangent xE τ) →
          (let p : M := (G.maps3 t) x
           let pu : TangentSpace I p := (G.maps3 t).pushforwardTangent x u
           let pv : TangentSpace I p := (G.maps3 t).pushforwardTangent x v
           let cu : F :=
            SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p pu
           let cv : F :=
            SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p pv
           (fderivWithin ℝ
              (fun yE : F ↦
                SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
                  (I := I) (M := M) realization.metric p (t, yE))
              (Set.range I) ((extChartAt I p) p))
              (X t p) cu cv +
            (realization.metric t).inner p
              (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p
                ((Df t (α.flow (xE, t))) cu)) pv +
            (realization.metric t).inner p pu
              (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p
                ((Df t (α.flow (xE, t))) cv)) =
            -intrinsicDeTurckCorrection (I := I) (M := M)
              realization.metric realization.background t p pu pv) :=
    G.spatial_tangent_correction_eq_neg_intrinsicDeTurckCorrection_of_lieCorrection
      (I := I) (M := M)
      realization.metric realization.background α hDeTurckVector_mdiff hlieCorrection
  exact
    realization.variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_correction
      G α gauge3 hgauge_maps hsIcc hchartRHS_eq_intrinsic hcorrection

/-- Pointwise scalar-value adapter from a model-slot variational linearization
identity.

This is the same scalar `hvalue` endpoint as
`variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_correction`, but
the spatial/tangent correction is supplied by the raw model-slot signed
correction theorem and is only specialized to source coordinates at the final
handoff. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_modelSlotCorrection
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    {tmin tmax : ℝ} {τ₀ : Icc tmin tmax}
    {f : ℝ → F → F} {Df : ℝ → F → F →L[ℝ] F}
    {x₀ : F} {r : ℝ≥0}
    (α : ModelGaugeFlowODE.VariationalLocalFlowSolution f Df τ₀ x₀ r)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      realization.metric realization.background (Icc ivp.initialTime sol.terminalTime)
      ivp.initialTime)
    (hgauge_maps : gauge3.maps = G.maps3)
    (hsIcc : s ⊆ Icc ivp.initialTime sol.terminalTime)
    (hchartRHS_eq_intrinsic : ∀ ⦃t : ℝ⦄,
      t ∈ Icc ivp.initialTime sol.terminalTime → ∀ x : M,
        ∀ u v : TangentSpace I x,
          A t (sol.curve t) x u v =
            intrinsicRicciDeTurckRHS (I := I) (M := M)
              realization.metric realization.background t x u v)
    (hDeTurckVector_mdiff : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ p : M,
      MDiffAt (T%
        (intrinsicDeTurckVectorField (I := I) (M := M)
          realization.metric realization.background t)) p)
    (hDf : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ wE : F,
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        (let p : M := (G.maps3 t) x
         let pw : TangentSpace I p :=
          SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p wE
         SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p
              ((Df t (α.flow (xE, t))) wE) =
            (((chosenLeviCivitaFamily (I := I) (M := M) realization.metric) t)
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                realization.metric realization.background t) p pw) -
            (((chosenLeviCivitaFamily (I := I) (M := M) realization.metric) t)
              (FiberBundle.extend F pw) p (X t p)))) :
    ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ u v : TangentSpace I x,
      ∀ (i : κ) (K : TopologicalSpace.Compacts M)
        (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
        (hK_sub_target : (K : Set M) ⊆
          (trivializationAt BilF
            (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            ((G.maps3 t) x)).baseSet)
        (hKmem_int : (G.maps3 t) x ∈ interior (K : Set M)),
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        (let B' : F →L[ℝ] F →L[ℝ] ℝ :=
          (targetBilinearCoordReadoutContinuousLinearMap
            (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
            (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
            ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target
            (A t (sol.curve t))
            (⟨(G.maps3 t) x, interior_subset hKmem_int⟩ : K)) +
          (fderivWithin ℝ
            (fun yE : F ↦
              SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
                (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
            (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
            (X t ((G.maps3 t) x));
        B'
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
            ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x u))
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
            ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x v)) +
          (realization.metric t).inner ((G.maps3 t) x)
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I)
              ((G.maps3 t) x)
              ((Df t (α.flow (xE, t)))
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
                  ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x u))))
            ((G.maps3 t).pushforwardTangent x v) +
          (realization.metric t).inner ((G.maps3 t) x)
            ((G.maps3 t).pushforwardTangent x u)
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I)
              ((G.maps3 t) x)
              ((Df t (α.flow (xE, t)))
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
                  ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x v)))) =
        realization.toIntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
          gauge3 t x u v) := by
  have hcorrection :
      ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
        ∀ u v : TangentSpace I x,
        ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
          (fun τ : ℝ ↦
            SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
              (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
            (fun τ : ℝ ↦ α.tangent xE τ) →
          (let p : M := (G.maps3 t) x
           let pu : TangentSpace I p := (G.maps3 t).pushforwardTangent x u
           let pv : TangentSpace I p := (G.maps3 t).pushforwardTangent x v
           let cu : F :=
            SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p pu
           let cv : F :=
            SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p pv
           (fderivWithin ℝ
              (fun yE : F ↦
                SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
                  (I := I) (M := M) realization.metric p (t, yE))
              (Set.range I) ((extChartAt I p) p))
              (X t p) cu cv +
            (realization.metric t).inner p
              (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p
                ((Df t (α.flow (xE, t))) cu)) pv +
            (realization.metric t).inner p pu
              (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p
                ((Df t (α.flow (xE, t))) cv)) =
            -intrinsicDeTurckCorrection (I := I) (M := M)
              realization.metric realization.background t p pu pv) := by
    intro t ht x u v xE hxE hAeq
    let p : M := (G.maps3 t) x
    let pu : TangentSpace I p := (G.maps3 t).pushforwardTangent x u
    let pv : TangentSpace I p := (G.maps3 t).pushforwardTangent x v
    let cu : F := SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p pu
    let cv : F := SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p pv
    simpa [p, pu, pv, cu, cv] using
      G.spatial_tangent_correction_modelSlots_eq_neg_intrinsicDeTurckCorrection_of_tangentVectorOfCoordinate_Df_eq_cov_sub_extend
        realization.metric realization.background α hDeTurckVector_mdiff hDf
        ht x cu cv xE hxE hAeq
  exact
    realization.variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_correction
      G α gauge3 hgauge_maps hsIcc hchartRHS_eq_intrinsic hcorrection

/-- Pointwise scalar-value adapter from a signed model-slot correction.

This is the same scalar `hvalue` endpoint as
`variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_correction`, but
the signed spatial/tangent correction may be supplied in arbitrary centered
model slots and is specialized to source tangent coordinates only at this final
handoff. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_modelSlotSignedCorrection
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    {tmin tmax : ℝ} {τ₀ : Icc tmin tmax}
    {f : ℝ → F → F} {Df : ℝ → F → F →L[ℝ] F}
    {x₀ : F} {r : ℝ≥0}
    (α : ModelGaugeFlowODE.VariationalLocalFlowSolution f Df τ₀ x₀ r)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      realization.metric realization.background (Icc ivp.initialTime sol.terminalTime)
      ivp.initialTime)
    (hgauge_maps : gauge3.maps = G.maps3)
    (hsIcc : s ⊆ Icc ivp.initialTime sol.terminalTime)
    (hchartRHS_eq_intrinsic : ∀ ⦃t : ℝ⦄,
      t ∈ Icc ivp.initialTime sol.terminalTime → ∀ x : M,
        ∀ u v : TangentSpace I x,
          A t (sol.curve t) x u v =
            intrinsicRicciDeTurckRHS (I := I) (M := M)
              realization.metric realization.background t x u v)
    (hmodelCorrection : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ uE vE : F,
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        (let p : M := (G.maps3 t) x
         (fderivWithin ℝ
            (fun yE : F ↦
              SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
                (I := I) (M := M) realization.metric p (t, yE))
            (Set.range I) ((extChartAt I p) p))
            (X t p) uE vE +
          (realization.metric t).inner p
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p
              ((Df t (α.flow (xE, t))) uE))
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p vE) +
          (realization.metric t).inner p
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p uE)
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p
              ((Df t (α.flow (xE, t))) vE)) =
            -intrinsicDeTurckCorrection (I := I) (M := M)
            realization.metric realization.background t p
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p uE)
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p vE))) :
    ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ u v : TangentSpace I x,
      ∀ (i : κ) (K : TopologicalSpace.Compacts M)
        (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
        (hK_sub_target : (K : Set M) ⊆
          (trivializationAt BilF
            (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            ((G.maps3 t) x)).baseSet)
        (hKmem_int : (G.maps3 t) x ∈ interior (K : Set M)),
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        (let B' : F →L[ℝ] F →L[ℝ] ℝ :=
          (targetBilinearCoordReadoutContinuousLinearMap
            (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
            (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
            ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target
            (A t (sol.curve t))
            (⟨(G.maps3 t) x, interior_subset hKmem_int⟩ : K)) +
          (fderivWithin ℝ
            (fun yE : F ↦
              SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
                (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
            (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
            (X t ((G.maps3 t) x));
        B'
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
            ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x u))
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
            ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x v)) +
          (realization.metric t).inner ((G.maps3 t) x)
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I)
              ((G.maps3 t) x)
              ((Df t (α.flow (xE, t)))
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
                  ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x u))))
            ((G.maps3 t).pushforwardTangent x v) +
          (realization.metric t).inner ((G.maps3 t) x)
            ((G.maps3 t).pushforwardTangent x u)
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I)
              ((G.maps3 t) x)
              ((Df t (α.flow (xE, t)))
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
                  ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x v)))) =
        realization.toIntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
          gauge3 t x u v) := by
  have hcorrection :
      ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
        ∀ u v : TangentSpace I x,
        ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
          (fun τ : ℝ ↦
            SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
              (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
            (fun τ : ℝ ↦ α.tangent xE τ) →
          (let p : M := (G.maps3 t) x
           let pu : TangentSpace I p := (G.maps3 t).pushforwardTangent x u
           let pv : TangentSpace I p := (G.maps3 t).pushforwardTangent x v
           let cu : F :=
            SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p pu
           let cv : F :=
            SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p pv
           (fderivWithin ℝ
              (fun yE : F ↦
                SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
                  (I := I) (M := M) realization.metric p (t, yE))
              (Set.range I) ((extChartAt I p) p))
              (X t p) cu cv +
            (realization.metric t).inner p
              (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p
                ((Df t (α.flow (xE, t))) cu)) pv +
            (realization.metric t).inner p pu
              (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p
                ((Df t (α.flow (xE, t))) cv)) =
            -intrinsicDeTurckCorrection (I := I) (M := M)
              realization.metric realization.background t p pu pv) := by
    intro t ht x u v xE hxE hAeq
    let p : M := (G.maps3 t) x
    let pu : TangentSpace I p := (G.maps3 t).pushforwardTangent x u
    let pv : TangentSpace I p := (G.maps3 t).pushforwardTangent x v
    let cu : F := SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p pu
    let cv : F := SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p pv
    simpa [p, pu, pv, cu, cv] using hmodelCorrection ht x cu cv xE hxE hAeq
  exact
    realization.variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_correction
      G α gauge3 hgauge_maps hsIcc hchartRHS_eq_intrinsic hcorrection

/-- Closed-ball Picard derivative specialization of
`variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_correction`.

This keeps the scalar readout endpoint unchanged while deriving its signed
spatial/tangent correction directly from closed-ball model derivative data and
the local fixed-chart gauge-field identification. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_closedBall_model_hasFDerivWithinAt_of_eventuallyEqWithin
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    {tmin tmax : ℝ} {τ₀ : Icc tmin tmax}
    {f : ℝ → F → F} {Df : ℝ → F → F →L[ℝ] F}
    {x₀ : F} {r a : ℝ≥0}
    (α : ModelGaugeFlowODE.VariationalLocalFlowSolution f Df τ₀ x₀ r)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      realization.metric realization.background (Icc ivp.initialTime sol.terminalTime)
      ivp.initialTime)
    (hgauge_maps : gauge3.maps = G.maps3)
    (hsIcc : s ⊆ Icc ivp.initialTime sol.terminalTime)
    (hchartRHS_eq_intrinsic : ∀ ⦃t : ℝ⦄,
      t ∈ Icc ivp.initialTime sol.terminalTime → ∀ x : M,
        ∀ u v : TangentSpace I x,
          A t (sol.curve t) x u v =
            intrinsicRicciDeTurckRHS (I := I) (M := M)
              realization.metric realization.background t x u v)
    {tmin₁ tmax₁ : ℝ}
    (hDeTurckVector_mdiff : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ p : M,
      MDiffAt (T%
        (intrinsicDeTurckVectorField (I := I) (M := M)
          realization.metric realization.background t)) p)
    (hXeq : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      X t ((G.maps3 t) x) =
        intrinsicDeTurckGaugeField (I := I) (M := M)
          realization.metric realization.background t ((G.maps3 t) x))
    (htime : s ⊆ Icc tmin₁ tmax₁)
    (hbase : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ w : TangentSpace I x,
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)) =ᶠ[
          𝓝[s] t] (fun τ : ℝ ↦ α.flow (xE, τ)))
    (hball : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ w : TangentSpace I x,
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        α.flow (xE, t) ∈ Metric.ball x₀ a)
    (hder : ∀ τ ∈ Icc tmin₁ tmax₁, ∀ z ∈ Metric.closedBall x₀ a,
      HasFDerivWithinAt (f τ) (Df τ z) (Metric.closedBall x₀ a) z)
    (hfCoord : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ w : TangentSpace I x,
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        (f t) =ᶠ[𝓝[Set.range I] (α.flow (xE, t))]
          (fun y : F =>
            let p : M := (G.maps3 t) x
            let q : M := (extChartAt I p).symm y
            tangentCoordChange I q p q
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                realization.metric realization.background t q))) :
    ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ u v : TangentSpace I x,
      ∀ (i : κ) (K : TopologicalSpace.Compacts M)
        (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
        (hK_sub_target : (K : Set M) ⊆
          (trivializationAt BilF
            (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            ((G.maps3 t) x)).baseSet)
        (hKmem_int : (G.maps3 t) x ∈ interior (K : Set M)),
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        (let B' : F →L[ℝ] F →L[ℝ] ℝ :=
          (targetBilinearCoordReadoutContinuousLinearMap
            (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
            (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
            ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target
            (A t (sol.curve t))
            (⟨(G.maps3 t) x, interior_subset hKmem_int⟩ : K)) +
          (fderivWithin ℝ
            (fun yE : F ↦
              SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
                (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
            (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
            (X t ((G.maps3 t) x));
        B'
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
            ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x u))
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
            ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x v)) +
          (realization.metric t).inner ((G.maps3 t) x)
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I)
              ((G.maps3 t) x)
              ((Df t (α.flow (xE, t)))
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
                  ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x u))))
            ((G.maps3 t).pushforwardTangent x v) +
          (realization.metric t).inner ((G.maps3 t) x)
            ((G.maps3 t).pushforwardTangent x u)
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I)
              ((G.maps3 t) x)
              ((Df t (α.flow (xE, t)))
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
                  ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x v)))) =
        realization.toIntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
          gauge3 t x u v) := by
  exact
    realization.variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_modelSlotSignedCorrection
      G α gauge3 hgauge_maps hsIcc hchartRHS_eq_intrinsic
      (G.spatial_tangent_correction_modelSlots_eq_neg_intrinsicDeTurckCorrection_of_closedBall_model_hasFDerivWithinAt_of_eventuallyEqWithin
        (I := I) (M := M)
        realization.metric realization.background α hDeTurckVector_mdiff
        hXeq htime hbase hball hder hfCoord)

/-- Closed-ball Picard scalar route with the model vector field identified by
local `EqOn` data near the fixed chart center. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_closedBall_model_hasFDerivWithinAt_of_eventuallyEqWithin_of_eqOn_nhdsWithin
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    {tmin tmax : ℝ} {τ₀ : Icc tmin tmax}
    {f : ℝ → F → F} {Df : ℝ → F → F →L[ℝ] F}
    {x₀ : F} {r a : ℝ≥0}
    (α : ModelGaugeFlowODE.VariationalLocalFlowSolution f Df τ₀ x₀ r)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      realization.metric realization.background (Icc ivp.initialTime sol.terminalTime)
      ivp.initialTime)
    (hgauge_maps : gauge3.maps = G.maps3)
    (hsIcc : s ⊆ Icc ivp.initialTime sol.terminalTime)
    (hchartRHS_eq_intrinsic : ∀ ⦃t : ℝ⦄,
      t ∈ Icc ivp.initialTime sol.terminalTime → ∀ x : M,
        ∀ u v : TangentSpace I x,
          A t (sol.curve t) x u v =
            intrinsicRicciDeTurckRHS (I := I) (M := M)
              realization.metric realization.background t x u v)
    {tmin₁ tmax₁ : ℝ}
    (hDeTurckVector_mdiff : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ p : M,
      MDiffAt (T%
        (intrinsicDeTurckVectorField (I := I) (M := M)
          realization.metric realization.background t)) p)
    (hXeq : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      X t ((G.maps3 t) x) =
        intrinsicDeTurckGaugeField (I := I) (M := M)
          realization.metric realization.background t ((G.maps3 t) x))
    (htime : s ⊆ Icc tmin₁ tmax₁)
    (hbase : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ w : TangentSpace I x,
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)) =ᶠ[
          𝓝[s] t] (fun τ : ℝ ↦ α.flow (xE, τ)))
    (hball : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ w : TangentSpace I x,
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        α.flow (xE, t) ∈ Metric.ball x₀ a)
    (hder : ∀ τ ∈ Icc tmin₁ tmax₁, ∀ z ∈ Metric.closedBall x₀ a,
      HasFDerivWithinAt (f τ) (Df τ z) (Metric.closedBall x₀ a) z)
    (hfEqOn : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∃ U : Set F,
        U ∈ 𝓝[Set.range I]
          ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)) ∧
        Set.EqOn (f t)
          (fun y : F =>
            let p : M := (G.maps3 t) x
            let q : M := (extChartAt I p).symm y
            tangentCoordChange I q p q
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                realization.metric realization.background t q))
          U) :
    ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ u v : TangentSpace I x,
      ∀ (i : κ) (K : TopologicalSpace.Compacts M)
        (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
        (hK_sub_target : (K : Set M) ⊆
          (trivializationAt BilF
            (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            ((G.maps3 t) x)).baseSet)
        (hKmem_int : (G.maps3 t) x ∈ interior (K : Set M)),
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        (let B' : F →L[ℝ] F →L[ℝ] ℝ :=
          (targetBilinearCoordReadoutContinuousLinearMap
            (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
            (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
            ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target
            (A t (sol.curve t))
            (⟨(G.maps3 t) x, interior_subset hKmem_int⟩ : K)) +
          (fderivWithin ℝ
            (fun yE : F ↦
              SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
                (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
            (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
            (X t ((G.maps3 t) x));
        B'
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
            ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x u))
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
            ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x v)) +
          (realization.metric t).inner ((G.maps3 t) x)
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I)
              ((G.maps3 t) x)
              ((Df t (α.flow (xE, t)))
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
                  ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x u))))
            ((G.maps3 t).pushforwardTangent x v) +
          (realization.metric t).inner ((G.maps3 t) x)
            ((G.maps3 t).pushforwardTangent x u)
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I)
              ((G.maps3 t) x)
              ((Df t (α.flow (xE, t)))
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
                  ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x v)))) =
        realization.toIntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
          gauge3 t x u v) := by
  exact
    realization.variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_modelSlotSignedCorrection
      G α gauge3 hgauge_maps hsIcc hchartRHS_eq_intrinsic
      (G.spatial_tangent_correction_modelSlots_eq_neg_intrinsicDeTurckCorrection_of_closedBall_model_hasFDerivWithinAt_of_eventuallyEqWithin_of_eqOn_nhdsWithin
        (I := I) (M := M)
        realization.metric realization.background α hDeTurckVector_mdiff
        hXeq htime hbase hball hder hfEqOn)

/-- Closed-ball Picard scalar route with the Picard model vector field
identified locally with an auxiliary vector field, plus relative-filter
agreement of that auxiliary field with the intrinsic DeTurck gauge field along
the flow. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_closedBall_model_hasFDerivWithinAt_of_eventuallyEqWithin_of_eqOn_vectorField_of_eventuallyEq_along_maps3_nhdsWithin
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    {tmin tmax : ℝ} {τ₀ : Icc tmin tmax}
    {f : ℝ → F → F} {Df : ℝ → F → F →L[ℝ] F}
    {x₀ : F} {r a : ℝ≥0}
    (α : ModelGaugeFlowODE.VariationalLocalFlowSolution f Df τ₀ x₀ r)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      realization.metric realization.background (Icc ivp.initialTime sol.terminalTime)
      ivp.initialTime)
    (hgauge_maps : gauge3.maps = G.maps3)
    (hsIcc : s ⊆ Icc ivp.initialTime sol.terminalTime)
    (hchartRHS_eq_intrinsic : ∀ ⦃t : ℝ⦄,
      t ∈ Icc ivp.initialTime sol.terminalTime → ∀ x : M,
        ∀ u v : TangentSpace I x,
          A t (sol.curve t) x u v =
            intrinsicRicciDeTurckRHS (I := I) (M := M)
              realization.metric realization.background t x u v)
    {tmin₁ tmax₁ : ℝ}
    (hDeTurckVector_mdiff : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ p : M,
      MDiffAt (T%
        (intrinsicDeTurckVectorField (I := I) (M := M)
          realization.metric realization.background t)) p)
    (hXeq : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      X t ((G.maps3 t) x) =
        intrinsicDeTurckGaugeField (I := I) (M := M)
          realization.metric realization.background t ((G.maps3 t) x))
    (htime : s ⊆ Icc tmin₁ tmax₁)
    (hbase : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ w : TangentSpace I x,
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)) =ᶠ[
          𝓝[s] t] (fun τ : ℝ ↦ α.flow (xE, τ)))
    (hball : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ w : TangentSpace I x,
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        α.flow (xE, t) ∈ Metric.ball x₀ a)
    (hder : ∀ τ ∈ Icc tmin₁ tmax₁, ∀ z ∈ Metric.closedBall x₀ a,
      HasFDerivWithinAt (f τ) (Df τ z) (Metric.closedBall x₀ a) z)
    (hfY : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∃ U : Set F,
        U ∈ 𝓝[Set.range I]
          ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)) ∧
        Set.EqOn (f t)
          (fun y : F =>
            let p : M := (G.maps3 t) x
            let q : M := (extChartAt I p).symm y
            tangentCoordChange I q p q (Y t q))
          U)
    (hY : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ᶠ τ in 𝓝[s] t, ∀ x : M,
        Y τ ((G.maps3 τ) x) =
          intrinsicDeTurckGaugeField (I := I) (M := M)
            realization.metric realization.background τ ((G.maps3 τ) x)) :
    ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ u v : TangentSpace I x,
      ∀ (i : κ) (K : TopologicalSpace.Compacts M)
        (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
        (hK_sub_target : (K : Set M) ⊆
          (trivializationAt BilF
            (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            ((G.maps3 t) x)).baseSet)
        (hKmem_int : (G.maps3 t) x ∈ interior (K : Set M)),
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        (let B' : F →L[ℝ] F →L[ℝ] ℝ :=
          (targetBilinearCoordReadoutContinuousLinearMap
            (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
            (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
            ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target
            (A t (sol.curve t))
            (⟨(G.maps3 t) x, interior_subset hKmem_int⟩ : K)) +
          (fderivWithin ℝ
            (fun yE : F ↦
              SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
                (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
            (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
            (X t ((G.maps3 t) x));
        B'
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
            ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x u))
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
            ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x v)) +
          (realization.metric t).inner ((G.maps3 t) x)
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I)
              ((G.maps3 t) x)
              ((Df t (α.flow (xE, t)))
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
                  ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x u))))
            ((G.maps3 t).pushforwardTangent x v) +
          (realization.metric t).inner ((G.maps3 t) x)
            ((G.maps3 t).pushforwardTangent x u)
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I)
              ((G.maps3 t) x)
              ((Df t (α.flow (xE, t)))
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
                  ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x v)))) =
        realization.toIntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
          gauge3 t x u v) := by
  have hfEqOn : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∃ U : Set F,
        U ∈ 𝓝[Set.range I]
          ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)) ∧
        Set.EqOn (f t)
          (fun y : F =>
            let p : M := (G.maps3 t) x
            let q : M := (extChartAt I p).symm y
            tangentCoordChange I q p q
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                realization.metric realization.background t q))
          U :=
    G.model_vectorField_eqOn_tangentCoordChange_of_eqOn_vectorField_of_eventuallyEq_along_maps3_nhdsWithin
      (I := I) (M := M) realization.metric realization.background hfY hY
  exact
    realization.variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_closedBall_model_hasFDerivWithinAt_of_eventuallyEqWithin_of_eqOn_nhdsWithin
      G α gauge3 hgauge_maps hsIcc hchartRHS_eq_intrinsic hDeTurckVector_mdiff
      hXeq htime hbase hball hder hfEqOn

/-- Compact-witness form of
`variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_closedBall_model_hasFDerivWithinAt_of_eventuallyEqWithin_of_eqOn_vectorField_of_eventuallyEq_along_maps3_nhdsWithin`.

The retained source cover and selected local readout equality first transport
the patch-local Picard-model/auxiliary-field `EqOn` to the glued-flow chart
center.  The auxiliary-along-flow certificate then identifies the auxiliary
field with the intrinsic DeTurck gauge field before entering the existing
closed-ball scalar route. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_closedBall_model_hasFDerivWithinAt_of_eventuallyEqWithin_of_iUnion_readout_eqOn_of_eventuallyEq_along_maps3_nhdsWithin
    {ι : Type*}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    {tmin tmax : ℝ} {τ₀ : Icc tmin tmax}
    {f : ℝ → F → F} {Df : ℝ → F → F →L[ℝ] F}
    {x₀ : F} {r a : ℝ≥0}
    (α : ModelGaugeFlowODE.VariationalLocalFlowSolution f Df τ₀ x₀ r)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      realization.metric realization.background (Icc ivp.initialTime sol.terminalTime)
      ivp.initialTime)
    (hgauge_maps : gauge3.maps = G.maps3)
    (hsIcc : s ⊆ Icc ivp.initialTime sol.terminalTime)
    (hchartRHS_eq_intrinsic : ∀ ⦃t : ℝ⦄,
      t ∈ Icc ivp.initialTime sol.terminalTime → ∀ x : M,
        ∀ u v : TangentSpace I x,
          A t (sol.curve t) x u v =
            intrinsicRicciDeTurckRHS (I := I) (M := M)
              realization.metric realization.background t x u v)
    {tmin₁ tmax₁ : ℝ}
    (hDeTurckVector_mdiff : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ p : M,
      MDiffAt (T%
        (intrinsicDeTurckVectorField (I := I) (M := M)
          realization.metric realization.background t)) p)
    (hXeq : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      X t ((G.maps3 t) x) =
        intrinsicDeTurckGaugeField (I := I) (M := M)
          realization.metric realization.background t ((G.maps3 t) x))
    (htime : s ⊆ Icc tmin₁ tmax₁)
    (hbase : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ w : TangentSpace I x,
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)) =ᶠ[
          𝓝[s] t] (fun τ : ℝ ↦ α.flow (xE, τ)))
    (hball : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ w : TangentSpace I x,
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        α.flow (xE, t) ∈ Metric.ball x₀ a)
    (hder : ∀ τ ∈ Icc tmin₁ tmax₁, ∀ z ∈ Metric.closedBall x₀ a,
      HasFDerivWithinAt (f τ) (Df τ z) (Metric.closedBall x₀ a) z)
    (Fₗ : ι → ℝ → M → M) (U : ℝ → ι → Set M)
    (hsource_cover : ∀ ⦃t : ℝ⦄, t ∈ s → Set.univ ⊆ ⋃ i, U t i)
    (hreadout : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ i, ∀ x : M, x ∈ U t i →
      ∀ᶠ τ in 𝓝 t, ∃ W' : Set M, W' ∈ 𝓝 x ∧
        EqOn (fun z : M ↦ (G.maps3 τ) z) (Fₗ i τ) W')
    (hfLocal : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ i, ∀ x : M, x ∈ U t i →
      ∃ W : Set F,
        W ∈ 𝓝[Set.range I] ((extChartAt I (Fₗ i t x)) (Fₗ i t x)) ∧
        Set.EqOn (f t)
          (fun y : F =>
            let p : M := Fₗ i t x
            let q : M := (extChartAt I p).symm y
            tangentCoordChange I q p q (Y t q))
          W)
    (hY : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ᶠ τ in 𝓝[s] t, ∀ x : M,
        Y τ ((G.maps3 τ) x) =
          intrinsicDeTurckGaugeField (I := I) (M := M)
            realization.metric realization.background τ ((G.maps3 τ) x)) :
    ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ u v : TangentSpace I x,
      ∀ (i : κ) (K : TopologicalSpace.Compacts M)
        (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
        (hK_sub_target : (K : Set M) ⊆
          (trivializationAt BilF
            (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            ((G.maps3 t) x)).baseSet)
        (hKmem_int : (G.maps3 t) x ∈ interior (K : Set M)),
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        (let B' : F →L[ℝ] F →L[ℝ] ℝ :=
          (targetBilinearCoordReadoutContinuousLinearMap
            (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
            (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
            ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target
            (A t (sol.curve t))
            (⟨(G.maps3 t) x, interior_subset hKmem_int⟩ : K)) +
          (fderivWithin ℝ
            (fun yE : F ↦
              SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
                (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
            (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
            (X t ((G.maps3 t) x));
        B'
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
            ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x u))
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
            ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x v)) +
          (realization.metric t).inner ((G.maps3 t) x)
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I)
              ((G.maps3 t) x)
              ((Df t (α.flow (xE, t)))
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
                  ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x u))))
            ((G.maps3 t).pushforwardTangent x v) +
          (realization.metric t).inner ((G.maps3 t) x)
            ((G.maps3 t).pushforwardTangent x u)
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I)
              ((G.maps3 t) x)
              ((Df t (α.flow (xE, t)))
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
                  ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x v)))) =
        realization.toIntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
          gauge3 t x u v) := by
  have hfY : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∃ W : Set F,
        W ∈ 𝓝[Set.range I]
          ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)) ∧
        Set.EqOn (f t)
          (fun y : F =>
            let p : M := (G.maps3 t) x
            let q : M := (extChartAt I p).symm y
            tangentCoordChange I q p q (Y t q))
          W :=
    G.model_vectorField_eqOn_tangentCoordChange_of_iUnion_readout_eqOn
      Fₗ U hsource_cover hreadout hfLocal
  exact
    realization.variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_closedBall_model_hasFDerivWithinAt_of_eventuallyEqWithin_of_eqOn_vectorField_of_eventuallyEq_along_maps3_nhdsWithin
      G α gauge3 hgauge_maps hsIcc hchartRHS_eq_intrinsic hDeTurckVector_mdiff
      hXeq htime hbase hball hder hfY hY

/-- Compact-witness scalar route with the patch-local model-field input
discharged from current-time anchored local Picard flows and `LocalGluingData`.

This is the smooth-realization counterpart of the raw compact correction
Picard/local-gluing bridge: it first packages the local Picard witnesses into
the patch-local `EqOn` expected by the existing scalar finite-cover route, then
applies that route unchanged. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_closedBall_model_hasFDerivWithinAt_of_eventuallyEqWithin_of_iUnion_readout_localGluingData_localFlowSolution_of_eventuallyEq_along_maps3_nhdsWithin
    {ι : Type*}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    {tmin tmax : ℝ} {τ₀ : Icc tmin tmax}
    {f : ℝ → F → F} {Df : ℝ → F → F →L[ℝ] F}
    {x₀ : F} {r a : ℝ≥0}
    (α : ModelGaugeFlowODE.VariationalLocalFlowSolution f Df τ₀ x₀ r)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      realization.metric realization.background (Icc ivp.initialTime sol.terminalTime)
      ivp.initialTime)
    (hgauge_maps : gauge3.maps = G.maps3)
    (hsIcc : s ⊆ Icc ivp.initialTime sol.terminalTime)
    (hchartRHS_eq_intrinsic : ∀ ⦃t : ℝ⦄,
      t ∈ Icc ivp.initialTime sol.terminalTime → ∀ x : M,
        ∀ u v : TangentSpace I x,
          A t (sol.curve t) x u v =
            intrinsicRicciDeTurckRHS (I := I) (M := M)
              realization.metric realization.background t x u v)
    {tmin₁ tmax₁ : ℝ}
    (hDeTurckVector_mdiff : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ p : M,
      MDiffAt (T%
        (intrinsicDeTurckVectorField (I := I) (M := M)
          realization.metric realization.background t)) p)
    (hXeq : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      X t ((G.maps3 t) x) =
        intrinsicDeTurckGaugeField (I := I) (M := M)
          realization.metric realization.background t ((G.maps3 t) x))
    (htime : s ⊆ Icc tmin₁ tmax₁)
    (hbase : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ w : TangentSpace I x,
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)) =ᶠ[
          𝓝[s] t] (fun τ : ℝ ↦ α.flow (xE, τ)))
    (hball : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ w : TangentSpace I x,
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        α.flow (xE, t) ∈ Metric.ball x₀ a)
    (hder : ∀ τ ∈ Icc tmin₁ tmax₁, ∀ z ∈ Metric.closedBall x₀ a,
      HasFDerivWithinAt (f τ) (Df τ z) (Metric.closedBall x₀ a) z)
    (Fₗ Gₗ : ι → ℝ → M → M) (U V : ℝ → ι → Set M)
    (hsource_cover : ∀ ⦃t : ℝ⦄, t ∈ s → Set.univ ⊆ ⋃ i, U t i)
    (hreadout : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ i, ∀ x : M, x ∈ U t i →
      ∀ᶠ τ in 𝓝 t, ∃ W' : Set M, W' ∈ 𝓝 x ∧
        EqOn (fun z : M ↦ (G.maps3 τ) z) (Fₗ i τ) W')
    {tminLocal tmaxLocal : ℝ}
    (hltLocal : tminLocal < tmaxLocal)
    (hsLocal : s ⊆ Icc tminLocal tmaxLocal)
    (x₀Local : ∀ (t : ℝ), t ∈ s → ι → M → F)
    (rLocal : ∀ (t : ℝ), t ∈ s → ι → M → ℝ≥0)
    (β : ∀ (t : ℝ) (ht : t ∈ s) (i : ι) (x : M),
      ModelGaugeFlowODE.LocalFlowSolution f
        (⟨t, hsLocal ht⟩ : Icc tminLocal tmaxLocal)
        (x₀Local t ht i x) (rLocal t ht i x))
    (hlocalData : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ i,
      LocalGluingData (I := I) (M := M) 3 (Fₗ i t) (Gₗ i t) (U t i) (V t i))
    (hsourceLocal : ∀ ⦃t : ℝ⦄ (ht : t ∈ s) (i : ι) (x : M),
      x ∈ U t i →
        ∀ q : M, q ∈ V t i ∩ (extChartAt I (Fₗ i t x)).source →
          (fun τ : ℝ ↦ Fₗ i τ (Gₗ i t q)) ⁻¹' (extChartAt I q).source ∈
            𝓝[Icc tminLocal tmaxLocal] t)
    (hballLocal : ∀ ⦃t : ℝ⦄ (ht : t ∈ s) (i : ι) (x : M), x ∈ U t i →
      ∀ y ∈ (extChartAt I (Fₗ i t x)).target ∩
          (extChartAt I (Fₗ i t x)).symm ⁻¹'
            (V t i ∩ (extChartAt I (Fₗ i t x)).source),
        y ∈ Metric.closedBall (x₀Local t ht i x) (rLocal t ht i x))
    (hmodelEqLocal : ∀ ⦃t : ℝ⦄ (ht : t ∈ s) (i : ι) (x : M),
      x ∈ U t i →
        ∀ y ∈ (extChartAt I (Fₗ i t x)).target ∩
            (extChartAt I (Fₗ i t x)).symm ⁻¹'
              (V t i ∩ (extChartAt I (Fₗ i t x)).source),
          (fun τ : ℝ ↦
            (extChartAt I (Fₗ i t x))
              (Fₗ i τ (Gₗ i t ((extChartAt I (Fₗ i t x)).symm y)))) =ᶠ[
                𝓝[Icc tminLocal tmaxLocal] t]
              (fun τ : ℝ ↦ (β t ht i x).flow y τ))
    (hderivLocal : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ i, ∀ z : M, z ∈ U t i →
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I (Fₗ i t z)) (Fₗ i τ z))
        (Y t (Fₗ i t z)) (Icc tminLocal tmaxLocal) t)
    (hY : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ᶠ τ in 𝓝[s] t, ∀ x : M,
        Y τ ((G.maps3 τ) x) =
          intrinsicDeTurckGaugeField (I := I) (M := M)
            realization.metric realization.background τ ((G.maps3 τ) x)) :
    ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ u v : TangentSpace I x,
      ∀ (i : κ) (K : TopologicalSpace.Compacts M)
        (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
        (hK_sub_target : (K : Set M) ⊆
          (trivializationAt BilF
            (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            ((G.maps3 t) x)).baseSet)
        (hKmem_int : (G.maps3 t) x ∈ interior (K : Set M)),
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        (let B' : F →L[ℝ] F →L[ℝ] ℝ :=
          (targetBilinearCoordReadoutContinuousLinearMap
            (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
            (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
            ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target
            (A t (sol.curve t))
            (⟨(G.maps3 t) x, interior_subset hKmem_int⟩ : K)) +
          (fderivWithin ℝ
            (fun yE : F ↦
              SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
                (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
            (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
            (X t ((G.maps3 t) x));
        B'
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
            ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x u))
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
            ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x v)) +
          (realization.metric t).inner ((G.maps3 t) x)
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I)
              ((G.maps3 t) x)
              ((Df t (α.flow (xE, t)))
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
                  ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x u))))
            ((G.maps3 t).pushforwardTangent x v) +
          (realization.metric t).inner ((G.maps3 t) x)
            ((G.maps3 t).pushforwardTangent x u)
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I)
              ((G.maps3 t) x)
              ((Df t (α.flow (xE, t)))
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
                  ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x v)))) =
        realization.toIntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
          gauge3 t x u v) := by
  exact
    realization.variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_closedBall_model_hasFDerivWithinAt_of_eventuallyEqWithin_of_iUnion_readout_eqOn_of_eventuallyEq_along_maps3_nhdsWithin
      G α gauge3 hgauge_maps hsIcc hchartRHS_eq_intrinsic hDeTurckVector_mdiff
      hXeq htime hbase hball hder Fₗ U hsource_cover hreadout
      (Diffeomorph3GaugeFlowOn.model_vectorField_local_eqOn_tangentCoordChange_of_eventuallyEq_mpullbackWithin
        (I := I) (M := M) (Y := Y) (s := s) Fₗ U
        (Diffeomorph3GaugeFlowOn.model_vectorField_eventuallyEq_iUnion_readout_mpullbackWithin_of_localGluingData_localFlowSolution
          (I := I) (M := M) (Y := Y) (s := s) (f := f)
          Fₗ Gₗ U V hltLocal hsLocal x₀Local rLocal β
          hlocalData hsourceLocal hballLocal hmodelEqLocal hderivLocal))
      hY

/-- Compact-witness scalar route with the patch-local model-field input
discharged from current-time anchored local Picard flows, deriving source
persistence from readout continuity and model/readout eventual equality from
patch-local `EqOn` on the Picard time set. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_closedBall_model_hasFDerivWithinAt_of_eventuallyEqWithin_of_iUnion_readout_localGluingData_localFlowSolution_of_continuousWithinAt_of_eqOn_of_eventuallyEq_along_maps3_nhdsWithin
    {ι : Type*}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    {tmin tmax : ℝ} {τ₀ : Icc tmin tmax}
    {f : ℝ → F → F} {Df : ℝ → F → F →L[ℝ] F}
    {x₀ : F} {r a : ℝ≥0}
    (α : ModelGaugeFlowODE.VariationalLocalFlowSolution f Df τ₀ x₀ r)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      realization.metric realization.background (Icc ivp.initialTime sol.terminalTime)
      ivp.initialTime)
    (hgauge_maps : gauge3.maps = G.maps3)
    (hsIcc : s ⊆ Icc ivp.initialTime sol.terminalTime)
    (hchartRHS_eq_intrinsic : ∀ ⦃t : ℝ⦄,
      t ∈ Icc ivp.initialTime sol.terminalTime → ∀ x : M,
        ∀ u v : TangentSpace I x,
          A t (sol.curve t) x u v =
            intrinsicRicciDeTurckRHS (I := I) (M := M)
              realization.metric realization.background t x u v)
    {tmin₁ tmax₁ : ℝ}
    (hDeTurckVector_mdiff : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ p : M,
      MDiffAt (T%
        (intrinsicDeTurckVectorField (I := I) (M := M)
          realization.metric realization.background t)) p)
    (hXeq : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      X t ((G.maps3 t) x) =
        intrinsicDeTurckGaugeField (I := I) (M := M)
          realization.metric realization.background t ((G.maps3 t) x))
    (htime : s ⊆ Icc tmin₁ tmax₁)
    (hbase : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ w : TangentSpace I x,
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)) =ᶠ[
          𝓝[s] t] (fun τ : ℝ ↦ α.flow (xE, τ)))
    (hball : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ w : TangentSpace I x,
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        α.flow (xE, t) ∈ Metric.ball x₀ a)
    (hder : ∀ τ ∈ Icc tmin₁ tmax₁, ∀ z ∈ Metric.closedBall x₀ a,
      HasFDerivWithinAt (f τ) (Df τ z) (Metric.closedBall x₀ a) z)
    (Fₗ Gₗ : ι → ℝ → M → M) (U V : ℝ → ι → Set M)
    (hsource_cover : ∀ ⦃t : ℝ⦄, t ∈ s → Set.univ ⊆ ⋃ i, U t i)
    (hreadout : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ i, ∀ x : M, x ∈ U t i →
      ∀ᶠ τ in 𝓝 t, ∃ W' : Set M, W' ∈ 𝓝 x ∧
        EqOn (fun z : M ↦ (G.maps3 τ) z) (Fₗ i τ) W')
    {tminLocal tmaxLocal : ℝ}
    (hltLocal : tminLocal < tmaxLocal)
    (hsLocal : s ⊆ Icc tminLocal tmaxLocal)
    (x₀Local : ∀ (t : ℝ), t ∈ s → ι → M → F)
    (rLocal : ∀ (t : ℝ), t ∈ s → ι → M → ℝ≥0)
    (β : ∀ (t : ℝ) (ht : t ∈ s) (i : ι) (x : M),
      ModelGaugeFlowODE.LocalFlowSolution f
        (⟨t, hsLocal ht⟩ : Icc tminLocal tmaxLocal)
        (x₀Local t ht i x) (rLocal t ht i x))
    (hlocalData : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ i,
      LocalGluingData (I := I) (M := M) 3 (Fₗ i t) (Gₗ i t) (U t i) (V t i))
    (hcontLocal : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ i, ∀ z : M, z ∈ U t i →
      ContinuousWithinAt (fun τ : ℝ ↦ Fₗ i τ z) (Icc tminLocal tmaxLocal) t)
    (hballLocal : ∀ ⦃t : ℝ⦄ (ht : t ∈ s) (i : ι) (x : M), x ∈ U t i →
      ∀ y ∈ (extChartAt I (Fₗ i t x)).target ∩
          (extChartAt I (Fₗ i t x)).symm ⁻¹'
            (V t i ∩ (extChartAt I (Fₗ i t x)).source),
        y ∈ Metric.closedBall (x₀Local t ht i x) (rLocal t ht i x))
    (hmodelEqOnLocal : ∀ ⦃t : ℝ⦄ (ht : t ∈ s) (i : ι) (x : M),
      x ∈ U t i →
        ∀ y ∈ (extChartAt I (Fₗ i t x)).target ∩
            (extChartAt I (Fₗ i t x)).symm ⁻¹'
              (V t i ∩ (extChartAt I (Fₗ i t x)).source),
          Set.EqOn
            (fun τ : ℝ ↦
              (extChartAt I (Fₗ i t x))
                (Fₗ i τ (Gₗ i t ((extChartAt I (Fₗ i t x)).symm y))))
            (fun τ : ℝ ↦ (β t ht i x).flow y τ) (Icc tminLocal tmaxLocal))
    (hderivLocal : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ i, ∀ z : M, z ∈ U t i →
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I (Fₗ i t z)) (Fₗ i τ z))
        (Y t (Fₗ i t z)) (Icc tminLocal tmaxLocal) t)
    (hY : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ᶠ τ in 𝓝[s] t, ∀ x : M,
        Y τ ((G.maps3 τ) x) =
          intrinsicDeTurckGaugeField (I := I) (M := M)
            realization.metric realization.background τ ((G.maps3 τ) x)) :
    ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ u v : TangentSpace I x,
      ∀ (i : κ) (K : TopologicalSpace.Compacts M)
        (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
        (hK_sub_target : (K : Set M) ⊆
          (trivializationAt BilF
            (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            ((G.maps3 t) x)).baseSet)
        (hKmem_int : (G.maps3 t) x ∈ interior (K : Set M)),
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        (let B' : F →L[ℝ] F →L[ℝ] ℝ :=
          (targetBilinearCoordReadoutContinuousLinearMap
            (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
            (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
            ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target
            (A t (sol.curve t))
            (⟨(G.maps3 t) x, interior_subset hKmem_int⟩ : K)) +
          (fderivWithin ℝ
            (fun yE : F ↦
              SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
                (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
            (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
            (X t ((G.maps3 t) x));
        B'
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
            ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x u))
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
            ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x v)) +
          (realization.metric t).inner ((G.maps3 t) x)
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I)
              ((G.maps3 t) x)
              ((Df t (α.flow (xE, t)))
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
                  ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x u))))
            ((G.maps3 t).pushforwardTangent x v) +
          (realization.metric t).inner ((G.maps3 t) x)
            ((G.maps3 t).pushforwardTangent x u)
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I)
              ((G.maps3 t) x)
              ((Df t (α.flow (xE, t)))
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
                  ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x v)))) =
        realization.toIntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
          gauge3 t x u v) := by
  exact
    realization.variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_closedBall_model_hasFDerivWithinAt_of_eventuallyEqWithin_of_iUnion_readout_localGluingData_localFlowSolution_of_eventuallyEq_along_maps3_nhdsWithin
      G α gauge3 hgauge_maps hsIcc hchartRHS_eq_intrinsic hDeTurckVector_mdiff
      hXeq htime hbase hball hder Fₗ Gₗ U V hsource_cover hreadout
      hltLocal hsLocal x₀Local rLocal β hlocalData
      (Diffeomorph3GaugeFlowOn.iUnion_readout_source_extChartAt_mem_nhdsWithin_of_localGluingData_continuousWithinAt
        (I := I) (M := M) (timeSet := Icc tminLocal tmaxLocal) (s := s)
        Fₗ Gₗ U V hlocalData hcontLocal)
      hballLocal
      (Diffeomorph3GaugeFlowOn.iUnion_readout_model_eventuallyEq_nhdsWithin_of_eqOn
        (I := I) (M := M) (timeSet := Icc tminLocal tmaxLocal) (s := s)
        Fₗ Gₗ U V (fun t ht i x y τ ↦ (β t ht i x).flow y τ)
        hmodelEqOnLocal)
      hderivLocal hY

/-- Compact-witness scalar route with source persistence from readout
continuity and model/readout equality supplied as lifted manifold-side
Picard/readout equality plus target membership. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_closedBall_model_hasFDerivWithinAt_of_eventuallyEqWithin_of_iUnion_readout_localGluingData_localFlowSolution_of_continuousWithinAt_of_lifted_model_eqOn_of_eventuallyEq_along_maps3_nhdsWithin
    {ι : Type*}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    {tmin tmax : ℝ} {τ₀ : Icc tmin tmax}
    {f : ℝ → F → F} {Df : ℝ → F → F →L[ℝ] F}
    {x₀ : F} {r a : ℝ≥0}
    (α : ModelGaugeFlowODE.VariationalLocalFlowSolution f Df τ₀ x₀ r)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      realization.metric realization.background (Icc ivp.initialTime sol.terminalTime)
      ivp.initialTime)
    (hgauge_maps : gauge3.maps = G.maps3)
    (hsIcc : s ⊆ Icc ivp.initialTime sol.terminalTime)
    (hchartRHS_eq_intrinsic : ∀ ⦃t : ℝ⦄,
      t ∈ Icc ivp.initialTime sol.terminalTime → ∀ x : M,
        ∀ u v : TangentSpace I x,
          A t (sol.curve t) x u v =
            intrinsicRicciDeTurckRHS (I := I) (M := M)
              realization.metric realization.background t x u v)
    {tmin₁ tmax₁ : ℝ}
    (hDeTurckVector_mdiff : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ p : M,
      MDiffAt (T%
        (intrinsicDeTurckVectorField (I := I) (M := M)
          realization.metric realization.background t)) p)
    (hXeq : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      X t ((G.maps3 t) x) =
        intrinsicDeTurckGaugeField (I := I) (M := M)
          realization.metric realization.background t ((G.maps3 t) x))
    (htime : s ⊆ Icc tmin₁ tmax₁)
    (hbase : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ w : TangentSpace I x,
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)) =ᶠ[
          𝓝[s] t] (fun τ : ℝ ↦ α.flow (xE, τ)))
    (hball : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ w : TangentSpace I x,
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        α.flow (xE, t) ∈ Metric.ball x₀ a)
    (hder : ∀ τ ∈ Icc tmin₁ tmax₁, ∀ z ∈ Metric.closedBall x₀ a,
      HasFDerivWithinAt (f τ) (Df τ z) (Metric.closedBall x₀ a) z)
    (Fₗ Gₗ : ι → ℝ → M → M) (U V : ℝ → ι → Set M)
    (hsource_cover : ∀ ⦃t : ℝ⦄, t ∈ s → Set.univ ⊆ ⋃ i, U t i)
    (hreadout : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ i, ∀ x : M, x ∈ U t i →
      ∀ᶠ τ in 𝓝 t, ∃ W' : Set M, W' ∈ 𝓝 x ∧
        EqOn (fun z : M ↦ (G.maps3 τ) z) (Fₗ i τ) W')
    {tminLocal tmaxLocal : ℝ}
    (hltLocal : tminLocal < tmaxLocal)
    (hsLocal : s ⊆ Icc tminLocal tmaxLocal)
    (x₀Local : ∀ (t : ℝ), t ∈ s → ι → M → F)
    (rLocal : ∀ (t : ℝ), t ∈ s → ι → M → ℝ≥0)
    (β : ∀ (t : ℝ) (ht : t ∈ s) (i : ι) (x : M),
      ModelGaugeFlowODE.LocalFlowSolution f
        (⟨t, hsLocal ht⟩ : Icc tminLocal tmaxLocal)
        (x₀Local t ht i x) (rLocal t ht i x))
    (hlocalData : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ i,
      LocalGluingData (I := I) (M := M) 3 (Fₗ i t) (Gₗ i t) (U t i) (V t i))
    (hcontLocal : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ i, ∀ z : M, z ∈ U t i →
      ContinuousWithinAt (fun τ : ℝ ↦ Fₗ i τ z) (Icc tminLocal tmaxLocal) t)
    (hballLocal : ∀ ⦃t : ℝ⦄ (ht : t ∈ s) (i : ι) (x : M), x ∈ U t i →
      ∀ y ∈ (extChartAt I (Fₗ i t x)).target ∩
          (extChartAt I (Fₗ i t x)).symm ⁻¹'
            (V t i ∩ (extChartAt I (Fₗ i t x)).source),
        y ∈ Metric.closedBall (x₀Local t ht i x) (rLocal t ht i x))
    (hmodelLiftedEqOn : ∀ ⦃t : ℝ⦄ (ht : t ∈ s) (i : ι) (x : M),
      x ∈ U t i →
        ∀ y ∈ (extChartAt I (Fₗ i t x)).target ∩
            (extChartAt I (Fₗ i t x)).symm ⁻¹'
              (V t i ∩ (extChartAt I (Fₗ i t x)).source),
          Set.EqOn
            (fun τ : ℝ ↦
              Fₗ i τ (Gₗ i t ((extChartAt I (Fₗ i t x)).symm y)))
            (fun τ : ℝ ↦
              (extChartAt I (Fₗ i t x)).symm ((β t ht i x).flow y τ))
            (Icc tminLocal tmaxLocal))
    (hmodelTarget : ∀ ⦃t : ℝ⦄ (ht : t ∈ s) (i : ι) (x : M),
      x ∈ U t i →
        ∀ y ∈ (extChartAt I (Fₗ i t x)).target ∩
            (extChartAt I (Fₗ i t x)).symm ⁻¹'
              (V t i ∩ (extChartAt I (Fₗ i t x)).source),
          ∀ τ ∈ Icc tminLocal tmaxLocal, (β t ht i x).flow y τ ∈
            (extChartAt I (Fₗ i t x)).target)
    (hderivLocal : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ i, ∀ z : M, z ∈ U t i →
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I (Fₗ i t z)) (Fₗ i τ z))
        (Y t (Fₗ i t z)) (Icc tminLocal tmaxLocal) t)
    (hY : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ᶠ τ in 𝓝[s] t, ∀ x : M,
        Y τ ((G.maps3 τ) x) =
          intrinsicDeTurckGaugeField (I := I) (M := M)
            realization.metric realization.background τ ((G.maps3 τ) x)) :
    ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ u v : TangentSpace I x,
      ∀ (i : κ) (K : TopologicalSpace.Compacts M)
        (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
        (hK_sub_target : (K : Set M) ⊆
          (trivializationAt BilF
            (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            ((G.maps3 t) x)).baseSet)
        (hKmem_int : (G.maps3 t) x ∈ interior (K : Set M)),
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        (let B' : F →L[ℝ] F →L[ℝ] ℝ :=
          (targetBilinearCoordReadoutContinuousLinearMap
            (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
            (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
            ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target
            (A t (sol.curve t))
            (⟨(G.maps3 t) x, interior_subset hKmem_int⟩ : K)) +
          (fderivWithin ℝ
            (fun yE : F ↦
              SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
                (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
            (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
            (X t ((G.maps3 t) x));
        B'
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
            ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x u))
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
            ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x v)) +
          (realization.metric t).inner ((G.maps3 t) x)
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I)
              ((G.maps3 t) x)
              ((Df t (α.flow (xE, t)))
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
                  ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x u))))
            ((G.maps3 t).pushforwardTangent x v) +
          (realization.metric t).inner ((G.maps3 t) x)
            ((G.maps3 t).pushforwardTangent x u)
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I)
              ((G.maps3 t) x)
              ((Df t (α.flow (xE, t)))
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
                  ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x v)))) =
        realization.toIntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
          gauge3 t x u v) := by
  exact
    realization.variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_closedBall_model_hasFDerivWithinAt_of_eventuallyEqWithin_of_iUnion_readout_localGluingData_localFlowSolution_of_continuousWithinAt_of_eqOn_of_eventuallyEq_along_maps3_nhdsWithin
      G α gauge3 hgauge_maps hsIcc hchartRHS_eq_intrinsic hDeTurckVector_mdiff
      hXeq htime hbase hball hder Fₗ Gₗ U V hsource_cover hreadout
      hltLocal hsLocal x₀Local rLocal β hlocalData hcontLocal hballLocal
      (Diffeomorph3GaugeFlowOn.iUnion_readout_model_eqOn_of_lifted_model_eqOn
        (I := I) (M := M) (timeSet := Icc tminLocal tmaxLocal) (s := s)
        Fₗ Gₗ U V (fun t ht i x y τ ↦ (β t ht i x).flow y τ)
        hmodelLiftedEqOn hmodelTarget)
      hderivLocal hY

/-- Indexed readout/variational data plus the local Picard/gluing correction
route give tensor time-regularity for the gauge-corrected DeTurck pullback
velocity.

This is the tensor companion of
`variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_closedBall_model_hasFDerivWithinAt_of_eventuallyEqWithin_of_iUnion_readout_localGluingData_localFlowSolution_of_continuousWithinAt_of_lifted_model_eqOn_of_eventuallyEq_along_maps3_nhdsWithin`:
the scalar value identity is derived from lifted Picard equality, local gluing
data, and the auxiliary field agreement before entering the indexed
readout-lifted tensor route. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.hasTimeDerivativeOn_of_variationalTangentMap_readout_mem_ball_iUnion_source_hasFDerivAt_lifted_eqOn_interior_cover_target_overlap_Ioo_gaugeCorrectedPullbackVelocity_of_chartRHS_closedBall_localGluingData_localFlowSolution_of_continuousWithinAt_of_lifted_model_eqOn
    {ι : Type*}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (hcover_int : (⋃ i, interior (Kc i : Set M)) = Set.univ)
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (hs : ∀ ⦃t : ℝ⦄, t ∈ s → s ∈ 𝓝 t)
    (hsIoo : s ⊆ Ioo ivp.initialTime sol.terminalTime)
    {tmin tmax : ℝ} {τ₀ : Icc tmin tmax}
    {f : ℝ → F → F} {Df : ℝ → F → F →L[ℝ] F}
    {x₀ : F} {r a : ℝ≥0}
    (α : ModelGaugeFlowODE.VariationalLocalFlowSolution f Df τ₀ x₀ r)
    (hsModel : s ⊆ Ioo tmin tmax)
    {tmin₁ tmax₁ : ℝ}
    (hDeTurckVector_mdiff : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ p : M,
      MDiffAt (T%
        (intrinsicDeTurckVectorField (I := I) (M := M)
          realization.metric realization.background t)) p)
    (hXeq : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      X t ((G.maps3 t) x) =
        intrinsicDeTurckGaugeField (I := I) (M := M)
          realization.metric realization.background t ((G.maps3 t) x))
    (htime : s ⊆ Icc tmin₁ tmax₁)
    (hbase : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ w : TangentSpace I x,
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)) =ᶠ[
          𝓝[s] t] (fun τ : ℝ ↦ α.flow (xE, τ)))
    (hball : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ w : TangentSpace I x,
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        α.flow (xE, t) ∈ Metric.ball x₀ a)
    (hder : ∀ τ ∈ Icc tmin₁ tmax₁, ∀ z ∈ Metric.closedBall x₀ a,
      HasFDerivWithinAt (f τ) (Df τ z) (Metric.closedBall x₀ a) z)
    (Fₗ Gₗ : ι → ℝ → M → M) (U V : ℝ → ι → Set M)
    (hsource_cover : ∀ ⦃t : ℝ⦄, t ∈ s → Set.univ ⊆ ⋃ i, U t i)
    (hreadout : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ i, ∀ x : M, x ∈ U t i →
        ∀ᶠ τ in 𝓝 t,
          ∃ W : Set M, W ∈ 𝓝 x ∧
            EqOn (fun z : M ↦ (G.maps3 τ) z) (Fₗ i τ) W)
    (hflow_deriv : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ ⦃xE : F⦄, xE ∈ Metric.ball x₀ r →
        ∀ᶠ τ in 𝓝 t,
          HasFDerivAt (fun y : F ↦ α.flow (y, τ))
            (α.tangent xE τ) xE)
    (hdata : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ i, ∀ x : M, x ∈ U t i →
        (extChartAt I x) x ∈ Metric.ball x₀ r ∧
        (extChartAt I ((G.maps3 t) x)).target ∈
          𝓝 (α.flow (((extChartAt I x) x), t)) ∧
        ∀ᶠ τ in 𝓝 t,
          ∃ W : Set M, W ∈ 𝓝 x ∧
            EqOn (Fₗ i τ)
              (fun z : M ↦ (extChartAt I ((G.maps3 t) x)).symm
                (α.flow ((extChartAt I x) z, τ))) W)
    {tminLocal tmaxLocal : ℝ}
    (hltLocal : tminLocal < tmaxLocal)
    (hsLocal : s ⊆ Icc tminLocal tmaxLocal)
    (x₀Local : ∀ (t : ℝ), t ∈ s → ι → M → F)
    (rLocal : ∀ (t : ℝ), t ∈ s → ι → M → ℝ≥0)
    (β : ∀ (t : ℝ) (ht : t ∈ s) (i : ι) (x : M),
      ModelGaugeFlowODE.LocalFlowSolution f
        (⟨t, hsLocal ht⟩ : Icc tminLocal tmaxLocal)
        (x₀Local t ht i x) (rLocal t ht i x))
    (hlocalData : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ i,
      LocalGluingData (I := I) (M := M) 3 (Fₗ i t) (Gₗ i t) (U t i) (V t i))
    (hcontLocal : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ i, ∀ z : M, z ∈ U t i →
      ContinuousWithinAt (fun τ : ℝ ↦ Fₗ i τ z) (Icc tminLocal tmaxLocal) t)
    (hballLocal : ∀ ⦃t : ℝ⦄ (ht : t ∈ s) (i : ι) (x : M), x ∈ U t i →
      ∀ y ∈ (extChartAt I (Fₗ i t x)).target ∩
          (extChartAt I (Fₗ i t x)).symm ⁻¹'
            (V t i ∩ (extChartAt I (Fₗ i t x)).source),
        y ∈ Metric.closedBall (x₀Local t ht i x) (rLocal t ht i x))
    (hmodelLiftedEqOn : ∀ ⦃t : ℝ⦄ (ht : t ∈ s) (i : ι) (x : M),
      x ∈ U t i →
        ∀ y ∈ (extChartAt I (Fₗ i t x)).target ∩
            (extChartAt I (Fₗ i t x)).symm ⁻¹'
              (V t i ∩ (extChartAt I (Fₗ i t x)).source),
          Set.EqOn
            (fun τ : ℝ ↦
              Fₗ i τ (Gₗ i t ((extChartAt I (Fₗ i t x)).symm y)))
            (fun τ : ℝ ↦
              (extChartAt I (Fₗ i t x)).symm ((β t ht i x).flow y τ))
            (Icc tminLocal tmaxLocal))
    (hmodelTarget : ∀ ⦃t : ℝ⦄ (ht : t ∈ s) (i : ι) (x : M),
      x ∈ U t i →
        ∀ y ∈ (extChartAt I (Fₗ i t x)).target ∩
            (extChartAt I (Fₗ i t x)).symm ⁻¹'
              (V t i ∩ (extChartAt I (Fₗ i t x)).source),
          ∀ τ ∈ Icc tminLocal tmaxLocal, (β t ht i x).flow y τ ∈
            (extChartAt I (Fₗ i t x)).target)
    (hderivLocal : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ i, ∀ z : M, z ∈ U t i →
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I (Fₗ i t z)) (Fₗ i τ z))
        (Y t (Fₗ i t z)) (Icc tminLocal tmaxLocal) t)
    (hY : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ᶠ τ in 𝓝[s] t, ∀ x : M,
        Y τ ((G.maps3 τ) x) =
          intrinsicDeTurckGaugeField (I := I) (M := M)
            realization.metric realization.background τ ((G.maps3 τ) x))
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      realization.metric realization.background (Icc ivp.initialTime sol.terminalTime)
      ivp.initialTime)
    (hgauge_maps : gauge3.maps = G.maps3)
    (hchartRHS_eq_intrinsic : ∀ ⦃t : ℝ⦄,
      t ∈ Icc ivp.initialTime sol.terminalTime → ∀ x : M,
        ∀ u v : TangentSpace I x,
          A t (sol.curve t) x u v =
            intrinsicRicciDeTurckRHS (I := I) (M := M)
              realization.metric realization.background t x u v) :
    HasTimeDerivativeOn (I := I) (M := M)
      (G.maps3.pullbackMetricFamily realization.metric)
      (realization.toIntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
        gauge3) s := by
  have hsIcc : s ⊆ Icc ivp.initialTime sol.terminalTime := fun {t} ht =>
    Ioo_subset_Icc_self (hsIoo ht)
  have hvalue :=
    realization.variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_closedBall_model_hasFDerivWithinAt_of_eventuallyEqWithin_of_iUnion_readout_localGluingData_localFlowSolution_of_continuousWithinAt_of_lifted_model_eqOn_of_eventuallyEq_along_maps3_nhdsWithin
      G α gauge3 hgauge_maps hsIcc hchartRHS_eq_intrinsic hDeTurckVector_mdiff
      hXeq htime hbase hball hder Fₗ Gₗ U V hsource_cover hreadout
      hltLocal hsLocal x₀Local rLocal β hlocalData hcontLocal hballLocal
      hmodelLiftedEqOn hmodelTarget hderivLocal hY
  exact
    realization.hasTimeDerivativeOn_of_variationalTangentMap_readout_mem_ball_iUnion_source_hasFDerivAt_lifted_eqOn_interior_cover_target_overlap_Ioo_geometricValue
      (M := M) (F := F) (I := I) hcover_int G hs hsIoo α hsModel Fₗ U
      hsource_cover hreadout hflow_deriv hdata hvalue

/-- State-preserving closed-ball Picard estimates plus local Picard/gluing
correction data give the gauge-corrected tensor time-derivative route.

Compared with
`hasTimeDerivativeOn_of_variationalTangentMap_readout_mem_ball_iUnion_source_hasFDerivAt_lifted_eqOn_interior_cover_target_overlap_Ioo_gaugeCorrectedPullbackVelocity_of_chartRHS_closedBall_localGluingData_localFlowSolution_of_continuousWithinAt_of_lifted_model_eqOn`,
callers provide the compact closed-interval source cover and the selected
state-preserving Picard estimate package; the source-coordinate derivative of
the variational model flow is derived internally. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.hasTimeDerivativeOn_ofProductStatePreservingComponentClosedBallContinuityEstimates_restrict_readout_mem_ball_iUnion_Icc_cover_lifted_eqOn_interior_cover_target_overlap_Ioo_gaugeCorrectedPullbackVelocity_of_chartRHS_closedBall_localGluingData_localFlowSolution_of_continuousWithinAt_of_lifted_model_eqOn
    {ι : Type*}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (hcover_int : (⋃ i, interior (Kc i : Set M)) = Set.univ)
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (hs : ∀ ⦃t : ℝ⦄, t ∈ s → s ∈ 𝓝 t)
    (hsIoo : s ⊆ Ioo ivp.initialTime sol.terminalTime)
    {tmin tmax : ℝ} {tmin0 tmax0 : ℝ} {tbase : Icc tmin0 tmax0}
    {f : ℝ → F → F} {Df : ℝ → F → F →L[ℝ] F}
    {x₀ : F} {a R Kf KD Lf BA BD r : ℝ≥0}
    (hf_lip : ∀ t ∈ Icc tmin0 tmax0,
      LipschitzOnWith Kf (f t) (Metric.closedBall x₀ a))
    (hDf_lip : ∀ t ∈ Icc tmin0 tmax0,
      LipschitzOnWith KD (Df t) (Metric.closedBall x₀ a))
    (hf_bound : ∀ t ∈ Icc tmin0 tmax0, ∀ y ∈ Metric.closedBall x₀ a,
      ‖f t y‖ ≤ Lf)
    (hA_bound : ∀ A ∈ Metric.closedBall (1 : F →L[ℝ] F) a, ‖A‖₊ ≤ BA)
    (hD_bound : ∀ t ∈ Icc tmin0 tmax0, ∀ y ∈ Metric.closedBall x₀ a,
      ‖Df t y‖₊ ≤ BD)
    (hf_cont : ∀ y ∈ Metric.closedBall x₀ a,
      ContinuousOn (fun t : ℝ => f t y) (Icc tmin0 tmax0))
    (hDf_cont : ∀ y ∈ Metric.closedBall x₀ a,
      ContinuousOn (fun t : ℝ => Df t y) (Icc tmin0 tmax0))
    (hmul : (max Lf (BD * BA)) * max (tmax0 - tbase) (tbase - tmin0) ≤ a - R)
    (htime : Icc tmin tmax ⊆ Icc tmin0 tmax0)
    (htbase : (tbase : ℝ) ∈ Icc tmin tmax)
    (hr : r ≤ R)
    (hder : ∀ τ ∈ Icc tmin0 tmax0, ∀ z ∈ Metric.closedBall x₀ a,
      HasFDerivWithinAt (f τ) (Df τ z) (Metric.closedBall x₀ a) z)
    (α : ModelGaugeFlowODE.VariationalLocalFlowSolution f Df
      (⟨(tbase : ℝ), htbase⟩ : Icc tmin tmax) x₀ r)
    (hα : α =
      ModelGaugeFlowODE.VariationalLocalFlowSolution.ofProductStatePreservingComponentClosedBallContinuityEstimates_restrict
        (t₀ := tbase) hf_lip hDf_lip hf_bound hA_bound hD_bound
        hf_cont hDf_cont hmul htime htbase hr)
    (hsModel : s ⊆ Ioo tmin tmax)
    (hDeTurckVector_mdiff : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ p : M,
      MDiffAt (T%
        (intrinsicDeTurckVectorField (I := I) (M := M)
          realization.metric realization.background t)) p)
    (hXeq : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      X t ((G.maps3 t) x) =
        intrinsicDeTurckGaugeField (I := I) (M := M)
          realization.metric realization.background t ((G.maps3 t) x))
    (hbase : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ w : TangentSpace I x,
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)) =ᶠ[
          𝓝[s] t] (fun τ : ℝ ↦ α.flow (xE, τ)))
    (hball : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ w : TangentSpace I x,
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        α.flow (xE, t) ∈ Metric.ball x₀ a)
    (Fₗ Gₗ : ι → ℝ → M → M) (U V : ℝ → ι → Set M)
    (hsource_cover : ∀ ⦃t : ℝ⦄, t ∈ Icc tmin tmax → Set.univ ⊆ ⋃ i, U t i)
    (hreadout : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ i, ∀ x : M, x ∈ U t i →
        ∀ᶠ τ in 𝓝 t,
          ∃ W : Set M, W ∈ 𝓝 x ∧
            EqOn (fun z : M ↦ (G.maps3 τ) z) (Fₗ i τ) W)
    (hdata : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ i, ∀ x : M, x ∈ U t i →
        (extChartAt I x) x ∈ Metric.ball x₀ r ∧
        (extChartAt I ((G.maps3 t) x)).target ∈
          𝓝 (α.flow (((extChartAt I x) x), t)) ∧
        ∀ᶠ τ in 𝓝 t,
          ∃ W : Set M, W ∈ 𝓝 x ∧
            EqOn (Fₗ i τ)
              (fun z : M ↦ (extChartAt I ((G.maps3 t) x)).symm
                (α.flow ((extChartAt I x) z, τ))) W)
    {tminLocal tmaxLocal : ℝ}
    (hltLocal : tminLocal < tmaxLocal)
    (hsLocal : s ⊆ Icc tminLocal tmaxLocal)
    (x₀Local : ∀ (t : ℝ), t ∈ s → ι → M → F)
    (rLocal : ∀ (t : ℝ), t ∈ s → ι → M → ℝ≥0)
    (β : ∀ (t : ℝ) (ht : t ∈ s) (i : ι) (x : M),
      ModelGaugeFlowODE.LocalFlowSolution f
        (⟨t, hsLocal ht⟩ : Icc tminLocal tmaxLocal)
        (x₀Local t ht i x) (rLocal t ht i x))
    (hlocalData : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ i,
      LocalGluingData (I := I) (M := M) 3 (Fₗ i t) (Gₗ i t) (U t i) (V t i))
    (hcontLocal : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ i, ∀ z : M, z ∈ U t i →
      ContinuousWithinAt (fun τ : ℝ ↦ Fₗ i τ z) (Icc tminLocal tmaxLocal) t)
    (hballLocal : ∀ ⦃t : ℝ⦄ (ht : t ∈ s) (i : ι) (x : M), x ∈ U t i →
      ∀ y ∈ (extChartAt I (Fₗ i t x)).target ∩
          (extChartAt I (Fₗ i t x)).symm ⁻¹'
            (V t i ∩ (extChartAt I (Fₗ i t x)).source),
        y ∈ Metric.closedBall (x₀Local t ht i x) (rLocal t ht i x))
    (hmodelLiftedEqOn : ∀ ⦃t : ℝ⦄ (ht : t ∈ s) (i : ι) (x : M),
      x ∈ U t i →
        ∀ y ∈ (extChartAt I (Fₗ i t x)).target ∩
            (extChartAt I (Fₗ i t x)).symm ⁻¹'
              (V t i ∩ (extChartAt I (Fₗ i t x)).source),
          Set.EqOn
            (fun τ : ℝ ↦
              Fₗ i τ (Gₗ i t ((extChartAt I (Fₗ i t x)).symm y)))
            (fun τ : ℝ ↦
              (extChartAt I (Fₗ i t x)).symm ((β t ht i x).flow y τ))
            (Icc tminLocal tmaxLocal))
    (hmodelTarget : ∀ ⦃t : ℝ⦄ (ht : t ∈ s) (i : ι) (x : M),
      x ∈ U t i →
        ∀ y ∈ (extChartAt I (Fₗ i t x)).target ∩
            (extChartAt I (Fₗ i t x)).symm ⁻¹'
              (V t i ∩ (extChartAt I (Fₗ i t x)).source),
          ∀ τ ∈ Icc tminLocal tmaxLocal, (β t ht i x).flow y τ ∈
            (extChartAt I (Fₗ i t x)).target)
    (hderivLocal : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ i, ∀ z : M, z ∈ U t i →
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I (Fₗ i t z)) (Fₗ i τ z))
        (Y t (Fₗ i t z)) (Icc tminLocal tmaxLocal) t)
    (hY : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ᶠ τ in 𝓝[s] t, ∀ x : M,
        Y τ ((G.maps3 τ) x) =
          intrinsicDeTurckGaugeField (I := I) (M := M)
            realization.metric realization.background τ ((G.maps3 τ) x))
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      realization.metric realization.background (Icc ivp.initialTime sol.terminalTime)
      ivp.initialTime)
    (hgauge_maps : gauge3.maps = G.maps3)
    (hchartRHS_eq_intrinsic : ∀ ⦃t : ℝ⦄,
      t ∈ Icc ivp.initialTime sol.terminalTime → ∀ x : M,
        ∀ u v : TangentSpace I x,
          A t (sol.curve t) x u v =
            intrinsicRicciDeTurckRHS (I := I) (M := M)
              realization.metric realization.background t x u v) :
    HasTimeDerivativeOn (I := I) (M := M)
      (G.maps3.pullbackMetricFamily realization.metric)
      (realization.toIntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
        gauge3) s := by
  have hflow_deriv : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ ⦃xE : F⦄, xE ∈ Metric.ball x₀ r →
        ∀ᶠ τ in 𝓝 t,
          HasFDerivAt (fun y : F ↦ α.flow (y, τ))
            (α.tangent xE τ) xE := by
    have hsource : ∀ ⦃t : ℝ⦄, t ∈ Ioo tmin tmax →
        ∀ ⦃xE : F⦄, xE ∈ Metric.ball x₀ r →
          ∀ᶠ τ in 𝓝 t,
            HasFDerivAt (fun y : F ↦ α.flow (y, τ))
              (α.tangent xE τ) xE := by
      simpa [hα] using
        (ModelGaugeFlowODE.VariationalLocalFlowSolution.ofProductStatePreservingComponentClosedBallContinuityEstimates_restrict_source_eventually_flow_timeSlice_hasFDerivAt_of_hasFDerivWithinAt_Ioo_of_le_radius
          (t₀ := tbase) hf_lip hDf_lip hf_bound hA_bound hD_bound
          hf_cont hDf_cont hmul htime htbase hr hder)
    intro t ht xE hxE
    exact hsource (hsModel ht) hxE
  exact
    realization.hasTimeDerivativeOn_of_variationalTangentMap_readout_mem_ball_iUnion_source_hasFDerivAt_lifted_eqOn_interior_cover_target_overlap_Ioo_gaugeCorrectedPullbackVelocity_of_chartRHS_closedBall_localGluingData_localFlowSolution_of_continuousWithinAt_of_lifted_model_eqOn
      hcover_int G hs hsIoo α hsModel hDeTurckVector_mdiff hXeq
      (fun {t} ht ↦ htime (Ioo_subset_Icc_self (hsModel ht))) hbase hball hder
      Fₗ Gₗ U V
      (fun {t} ht ↦ hsource_cover (Ioo_subset_Icc_self (hsModel ht)))
      hreadout hflow_deriv hdata hltLocal hsLocal x₀Local rLocal β
      hlocalData hcontLocal hballLocal hmodelLiftedEqOn hmodelTarget
      hderivLocal hY gauge3 hgauge_maps hchartRHS_eq_intrinsic

/-- Intrinsic-gauge-field specialization of
`hasTimeDerivativeOn_of_variationalTangentMap_readout_mem_ball_iUnion_source_hasFDerivAt_lifted_eqOn_interior_cover_target_overlap_Ioo_gaugeCorrectedPullbackVelocity_of_chartRHS_closedBall_localGluingData_localFlowSolution_of_continuousWithinAt_of_lifted_model_eqOn`.

The local Picard/gluing correction route is unchanged; the pointwise vector-field
identity is discharged because the raw `C³` flow is already driven by the
intrinsic DeTurck gauge field of the smooth realization. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.hasTimeDerivativeOn_of_variationalTangentMap_readout_mem_ball_iUnion_source_hasFDerivAt_lifted_eqOn_interior_cover_target_overlap_Ioo_gaugeCorrectedPullbackVelocity_of_chartRHS_closedBall_localGluingData_localFlowSolution_of_continuousWithinAt_of_lifted_model_eqOn_of_intrinsicDeTurckGaugeField
    {ι : Type*}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (hcover_int : (⋃ i, interior (Kc i : Set M)) = Set.univ)
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (intrinsicDeTurckGaugeField (I := I) (M := M)
        realization.metric realization.background) s gaugeInitialTime)
    (hs : ∀ ⦃t : ℝ⦄, t ∈ s → s ∈ 𝓝 t)
    (hsIoo : s ⊆ Ioo ivp.initialTime sol.terminalTime)
    {tmin tmax : ℝ} {τ₀ : Icc tmin tmax}
    {f : ℝ → F → F} {Df : ℝ → F → F →L[ℝ] F}
    {x₀ : F} {r a : ℝ≥0}
    (α : ModelGaugeFlowODE.VariationalLocalFlowSolution f Df τ₀ x₀ r)
    (hsModel : s ⊆ Ioo tmin tmax)
    {tmin₁ tmax₁ : ℝ}
    (hDeTurckVector_mdiff : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ p : M,
      MDiffAt (T%
        (intrinsicDeTurckVectorField (I := I) (M := M)
          realization.metric realization.background t)) p)
    (htime : s ⊆ Icc tmin₁ tmax₁)
    (hbase : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ w : TangentSpace I x,
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)) =ᶠ[
          𝓝[s] t] (fun τ : ℝ ↦ α.flow (xE, τ)))
    (hball : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ w : TangentSpace I x,
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        α.flow (xE, t) ∈ Metric.ball x₀ a)
    (hder : ∀ τ ∈ Icc tmin₁ tmax₁, ∀ z ∈ Metric.closedBall x₀ a,
      HasFDerivWithinAt (f τ) (Df τ z) (Metric.closedBall x₀ a) z)
    (Fₗ Gₗ : ι → ℝ → M → M) (U V : ℝ → ι → Set M)
    (hsource_cover : ∀ ⦃t : ℝ⦄, t ∈ s → Set.univ ⊆ ⋃ i, U t i)
    (hreadout : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ i, ∀ x : M, x ∈ U t i →
        ∀ᶠ τ in 𝓝 t,
          ∃ W : Set M, W ∈ 𝓝 x ∧
            EqOn (fun z : M ↦ (G.maps3 τ) z) (Fₗ i τ) W)
    (hflow_deriv : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ ⦃xE : F⦄, xE ∈ Metric.ball x₀ r →
        ∀ᶠ τ in 𝓝 t,
          HasFDerivAt (fun y : F ↦ α.flow (y, τ))
            (α.tangent xE τ) xE)
    (hdata : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ i, ∀ x : M, x ∈ U t i →
        (extChartAt I x) x ∈ Metric.ball x₀ r ∧
        (extChartAt I ((G.maps3 t) x)).target ∈
          𝓝 (α.flow (((extChartAt I x) x), t)) ∧
        ∀ᶠ τ in 𝓝 t,
          ∃ W : Set M, W ∈ 𝓝 x ∧
            EqOn (Fₗ i τ)
              (fun z : M ↦ (extChartAt I ((G.maps3 t) x)).symm
                (α.flow ((extChartAt I x) z, τ))) W)
    {tminLocal tmaxLocal : ℝ}
    (hltLocal : tminLocal < tmaxLocal)
    (hsLocal : s ⊆ Icc tminLocal tmaxLocal)
    (x₀Local : ∀ (t : ℝ), t ∈ s → ι → M → F)
    (rLocal : ∀ (t : ℝ), t ∈ s → ι → M → ℝ≥0)
    (β : ∀ (t : ℝ) (ht : t ∈ s) (i : ι) (x : M),
      ModelGaugeFlowODE.LocalFlowSolution f
        (⟨t, hsLocal ht⟩ : Icc tminLocal tmaxLocal)
        (x₀Local t ht i x) (rLocal t ht i x))
    (hlocalData : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ i,
      LocalGluingData (I := I) (M := M) 3 (Fₗ i t) (Gₗ i t) (U t i) (V t i))
    (hcontLocal : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ i, ∀ z : M, z ∈ U t i →
      ContinuousWithinAt (fun τ : ℝ ↦ Fₗ i τ z) (Icc tminLocal tmaxLocal) t)
    (hballLocal : ∀ ⦃t : ℝ⦄ (ht : t ∈ s) (i : ι) (x : M), x ∈ U t i →
      ∀ y ∈ (extChartAt I (Fₗ i t x)).target ∩
          (extChartAt I (Fₗ i t x)).symm ⁻¹'
            (V t i ∩ (extChartAt I (Fₗ i t x)).source),
        y ∈ Metric.closedBall (x₀Local t ht i x) (rLocal t ht i x))
    (hmodelLiftedEqOn : ∀ ⦃t : ℝ⦄ (ht : t ∈ s) (i : ι) (x : M),
      x ∈ U t i →
        ∀ y ∈ (extChartAt I (Fₗ i t x)).target ∩
            (extChartAt I (Fₗ i t x)).symm ⁻¹'
              (V t i ∩ (extChartAt I (Fₗ i t x)).source),
          Set.EqOn
            (fun τ : ℝ ↦
              Fₗ i τ (Gₗ i t ((extChartAt I (Fₗ i t x)).symm y)))
            (fun τ : ℝ ↦
              (extChartAt I (Fₗ i t x)).symm ((β t ht i x).flow y τ))
            (Icc tminLocal tmaxLocal))
    (hmodelTarget : ∀ ⦃t : ℝ⦄ (ht : t ∈ s) (i : ι) (x : M),
      x ∈ U t i →
        ∀ y ∈ (extChartAt I (Fₗ i t x)).target ∩
            (extChartAt I (Fₗ i t x)).symm ⁻¹'
              (V t i ∩ (extChartAt I (Fₗ i t x)).source),
          ∀ τ ∈ Icc tminLocal tmaxLocal, (β t ht i x).flow y τ ∈
            (extChartAt I (Fₗ i t x)).target)
    (hderivLocal : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ i, ∀ z : M, z ∈ U t i →
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I (Fₗ i t z)) (Fₗ i τ z))
        (Y t (Fₗ i t z)) (Icc tminLocal tmaxLocal) t)
    (hY : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ᶠ τ in 𝓝[s] t, ∀ x : M,
        Y τ ((G.maps3 τ) x) =
          intrinsicDeTurckGaugeField (I := I) (M := M)
            realization.metric realization.background τ ((G.maps3 τ) x))
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      realization.metric realization.background (Icc ivp.initialTime sol.terminalTime)
      ivp.initialTime)
    (hgauge_maps : gauge3.maps = G.maps3)
    (hchartRHS_eq_intrinsic : ∀ ⦃t : ℝ⦄,
      t ∈ Icc ivp.initialTime sol.terminalTime → ∀ x : M,
        ∀ u v : TangentSpace I x,
          A t (sol.curve t) x u v =
            intrinsicRicciDeTurckRHS (I := I) (M := M)
              realization.metric realization.background t x u v) :
    HasTimeDerivativeOn (I := I) (M := M)
      (G.maps3.pullbackMetricFamily realization.metric)
      (realization.toIntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
        gauge3) s := by
  exact
    realization.hasTimeDerivativeOn_of_variationalTangentMap_readout_mem_ball_iUnion_source_hasFDerivAt_lifted_eqOn_interior_cover_target_overlap_Ioo_gaugeCorrectedPullbackVelocity_of_chartRHS_closedBall_localGluingData_localFlowSolution_of_continuousWithinAt_of_lifted_model_eqOn
      hcover_int G hs hsIoo α hsModel hDeTurckVector_mdiff
      (fun {_t} _ht _x ↦ rfl) htime hbase hball hder Fₗ Gₗ U V
      hsource_cover hreadout hflow_deriv hdata hltLocal hsLocal x₀Local
      rLocal β hlocalData hcontLocal hballLocal hmodelLiftedEqOn
      hmodelTarget hderivLocal hY gauge3 hgauge_maps hchartRHS_eq_intrinsic

/-- State-preserving closed-ball Picard estimates plus local Picard/gluing
correction data give the intrinsic-gauge tensor time-derivative route.

Compared with
`hasTimeDerivativeOn_of_variationalTangentMap_readout_mem_ball_iUnion_source_hasFDerivAt_lifted_eqOn_interior_cover_target_overlap_Ioo_gaugeCorrectedPullbackVelocity_of_chartRHS_closedBall_localGluingData_localFlowSolution_of_continuousWithinAt_of_lifted_model_eqOn_of_intrinsicDeTurckGaugeField`,
callers provide the compact closed-interval source cover and the selected
state-preserving Picard estimate package; the source-coordinate derivative of
the variational model flow is derived internally. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.hasTimeDerivativeOn_ofProductStatePreservingComponentClosedBallContinuityEstimates_restrict_readout_mem_ball_iUnion_Icc_cover_lifted_eqOn_interior_cover_target_overlap_Ioo_gaugeCorrectedPullbackVelocity_of_chartRHS_closedBall_localGluingData_localFlowSolution_of_continuousWithinAt_of_lifted_model_eqOn_of_intrinsicDeTurckGaugeField
    {ι : Type*}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (hcover_int : (⋃ i, interior (Kc i : Set M)) = Set.univ)
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (intrinsicDeTurckGaugeField (I := I) (M := M)
        realization.metric realization.background) s gaugeInitialTime)
    (hs : ∀ ⦃t : ℝ⦄, t ∈ s → s ∈ 𝓝 t)
    (hsIoo : s ⊆ Ioo ivp.initialTime sol.terminalTime)
    {tmin tmax : ℝ} {tmin0 tmax0 : ℝ} {tbase : Icc tmin0 tmax0}
    {f : ℝ → F → F} {Df : ℝ → F → F →L[ℝ] F}
    {x₀ : F} {a R Kf KD Lf BA BD r : ℝ≥0}
    (hf_lip : ∀ t ∈ Icc tmin0 tmax0,
      LipschitzOnWith Kf (f t) (Metric.closedBall x₀ a))
    (hDf_lip : ∀ t ∈ Icc tmin0 tmax0,
      LipschitzOnWith KD (Df t) (Metric.closedBall x₀ a))
    (hf_bound : ∀ t ∈ Icc tmin0 tmax0, ∀ y ∈ Metric.closedBall x₀ a,
      ‖f t y‖ ≤ Lf)
    (hA_bound : ∀ A ∈ Metric.closedBall (1 : F →L[ℝ] F) a, ‖A‖₊ ≤ BA)
    (hD_bound : ∀ t ∈ Icc tmin0 tmax0, ∀ y ∈ Metric.closedBall x₀ a,
      ‖Df t y‖₊ ≤ BD)
    (hf_cont : ∀ y ∈ Metric.closedBall x₀ a,
      ContinuousOn (fun t : ℝ => f t y) (Icc tmin0 tmax0))
    (hDf_cont : ∀ y ∈ Metric.closedBall x₀ a,
      ContinuousOn (fun t : ℝ => Df t y) (Icc tmin0 tmax0))
    (hmul : (max Lf (BD * BA)) * max (tmax0 - tbase) (tbase - tmin0) ≤ a - R)
    (htime : Icc tmin tmax ⊆ Icc tmin0 tmax0)
    (htbase : (tbase : ℝ) ∈ Icc tmin tmax)
    (hr : r ≤ R)
    (hder : ∀ τ ∈ Icc tmin0 tmax0, ∀ z ∈ Metric.closedBall x₀ a,
      HasFDerivWithinAt (f τ) (Df τ z) (Metric.closedBall x₀ a) z)
    (α : ModelGaugeFlowODE.VariationalLocalFlowSolution f Df
      (⟨(tbase : ℝ), htbase⟩ : Icc tmin tmax) x₀ r)
    (hα : α =
      ModelGaugeFlowODE.VariationalLocalFlowSolution.ofProductStatePreservingComponentClosedBallContinuityEstimates_restrict
        (t₀ := tbase) hf_lip hDf_lip hf_bound hA_bound hD_bound
        hf_cont hDf_cont hmul htime htbase hr)
    (hsModel : s ⊆ Ioo tmin tmax)
    (hDeTurckVector_mdiff : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ p : M,
      MDiffAt (T%
        (intrinsicDeTurckVectorField (I := I) (M := M)
          realization.metric realization.background t)) p)
    (hbase : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ w : TangentSpace I x,
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)) =ᶠ[
          𝓝[s] t] (fun τ : ℝ ↦ α.flow (xE, τ)))
    (hball : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ w : TangentSpace I x,
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        α.flow (xE, t) ∈ Metric.ball x₀ a)
    (Fₗ Gₗ : ι → ℝ → M → M) (U V : ℝ → ι → Set M)
    (hsource_cover : ∀ ⦃t : ℝ⦄, t ∈ Icc tmin tmax → Set.univ ⊆ ⋃ i, U t i)
    (hreadout : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ i, ∀ x : M, x ∈ U t i →
        ∀ᶠ τ in 𝓝 t,
          ∃ W : Set M, W ∈ 𝓝 x ∧
            EqOn (fun z : M ↦ (G.maps3 τ) z) (Fₗ i τ) W)
    (hdata : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ i, ∀ x : M, x ∈ U t i →
        (extChartAt I x) x ∈ Metric.ball x₀ r ∧
        (extChartAt I ((G.maps3 t) x)).target ∈
          𝓝 (α.flow (((extChartAt I x) x), t)) ∧
        ∀ᶠ τ in 𝓝 t,
          ∃ W : Set M, W ∈ 𝓝 x ∧
            EqOn (Fₗ i τ)
              (fun z : M ↦ (extChartAt I ((G.maps3 t) x)).symm
                (α.flow ((extChartAt I x) z, τ))) W)
    {tminLocal tmaxLocal : ℝ}
    (hltLocal : tminLocal < tmaxLocal)
    (hsLocal : s ⊆ Icc tminLocal tmaxLocal)
    (x₀Local : ∀ (t : ℝ), t ∈ s → ι → M → F)
    (rLocal : ∀ (t : ℝ), t ∈ s → ι → M → ℝ≥0)
    (β : ∀ (t : ℝ) (ht : t ∈ s) (i : ι) (x : M),
      ModelGaugeFlowODE.LocalFlowSolution f
        (⟨t, hsLocal ht⟩ : Icc tminLocal tmaxLocal)
        (x₀Local t ht i x) (rLocal t ht i x))
    (hlocalData : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ i,
      LocalGluingData (I := I) (M := M) 3 (Fₗ i t) (Gₗ i t) (U t i) (V t i))
    (hcontLocal : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ i, ∀ z : M, z ∈ U t i →
      ContinuousWithinAt (fun τ : ℝ ↦ Fₗ i τ z) (Icc tminLocal tmaxLocal) t)
    (hballLocal : ∀ ⦃t : ℝ⦄ (ht : t ∈ s) (i : ι) (x : M), x ∈ U t i →
      ∀ y ∈ (extChartAt I (Fₗ i t x)).target ∩
          (extChartAt I (Fₗ i t x)).symm ⁻¹'
            (V t i ∩ (extChartAt I (Fₗ i t x)).source),
        y ∈ Metric.closedBall (x₀Local t ht i x) (rLocal t ht i x))
    (hmodelLiftedEqOn : ∀ ⦃t : ℝ⦄ (ht : t ∈ s) (i : ι) (x : M),
      x ∈ U t i →
        ∀ y ∈ (extChartAt I (Fₗ i t x)).target ∩
            (extChartAt I (Fₗ i t x)).symm ⁻¹'
              (V t i ∩ (extChartAt I (Fₗ i t x)).source),
          Set.EqOn
            (fun τ : ℝ ↦
              Fₗ i τ (Gₗ i t ((extChartAt I (Fₗ i t x)).symm y)))
            (fun τ : ℝ ↦
              (extChartAt I (Fₗ i t x)).symm ((β t ht i x).flow y τ))
            (Icc tminLocal tmaxLocal))
    (hmodelTarget : ∀ ⦃t : ℝ⦄ (ht : t ∈ s) (i : ι) (x : M),
      x ∈ U t i →
        ∀ y ∈ (extChartAt I (Fₗ i t x)).target ∩
            (extChartAt I (Fₗ i t x)).symm ⁻¹'
              (V t i ∩ (extChartAt I (Fₗ i t x)).source),
          ∀ τ ∈ Icc tminLocal tmaxLocal, (β t ht i x).flow y τ ∈
            (extChartAt I (Fₗ i t x)).target)
    (hderivLocal : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ i, ∀ z : M, z ∈ U t i →
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I (Fₗ i t z)) (Fₗ i τ z))
        (Y t (Fₗ i t z)) (Icc tminLocal tmaxLocal) t)
    (hY : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ᶠ τ in 𝓝[s] t, ∀ x : M,
        Y τ ((G.maps3 τ) x) =
          intrinsicDeTurckGaugeField (I := I) (M := M)
            realization.metric realization.background τ ((G.maps3 τ) x))
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      realization.metric realization.background (Icc ivp.initialTime sol.terminalTime)
      ivp.initialTime)
    (hgauge_maps : gauge3.maps = G.maps3)
    (hchartRHS_eq_intrinsic : ∀ ⦃t : ℝ⦄,
      t ∈ Icc ivp.initialTime sol.terminalTime → ∀ x : M,
        ∀ u v : TangentSpace I x,
          A t (sol.curve t) x u v =
            intrinsicRicciDeTurckRHS (I := I) (M := M)
              realization.metric realization.background t x u v) :
    HasTimeDerivativeOn (I := I) (M := M)
      (G.maps3.pullbackMetricFamily realization.metric)
      (realization.toIntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
        gauge3) s := by
  have hflow_deriv : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ ⦃xE : F⦄, xE ∈ Metric.ball x₀ r →
        ∀ᶠ τ in 𝓝 t,
          HasFDerivAt (fun y : F ↦ α.flow (y, τ))
            (α.tangent xE τ) xE := by
    have hsource : ∀ ⦃t : ℝ⦄, t ∈ Ioo tmin tmax →
        ∀ ⦃xE : F⦄, xE ∈ Metric.ball x₀ r →
          ∀ᶠ τ in 𝓝 t,
            HasFDerivAt (fun y : F ↦ α.flow (y, τ))
              (α.tangent xE τ) xE := by
      simpa [hα] using
        (ModelGaugeFlowODE.VariationalLocalFlowSolution.ofProductStatePreservingComponentClosedBallContinuityEstimates_restrict_source_eventually_flow_timeSlice_hasFDerivAt_of_hasFDerivWithinAt_Ioo_of_le_radius
          (t₀ := tbase) hf_lip hDf_lip hf_bound hA_bound hD_bound
          hf_cont hDf_cont hmul htime htbase hr hder)
    intro t ht xE hxE
    exact hsource (hsModel ht) hxE
  exact
    realization.hasTimeDerivativeOn_of_variationalTangentMap_readout_mem_ball_iUnion_source_hasFDerivAt_lifted_eqOn_interior_cover_target_overlap_Ioo_gaugeCorrectedPullbackVelocity_of_chartRHS_closedBall_localGluingData_localFlowSolution_of_continuousWithinAt_of_lifted_model_eqOn_of_intrinsicDeTurckGaugeField
      hcover_int G hs hsIoo α hsModel hDeTurckVector_mdiff
      (fun {t} ht ↦ htime (Ioo_subset_Icc_self (hsModel ht))) hbase hball hder
      Fₗ Gₗ U V
      (fun {t} ht ↦ hsource_cover (Ioo_subset_Icc_self (hsModel ht)))
      hreadout hflow_deriv hdata hltLocal hsLocal x₀Local rLocal β
      hlocalData hcontLocal hballLocal hmodelLiftedEqOn hmodelTarget
      hderivLocal hY gauge3 hgauge_maps hchartRHS_eq_intrinsic

/-- Smooth-background specialization of the state-preserving intrinsic local
Picard/gluing tensor route.

The source-coordinate derivative is supplied by the state-preserving closed-ball
Picard estimates, and the DeTurck-vector `MDiffAt` input is discharged from
slicewise `C¹` regularity of the background connection. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.hasTimeDerivativeOn_ofProductStatePreservingComponentClosedBallContinuityEstimates_restrict_readout_mem_ball_iUnion_Icc_cover_lifted_eqOn_interior_cover_target_overlap_Ioo_gaugeCorrectedPullbackVelocity_of_chartRHS_closedBall_localGluingData_localFlowSolution_of_continuousWithinAt_of_lifted_model_eqOn_of_intrinsicDeTurckGaugeField_of_contMDiffCovariantDerivative_background
    {ι : Type*}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (hcover_int : (⋃ i, interior (Kc i : Set M)) = Set.univ)
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (intrinsicDeTurckGaugeField (I := I) (M := M)
        realization.metric realization.background) s gaugeInitialTime)
    (hs : ∀ ⦃t : ℝ⦄, t ∈ s → s ∈ 𝓝 t)
    (hsIoo : s ⊆ Ioo ivp.initialTime sol.terminalTime)
    {tmin tmax : ℝ} {tmin0 tmax0 : ℝ} {tbase : Icc tmin0 tmax0}
    {f : ℝ → F → F} {Df : ℝ → F → F →L[ℝ] F}
    {x₀ : F} {a R Kf KD Lf BA BD r : ℝ≥0}
    (hf_lip : ∀ t ∈ Icc tmin0 tmax0,
      LipschitzOnWith Kf (f t) (Metric.closedBall x₀ a))
    (hDf_lip : ∀ t ∈ Icc tmin0 tmax0,
      LipschitzOnWith KD (Df t) (Metric.closedBall x₀ a))
    (hf_bound : ∀ t ∈ Icc tmin0 tmax0, ∀ y ∈ Metric.closedBall x₀ a,
      ‖f t y‖ ≤ Lf)
    (hA_bound : ∀ A ∈ Metric.closedBall (1 : F →L[ℝ] F) a, ‖A‖₊ ≤ BA)
    (hD_bound : ∀ t ∈ Icc tmin0 tmax0, ∀ y ∈ Metric.closedBall x₀ a,
      ‖Df t y‖₊ ≤ BD)
    (hf_cont : ∀ y ∈ Metric.closedBall x₀ a,
      ContinuousOn (fun t : ℝ => f t y) (Icc tmin0 tmax0))
    (hDf_cont : ∀ y ∈ Metric.closedBall x₀ a,
      ContinuousOn (fun t : ℝ => Df t y) (Icc tmin0 tmax0))
    (hmul : (max Lf (BD * BA)) * max (tmax0 - tbase) (tbase - tmin0) ≤ a - R)
    (htime : Icc tmin tmax ⊆ Icc tmin0 tmax0)
    (htbase : (tbase : ℝ) ∈ Icc tmin tmax)
    (hr : r ≤ R)
    (hder : ∀ τ ∈ Icc tmin0 tmax0, ∀ z ∈ Metric.closedBall x₀ a,
      HasFDerivWithinAt (f τ) (Df τ z) (Metric.closedBall x₀ a) z)
    (α : ModelGaugeFlowODE.VariationalLocalFlowSolution f Df
      (⟨(tbase : ℝ), htbase⟩ : Icc tmin tmax) x₀ r)
    (hα : α =
      ModelGaugeFlowODE.VariationalLocalFlowSolution.ofProductStatePreservingComponentClosedBallContinuityEstimates_restrict
        (t₀ := tbase) hf_lip hDf_lip hf_bound hA_bound hD_bound
        hf_cont hDf_cont hmul htime htbase hr)
    (hsModel : s ⊆ Ioo tmin tmax)
    (hbackground : ∀ ⦃t : ℝ⦄, t ∈ s →
      CovariantDerivative.ContMDiffCovariantDerivative (realization.background t) 1)
    (hbase : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ w : TangentSpace I x,
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)) =ᶠ[
          𝓝[s] t] (fun τ : ℝ ↦ α.flow (xE, τ)))
    (hball : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ w : TangentSpace I x,
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        α.flow (xE, t) ∈ Metric.ball x₀ a)
    (Fₗ Gₗ : ι → ℝ → M → M) (U V : ℝ → ι → Set M)
    (hsource_cover : ∀ ⦃t : ℝ⦄, t ∈ Icc tmin tmax → Set.univ ⊆ ⋃ i, U t i)
    (hreadout : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ i, ∀ x : M, x ∈ U t i →
        ∀ᶠ τ in 𝓝 t,
          ∃ W : Set M, W ∈ 𝓝 x ∧
            EqOn (fun z : M ↦ (G.maps3 τ) z) (Fₗ i τ) W)
    (hdata : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ i, ∀ x : M, x ∈ U t i →
        (extChartAt I x) x ∈ Metric.ball x₀ r ∧
        (extChartAt I ((G.maps3 t) x)).target ∈
          𝓝 (α.flow (((extChartAt I x) x), t)) ∧
        ∀ᶠ τ in 𝓝 t,
          ∃ W : Set M, W ∈ 𝓝 x ∧
            EqOn (Fₗ i τ)
              (fun z : M ↦ (extChartAt I ((G.maps3 t) x)).symm
                (α.flow ((extChartAt I x) z, τ))) W)
    {tminLocal tmaxLocal : ℝ}
    (hltLocal : tminLocal < tmaxLocal)
    (hsLocal : s ⊆ Icc tminLocal tmaxLocal)
    (x₀Local : ∀ (t : ℝ), t ∈ s → ι → M → F)
    (rLocal : ∀ (t : ℝ), t ∈ s → ι → M → ℝ≥0)
    (β : ∀ (t : ℝ) (ht : t ∈ s) (i : ι) (x : M),
      ModelGaugeFlowODE.LocalFlowSolution f
        (⟨t, hsLocal ht⟩ : Icc tminLocal tmaxLocal)
        (x₀Local t ht i x) (rLocal t ht i x))
    (hlocalData : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ i,
      LocalGluingData (I := I) (M := M) 3 (Fₗ i t) (Gₗ i t) (U t i) (V t i))
    (hcontLocal : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ i, ∀ z : M, z ∈ U t i →
      ContinuousWithinAt (fun τ : ℝ ↦ Fₗ i τ z) (Icc tminLocal tmaxLocal) t)
    (hballLocal : ∀ ⦃t : ℝ⦄ (ht : t ∈ s) (i : ι) (x : M), x ∈ U t i →
      ∀ y ∈ (extChartAt I (Fₗ i t x)).target ∩
          (extChartAt I (Fₗ i t x)).symm ⁻¹'
            (V t i ∩ (extChartAt I (Fₗ i t x)).source),
        y ∈ Metric.closedBall (x₀Local t ht i x) (rLocal t ht i x))
    (hmodelLiftedEqOn : ∀ ⦃t : ℝ⦄ (ht : t ∈ s) (i : ι) (x : M),
      x ∈ U t i →
        ∀ y ∈ (extChartAt I (Fₗ i t x)).target ∩
            (extChartAt I (Fₗ i t x)).symm ⁻¹'
              (V t i ∩ (extChartAt I (Fₗ i t x)).source),
          Set.EqOn
            (fun τ : ℝ ↦
              Fₗ i τ (Gₗ i t ((extChartAt I (Fₗ i t x)).symm y)))
            (fun τ : ℝ ↦
              (extChartAt I (Fₗ i t x)).symm ((β t ht i x).flow y τ))
            (Icc tminLocal tmaxLocal))
    (hmodelTarget : ∀ ⦃t : ℝ⦄ (ht : t ∈ s) (i : ι) (x : M),
      x ∈ U t i →
        ∀ y ∈ (extChartAt I (Fₗ i t x)).target ∩
            (extChartAt I (Fₗ i t x)).symm ⁻¹'
              (V t i ∩ (extChartAt I (Fₗ i t x)).source),
          ∀ τ ∈ Icc tminLocal tmaxLocal, (β t ht i x).flow y τ ∈
            (extChartAt I (Fₗ i t x)).target)
    (hderivLocal : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ i, ∀ z : M, z ∈ U t i →
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I (Fₗ i t z)) (Fₗ i τ z))
        (Y t (Fₗ i t z)) (Icc tminLocal tmaxLocal) t)
    (hY : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ᶠ τ in 𝓝[s] t, ∀ x : M,
        Y τ ((G.maps3 τ) x) =
          intrinsicDeTurckGaugeField (I := I) (M := M)
            realization.metric realization.background τ ((G.maps3 τ) x))
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      realization.metric realization.background (Icc ivp.initialTime sol.terminalTime)
      ivp.initialTime)
    (hgauge_maps : gauge3.maps = G.maps3)
    (hchartRHS_eq_intrinsic : ∀ ⦃t : ℝ⦄,
      t ∈ Icc ivp.initialTime sol.terminalTime → ∀ x : M,
        ∀ u v : TangentSpace I x,
          A t (sol.curve t) x u v =
            intrinsicRicciDeTurckRHS (I := I) (M := M)
              realization.metric realization.background t x u v) :
    HasTimeDerivativeOn (I := I) (M := M)
      (G.maps3.pullbackMetricFamily realization.metric)
      (realization.toIntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
        gauge3) s := by
  exact
    realization.hasTimeDerivativeOn_ofProductStatePreservingComponentClosedBallContinuityEstimates_restrict_readout_mem_ball_iUnion_Icc_cover_lifted_eqOn_interior_cover_target_overlap_Ioo_gaugeCorrectedPullbackVelocity_of_chartRHS_closedBall_localGluingData_localFlowSolution_of_continuousWithinAt_of_lifted_model_eqOn_of_intrinsicDeTurckGaugeField
      (M := M) (F := F) (I := I) hcover_int G hs hsIoo
      hf_lip hDf_lip hf_bound hA_bound hD_bound hf_cont hDf_cont
      hmul htime htbase hr hder α hα hsModel
      (fun {t} ht p ↦
        intrinsicDeTurckVectorField_mdiffAt_of_contMDiffCovariantDerivative_background
          (I := I) (M := M) realization.metric realization.background t
          (hbackground ht) p)
      hbase hball Fₗ Gₗ U V hsource_cover hreadout hdata hltLocal hsLocal
      x₀Local rLocal β hlocalData hcontLocal hballLocal hmodelLiftedEqOn
      hmodelTarget hderivLocal hY gauge3 hgauge_maps hchartRHS_eq_intrinsic

/-- Levi-Civita-background specialization of
`variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_lieCorrection`.
The DeTurck-vector `MDiffAt` input is discharged by the zero-section
regularity bridge; the chart-RHS identification and the coordinate
Lie-correction identity remain explicit hypotheses. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_lieCorrection_of_isLeviCivita
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    {tmin tmax : ℝ} {τ₀ : Icc tmin tmax}
    {f : ℝ → F → F} {Df : ℝ → F → F →L[ℝ] F}
    {x₀ : F} {r : ℝ≥0}
    (α : ModelGaugeFlowODE.VariationalLocalFlowSolution f Df τ₀ x₀ r)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      realization.metric realization.background (Icc ivp.initialTime sol.terminalTime)
      ivp.initialTime)
    (hgauge_maps : gauge3.maps = G.maps3)
    (hsIcc : s ⊆ Icc ivp.initialTime sol.terminalTime)
    (hchartRHS_eq_intrinsic : ∀ ⦃t : ℝ⦄,
      t ∈ Icc ivp.initialTime sol.terminalTime → ∀ x : M,
        ∀ u v : TangentSpace I x,
          A t (sol.curve t) x u v =
            intrinsicRicciDeTurckRHS (I := I) (M := M)
              realization.metric realization.background t x u v)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) realization.metric realization.background)
    (hlieCorrection : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ u v : TangentSpace I x,
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        (let p : M := (G.maps3 t) x
         let pu : TangentSpace I p := (G.maps3 t).pushforwardTangent x u
         let pv : TangentSpace I p := (G.maps3 t).pushforwardTangent x v
         let cu : F :=
          SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p pu
         let cv : F :=
          SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p pv
         (fderivWithin ℝ
            (fun yE : F ↦
              SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
                (I := I) (M := M) realization.metric p (t, yE))
            (Set.range I) ((extChartAt I p) p))
            (X t p) cu cv +
          (realization.metric t).inner p
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p
              ((Df t (α.flow (xE, t))) cu)) pv +
          (realization.metric t).inner p pu
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p
              ((Df t (α.flow (xE, t))) cv)) =
          (realization.metric t).inner p
            (((chosenLeviCivitaFamily (I := I) (M := M) realization.metric) t)
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                realization.metric realization.background t) p pu) pv +
          (realization.metric t).inner p pu
            (((chosenLeviCivitaFamily (I := I) (M := M) realization.metric) t)
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                realization.metric realization.background t) p pv))) :
    ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ u v : TangentSpace I x,
      ∀ (i : κ) (K : TopologicalSpace.Compacts M)
        (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
        (hK_sub_target : (K : Set M) ⊆
          (trivializationAt BilF
            (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            ((G.maps3 t) x)).baseSet)
        (hKmem_int : (G.maps3 t) x ∈ interior (K : Set M)),
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        (let B' : F →L[ℝ] F →L[ℝ] ℝ :=
          (targetBilinearCoordReadoutContinuousLinearMap
            (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
            (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
            ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target
            (A t (sol.curve t))
            (⟨(G.maps3 t) x, interior_subset hKmem_int⟩ : K)) +
          (fderivWithin ℝ
            (fun yE : F ↦
              SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
                (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
            (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
            (X t ((G.maps3 t) x));
        B'
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
            ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x u))
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
            ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x v)) +
          (realization.metric t).inner ((G.maps3 t) x)
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I)
              ((G.maps3 t) x)
              ((Df t (α.flow (xE, t)))
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
                  ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x u))))
            ((G.maps3 t).pushforwardTangent x v) +
          (realization.metric t).inner ((G.maps3 t) x)
            ((G.maps3 t).pushforwardTangent x u)
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I)
              ((G.maps3 t) x)
              ((Df t (α.flow (xE, t)))
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
                  ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x v)))) =
        realization.toIntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
          gauge3 t x u v) := by
  exact
    realization.variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_lieCorrection
      G α gauge3 hgauge_maps hsIcc hchartRHS_eq_intrinsic
      (fun {t} _ht p ↦
        intrinsicDeTurckVectorField_mdiffAt_of_isLeviCivita
          (I := I) (M := M) realization.metric realization.background hbackground t p)
      hlieCorrection

/-- Smooth-background specialization of
`variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_lieCorrection`.
The DeTurck-vector `MDiffAt` input is discharged from slicewise `C¹`
regularity of the background connection; the chart-RHS identification and the
coordinate Lie-correction identity remain explicit hypotheses. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_lieCorrection_of_contMDiffCovariantDerivative_background
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    {tmin tmax : ℝ} {τ₀ : Icc tmin tmax}
    {f : ℝ → F → F} {Df : ℝ → F → F →L[ℝ] F}
    {x₀ : F} {r : ℝ≥0}
    (α : ModelGaugeFlowODE.VariationalLocalFlowSolution f Df τ₀ x₀ r)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      realization.metric realization.background (Icc ivp.initialTime sol.terminalTime)
      ivp.initialTime)
    (hgauge_maps : gauge3.maps = G.maps3)
    (hsIcc : s ⊆ Icc ivp.initialTime sol.terminalTime)
    (hchartRHS_eq_intrinsic : ∀ ⦃t : ℝ⦄,
      t ∈ Icc ivp.initialTime sol.terminalTime → ∀ x : M,
        ∀ u v : TangentSpace I x,
          A t (sol.curve t) x u v =
            intrinsicRicciDeTurckRHS (I := I) (M := M)
              realization.metric realization.background t x u v)
    (hbackground : ∀ ⦃t : ℝ⦄, t ∈ s →
      CovariantDerivative.ContMDiffCovariantDerivative (realization.background t) 1)
    (hlieCorrection : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ u v : TangentSpace I x,
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        (let p : M := (G.maps3 t) x
         let pu : TangentSpace I p := (G.maps3 t).pushforwardTangent x u
         let pv : TangentSpace I p := (G.maps3 t).pushforwardTangent x v
         let cu : F :=
          SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p pu
         let cv : F :=
          SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p pv
         (fderivWithin ℝ
            (fun yE : F ↦
              SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
                (I := I) (M := M) realization.metric p (t, yE))
            (Set.range I) ((extChartAt I p) p))
            (X t p) cu cv +
          (realization.metric t).inner p
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p
              ((Df t (α.flow (xE, t))) cu)) pv +
          (realization.metric t).inner p pu
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p
              ((Df t (α.flow (xE, t))) cv)) =
          (realization.metric t).inner p
            (((chosenLeviCivitaFamily (I := I) (M := M) realization.metric) t)
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                realization.metric realization.background t) p pu) pv +
          (realization.metric t).inner p pu
            (((chosenLeviCivitaFamily (I := I) (M := M) realization.metric) t)
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                realization.metric realization.background t) p pv))) :
    ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ u v : TangentSpace I x,
      ∀ (i : κ) (K : TopologicalSpace.Compacts M)
        (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
        (hK_sub_target : (K : Set M) ⊆
          (trivializationAt BilF
            (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            ((G.maps3 t) x)).baseSet)
        (hKmem_int : (G.maps3 t) x ∈ interior (K : Set M)),
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        (let B' : F →L[ℝ] F →L[ℝ] ℝ :=
          (targetBilinearCoordReadoutContinuousLinearMap
            (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
            (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
            ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target
            (A t (sol.curve t))
            (⟨(G.maps3 t) x, interior_subset hKmem_int⟩ : K)) +
          (fderivWithin ℝ
            (fun yE : F ↦
              SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
                (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
            (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
            (X t ((G.maps3 t) x));
        B'
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
            ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x u))
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
            ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x v)) +
          (realization.metric t).inner ((G.maps3 t) x)
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I)
              ((G.maps3 t) x)
              ((Df t (α.flow (xE, t)))
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
                  ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x u))))
            ((G.maps3 t).pushforwardTangent x v) +
          (realization.metric t).inner ((G.maps3 t) x)
            ((G.maps3 t).pushforwardTangent x u)
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I)
              ((G.maps3 t) x)
              ((Df t (α.flow (xE, t)))
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I)
                  ((G.maps3 t) x) ((G.maps3 t).pushforwardTangent x v)))) =
        realization.toIntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
          gauge3 t x u v) := by
  exact
    realization.variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_lieCorrection
      G α gauge3 hgauge_maps hsIcc hchartRHS_eq_intrinsic
      (fun {t} ht p ↦
        intrinsicDeTurckVectorField_mdiffAt_of_contMDiffCovariantDerivative_background
          (I := I) (M := M) realization.metric realization.background t
          (hbackground ht) p)
      hlieCorrection

/-- Indexed readout/variational data plus the Lie-correction scalar bridge give
tensor time-regularity for the gauge-corrected DeTurck pullback velocity.

This packages the scalar
`variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_lieCorrection`
endpoint into the indexed-source-cover tensor route, leaving callers with the
readout/Picard derivative data, the chart-RHS identification, and the
pre-sign Lie-correction identity. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.hasTimeDerivativeOn_of_variationalTangentMap_readout_mem_ball_iUnion_source_hasFDerivAt_lifted_eqOn_interior_cover_target_overlap_Ioo_gaugeCorrectedPullbackVelocity_of_chartRHS_lieCorrection
    {ι : Type*}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (hcover_int : (⋃ i, interior (Kc i : Set M)) = Set.univ)
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (hs : ∀ ⦃t : ℝ⦄, t ∈ s → s ∈ 𝓝 t)
    (hsIoo : s ⊆ Ioo ivp.initialTime sol.terminalTime)
    {tmin tmax : ℝ} {τ₀ : Icc tmin tmax}
    {f : ℝ → F → F} {Df : ℝ → F → F →L[ℝ] F}
    {x₀ : F} {r : ℝ≥0}
    (α : ModelGaugeFlowODE.VariationalLocalFlowSolution f Df τ₀ x₀ r)
    (hsModel : s ⊆ Ioo tmin tmax)
    (Fₗ : ι → ℝ → M → M)
    (U : ℝ → ι → Set M)
    (hsource_cover : ∀ ⦃t : ℝ⦄, t ∈ s → Set.univ ⊆ ⋃ i, U t i)
    (hreadout : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ i, ∀ x : M, x ∈ U t i →
        ∀ᶠ τ in 𝓝 t,
          ∃ W : Set M, W ∈ 𝓝 x ∧
            EqOn (fun z : M ↦ (G.maps3 τ) z) (Fₗ i τ) W)
    (hflow_deriv : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ ⦃xE : F⦄, xE ∈ Metric.ball x₀ r →
        ∀ᶠ τ in 𝓝 t,
          HasFDerivAt (fun y : F ↦ α.flow (y, τ))
            (α.tangent xE τ) xE)
    (hdata : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ i, ∀ x : M, x ∈ U t i →
        (extChartAt I x) x ∈ Metric.ball x₀ r ∧
        (extChartAt I ((G.maps3 t) x)).target ∈
          𝓝 (α.flow (((extChartAt I x) x), t)) ∧
        ∀ᶠ τ in 𝓝 t,
          ∃ W : Set M, W ∈ 𝓝 x ∧
            EqOn (Fₗ i τ)
              (fun z : M ↦ (extChartAt I ((G.maps3 t) x)).symm
                (α.flow ((extChartAt I x) z, τ))) W)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      realization.metric realization.background (Icc ivp.initialTime sol.terminalTime)
      ivp.initialTime)
    (hgauge_maps : gauge3.maps = G.maps3)
    (hchartRHS_eq_intrinsic : ∀ ⦃t : ℝ⦄,
      t ∈ Icc ivp.initialTime sol.terminalTime → ∀ x : M,
        ∀ u v : TangentSpace I x,
          A t (sol.curve t) x u v =
            intrinsicRicciDeTurckRHS (I := I) (M := M)
              realization.metric realization.background t x u v)
    (hDeTurckVector_mdiff : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ p : M,
      MDiffAt (T%
        (intrinsicDeTurckVectorField (I := I) (M := M)
          realization.metric realization.background t)) p)
    (hlieCorrection : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ u v : TangentSpace I x,
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        (let p : M := (G.maps3 t) x
         let pu : TangentSpace I p := (G.maps3 t).pushforwardTangent x u
         let pv : TangentSpace I p := (G.maps3 t).pushforwardTangent x v
         let cu : F :=
          SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p pu
         let cv : F :=
          SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p pv
         (fderivWithin ℝ
            (fun yE : F ↦
              SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
                (I := I) (M := M) realization.metric p (t, yE))
            (Set.range I) ((extChartAt I p) p))
            (X t p) cu cv +
          (realization.metric t).inner p
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p
              ((Df t (α.flow (xE, t))) cu)) pv +
          (realization.metric t).inner p pu
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p
              ((Df t (α.flow (xE, t))) cv)) =
          (realization.metric t).inner p
            (((chosenLeviCivitaFamily (I := I) (M := M) realization.metric) t)
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                realization.metric realization.background t) p pu) pv +
          (realization.metric t).inner p pu
            (((chosenLeviCivitaFamily (I := I) (M := M) realization.metric) t)
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                realization.metric realization.background t) p pv))) :
    HasTimeDerivativeOn (I := I) (M := M)
      (G.maps3.pullbackMetricFamily realization.metric)
      (realization.toIntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
        gauge3) s := by
  have hsIcc : s ⊆ Icc ivp.initialTime sol.terminalTime := fun {t} ht =>
    Ioo_subset_Icc_self (hsIoo ht)
  have hvalue :=
    realization.variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_lieCorrection
      G α gauge3 hgauge_maps hsIcc hchartRHS_eq_intrinsic
      hDeTurckVector_mdiff hlieCorrection
  exact
    realization.hasTimeDerivativeOn_of_variationalTangentMap_readout_mem_ball_iUnion_source_hasFDerivAt_lifted_eqOn_interior_cover_target_overlap_Ioo_geometricValue
      (M := M) (F := F) (I := I) hcover_int G hs hsIoo α hsModel Fₗ U
      hsource_cover hreadout hflow_deriv hdata hvalue

/-- Smooth-background specialization of
`hasTimeDerivativeOn_of_variationalTangentMap_readout_mem_ball_iUnion_source_hasFDerivAt_lifted_eqOn_interior_cover_target_overlap_Ioo_gaugeCorrectedPullbackVelocity_of_chartRHS_lieCorrection`.
The DeTurck-vector regularity input is discharged from slicewise `C¹`
regularity of the background connection. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.hasTimeDerivativeOn_of_variationalTangentMap_readout_mem_ball_iUnion_source_hasFDerivAt_lifted_eqOn_interior_cover_target_overlap_Ioo_gaugeCorrectedPullbackVelocity_of_chartRHS_lieCorrection_of_contMDiffCovariantDerivative_background
    {ι : Type*}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (hcover_int : (⋃ i, interior (Kc i : Set M)) = Set.univ)
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (hs : ∀ ⦃t : ℝ⦄, t ∈ s → s ∈ 𝓝 t)
    (hsIoo : s ⊆ Ioo ivp.initialTime sol.terminalTime)
    {tmin tmax : ℝ} {τ₀ : Icc tmin tmax}
    {f : ℝ → F → F} {Df : ℝ → F → F →L[ℝ] F}
    {x₀ : F} {r : ℝ≥0}
    (α : ModelGaugeFlowODE.VariationalLocalFlowSolution f Df τ₀ x₀ r)
    (hsModel : s ⊆ Ioo tmin tmax)
    (Fₗ : ι → ℝ → M → M)
    (U : ℝ → ι → Set M)
    (hsource_cover : ∀ ⦃t : ℝ⦄, t ∈ s → Set.univ ⊆ ⋃ i, U t i)
    (hreadout : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ i, ∀ x : M, x ∈ U t i →
        ∀ᶠ τ in 𝓝 t,
          ∃ W : Set M, W ∈ 𝓝 x ∧
            EqOn (fun z : M ↦ (G.maps3 τ) z) (Fₗ i τ) W)
    (hflow_deriv : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ ⦃xE : F⦄, xE ∈ Metric.ball x₀ r →
        ∀ᶠ τ in 𝓝 t,
          HasFDerivAt (fun y : F ↦ α.flow (y, τ))
            (α.tangent xE τ) xE)
    (hdata : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ i, ∀ x : M, x ∈ U t i →
        (extChartAt I x) x ∈ Metric.ball x₀ r ∧
        (extChartAt I ((G.maps3 t) x)).target ∈
          𝓝 (α.flow (((extChartAt I x) x), t)) ∧
        ∀ᶠ τ in 𝓝 t,
          ∃ W : Set M, W ∈ 𝓝 x ∧
            EqOn (Fₗ i τ)
              (fun z : M ↦ (extChartAt I ((G.maps3 t) x)).symm
                (α.flow ((extChartAt I x) z, τ))) W)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      realization.metric realization.background (Icc ivp.initialTime sol.terminalTime)
      ivp.initialTime)
    (hgauge_maps : gauge3.maps = G.maps3)
    (hchartRHS_eq_intrinsic : ∀ ⦃t : ℝ⦄,
      t ∈ Icc ivp.initialTime sol.terminalTime → ∀ x : M,
        ∀ u v : TangentSpace I x,
          A t (sol.curve t) x u v =
            intrinsicRicciDeTurckRHS (I := I) (M := M)
              realization.metric realization.background t x u v)
    (hbackground : ∀ ⦃t : ℝ⦄, t ∈ s →
      CovariantDerivative.ContMDiffCovariantDerivative (realization.background t) 1)
    (hlieCorrection : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ u v : TangentSpace I x,
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        (let p : M := (G.maps3 t) x
         let pu : TangentSpace I p := (G.maps3 t).pushforwardTangent x u
         let pv : TangentSpace I p := (G.maps3 t).pushforwardTangent x v
         let cu : F :=
          SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p pu
         let cv : F :=
          SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p pv
         (fderivWithin ℝ
            (fun yE : F ↦
              SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
                (I := I) (M := M) realization.metric p (t, yE))
            (Set.range I) ((extChartAt I p) p))
            (X t p) cu cv +
          (realization.metric t).inner p
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p
              ((Df t (α.flow (xE, t))) cu)) pv +
          (realization.metric t).inner p pu
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p
              ((Df t (α.flow (xE, t))) cv)) =
          (realization.metric t).inner p
            (((chosenLeviCivitaFamily (I := I) (M := M) realization.metric) t)
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                realization.metric realization.background t) p pu) pv +
          (realization.metric t).inner p pu
            (((chosenLeviCivitaFamily (I := I) (M := M) realization.metric) t)
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                realization.metric realization.background t) p pv))) :
    HasTimeDerivativeOn (I := I) (M := M)
      (G.maps3.pullbackMetricFamily realization.metric)
      (realization.toIntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
        gauge3) s := by
  exact
    realization.hasTimeDerivativeOn_of_variationalTangentMap_readout_mem_ball_iUnion_source_hasFDerivAt_lifted_eqOn_interior_cover_target_overlap_Ioo_gaugeCorrectedPullbackVelocity_of_chartRHS_lieCorrection
      (M := M) (F := F) (I := I) hcover_int G hs hsIoo α hsModel Fₗ U
      hsource_cover hreadout hflow_deriv hdata gauge3 hgauge_maps hchartRHS_eq_intrinsic
      (fun {t} ht p ↦
        intrinsicDeTurckVectorField_mdiffAt_of_contMDiffCovariantDerivative_background
          (I := I) (M := M) realization.metric realization.background t
          (hbackground ht) p)
      hlieCorrection

/-- Closed-interval source-cover version of
`hasTimeDerivativeOn_of_variationalTangentMap_readout_mem_ball_iUnion_source_hasFDerivAt_lifted_eqOn_interior_cover_target_overlap_Ioo_gaugeCorrectedPullbackVelocity_of_chartRHS_lieCorrection`.

This matches compact Picard witnesses whose source cover is selected on the
closed model interval, while the tensor derivative is still proved on the open
active set `s`. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.hasTimeDerivativeOn_of_variationalTangentMap_readout_mem_ball_iUnion_Icc_cover_source_hasFDerivAt_lifted_eqOn_interior_cover_target_overlap_Ioo_gaugeCorrectedPullbackVelocity_of_chartRHS_lieCorrection
    {ι : Type*}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (hcover_int : (⋃ i, interior (Kc i : Set M)) = Set.univ)
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (hs : ∀ ⦃t : ℝ⦄, t ∈ s → s ∈ 𝓝 t)
    (hsIoo : s ⊆ Ioo ivp.initialTime sol.terminalTime)
    {tmin tmax : ℝ} {τ₀ : Icc tmin tmax}
    {f : ℝ → F → F} {Df : ℝ → F → F →L[ℝ] F}
    {x₀ : F} {r : ℝ≥0}
    (α : ModelGaugeFlowODE.VariationalLocalFlowSolution f Df τ₀ x₀ r)
    (hsModel : s ⊆ Ioo tmin tmax)
    (Fₗ : ι → ℝ → M → M)
    (U : ℝ → ι → Set M)
    (hsource_cover : ∀ ⦃t : ℝ⦄, t ∈ Icc tmin tmax → Set.univ ⊆ ⋃ i, U t i)
    (hreadout : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ i, ∀ x : M, x ∈ U t i →
        ∀ᶠ τ in 𝓝 t,
          ∃ W : Set M, W ∈ 𝓝 x ∧
            EqOn (fun z : M ↦ (G.maps3 τ) z) (Fₗ i τ) W)
    (hflow_deriv : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ ⦃xE : F⦄, xE ∈ Metric.ball x₀ r →
        ∀ᶠ τ in 𝓝 t,
          HasFDerivAt (fun y : F ↦ α.flow (y, τ))
            (α.tangent xE τ) xE)
    (hdata : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ i, ∀ x : M, x ∈ U t i →
        (extChartAt I x) x ∈ Metric.ball x₀ r ∧
        (extChartAt I ((G.maps3 t) x)).target ∈
          𝓝 (α.flow (((extChartAt I x) x), t)) ∧
        ∀ᶠ τ in 𝓝 t,
          ∃ W : Set M, W ∈ 𝓝 x ∧
            EqOn (Fₗ i τ)
              (fun z : M ↦ (extChartAt I ((G.maps3 t) x)).symm
                (α.flow ((extChartAt I x) z, τ))) W)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      realization.metric realization.background (Icc ivp.initialTime sol.terminalTime)
      ivp.initialTime)
    (hgauge_maps : gauge3.maps = G.maps3)
    (hchartRHS_eq_intrinsic : ∀ ⦃t : ℝ⦄,
      t ∈ Icc ivp.initialTime sol.terminalTime → ∀ x : M,
        ∀ u v : TangentSpace I x,
          A t (sol.curve t) x u v =
            intrinsicRicciDeTurckRHS (I := I) (M := M)
              realization.metric realization.background t x u v)
    (hDeTurckVector_mdiff : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ p : M,
      MDiffAt (T%
        (intrinsicDeTurckVectorField (I := I) (M := M)
          realization.metric realization.background t)) p)
    (hlieCorrection : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ u v : TangentSpace I x,
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        (let p : M := (G.maps3 t) x
         let pu : TangentSpace I p := (G.maps3 t).pushforwardTangent x u
         let pv : TangentSpace I p := (G.maps3 t).pushforwardTangent x v
         let cu : F :=
          SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p pu
         let cv : F :=
          SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p pv
         (fderivWithin ℝ
            (fun yE : F ↦
              SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
                (I := I) (M := M) realization.metric p (t, yE))
            (Set.range I) ((extChartAt I p) p))
            (X t p) cu cv +
          (realization.metric t).inner p
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p
              ((Df t (α.flow (xE, t))) cu)) pv +
          (realization.metric t).inner p pu
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p
              ((Df t (α.flow (xE, t))) cv)) =
          (realization.metric t).inner p
            (((chosenLeviCivitaFamily (I := I) (M := M) realization.metric) t)
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                realization.metric realization.background t) p pu) pv +
          (realization.metric t).inner p pu
            (((chosenLeviCivitaFamily (I := I) (M := M) realization.metric) t)
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                realization.metric realization.background t) p pv))) :
    HasTimeDerivativeOn (I := I) (M := M)
      (G.maps3.pullbackMetricFamily realization.metric)
      (realization.toIntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
        gauge3) s := by
  exact
    realization.hasTimeDerivativeOn_of_variationalTangentMap_readout_mem_ball_iUnion_source_hasFDerivAt_lifted_eqOn_interior_cover_target_overlap_Ioo_gaugeCorrectedPullbackVelocity_of_chartRHS_lieCorrection
      (M := M) (F := F) (I := I) hcover_int G hs hsIoo α hsModel Fₗ U
      (fun {t} ht ↦ hsource_cover (t := t) (Ioo_subset_Icc_self (hsModel ht)))
      hreadout hflow_deriv hdata gauge3 hgauge_maps hchartRHS_eq_intrinsic
      hDeTurckVector_mdiff hlieCorrection

/-- Smooth-background specialization of the closed-interval source-cover
Lie-correction tensor route. The only removed hypothesis is the explicit
DeTurck-vector `MDiffAt` input. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.hasTimeDerivativeOn_of_variationalTangentMap_readout_mem_ball_iUnion_Icc_cover_source_hasFDerivAt_lifted_eqOn_interior_cover_target_overlap_Ioo_gaugeCorrectedPullbackVelocity_of_chartRHS_lieCorrection_of_contMDiffCovariantDerivative_background
    {ι : Type*}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (hcover_int : (⋃ i, interior (Kc i : Set M)) = Set.univ)
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (hs : ∀ ⦃t : ℝ⦄, t ∈ s → s ∈ 𝓝 t)
    (hsIoo : s ⊆ Ioo ivp.initialTime sol.terminalTime)
    {tmin tmax : ℝ} {τ₀ : Icc tmin tmax}
    {f : ℝ → F → F} {Df : ℝ → F → F →L[ℝ] F}
    {x₀ : F} {r : ℝ≥0}
    (α : ModelGaugeFlowODE.VariationalLocalFlowSolution f Df τ₀ x₀ r)
    (hsModel : s ⊆ Ioo tmin tmax)
    (Fₗ : ι → ℝ → M → M)
    (U : ℝ → ι → Set M)
    (hsource_cover : ∀ ⦃t : ℝ⦄, t ∈ Icc tmin tmax → Set.univ ⊆ ⋃ i, U t i)
    (hreadout : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ i, ∀ x : M, x ∈ U t i →
        ∀ᶠ τ in 𝓝 t,
          ∃ W : Set M, W ∈ 𝓝 x ∧
            EqOn (fun z : M ↦ (G.maps3 τ) z) (Fₗ i τ) W)
    (hflow_deriv : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ ⦃xE : F⦄, xE ∈ Metric.ball x₀ r →
        ∀ᶠ τ in 𝓝 t,
          HasFDerivAt (fun y : F ↦ α.flow (y, τ))
            (α.tangent xE τ) xE)
    (hdata : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ i, ∀ x : M, x ∈ U t i →
        (extChartAt I x) x ∈ Metric.ball x₀ r ∧
        (extChartAt I ((G.maps3 t) x)).target ∈
          𝓝 (α.flow (((extChartAt I x) x), t)) ∧
        ∀ᶠ τ in 𝓝 t,
          ∃ W : Set M, W ∈ 𝓝 x ∧
            EqOn (Fₗ i τ)
              (fun z : M ↦ (extChartAt I ((G.maps3 t) x)).symm
                (α.flow ((extChartAt I x) z, τ))) W)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      realization.metric realization.background (Icc ivp.initialTime sol.terminalTime)
      ivp.initialTime)
    (hgauge_maps : gauge3.maps = G.maps3)
    (hchartRHS_eq_intrinsic : ∀ ⦃t : ℝ⦄,
      t ∈ Icc ivp.initialTime sol.terminalTime → ∀ x : M,
        ∀ u v : TangentSpace I x,
          A t (sol.curve t) x u v =
            intrinsicRicciDeTurckRHS (I := I) (M := M)
              realization.metric realization.background t x u v)
    (hbackground : ∀ ⦃t : ℝ⦄, t ∈ s →
      CovariantDerivative.ContMDiffCovariantDerivative (realization.background t) 1)
    (hlieCorrection : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ u v : TangentSpace I x,
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        (let p : M := (G.maps3 t) x
         let pu : TangentSpace I p := (G.maps3 t).pushforwardTangent x u
         let pv : TangentSpace I p := (G.maps3 t).pushforwardTangent x v
         let cu : F :=
          SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p pu
         let cv : F :=
          SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p pv
         (fderivWithin ℝ
            (fun yE : F ↦
              SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
                (I := I) (M := M) realization.metric p (t, yE))
            (Set.range I) ((extChartAt I p) p))
            (X t p) cu cv +
          (realization.metric t).inner p
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p
              ((Df t (α.flow (xE, t))) cu)) pv +
          (realization.metric t).inner p pu
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p
              ((Df t (α.flow (xE, t))) cv)) =
          (realization.metric t).inner p
            (((chosenLeviCivitaFamily (I := I) (M := M) realization.metric) t)
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                realization.metric realization.background t) p pu) pv +
          (realization.metric t).inner p pu
            (((chosenLeviCivitaFamily (I := I) (M := M) realization.metric) t)
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                realization.metric realization.background t) p pv))) :
    HasTimeDerivativeOn (I := I) (M := M)
      (G.maps3.pullbackMetricFamily realization.metric)
      (realization.toIntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
        gauge3) s := by
  exact
    realization.hasTimeDerivativeOn_of_variationalTangentMap_readout_mem_ball_iUnion_source_hasFDerivAt_lifted_eqOn_interior_cover_target_overlap_Ioo_gaugeCorrectedPullbackVelocity_of_chartRHS_lieCorrection_of_contMDiffCovariantDerivative_background
      (M := M) (F := F) (I := I) hcover_int G hs hsIoo α hsModel Fₗ U
      (fun {t} ht ↦ hsource_cover (t := t) (Ioo_subset_Icc_self (hsModel ht)))
      hreadout hflow_deriv hdata gauge3 hgauge_maps hchartRHS_eq_intrinsic
      hbackground hlieCorrection

/-- Smooth-realization state-preserving route from the signed spatial/tangent
DeTurck-correction identity.

This is the correction-form companion of the closed-interval Lie-correction
route below.  It lets compact selected gauge-flow callers reuse a previously
proved `-intrinsicDeTurckCorrection` scalar identity directly; the
state-preserving Picard estimates still supply the source-coordinate derivative
of the variational model flow. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.hasTimeDerivativeOn_ofProductStatePreservingComponentClosedBallContinuityEstimates_restrict_readout_mem_ball_iUnion_Icc_cover_lifted_eqOn_interior_cover_target_overlap_Ioo_gaugeCorrectedPullbackVelocity_of_chartRHS_correction
    {ι : Type*}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (hcover_int : (⋃ i, interior (Kc i : Set M)) = Set.univ)
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (hs : ∀ ⦃t : ℝ⦄, t ∈ s → s ∈ 𝓝 t)
    (hsIoo : s ⊆ Ioo ivp.initialTime sol.terminalTime)
    {tmin tmax : ℝ} {tmin0 tmax0 : ℝ} {tbase : Icc tmin0 tmax0}
    {f : ℝ → F → F} {Df : ℝ → F → F →L[ℝ] F}
    {x₀ : F} {a R Kf KD Lf BA BD r : ℝ≥0}
    (hf_lip : ∀ t ∈ Icc tmin0 tmax0,
      LipschitzOnWith Kf (f t) (Metric.closedBall x₀ a))
    (hDf_lip : ∀ t ∈ Icc tmin0 tmax0,
      LipschitzOnWith KD (Df t) (Metric.closedBall x₀ a))
    (hf_bound : ∀ t ∈ Icc tmin0 tmax0, ∀ y ∈ Metric.closedBall x₀ a,
      ‖f t y‖ ≤ Lf)
    (hA_bound : ∀ A ∈ Metric.closedBall (1 : F →L[ℝ] F) a, ‖A‖₊ ≤ BA)
    (hD_bound : ∀ t ∈ Icc tmin0 tmax0, ∀ y ∈ Metric.closedBall x₀ a,
      ‖Df t y‖₊ ≤ BD)
    (hf_cont : ∀ y ∈ Metric.closedBall x₀ a,
      ContinuousOn (fun t : ℝ => f t y) (Icc tmin0 tmax0))
    (hDf_cont : ∀ y ∈ Metric.closedBall x₀ a,
      ContinuousOn (fun t : ℝ => Df t y) (Icc tmin0 tmax0))
    (hmul : (max Lf (BD * BA)) * max (tmax0 - tbase) (tbase - tmin0) ≤ a - R)
    (htime : Icc tmin tmax ⊆ Icc tmin0 tmax0)
    (htbase : (tbase : ℝ) ∈ Icc tmin tmax)
    (hr : r ≤ R)
    (hder : ∀ τ ∈ Icc tmin0 tmax0, ∀ z ∈ Metric.closedBall x₀ a,
      HasFDerivWithinAt (f τ) (Df τ z) (Metric.closedBall x₀ a) z)
    (α : ModelGaugeFlowODE.VariationalLocalFlowSolution f Df
      (⟨(tbase : ℝ), htbase⟩ : Icc tmin tmax) x₀ r)
    (hα : α =
      ModelGaugeFlowODE.VariationalLocalFlowSolution.ofProductStatePreservingComponentClosedBallContinuityEstimates_restrict
        (t₀ := tbase) hf_lip hDf_lip hf_bound hA_bound hD_bound
        hf_cont hDf_cont hmul htime htbase hr)
    (hsModel : s ⊆ Ioo tmin tmax)
    (Fₗ : ι → ℝ → M → M)
    (U : ℝ → ι → Set M)
    (hsource_cover : ∀ ⦃t : ℝ⦄, t ∈ Icc tmin tmax → Set.univ ⊆ ⋃ i, U t i)
    (hreadout : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ i, ∀ x : M, x ∈ U t i →
        ∀ᶠ τ in 𝓝 t,
          ∃ W : Set M, W ∈ 𝓝 x ∧
            EqOn (fun z : M ↦ (G.maps3 τ) z) (Fₗ i τ) W)
    (hdata : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ i, ∀ x : M, x ∈ U t i →
        (extChartAt I x) x ∈ Metric.ball x₀ r ∧
        (extChartAt I ((G.maps3 t) x)).target ∈
          𝓝 (α.flow (((extChartAt I x) x), t)) ∧
        ∀ᶠ τ in 𝓝 t,
          ∃ W : Set M, W ∈ 𝓝 x ∧
            EqOn (Fₗ i τ)
              (fun z : M ↦ (extChartAt I ((G.maps3 t) x)).symm
                (α.flow ((extChartAt I x) z, τ))) W)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      realization.metric realization.background (Icc ivp.initialTime sol.terminalTime)
      ivp.initialTime)
    (hgauge_maps : gauge3.maps = G.maps3)
    (hchartRHS_eq_intrinsic : ∀ ⦃t : ℝ⦄,
      t ∈ Icc ivp.initialTime sol.terminalTime → ∀ x : M,
        ∀ u v : TangentSpace I x,
          A t (sol.curve t) x u v =
            intrinsicRicciDeTurckRHS (I := I) (M := M)
              realization.metric realization.background t x u v)
    (hcorrection : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ u v : TangentSpace I x,
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        (let p : M := (G.maps3 t) x
         let pu : TangentSpace I p := (G.maps3 t).pushforwardTangent x u
         let pv : TangentSpace I p := (G.maps3 t).pushforwardTangent x v
         let cu : F := SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p pu
         let cv : F := SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p pv
         (fderivWithin ℝ
            (fun yE : F ↦
              SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
                (I := I) (M := M) realization.metric p (t, yE))
            (Set.range I) ((extChartAt I p) p))
            (X t p) cu cv +
          (realization.metric t).inner p
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p
              ((Df t (α.flow (xE, t))) cu)) pv +
          (realization.metric t).inner p pu
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p
              ((Df t (α.flow (xE, t))) cv)) =
          -intrinsicDeTurckCorrection (I := I) (M := M)
            realization.metric realization.background t p pu pv)) :
    HasTimeDerivativeOn (I := I) (M := M)
      (G.maps3.pullbackMetricFamily realization.metric)
      (realization.toIntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
        gauge3) s := by
  have hflow_deriv : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ ⦃xE : F⦄, xE ∈ Metric.ball x₀ r →
        ∀ᶠ τ in 𝓝 t,
          HasFDerivAt (fun y : F ↦ α.flow (y, τ))
            (α.tangent xE τ) xE := by
    have hsource : ∀ ⦃t : ℝ⦄, t ∈ Ioo tmin tmax →
        ∀ ⦃xE : F⦄, xE ∈ Metric.ball x₀ r →
          ∀ᶠ τ in 𝓝 t,
            HasFDerivAt (fun y : F ↦ α.flow (y, τ))
              (α.tangent xE τ) xE := by
      simpa [hα] using
        (ModelGaugeFlowODE.VariationalLocalFlowSolution.ofProductStatePreservingComponentClosedBallContinuityEstimates_restrict_source_eventually_flow_timeSlice_hasFDerivAt_of_hasFDerivWithinAt_Ioo_of_le_radius
          (t₀ := tbase) hf_lip hDf_lip hf_bound hA_bound hD_bound
          hf_cont hDf_cont hmul htime htbase hr hder)
    intro t ht xE hxE
    exact hsource (hsModel ht) hxE
  have hsIcc : s ⊆ Icc ivp.initialTime sol.terminalTime := fun {t} ht =>
    Ioo_subset_Icc_self (hsIoo ht)
  have hvalue :=
    realization.variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_correction
      G α gauge3 hgauge_maps hsIcc hchartRHS_eq_intrinsic hcorrection
  exact
    realization.hasTimeDerivativeOn_of_variationalTangentMap_readout_mem_ball_iUnion_Icc_cover_source_hasFDerivAt_lifted_eqOn_interior_cover_target_overlap_Ioo_geometricValue
      (M := M) (F := F) (I := I) hcover_int G hs hsIoo α hsModel Fₗ U
      hsource_cover hreadout hflow_deriv hdata hvalue

/-- Smooth-background, closed-interval finite-cover gauge-corrected route with
the state-preserving closed-ball Picard estimates supplying the model-flow
source-coordinate derivative. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.hasTimeDerivativeOn_ofProductStatePreservingComponentClosedBallContinuityEstimates_restrict_readout_mem_ball_iUnion_Icc_cover_lifted_eqOn_interior_cover_target_overlap_Ioo_gaugeCorrectedPullbackVelocity_of_chartRHS_lieCorrection_of_contMDiffCovariantDerivative_background
    {ι : Type*}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (hcover_int : (⋃ i, interior (Kc i : Set M)) = Set.univ)
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (hs : ∀ ⦃t : ℝ⦄, t ∈ s → s ∈ 𝓝 t)
    (hsIoo : s ⊆ Ioo ivp.initialTime sol.terminalTime)
    {tmin tmax : ℝ} {tmin0 tmax0 : ℝ} {tbase : Icc tmin0 tmax0}
    {f : ℝ → F → F} {Df : ℝ → F → F →L[ℝ] F}
    {x₀ : F} {a R Kf KD Lf BA BD r : ℝ≥0}
    (hf_lip : ∀ t ∈ Icc tmin0 tmax0,
      LipschitzOnWith Kf (f t) (Metric.closedBall x₀ a))
    (hDf_lip : ∀ t ∈ Icc tmin0 tmax0,
      LipschitzOnWith KD (Df t) (Metric.closedBall x₀ a))
    (hf_bound : ∀ t ∈ Icc tmin0 tmax0, ∀ y ∈ Metric.closedBall x₀ a,
      ‖f t y‖ ≤ Lf)
    (hA_bound : ∀ A ∈ Metric.closedBall (1 : F →L[ℝ] F) a, ‖A‖₊ ≤ BA)
    (hD_bound : ∀ t ∈ Icc tmin0 tmax0, ∀ y ∈ Metric.closedBall x₀ a,
      ‖Df t y‖₊ ≤ BD)
    (hf_cont : ∀ y ∈ Metric.closedBall x₀ a,
      ContinuousOn (fun t : ℝ => f t y) (Icc tmin0 tmax0))
    (hDf_cont : ∀ y ∈ Metric.closedBall x₀ a,
      ContinuousOn (fun t : ℝ => Df t y) (Icc tmin0 tmax0))
    (hmul : (max Lf (BD * BA)) * max (tmax0 - tbase) (tbase - tmin0) ≤ a - R)
    (htime : Icc tmin tmax ⊆ Icc tmin0 tmax0)
    (htbase : (tbase : ℝ) ∈ Icc tmin tmax)
    (hr : r ≤ R)
    (hder : ∀ τ ∈ Icc tmin0 tmax0, ∀ z ∈ Metric.closedBall x₀ a,
      HasFDerivWithinAt (f τ) (Df τ z) (Metric.closedBall x₀ a) z)
    (α : ModelGaugeFlowODE.VariationalLocalFlowSolution f Df
      (⟨(tbase : ℝ), htbase⟩ : Icc tmin tmax) x₀ r)
    (hα : α =
      ModelGaugeFlowODE.VariationalLocalFlowSolution.ofProductStatePreservingComponentClosedBallContinuityEstimates_restrict
        (t₀ := tbase) hf_lip hDf_lip hf_bound hA_bound hD_bound
        hf_cont hDf_cont hmul htime htbase hr)
    (hsModel : s ⊆ Ioo tmin tmax)
    (Fₗ : ι → ℝ → M → M)
    (U : ℝ → ι → Set M)
    (hsource_cover : ∀ ⦃t : ℝ⦄, t ∈ Icc tmin tmax → Set.univ ⊆ ⋃ i, U t i)
    (hreadout : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ i, ∀ x : M, x ∈ U t i →
        ∀ᶠ τ in 𝓝 t,
          ∃ W : Set M, W ∈ 𝓝 x ∧
            EqOn (fun z : M ↦ (G.maps3 τ) z) (Fₗ i τ) W)
    (hdata : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ i, ∀ x : M, x ∈ U t i →
        (extChartAt I x) x ∈ Metric.ball x₀ r ∧
        (extChartAt I ((G.maps3 t) x)).target ∈
          𝓝 (α.flow (((extChartAt I x) x), t)) ∧
        ∀ᶠ τ in 𝓝 t,
          ∃ W : Set M, W ∈ 𝓝 x ∧
            EqOn (Fₗ i τ)
              (fun z : M ↦ (extChartAt I ((G.maps3 t) x)).symm
                (α.flow ((extChartAt I x) z, τ))) W)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      realization.metric realization.background (Icc ivp.initialTime sol.terminalTime)
      ivp.initialTime)
    (hgauge_maps : gauge3.maps = G.maps3)
    (hchartRHS_eq_intrinsic : ∀ ⦃t : ℝ⦄,
      t ∈ Icc ivp.initialTime sol.terminalTime → ∀ x : M,
        ∀ u v : TangentSpace I x,
          A t (sol.curve t) x u v =
            intrinsicRicciDeTurckRHS (I := I) (M := M)
              realization.metric realization.background t x u v)
    (hbackground : ∀ ⦃t : ℝ⦄, t ∈ s →
      CovariantDerivative.ContMDiffCovariantDerivative (realization.background t) 1)
    (hlieCorrection : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ u v : TangentSpace I x,
      ∀ xE : F, xE ∈ Metric.closedBall x₀ r →
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ α.tangent xE τ) →
        (let p : M := (G.maps3 t) x
         let pu : TangentSpace I p := (G.maps3 t).pushforwardTangent x u
         let pv : TangentSpace I p := (G.maps3 t).pushforwardTangent x v
         let cu : F := SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p pu
         let cv : F := SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p pv
         (fderivWithin ℝ
            (fun yE : F ↦
              SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
                (I := I) (M := M) realization.metric p (t, yE))
            (Set.range I) ((extChartAt I p) p))
            (X t p) cu cv +
          (realization.metric t).inner p
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p
              ((Df t (α.flow (xE, t))) cu)) pv +
          (realization.metric t).inner p pu
            (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p
              ((Df t (α.flow (xE, t))) cv)) =
          (realization.metric t).inner p
            (((chosenLeviCivitaFamily (I := I) (M := M) realization.metric) t)
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                realization.metric realization.background t) p pu) pv +
          (realization.metric t).inner p pu
            (((chosenLeviCivitaFamily (I := I) (M := M) realization.metric) t)
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                realization.metric realization.background t) p pv))) :
    HasTimeDerivativeOn (I := I) (M := M)
      (G.maps3.pullbackMetricFamily realization.metric)
      (realization.toIntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
        gauge3) s := by
  have hflow_deriv : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ ⦃xE : F⦄, xE ∈ Metric.ball x₀ r →
        ∀ᶠ τ in 𝓝 t,
          HasFDerivAt (fun y : F ↦ α.flow (y, τ))
            (α.tangent xE τ) xE := by
    have hsource : ∀ ⦃t : ℝ⦄, t ∈ Ioo tmin tmax →
        ∀ ⦃xE : F⦄, xE ∈ Metric.ball x₀ r →
          ∀ᶠ τ in 𝓝 t,
            HasFDerivAt (fun y : F ↦ α.flow (y, τ))
              (α.tangent xE τ) xE := by
      simpa [hα] using
        (ModelGaugeFlowODE.VariationalLocalFlowSolution.ofProductStatePreservingComponentClosedBallContinuityEstimates_restrict_source_eventually_flow_timeSlice_hasFDerivAt_of_hasFDerivWithinAt_Ioo_of_le_radius
          (t₀ := tbase) hf_lip hDf_lip hf_bound hA_bound hD_bound
          hf_cont hDf_cont hmul htime htbase hr hder)
    intro t ht xE hxE
    exact hsource (hsModel ht) hxE
  exact
    realization.hasTimeDerivativeOn_of_variationalTangentMap_readout_mem_ball_iUnion_Icc_cover_source_hasFDerivAt_lifted_eqOn_interior_cover_target_overlap_Ioo_gaugeCorrectedPullbackVelocity_of_chartRHS_lieCorrection_of_contMDiffCovariantDerivative_background
      (M := M) (F := F) (I := I) hcover_int G hs hsIoo α hsModel Fₗ U
      hsource_cover hreadout hflow_deriv hdata gauge3 hgauge_maps
      hchartRHS_eq_intrinsic hbackground hlieCorrection

/-- Interior-cover target-overlap scalar derivatives, tangent-map derivative
data, and the scalar velocity identity give tensor time-regularity for the
non-identity raw gauge pullback on any open time set inside the Banach
solution interval. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.hasTimeDerivativeOn_of_interior_cover_target_overlap_Ioo
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (hcover_int : (⋃ i, interior (Kc i : Set M)) = Set.univ)
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (hs : ∀ ⦃t : ℝ⦄, t ∈ s → s ∈ 𝓝 t)
    (hsIoo : s ⊆ Ioo ivp.initialTime sol.terminalTime)
    {gdot : MetricTensorFamily (I := I) (M := M)}
    (hA : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∃ D : F →L[ℝ] F,
        HasDerivAt
          (fun τ : ℝ ↦
            SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
              (I := I) (M := M) G.maps3 t τ x)
          (D.comp
            (SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
              (I := I) (M := M) G.maps3 t t x)) t)
    (hvalue : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M,
      ∀ u v : TangentSpace I x,
      ∀ (i : κ) (K : TopologicalSpace.Compacts M)
        (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
        (hK_sub_target : (K : Set M) ⊆
          (trivializationAt BilF
            (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            ((G.maps3 t) x)).baseSet)
        (hKmem_int : (G.maps3 t) x ∈ interior (K : Set M))
        (D : F →L[ℝ] F),
        (let B' : F →L[ℝ] F →L[ℝ] ℝ :=
          (targetBilinearCoordReadoutContinuousLinearMap
            (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
            (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
            ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target
            (A t (sol.curve t))
            (⟨(G.maps3 t) x, interior_subset hKmem_int⟩ : K)) +
          (fderivWithin ℝ
            (fun yE : F ↦
              SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
                (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
            (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
            (X t ((G.maps3 t) x));
        B'
          (SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t t x
            (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) x u))
          (SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) G.maps3 t t x
            (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) x v)) +
          SmoothSelfDiffeomorph3Family.pullbackMetricBilinearCoordinateMap
            (I := I) (M := M) G.maps3 realization.metric t t x
            (D (SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
              (I := I) (M := M) G.maps3 t t x
              (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) x u)))
            (SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
              (I := I) (M := M) G.maps3 t t x
              (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) x v)) +
          SmoothSelfDiffeomorph3Family.pullbackMetricBilinearCoordinateMap
            (I := I) (M := M) G.maps3 realization.metric t t x
            (SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
              (I := I) (M := M) G.maps3 t t x
              (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) x u))
            (D (SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
              (I := I) (M := M) G.maps3 t t x
              (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) x v))) =
        gdot t x u v)) :
    HasTimeDerivativeOn (I := I) (M := M)
      (G.maps3.pullbackMetricFamily realization.metric) gdot s := by
  refine
    SmoothSelfDiffeomorph3Family.hasTimeDerivativeOn_of_coordinatePullbackMetricComponentDerivatives
      (I := I) (M := M)
      (realization.coordinatePullbackMetricComponentDerivativeOn_of_interior_cover_target_overlap_Ioo
        (M := M) (F := F) (I := I) hcover_int G hs hsIoo hA hvalue) ?_
  intro t ht x u v
  exact G.eventuallyEq_geometric_pullbackMetricInnerCoordinateModel
    (I := I) (M := M) (t := t) (hs ht) realization.metric x u v

/-- Right-sided raw gauge-flow metric-coordinate derivative from eventual
membership in one compact cover piece, relative to the raw time set.  The
selected compact chart curve is built internally and is made constant off the
raw time set, so only within-`s` continuity of the gauge orbit is needed. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_hasDerivWithinAt_along_gauge_eval_of_eventually_mem_Kc_Ico
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (htG : t ∈ s)
    (hs_sub : s ⊆ Ici t)
    (ht : t ∈ Ico ivp.initialTime sol.terminalTime)
    (i : κ) (x : M)
    (hcenter : x0 i = (G.maps3 t) x)
    (hmem_t : (G.maps3 t) x ∈ (Kc i : Set M))
    (hmem : ∀ᶠ τ in 𝓝[s] t, (G.maps3 τ) x ∈ (Kc i : Set M)) :
    HasDerivWithinAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric ((G.maps3 t) x)
          (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)))
      (((equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (A t (sol.curve t))).1 i
          (⟨(G.maps3 t) x, hmem_t⟩ : Kc i)) +
        (fderivWithin ℝ
          (fun yE : F ↦
            SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
              (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
          (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
          (X t ((G.maps3 t) x))) s t := by
  let y : ℝ → M := fun τ ↦ (G.maps3 τ) x
  let xK : ℝ → Kc i :=
    compactCurveOfEventuallyMemOnSet (Kc i : Set M) y s t hmem_t
  have hxK : Filter.Tendsto xK (𝓝[Ici t] t) (𝓝 (xK t)) := by
    exact compactCurveOfEventuallyMemOnSet_tendsto_Ici
      (K := (Kc i : Set M)) (y := y) (s := s) (t := t) (hy_t := hmem_t)
      htG (G.continuousWithinAt_eval htG x) hmem
  have hxK_eval : (fun τ : ℝ ↦ (xK τ).1) =ᶠ[𝓝[s] t]
      fun τ : ℝ ↦ (G.maps3 τ) x := by
    exact compactCurveOfEventuallyMemOnSet_eventually_val_eq
      (K := (Kc i : Set M)) (y := y) (s := s) (t := t) (hy_t := hmem_t) hmem
  have hmain :=
    realization.metricBilinearCoordinateField_hasDerivWithinAt_along_gauge_eval_of_coord_mem_timeSet_Ico
      (M := M) (F := F) (I := I) het G htG hs_sub ht i x hcenter hxK hxK_eval
  simpa [xK, y, compactCurveOfEventuallyMemOnSet, htG, hmem_t] using hmain

/-- Right-sided raw gauge-flow metric-coordinate derivative from membership of
the time-`t` gauge point in the interior of one compact cover piece, relative to
the raw time set.  This is the endpoint analogue of
`metricBilinearCoordinateField_hasDerivAt_along_gauge_eval_of_mem_interior_Kc_Ioo`. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_hasDerivWithinAt_along_gauge_eval_of_mem_interior_Kc_Ico
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (htG : t ∈ s)
    (hs_sub : s ⊆ Ici t)
    (ht : t ∈ Ico ivp.initialTime sol.terminalTime)
    (i : κ) (x : M)
    (hcenter : x0 i = (G.maps3 t) x)
    (hmem_int : (G.maps3 t) x ∈ interior (Kc i : Set M)) :
    HasDerivWithinAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric ((G.maps3 t) x)
          (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)))
      (((equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (A t (sol.curve t))).1 i
          (⟨(G.maps3 t) x, interior_subset hmem_int⟩ : Kc i)) +
        (fderivWithin ℝ
          (fun yE : F ↦
            SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
              (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
          (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
          (X t ((G.maps3 t) x))) s t := by
  have hmem_t : (G.maps3 t) x ∈ (Kc i : Set M) := interior_subset hmem_int
  have hmem : ∀ᶠ τ in 𝓝[s] t, (G.maps3 τ) x ∈ (Kc i : Set M) :=
    eventually_mem_of_tendsto_of_mem_interior (G.continuousWithinAt_eval htG x) hmem_int
  exact
    realization.metricBilinearCoordinateField_hasDerivWithinAt_along_gauge_eval_of_eventually_mem_Kc_Ico
      (M := M) (F := F) (I := I) het G htG hs_sub ht i x hcenter hmem_t hmem

/-- The smooth realization supplies the raw identity-gauge scalar derivative
obligation on the open Banach interval, with the Banach chart right-hand side
as the metric velocity. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.id_pullbackMetricInnerDerivativeOn_Ioo_chartRHS
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (x0 : κ → M)
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol) :
    SmoothSelfDiffeomorph3Family.PullbackMetricInnerDerivativeOn (I := I) (M := M)
      (SmoothSelfDiffeomorph3Family.id (I := I) (M := M)) realization.metric
      (fun τ x u v ↦ A τ (sol.curve τ) x u v)
      (Ioo ivp.initialTime sol.terminalTime) := by
  exact
    SmoothSelfDiffeomorph3Family.id_pullbackMetricInnerDerivativeOn
      (I := I) (M := M)
      (realization.hasTimeDerivativeOn_Ioo_chartRHS
        (M := M) (F := F) (I := I) x0 het)

/-- The tensor time-derivative form of
`id_pullbackMetricInnerDerivativeOn_Ioo_chartRHS`: the identity raw `C^3`
gauge-pullback of a smooth Banach realization is differentiated by the Banach
chart right-hand side on the open interval. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.id_pullbackMetricFamily_hasTimeDerivativeOn_Ioo_chartRHS
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (x0 : κ → M)
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol) :
    HasTimeDerivativeOn (I := I) (M := M)
      ((SmoothSelfDiffeomorph3Family.id (I := I) (M := M)).pullbackMetricFamily
        realization.metric)
      (fun τ x u v ↦ A τ (sol.curve τ) x u v)
      (Ioo ivp.initialTime sol.terminalTime) := by
  simpa [SmoothSelfDiffeomorph3Family.id_pullbackMetricFamily] using
    (realization.hasTimeDerivativeOn_Ioo_chartRHS
      (M := M) (F := F) (I := I) x0 het)

/-- Global chart closure data yields the intrinsic compact point-4 theorem package
through raw identity `C^3` gauge-flow existence and named scalar derivative data. -/
noncomputable def RicciDeTurckChartClosureData.toIntrinsicLocalExistenceUniqueness_viaRawIdentityGauge
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureData x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    IntrinsicLocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp := by
  exact
    D.toChosenIntrinsicDeTurckLocalExistenceUniqueness
      |>.toIntrinsic_viaGaugeFlowExistencePullbackMetricInnerDerivative
        (IntrinsicDeTurckGaugeFlowExistence.identityOfChosenBackground
          (E := F) (H := H) (I := I) (M := M) ivp)
        (IntrinsicDeTurckGaugeFlowExistence.identityOfChosenBackground_pullbackMetricInnerDerivativeData
          (E := F) (H := H) (I := I) (M := M) ivp)

/-- Proof-level version of
`RicciDeTurckChartClosureData.toIntrinsicLocalExistenceUniqueness_viaRawIdentityGauge`. -/
theorem RicciDeTurckChartClosureData.nonempty_intrinsicLocalExistenceUniqueness_viaRawIdentityGauge
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureData x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    Nonempty (IntrinsicLocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp) :=
  ⟨D.toIntrinsicLocalExistenceUniqueness_viaRawIdentityGauge⟩

/-- Global chart closure data yields the ordinary compact point-4 theorem package
through raw identity `C^3` gauge-flow existence and named scalar derivative data. -/
noncomputable def RicciDeTurckChartClosureData.toLocalExistenceUniqueness_viaRawIdentityGauge
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureData x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    LocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp := by
  exact
    D.toChosenIntrinsicDeTurckLocalExistenceUniqueness
      |>.toOrdinary_viaGaugeFlowExistencePullbackMetricInnerDerivative
        (IntrinsicDeTurckGaugeFlowExistence.identityOfChosenBackground
          (E := F) (H := H) (I := I) (M := M) ivp)
        (IntrinsicDeTurckGaugeFlowExistence.identityOfChosenBackground_pullbackMetricInnerDerivativeData
          (E := F) (H := H) (I := I) (M := M) ivp)

/-- Proof-level version of
`RicciDeTurckChartClosureData.toLocalExistenceUniqueness_viaRawIdentityGauge`. -/
theorem RicciDeTurckChartClosureData.nonempty_localExistenceUniqueness_viaRawIdentityGauge
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureData x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    Nonempty (LocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp) :=
  ⟨D.toLocalExistenceUniqueness_viaRawIdentityGauge⟩

/-- Global chart-closure data exposes the state-preserving Banach solution,
common-interval uniqueness, and symmetric positive-definite persistence before
passing through smooth realization or theorem-package projections. -/
theorem RicciDeTurckChartClosureData.exists_unique_banachEvolutionLocalSolutionIn
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureData x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    ∃ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover)
        ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      (∀ sol' : BanachEvolutionLocalSolutionIn chart.A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover)
          ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
        EqOn sol.curve sol'.curve
          (Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus
          (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover := by
  simpa [InitialValueProblem.toContinuousSectionSpace] using
    chart.exists_unique_symmetricPositiveDefinite
      (M := M) (F := F) (I := I)

/-- Global chart-closure data also exposes the continuous
Riemannian-metric-valued curve represented by the selected Banach solution. -/
theorem RicciDeTurckChartClosureData.exists_unique_with_continuousRiemannianMetricCurve
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureData x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    ∃ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover)
        ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      (∀ sol' : BanachEvolutionLocalSolutionIn chart.A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover)
          ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
        EqOn sol.curve sol'.curve
          (Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime))) ∧
      (∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus
          (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ∧
      ∃ G : ℝ → _root_.Bundle.ContinuousRiemannianMetric F (TangentSpace I : M → Type _),
        (∀ ⦃t : ℝ⦄, (ht : t ∈ Icc ivp.initialTime sol.terminalTime) →
          ∀ (x : M) (u v : TangentSpace I x),
            (G t).inner x u v = sol.curve t x u v) ∧
        G ivp.initialTime = ivp.initialMetric.toContinuousRiemannianMetric := by
  simpa [InitialValueProblem.toContinuousSectionSpace] using
    chart.exists_unique_with_continuousRiemannianMetricCurve
      (M := M) (F := F) (I := I)

/-- Single-choice global closure readout carrying the Banach solution,
common-interval uniqueness, symmetric positive-definite persistence, continuous
Riemannian metric curve, smooth realization, and reverse encoding. -/
theorem RicciDeTurckChartClosureData.exists_unique_with_continuousRiemannianMetricCurve_realization_candidateEncoding
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureData x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    ∃ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover)
        ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      (∀ sol' : BanachEvolutionLocalSolutionIn chart.A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover)
          ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
        EqOn sol.curve sol'.curve
          (Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime))) ∧
      (∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus
          (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ∧
      (∃ G : ℝ → _root_.Bundle.ContinuousRiemannianMetric F (TangentSpace I : M → Type _),
        (∀ ⦃t : ℝ⦄, (ht : t ∈ Icc ivp.initialTime sol.terminalTime) →
          ∀ (x : M) (u v : TangentSpace I x),
            (G t).inner x u v = sol.curve t x u v) ∧
        G ivp.initialTime = ivp.initialMetric.toContinuousRiemannianMetric) ∧
      Nonempty (Σ realization : RicciDeTurckSmoothRealizationData
          x0 et het Kc hKc Ko hKo hKoEq hcover chart sol,
        TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
          (M := M) (F := F) (I := I) chart
          (realization.toChosenIntrinsicDeTurckLocalSolution.1)) := by
  rcases D.exists_unique_with_continuousRiemannianMetricCurve
      (M := M) (F := F) (I := I) with
    ⟨sol, huniq, hspd, hcurve⟩
  exact ⟨sol, huniq, hspd, hcurve,
    ⟨⟨D.realization sol, D.realizationCandidateEncoding sol⟩⟩⟩

/-- Global closure data selects a canonical continuous Riemannian-metric curve whose
values are unique on common Banach existence intervals. -/
theorem RicciDeTurckChartClosureData.exists_unique_continuousRiemannianMetricCurve_on_common_interval
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureData x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    ∃ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover)
        ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      (∀ sol' : BanachEvolutionLocalSolutionIn chart.A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover)
          ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
        EqOn sol.curve sol'.curve
          (Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime))) ∧
      ∃ hspd : ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus
          (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover,
        ∀ (sol' : BanachEvolutionLocalSolutionIn chart.A
            (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
              et Kc hKc Ko hKo hKoEq hcover)
            ivp.initialTime
            (InitialValueProblem.toContinuousSectionSpace
              (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp))
          (hspd' : ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol'.terminalTime →
            sol'.curve t ∈ symmetricPositiveDefiniteLocus
              (M := M) (F := F) (W := (TangentSpace I : M → Type _))
              et Kc hKc Ko hKo hKoEq hcover)
          ⦃t : ℝ⦄,
          t ∈ Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime) →
          BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve
              (M := M) (F := F) (W := (TangentSpace I : M → Type _))
              et Kc hKc Ko hKo hKoEq hcover sol hspd
              ivp.initialMetric.toContinuousRiemannianMetric t =
            BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve
              (M := M) (F := F) (W := (TangentSpace I : M → Type _))
              et Kc hKc Ko hKo hKoEq hcover sol' hspd'
              ivp.initialMetric.toContinuousRiemannianMetric t := by
  rcases D.exists_unique_banachEvolutionLocalSolutionIn (M := M) (F := F) (I := I) with
    ⟨sol, huniq, hspd⟩
  refine ⟨sol, huniq, hspd, ?_⟩
  intro sol' hspd' t ht
  exact BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve_eq_on_common_interval
    (M := M) (F := F) (W := (TangentSpace I : M → Type _))
    et Kc hKc Ko hKo hKoEq hcover sol sol' (huniq sol') hspd hspd'
    ivp.initialMetric.toContinuousRiemannianMetric
    ivp.initialMetric.toContinuousRiemannianMetric ht

/-- Proof-level Banach solution existence readout from global chart-closure data. -/
theorem RicciDeTurckChartClosureData.nonempty_banachEvolutionLocalSolutionIn
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureData x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    Nonempty (BanachEvolutionLocalSolutionIn chart.A
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover)
      ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)) := by
  rcases D.exists_unique_banachEvolutionLocalSolutionIn (M := M) (F := F) (I := I) with
    ⟨sol, _huniq, _hspd⟩
  exact ⟨sol⟩

/-- Global chart-closure data pairs the smooth realization of a chosen Banach
solution with the reverse encoding of the realized chosen-background
candidate. -/
theorem RicciDeTurckChartClosureData.nonempty_realization_candidateEncoding
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureData x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    (sol : BanachEvolutionLocalSolutionIn chart.A
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)) :
    Nonempty (Σ realization : RicciDeTurckSmoothRealizationData
        x0 et het Kc hKc Ko hKo hKoEq hcover chart sol,
      TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
        (M := M) (F := F) (I := I) chart
        (realization.toChosenIntrinsicDeTurckLocalSolution.1)) :=
  ⟨⟨D.realization sol, D.realizationCandidateEncoding sol⟩⟩

/-- Proof-level paired global Banach solution, smooth realization, and reverse
encoding for the chosen-background candidate represented by that realization. -/
theorem RicciDeTurckChartClosureData.nonempty_banachEvolutionLocalSolutionIn_realization_candidateEncoding
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureData x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    Nonempty (Σ sol : BanachEvolutionLocalSolutionIn chart.A
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover)
      ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      Σ realization : RicciDeTurckSmoothRealizationData
          x0 et het Kc hKc Ko hKo hKoEq hcover chart sol,
        TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
          (M := M) (F := F) (I := I) chart
          (realization.toChosenIntrinsicDeTurckLocalSolution.1)) := by
  rcases D.nonempty_banachEvolutionLocalSolutionIn (M := M) (F := F) (I := I) with ⟨sol⟩
  exact ⟨⟨sol, D.realization sol, D.realizationCandidateEncoding sol⟩⟩

/-- Interval chart closure data yields the intrinsic compact point-4 theorem package
through raw identity `C^3` gauge-flow existence and named scalar derivative data. -/
noncomputable def RicciDeTurckChartClosureDataOnIcc.toIntrinsicLocalExistenceUniqueness_viaRawIdentityGauge
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    IntrinsicLocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp := by
  exact
    D.toChosenIntrinsicDeTurckLocalExistenceUniqueness
      |>.toIntrinsic_viaGaugeFlowExistencePullbackMetricInnerDerivative
        (IntrinsicDeTurckGaugeFlowExistence.identityOfChosenBackground
          (E := F) (H := H) (I := I) (M := M) ivp)
        (IntrinsicDeTurckGaugeFlowExistence.identityOfChosenBackground_pullbackMetricInnerDerivativeData
          (E := F) (H := H) (I := I) (M := M) ivp)

/-- Proof-level version of
`RicciDeTurckChartClosureDataOnIcc.toIntrinsicLocalExistenceUniqueness_viaRawIdentityGauge`. -/
theorem RicciDeTurckChartClosureDataOnIcc.nonempty_intrinsicLocalExistenceUniqueness_viaRawIdentityGauge
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    Nonempty (IntrinsicLocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp) :=
  ⟨D.toIntrinsicLocalExistenceUniqueness_viaRawIdentityGauge⟩

/-- Interval chart closure data yields the ordinary compact point-4 theorem package
through raw identity `C^3` gauge-flow existence and named scalar derivative data. -/
noncomputable def RicciDeTurckChartClosureDataOnIcc.toLocalExistenceUniqueness_viaRawIdentityGauge
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    LocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp := by
  exact
    D.toChosenIntrinsicDeTurckLocalExistenceUniqueness
      |>.toOrdinary_viaGaugeFlowExistencePullbackMetricInnerDerivative
        (IntrinsicDeTurckGaugeFlowExistence.identityOfChosenBackground
          (E := F) (H := H) (I := I) (M := M) ivp)
        (IntrinsicDeTurckGaugeFlowExistence.identityOfChosenBackground_pullbackMetricInnerDerivativeData
          (E := F) (H := H) (I := I) (M := M) ivp)

/-- Proof-level version of
`RicciDeTurckChartClosureDataOnIcc.toLocalExistenceUniqueness_viaRawIdentityGauge`. -/
theorem RicciDeTurckChartClosureDataOnIcc.nonempty_localExistenceUniqueness_viaRawIdentityGauge
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    Nonempty (LocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp) :=
  ⟨D.toLocalExistenceUniqueness_viaRawIdentityGauge⟩

/-- Ambient interval chart-closure data exposes the state-preserving Banach
solution and its common-interval uniqueness witness before passing through the
smooth realization or theorem-package projections. -/
theorem RicciDeTurckChartClosureDataOnIcc.exists_unique_banachEvolutionLocalSolutionIn
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    ∃ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover)
        ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      sol.terminalTime ≤ T ∧
      ∀ sol' : BanachEvolutionLocalSolutionIn chart.A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover)
          ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
        EqOn sol.curve sol'.curve
          (Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime)) := by
  exact
    exists_unique_in_positiveDefiniteLocus_of_isPicardLindelof_lipschitzOn_Icc_terminal_le
      (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      x0 et het Kc hKc Ko hKo hKoEq hcover inferInstance chart.hT chart.picard
      (by
        simpa [InitialValueProblem.toContinuousSectionSpace] using
          mem_positiveDefiniteLocus_of_continuousRiemannianMetric
            (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover
            ivp.initialMetric.toContinuousRiemannianMetric)
      chart.lipschitzOn_Icc

/-- Ambient interval chart-closure data exposes the stronger symmetric
positive-definite persistence statement for the selected Banach solution. -/
theorem RicciDeTurckChartClosureDataOnIcc.exists_unique_symmetricPositiveDefinite_banachEvolutionLocalSolutionIn
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    ∃ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover)
        ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      sol.terminalTime ≤ T ∧
      (∀ sol' : BanachEvolutionLocalSolutionIn chart.A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover)
          ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
        EqOn sol.curve sol'.curve
          (Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus
          (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover := by
  simpa [InitialValueProblem.toContinuousSectionSpace] using
    chart.exists_unique_symmetricPositiveDefinite_terminal_le
      (M := M) (F := F) (I := I)

/-- Ambient interval chart-closure data also exposes the continuous
Riemannian-metric-valued curve represented by the selected Banach solution. -/
theorem RicciDeTurckChartClosureDataOnIcc.exists_unique_with_continuousRiemannianMetricCurve_terminal_le
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    ∃ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover)
        ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      sol.terminalTime ≤ T ∧
      (∀ sol' : BanachEvolutionLocalSolutionIn chart.A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover)
          ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
        EqOn sol.curve sol'.curve
          (Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime))) ∧
      (∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus
          (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ∧
      ∃ G : ℝ → _root_.Bundle.ContinuousRiemannianMetric F (TangentSpace I : M → Type _),
        (∀ ⦃t : ℝ⦄, (ht : t ∈ Icc ivp.initialTime sol.terminalTime) →
          ∀ (x : M) (u v : TangentSpace I x),
            (G t).inner x u v = sol.curve t x u v) ∧
        G ivp.initialTime = ivp.initialMetric.toContinuousRiemannianMetric := by
  simpa [InitialValueProblem.toContinuousSectionSpace] using
    chart.exists_unique_with_continuousRiemannianMetricCurve_terminal_le
      (M := M) (F := F) (I := I)

/-- Single-choice ambient interval closure readout carrying the Banach solution,
terminal control, common-interval uniqueness, symmetric positive-definite
persistence, continuous Riemannian metric curve, smooth realization, and reverse
encoding. -/
theorem RicciDeTurckChartClosureDataOnIcc.exists_unique_with_continuousRiemannianMetricCurve_realization_candidateEncoding_terminal_le
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    ∃ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover)
        ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      sol.terminalTime ≤ T ∧
      (∀ sol' : BanachEvolutionLocalSolutionIn chart.A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover)
          ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
        EqOn sol.curve sol'.curve
          (Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime))) ∧
      (∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus
          (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ∧
      (∃ G : ℝ → _root_.Bundle.ContinuousRiemannianMetric F (TangentSpace I : M → Type _),
        (∀ ⦃t : ℝ⦄, (ht : t ∈ Icc ivp.initialTime sol.terminalTime) →
          ∀ (x : M) (u v : TangentSpace I x),
            (G t).inner x u v = sol.curve t x u v) ∧
        G ivp.initialTime = ivp.initialMetric.toContinuousRiemannianMetric) ∧
      Nonempty (Σ realization : RicciDeTurckSmoothRealizationDataOnIcc
          x0 et het Kc hKc Ko hKo hKoEq hcover chart sol,
        TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
          (M := M) (F := F) (I := I) chart
          (realization.toChosenIntrinsicDeTurckLocalSolution.1)) := by
  rcases D.exists_unique_with_continuousRiemannianMetricCurve_terminal_le
      (M := M) (F := F) (I := I) with
    ⟨sol, hterminal, huniq, hspd, hcurve⟩
  exact ⟨sol, hterminal, huniq, hspd, hcurve,
    ⟨⟨D.realization sol, D.realizationCandidateEncoding sol⟩⟩⟩

/-- Interval closure data selects a canonical continuous Riemannian-metric curve
whose values are unique on common Banach existence intervals, while retaining the
Picard terminal-time bound. -/
theorem RicciDeTurckChartClosureDataOnIcc.exists_unique_continuousRiemannianMetricCurve_on_common_interval_terminal_le
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    ∃ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover)
        ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      sol.terminalTime ≤ T ∧
      (∀ sol' : BanachEvolutionLocalSolutionIn chart.A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover)
          ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
        EqOn sol.curve sol'.curve
          (Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime))) ∧
      ∃ hspd : ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus
          (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover,
        ∀ (sol' : BanachEvolutionLocalSolutionIn chart.A
            (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
              et Kc hKc Ko hKo hKoEq hcover)
            ivp.initialTime
            (InitialValueProblem.toContinuousSectionSpace
              (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp))
          (hspd' : ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol'.terminalTime →
            sol'.curve t ∈ symmetricPositiveDefiniteLocus
              (M := M) (F := F) (W := (TangentSpace I : M → Type _))
              et Kc hKc Ko hKo hKoEq hcover)
          ⦃t : ℝ⦄,
          t ∈ Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime) →
          BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve
              (M := M) (F := F) (W := (TangentSpace I : M → Type _))
              et Kc hKc Ko hKo hKoEq hcover sol hspd
              ivp.initialMetric.toContinuousRiemannianMetric t =
            BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve
              (M := M) (F := F) (W := (TangentSpace I : M → Type _))
              et Kc hKc Ko hKo hKoEq hcover sol' hspd'
              ivp.initialMetric.toContinuousRiemannianMetric t := by
  rcases D.exists_unique_symmetricPositiveDefinite_banachEvolutionLocalSolutionIn
      (M := M) (F := F) (I := I) with
    ⟨sol, hterminal, huniq, hspd⟩
  refine ⟨sol, hterminal, huniq, hspd, ?_⟩
  intro sol' hspd' t ht
  exact BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve_eq_on_common_interval
    (M := M) (F := F) (W := (TangentSpace I : M → Type _))
    et Kc hKc Ko hKo hKoEq hcover sol sol' (huniq sol') hspd hspd'
    ivp.initialMetric.toContinuousRiemannianMetric
    ivp.initialMetric.toContinuousRiemannianMetric ht

/-- Proof-level Banach solution existence readout from ambient interval
chart-closure data. -/
theorem RicciDeTurckChartClosureDataOnIcc.nonempty_banachEvolutionLocalSolutionIn
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    Nonempty (BanachEvolutionLocalSolutionIn chart.A
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover)
      ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)) := by
  rcases D.exists_unique_banachEvolutionLocalSolutionIn (M := M) (F := F) (I := I) with
    ⟨sol, _hsolT, _huniq⟩
  exact ⟨sol⟩

/-- Ambient interval chart-closure data pairs the smooth realization of a chosen
state-preserving Banach solution with the reverse encoding of the realized
chosen-background candidate. -/
theorem RicciDeTurckChartClosureDataOnIcc.nonempty_realization_candidateEncoding
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    (sol : BanachEvolutionLocalSolutionIn chart.A
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)) :
    Nonempty (Σ realization : RicciDeTurckSmoothRealizationDataOnIcc
        x0 et het Kc hKc Ko hKo hKoEq hcover chart sol,
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
        (M := M) (F := F) (I := I) chart
        (realization.toChosenIntrinsicDeTurckLocalSolution.1)) :=
  ⟨⟨D.realization sol, D.realizationCandidateEncoding sol⟩⟩

/-- Constructive ambient interval closure readout choosing a Banach solution
together with terminal-time control, common-interval uniqueness, smooth
realization, and reverse encoding for the realized chosen-background candidate. -/
theorem RicciDeTurckChartClosureDataOnIcc.exists_unique_banachEvolutionLocalSolutionIn_realization_candidateEncoding
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    ∃ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover)
        ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      sol.terminalTime ≤ T ∧
      (∀ sol' : BanachEvolutionLocalSolutionIn chart.A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover)
          ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
        EqOn sol.curve sol'.curve
          (Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime))) ∧
      Nonempty (Σ realization : RicciDeTurckSmoothRealizationDataOnIcc
          x0 et het Kc hKc Ko hKo hKoEq hcover chart sol,
        TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
          (M := M) (F := F) (I := I) chart
          (realization.toChosenIntrinsicDeTurckLocalSolution.1)) := by
  rcases D.exists_unique_banachEvolutionLocalSolutionIn (M := M) (F := F) (I := I) with
    ⟨sol, hsolT, huniq⟩
  exact ⟨sol, hsolT, huniq, D.nonempty_realization_candidateEncoding sol⟩

/-- Proof-level symmetric-carrier interval closure data derived from ambient interval closure data
and a Picard proof on the restricted symmetric carrier. -/
theorem SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.nonempty_ofRicciDeTurckChartClosureDataOnIcc
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    (picard : IsPicardLindelof
      (chart.restrictedSymmetricA
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
      (tmin := ivp.initialTime) (tmax := T)
      ⟨ivp.initialTime, ⟨le_rfl, le_of_lt chart.hT⟩⟩
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) a 0 L Kpic) :
    Nonempty (SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
      x0 et het Kc hKc Ko hKo hKoEq hcover chart) :=
  ⟨SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.ofRicciDeTurckChartClosureDataOnIcc
    (M := M) (F := F) (I := I) (D := D) picard⟩

/-- Proof-level symmetric-carrier interval closure data after shrinking the ambient interval chart
inside the Riemannian metric cone. -/
theorem SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.nonempty_ofShrunkRicciDeTurckChartClosureDataOnIcc
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    {T' : ℝ} (hT' : ivp.initialTime < T') (hT'le : T' ≤ T)
    {a' : ℝ≥0} (ha' : a' ≤ a)
    (htime : L * max (T' - ivp.initialTime) (ivp.initialTime - ivp.initialTime) ≤
      a' - (0 : ℝ≥0))
    (hball : Metric.closedBall
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
      riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
    (hencode_terminal : ∀ candidate : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      (D.encode candidate).sol.terminalTime ≤ T') :
    Nonempty (SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
      x0 et het Kc hKc Ko hKo hKoEq hcover
      (chart.shrink (M := M) (F := F) (I := I) hT' hT'le ha' htime)) :=
  ⟨SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.ofShrunkRicciDeTurckChartClosureDataOnIcc
    (M := M) (F := F) (I := I) (D := D)
    hT' hT'le ha' htime hball hencode_terminal⟩

/-- If the current chart radius already lies in the Riemannian metric cone, the chart-derived
symmetric carrier exposes an actual state-preserving Banach solution and common-interval uniqueness
without first passing through a smaller metric-cone shrink. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_unique_restrictedSymmetricA_banachEvolutionLocalSolutionIn_of_closedBall_subset_riemannianMetricLocus
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (hball : Metric.closedBall
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a : ℝ) ⊆
      riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover) :
    ∃ sol : BanachEvolutionLocalSolutionIn
        (chart.restrictedSymmetricA
          (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
        (riemannianMetricLocusSubmodule (M := M) (F := F)
          (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
        ivp.initialTime
        (InitialValueProblem.toSymmetricSectionSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
      sol.terminalTime ≤ T ∧
      ∀ sol' : BanachEvolutionLocalSolutionIn
          (chart.restrictedSymmetricA
            (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
          (riemannianMetricLocusSubmodule (M := M) (F := F)
            (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
          ivp.initialTime
          (InitialValueProblem.toSymmetricSectionSubmodule
            (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
        EqOn sol.curve sol'.curve
          (Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime)) := by
  have hpicard :=
    chart.restrictedSymmetricA_picard_of_closedBall_subset_riemannianMetricLocus
      (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover hball
  exact
    exists_unique_in_riemannianMetricLocusSubmodule_of_isPicardLindelof_lipschitzOn_Icc_terminal_le
      (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      x0 et het Kc hKc Ko hKo hKoEq hcover inferInstance chart.hT
      hpicard
      (InitialValueProblem.toSymmetricSectionSubmodule_mem_riemannianMetricLocusSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp)
      (chart.restrictedSymmetricA_lipschitzOn_Icc
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)

/-- Proof-level Banach solution existence for the chart-derived symmetric carrier when the current
Picard ball is already contained in the Riemannian metric cone. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.nonempty_restrictedSymmetricA_banachEvolutionLocalSolutionIn_of_closedBall_subset_riemannianMetricLocus
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (hball : Metric.closedBall
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a : ℝ) ⊆
      riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover) :
    Nonempty (BanachEvolutionLocalSolutionIn
      (chart.restrictedSymmetricA
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
      (riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
      ivp.initialTime
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp)) := by
  rcases chart.exists_unique_restrictedSymmetricA_banachEvolutionLocalSolutionIn_of_closedBall_subset_riemannianMetricLocus
      (M := M) (F := F) (I := I) hball with
    ⟨sol, _hsolT, _huniq⟩
  exact ⟨sol⟩
/-- A positive-radius interval chart can be shrunk to an actual state-preserving Banach solution for
the chart-derived symmetric Riemannian-metric carrier, retaining terminal-time control and uniqueness
on common closed intervals. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_metricCone_shrunk_restrictedSymmetricA_banachEvolutionLocalSolutionIn
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (ha : 0 < a) :
    ∃ (T' : ℝ) (a' : ℝ≥0) (_hT' : ivp.initialTime < T'),
      ∃ chart' : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T' a' L Kpic Kstate,
        T' ≤ T ∧ 0 < a' ∧ a' ≤ a ∧
          Metric.closedBall
            (InitialValueProblem.toSymmetricSectionSubmodule
              (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
            riemannianMetricLocusSubmodule (M := M) (F := F)
              (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover ∧
          ∃ sol : BanachEvolutionLocalSolutionIn
              (chart'.restrictedSymmetricA
                (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
              (riemannianMetricLocusSubmodule (M := M) (F := F)
                (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
              ivp.initialTime
              (InitialValueProblem.toSymmetricSectionSubmodule
                (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
            sol.terminalTime ≤ T' ∧
            ∀ sol' : BanachEvolutionLocalSolutionIn
                (chart'.restrictedSymmetricA
                  (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
                (riemannianMetricLocusSubmodule (M := M) (F := F)
                  (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
                ivp.initialTime
                (InitialValueProblem.toSymmetricSectionSubmodule
                  (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
              EqOn sol.curve sol'.curve
                (Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime)) := by
  rcases chart.exists_metricCone_shrunk_restrictedSymmetricA_picard
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover ha with
    ⟨T', a', hT', chart', hT'le, ha'pos, ha'le, hball, hpicard⟩
  have hLip : ∀ t ∈ Icc ivp.initialTime T', LipschitzOnWith Kstate
      ((chart'.restrictedSymmetricA
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover) t)
      (riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover) :=
    chart'.restrictedSymmetricA_lipschitzOn_Icc
      (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover
  rcases
      exists_unique_in_riemannianMetricLocusSubmodule_of_isPicardLindelof_lipschitzOn_Icc_terminal_le
        (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        x0 et het Kc hKc Ko hKo hKoEq hcover inferInstance hT'
        hpicard
        (InitialValueProblem.toSymmetricSectionSubmodule_mem_riemannianMetricLocusSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp)
        hLip with
    ⟨sol, hsolT, huniq⟩
  exact ⟨T', a', hT', chart', hT'le, ha'pos, ha'le, hball, sol, hsolT, huniq⟩

/-- Proof-level existence readout for the chart-derived symmetric-carrier Banach solution produced
after the standard metric-cone shrink. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.nonempty_metricCone_shrunk_restrictedSymmetricA_banachEvolutionLocalSolutionIn
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (ha : 0 < a) :
    ∃ (T' : ℝ) (a' : ℝ≥0) (_hT' : ivp.initialTime < T'),
      ∃ chart' : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T' a' L Kpic Kstate,
        T' ≤ T ∧ 0 < a' ∧ a' ≤ a ∧
          Metric.closedBall
            (InitialValueProblem.toSymmetricSectionSubmodule
              (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
            riemannianMetricLocusSubmodule (M := M) (F := F)
              (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover ∧
          Nonempty (BanachEvolutionLocalSolutionIn
            (chart'.restrictedSymmetricA
              (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
            (riemannianMetricLocusSubmodule (M := M) (F := F)
              (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
            ivp.initialTime
            (InitialValueProblem.toSymmetricSectionSubmodule
              (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp)) := by
  rcases chart.exists_metricCone_shrunk_restrictedSymmetricA_banachEvolutionLocalSolutionIn
      (M := M) (F := F) (I := I) ha with
    ⟨T', a', hT', chart', hT'le, ha'pos, ha'le, hball, sol, _hsolT, _huniq⟩
  exact ⟨T', a', hT', chart', hT'le, ha'pos, ha'le, hball, ⟨sol⟩⟩

/-- Symmetric-carrier interval closure data exposes the state-preserving Banach solution and its
common-interval uniqueness witness before passing to intrinsic geometric theorem packages. -/
theorem SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.exists_unique_banachEvolutionLocalSolutionIn
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
      x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    ∃ sol : BanachEvolutionLocalSolutionIn
        (chart.restrictedSymmetricA
          (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
        (riemannianMetricLocusSubmodule (M := M) (F := F)
          (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
        ivp.initialTime
        (InitialValueProblem.toSymmetricSectionSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
      sol.terminalTime ≤ T ∧
      ∀ sol' : BanachEvolutionLocalSolutionIn
          (chart.restrictedSymmetricA
            (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
          (riemannianMetricLocusSubmodule (M := M) (F := F)
            (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
          ivp.initialTime
          (InitialValueProblem.toSymmetricSectionSubmodule
            (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
        EqOn sol.curve sol'.curve
          (Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime)) := by
  exact
    exists_unique_in_riemannianMetricLocusSubmodule_of_isPicardLindelof_lipschitzOn_Icc_terminal_le
      (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      x0 et het Kc hKc Ko hKo hKoEq hcover inferInstance chart.hT
      D.picard
      (InitialValueProblem.toSymmetricSectionSubmodule_mem_riemannianMetricLocusSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp)
      (chart.restrictedSymmetricA_lipschitzOn_Icc
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)

/-- Proof-level Banach solution existence readout from symmetric-carrier interval closure data. -/
theorem SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.nonempty_banachEvolutionLocalSolutionIn
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
      x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    Nonempty (BanachEvolutionLocalSolutionIn
      (chart.restrictedSymmetricA
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
      (riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
      ivp.initialTime
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp)) := by
  rcases D.exists_unique_banachEvolutionLocalSolutionIn
      (M := M) (F := F) (I := I) with
    ⟨sol, _hsolT, _huniq⟩
  exact ⟨sol⟩

/-- Proof-level smooth-realization readout from symmetric-carrier interval closure data. -/
theorem SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.nonempty_realization
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
      x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    (sol : BanachEvolutionLocalSolutionIn
      (chart.restrictedSymmetricA
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
      (riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
      ivp.initialTime
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp)) :
    Nonempty (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp
      (BanachEvolutionLocalSolutionIn.toAmbientContinuousSectionSpace_of_riemannianMetricLocusSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp
        (chart.restrictedSymmetricA_coe_of_mem
          (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover) sol)) := by
  exact ⟨D.realization sol⟩

/-- Proof-level paired Banach solution and smooth-realization readout from
symmetric-carrier interval closure data. -/
theorem SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.nonempty_banachEvolutionLocalSolutionIn_realization
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
      x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    Nonempty (Σ sol : BanachEvolutionLocalSolutionIn
      (chart.restrictedSymmetricA
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
      (riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
      ivp.initialTime
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
      BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp
        (BanachEvolutionLocalSolutionIn.toAmbientContinuousSectionSpace_of_riemannianMetricLocusSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp
          (chart.restrictedSymmetricA_coe_of_mem
            (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover) sol)) := by
  rcases D.nonempty_banachEvolutionLocalSolutionIn (M := M) (F := F) (I := I) with ⟨sol⟩
  exact ⟨⟨sol, D.realization sol⟩⟩

/-- Proof-level reverse-encoding readout from symmetric-carrier interval closure data. -/
theorem SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.nonempty_candidateEncoding
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
      x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    (candidate : ChosenIntrinsicDeTurckLocalSolution
      (E := F) (H := H) (I := I) (M := M) ivp) :
    Nonempty (SymmetricSubmoduleCandidateEncodingOnIcc
      (T := T)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      (chart.restrictedSymmetricA
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
      chart.A
      (chart.restrictedSymmetricA_coe_of_mem
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
      candidate.1) := by
  exact ⟨D.encode candidate⟩

/-- Proof-level paired Banach solution, smooth realization, and reverse encoding
for the chosen-background candidate represented by that realization. -/
theorem SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.nonempty_banachEvolutionLocalSolutionIn_realization_candidateEncoding
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
      x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    Nonempty (Σ sol : BanachEvolutionLocalSolutionIn
      (chart.restrictedSymmetricA
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
      (riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
      ivp.initialTime
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
      Σ realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp
        (BanachEvolutionLocalSolutionIn.toAmbientContinuousSectionSpace_of_riemannianMetricLocusSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp
          (chart.restrictedSymmetricA_coe_of_mem
            (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover) sol),
        SymmetricSubmoduleCandidateEncodingOnIcc
          (T := T) x0 et het Kc hKc Ko hKo hKoEq hcover
          (chart.restrictedSymmetricA
            (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
          chart.A
          (chart.restrictedSymmetricA_coe_of_mem
            (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
          (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
            (M := M) (F := F) (I := I) realization)) := by
  rcases D.nonempty_banachEvolutionLocalSolutionIn (M := M) (F := F) (I := I) with ⟨sol⟩
  let realization := D.realization sol
  let candidate : ChosenIntrinsicDeTurckLocalSolution
      (E := F) (H := H) (I := I) (M := M) ivp :=
    ⟨BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
      (M := M) (F := F) (I := I) realization, D.usesChosenBackground sol⟩
  exact ⟨⟨sol, realization, D.encode candidate⟩⟩
/-- Proof-level paired Banach solution, terminal-time control,
common-interval uniqueness, smooth realization, and reverse encoding for the
chosen-background candidate represented by that realization. -/
theorem SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.nonempty_banachEvolutionLocalSolutionIn_unique_realization_candidateEncoding
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
      x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    Nonempty (Σ sol : { sol : BanachEvolutionLocalSolutionIn
      (chart.restrictedSymmetricA
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
      (riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
      ivp.initialTime
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) //
      sol.terminalTime ≤ T ∧
      ∀ sol' : BanachEvolutionLocalSolutionIn
        (chart.restrictedSymmetricA
          (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
        (riemannianMetricLocusSubmodule (M := M) (F := F)
          (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
        ivp.initialTime
        (InitialValueProblem.toSymmetricSectionSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
      EqOn sol.curve sol'.curve
        (Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime)) },
      Sigma fun realization :
        (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp
        (BanachEvolutionLocalSolutionIn.toAmbientContinuousSectionSpace_of_riemannianMetricLocusSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp
          (chart.restrictedSymmetricA_coe_of_mem
            (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover) sol.1)) =>
        SymmetricSubmoduleCandidateEncodingOnIcc
          (T := T) x0 et het Kc hKc Ko hKo hKoEq hcover
          (chart.restrictedSymmetricA
            (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
          chart.A
          (chart.restrictedSymmetricA_coe_of_mem
            (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
          (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
            (M := M) (F := F) (I := I) realization)) := by
  rcases D.exists_unique_banachEvolutionLocalSolutionIn
      (M := M) (F := F) (I := I) with
    ⟨sol, hT, huniq⟩
  let realization := D.realization sol
  let candidate : ChosenIntrinsicDeTurckLocalSolution
      (E := F) (H := H) (I := I) (M := M) ivp :=
    ⟨BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
      (M := M) (F := F) (I := I) realization, D.usesChosenBackground sol⟩
  exact ⟨⟨⟨sol, hT, huniq⟩, realization, D.encode candidate⟩⟩
/-- Constructive readout of the strongest symmetric-carrier interval witness:
choose the Banach solution together with terminal-time control, common-interval
uniqueness, smooth realization, and reverse encoding. -/
theorem SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.exists_banachEvolutionLocalSolutionIn_unique_realization_candidateEncoding
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
      x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    ∃ sol : BanachEvolutionLocalSolutionIn
      (chart.restrictedSymmetricA
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
      (riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
      ivp.initialTime
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
      sol.terminalTime ≤ T ∧
      (∀ sol' : BanachEvolutionLocalSolutionIn
        (chart.restrictedSymmetricA
          (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
        (riemannianMetricLocusSubmodule (M := M) (F := F)
          (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
        ivp.initialTime
        (InitialValueProblem.toSymmetricSectionSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
      EqOn sol.curve sol'.curve
        (Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime))) ∧
      Nonempty (Sigma fun realization :
        (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp
        (BanachEvolutionLocalSolutionIn.toAmbientContinuousSectionSpace_of_riemannianMetricLocusSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp
          (chart.restrictedSymmetricA_coe_of_mem
            (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover) sol)) =>
        SymmetricSubmoduleCandidateEncodingOnIcc
          (T := T) x0 et het Kc hKc Ko hKo hKoEq hcover
          (chart.restrictedSymmetricA
            (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
          chart.A
          (chart.restrictedSymmetricA_coe_of_mem
            (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
          (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
            (M := M) (F := F) (I := I) realization)) := by
  rcases D.exists_unique_banachEvolutionLocalSolutionIn
      (M := M) (F := F) (I := I) with
    ⟨sol, hT, huniq⟩
  let realization := D.realization sol
  let candidate : ChosenIntrinsicDeTurckLocalSolution
      (E := F) (H := H) (I := I) (M := M) ivp :=
    ⟨BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
      (M := M) (F := F) (I := I) realization, D.usesChosenBackground sol⟩
  exact ⟨sol, hT, huniq, ⟨⟨realization, D.encode candidate⟩⟩⟩

/-- Proof-level chosen-background theorem package from symmetric-carrier interval closure data. -/
theorem SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.nonempty_chosenIntrinsicDeTurckLocalExistenceUniqueness
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
      x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    Nonempty (ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := F) (H := H) (I := I) (M := M) ivp) :=
  ⟨D.toChosenIntrinsicDeTurckLocalExistenceUniqueness⟩

/-- Proof-level intrinsic theorem package from symmetric-carrier interval closure data. -/
theorem SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.nonempty_intrinsicLocalExistenceUniqueness
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
      x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    Nonempty (IntrinsicLocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp) :=
  ⟨D.toIntrinsicLocalExistenceUniqueness⟩

/-- Proof-level ordinary theorem package from symmetric-carrier interval closure data. -/
theorem SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.nonempty_localExistenceUniqueness
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
      x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    Nonempty (LocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp) :=
  ⟨D.toLocalExistenceUniqueness⟩

/-- Ambient interval closure data yields the chosen-background, intrinsic, and
ordinary point-4 theorem packages without any terminal-fit hypothesis when the
original Picard closed ball is already contained in the Riemannian metric cone.
In this case the chart-derived symmetric carrier is built on the original
interval, so arbitrary reverse-encoded candidate intervals only need their
existing chart terminal bound. -/
theorem RicciDeTurckChartClosureDataOnIcc.nonempty_theoremPackages_of_closedBall_subset_riemannianMetricLocus
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    (hball : Metric.closedBall
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) a ⊆
      riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover) :
    Nonempty (ChosenIntrinsicDeTurckLocalExistenceUniqueness
        (E := F) (H := H) (I := I) (M := M) ivp) ∧
      Nonempty (IntrinsicLocalExistenceUniqueness
        (E := F) (H := H) (I := I) (M := M) ivp) ∧
      Nonempty (LocalExistenceUniqueness
        (E := F) (H := H) (I := I) (M := M) ivp) := by
  let Dsym : SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
      x0 et het Kc hKc Ko hKo hKoEq hcover chart :=
    SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.ofRicciDeTurckChartClosureDataOnIcc
      (M := M) (F := F) (I := I) (D := D)
      (chart.restrictedSymmetricA_picard_of_closedBall_subset_riemannianMetricLocus
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover hball)
  constructor
  · exact ⟨Dsym.toChosenIntrinsicDeTurckLocalExistenceUniqueness⟩
  constructor
  · exact ⟨Dsym.toIntrinsicLocalExistenceUniqueness⟩
  · exact ⟨Dsym.toLocalExistenceUniqueness⟩

/-- Ambient interval closure data, after the standard metric-cone shrink to the genuine symmetric
carrier, yields the chosen-background, intrinsic, and ordinary point-4 theorem packages as one
proof-level witness.  The only remaining compatibility input is that encoded candidates fit inside
the selected shrunken chart interval. -/
theorem RicciDeTurckChartClosureDataOnIcc.nonempty_theoremPackages_of_metricCone_shrunk_symmetricCarrier
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    {T' : ℝ} (hT' : ivp.initialTime < T') (hT'le : T' ≤ T)
    {a' : ℝ≥0} (ha' : a' ≤ a)
    (htime : L * max (T' - ivp.initialTime) (ivp.initialTime - ivp.initialTime) ≤
      a' - (0 : ℝ≥0))
    (hball : Metric.closedBall
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
      riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
    (hencode_terminal : ∀ candidate : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      (D.encode candidate).sol.terminalTime ≤ T') :
    Nonempty (ChosenIntrinsicDeTurckLocalExistenceUniqueness
        (E := F) (H := H) (I := I) (M := M) ivp) ∧
      Nonempty (IntrinsicLocalExistenceUniqueness
        (E := F) (H := H) (I := I) (M := M) ivp) ∧
      Nonempty (LocalExistenceUniqueness
        (E := F) (H := H) (I := I) (M := M) ivp) := by
  rcases
      SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.nonempty_ofShrunkRicciDeTurckChartClosureDataOnIcc
        (M := M) (F := F) (I := I) (D := D)
        hT' hT'le ha' htime hball hencode_terminal with
    ⟨Dsym⟩
  constructor
  · exact ⟨Dsym.toChosenIntrinsicDeTurckLocalExistenceUniqueness⟩
  constructor
  · exact ⟨Dsym.toIntrinsicLocalExistenceUniqueness⟩
  · exact ⟨Dsym.toLocalExistenceUniqueness⟩

/-- Proof-level intrinsic theorem family from symmetric-carrier interval closure data. -/
theorem nonempty_intrinsicLocalExistenceUniquenessFamily_of_symmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (D : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
        x0 et het Kc hKc Ko hKo hKoEq hcover (chart ivp)) :
    Nonempty (IntrinsicLocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M)) :=
  ⟨intrinsicLocalExistenceUniquenessFamily_of_symmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
    (M := M) (F := F) (I := I) (x0 := x0) (et := et) (het := het)
    (Kc := Kc) (hKc := hKc) (Ko := Ko) (hKo := hKo)
    (hKoEq := hKoEq) (hcover := hcover) T a L Kpic Kstate chart D⟩

/-- Proof-level ordinary theorem family from symmetric-carrier interval closure data. -/
theorem nonempty_localExistenceUniquenessFamily_of_symmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (D : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
        x0 et het Kc hKc Ko hKo hKoEq hcover (chart ivp)) :
    Nonempty (LocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M)) :=
  ⟨localExistenceUniquenessFamily_of_symmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
    (M := M) (F := F) (I := I) (x0 := x0) (et := et) (het := het)
    (Kc := Kc) (hKc := hKc) (Ko := Ko) (hKo := hKo)
    (hKoEq := hKoEq) (hcover := hcover) T a L Kpic Kstate chart D⟩

/-- Proof-level intrinsic theorem family from global chart-closure data. -/
theorem nonempty_intrinsicLocalExistenceUniquenessFamily_of_ricciDeTurckChartClosureData
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChart
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (D : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      RicciDeTurckChartClosureData x0 et het Kc hKc Ko hKo hKoEq hcover (chart ivp)) :
    Nonempty (IntrinsicLocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M)) :=
  ⟨intrinsicLocalExistenceUniquenessFamily_of_ricciDeTurckChartClosureData
    (M := M) (F := F) (I := I) (x0 := x0) (et := et) (het := het)
    (Kc := Kc) (hKc := hKc) (Ko := Ko) (hKo := hKo)
    (hKoEq := hKoEq) (hcover := hcover) T a L Kpic Kstate chart D⟩

/-- Proof-level ordinary theorem family from global chart-closure data. -/
theorem nonempty_localExistenceUniquenessFamily_of_ricciDeTurckChartClosureData
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChart
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (D : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      RicciDeTurckChartClosureData x0 et het Kc hKc Ko hKo hKoEq hcover (chart ivp)) :
    Nonempty (LocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M)) :=
  ⟨localExistenceUniquenessFamily_of_ricciDeTurckChartClosureData
    (M := M) (F := F) (I := I) (x0 := x0) (et := et) (het := het)
    (Kc := Kc) (hKc := hKc) (Ko := Ko) (hKo := hKo)
    (hKoEq := hKoEq) (hcover := hcover) T a L Kpic Kstate chart D⟩

/-- Proof-level intrinsic theorem family from interval chart-closure data. -/
theorem nonempty_intrinsicLocalExistenceUniquenessFamily_of_ricciDeTurckChartClosureDataOnIcc
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (D : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover (chart ivp)) :
    Nonempty (IntrinsicLocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M)) :=
  ⟨intrinsicLocalExistenceUniquenessFamily_of_ricciDeTurckChartClosureDataOnIcc
    (M := M) (F := F) (I := I) (x0 := x0) (et := et) (het := het)
    (Kc := Kc) (hKc := hKc) (Ko := Ko) (hKo := hKo)
    (hKoEq := hKoEq) (hcover := hcover) T a L Kpic Kstate chart D⟩

/-- Proof-level ordinary theorem family from interval chart-closure data. -/
theorem nonempty_localExistenceUniquenessFamily_of_ricciDeTurckChartClosureDataOnIcc
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (D : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover (chart ivp)) :
    Nonempty (LocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M)) :=
  ⟨localExistenceUniquenessFamily_of_ricciDeTurckChartClosureDataOnIcc
    (M := M) (F := F) (I := I) (x0 := x0) (et := et) (het := het)
    (Kc := Kc) (hKc := hKc) (Ko := Ko) (hKo := hKo)
    (hKoEq := hKoEq) (hcover := hcover) T a L Kpic Kstate chart D⟩

end GlobalClosure

end MetricLocusEvolution
end AnalyticPDE
end RicciFlow
