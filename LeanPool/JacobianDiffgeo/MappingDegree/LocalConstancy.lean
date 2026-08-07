/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

/-
Blueprint unit: mapping-degree. Local constancy of `fiberMultSum` (heart, part 2).
-/
import LeanPool.JacobianDiffgeo.MappingDegree.RootCounting
import LeanPool.JacobianDiffgeo.MappingDegree.LocalStructure
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Local constancy of `fiberMultSum` (heart, part 2)

Combines the planar count (`RootCounting.lean`) with the stack of adapted charts
(`LocalStructure.lean`) to show `fiberMultSum F` is locally constant, hence constant on the
connected `Y` — the well-definedness theorem for `degree`.

* `RS.FiberStack.sum_multiplicity_inter_source` — per-chart count: over `y ∈ S.V`, the part of
  the fiber inside the `i`-th chart source carries total multiplicity `multiplicity F (S.pt i)`
  (transported through the adapted chart bijection with the planar root set of `RootCounting`).
* `RS.FiberStack.fiberMultSum_eq_sum` — the fiber-sum is the same (`∑ i, multiplicity F (S.pt i)`)
  for every `y ∈ S.V`, via the disjoint decomposition `FiberStack.fiber_eq_iUnion`.
* `RS.isLocallyConstant_fiberMultSum` — `fiberMultSum F` is locally constant on all of `Y`.
* `RS.fiberMultSum_const` — THE well-definedness theorem: `fiberMultSum F` is the same at every
  `y : Y` (needs `[ConnectedSpace Y]`).
-/

open Filter Set Function
open scoped ContDiff Manifold Topology

namespace RS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {F : X → Y}

namespace FiberStack

variable {y₀ : Y} (S : FiberStack F y₀)

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [T2Space Y]
  [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y] in
/-- The chart bijection underlying the per-chart count: over `y ∈ S.V`, the `i`-th adapted
chart carries the part of the fiber inside its source bijectively onto the planar root set of
`ζ ^ k = e' y` (`k := multiplicity F (S.pt i)`). Private plumbing for
`sum_multiplicity_inter_source` and `fiberMultSum_eq_sum`. -/
private theorem bijOn_e {y : Y} (hy : y ∈ S.V) (i : Fin S.n) :
    Set.BijOn (S.A i).e (F ⁻¹' {y} ∩ (S.A i).e.source)
      {ζ : ℂ | ζ ^ multiplicity F (S.pt i) = (S.A i).e' y} := by
  set k := multiplicity F (S.pt i)
  set A := S.A i
  have hk0 : k ≠ 0 := S.mult_ne_zero i
  have hyA' : y ∈ A.e'.source := S.V_subset i hy
  have hw : ‖A.e' y‖ < A.radius ^ k := mem_ball_zero_iff.mp (S.map_V_mem_ball i y hy)
  refine ⟨?_, ?_, ?_⟩
  · -- MapsTo
    rintro x ⟨hx1, hx2⟩
    have hxy : F x = y := hx1
    change A.e x ^ k = A.e' y
    rw [← A.eqOn_pow x hx2, hxy]
  · -- InjOn
    exact A.e.injOn.mono Set.inter_subset_right
  · -- SurjOn
    intro ζ hζ
    have hζeq : ζ ^ k = A.e' y := hζ
    have hζlt : ‖ζ‖ < A.radius := norm_lt_of_pow_eq hk0 A.radius_pos.le hζeq hw
    have hζt : ζ ∈ A.e.target := by rw [A.target_eq]; exact mem_ball_zero_iff.mpr hζlt
    have hxs : A.e.symm ζ ∈ A.e.source := A.e.map_target hζt
    have hex : A.e (A.e.symm ζ) = ζ := A.e.right_inv hζt
    have hxe' : F (A.e.symm ζ) ∈ A.e'.source := A.mapsTo hxs
    have heq2 : A.e' (F (A.e.symm ζ)) = A.e' y := by
      rw [A.eqOn_pow _ hxs, hex, hζeq]
    have hFxy : F (A.e.symm ζ) = y := A.e'.injOn hxe' hyA' heq2
    exact ⟨A.e.symm ζ, ⟨hFxy, hxs⟩, hex⟩

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [T2Space Y] in
/-- Multiplicity transport through the adapted chart: on the `i`-th chart source, `F`'s
multiplicity at `x` is the planar vanishing order of `z ↦ z ^ k - e' y` at `e x`. Private
plumbing for `sum_multiplicity_inter_source`. -/
private theorem multiplicity_eq_analyticOrderAt (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F) {y : Y}
    (i : Fin S.n) {x : X} (hx : x ∈ F ⁻¹' {y} ∩ (S.A i).e.source) :
    multiplicity F x = (analyticOrderAt
      (fun z : ℂ ↦ z ^ multiplicity F (S.pt i) - (S.A i).e' y) ((S.A i).e x)).toNat := by
  set k := multiplicity F (S.pt i)
  set A := S.A i
  obtain ⟨hx1, hx2⟩ := hx
  have hxy : F x = y := hx1
  have hxe' : F x ∈ A.e'.source := A.mapsTo hx2
  have hinv := analyticOrderAt_charts_eq_multiplicityENat (hF x)
    A.mem_maximalAtlas hx2 A.mem_maximalAtlas' hxe'
  have hev : (fun z ↦ A.e' (F (A.e.symm z)) - A.e' (F x)) =ᶠ[𝓝 (A.e x)]
      fun z ↦ z ^ k - A.e' y := by
    filter_upwards [A.e.open_target.mem_nhds (A.e.map_source hx2)] with z hz
    rw [A.eqOn_pow _ (A.e.map_target hz), A.e.right_inv hz, hxy]
  rw [analyticOrderAt_congr hev] at hinv
  rw [multiplicity_def, ← hinv]

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [T2Space Y] in
/-- Per-chart count (heart, part 2a): over `y ∈ S.V`, the part of the fiber inside the `i`-th
chart source carries total multiplicity `multiplicity F (S.pt i)`. -/
theorem sum_multiplicity_inter_source (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F) {y : Y} (hy : y ∈ S.V)
    (i : Fin S.n) :
    ∑ᶠ x ∈ F ⁻¹' {y} ∩ (S.A i).e.source, multiplicity F x = multiplicity F (S.pt i) := by
  rw [finsum_mem_eq_of_bijOn (S.A i).e (bijOn_e S hy i)
      (g := fun ζ : ℂ ↦ (analyticOrderAt
        (fun z : ℂ ↦ z ^ multiplicity F (S.pt i) - (S.A i).e' y) ζ).toNat)
      (fun x hx ↦ multiplicity_eq_analyticOrderAt S hF i hx)]
  exact sum_toNat_analyticOrderAt_pow_sub (S.mult_ne_zero i) ((S.A i).e' y)

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [T2Space Y] in
/-- Heart, part 2b: the fiber-sum is the same (`∑ i, multiplicity F (S.pt i)`) for every
`y ∈ S.V`. -/
theorem fiberMultSum_eq_sum (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F) {y : Y} (hy : y ∈ S.V) :
    fiberMultSum F y = ∑ i, multiplicity F (S.pt i) := by
  have hfin : ∀ i : Fin S.n, (F ⁻¹' {y} ∩ (S.A i).e.source).Finite := by
    intro i
    have hbij := bijOn_e S hy i
    have ht : ({ζ : ℂ | ζ ^ multiplicity F (S.pt i) = (S.A i).e' y}).Finite :=
      setOf_pow_eq_finite (S.mult_ne_zero i) _
    have himg : ((S.A i).e '' (F ⁻¹' {y} ∩ (S.A i).e.source)).Finite := by
      rw [hbij.image_eq]; exact ht
    exact Set.Finite.of_finite_image himg hbij.injOn
  have hdisj : Pairwise (Disjoint on fun i ↦ F ⁻¹' {y} ∩ (S.A i).e.source) := fun i j hij ↦
    (S.disjoint_sources hij).mono Set.inter_subset_right Set.inter_subset_right
  rw [fiberMultSum_def, S.fiber_eq_iUnion hy, finsum_mem_iUnion hdisj hfin]
  have hsum : ∀ i : Fin S.n,
      (∑ᶠ x ∈ F ⁻¹' {y} ∩ (S.A i).e.source, multiplicity F x) = multiplicity F (S.pt i) :=
    fun i ↦ sum_multiplicity_inter_source S hF hy i
  simp_rw [hsum]
  exact finsum_eq_sum_of_fintype _

end FiberStack

/-- `fiberMultSum F` is locally constant on all of `Y` (including at branch values): at every
`y₀`, the stack's neighborhood `S.V` witnesses constancy via `fiberMultSum_eq_sum` applied twice
(at `y` and at `y₀`). -/
theorem isLocallyConstant_fiberMultSum (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hne : ¬ ∃ c, ∀ x, F x = c) : IsLocallyConstant (fiberMultSum F) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro y₀
  obtain ⟨S⟩ := exists_fiberStack hF hne y₀
  refine ⟨S.V, S.isOpen_V, S.mem_V, fun y hy ↦ ?_⟩
  rw [S.fiberMultSum_eq_sum hF hy, S.fiberMultSum_eq_sum hF S.mem_V]

/-- THE well-definedness theorem: `fiberMultSum F` takes the same value at every point of the
connected `Y`. -/
theorem fiberMultSum_const [ConnectedSpace Y] (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hne : ¬ ∃ c, ∀ x, F x = c) (y y' : Y) : fiberMultSum F y = fiberMultSum F y' :=
  (isLocallyConstant_fiberMultSum hF hne).apply_eq_of_preconnectedSpace y y'

end RS
