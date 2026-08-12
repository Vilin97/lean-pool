/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

/-
Blueprint unit: meromorphic-trace. `Tr_F h`: the global assembly, file 5 of the design's 6-file
plan.
-/
import LeanPool.JacobianDiffgeo.MeromorphicTrace.PlanarTrace
import LeanPool.JacobianDiffgeo.MeromorphicTrace.OrderMultiplicity
import LeanPool.JacobianDiffgeo.MappingDegree.LocalStructure
import LeanPool.JacobianDiffgeo.MappingDegree.Ramification

/-!
# `Tr_F h`: the surface-level fibre trace (meromorphic-trace, cluster 2)

Unit: meromorphic-trace (`docs/design/meromorphic-trace.md` §2 D7, §4.5, §5 P7). Standing surface
hypotheses on `X`; `Y` a second Riemann surface (`[T2Space Y]`, no compactness/connectedness
needed on `Y` itself).

* `trace F h y₀` — the fibre trace of `h` along `F`, evaluated via an arbitrary `FiberStack`
  chosen (per point) by `Classical.choice`; total via an `if`-dispatch on
  `Nonempty (FiberStack F y₀)` so the *definition* carries no `ContMDiff`/nonconstancy hypothesis
  (design §5.7's "Design correction", needed because `exists_fiberStack` itself needs `hne`).
* `trace_of_forall_eq` — junk guard: `trace` vanishes identically for constant `F` (R2 resolved
  honestly below: `Nonempty (FiberStack F y₀)` is shown FALSE outright at `y₀ = c` too, via a
  short cardinality argument, not left open as the design worried it might have to be).
* **Well-definedness, resolved (design risk R1)**: `trace_eq_finsum` — at ANY point where a
  `FiberStack` exists at all, `trace F h y₀ = ∑ᶠ x ∈ F⁻¹{y₀}, h x`, the naive fibre sum,
  independent of the stack `Classical.choice` picked (no holomorphy/nonconstancy hypotheses).
  Engine: `sum_traceZk_stack`, the planar-to-fibre reindexing of the stack formula along the
  adapted-chart bijection (the `h`-weighted analogue of mapping-degree's
  `sum_multiplicity_inter_source`, via the same `BijOn`), valid over ALL of `S.V`, not just at
  `y₀`. This bypasses R1's "compare two stacks" problem exactly as this file's earlier scope
  note predicted. `trace_eq_finsum'` is the every-point version (via `exists_fiberStack`);
  `trace_eq_stack_sum` re-expresses `trace` through an ARBITRARY stack on its whole
  neighborhood `S.V` — the consumption shape `form-trace-tower`'s `resAtP1_trace_eq_sum` needs.
* `meromorphicAtX_trace` (P7, the file's centerpiece): `Tr_F h` is `MeromorphicAtX` at every
  point of `Y`, by reading `trace` through one fixed stack (`trace_eq_stack_sum`), so that in
  the target charts it is a finite sum of planar `traceZk`s (each `MeromorphicAt 0` by P5)
  composed with the maximal-atlas charts `(S.A i).e'`; CC3 chart invariance
  (`meromorphicAtX_iff_of_mem_source`) transports each summand.
* `trace_of_regular` — the design's sanity anchor: at a regular value the trace is the naive
  sum over the sheets. (Stated with the design's `IsRegularValue` hypothesis for interface
  stability, though `trace_eq_finsum'` proves the identity at every point.)
-/

open scoped ContDiff Manifold OnePoint
open Filter Set Function Topology

namespace RS.MTrace


variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {F : X → Y} {h : X → ℂ} {y₀ : Y}

open scoped Classical in
/-- The fibre trace of `h` along `F`, evaluated via an arbitrary chosen `FiberStack` at `y₀`.
Total: `0` if no stack can be witnessed at `y₀` (the only case this can happen for holomorphic
`F` is at the single value of a *constant* map, `trace_of_forall_eq`). -/
noncomputable def trace (F : X → Y) (h : X → ℂ) (y₀ : Y) : ℂ :=
  if hS : Nonempty (RS.FiberStack F y₀) then
    have S := hS.some
    ∑ i, traceZk (h ∘ (S.A i).e.symm) (RS.multiplicity F (S.pt i)) ((S.A i).e' y₀)
  else 0

open scoped Classical in
omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X] [T2Space Y]
    [IsManifold 𝓘(ℂ, ℂ) ω Y] in
theorem trace_def (F : X → Y) (h : X → ℂ) (y₀ : Y) (hS : Nonempty (RS.FiberStack F y₀)) :
    trace F h y₀ = ∑ i, traceZk (h ∘ (hS.some.A i).e.symm) (RS.multiplicity F (hS.some.pt i))
      ((hS.some.A i).e' y₀) := dite_eq_left hS

open scoped Classical in
omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X] [T2Space Y]
    [IsManifold 𝓘(ℂ, ℂ) ω Y] in
theorem trace_of_not_nonempty (hns : ¬ Nonempty (RS.FiberStack F y₀)) : trace F h y₀ = 0 :=
  dite_eq_right hns

/-- A positive-dimensional charted space over `ℂ` (in particular perfect — no isolated points,
`RS.nhdsNE_neBot`) that is `Nonempty` is infinite. -/
private theorem infinite_of_chartedSpace_complex {Z : Type*} [TopologicalSpace Z] [T1Space Z]
    [ChartedSpace ℂ Z] [Nonempty Z] : Infinite Z := by
  rw [← not_finite_iff_infinite]
  intro hfin
  have : DiscreteTopology Z := Finite.instDiscreteTopology
  have hne : (𝓝[≠] (Classical.arbitrary Z)).NeBot := RS.nhdsNE_neBot _
  have hmem : (∅ : Set Z) ∈ 𝓝[≠] (Classical.arbitrary Z) := by
    rw [mem_nhdsWithin]
    exact ⟨{Classical.arbitrary Z}, isOpen_discrete _, rfl, by simp⟩
  exact hne.ne (Filter.empty_mem_iff_bot.mp hmem)

omit [CompactSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X] [T2Space Y] [IsManifold 𝓘(ℂ, ℂ) ω Y] in
/-- Junk convention (R2, resolved): `trace` vanishes identically for constant `F`. Away from the
constant value, the fibre is empty, giving a genuine (degenerate, `n = 0`) `FiberStack` directly;
AT the constant value, `X` being infinite (`infinite_of_chartedSpace_complex`) makes
`Nonempty (FiberStack F y₀)` outright impossible (a `FiberStack`'s `pt : Fin n → X` would have to
enumerate all of `X` bijectively onto its range, impossible for infinite `X`, finite `n`). -/
theorem trace_of_forall_eq (c : Y) : trace (fun _ : X => c) h = fun _ => 0 := by
  funext y₀
  by_cases hy : y₀ = c
  · subst hy
    apply trace_of_not_nonempty
    rintro ⟨S⟩
    have hrange : Set.range S.pt = Set.univ := by
      rw [S.range_pt]; ext x; simp
    have hfin : (Set.univ : Set X).Finite := hrange ▸ Set.finite_range S.pt
    have : Infinite X := infinite_of_chartedSpace_complex (Z := X)
    exact Set.infinite_univ hfin
  · by_cases hS : Nonempty (RS.FiberStack (fun _ : X => c) y₀)
    · rw [trace_def _ _ _ hS]
      set S := hS.some with hS_def
      have hrange : Set.range S.pt = (∅ : Set X) := by
        rw [S.range_pt]
        ext x
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
        exact fun hcx => hy hcx.symm
      have h0 : IsEmpty (Fin S.n) := by
        rw [← not_nonempty_iff]
        rintro ⟨i⟩
        have hmem : S.pt i ∈ Set.range S.pt := Set.mem_range_self i
        rw [hrange] at hmem
        exact hmem
      have := h0
      simp
    · exact trace_of_not_nonempty hS

/-! ### Well-definedness: `trace` IS the naive fibre sum (design risk R1, resolved)

The engine is the adapted-chart bijection between the part of the fibre inside the `i`-th chart
source and the planar root set `{ζ | ζ ^ k = e' y}` — the same `BijOn` as mapping-degree's
(private) `FiberStack.bijOn_e` (`LocalConstancy.lean`), reproved here verbatim since it is not
exported there, then used to reindex `h`-weighted sums instead of multiplicity counts. -/

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X] [T2Space Y]
  [IsManifold 𝓘(ℂ) ω Y] in
/-- The adapted-chart bijection over `y ∈ S.V` (mapping-degree's `bijOn_e`, reproved). -/
private theorem bijOn_stack_e {y₀ : Y} (S : RS.FiberStack F y₀) {y : Y} (hy : y ∈ S.V)
    (i : Fin S.n) :
    Set.BijOn (S.A i).e (F ⁻¹' {y} ∩ (S.A i).e.source)
      {ζ : ℂ | ζ ^ RS.multiplicity F (S.pt i) = (S.A i).e' y} := by
  set k := RS.multiplicity F (S.pt i)
  set A := S.A i
  have hk0 : k ≠ 0 := S.mult_ne_zero i
  have hyA' : y ∈ A.e'.source := S.V_subset i hy
  have hw : ‖A.e' y‖ < A.radius ^ k := mem_ball_zero_iff.mp (S.map_V_mem_ball i y hy)
  refine ⟨?_, ?_, ?_⟩
  · rintro x ⟨hx1, hx2⟩
    have hxy : F x = y := hx1
    change A.e x ^ k = A.e' y
    rw [← A.eqOn_pow x hx2, hxy]
  · exact A.e.injOn.mono Set.inter_subset_right
  · intro ζ hζ
    have hζeq : ζ ^ k = A.e' y := hζ
    have hζlt : ‖ζ‖ < A.radius := RS.norm_lt_of_pow_eq hk0 A.radius_pos.le hζeq hw
    have hζt : ζ ∈ A.e.target := by rw [A.target_eq]; exact mem_ball_zero_iff.mpr hζlt
    have hxs : A.e.symm ζ ∈ A.e.source := A.e.map_target hζt
    have hex : A.e (A.e.symm ζ) = ζ := A.e.right_inv hζt
    have hxe' : F (A.e.symm ζ) ∈ A.e'.source := A.mapsTo hxs
    have heq2 : A.e' (F (A.e.symm ζ)) = A.e' y := by
      rw [A.eqOn_pow _ hxs, hex, hζeq]
    have hFxy : F (A.e.symm ζ) = y := A.e'.injOn hxe' hyA' heq2
    exact ⟨A.e.symm ζ, ⟨hFxy, hxs⟩, hex⟩

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X] [T2Space Y]
  [IsManifold 𝓘(ℂ) ω Y] in
/-- Per-chart piece: over `y ∈ S.V`, the planar `traceZk` of the chart-transported `h` at the
chart image of `y` is the naive `h`-sum over the part of the fibre inside the `i`-th chart
source (reindex along `bijOn_stack_e`). -/
private theorem traceZk_stack_piece {y₀ : Y} (S : RS.FiberStack F y₀) {y : Y} (hy : y ∈ S.V)
    (i : Fin S.n) :
    traceZk (h ∘ (S.A i).e.symm) (RS.multiplicity F (S.pt i)) ((S.A i).e' y)
      = ∑ᶠ x ∈ F ⁻¹' {y} ∩ (S.A i).e.source, h x := by
  rw [traceZk_def]
  refine (finsum_mem_eq_of_bijOn (S.A i).e (bijOn_stack_e S hy i) ?_).symm
  intro x hx
  show h x = (h ∘ (S.A i).e.symm) ((S.A i).e x)
  simp only [Function.comp_apply]
  rw [(S.A i).e.left_inv hx.2]

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X] [T2Space Y]
  [IsManifold 𝓘(ℂ) ω Y] in
/-- The stack formula computes the naive fibre sum — over ALL of `S.V`, not just at `y₀` (the
`h`-weighted analogue of mapping-degree's `FiberStack.fiberMultSum_eq_sum`). No holomorphy or
nonconstancy hypotheses: the identity is forced by the stack structure alone. -/
theorem sum_traceZk_stack {y₀ : Y} (S : RS.FiberStack F y₀) {y : Y} (hy : y ∈ S.V) :
    ∑ i, traceZk (h ∘ (S.A i).e.symm) (RS.multiplicity F (S.pt i)) ((S.A i).e' y)
      = ∑ᶠ x ∈ F ⁻¹' {y}, h x := by
  have hfin : ∀ i : Fin S.n, (F ⁻¹' {y} ∩ (S.A i).e.source).Finite := by
    intro i
    have hbij := bijOn_stack_e S hy i
    have ht : ({ζ : ℂ | ζ ^ RS.multiplicity F (S.pt i) = (S.A i).e' y}).Finite :=
      RS.setOf_pow_eq_finite (S.mult_ne_zero i) _
    have himg : ((S.A i).e '' (F ⁻¹' {y} ∩ (S.A i).e.source)).Finite := by
      rw [hbij.image_eq]; exact ht
    exact Set.Finite.of_finite_image himg hbij.injOn
  have hdisj : Pairwise (Disjoint on fun i => F ⁻¹' {y} ∩ (S.A i).e.source) := fun i j hij =>
    (S.disjoint_sources hij).mono Set.inter_subset_right Set.inter_subset_right
  calc ∑ i, traceZk (h ∘ (S.A i).e.symm) (RS.multiplicity F (S.pt i)) ((S.A i).e' y)
      = ∑ i, ∑ᶠ x ∈ F ⁻¹' {y} ∩ (S.A i).e.source, h x :=
        Finset.sum_congr rfl fun i _ => traceZk_stack_piece S hy i
    _ = ∑ᶠ i : Fin S.n, ∑ᶠ x ∈ F ⁻¹' {y} ∩ (S.A i).e.source, h x :=
        (finsum_eq_sum_of_fintype _).symm
    _ = ∑ᶠ x ∈ ⋃ i, (F ⁻¹' {y} ∩ (S.A i).e.source), h x :=
        (finsum_mem_iUnion hdisj hfin).symm
    _ = ∑ᶠ x ∈ F ⁻¹' {y}, h x := by rw [← S.fiber_eq_iUnion hy]

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X] [T2Space Y]
    [IsManifold 𝓘(ℂ, ℂ) ω Y] in
/-- **Well-definedness of `trace` (design risk R1, resolved)**: at any point where a
`FiberStack` exists at all, `trace` equals the naive fibre sum `∑ᶠ x ∈ F⁻¹{y₀}, h x` — in
particular the stack picked by `Classical.choice` in `trace`'s definition is immaterial. -/
theorem trace_eq_finsum (hS : Nonempty (RS.FiberStack F y₀)) :
    trace F h y₀ = ∑ᶠ x ∈ F ⁻¹' {y₀}, h x := by
  rw [trace_def F h y₀ hS]
  exact sum_traceZk_stack hS.some hS.some.mem_V

/-- Every-point version of `trace_eq_finsum` for holomorphic nonconstant `F` (stacks exist
everywhere, `exists_fiberStack`). -/
theorem trace_eq_finsum' (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F) (hne : ¬ ∃ c, ∀ x, F x = c) (y : Y) :
    trace F h y = ∑ᶠ x ∈ F ⁻¹' {y}, h x :=
  trace_eq_finsum (RS.exists_fiberStack hF hne y)

/-- `trace` reads through an ARBITRARY stack `S` at `y₀` on ALL of `S.V` — the consumption
shape for `form-trace-tower` (fix one stack, transport `trace` through its adapted charts near
`y₀`). -/
theorem trace_eq_stack_sum (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F) (hne : ¬ ∃ c, ∀ x, F x = c)
    {y₀ : Y} (S : RS.FiberStack F y₀) {y : Y} (hy : y ∈ S.V) :
    trace F h y = ∑ i, traceZk (h ∘ (S.A i).e.symm) (RS.multiplicity F (S.pt i))
      ((S.A i).e' y) := by
  rw [trace_eq_finsum' hF hne y, sum_traceZk_stack S hy]

/-- Sanity anchor (design §4.5): at a regular value, `trace` reduces to the naive
sum-over-the-sheets formula. The regularity hypothesis is kept for interface stability with the
design even though `trace_eq_finsum'` proves the identity at every point. -/
theorem trace_of_regular (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F) (hne : ¬ ∃ c, ∀ x, F x = c)
    {y₀ : Y} (_hy₀ : RS.IsRegularValue F y₀) :
    trace F h y₀ = ∑ᶠ x ∈ F ⁻¹' {y₀}, h x :=
  trace_eq_finsum' hF hne y₀

/-! ### Meromorphy of the trace (P7) -/

/-- **Meromorphy of the fibre trace** (P7, the design's centerpiece for this file): for
holomorphic nonconstant `F : X → Y` and `h` meromorphic everywhere on `X`, `Tr_F h` is
meromorphic at every point of `Y`. Route: fix ONE stack `S` at `y₀`; on `S.V` the trace IS the
stack formula (`trace_eq_stack_sum`), a finite sum of planar `traceZk`s — each meromorphic at
`0` by P5 (`meromorphicAt_traceZk`) — composed with the target charts `(S.A i).e'`; transport
through the charts by CC3 chart invariance (`meromorphicAtX_iff_of_mem_source`). -/
theorem meromorphicAtX_trace (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F) (hne : ¬ ∃ c, ∀ x, F x = c)
    (hh : MeromorphicOnX h Set.univ) (y₀ : Y) : MeromorphicAtX (trace F h) y₀ := by
  obtain ⟨S⟩ := RS.exists_fiberStack hF hne y₀
  -- the planar pieces are meromorphic at `0`
  have hpiece : ∀ i : Fin S.n, MeromorphicAt
      (traceZk (h ∘ (S.A i).e.symm) (RS.multiplicity F (S.pt i))) 0 := by
    intro i
    have h1 : MeromorphicAt (h ∘ (S.A i).e.symm) ((S.A i).e (S.pt i)) :=
      (RS.meromorphicAtX_iff_of_mem_source (S.A i).mem_maximalAtlas (S.mem_source_pt i)).1
        (hh (S.pt i) (Set.mem_univ _))
    rw [(S.A i).map_eq_zero] at h1
    exact meromorphicAt_traceZk h1 (S.mult_ne_zero i)
  -- each summand, as a function on `Y`, is meromorphic at `y₀`
  have hsummand : ∀ i : Fin S.n, MeromorphicAtX
      (fun y => traceZk (h ∘ (S.A i).e.symm) (RS.multiplicity F (S.pt i)) ((S.A i).e' y))
      y₀ := by
    intro i
    have hy₀src : y₀ ∈ (S.A i).e'.source := S.V_subset i S.mem_V
    have hy₀0 : (S.A i).e' y₀ = 0 := by
      have h0 : (S.A i).e' (F (S.pt i)) = 0 := (S.A i).map_eq_zero'
      rwa [S.maps_pt_eq i] at h0
    rw [RS.meromorphicAtX_iff_of_mem_source (S.A i).mem_maximalAtlas' hy₀src, hy₀0]
    have h0tgt : (0 : ℂ) ∈ (S.A i).e'.target := by
      rw [(S.A i).target_eq']
      exact Metric.mem_ball_self (pow_pos (S.A i).radius_pos _)
    have hev : ((fun y => traceZk (h ∘ (S.A i).e.symm) (RS.multiplicity F (S.pt i))
        ((S.A i).e' y)) ∘ (S.A i).e'.symm) =ᶠ[𝓝[≠] (0 : ℂ)]
        traceZk (h ∘ (S.A i).e.symm) (RS.multiplicity F (S.pt i)) := by
      have hmem : ∀ᶠ z in 𝓝 (0 : ℂ), z ∈ (S.A i).e'.target :=
        (S.A i).e'.open_target.mem_nhds h0tgt
      filter_upwards [hmem.filter_mono nhdsWithin_le_nhds] with z hz
      simp only [Function.comp_apply]
      rw [(S.A i).e'.right_inv hz]
    exact (hpiece i).congr hev.symm
  -- the finite sum is meromorphic at `y₀`, and agrees with `trace F h` near `y₀`
  have hsum : MeromorphicAtX (fun y => ∑ i, traceZk (h ∘ (S.A i).e.symm)
      (RS.multiplicity F (S.pt i)) ((S.A i).e' y)) y₀ := by
    change MeromorphicAt _ _
    exact MeromorphicAt.fun_sum fun i _ => hsummand i
  have hev : (fun y => ∑ i, traceZk (h ∘ (S.A i).e.symm) (RS.multiplicity F (S.pt i))
      ((S.A i).e' y)) =ᶠ[𝓝[≠] y₀] trace F h := by
    have hV : ∀ᶠ y in 𝓝 y₀, y ∈ S.V := S.isOpen_V.mem_nhds S.mem_V
    filter_upwards [hV.filter_mono nhdsWithin_le_nhds] with y hy
    exact (trace_eq_stack_sum hF hne S hy).symm
  exact hsum.congr hev

end RS.MTrace
