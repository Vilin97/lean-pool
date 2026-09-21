/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wiygul
-/

/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Claude Fable 5 (Anthropic), Claude Opus 4.7 (Anthropic)
  — at the request of David Wiygul
-/
module

public import Mathlib
import all Mathlib.Geometry.Manifold.WhitneyEmbedding

/-!
# Whitney extension along the bump-covering embedding

Let `f : SmoothBumpCovering ι I M` be a finite smooth bump covering of a compact
manifold `M` (no boundary), and `Φ = f.embPiTan : M → (ι → E × ℝ)` (this module's
public wrapper around Mathlib's `embeddingPiTangent`),
`Φ x i = (f i x • extChartAt I (c i) x, f i x)`, Mathlib's Whitney map.

**Theorem** (`SmoothBumpCovering.exists_extension`): every smooth `h : M → V`
is the restriction along `Φ` of a smooth `F : (ι → E × ℝ) → V`.

Construction (Wassermann §13, adapted to `Φ`).  Let `U i := interior {f i = 1}`;
these open sets cover `M`.  Take a smooth partition of unity `ψ` subordinate to
`U`, and for each `i` push `ψ i • h` (supported inside the chart at `c i`)
forward to a smooth `G i : E → V` with `G i (extChartAt I (c i) x) = ψ i x • h x`
on the chart source.  Let `θ : ℝ → ℝ` be smooth with `θ 1 = 1` and `θ = 0`
on `(-∞, 1/2]`.  Set
    F y := ∑ i, θ (y i).2 • G i ((y i).2⁻¹ • (y i).1).
On `M`: if `ψ i x ≠ 0` then `x ∈ U i`, so `f i x = 1`, `(Φ x) i = (φ_i x, 1)`,
and the `i`-th term is `G i (φ_i x) = ψ i x • h x`; if `ψ i x = 0` the term
vanishes either because `θ (f i x) = 0` (when `f i x ≤ 1/2`) or because
`G i (φ_i x) = ψ i x • h x = 0` (when `f i x > 1/2`, where the argument is
`φ_i x`).  Summing, `F (Φ x) = ∑ i, ψ i x • h x = h x`.

Why `[I.Boundaryless]`: `I.Boundaryless` supplies open chart targets in `E`,
which is what this extension-by-zero uses (the push-forward `G i` is
`ψ i • h ∘ (extChartAt).symm` on the chart target and `0` elsewhere;
smoothness on `E` follows because the chart target is open).  A model that
satisfies only the pointwise notion `BoundarylessManifold I M`, or a genuine
boundary, would need extra argument (e.g. a Seeley-type extension) — not
attempted here.

No compact support is claimed for `F`: the reduction to `nashTorus` cuts off
against the flat metric with a bump equal to `1` on `Φ '' univ` anyway
(the periodization step, `Compact/Periodization.lean`).

Leaves L1–L5 are self-contained; L6 is the assembly.  All six were proved by
Aristotle (project 564db993, 2026-08-30).
-/

open scoped Manifold ContDiff Topology
open Set Function

noncomputable section

namespace NashEmbedding

section Leaves

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **L1.** A smooth cutoff on `ℝ` equal to `1` at `1` and to `0` on `(-∞, 1/2]`. -/
public theorem exists_cutoff_one_half :
    ∃ θ : ℝ → ℝ, ContDiff ℝ ∞ θ ∧ θ 1 = 1 ∧ ∀ t ≤ (1 / 2 : ℝ), θ t = 0 := by
  refine ⟨fun t => Real.smoothTransition (2 * t - 1), ?_, ?_, ?_⟩
  · exact (Real.smoothTransition.contDiff (n := ⊤)).comp
      ((contDiff_id.const_smul (2 : ℝ)).sub contDiff_const)
  · norm_num [Real.smoothTransition.one]
  · intro t ht
    exact Real.smoothTransition.zero_of_nonpos (by linarith)

omit [FiniteDimensional ℝ E] in
/-- **L2.** Push-forward through a chart.  If `g : M → V` is smooth with closed
  support inside the source of the chart at `c`, and `I` has no boundary, then
  `g ∘ (extChartAt I c).symm`, extended by `0`, is a smooth function on `E`
  agreeing with `g` through the chart on the chart source. -/
public theorem exists_chart_pushforward [I.Boundaryless] (c : M) {g : M → V}
    (hg : ContMDiff I 𝓘(ℝ, V) ∞ g) (hsupp : tsupport g ⊆ (chartAt H c).source)
    (hcpt : HasCompactSupport g) :
    ∃ G : E → V, ContDiff ℝ ∞ G ∧
      ∀ x ∈ (chartAt H c).source, G (extChartAt I c x) = g x := by
  classical
  set e := extChartAt I c
  have hsrc : e.source = (chartAt H c).source := extChartAt_source (I := I) c
  have hopen : IsOpen e.target := isOpen_extChartAt_target (I := I) c
  refine ⟨fun z => if z ∈ e.target then g (e.symm z) else 0, ?_, ?_⟩
  · -- smoothness
    -- on `e.target` the function agrees with the smooth `g ∘ e.symm`
    have hsmooth : ContDiffOn ℝ ∞ (fun z => g (e.symm z)) e.target :=
      (hg.comp_contMDiffOn (contMDiffOn_extChartAt_symm (I := I) c)).contDiffOn
    -- the compact set outside which the function vanishes
    set K : Set E := e '' tsupport g
    have hKcpt : IsCompact K :=
      hcpt.image_of_continuousOn (((continuousOn_extChartAt (I := I) c)).mono
        (by rw [hsrc]; exact hsupp))
    have hKsub : K ⊆ e.target := by
      rintro _ ⟨x, hx, rfl⟩
      exact e.mapsTo (hsrc ▸ hsupp hx)
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ e.target
    · have hev : (fun z => if z ∈ e.target then g (e.symm z) else 0) =ᶠ[𝓝 z]
          fun z => g (e.symm z) := by
        filter_upwards [hopen.mem_nhds hz] with w hw using if_pos hw
      exact (hsmooth.contDiffAt (hopen.mem_nhds hz)).congr_of_eventuallyEq hev
    · have hzK : z ∈ Kᶜ := fun h => hz (hKsub h)
      have hev : (fun z => if z ∈ e.target then g (e.symm z) else 0) =ᶠ[𝓝 z]
          fun _ => (0 : V) := by
        filter_upwards [hKcpt.isClosed.isOpen_compl.mem_nhds hzK] with w hw
        by_cases hwt : w ∈ e.target
        · rw [if_pos hwt]
          by_contra hne
          exact hw ⟨e.symm w, subset_tsupport _ hne, e.right_inv hwt⟩
        · rw [if_neg hwt]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  · intro x hx
    have hxs : x ∈ e.source := hsrc ▸ hx
    simp only [if_pos (e.mapsTo hxs), e.left_inv hxs]

omit [IsManifold I ∞ M] in
/-- **L3.** For a smooth bump covering of `M`, the interiors of the sets `{f i = 1}`
  form an open cover of `M`. -/
public theorem SmoothBumpCovering.interior_eq_one_cover {ι : Type*}
    (f : SmoothBumpCovering ι I M) :
    (∀ i, IsOpen (interior {x | f i x = 1})) ∧
      (univ : Set M) ⊆ ⋃ i, interior {x | f i x = 1} := by
  refine ⟨fun i => isOpen_interior, fun x _ => ?_⟩
  obtain ⟨i, hi⟩ := f.eventuallyEq_one' x (mem_univ x)
  refine mem_iUnion.2 ⟨i, mem_interior_iff_mem_nhds.2 ?_⟩
  filter_upwards [hi] with y hy using hy

/-- **L4.** A smooth partition of unity subordinate to that cover. -/
public theorem SmoothBumpCovering.exists_partition_subordinate_interior_eq_one {ι : Type*}
    [T2Space M] [CompactSpace M] (f : SmoothBumpCovering ι I M) :
    ∃ ψ : SmoothPartitionOfUnity ι I M univ,
      ψ.IsSubordinate fun i => interior {x | f i x = 1} := by
  obtain ⟨ho, hcov⟩ := SmoothBumpCovering.interior_eq_one_cover f
  exact SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ _ ho hcov

omit [FiniteDimensional ℝ E] in
/-- **L5.** The building block `p ↦ θ p.2 • G (p.2⁻¹ • p.1)` on `E × ℝ` is smooth
  when `θ` vanishes on `(-∞, 1/2]` (so the `p.2⁻¹` singularity is never seen). -/
public theorem contDiff_cutoff_smul_rescale {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (hθ0 : ∀ t ≤ (1 / 2 : ℝ), θ t = 0) {G : E → V} (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (fun p : E × ℝ => θ p.2 • G (p.2⁻¹ • p.1)) := by
  -- Smoothness is local: the open sets `{p | p.2 < 1/2}` and `{p | 0 < p.2}` cover
  -- `E × ℝ`; on the first the function is identically `0` (as `θ p.2 = 0`), on the
  -- second both factors are smooth (`p.2⁻¹` is smooth away from `0`).
  rw [contDiff_iff_contDiffAt]
  intro p
  rcases lt_or_ge p.2 (1 / 2 : ℝ) with h | h
  · have hev : (fun p : E × ℝ => θ p.2 • G (p.2⁻¹ • p.1)) =ᶠ[𝓝 p] fun _ => (0 : V) := by
      filter_upwards [(isOpen_lt continuous_snd continuous_const).mem_nhds h] with q hq
      simp [hθ0 q.2 (le_of_lt hq)]
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hp : p.2 ≠ 0 := by
      intro h0
      rw [h0] at h
      norm_num at h
    have h1 : ContDiffAt ℝ ∞ (fun p : E × ℝ => θ p.2) p :=
      hθ.contDiffAt.comp p contDiffAt_snd
    have h2 : ContDiffAt ℝ ∞ (fun p : E × ℝ => p.2⁻¹ • p.1) p :=
      (contDiffAt_snd.inv hp).smul contDiffAt_fst
    exact h1.smul (hG.contDiffAt.comp p h2)

end Leaves

section Main

variable {ι : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Public opaque re-export of `SmoothBumpCovering.embeddingPiTangent` for legacy-file consumers
that cannot use `import all` to reach the constant, which is non-public at v4.31.0
(Mathlib PR #39886). Downstream files should use `embPiTan` and the associated
`embPiTan_*` API lemmas. -/
public noncomputable def _root_.SmoothBumpCovering.embPiTan
    [T2Space M] [Fintype ι] (f : SmoothBumpCovering ι I M) :
    C^∞⟮I, M; 𝓘(ℝ, ι → E × ℝ), ι → E × ℝ⟯ :=
  f.embeddingPiTangent

/-- Public wrapper for `SmoothBumpCovering.embeddingPiTangent_injective`. -/
public theorem _root_.SmoothBumpCovering.embPiTan_injective
    [T2Space M] [Fintype ι] (f : SmoothBumpCovering ι I M) :
    Function.Injective f.embPiTan :=
  f.embeddingPiTangent_injective

/-- Public wrapper for `SmoothBumpCovering.embeddingPiTangent_injective_mfderiv`. -/
public theorem _root_.SmoothBumpCovering.embPiTan_injective_mfderiv
    [T2Space M] [Fintype ι] (f : SmoothBumpCovering ι I M)
    (x : M) (hx : x ∈ Set.univ) :
    Function.Injective (mfderiv I 𝓘(ℝ, ι → E × ℝ) f.embPiTan x) :=
  f.embeddingPiTangent_injective_mfderiv x hx

/-- **L6 / S2 (Whitney extension).**  Every smooth `h : M → V` on a compact
  boundaryless manifold extends smoothly along the bump-covering embedding
  `Φ = f.embPiTan : M → (ι → E × ℝ)`, the public wrapper around Mathlib's
  `embeddingPiTangent`. -/
public theorem _root_.SmoothBumpCovering.exists_extension [T2Space M] [CompactSpace M] [I.Boundaryless]
    [Fintype ι] (f : SmoothBumpCovering ι I M) {h : M → V}
    (hh : ContMDiff I 𝓘(ℝ, V) ∞ h) :
    ∃ F : (ι → E × ℝ) → V, ContDiff ℝ ∞ F ∧ ∀ x, F (f.embPiTan x) = h x := by
  change ∃ F : (ι → E × ℝ) → V, ContDiff ℝ ∞ F ∧ ∀ x, F (f.embeddingPiTangent x) = h x
  -- Plan: θ from L1; ψ from L4; for each i, `g i := fun x => ψ i x • h x` is smooth
  -- with `tsupport (g i) ⊆ interior {f i = 1} ⊆ (chartAt H (f.c i)).source`
  -- (name this `hsupp i`; the second inclusion is `SmoothBumpCovering.support_subset_source`-
  -- style: `f i x = 1` forces `x ∈ (chartAt H (f.c i)).source`, see
  -- `SmoothBumpCovering.mem_chartAt_source_of_eq_one`), and `HasCompactSupport (g i)`
  -- from `CompactSpace M`; `G i` from L2; then
  --   `F y := ∑ i, θ (y i).2 • G i ((y i).2⁻¹ • (y i).1)`
  -- is smooth by L5 composed with the continuous linear projections, and
  -- `F (Φ x) = ∑ i, ψ i x • h x = h x` by the case analysis in the file header
  -- (`ψ i x ≠ 0 → f i x = 1`, `SmoothBumpCovering.embeddingPiTangent_coe`,
  -- `SmoothPartitionOfUnity.sum_eq_one`).
  classical
  obtain ⟨θ, hθ, hθ1, hθ0⟩ := exists_cutoff_one_half
  obtain ⟨ψ, hψsub⟩ := SmoothBumpCovering.exists_partition_subordinate_interior_eq_one f
  have hgs : ∀ i, ContMDiff I 𝓘(ℝ, V) ∞ fun x => ψ i x • h x := fun i =>
    (ψ i).contMDiff.smul hh
  have hone : ∀ (i : ι) (x : M), x ∈ interior {y : M | f i y = 1} → f i x = 1 := by
    intro i x hx
    have hx' : x ∈ {y : M | f i y = 1} := interior_subset hx
    simpa using hx'
  have hsupp : ∀ i, tsupport (fun x => ψ i x • h x) ⊆ (chartAt H (f.c i)).source := fun i =>
    (tsupport_smul_subset_left _ _).trans <| (hψsub i).trans fun x hx =>
      f.mem_chartAt_source_of_eq_one (hone i x hx)
  have hgc : ∀ i, HasCompactSupport fun x : M => ψ i x • h x := fun i =>
    HasCompactSupport.of_compactSpace _
  choose G hGsmooth hGeq using fun i => exists_chart_pushforward (f.c i) (hgs i) (hsupp i) (hgc i)
  refine ⟨fun y => ∑ i, θ (y i).2 • G i ((y i).2⁻¹ • (y i).1), ?_, ?_⟩
  · refine ContDiff.sum fun i _ => ?_
    exact (contDiff_cutoff_smul_rescale hθ hθ0 (hGsmooth i)).comp
      (contDiff_apply ℝ (E × ℝ) i)
  · intro x
    have hterm : ∀ i : ι,
        θ (f.embeddingPiTangent x i).2 •
            G i ((f.embeddingPiTangent x i).2⁻¹ • (f.embeddingPiTangent x i).1) =
          ψ i x • h x := by
      intro i
      simp only [SmoothBumpCovering.embeddingPiTangent_coe]
      by_cases hle : f i x ≤ 1 / 2
      · have hψ0 : ψ i x = 0 := by
          by_contra hne
          have hx1 : f i x = 1 := hone i x (hψsub i (subset_tsupport _ hne))
          rw [hx1] at hle
          norm_num at hle
        rw [hθ0 _ hle, hψ0]
        simp
      · push Not at hle
        have hne0 : f i x ≠ 0 := by
          intro h0
          rw [h0] at hle
          norm_num at hle
        have hxs : x ∈ (chartAt H (f.c i)).source :=
          (f i).support_subset_source (by simpa using hne0)
        rw [inv_smul_smul₀ hne0, hGeq i x hxs]
        by_cases hψ0 : ψ i x = 0
        · rw [hψ0]
          simp
        · have hx1 : f i x = 1 := hone i x (hψsub i (subset_tsupport _ hψ0))
          rw [hx1, hθ1, one_smul]
    calc ∑ i, θ (f.embeddingPiTangent x i).2 •
            G i ((f.embeddingPiTangent x i).2⁻¹ • (f.embeddingPiTangent x i).1)
        = ∑ i, ψ i x • h x := Finset.sum_congr rfl fun i _ => hterm i
      _ = (∑ i, ψ i x) • h x := by rw [Finset.sum_smul]
      _ = h x := by
          rw [← finsum_eq_sum_of_fintype, ψ.sum_eq_one (mem_univ x), one_smul]

end Main

end NashEmbedding

end
