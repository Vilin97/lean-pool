/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

/-
Blueprint unit: meromorphic-trace. The `toP1` bridge: meromorphic function → holomorphic map to
`ℙ¹`, file 1 of the design's 6-file plan.
-/
import LeanPool.JacobianDiffgeo.Meromorphic.OrderEval
import LeanPool.JacobianDiffgeo.ProjectiveLine.Holomorphy

/-!
# `toP1`: the `f`-to-`ℙ¹` bridge (meromorphic-trace, cluster 1)

Unit: meromorphic-trace (`docs/design/meromorphic-trace.md` §2 D2/D3, §4.1, §5 P1). Standing
surface hypotheses throughout (`CONVENTIONS.md`).

* `toP1 f x : OnePoint ℂ` — `∞` at poles, the limiting value along the punctured neighborhood
  elsewhere (D2). Total; junk elsewhere for non-meromorphic `f`.
* `toP1_contMDiff` (P1): for `f` meromorphic everywhere, `toP1 f : X → ℙ¹` is holomorphic.
  **Deviation from the design's proof plan**: `meromorphic-and-divisors`'s `MeroGermOn`/`OrderEval`
  layer (`ℳ X`, `evalAt`, `holoRepr`, `holoRepr_contMDiffAt`) — which the design doc explicitly
  recorded as "not yet built" at design time — is now built; we route through it (`toP1 f` agrees
  *everywhere* with `toP1 (mk f hf).holoRepr`, since both `ordAtX` and `limUnder` are `𝓝[≠]x`-germ
  notions and `holoRepr` matches any representative `𝓝[≠]x`-eventually at *every* `x`), which
  handles the "poles/zeros are isolated" bookkeeping the design's hand-written plan struggled with,
  and lets us cite `MeroGermOn.holoRepr_contMDiffAt`/`ContMDiffAt.onePointCoe`
  (`ProjectiveLine.Holomorphy`, also since-landed) directly instead of re-deriving the chart-local
  analytic-repair argument from scratch. This is a strictly shorter, more robust proof of the same
  theorem; the exported statement is unchanged.
* `toP1_not_const` (D3): an everywhere-meromorphic, not-codiscretely-constant `f` induces a
  nonconstant `toP1 f`.
-/

open scoped ContDiff Manifold OnePoint
open Filter Set Function Topology

namespace RS.MTrace

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {f : X → ℂ} {x : X}

/-- The canonical `ℙ¹`-valued lift of a raw meromorphic function: `∞` at poles, the limiting
value along the punctured neighborhood elsewhere. Total (junk elsewhere for non-meromorphic `f`);
the honest content is `toP1_contMDiff`. -/
noncomputable def toP1 (f : X → ℂ) (x : X) : OnePoint ℂ :=
  if 0 ≤ RS.ordAtX f x then ((Filter.limUnder (𝓝[≠] x) f : ℂ) : OnePoint ℂ) else (∞ : OnePoint ℂ)

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X] in
theorem toP1_eq_infty_iff : toP1 f x = (∞ : OnePoint ℂ) ↔ RS.ordAtX f x < 0 := by
  unfold toP1
  split_ifs with h
  · simp only [OnePoint.coe_ne_infty, false_iff]
    exact not_lt.2 h
  · simp only [not_le] at h
    simp [h]

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X] in
theorem toP1_eq_coe_iff {c : ℂ} :
    toP1 f x = (c : OnePoint ℂ) ↔ 0 ≤ RS.ordAtX f x ∧ Filter.limUnder (𝓝[≠] x) f = c := by
  unfold toP1
  split_ifs with h
  · rw [OnePoint.coe_eq_coe]
    constructor
    · intro heq; exact ⟨h, heq⟩
    · rintro ⟨-, heq⟩; exact heq
  · constructor
    · intro heq; exact absurd heq.symm (OnePoint.coe_ne_infty c)
    · rintro ⟨h0, -⟩; exact absurd h0 h

/-! ### `toP1_contMDiff` (P1) -/

omit [CompactSpace X] [ConnectedSpace X] in
theorem toP1_contMDiff (hf : MeromorphicOnX f Set.univ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (toP1 f) := by
  -- Route through `holoRepr`: `toP1 f = toP1 f'` everywhere, `f' := (mk f hf).holoRepr`.
  set φ : RS.MeroGermOn X Set.univ := RS.MeroGermOn.mk f hf with hφ_def
  set f' : X → ℂ := φ.holoRepr with hf'_def
  have hf'mero : MeromorphicOnX f' Set.univ := RS.MeroGermOn.meromorphicOnX_holoRepr isOpen_univ φ
  have hordf' : ∀ y, RS.ordAtX f' y = φ.ord y := by
    intro y
    have hrep : RS.MeroGermOn.mk f' hf'mero = φ := RS.MeroGermOn.mk_holoRepr isOpen_univ φ
    rw [← RS.MeroGermOn.ord_mk isOpen_univ (mem_univ y) (f := f') (hf := hf'mero), hrep]
  have heq_germ : ∀ y, f =ᶠ[𝓝[≠] y] f' :=
    fun y => (RS.MeroGermOn.holoRepr_eventuallyEq_nhdsNE isOpen_univ (mem_univ y) φ rfl).symm
  have htoP1_eq : toP1 f = toP1 f' := by
    funext y
    have hordeq : RS.ordAtX f y = RS.ordAtX f' y := RS.ordAtX_congr (heq_germ y)
    have hlimeq : Filter.limUnder (𝓝[≠] y) f = Filter.limUnder (𝓝[≠] y) f' :=
      RS.limUnder_congr (heq_germ y)
    unfold toP1
    rw [hordeq, hlimeq]
  -- Pointwise fact: wherever `0 ≤ ordAtX f' z`, `toP1 f' z = ↑(f' z)` (no "isolated" propagation
  -- needed *pointwise*: `holoRepr_contMDiffAt` gives continuity of `f'` AT that point directly).
  have hpointwise : ∀ z, 0 ≤ RS.ordAtX f' z → toP1 f' z = ((f' z : ℂ) : OnePoint ℂ) := by
    intro z hz
    have hordφz : 0 ≤ φ.ord z := (hordf' z) ▸ hz
    have hcz : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f' z :=
      RS.MeroGermOn.holoRepr_contMDiffAt isOpen_univ (mem_univ z) hordφz
    rw [toP1_eq_coe_iff]
    exact ⟨hz, (hcz.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).limUnder_eq⟩
  rw [htoP1_eq]
  intro y
  by_cases h0 : 0 ≤ RS.ordAtX f' y
  · -- Regular case (order finite ≥0, or ⊤): `toP1 f' = ↑∘f'` on a *full* neighborhood of `y`
    -- (isolated zeros/poles, `eventually_ordAtX_eq_top`/`eventually_ordAtX_eq_zero`), so
    -- `toP1 f'` inherits `ContMDiffAt` from `f'` via `ContMDiffAt.onePointCoe` + congr.
    have hordφ : 0 ≤ φ.ord y := (hordf' y) ▸ h0
    have hcy : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f' y :=
      RS.MeroGermOn.holoRepr_contMDiffAt isOpen_univ (mem_univ y) hordφ
    have heqfull : toP1 f' =ᶠ[𝓝 y] fun z => ((f' z : ℂ) : OnePoint ℂ) := by
      by_cases htop : RS.ordAtX f' y = ⊤
      · filter_upwards [RS.eventually_ordAtX_eq_top htop] with z hz
        exact hpointwise z (hz ▸ le_top)
      · have hreg : ∀ᶠ z in 𝓝[≠] y, RS.ordAtX f' z = 0 :=
          RS.eventually_ordAtX_eq_zero (hf'mero y (mem_univ y)) htop
        rw [eventually_nhdsWithin_iff] at hreg
        filter_upwards [hreg] with z hz
        rcases eq_or_ne z y with rfl | hzy
        · exact hpointwise z h0
        · exact hpointwise z (hz hzy ▸ le_rfl)
    exact ContMDiffAt.congr_of_eventuallyEq (RS.P1.ContMDiffAt.onePointCoe hcy) heqfull
  · -- Pole case: adapt `RS.P1.contMDiffAt_of_pole`'s (planar) proof to the manifold `X`.
    have hordlt : RS.ordAtX f' y < 0 := not_le.1 h0
    set e := chartAt ℂ y with he_def
    set c := e y with hc_def
    have hg : MeromorphicAt (f' ∘ e.symm) c := hf'mero y (mem_univ y)
    have hordg : meromorphicOrderAt (f' ∘ e.symm) c < 0 := hordlt
    have heq : ∀ᶠ z in 𝓝[≠] y, toP1 f' z = ((f' z : ℂ) : OnePoint ℂ) := by
      have hreg : ∀ᶠ z in 𝓝[≠] y, RS.ordAtX f' z = 0 :=
        RS.eventually_ordAtX_eq_zero (hf'mero y (mem_univ y)) hordlt.ne_top
      filter_upwards [hreg] with z hz
      exact hpointwise z (hz ▸ le_rfl)
    have hcobdd : Tendsto f' (𝓝[≠] y) (Bornology.cobounded ℂ) :=
      (RS.tendsto_cobounded_iff_ordAtX_neg (hf'mero y (mem_univ y))).2 hordlt
    have hpunc : Tendsto (toP1 f') (𝓝[≠] y) (𝓝 (∞ : OnePoint ℂ)) := by
      rw [Filter.tendsto_congr' heq]
      exact RS.P1.tendsto_coe_cobounded.comp hcobdd
    have hFinf : toP1 f' y = (∞ : OnePoint ℂ) := toP1_eq_infty_iff.2 hordlt
    have hpure : Tendsto (toP1 f') (pure y) (𝓝 (∞ : OnePoint ℂ)) := hFinf ▸ tendsto_pure_nhds _ y
    have hcombine : Tendsto (toP1 f') (𝓝 y) (𝓝 (∞ : OnePoint ℂ)) := by
      rw [← nhdsNE_sup_pure y, tendsto_sup]
      exact ⟨hpunc, hpure⟩
    have hcontF : ContinuousAt (toP1 f') y := by rw [ContinuousAt, hFinf]; exact hcombine
    rw [RS.P1.contMDiffAt_iff_analyticAt_of_eq_infty hFinf]
    refine ⟨hcontF, ?_⟩
    have heqchart : ∀ᶠ z in 𝓝[≠] c, toP1 f' (e.symm z) = ((f' (e.symm z) : ℂ) : OnePoint ℂ) :=
      RS.eventually_nhdsNE_iff_comp_chart.mp heq
    have hcompeq :
        (⇑RS.P1.invChart ∘ (toP1 f') ∘ ⇑e.symm) =ᶠ[𝓝[≠] c] (f' ∘ e.symm)⁻¹ := by
      filter_upwards [heqchart] with z hz
      change RS.P1.invChart (toP1 f' (e.symm z)) = ((f' ∘ e.symm) z)⁻¹
      rw [hz, RS.P1.invChart_apply_coe]
      rfl
    have hordinv : meromorphicOrderAt (⇑RS.P1.invChart ∘ (toP1 f') ∘ ⇑e.symm) c
        = meromorphicOrderAt (f' ∘ e.symm)⁻¹ c := meromorphicOrderAt_congr hcompeq
    have hpos : 0 < meromorphicOrderAt (⇑RS.P1.invChart ∘ (toP1 f') ∘ ⇑e.symm) c := by
      rw [hordinv, meromorphicOrderAt_inv]
      exact LinearOrderedAddCommGroupWithTop.neg_pos.2 (Or.inl hordg)
    have hvalz : (⇑RS.P1.invChart ∘ (toP1 f') ∘ ⇑e.symm) c = 0 := by
      change RS.P1.invChart (toP1 f' (e.symm c)) = 0
      rw [show e.symm c = y from e.left_inv (mem_chart_source ℂ y), hFinf,
        RS.P1.invChart_apply_infty]
    exact AnalyticAt.of_meromorphicOrderAt_pos hpos hvalz

/-! ### Reusable `holoRepr` facts (for `OrderMultiplicity`/`ArgumentPrinciple`) -/

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- `f` agrees with its `holoRepr` in `toP1`, everywhere (both `ordAtX` and `limUnder` are
`𝓝[≠]x`-germ notions, and `holoRepr` matches any representative there, at *every* `x`). -/
theorem toP1_eq_toP1_holoRepr (hf : MeromorphicOnX f Set.univ) :
    toP1 f = toP1 (RS.MeroGermOn.mk f hf).holoRepr := by
  funext y
  have heq : f =ᶠ[𝓝[≠] y] (RS.MeroGermOn.mk f hf).holoRepr :=
    (RS.MeroGermOn.holoRepr_eventuallyEq_nhdsNE isOpen_univ (mem_univ y)
      (RS.MeroGermOn.mk f hf) rfl).symm
  unfold toP1
  rw [RS.ordAtX_congr heq, RS.limUnder_congr heq]

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
theorem ordAtX_holoRepr (hf : MeromorphicOnX f Set.univ) (y : X) :
    RS.ordAtX (RS.MeroGermOn.mk f hf).holoRepr y = RS.ordAtX f y :=
  (RS.ordAtX_congr ((RS.MeroGermOn.holoRepr_eventuallyEq_nhdsNE isOpen_univ (mem_univ y)
    (RS.MeroGermOn.mk f hf) rfl).symm)).symm

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
theorem meromorphicOnX_holoRepr' (hf : MeromorphicOnX f Set.univ) :
    MeromorphicOnX (RS.MeroGermOn.mk f hf).holoRepr Set.univ :=
  RS.MeroGermOn.meromorphicOnX_holoRepr isOpen_univ _

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
theorem holoRepr_contMDiffAt_of_nonneg (hf : MeromorphicOnX f Set.univ) {y : X}
    (hy : 0 ≤ RS.ordAtX (RS.MeroGermOn.mk f hf).holoRepr y) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (RS.MeroGermOn.mk f hf).holoRepr y := by
  rw [ordAtX_holoRepr hf y] at hy
  exact RS.MeroGermOn.holoRepr_contMDiffAt isOpen_univ (mem_univ y)
    (by rwa [RS.MeroGermOn.ord_mk isOpen_univ (mem_univ y)])

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- Wherever `f`'s `holoRepr` has nonnegative order, `toP1` of it is the literal coercion — a
*pointwise* fact (no "isolated zeros" propagation needed: `holoRepr_contMDiffAt` gives continuity
of the `holoRepr` AT that point directly). -/
theorem toP1_holoRepr_eq_coe_of_nonneg (hf : MeromorphicOnX f Set.univ) {y : X}
    (hy : 0 ≤ RS.ordAtX (RS.MeroGermOn.mk f hf).holoRepr y) :
    toP1 (RS.MeroGermOn.mk f hf).holoRepr y =
      (((RS.MeroGermOn.mk f hf).holoRepr y : ℂ) : OnePoint ℂ) := by
  have hcy := holoRepr_contMDiffAt_of_nonneg hf hy
  rw [toP1_eq_coe_iff]
  exact ⟨hy, (hcy.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).limUnder_eq⟩

omit [CompactSpace X] [ConnectedSpace X] in
/-- Full-neighborhood upgrade of `toP1_holoRepr_eq_coe_of_nonneg`: at a regular point (finite or
`⊤` order), `toP1 (holoRepr)` agrees with the coercion on a *full* neighborhood (isolated
zeros/poles). -/
theorem toP1_holoRepr_eventuallyEq_coe_of_nonneg (hf : MeromorphicOnX f Set.univ) {y : X}
    (hy : 0 ≤ RS.ordAtX (RS.MeroGermOn.mk f hf).holoRepr y) :
    toP1 (RS.MeroGermOn.mk f hf).holoRepr =ᶠ[𝓝 y]
      fun z => (((RS.MeroGermOn.mk f hf).holoRepr z : ℂ) : OnePoint ℂ) := by
  set f' := (RS.MeroGermOn.mk f hf).holoRepr with hf'_def
  have hf'mero : MeromorphicOnX f' Set.univ := meromorphicOnX_holoRepr' hf
  by_cases htop : RS.ordAtX f' y = ⊤
  · filter_upwards [RS.eventually_ordAtX_eq_top htop] with z hz
    exact toP1_holoRepr_eq_coe_of_nonneg hf (hz ▸ le_top)
  · have hreg : ∀ᶠ z in 𝓝[≠] y, RS.ordAtX f' z = 0 :=
      RS.eventually_ordAtX_eq_zero (hf'mero y (mem_univ y)) htop
    rw [eventually_nhdsWithin_iff] at hreg
    filter_upwards [hreg] with z hz
    rcases eq_or_ne z y with rfl | hzy
    · exact toP1_holoRepr_eq_coe_of_nonneg hf hy
    · exact toP1_holoRepr_eq_coe_of_nonneg hf (hz hzy ▸ le_rfl)

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- The `invChart` chart-composite of `toP1 (holoRepr)` at a pole matches the (inverted) chart
composite of `holoRepr` itself, off the pole. -/
theorem invChart_toP1_holoRepr_eventuallyEq_of_neg (hf : MeromorphicOnX f Set.univ) {y : X}
    (hy : RS.ordAtX (RS.MeroGermOn.mk f hf).holoRepr y < 0) :
    (⇑RS.P1.invChart ∘ (toP1 (RS.MeroGermOn.mk f hf).holoRepr) ∘ ⇑(chartAt ℂ y).symm)
      =ᶠ[𝓝[≠] (chartAt ℂ y y)] ((RS.MeroGermOn.mk f hf).holoRepr ∘ (chartAt ℂ y).symm)⁻¹ := by
  set f' := (RS.MeroGermOn.mk f hf).holoRepr with hf'_def
  have hf'mero : MeromorphicOnX f' Set.univ := meromorphicOnX_holoRepr' hf
  set e := chartAt ℂ y with he_def
  have heq : ∀ᶠ z in 𝓝[≠] y, toP1 f' z = ((f' z : ℂ) : OnePoint ℂ) := by
    have hreg : ∀ᶠ z in 𝓝[≠] y, RS.ordAtX f' z = 0 :=
      RS.eventually_ordAtX_eq_zero (hf'mero y (mem_univ y)) hy.ne_top
    filter_upwards [hreg] with z hz
    exact toP1_holoRepr_eq_coe_of_nonneg hf (hz ▸ le_rfl)
  have heqchart : ∀ᶠ z in 𝓝[≠] e y, toP1 f' (e.symm z) = ((f' (e.symm z) : ℂ) : OnePoint ℂ) :=
    RS.eventually_nhdsNE_iff_comp_chart.mp heq
  filter_upwards [heqchart] with z hz
  change RS.P1.invChart (toP1 f' (e.symm z)) = ((f' ∘ e.symm) z)⁻¹
  rw [hz, RS.P1.invChart_apply_coe]
  rfl

/-! ### Nonconstancy (D3) -/

/-- The natural raw-function nonconstancy hypothesis: `f` is not codiscretely equal to any single
constant. (What callers holding `ℳ X` nonzero-ness will have once that field is in hand; stated
here germ-level so we do not need it.) -/
def NotEventuallyConstX (f : X → ℂ) : Prop := ∀ c : ℂ, ¬ (fun x => f x - c) =ᶠ[codiscrete X] 0

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- If a globally meromorphic `g` has *strictly positive* order at *every* point, `g` is
codiscretely `0`: a point where the order is finite (`≠ ⊤`) would force order `0` at nearby
points (`eventually_ordAtX_eq_zero`), contradicting positivity there; so the order is `⊤`
everywhere. -/
private theorem eventuallyEq_zero_codiscrete_of_forall_ordAtX_pos {g : X → ℂ}
    (hg : MeromorphicOnX g Set.univ) (hpos : ∀ x, 0 < RS.ordAtX g x) :
    g =ᶠ[codiscrete X] 0 := by
  have htop : ∀ x, RS.ordAtX g x = ⊤ := by
    intro x
    by_contra hne
    have hnear := RS.eventually_ordAtX_eq_zero (hg x (mem_univ x)) hne
    obtain ⟨y, hy⟩ := hnear.exists
    exact absurd hy (hpos y).ne'
  exact RS.eventuallyEq_codiscrete_iff.2 (fun x => RS.ordAtX_eq_top_iff.1 (htop x))

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- The translation: an everywhere-meromorphic `f` on connected `X` that is not codiscretely a
constant induces a nonconstant `toP1 f`. Both degenerate cases (`toP1 f ≡ ↑c` and `toP1 f ≡ ∞`)
are ruled out by the SAME `eventuallyEq_zero_codiscrete_of_forall_ordAtX_pos` engine, applied to
`f - c` (finite case) resp. `f⁻¹` (the `∞` case, via `ordAtX_inv` unconditional). -/
theorem toP1_not_const (hf : MeromorphicOnX f Set.univ) (hnc : NotEventuallyConstX f) :
    ¬ ∃ c, ∀ x, toP1 f x = c := by
  rintro ⟨c, hc⟩
  induction c using OnePoint.rec with
  | infty =>
    have hfinv_mero : MeromorphicOnX f⁻¹ Set.univ := hf.inv
    have hpos : ∀ x, 0 < RS.ordAtX f⁻¹ x := by
      intro x
      have h1 : RS.ordAtX f x < 0 := toP1_eq_infty_iff.1 (hc x)
      rw [RS.ordAtX_inv]
      exact LinearOrderedAddCommGroupWithTop.neg_pos.2 (Or.inl h1)
    have hz : f⁻¹ =ᶠ[codiscrete X] 0 :=
      eventuallyEq_zero_codiscrete_of_forall_ordAtX_pos hfinv_mero hpos
    have hz' : f =ᶠ[codiscrete X] 0 := by
      rw [RS.eventuallyEq_codiscrete_iff] at hz ⊢
      intro x
      filter_upwards [hz x] with y hy
      simpa using congrArg Inv.inv hy
    exact hnc 0 (by simpa using hz')
  | coe c₀ =>
    have hmerosub : MeromorphicOnX (f - fun _ => c₀) Set.univ :=
      hf.sub (meromorphicOnX_const c₀ Set.univ)
    have hpos : ∀ x, 0 < RS.ordAtX (f - fun _ => c₀) x := by
      intro x
      obtain ⟨h1a, h1b⟩ := toP1_eq_coe_iff.1 (hc x)
      obtain ⟨d, hd⟩ := (RS.tendsto_nhds_iff_ordAtX_nonneg (hf x (mem_univ x))).2 h1a
      have hdc : d = c₀ := hd.limUnder_eq.symm.trans h1b
      rw [hdc] at hd
      have htend : Tendsto (f - fun _ => c₀) (𝓝[≠] x) (𝓝 0) := by
        have hconst : Tendsto (fun _ : X => c₀) (𝓝[≠] x) (𝓝 c₀) := tendsto_const_nhds
        have hsub := hd.sub hconst
        simp only [sub_self] at hsub
        exact hsub
      have htend' : Tendsto ((f - fun _ => c₀) ∘ (chartAt ℂ x).symm)
          (𝓝[≠] (chartAt ℂ x x)) (𝓝 0) := RS.tendsto_nhdsNE_comp_chart_iff.1 htend
      exact (tendsto_zero_iff_meromorphicOrderAt_pos (hmerosub x (mem_univ x))).1 htend'
    have hz : (f - fun _ => c₀) =ᶠ[codiscrete X] 0 :=
      eventuallyEq_zero_codiscrete_of_forall_ordAtX_pos hmerosub hpos
    apply hnc c₀
    rw [RS.eventuallyEq_codiscrete_iff] at hz ⊢
    intro x
    filter_upwards [hz x] with y hy
    simpa using hy

end RS.MTrace
