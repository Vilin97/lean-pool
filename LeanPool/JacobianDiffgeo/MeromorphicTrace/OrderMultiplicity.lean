/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

/-
Blueprint unit: meromorphic-trace. Order↔multiplicity bridges (zero and pole cases), file 2 of
the design's 6-file plan.
-/
import LeanPool.JacobianDiffgeo.MeromorphicTrace.ToP1
import LeanPool.JacobianDiffgeo.LocalMultiplicity.Multiplicity

/-!
# Order↔multiplicity bridges (meromorphic-trace, cluster 1)

Unit: meromorphic-trace (`docs/design/meromorphic-trace.md` §2 D4, §4.2, §5 P2). Standing surface
hypotheses throughout.

* `multiplicity_toP1_of_ordAtX_pos`: at a zero of `f`, CC4's multiplicity of `toP1 f` (read in
  `coeChart`, the chart at `↑0`) IS the vanishing order.
* `multiplicity_toP1_of_ordAtX_neg`: at a pole of `f`, CC4's multiplicity of `toP1 f` (read in
  `invChart`, the chart at `∞`) IS the order of the pole (made positive).

Route: both hard cases reduce to CC3's `ordAtX_of_contMDiffAt_eq_zero` (already built,
local-multiplicity/meromorphic-and-divisors) applied to `f' := holoRepr` (resp. `f'⁻¹` for the
pole case), plus ONE shared CC4-level `inChartAt`-germ comparison
(`multiplicityENat_toP1_eq_of_eventuallyEq`) identifying `multiplicityENat (toP1 f') x` with the
`multiplicityENat` of the appropriate ℂ-valued companion, using the reusable `holoRepr`/`toP1`
facts exported by `ToP1.lean`.

**Deviation**: the design's third export, `multiplicity_toP1_of_ordAtX_eq_zero`
(`ordAtX f x = 0 → multiplicity (toP1 f) x = 1`), is **mathematically false as stated** and is
NOT proved here. Counterexample: `f (z) = 1 + z ^ 2` near `z = 0` has `ordAtX f 0 = 0`
(`f 0 = 1 ≠ 0`, a "regular value" in the vanishing-order sense) but `toP1 f` has multiplicity `2`
at `0` as a *map* (`f y - f 0 = y ^ 2`, a genuine ramification point — `ordAtX f x = 0` says
nothing about `deriv f x`, only that `f` does not vanish/pole at `x`). The design itself flags
this lemma as a non-essential "cheap corollary... even though we do not need it ourselves" for
`form-trace-tower`'s glue; nothing in this unit's own proof obligations needs it, so it is simply
dropped rather than patched into a different (correct) statement under the same name.
-/

open scoped ContDiff Manifold OnePoint
open Filter Set Function Topology

namespace RS.MTrace

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {f : X → ℂ} {x : X}

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Shared CC4-level bridge: if the target-chart composite of `toP1 G` matches (on a *full*
neighborhood) the chart composite of a companion ℂ-valued function `g`, the CC4 multiplicities of
`toP1 G` and of `g` coincide (same `inChartAt` germ, since the target chart's own recentering
matches `g`'s own value at `x` automatically, `chartAt_self_eq` on the ℂ side). -/
private theorem multiplicityENat_toP1_eq_of_eventuallyEq {G g : X → ℂ} {x : X}
    {chart : OpenPartialHomeomorph (OnePoint ℂ) ℂ} (hchart : chartAt ℂ (toP1 G x) = chart)
    (hcompeq : (⇑chart ∘ (toP1 G) ∘ ⇑(chartAt ℂ x).symm) =ᶠ[𝓝 (chartAt ℂ x x)]
      (g ∘ (chartAt ℂ x).symm)) :
    RS.multiplicityENat (toP1 G) x = RS.multiplicityENat g x := by
  have hcompeq' : ∀ᶠ z in 𝓝 (chartAt ℂ x x),
      chart (toP1 G ((chartAt ℂ x).symm z)) = g ((chartAt ℂ x).symm z) := by
    filter_upwards [hcompeq] with z hz using hz
  have hzc : chart (toP1 G x) = g x := by
    have h := hcompeq'.self_of_nhds
    rwa [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)] at h
  have hinChartAt_eq : RS.inChartAt (toP1 G) x =ᶠ[𝓝 (chartAt ℂ x x)] RS.inChartAt g x := by
    filter_upwards [hcompeq'] with z hz
    change chartAt ℂ (toP1 G x) (toP1 G ((chartAt ℂ x).symm z)) - chartAt ℂ (toP1 G x) (toP1 G x)
      = chartAt ℂ (g x) (g ((chartAt ℂ x).symm z)) - chartAt ℂ (g x) (g x)
    rw [hchart, hz, hzc, chartAt_self_eq]
    rfl
  unfold RS.multiplicityENat
  exact analyticOrderAt_congr hinChartAt_eq

/-- Upgrade a `𝓝[≠]`-eventual chart-composite match (plus a value match AT the point) to a full
`𝓝`-eventual one. -/
private theorem eventuallyEq_of_eventuallyEq_nhdsNE_of_eq {α : Type*} [TopologicalSpace α]
    {F G : α → ℂ} {c : α} (hpunc : F =ᶠ[𝓝[≠] c] G) (hval : F c = G c) : F =ᶠ[𝓝 c] G := by
  have hpunc' : ∀ᶠ z in 𝓝[≠] c, F z = G z := hpunc
  rw [eventually_nhdsWithin_iff] at hpunc'
  filter_upwards [hpunc'] with z hz
  rcases eq_or_ne z c with rfl | hzc
  · exact hval
  · exact hz hzc

omit [CompactSpace X] [ConnectedSpace X] in
/-- Zero case (P2): at a zero of `f`, CC4's multiplicity of `toP1 f` IS the vanishing order. -/
theorem multiplicity_toP1_of_ordAtX_pos (hf : MeromorphicOnX f Set.univ)
    (hx : 0 < RS.ordAtX f x) :
    (RS.multiplicity (toP1 f) x : ℤ) = (RS.ordAtX f x).untop₀ := by
  have hordeq : RS.ordAtX (RS.MeroGermOn.mk f hf).holoRepr x = RS.ordAtX f x := ordAtX_holoRepr hf x
  have hx' : 0 < RS.ordAtX (RS.MeroGermOn.mk f hf).holoRepr x := hordeq ▸ hx
  have hcx : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (RS.MeroGermOn.mk f hf).holoRepr x :=
    holoRepr_contMDiffAt_of_nonneg hf hx'.le
  set f' := (RS.MeroGermOn.mk f hf).holoRepr with hf'_def
  -- `f' x = 0`: order > 0 ⟹ `f'` tends to `0` along `𝓝[≠]x`, matching its own continuous value.
  have hf'x0 : f' x = 0 := by
    have htend1 : Tendsto f' (𝓝[≠] x) (𝓝 (f' x)) :=
      hcx.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have htend2 : Tendsto f' (𝓝[≠] x) (𝓝 0) := by
      have hchart : (0 : ℤ) < meromorphicOrderAt (f' ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) := hx'
      exact RS.tendsto_nhdsNE_comp_chart_iff.2 (tendsto_zero_of_meromorphicOrderAt_pos hchart)
    exact tendsto_nhds_unique htend1 htend2
  -- CC3 ↔ CC4 bridge for the ℂ-valued `f'` (already built, local-multiplicity/CC3 compat).
  have hbridge : RS.ordAtX f' x = (RS.multiplicityENat f' x).map (Nat.cast : ℕ → ℤ) :=
    RS.ordAtX_of_contMDiffAt_eq_zero hcx hf'x0
  -- The two CC4 multiplicities (of `toP1 f'` and of `f'`) coincide, via `coeChart`.
  have htoP1x0 : toP1 f' x = ((0 : ℂ) : OnePoint ℂ) := by
    rw [show toP1 f' x = ((f' x : ℂ) : OnePoint ℂ) from toP1_holoRepr_eq_coe_of_nonneg hf hx'.le,
      hf'x0]
  have heqfull : toP1 f' =ᶠ[𝓝 x] fun z => ((f' z : ℂ) : OnePoint ℂ) :=
    toP1_holoRepr_eventuallyEq_coe_of_nonneg hf hx'.le
  have hchartcoe : chartAt ℂ (toP1 f' x) = RS.P1.coeChart := by
    rw [htoP1x0]; exact RS.P1.chartAt_coe 0
  have hmap : Filter.map (chartAt ℂ x).symm (𝓝 (chartAt ℂ x x)) = 𝓝 x :=
    (chartAt ℂ x).symm_map_nhds_eq (mem_chart_source ℂ x)
  have hcompeq : (⇑RS.P1.coeChart ∘ (toP1 f') ∘ ⇑(chartAt ℂ x).symm) =ᶠ[𝓝 (chartAt ℂ x x)]
      (f' ∘ (chartAt ℂ x).symm) := by
    have heqfull2 : ∀ᶠ z in 𝓝 x, toP1 f' z = ((f' z : ℂ) : OnePoint ℂ) := heqfull
    have heqfull' : ∀ᶠ z in 𝓝 (chartAt ℂ x x),
        toP1 f' ((chartAt ℂ x).symm z) = ((f' ((chartAt ℂ x).symm z) : ℂ) : OnePoint ℂ) := by
      rw [← hmap, eventually_map] at heqfull2
      exact heqfull2
    filter_upwards [heqfull'] with z hz
    change RS.P1.coeChart (toP1 f' ((chartAt ℂ x).symm z)) = f' ((chartAt ℂ x).symm z)
    rw [hz, RS.P1.coeChart_apply_coe]
  have hmultEq : RS.multiplicityENat (toP1 f') x = RS.multiplicityENat f' x :=
    multiplicityENat_toP1_eq_of_eventuallyEq hchartcoe hcompeq
  have hordfinal : RS.ordAtX f' x = (RS.multiplicityENat (toP1 f') x).map (Nat.cast : ℕ → ℤ) := by
    rw [hbridge, hmultEq]
  rw [← toP1_eq_toP1_holoRepr hf] at hordfinal
  rw [← hordeq, hordfinal, RS.multiplicity_def]
  cases h : RS.multiplicityENat (toP1 f) x with
  | top => simp
  | coe n => simp

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- Pole case (P2): at a pole of `f`, CC4's multiplicity of `toP1 f` IS the order of the pole
(made positive). -/
theorem multiplicity_toP1_of_ordAtX_neg (hf : MeromorphicOnX f Set.univ)
    (hx : RS.ordAtX f x < 0) :
    (RS.multiplicity (toP1 f) x : ℤ) = -(RS.ordAtX f x).untop₀ := by
  have hordeq : RS.ordAtX (RS.MeroGermOn.mk f hf).holoRepr x = RS.ordAtX f x := ordAtX_holoRepr hf x
  have hx' : RS.ordAtX (RS.MeroGermOn.mk f hf).holoRepr x < 0 := hordeq ▸ hx
  set f' := (RS.MeroGermOn.mk f hf).holoRepr with hf'_def
  have hf'mero : MeromorphicOnX f' Set.univ := meromorphicOnX_holoRepr' hf
  -- `f' x = 0` (junk value of `evalAt`/`holoRepr` off the nonneg-order locus).
  have hf'x0 : f' x = 0 := by
    have hnn : ¬ 0 ≤ (RS.MeroGermOn.mk f hf).ord x := by
      rw [RS.MeroGermOn.ord_mk isOpen_univ (mem_univ x), ← hordeq]
      exact not_le.2 hx'
    exact RS.MeroGermOn.evalAt_of_not_nonneg hnn
  have hf'inv_ordpos : (0 : ℤ) < meromorphicOrderAt (f'⁻¹ ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) :=
      by
    change (0 : ℤ) < meromorphicOrderAt (f' ∘ (chartAt ℂ x).symm)⁻¹ (chartAt ℂ x x)
    rw [meromorphicOrderAt_inv]
    exact LinearOrderedAddCommGroupWithTop.neg_pos.2 (Or.inl hx')
  have hf'invx0 : (f'⁻¹ ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) = 0 := by
    change (f' ((chartAt ℂ x).symm (chartAt ℂ x x)))⁻¹ = 0
    rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x), hf'x0, inv_zero]
  have hcxinv : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f'⁻¹ x :=
    RS.contMDiffAt_iff_analyticAt_comp_chartAt.2
      (AnalyticAt.of_meromorphicOrderAt_pos hf'inv_ordpos hf'invx0)
  have hordfinv : RS.ordAtX f'⁻¹ x = -RS.ordAtX f' x := RS.ordAtX_inv
  have hf'invx0' : f'⁻¹ x = 0 := by
    change (f' x)⁻¹ = 0
    rw [hf'x0, inv_zero]
  -- CC3 ↔ CC4 bridge for the ℂ-valued `f'⁻¹`.
  have hbridge : RS.ordAtX f'⁻¹ x = (RS.multiplicityENat f'⁻¹ x).map (Nat.cast : ℕ → ℤ) :=
    RS.ordAtX_of_contMDiffAt_eq_zero hcxinv hf'invx0'
  -- The two CC4 multiplicities (of `toP1 f'` and of `f'⁻¹`) coincide, via `invChart`.
  have htoP1xinf : toP1 f' x = (∞ : OnePoint ℂ) := toP1_eq_infty_iff.2 hx'
  have hchartinv : chartAt ℂ (toP1 f' x) = RS.P1.invChart := by
    rw [htoP1xinf]; exact RS.P1.chartAt_infty
  have hpunc : (⇑RS.P1.invChart ∘ (toP1 f') ∘ ⇑(chartAt ℂ x).symm) =ᶠ[𝓝[≠] (chartAt ℂ x x)]
      (f' ∘ (chartAt ℂ x).symm)⁻¹ := invChart_toP1_holoRepr_eventuallyEq_of_neg hf hx'
  have hval : (⇑RS.P1.invChart ∘ (toP1 f') ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) =
      (f' ∘ (chartAt ℂ x).symm)⁻¹ (chartAt ℂ x x) := by
    change RS.P1.invChart (toP1 f' ((chartAt ℂ x).symm (chartAt ℂ x x))) = _
    rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x), htoP1xinf, RS.P1.invChart_apply_infty]
    exact hf'invx0.symm
  have hcompeq : (⇑RS.P1.invChart ∘ (toP1 f') ∘ ⇑(chartAt ℂ x).symm) =ᶠ[𝓝 (chartAt ℂ x x)]
      (f' ∘ (chartAt ℂ x).symm)⁻¹ := eventuallyEq_of_eventuallyEq_nhdsNE_of_eq hpunc hval
  have hmultEq : RS.multiplicityENat (toP1 f') x = RS.multiplicityENat f'⁻¹ x :=
    multiplicityENat_toP1_eq_of_eventuallyEq hchartinv hcompeq
  have hordfinal : RS.ordAtX f'⁻¹ x = (RS.multiplicityENat (toP1 f') x).map (Nat.cast : ℕ → ℤ) := by
    rw [hbridge, hmultEq]
  rw [← toP1_eq_toP1_holoRepr hf] at hordfinal
  have hmain : (RS.multiplicity (toP1 f) x : ℤ) = (RS.ordAtX f'⁻¹ x).untop₀ := by
    rw [hordfinal, RS.multiplicity_def]
    cases h : RS.multiplicityENat (toP1 f) x with
    | top => simp
    | coe n => simp
  rw [hmain, hordfinv, WithTop.untop₀_neg, hordeq]

end RS.MTrace
