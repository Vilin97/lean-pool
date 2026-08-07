/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

/-
Blueprint unit: form-trace-tower. Pair-form residues `resAtX F h x` (D2) and their
chart-invariance (task item 1).
-/
import LeanPool.JacobianDiffgeo.ResidueCalculus.ChangeOfVariables
import LeanPool.JacobianDiffgeo.LocalMultiplicity.ChartBridge
import LeanPool.JacobianDiffgeo.Meromorphic.Predicates

/-!
# Pair-form residues (`form-trace-tower`, file 1/6)

Unit: form-trace-tower (`docs/design/form-trace-tower.md` §2 D2, §4.1, §5 P1). Fully independent
of `meromorphic-trace`'s build state.

For `F : X → Y` and `h : X → ℂ`, the pair-form `h · F^*(dz)` has coefficient `h` against the
pullback of the target's own coordinate differential — no new `Form1`-meromorphic type is
introduced (D1). Its residue at `x`, read in the PREFERRED chart pair (`chartAt`), is `resAtX`.

**Deviation from the design (found during construction, recorded honestly):** §4.1's
`resAtX_eq_of_mem_source` claims `resAtX` may be recomputed in ANY pair of maximal-atlas charts
`(e, e')` with NO correction factor. This is FALSE in general: e.g. `X = Y = ℂ` (standard
self-charts), `F = id`, `h = fun z => 1/z`, `x = 0`. Using `(e, e') = (id, id)` gives
`resAtX F h 0 = resAt (1/z) 0 = 1`. Using the (equally valid, maximal-atlas) target chart
`e' := (fun y => 2*y)` (an entire, invertible-derivative self-map of `ℂ`, hence in the maximal
atlas) gives `resAt (fun z => (1/z) * 2) 0 = 2 ≠ 1`. The root cause: changing the TARGET chart
changes WHICH 1-form `F^*(dz)` means (`d(e'_new) = deriv(e'_new ∘ e'_old.symm)(·) · d(e'_old)`,
a coefficient that VARIES over `X`, not a constant), so reusing the SAME bare `h` against a
different target chart computes the residue of a genuinely DIFFERENT 1-form. By contrast,
changing only the SOURCE chart (`e`) is a bona fide 1-form reparametrization and IS invariant
(exactly `RS.resAt_comp_mul_deriv`'s content) — this is `resAtX_eq_of_mem_source_left` below,
the one general, exported "chart invariance" fact. The target side is genuinely NOT free; where
a target-chart change is needed (§5 P-main, comparing to `AdaptedChartsAt`'s adapted target
chart), the correction is tracked explicitly via an additional calibration hypothesis rather
than assumed away (see `ResidueTraceCompat.lean`).

* `resAtX F h x` — the residue of `h · F^*(dz)` at `x` (D2).
* `resAtX_eq_of_mem_source_left` — SOURCE-chart invariance (task item 1, the TRUE half): may be
  computed in ANY maximal-atlas chart at `x`, target chart held fixed at `chartAt ℂ (F x)`.
* Basic algebra: `resAtX_congr`, `resAtX_add`, `resAtX_const_mul`.
-/

open scoped ContDiff Manifold
open Filter Topology Metric Function Set

namespace RS.FormTrace

variable {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-- The residue at `x` of the pair-form `h · F^*(dz)`, read in the PREFERRED chart at `x` (and
the preferred chart at `F x` for the target coordinate). Source-side chart-independence:
`resAtX_eq_of_mem_source_left` below. -/
noncomputable def resAtX (F : X → Y) (h : X → ℂ) (x : X) : ℂ :=
  RS.resAt (fun z => h ((chartAt ℂ x).symm z) *
    deriv (chartAt ℂ (F x) ∘ F ∘ (chartAt ℂ x).symm) z) (chartAt ℂ x x)

omit [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y] in
theorem resAtX_def (F : X → Y) (h : X → ℂ) (x : X) :
    resAtX F h x = RS.resAt (fun z => h ((chartAt ℂ x).symm z) *
      deriv (chartAt ℂ (F x) ∘ F ∘ (chartAt ℂ x).symm) z) (chartAt ℂ x x) := rfl

/-! ### Compat: the two-chart `ContMDiffAt ↔ AnalyticAt` bridge

Not currently exported by `surfaces-and-charts`/`Meromorphic.Predicates` for a general chart
PAIR `(e, e')` on `X`/`Y` (only for `f : X → ℂ` against the trivial target chart, via
`RS.contMDiffAt_iff_analyticAt_of_mem_source`). Derived here (one direction only — the direction
actually needed, `ContMDiffAt → AnalyticAt`) directly from mathlib's
`contMDiffWithinAt_iff_of_mem_maximalAtlas`, mirroring that existing proof's simp pattern. -/

section Compat

omit [IsManifold 𝓘(ℂ, ℂ) ω X] [IsManifold 𝓘(ℂ, ℂ) ω Y] in
/-- `ContMDiffAt` for a map `F : X → Y` gives analyticity of the chart composite in ANY pair of
maximal-atlas charts (`e` at `x`, `e'` at `F x`). (Only the forward direction is proved/needed;
the converse would need an extra continuity argument not required here.) -/
theorem analyticAt_comp_chart_pair {F : X → Y} {x : X}
    {e : OpenPartialHomeomorph X ℂ} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X)
    (hx : x ∈ e.source) {e' : OpenPartialHomeomorph Y ℂ}
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω Y) (hFx : F x ∈ e'.source)
    (hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x) :
    AnalyticAt ℂ (e' ∘ F ∘ e.symm) (e x) := by
  have h := ((contMDiffWithinAt_iff_of_mem_maximalAtlas he he' hx hFx).mp hF).2
  simp only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_id, Function.id_comp,
    Set.range_id, Set.preimage_univ, Set.univ_inter, contDiffWithinAt_univ] at h
  exact h.analyticAt

end Compat

/-! ### Source-chart invariance (task item 1) -/

omit [IsManifold 𝓘(ℂ, ℂ) ω Y] in
/-- Source-chart invariance of the pair-form integrand's residue: the target chart `e'` is held
FIXED (arbitrary), only the source chart varies. The TRUE, general half of chart-invariance —
directly analogous to `RS.ordAtX_eq_of_mem_source`, via ONE application of
`RS.resAt_comp_mul_deriv`. -/
theorem resAt_pairForm_source_change {F : X → Y} {h : X → ℂ} {x : X}
    {e1 e2 : OpenPartialHomeomorph X ℂ} (he1 : e1 ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X)
    (hx1 : x ∈ e1.source) (he2 : e2 ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X) (hx2 : x ∈ e2.source)
    {e' : OpenPartialHomeomorph Y ℂ} (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω Y)
    (hFx : F x ∈ e'.source) (hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x) (hh : MeromorphicAtX h x) :
    RS.resAt (fun z => h (e1.symm z) * deriv (e' ∘ F ∘ e1.symm) z) (e1 x)
      = RS.resAt (fun z => h (e2.symm z) * deriv (e' ∘ F ∘ e2.symm) z) (e2 x) := by
  set τ : ℂ → ℂ := e1 ∘ e2.symm with hτ_def
  obtain ⟨hτ, hτ'⟩ := analyticAt_transition he2 he1 hx2 hx1
  have hτ0 : τ (e2 x) = e1 x := by
    change e1 (e2.symm (e2 x)) = e1 x
    rw [e2.left_inv hx2]
  set f : ℂ → ℂ := fun z => h (e1.symm z) * deriv (e' ∘ F ∘ e1.symm) z with hf_def
  have hg1 : AnalyticAt ℂ (e' ∘ F ∘ e1.symm) (e1 x) :=
    analyticAt_comp_chart_pair he1 hx1 he' hFx hF
  have hh1 : MeromorphicAt (h ∘ e1.symm) (e1 x) :=
    (meromorphicAtX_iff_of_mem_source he1 hx1).1 hh
  have hf : MeromorphicAt f (e1 x) := hh1.mul hg1.deriv.meromorphicAt
  have hmain := resAt_comp_mul_deriv hτ hτ' hτ0 hf
  rw [← hmain]
  apply resAt_congr
  have hmem1 : ∀ᶠ w in 𝓝 (e2 x), e2.symm w ∈ e1.source := by
    have hcont := e2.continuousAt_symm (e2.map_source hx2)
    have hmem : e1.source ∈ 𝓝 (e2.symm (e2 x)) := by
      rw [e2.left_inv hx2]; exact e1.open_source.mem_nhds hx1
    exact hcont.eventually hmem
  have hτdiff : ∀ᶠ w in 𝓝 (e2 x), AnalyticAt ℂ τ w := hτ.eventually_analyticAt
  have hτtendsto : Filter.Tendsto τ (𝓝 (e2 x)) (𝓝 (e1 x)) := by
    rw [← hτ0]; exact hτ.continuousAt.tendsto
  have hg1diff : ∀ᶠ w in 𝓝 (e2 x), AnalyticAt ℂ (e' ∘ F ∘ e1.symm) (τ w) :=
    hτtendsto.eventually hg1.eventually_analyticAt
  have heqnear : ∀ᶠ w in 𝓝 (e2 x), ∀ᶠ w' in 𝓝 w, e2.symm w' ∈ e1.source :=
    hmem1.eventually_nhds
  have hcombined : ∀ᶠ w in 𝓝[≠] (e2 x), e2.symm w ∈ e1.source ∧ AnalyticAt ℂ τ w ∧
      AnalyticAt ℂ (e' ∘ F ∘ e1.symm) (τ w) ∧ (∀ᶠ w' in 𝓝 w, e2.symm w' ∈ e1.source) :=
    (hmem1.and (hτdiff.and (hg1diff.and heqnear))).filter_mono nhdsWithin_le_nhds
  filter_upwards [hcombined] with w hw
  obtain ⟨hw1, hw2, hw3, hw4⟩ := hw
  change h (e1.symm (τ w)) * deriv (e' ∘ F ∘ e1.symm) (τ w) * deriv τ w
    = h (e2.symm w) * deriv (e' ∘ F ∘ e2.symm) w
  have hval : e1.symm (τ w) = e2.symm w := by
    change e1.symm (e1 (e2.symm w)) = e2.symm w
    rw [e1.left_inv hw1]
  have heqfun : (fun w' => (e' ∘ F ∘ e1.symm) (τ w')) =ᶠ[𝓝 w] (e' ∘ F ∘ e2.symm) := by
    filter_upwards [hw4] with w' hw1'
    change (e' ∘ F ∘ e1.symm) (e1 (e2.symm w')) = (e' ∘ F ∘ e2.symm) w'
    simp only [Function.comp_apply]
    rw [e1.left_inv hw1']
  have hderiv1 : HasDerivAt τ (deriv τ w) w := hw2.differentiableAt.hasDerivAt
  have hderiv2 : HasDerivAt (e' ∘ F ∘ e1.symm) (deriv (e' ∘ F ∘ e1.symm) (τ w)) (τ w) :=
    hw3.differentiableAt.hasDerivAt
  have hcomp : HasDerivAt ((e' ∘ F ∘ e1.symm) ∘ τ)
      (deriv (e' ∘ F ∘ e1.symm) (τ w) * deriv τ w) w := hderiv2.comp w hderiv1
  have hcomp' : HasDerivAt (e' ∘ F ∘ e2.symm)
      (deriv (e' ∘ F ∘ e1.symm) (τ w) * deriv τ w) w :=
    hcomp.congr_of_eventuallyEq heqfun.symm
  rw [hval, hcomp'.deriv]
  ring

/-- Source-chart invariance (task item 1): `resAtX` may be computed in ANY maximal-atlas chart
at `x`, provided the TARGET chart is held at the preferred `chartAt ℂ (F x)`. -/
theorem resAtX_eq_of_mem_source_left {F : X → Y} {h : X → ℂ} {x : X}
    {e : OpenPartialHomeomorph X ℂ} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X)
    (hx : x ∈ e.source) (hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x) (hh : MeromorphicAtX h x) :
    resAtX F h x
      = RS.resAt (fun z => h (e.symm z) * deriv (chartAt ℂ (F x) ∘ F ∘ e.symm) z) (e x) := by
  rw [resAtX_def]
  exact resAt_pairForm_source_change (IsManifold.chart_mem_maximalAtlas x) (mem_chart_source ℂ x)
    he hx (IsManifold.chart_mem_maximalAtlas (F x)) (mem_chart_source ℂ (F x)) hF hh

/-! ### Basic algebra -/

omit [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y] in
theorem resAtX_congr {F : X → Y} {h h' : X → ℂ} {x : X} (hh : h =ᶠ[𝓝[≠] x] h') :
    resAtX F h x = resAtX F h' x := by
  rw [resAtX_def, resAtX_def]
  apply resAt_congr
  have heq := (eventuallyEq_nhdsNE_comp_chart_iff (f := h) (g := h') (x := x)).mp hh
  filter_upwards [heq] with z hz
  simp only [Function.comp_apply] at hz
  rw [hz]

theorem resAtX_add {F : X → Y} {h h' : X → ℂ} {x : X} (hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x)
    (hh : MeromorphicAtX h x) (hh' : MeromorphicAtX h' x) :
    resAtX F (fun y => h y + h' y) x = resAtX F h x + resAtX F h' x := by
  rw [resAtX_def, resAtX_def, resAtX_def]
  set c := chartAt ℂ x with hc_def
  set g : ℂ → ℂ := chartAt ℂ (F x) ∘ F ∘ c.symm with hg_def
  have hg : AnalyticAt ℂ g (c x) :=
    analyticAt_comp_chart_pair (IsManifold.chart_mem_maximalAtlas x) (mem_chart_source ℂ x)
      (IsManifold.chart_mem_maximalAtlas (F x)) (mem_chart_source ℂ (F x)) hF
  have hh1 : MeromorphicAt (h ∘ c.symm) (c x) :=
    (meromorphicAtX_iff_of_mem_source (IsManifold.chart_mem_maximalAtlas x)
      (mem_chart_source ℂ x)).1 hh
  have hh1' : MeromorphicAt (h' ∘ c.symm) (c x) :=
    (meromorphicAtX_iff_of_mem_source (IsManifold.chart_mem_maximalAtlas x)
      (mem_chart_source ℂ x)).1 hh'
  have hha : MeromorphicAt (fun z => h (c.symm z) * deriv g z) (c x) :=
    hh1.mul hg.deriv.meromorphicAt
  have hha' : MeromorphicAt (fun z => h' (c.symm z) * deriv g z) (c x) :=
    hh1'.mul hg.deriv.meromorphicAt
  have heq : (fun z => (h (c.symm z) + h' (c.symm z)) * deriv g z)
      = fun z => h (c.symm z) * deriv g z + h' (c.symm z) * deriv g z := by
    funext z; ring
  rw [heq, resAt_fun_add hha hha']

omit [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y] in
theorem resAtX_const_mul (c : ℂ) {F : X → Y} {h : X → ℂ} {x : X} :
    resAtX F (fun y => c * h y) x = c * resAtX F h x := by
  rw [resAtX_def, resAtX_def]
  have heq : (fun z => (c * h ((chartAt ℂ x).symm z)) *
      deriv (chartAt ℂ (F x) ∘ F ∘ (chartAt ℂ x).symm) z)
      = fun z => c * (h ((chartAt ℂ x).symm z) *
      deriv (chartAt ℂ (F x) ∘ F ∘ (chartAt ℂ x).symm) z) := by
    funext z; ring
  rw [heq, resAt_const_mul]

end RS.FormTrace
