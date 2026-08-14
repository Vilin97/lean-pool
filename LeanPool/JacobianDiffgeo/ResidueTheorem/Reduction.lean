/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.ResidueTheorem.P1Assembly
import LeanPool.JacobianDiffgeo.ResidueTheorem.Calibrated
import LeanPool.JacobianDiffgeo.FormTrace
import LeanPool.JacobianDiffgeo.CanonicalForms.Existence

/-!
# residue-theorem: the general-`X` reduction and THE residue theorem

Unit: residue-theorem (`docs/design/residue-theorem.md` §6, primary route per the orchestrator
addendum). This file closes Gap 2 of the previous partial delivery: the reduction of the
general compact-connected case to the `ℙ¹` base case (`P1Assembly.lean`) along a nonconstant
map `F := toP1 f' : X → ℙ¹`, via form-trace-tower's `resAtP1_trace_eq_sum` fed with the
CALIBRATED fiber stacks of `Calibrated.lean`.

**Resolution of the convention mismatch** flagged by the previous builder (`d f` vs `resAtX`'s
pullback convention at poles of `f`): no separate `MForm.ofPullback` object is needed. The two
conventions differ exactly by the target-chart transition `dz = -(w²)⁻¹ dw` at the `∞` fibre,
so the trace form is assembled from TWO coefficient functions of ONE pair `(h', H∞)`,
`H∞ := -(f')²·h'` (i.e. `h · F^*(dz)` re-expressed against `F^*(dw)`), matched fibre-by-fibre:

* `resAtX_toP1_eq_of_ord_nonneg` — over a finite value, `resAtX F h' x = (h • d φ).resAt x`;
* `resAtX_toP1_eq_of_ord_neg` — over `∞`, `resAtX F H∞ x = (h • d φ).resAt x`;
* the `ℙ¹`-side coefficients glue into a single `MFormData (OnePoint ℂ)` via
  `P1.formOfCoeFn` because `trace F H∞ = -(coeChart)²·(trace F h')` away from `∞`
  (`trace_const_mul_pullback` + fibre-wise honesty of `holoRepr`).

Main exports:
* `RS.residue_sum_eq_zero_of_exists_nonconstant` — **THE residue theorem**
  `∑ᶠ x, θ.resAt x = 0` on a compact connected surface admitting a nonconstant meromorphic
  function (canonical-forms D9 `exists_nonconstant_mero`'s exact export shape; now that
  `Jacobian/CanonicalForms/Existence.lean` has landed, the unconditional wrapper
  `RS.residue_sum_eq_zero` lives in `Jacobian/ResidueTheorem/Unconditional.lean`).
* `RS.MForm.sum_resAt_eq_zero_of_exists_nonconstant` — the serre-duality-tails consumption
  shape (`docs/requests/residue-theorem.md`): `∑ᶠ x, (f • θ).resAt x = 0`.

**`RS.MForm.d_ne_zero` moved to canonical-forms** (`Jacobian/CanonicalForms/Existence.lean`):
its proof used only canonical-forms/meromorphic-and-divisors machinery (no `ℙ¹`/trace/
calibration content), and canonical-forms itself needed exactly this fact for its own D9
existence chain (`exists_ne_zero_mform := ⟨MForm.d f, MForm.d_ne_zero hf⟩`). Since
residue-theorem is DOWNSTREAM of canonical-forms, keeping a second copy here would either
duplicate the ~90-line proof or require importing residue-theorem back into canonical-forms
(a cycle); canonical-forms is the clean home, so this file now imports it from there instead
(`import Jacobian.CanonicalForms.Existence`, above) — the call site below is unchanged.
-/

open scoped ContDiff Manifold OnePoint
open Set Filter Topology OnePoint Function

noncomputable section

namespace RS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### Reading `(h • d φ).resAt` in the chart -/

open scoped Classical in
omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- The residue of `h • d φ` at `x`, unfolded to the planar residue of the honest integrand
`h'·(f'∘chart⁻¹)'` (the `if`-guard of `MFormData.d`'s coefficient is discharged on the germ). -/
private theorem resAt_smul_d (h φ : ℳ X) (x : X) :
    (h • MForm.d φ).resAt x = RS.resAt (fun z => h.holoRepr ((chartAt ℂ x).symm z) *
      deriv (φ.holoRepr ∘ ⇑(chartAt ℂ x).symm) z) (chartAt ℂ x x) := by
  have hd : MForm.d φ = MForm.mk (MFormData.d φ) := rfl
  rw [hd, MForm.mero_smul_mk, MForm.resAt_mk]
  change RS.resAt ((MFormData.smul h (MFormData.d φ)).coeffAt x) (chartAt ℂ x x) = _
  apply RS.resAt_congr
  have htarget : ∀ᶠ z in 𝓝[≠] (chartAt ℂ x x), z ∈ (chartAt ℂ x).target :=
    eventually_nhdsWithin_of_eventually_nhds
      ((chartAt ℂ x).open_target.mem_nhds (mem_chart_target ℂ x))
  filter_upwards [htarget] with z hz
  change h.holoRepr ((chartAt ℂ x).symm z) *
      (if z ∈ (chartAt ℂ x).target then deriv (φ.holoRepr ∘ ⇑(chartAt ℂ x).symm) z else 0) = _
  rw [ite_eq_left hz]

/-! ### Honesty of `toP1 ∘ holoRepr` at nonnegative-order points -/

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- Pointwise: at a point of nonnegative order, `toP1 φ.holoRepr` is the literal coercion. -/
private theorem toP1_holoRepr_point (φ : ℳ X) {x : X} (hx : 0 ≤ ordAtX φ.holoRepr x) :
    MTrace.toP1 φ.holoRepr x = ((φ.holoRepr x : ℂ) : OnePoint ℂ) := by
  have hf₀ : MeromorphicOnX φ.holoRepr Set.univ :=
    MeroGermOn.meromorphicOnX_holoRepr isOpen_univ φ
  have hrepr : (MeroGermOn.mk φ.holoRepr hf₀).holoRepr = φ.holoRepr :=
    congrArg MeroGermOn.holoRepr (MeroGermOn.mk_holoRepr isOpen_univ φ)
  have h := MTrace.toP1_holoRepr_eq_coe_of_nonneg hf₀ (y := x) (by rw [hrepr]; exact hx)
  rwa [hrepr] at h

omit [CompactSpace X] [ConnectedSpace X] in
/-- Full-neighborhood version. -/
private theorem toP1_holoRepr_eventually (φ : ℳ X) {x : X} (hx : 0 ≤ ordAtX φ.holoRepr x) :
    MTrace.toP1 φ.holoRepr =ᶠ[𝓝 x] fun p => ((φ.holoRepr p : ℂ) : OnePoint ℂ) := by
  have hf₀ : MeromorphicOnX φ.holoRepr Set.univ :=
    MeroGermOn.meromorphicOnX_holoRepr isOpen_univ φ
  have hrepr : (MeroGermOn.mk φ.holoRepr hf₀).holoRepr = φ.holoRepr :=
    congrArg MeroGermOn.holoRepr (MeroGermOn.mk_holoRepr isOpen_univ φ)
  have h := MTrace.toP1_holoRepr_eventuallyEq_coe_of_nonneg hf₀ (y := x)
    (by rw [hrepr]; exact hx)
  rwa [hrepr] at h

/-! ### The two bridging lemmas: `resAtX` against `(h • d φ).resAt` -/

omit [CompactSpace X] [ConnectedSpace X] in
/-- **Bridge, finite-value case**: over a point where `φ` has nonnegative order (so
`F x = toP1 φ.holoRepr x` is finite and the target chart is `coeChart`), the pair-form residue
of `h.holoRepr` along `F` IS the residue of the 1-form `h • d φ`. -/
theorem resAtX_toP1_eq_of_ord_nonneg (φ h : ℳ X) {x : X}
    (hx : 0 ≤ ordAtX φ.holoRepr x) :
    FormTrace.resAtX (MTrace.toP1 φ.holoRepr) h.holoRepr x = (h • MForm.d φ).resAt x := by
  have hFx : MTrace.toP1 φ.holoRepr x = ((φ.holoRepr x : ℂ) : OnePoint ℂ) :=
    toP1_holoRepr_point φ hx
  have hFev : MTrace.toP1 φ.holoRepr =ᶠ[𝓝 x] fun p => ((φ.holoRepr p : ℂ) : OnePoint ℂ) :=
    toP1_holoRepr_eventually φ hx
  rw [FormTrace.resAtX_def, resAt_smul_d]
  apply RS.resAt_congr
  have hxe : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  have hEq : (⇑(chartAt ℂ (MTrace.toP1 φ.holoRepr x)) ∘ MTrace.toP1 φ.holoRepr ∘
      ⇑(chartAt ℂ x).symm) =ᶠ[𝓝 (chartAt ℂ x x)] (φ.holoRepr ∘ ⇑(chartAt ℂ x).symm) := by
    have h1 : ContinuousAt (chartAt ℂ x).symm (chartAt ℂ x x) :=
      (chartAt ℂ x).continuousAt_symm ((chartAt ℂ x).map_source hxe)
    have h2 : (chartAt ℂ x).symm (chartAt ℂ x x) = x := (chartAt ℂ x).left_inv hxe
    have hpull : ∀ᶠ w in 𝓝 (chartAt ℂ x x),
        MTrace.toP1 φ.holoRepr ((chartAt ℂ x).symm w)
          = ((φ.holoRepr ((chartAt ℂ x).symm w) : ℂ) : OnePoint ℂ) :=
      h1.eventually (h2 ▸ hFev)
    filter_upwards [hpull] with w hw
    change chartAt ℂ (MTrace.toP1 φ.holoRepr x)
      (MTrace.toP1 φ.holoRepr ((chartAt ℂ x).symm w)) = φ.holoRepr ((chartAt ℂ x).symm w)
    rw [hw, hFx, P1.chartAt_coe, P1.coeChart_apply_coe]
  have hDer := hEq.deriv
  filter_upwards [hDer.filter_mono nhdsWithin_le_nhds] with z hz
  show h.holoRepr ((chartAt ℂ x).symm z) *
      deriv (⇑(chartAt ℂ (MTrace.toP1 φ.holoRepr x)) ∘ MTrace.toP1 φ.holoRepr ∘
        ⇑(chartAt ℂ x).symm) z
    = h.holoRepr ((chartAt ℂ x).symm z) * deriv (φ.holoRepr ∘ ⇑(chartAt ℂ x).symm) z
  rw [hz]

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- **Bridge, `∞`-fibre case**: over a pole of `φ` (so `F x = ∞` and the target chart is
`invChart`, i.e. the pullback convention reads against `F^*(dw)` with `w = 1/z`), the pair-form
residue of the CORRECTED coefficient `H∞ := -(φ.holoRepr)²·h.holoRepr` along `F` is the residue
of `h • d φ` — the `dz = -(w²)⁻¹dw` transition exactly cancels. -/
theorem resAtX_toP1_eq_of_ord_neg (φ h : ℳ X) {x : X}
    (hx : ordAtX φ.holoRepr x < 0) :
    FormTrace.resAtX (MTrace.toP1 φ.holoRepr)
      (fun p => -(φ.holoRepr p ^ 2) * h.holoRepr p) x = (h • MForm.d φ).resAt x := by
  have hf'mero : MeromorphicOnX φ.holoRepr Set.univ :=
    MeroGermOn.meromorphicOnX_holoRepr isOpen_univ φ
  have hFx : MTrace.toP1 φ.holoRepr x = (∞ : OnePoint ℂ) := MTrace.toP1_eq_infty_iff.2 hx
  rw [FormTrace.resAtX_def, resAt_smul_d]
  apply RS.resAt_congr
  have hgmero : MeromorphicAt (φ.holoRepr ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) :=
    hf'mero x (Set.mem_univ x)
  have hordg : meromorphicOrderAt (φ.holoRepr ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) < 0 := hx
  have hne_top : meromorphicOrderAt (φ.holoRepr ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) ≠ ⊤ :=
    hordg.ne_top
  have hev_ne : ∀ᶠ w in 𝓝[≠] (chartAt ℂ x x), (φ.holoRepr ∘ ⇑(chartAt ℂ x).symm) w ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hgmero).1 hne_top
  have hev_an : ∀ᶠ w in 𝓝[≠] (chartAt ℂ x x),
      AnalyticAt ℂ (φ.holoRepr ∘ ⇑(chartAt ℂ x).symm) w :=
    hgmero.eventually_analyticAt
  -- `invChart ∘ F` reads as `(f')⁻¹`, eventually on the punctured neighborhood
  have hIeqX : ∀ᶠ p in 𝓝[≠] x,
      P1.invChart (MTrace.toP1 φ.holoRepr p) = (φ.holoRepr p)⁻¹ := by
    have hev_ord : ∀ᶠ p in 𝓝[≠] x, ordAtX φ.holoRepr p = 0 :=
      eventually_ordAtX_eq_zero (hf'mero x (Set.mem_univ x)) hne_top
    filter_upwards [hev_ord] with p hp
    rw [toP1_holoRepr_point φ (le_of_eq hp.symm), P1.invChart_apply_coe]
  have hIeq : ∀ᶠ w in 𝓝[≠] (chartAt ℂ x x),
      (⇑P1.invChart ∘ MTrace.toP1 φ.holoRepr ∘ ⇑(chartAt ℂ x).symm) w
        = ((φ.holoRepr ∘ ⇑(chartAt ℂ x).symm) w)⁻¹ := by
    have h1 := eventually_nhdsNE_iff_comp_chart
      (p := fun p => P1.invChart (MTrace.toP1 φ.holoRepr p) = (φ.holoRepr p)⁻¹) |>.1 hIeqX
    filter_upwards [h1] with w hw
    exact hw
  rw [Filter.eventually_iff, mem_nhdsWithin] at hIeq
  obtain ⟨U, hUopen, hcU, hUsub⟩ := hIeq
  have hUopen' : IsOpen (U ∩ {(chartAt ℂ x x)}ᶜ) := hUopen.inter isOpen_compl_singleton
  have hUev : ∀ᶠ w in 𝓝[≠] (chartAt ℂ x x), w ∈ U ∩ {(chartAt ℂ x x)}ᶜ := by
    rw [Filter.eventually_iff, mem_nhdsWithin]
    exact ⟨U, hUopen, hcU, fun w hw => hw⟩
  filter_upwards [hev_ne, hev_an, hUev] with w hwne hwan hwU
  have hloc : (⇑(chartAt ℂ (MTrace.toP1 φ.holoRepr x)) ∘ MTrace.toP1 φ.holoRepr ∘
      ⇑(chartAt ℂ x).symm) =ᶠ[𝓝 w]
      fun v => ((φ.holoRepr ∘ ⇑(chartAt ℂ x).symm) v)⁻¹ := by
    filter_upwards [hUopen'.mem_nhds hwU] with v hv
    change chartAt ℂ (MTrace.toP1 φ.holoRepr x)
      (MTrace.toP1 φ.holoRepr ((chartAt ℂ x).symm v)) = _
    rw [hFx, P1.chartAt_infty]
    exact hUsub hv
  have hderiv_eq : deriv (⇑(chartAt ℂ (MTrace.toP1 φ.holoRepr x)) ∘ MTrace.toP1 φ.holoRepr ∘
      ⇑(chartAt ℂ x).symm) w
      = deriv (fun v => ((φ.holoRepr ∘ ⇑(chartAt ℂ x).symm) v)⁻¹) w := hloc.deriv_eq
  have hderiv_inv : deriv (fun v => ((φ.holoRepr ∘ ⇑(chartAt ℂ x).symm) v)⁻¹) w
      = -deriv (φ.holoRepr ∘ ⇑(chartAt ℂ x).symm) w /
          ((φ.holoRepr ∘ ⇑(chartAt ℂ x).symm) w) ^ 2 :=
    deriv_fun_inv'' hwan.differentiableAt hwne
  change (fun p => -(φ.holoRepr p ^ 2) * h.holoRepr p) ((chartAt ℂ x).symm w) *
      deriv (⇑(chartAt ℂ (MTrace.toP1 φ.holoRepr x)) ∘ MTrace.toP1 φ.holoRepr ∘
        ⇑(chartAt ℂ x).symm) w
    = h.holoRepr ((chartAt ℂ x).symm w) * deriv (φ.holoRepr ∘ ⇑(chartAt ℂ x).symm) w
  rw [hderiv_eq, hderiv_inv]
  have hg0 : φ.holoRepr ((chartAt ℂ x).symm w) ≠ 0 := hwne
  simp only [Function.comp_apply]
  field_simp

/-! ### `MForm.d_ne_zero` — now imported from `canonical-forms`

Moved to `Jacobian/CanonicalForms/Existence.lean` (see the module docstring above): the proof
never used any residue-theorem-specific content, and canonical-forms' own D9 existence chain
needed exactly this fact. `import Jacobian.CanonicalForms.Existence` (above) brings it into
scope unchanged; the call site below (`MForm.d_ne_zero hφ`) is untouched. -/

/-! ### THE residue theorem -/

/-- The `∞`-chart reading of a meromorphic function on `ℂ` is again meromorphic. Split out of
`residue_sum_eq_zero_of_exists_nonconstant` to keep that proof under the 200-line size we hold
ourselves to. -/
private theorem meromorphicOn_invChart_reading {R_T G : ℂ → ℂ}
    (hRT : MeromorphicOn R_T Set.univ) (hInfMeroT : MeromorphicAt G 0)
    (hgermInf : (fun w : ℂ => -(w ^ 2)⁻¹ * R_T w⁻¹) =ᶠ[𝓝[≠] (0 : ℂ)] G) :
    MeromorphicOn (fun w : ℂ => -(w ^ 2)⁻¹ * R_T w⁻¹) Set.univ := by
  intro w₀ _
  by_cases hw₀ : w₀ = 0
  · subst hw₀
    exact hInfMeroT.congr hgermInf.symm
  · have h1 : MeromorphicAt (fun w : ℂ => -(w ^ 2)⁻¹) w₀ :=
      ((MeromorphicAt.id w₀).pow 2).inv.neg
    have hτ : AnalyticAt ℂ (Inv.inv : ℂ → ℂ) w₀ := analyticAt_id.inv hw₀
    have hτ' : deriv (Inv.inv : ℂ → ℂ) w₀ ≠ 0 := by
      rw [deriv_inv]
      exact neg_ne_zero.2 (inv_ne_zero (pow_ne_zero 2 hw₀))
    have h2 : MeromorphicAt (R_T ∘ Inv.inv) w₀ :=
      (meromorphicAt_comp_iff_of_deriv_ne_zero hτ hτ').2 (hRT w₀⁻¹ (Set.mem_univ _))
    exact h1.mul h2

open scoped Classical in
/-- **THE residue theorem** (Forster 10.21 / Miranda VI eq. 3.2, blueprint headline
`∑_p Res_p(θ) = 0`): on a compact connected Riemann surface admitting a nonconstant meromorphic
function (the exact shape of canonical-forms D9's `exists_nonconstant_mero`), the residues of
any meromorphic 1-form sum to zero. The unconditional statement (`hex` discharged by
`exists_nonconstant_mero` itself, now that `Existence.lean` has landed) is
`RS.residue_sum_eq_zero` in `Jacobian/ResidueTheorem/Unconditional.lean`.

Proved by the trace route (design §6): write `θ = h • d φ` (D8, one-dimensionality over
`ℳ(X)`), push down along `F := toP1 φ.holoRepr` fibre-by-fibre through calibrated fiber stacks
(`resAtP1_trace_eq_sum`), assemble the trace data into a single meromorphic 1-form on `ℙ¹` via
`formOfCoeFn`, and conclude by the `ℙ¹` base case (`P1.sum_resAt_eq_zero`). -/
theorem residue_sum_eq_zero_of_exists_nonconstant
    (hex : ∃ f : ℳ X, ∀ c : ℂ, f ≠ algebraMap ℂ (ℳ X) c) (θ : MForm X) :
    ∑ᶠ x, θ.resAt x = 0 := by
  obtain ⟨φ, hφ⟩ := hex
  have hd0 : MForm.d φ ≠ 0 := MForm.d_ne_zero hφ
  obtain ⟨h, rfl⟩ := MForm.exists_smul_eq hd0 θ
  -- the map to ℙ¹
  have hf'mero : MeromorphicOnX φ.holoRepr Set.univ :=
    MeroGermOn.meromorphicOnX_holoRepr isOpen_univ φ
  set F : X → OnePoint ℂ := MTrace.toP1 φ.holoRepr with hF_def
  have hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F := MTrace.toP1_contMDiff hf'mero
  have hncX : MTrace.NotEventuallyConstX φ.holoRepr := by
    intro c hcon
    apply hφ c
    rw [← MeroGermOn.mk_holoRepr isOpen_univ φ, MeroGermOn.algebraMap_mk]
    apply MeroGermOn.mk_eq_mk.2
    have h1 : ∀ᶠ p in Filter.codiscrete X, φ.holoRepr p - c = 0 := hcon
    filter_upwards [h1] with p hp
    exact sub_eq_zero.1 hp
  have hne : ¬ ∃ c, ∀ x, F x = c := MTrace.toP1_not_const hf'mero hncX
  -- the two trace coefficients
  have hh'mero : MeromorphicOnX h.holoRepr Set.univ :=
    MeroGermOn.meromorphicOnX_holoRepr isOpen_univ h
  set Hinf : X → ℂ := fun p => -(φ.holoRepr p ^ 2) * h.holoRepr p with hHinf_def
  have hHmero : MeromorphicOnX Hinf Set.univ := fun p hp =>
    (((hf'mero p hp).pow 2).neg).mul (hh'mero p hp)
  -- the ℙ¹-side coefficient function and its two-chart meromorphy
  set R_T : ℂ → ℂ := fun z => MTrace.trace F h.holoRepr ((z : ℂ) : OnePoint ℂ) with hRT_def
  have hRT : MeromorphicOn R_T Set.univ := by
    intro z _
    have h1 : MeromorphicAtX (MTrace.trace F h.holoRepr) ((z : ℂ) : OnePoint ℂ) :=
      MTrace.meromorphicAtX_trace hF hne hh'mero _
    have h2 := (meromorphicAtX_iff_of_mem_source P1.coeChart_mem_maximalAtlas
      (show ((z : ℂ) : OnePoint ℂ) ∈ P1.coeChart.source by
        rw [P1.coeChart_source]
        exact fun hcon => OnePoint.coe_ne_infty z hcon)).1 h1
    rw [P1.coeChart_apply_coe] at h2
    have hfun : MTrace.trace F h.holoRepr ∘ ⇑P1.coeChart.symm = R_T := by
      funext w
      simp only [Function.comp_apply, P1.coeChart_symm_apply]
      rfl
    rwa [hfun] at h2
  -- the trace of the corrected coefficient computes the ∞-chart reading of `R_T`
  have htr : ∀ v : ℂ,
      MTrace.trace F Hinf ((v : ℂ) : OnePoint ℂ) = -(v ^ 2) * R_T v := by
    intro v
    set hg : OnePoint ℂ → ℂ := fun y => -(P1.coeChart y ^ 2) with hg_def
    have h1 : MTrace.trace F Hinf ((v : ℂ) : OnePoint ℂ)
        = MTrace.trace F (fun p => hg (F p) * h.holoRepr p) ((v : ℂ) : OnePoint ℂ) := by
      rw [MTrace.trace_eq_finsum' hF hne, MTrace.trace_eq_finsum' hF hne]
      apply finsum_mem_congr rfl
      intro p hp
      have hFp : F p = ((v : ℂ) : OnePoint ℂ) := hp
      have hord : 0 ≤ ordAtX φ.holoRepr p := by
        by_contra hcon
        have h2 : F p = (∞ : OnePoint ℂ) := MTrace.toP1_eq_infty_iff.2 (not_le.1 hcon)
        rw [hFp] at h2
        exact OnePoint.coe_ne_infty v h2
      have hcoe : F p = ((φ.holoRepr p : ℂ) : OnePoint ℂ) := toP1_holoRepr_point φ hord
      change Hinf p = hg (F p) * h.holoRepr p
      rw [hHinf_def, hg_def]
      simp only
      rw [hcoe, P1.coeChart_apply_coe]
    have h2 := congrFun (FormTrace.trace_const_mul_pullback hF hne (g := hg) h.holoRepr)
      (((v : ℂ) : OnePoint ℂ))
    rw [h1, h2, hg_def]
    simp only
    rw [P1.coeChart_apply_coe, hRT_def]
  -- the ∞-chart reading of `R_T` is the trace of `Hinf`, as germs at 0
  have hgermInf : (fun w : ℂ => -(w ^ 2)⁻¹ * R_T w⁻¹) =ᶠ[𝓝[≠] (0 : ℂ)]
      MTrace.trace F Hinf ∘ ⇑P1.invChart.symm := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    have hw0 : w ≠ 0 := hw
    change -(w ^ 2)⁻¹ * R_T w⁻¹ = MTrace.trace F Hinf (P1.invChart.symm w)
    rw [P1.invChart_symm_apply, P1.inversion_coe hw0, htr w⁻¹, inv_pow]
  have hInfMeroT : MeromorphicAt (MTrace.trace F Hinf ∘ ⇑P1.invChart.symm) 0 := by
    have h1 : MeromorphicAtX (MTrace.trace F Hinf) (∞ : OnePoint ℂ) :=
      MTrace.meromorphicAtX_trace hF hne hHmero _
    have h2 := (meromorphicAtX_iff_of_mem_source P1.invChart_mem_maximalAtlas
      (show (∞ : OnePoint ℂ) ∈ P1.invChart.source by
        rw [P1.invChart_source]
        simp)).1 h1
    rwa [P1.invChart_apply_infty] at h2
  have hRT' := meromorphicOn_invChart_reading hRT hInfMeroT hgermInf
  -- the trace form on ℙ¹
  set θT : MFormData (OnePoint ℂ) := P1.formOfCoeFn R_T hRT hRT' with hθT_def
  -- THE per-fibre identity
  have key : ∀ y₀ : OnePoint ℂ, (MForm.mk θT).resAt y₀
      = ∑ᶠ x ∈ F ⁻¹' {y₀}, (h • MForm.d φ).resAt x := by
    intro y₀
    induction y₀ using OnePoint.rec with
    | infty =>
      obtain ⟨S, hScal⟩ := exists_fiberStack_translated hF hne (∞ : OnePoint ℂ)
      have hcal : ∀ i : Fin S.n, ∀ y ∈ (S.A i).e'.source,
          (S.A i).e' y = chartAt ℂ (∞ : OnePoint ℂ) y
            - chartAt ℂ (∞ : OnePoint ℂ) (∞ : OnePoint ℂ) := fun i y _ => hScal i y
      have hsum_eq : ∑ᶠ x ∈ F ⁻¹' {(∞ : OnePoint ℂ)}, (h • MForm.d φ).resAt x
          = ∑ i, (h • MForm.d φ).resAt (S.pt i) := by
        rw [← S.range_pt, finsum_mem_range S.pt_injective, finsum_eq_sum_of_fintype]
      have hL : (MForm.mk θT).resAt (∞ : OnePoint ℂ)
          = RS.resAt (fun w => -(w ^ 2)⁻¹ * R_T w⁻¹) 0 := by
        change RS.resAt (θT.coeffAt (∞ : OnePoint ℂ))
          (chartAt ℂ (∞ : OnePoint ℂ) (∞ : OnePoint ℂ)) = _
        rw [P1.chartAt_infty, P1.invChart_apply_infty]
        rfl
      have hP1 : FormTrace.resAtP1 (MTrace.trace F Hinf) (∞ : OnePoint ℂ)
          = RS.resAt (MTrace.trace F Hinf ∘ ⇑P1.invChart.symm) 0 := by
        rw [FormTrace.resAtP1_def, P1.chartAt_infty, P1.invChart_apply_infty]
      rw [hsum_eq, hL, RS.resAt_congr hgermInf, ← hP1,
        FormTrace.resAtP1_trace_eq_sum hF hne hHmero S hcal]
      apply Finset.sum_congr rfl
      intro i _
      have hFi : F (S.pt i) = (∞ : OnePoint ℂ) := S.maps_pt_eq i
      have hord : ordAtX φ.holoRepr (S.pt i) < 0 := MTrace.toP1_eq_infty_iff.1 hFi
      exact resAtX_toP1_eq_of_ord_neg φ h hord
    | coe a =>
      obtain ⟨S, hScal⟩ := exists_fiberStack_translated hF hne ((a : ℂ) : OnePoint ℂ)
      have hcal : ∀ i : Fin S.n, ∀ y ∈ (S.A i).e'.source,
          (S.A i).e' y = chartAt ℂ ((a : ℂ) : OnePoint ℂ) y
            - chartAt ℂ ((a : ℂ) : OnePoint ℂ) ((a : ℂ) : OnePoint ℂ) := fun i y _ => hScal i y
      have hsum_eq : ∑ᶠ x ∈ F ⁻¹' {((a : ℂ) : OnePoint ℂ)}, (h • MForm.d φ).resAt x
          = ∑ i, (h • MForm.d φ).resAt (S.pt i) := by
        rw [← S.range_pt, finsum_mem_range S.pt_injective, finsum_eq_sum_of_fintype]
      have hL : (MForm.mk θT).resAt ((a : ℂ) : OnePoint ℂ) = RS.resAt R_T a := by
        change RS.resAt (θT.coeffAt (((a : ℂ) : OnePoint ℂ)))
          (chartAt ℂ (((a : ℂ) : OnePoint ℂ)) (((a : ℂ) : OnePoint ℂ))) = _
        rw [P1.chartAt_coe, P1.coeChart_apply_coe]
        rfl
      have hP1 : FormTrace.resAtP1 (MTrace.trace F h.holoRepr) ((a : ℂ) : OnePoint ℂ)
          = RS.resAt R_T a := by
        rw [FormTrace.resAtP1_def, P1.chartAt_coe, P1.coeChart_apply_coe]
        have hfun : MTrace.trace F h.holoRepr ∘ ⇑P1.coeChart.symm = R_T := by
          funext w
          simp only [Function.comp_apply, P1.coeChart_symm_apply]
          rfl
        rw [hfun]
      rw [hsum_eq, hL, ← hP1, FormTrace.resAtP1_trace_eq_sum hF hne hh'mero S hcal]
      apply Finset.sum_congr rfl
      intro i _
      have hFi : F (S.pt i) = ((a : ℂ) : OnePoint ℂ) := S.maps_pt_eq i
      have hord : 0 ≤ ordAtX φ.holoRepr (S.pt i) := by
        by_contra hcon
        have h2 : F (S.pt i) = (∞ : OnePoint ℂ) := MTrace.toP1_eq_infty_iff.2 (not_le.1 hcon)
        rw [hFi] at h2
        exact OnePoint.coe_ne_infty a h2
      exact resAtX_toP1_eq_of_ord_nonneg φ h hord
  -- assemble: support bookkeeping + the ℙ¹ base case
  have hsupp_fin : (Function.support fun x : X => (h • MForm.d φ).resAt x).Finite :=
    MForm.finite_support_resAt _
  set Yfin : Finset (OnePoint ℂ) :=
    (hsupp_fin.image F).toFinset ∪ {(∞ : OnePoint ℂ)} with hY_def
  have hkey0 : ∀ y₀ : OnePoint ℂ, y₀ ∉ Yfin → (MForm.mk θT).resAt y₀ = 0 := by
    intro y₀ hy₀
    rw [key y₀]
    apply finsum_mem_of_eqOn_zero
    intro x hx
    by_contra hne0
    apply hy₀
    apply Finset.mem_union_left
    rw [Set.Finite.mem_toFinset]
    exact ⟨x, Function.mem_support.2 hne0, hx⟩
  have hbase := P1.sum_resAt_eq_zero (MForm.mk θT)
  have hstep1 : ∑ᶠ y, (MForm.mk θT).resAt y = ∑ y ∈ Yfin, (MForm.mk θT).resAt y := by
    apply finsum_eq_finsetSum_of_support_subset
    intro y hy
    rw [Function.mem_support] at hy
    by_contra hcon
    exact hy (hkey0 y hcon)
  have hdisjY : (↑Yfin : Set (OnePoint ℂ)).PairwiseDisjoint (fun y => F ⁻¹' {y}) :=
    fun y₁ _ y₂ _ hne12 => Disjoint.preimage F (disjoint_singleton.2 hne12)
  have hfib_fin : ∀ y ∈ (↑Yfin : Set (OnePoint ℂ)), (F ⁻¹' {y}).Finite :=
    fun y _ => fiber_finite hF hne y
  have hsub : Function.support (fun x : X => (h • MForm.d φ).resAt x)
      ⊆ ⋃ y ∈ (↑Yfin : Set (OnePoint ℂ)), F ⁻¹' {y} := by
    intro x hx
    have h1 : F x ∈ (↑Yfin : Set (OnePoint ℂ)) := by
      apply Finset.mem_coe.2
      apply Finset.mem_union_left
      rw [Set.Finite.mem_toFinset]
      exact ⟨x, hx, rfl⟩
    have h2 : x ∈ F ⁻¹' {F x} := rfl
    exact Set.mem_biUnion h1 h2
  have hstep4 : ∑ᶠ x ∈ ⋃ y ∈ (↑Yfin : Set (OnePoint ℂ)), F ⁻¹' {y},
      (h • MForm.d φ).resAt x = ∑ᶠ x, (h • MForm.d φ).resAt x := by
    rw [← finsum_mem_inter_support (fun x : X => (h • MForm.d φ).resAt x)
        (⋃ y ∈ (↑Yfin : Set (OnePoint ℂ)), F ⁻¹' {y}),
      ← finsum_mem_univ (fun x : X => (h • MForm.d φ).resAt x),
      ← finsum_mem_inter_support (fun x : X => (h • MForm.d φ).resAt x) Set.univ,
      Set.univ_inter, Set.inter_eq_right.2 hsub]
  calc ∑ᶠ x, (h • MForm.d φ).resAt x
      = ∑ᶠ x ∈ ⋃ y ∈ (↑Yfin : Set (OnePoint ℂ)), F ⁻¹' {y},
          (h • MForm.d φ).resAt x := hstep4.symm
    _ = ∑ᶠ y ∈ (↑Yfin : Set (OnePoint ℂ)), ∑ᶠ x ∈ F ⁻¹' {y}, (h • MForm.d φ).resAt x :=
        finsum_mem_biUnion hdisjY Yfin.finite_toSet hfib_fin
    _ = ∑ y ∈ Yfin, ∑ᶠ x ∈ F ⁻¹' {y}, (h • MForm.d φ).resAt x :=
        finsum_mem_coe_finset _ _
    _ = ∑ y ∈ Yfin, (MForm.mk θT).resAt y :=
        Finset.sum_congr rfl fun y _ => (key y).symm
    _ = ∑ᶠ y, (MForm.mk θT).resAt y := hstep1.symm
    _ = 0 := hbase

/-- The serre-duality-tails consumption shape (`docs/requests/residue-theorem.md`,
`sum_resAt_eq_zero`): the residues of `f • θ` sum to zero, for any global meromorphic function
`f : ℳ X` and meromorphic 1-form `θ : MForm X`. This is the well-definedness input of the
Serre-pairing residue functional (`RS.TailDuality.pairT_alpha`, serre-duality-tails design §6
P3). Hypothesis-gated exactly like the main theorem; instantiate `hex` with canonical-forms
D9's `exists_nonconstant_mero` once `CanonicalForms/Existence.lean` lands. -/
theorem MForm.sum_resAt_eq_zero_of_exists_nonconstant
    (hex : ∃ f : ℳ X, ∀ c : ℂ, f ≠ algebraMap ℂ (ℳ X) c) (f : ℳ X) (θ : MForm X) :
    ∑ᶠ x, (f • θ).resAt x = 0 :=
  residue_sum_eq_zero_of_exists_nonconstant hex (f • θ)

/-- `Finset`-flexible corollary (the design §2 shape): the residues sum to zero over any finite
set containing the support of `resAt`. -/
theorem residueTheorem_of_exists_nonconstant
    (hex : ∃ f : ℳ X, ∀ c : ℂ, f ≠ algebraMap ℂ (ℳ X) c) (θ : MForm X)
    {S : Finset X} (hS : Function.support (fun x => θ.resAt x) ⊆ (S : Set X)) :
    ∑ x ∈ S, θ.resAt x = 0 := by
  rw [← finsum_eq_finsetSum_of_support_subset _ hS]
  exact residue_sum_eq_zero_of_exists_nonconstant hex θ

end RS
