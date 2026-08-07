/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.JacFunctorial.TraceCoeff
import LeanPool.JacobianDiffgeo.JacFunctorial.Density
import LeanPool.JacobianDiffgeo.MeromorphicTrace.FunctionTrace
import LeanPool.JacobianDiffgeo.Forms.OfCoeffs
import LeanPool.JacobianDiffgeo.JacFunctorial.Pullback

/-!
# `Form1.trace` — the fibrewise trace of a holomorphic 1-form (jacobian-functoriality §6)

Unit: jacobian-functoriality. For a nonconstant holomorphic `f : X → Y` between Riemann surfaces
(`X` compact connected), the trace `Tr_f η ∈ Form1 Y` of `η ∈ Form1 X`: in the target chart at
`y`, its coefficient is the sum over the fibre stack at `y` of the *repaired* Jacobian-weighted
planar traces (`RS.traceCoeff`, `TraceCoeff.lean`) of `η`'s chart coefficients, transported by
the branch/chart transition derivatives.

Main declarations:
* `RS.stackAt`/`RS.traceChart`/`RS.branchTrans`/`RS.traceCoeffFun` — the coefficient data over
  the chart family `ι := Y` (preferred charts restricted to the stack neighborhoods `S.V`).
* `RS.qCoeff f η e₀ x = (deriv (e₀ ∘ f ∘ (chartAt x).symm))⁻¹ * coeffAt x η` — the canonical
  (stack-free) per-fibre-point coefficient of the trace; `RS.traceCoeffFun_eq_qSum` identifies
  the defining coefficient with `∑ᶠ x ∈ f⁻¹{yhat}, qCoeff …` away from the chart center (well-
  definedness), and `RS.qSum_trans` is its chart-transition law — together these give `compat`
  on a dense subset of each chart overlap, extended to the whole overlap by continuity
  (`ContinuousOn.eqOn_of_subset_closure`, `Density.lean`).
* `RS.traceForm hf hne η : Form1 Y` (via `Form1.ofCoeffs`) and the challenge-facing
  **`RS.Form1.trace (f : X → Y) (hf) : Form1 X →ₗ[ℂ] Form1 Y`** (zero for constant `f`).
* `RS.coeffAt_traceForm` (the preferred-chart evaluation) and
  `RS.coeffAt_traceForm_of_isRegularValue` (the regular-value formula, feed for the projection
  formula / functoriality laws / the trace–period relation).
-/

open scoped ContDiff Manifold Topology
open Set Filter Metric IsManifold
open RS.FormTrace RS.MTrace

noncomputable section

namespace RS

/-! ### Planar helper: congruence of `traceZk` on the root set -/

theorem MTrace.traceZk_congr_root {g g' : ℂ → ℂ} {k : ℕ} {w : ℂ}
    (h : ∀ v, v ^ k = w → g v = g' v) :
    RS.MTrace.traceZk g k w = RS.MTrace.traceZk g' k w := by
  rw [RS.MTrace.traceZk_def, RS.MTrace.traceZk_def]
  exact finsum_mem_congr rfl fun v hv => h v hv

/-! ### Generic chart helpers -/

section ChartHelpers

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]

/-- Chain rule for `deriv` through an eventual factorization (local copy of `Pullback.lean`'s
private helper). -/
theorem deriv_eq_of_eventuallyEq_comp' {g h k : ℂ → ℂ} {z : ℂ}
    (hg : DifferentiableAt ℂ g (h z)) (hh : DifferentiableAt ℂ h z)
    (heq : k =ᶠ[𝓝 z] g ∘ h) : deriv k z = deriv g (h z) * deriv h z :=
  ((hg.hasDerivAt.comp z hh.hasDerivAt).congr_of_eventuallyEq heq).deriv

omit [IsManifold 𝓘(ℂ, ℂ) ω M] in
/-- The two transition derivatives between overlapping maximal-atlas charts are mutually
inverse. -/
theorem deriv_transition_mul {e e' : OpenPartialHomeomorph M ℂ}
    (he : e ∈ maximalAtlas 𝓘(ℂ) ω M) (he' : e' ∈ maximalAtlas 𝓘(ℂ) ω M)
    {q : M} (hq : q ∈ e.source) (hq' : q ∈ e'.source) :
    deriv (⇑e' ∘ ⇑e.symm) (e q) * deriv (⇑e ∘ ⇑e'.symm) (e' q) = 1 := by
  have hτ : AnalyticAt ℂ (⇑e' ∘ ⇑e.symm) (e q) := analyticAt_transition_fun he he' hq hq'
  have hσ : AnalyticAt ℂ (⇑e ∘ ⇑e'.symm) (e' q) := analyticAt_transition_fun he' he hq' hq
  have hid : (⇑e' ∘ ⇑e.symm) ∘ (⇑e ∘ ⇑e'.symm) =ᶠ[𝓝 (e' q)] id := by
    have h1 : e'.target ∈ 𝓝 (e' q) := e'.open_target.mem_nhds (e'.map_source hq')
    have h2 : ⇑e'.symm ⁻¹' e.source ∈ 𝓝 (e' q) := by
      apply (e'.continuousAt_symm (e'.map_source hq')).preimage_mem_nhds
      rw [e'.left_inv hq']
      exact e.open_source.mem_nhds hq
    filter_upwards [h1, h2] with z hz1 hz2
    simp only [Function.comp_apply, id_eq]
    rw [e.left_inv hz2, e'.right_inv hz1]
  have hval : (⇑e ∘ ⇑e'.symm) (e' q) = e q := by
    simp only [Function.comp_apply]
    rw [e'.left_inv hq']
  have hchain : deriv ((⇑e' ∘ ⇑e.symm) ∘ (⇑e ∘ ⇑e'.symm)) (e' q)
      = deriv (⇑e' ∘ ⇑e.symm) (e q) * deriv (⇑e ∘ ⇑e'.symm) (e' q) := by
    have h := deriv_eq_of_eventuallyEq_comp' (g := ⇑e' ∘ ⇑e.symm) (h := ⇑e ∘ ⇑e'.symm)
      (z := e' q) (by rw [hval]; exact hτ.differentiableAt) hσ.differentiableAt
      EventuallyEq.rfl
    rwa [hval] at h
  rw [← hchain, hid.deriv_eq, deriv_id]

/-- A nonempty open planar set is inside the closure of its complement of any finite set. -/
theorem open_subset_closure_diff {U : Set ℂ} (hU : IsOpen U) {s : Set ℂ} (hs : s.Finite) :
    U ⊆ closure (U \ s) := by
  intro z hz
  rw [mem_closure_iff_nhdsWithin_neBot]
  have hs' : IsClosed (s \ {z}) := (hs.subset sdiff_subset).isClosed
  have hmem : U ∩ (s \ {z})ᶜ ∈ 𝓝 z :=
    Filter.inter_mem (hU.mem_nhds hz) (hs'.isOpen_compl.mem_nhds (by simp))
  have h1 : 𝓝[({z}ᶜ : Set ℂ) ∩ (U ∩ (s \ {z})ᶜ)] z = 𝓝[({z}ᶜ : Set ℂ)] z :=
    nhdsWithin_inter_of_mem' (mem_nhdsWithin_of_mem_nhds hmem)
  have hsub : ({z}ᶜ : Set ℂ) ∩ (U ∩ (s \ {z})ᶜ) ⊆ U \ s := by
    rintro u ⟨hu1, hu2, hu3⟩
    refine ⟨hu2, fun hus => hu3 ⟨hus, ?_⟩⟩
    simpa using hu1
  have hne : (𝓝[({z}ᶜ : Set ℂ) ∩ (U ∩ (s \ {z})ᶜ)] z).NeBot := by
    rw [h1]
    exact RS.nhdsNE_neBot z
  exact hne.mono (nhdsWithin_mono z hsub)

end ChartHelpers

/-! ### The trace coefficient data -/

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {f : X → Y}

/-- The canonical fibre stack at `y` (a fixed choice, shared by every construction below). -/
def stackAt (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hne : ¬ ∃ c, ∀ x, f x = c) (y : Y) :
    RS.FiberStack f y :=
  (RS.exists_fiberStack hf hne y).some

variable (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hne : ¬ ∃ c, ∀ x, f x = c)

/-- The chart of the trace's coefficient data at index `y`: the preferred chart at `y`,
restricted to the stack neighborhood `(stackAt hf hne y).V`. -/
def traceChart (y : Y) : OpenPartialHomeomorph Y ℂ :=
  (chartAt ℂ y).restr (stackAt hf hne y).V

@[simp] theorem traceChart_coe (y : Y) : ⇑(traceChart hf hne y) = ⇑(chartAt ℂ y) := rfl

@[simp] theorem traceChart_symm_coe (y : Y) :
    ⇑(traceChart hf hne y).symm = ⇑(chartAt ℂ y).symm := rfl

theorem traceChart_source (y : Y) :
    (traceChart hf hne y).source = (chartAt ℂ y).source ∩ (stackAt hf hne y).V := by
  unfold traceChart
  rw [OpenPartialHomeomorph.restr_source, (stackAt hf hne y).isOpen_V.interior_eq]

theorem traceChart_target_eq (y : Y) :
    (traceChart hf hne y).target
      = (chartAt ℂ y).target ∩ ⇑(chartAt ℂ y).symm ⁻¹' (stackAt hf hne y).V := by
  unfold traceChart
  rw [OpenPartialHomeomorph.restr_target, (stackAt hf hne y).isOpen_V.interior_eq]

theorem mem_traceChart_source_self (y : Y) : y ∈ (traceChart hf hne y).source := by
  rw [traceChart_source]
  exact ⟨mem_chart_source ℂ y, (stackAt hf hne y).mem_V⟩

theorem traceChart_mem_maximalAtlas (y : Y) :
    traceChart hf hne y ∈ maximalAtlas 𝓘(ℂ) ω Y :=
  restr_mem_maximalAtlas (contDiffGroupoid ω 𝓘(ℂ)) (chart_mem_maximalAtlas y)
    (stackAt hf hne y).isOpen_V

/-- The transition from the preferred chart's coordinate at `y` to the `i`-th branch's target
chart coordinate. -/
def branchTrans (y : Y) (i : Fin (stackAt hf hne y).n) : ℂ → ℂ :=
  ⇑((stackAt hf hne y).A i).e' ∘ ⇑(chartAt ℂ y).symm

theorem analyticAt_branchTrans (y : Y) {w : ℂ} (hw : w ∈ (traceChart hf hne y).target)
    (i : Fin (stackAt hf hne y).n) : AnalyticAt ℂ (branchTrans hf hne y i) w := by
  rw [traceChart_target_eq] at hw
  exact analyticAt_trans ((stackAt hf hne y).A i).mem_maximalAtlas'
    (chart_mem_maximalAtlas y) hw.1 ((stackAt hf hne y).V_subset i hw.2)

theorem branchTrans_mem_ball (y : Y) {w : ℂ} (hw : w ∈ (traceChart hf hne y).target)
    (i : Fin (stackAt hf hne y).n) :
    branchTrans hf hne y i w ∈ Metric.ball 0
      (((stackAt hf hne y).A i).radius ^ multiplicity f ((stackAt hf hne y).pt i)) := by
  rw [traceChart_target_eq] at hw
  exact (stackAt hf hne y).map_V_mem_ball i _ hw.2

/-- The coefficient of the trace in the chart at index `y`: the branch-transported sum of the
repaired planar trace coefficients of `η`'s stack-chart coefficients. -/
def traceCoeffFun (η : Form1 X) (y : Y) : ℂ → ℂ := fun w =>
  ∑ i, deriv (branchTrans hf hne y i) w
    * traceCoeff (coeffIn ((stackAt hf hne y).A i).e η)
        (multiplicity f ((stackAt hf hne y).pt i)) (branchTrans hf hne y i w)

theorem analyticAt_coeffIn_stack_zero (η : Form1 X) (y : Y) (i : Fin (stackAt hf hne y).n) :
    AnalyticAt ℂ (coeffIn ((stackAt hf hne y).A i).e η) 0 := by
  apply η.analyticOnNhd_coeffIn ((stackAt hf hne y).A i).mem_maximalAtlas
  rw [((stackAt hf hne y).A i).target_eq]
  exact Metric.mem_ball_self ((stackAt hf hne y).radius_pos i)

/-- Analyticity of the trace coefficient on the whole (restricted) chart target — including
across branch points (the previous builder's blocker, discharged by
`RS.analyticOnNhd_traceCoeff`). -/
theorem analyticOnNhd_traceCoeffFun (η : Form1 X) (y : Y) :
    AnalyticOnNhd ℂ (traceCoeffFun hf hne η y) (traceChart hf hne y).target := by
  intro w hw
  apply Finset.analyticAt_fun_sum
  intro i _
  have hψ : AnalyticAt ℂ (branchTrans hf hne y i) w := analyticAt_branchTrans hf hne y hw i
  have htc : AnalyticAt ℂ
      (traceCoeff (coeffIn ((stackAt hf hne y).A i).e η)
        (multiplicity f ((stackAt hf hne y).pt i))) (branchTrans hf hne y i w) := by
    apply analyticOnNhd_traceCoeff ((stackAt hf hne y).radius_pos i)
      ((stackAt hf hne y).mult_ne_zero i) ?_ _ (branchTrans_mem_ball hf hne y hw i)
    rw [← ((stackAt hf hne y).A i).target_eq]
    exact η.analyticOnNhd_coeffIn ((stackAt hf hne y).A i).mem_maximalAtlas
  exact hψ.deriv.fun_mul (htc.fun_comp hψ)

/-! ### The canonical per-fibre-point coefficient `qCoeff` -/

/-- The canonical (stack-independent) contribution of a fibre point `x` to the trace's
coefficient in a target chart `e₀`: the coefficient of `η` at `x`, divided by the chart
derivative of `f`. (Junk `0` at ramified `x`, where the chart derivative vanishes.) -/
def qCoeff (f : X → Y) (η : Form1 X) (e₀ : OpenPartialHomeomorph Y ℂ) (x : X) : ℂ :=
  (deriv (⇑e₀ ∘ f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x))⁻¹ * coeffAt x η

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [T2Space Y] [IsManifold 𝓘(ℂ, ℂ) ω Y] in
/-- Factorization of the chart derivative of `f` through a pair of adapted charts:
`d(f-in-charts) = d(target transition) · (k·v^(k-1)) · d(source transition)`. -/
theorem deriv_chartRead_eq_of_adapted {x₀ : X} {k : ℕ} (A : AdaptedChartsAt f x₀ k)
    {e₀ : OpenPartialHomeomorph Y ℂ} (he₀ : e₀ ∈ maximalAtlas 𝓘(ℂ) ω Y)
    {x : X} (hx : x ∈ A.e.source) (hfx : f x ∈ e₀.source) :
    deriv (⇑e₀ ∘ f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x)
      = deriv (⇑e₀ ∘ ⇑A.e'.symm) (A.e' (f x)) * ((k : ℂ) * (A.e x) ^ (k - 1))
        * deriv (⇑A.e ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) := by
  have hxc : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  have hz₀t : chartAt ℂ x x ∈ (chartAt ℂ x).target := mem_chart_target ℂ x
  have hsymm0 : (chartAt ℂ x).symm (chartAt ℂ x x) = x := (chartAt ℂ x).left_inv hxc
  have hBan : AnalyticAt ℂ (⇑A.e ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) :=
    analyticAt_trans A.mem_maximalAtlas (chart_mem_maximalAtlas x) hz₀t
      (by rw [hsymm0]; exact hx)
  have hBd : HasDerivAt (⇑A.e ∘ ⇑(chartAt ℂ x).symm)
      (deriv (⇑A.e ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x)) (chartAt ℂ x x) :=
    hBan.differentiableAt.hasDerivAt
  have hvalB : (⇑A.e ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) = A.e x := by
    simp only [Function.comp_apply, hsymm0]
  have hfxsrc : f x ∈ A.e'.source := A.mapsTo hx
  have hOan : AnalyticAt ℂ (⇑e₀ ∘ ⇑A.e'.symm) (A.e' (f x)) :=
    analyticAt_trans he₀ A.mem_maximalAtlas' (A.e'.map_source hfxsrc)
      (by rw [A.e'.left_inv hfxsrc]; exact hfx)
  have hpow : HasDerivAt (fun v : ℂ => v ^ k) ((k : ℂ) * (A.e x) ^ (k - 1))
      ((⇑A.e ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x)) := by
    rw [hvalB]; exact hasDerivAt_pow k (A.e x)
  have hcomp1 := hpow.comp (chartAt ℂ x x) hBd
  have hptO : A.e' (f x) = (fun v : ℂ => v ^ k) ((⇑A.e ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x)) := by
    simp only [hvalB]
    exact A.eqOn_pow x hx
  have hOd : HasDerivAt (⇑e₀ ∘ ⇑A.e'.symm) (deriv (⇑e₀ ∘ ⇑A.e'.symm) (A.e' (f x)))
      ((fun v : ℂ => v ^ k) ((⇑A.e ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x))) := by
    rw [← hptO]
    exact hOan.differentiableAt.hasDerivAt
  have hcomp2 := hOd.comp (chartAt ℂ x x) hcomp1
  have hcont : ContinuousAt (⇑(chartAt ℂ x).symm) (chartAt ℂ x x) :=
    (chartAt ℂ x).continuousAt_symm hz₀t
  have hev : ∀ᶠ z in 𝓝 (chartAt ℂ x x), (chartAt ℂ x).symm z ∈ A.e.source := by
    have h := hcont.tendsto
    rw [hsymm0] at h
    exact h.eventually (A.e.open_source.mem_nhds hx)
  have heq : (⇑e₀ ∘ f ∘ ⇑(chartAt ℂ x).symm) =ᶠ[𝓝 (chartAt ℂ x x)]
      (⇑e₀ ∘ ⇑A.e'.symm) ∘ ((fun v : ℂ => v ^ k) ∘ (⇑A.e ∘ ⇑(chartAt ℂ x).symm)) := by
    filter_upwards [hev] with z hz
    change e₀ (f ((chartAt ℂ x).symm z)) = e₀ (A.e'.symm ((A.e ((chartAt ℂ x).symm z)) ^ k))
    rw [← A.eqOn_symm _ hz]
  have hD := (hcomp2.congr_of_eventuallyEq heq).deriv
  rw [hD]
  ring

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [T2Space Y] [IsManifold 𝓘(ℂ, ℂ) ω Y] in
/-- The per-fibre-point identity: `qCoeff` computed through the `i`-th branch of a fibre stack
is exactly the branch-transported, Jacobian-divided coefficient of `η` (the integrand of
`traceZkForm`). Holds at ramified points too (both sides junk to `0`). -/
theorem qCoeff_eq_branch_term {y : Y} (S : RS.FiberStack f y) (i : Fin S.n)
    {e₀ : OpenPartialHomeomorph Y ℂ} (he₀ : e₀ ∈ maximalAtlas 𝓘(ℂ) ω Y)
    {x : X} (hx : x ∈ (S.A i).e.source) (hfx : f x ∈ e₀.source) (η : Form1 X) :
    qCoeff f η e₀ x
      = deriv (⇑(S.A i).e' ∘ ⇑e₀.symm) (e₀ (f x))
        * (coeffIn (S.A i).e η ((S.A i).e x)
            * ((multiplicity f (S.pt i) : ℂ)
                * ((S.A i).e x) ^ ((multiplicity f (S.pt i) : ℤ) - 1))⁻¹) := by
  have hk1 : 1 ≤ multiplicity f (S.pt i) := S.one_le_mult i
  have hzp : ((S.A i).e x : ℂ) ^ ((multiplicity f (S.pt i) : ℤ) - 1)
      = ((S.A i).e x) ^ (multiplicity f (S.pt i) - 1) := by
    have h1 : (multiplicity f (S.pt i) : ℤ) - 1 = ((multiplicity f (S.pt i) - 1 : ℕ) : ℤ) := by
      omega
    rw [h1, zpow_natCast]
  rw [hzp]
  have hB := coeffAt_eq_deriv_mul_coeffIn η (S.A i).mem_maximalAtlas hx
  have hBne := deriv_transition_ne_zero (S.A i).mem_maximalAtlas hx
  have hD := deriv_chartRead_eq_of_adapted (S.A i) he₀ hx hfx
  have hprod := deriv_transition_mul he₀ (S.A i).mem_maximalAtlas' hfx ((S.A i).mapsTo hx)
  set T := deriv (⇑e₀ ∘ ⇑(S.A i).e'.symm) ((S.A i).e' (f x)) with hT_def
  set T' := deriv (⇑(S.A i).e' ∘ ⇑e₀.symm) (e₀ (f x)) with hT'_def
  set B := deriv (⇑(S.A i).e ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) with hB_def
  set J := (multiplicity f (S.pt i) : ℂ) * ((S.A i).e x) ^ (multiplicity f (S.pt i) - 1)
    with hJ_def
  have hTne : T ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hprod
    exact zero_ne_one hprod
  have hT'inv : T' = T⁻¹ := eq_inv_of_mul_eq_one_left hprod
  change (deriv (⇑e₀ ∘ f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x))⁻¹ * coeffAt x η
    = T' * (coeffIn (S.A i).e η ((S.A i).e x) * J⁻¹)
  rw [hD, hB, hT'inv]
  rcases eq_or_ne J 0 with hJ0 | hJ0
  · rw [hJ0]
    simp
  · field_simp

/-- Well-definedness at non-center points: the defining coefficient of the trace at `yhat ≠ y`
(in the chart at index `y`) is the canonical `qCoeff` fibre sum over `f⁻¹{yhat}`. -/
theorem traceCoeffFun_eq_qSum (η : Form1 X) {y yhat : Y}
    (hyhat : yhat ∈ (traceChart hf hne y).source) (hyhatne : yhat ≠ y) :
    traceCoeffFun hf hne η y (chartAt ℂ y yhat)
      = ∑ᶠ x ∈ f ⁻¹' {yhat}, qCoeff f η (chartAt ℂ y) x := by
  rw [traceChart_source] at hyhat
  obtain ⟨hyhatsrc, hyhatV⟩ := hyhat
  have hterm : ∀ i : Fin (stackAt hf hne y).n,
      deriv (branchTrans hf hne y i) (chartAt ℂ y yhat)
        * traceCoeff (coeffIn ((stackAt hf hne y).A i).e η)
            (multiplicity f ((stackAt hf hne y).pt i))
            (branchTrans hf hne y i (chartAt ℂ y yhat))
      = RS.MTrace.traceZk (qCoeff f η (chartAt ℂ y) ∘ ⇑((stackAt hf hne y).A i).e.symm)
          (multiplicity f ((stackAt hf hne y).pt i)) (((stackAt hf hne y).A i).e' yhat) := by
    intro i
    have hk0 : multiplicity f ((stackAt hf hne y).pt i) ≠ 0 := (stackAt hf hne y).mult_ne_zero i
    have hval : branchTrans hf hne y i (chartAt ℂ y yhat) = ((stackAt hf hne y).A i).e' yhat := by
      change ((stackAt hf hne y).A i).e' ((chartAt ℂ y).symm (chartAt ℂ y yhat)) = _
      rw [(chartAt ℂ y).left_inv hyhatsrc]
    have hy0 : ((stackAt hf hne y).A i).e' y = 0 := by
      have h := ((stackAt hf hne y).A i).map_eq_zero'
      rwa [(stackAt hf hne y).maps_pt_eq i] at h
    have hζne : ((stackAt hf hne y).A i).e' yhat ≠ 0 := by
      intro h0
      apply hyhatne
      apply ((stackAt hf hne y).A i).e'.injOn ((stackAt hf hne y).V_subset i hyhatV)
        ((stackAt hf hne y).V_subset i (stackAt hf hne y).mem_V)
      rw [h0, hy0]
    have hcoeff0 := analyticAt_coeffIn_stack_zero hf hne η y i
    rw [hval, traceCoeff_apply_of_ne_zero hcoeff0 hk0 hζne, traceZkForm_def]
    rw [← congrFun (RS.MTrace.traceZk_const_mul
      (h := fun v => coeffIn ((stackAt hf hne y).A i).e η v
        * ((multiplicity f ((stackAt hf hne y).pt i) : ℂ)
            * v ^ ((multiplicity f ((stackAt hf hne y).pt i) : ℤ) - 1))⁻¹)
      (deriv (branchTrans hf hne y i) (chartAt ℂ y yhat))
      (multiplicity f ((stackAt hf hne y).pt i))) (((stackAt hf hne y).A i).e' yhat)]
    apply RS.MTrace.traceZk_congr_root
    intro v hv
    have hv0 : v ≠ 0 := by
      rintro rfl
      rw [zero_pow hk0] at hv
      exact hζne hv.symm
    have hζball : ‖((stackAt hf hne y).A i).e' yhat‖
        < ((stackAt hf hne y).A i).radius ^ multiplicity f ((stackAt hf hne y).pt i) :=
      mem_ball_zero_iff.mp ((stackAt hf hne y).map_V_mem_ball i yhat hyhatV)
    have hvlt : ‖v‖ < ((stackAt hf hne y).A i).radius :=
      RS.norm_lt_of_pow_eq hk0 ((stackAt hf hne y).radius_pos i).le hv hζball
    have hvt : v ∈ ((stackAt hf hne y).A i).e.target := by
      rw [((stackAt hf hne y).A i).target_eq]
      exact mem_ball_zero_iff.mpr hvlt
    have hxs : ((stackAt hf hne y).A i).e.symm v ∈ ((stackAt hf hne y).A i).e.source :=
      ((stackAt hf hne y).A i).e.map_target hvt
    have hex : ((stackAt hf hne y).A i).e (((stackAt hf hne y).A i).e.symm v) = v :=
      ((stackAt hf hne y).A i).e.right_inv hvt
    have hfx : f (((stackAt hf hne y).A i).e.symm v) = yhat := by
      apply ((stackAt hf hne y).A i).e'.injOn
        (((stackAt hf hne y).A i).mapsTo hxs) ((stackAt hf hne y).V_subset i hyhatV)
      rw [((stackAt hf hne y).A i).eqOn_pow _ hxs, hex, hv]
    have hfxsrc : f (((stackAt hf hne y).A i).e.symm v) ∈ (chartAt ℂ y).source := by
      rw [hfx]; exact hyhatsrc
    have hq := qCoeff_eq_branch_term (stackAt hf hne y) i (chart_mem_maximalAtlas y) hxs
      hfxsrc η
    change deriv (branchTrans hf hne y i) (chartAt ℂ y yhat)
        * (coeffIn ((stackAt hf hne y).A i).e η v
            * ((multiplicity f ((stackAt hf hne y).pt i) : ℂ)
                * v ^ ((multiplicity f ((stackAt hf hne y).pt i) : ℤ) - 1))⁻¹)
      = (qCoeff f η (chartAt ℂ y) ∘ ⇑((stackAt hf hne y).A i).e.symm) v
    rw [Function.comp_apply, hq, hex, hfx]
    rfl
  calc traceCoeffFun hf hne η y (chartAt ℂ y yhat)
      = ∑ i, RS.MTrace.traceZk (qCoeff f η (chartAt ℂ y) ∘ ⇑((stackAt hf hne y).A i).e.symm)
          (multiplicity f ((stackAt hf hne y).pt i)) (((stackAt hf hne y).A i).e' yhat) :=
        Finset.sum_congr rfl fun i _ => hterm i
    _ = ∑ᶠ x ∈ f ⁻¹' {yhat}, qCoeff f η (chartAt ℂ y) x :=
        RS.MTrace.sum_traceZk_stack (stackAt hf hne y) hyhatV

include hf in
omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [T2Space Y] [IsManifold 𝓘(ℂ, ℂ) ω Y] in
/-- The chart-transition law for the canonical fibre sum. -/
theorem qSum_trans (η : Form1 X) {yhat : Y} {e₀ e₁ : OpenPartialHomeomorph Y ℂ}
    (he₀ : e₀ ∈ maximalAtlas 𝓘(ℂ) ω Y) (he₁ : e₁ ∈ maximalAtlas 𝓘(ℂ) ω Y)
    (hyhat₀ : yhat ∈ e₀.source) (hyhat₁ : yhat ∈ e₁.source) :
    ∑ᶠ x ∈ f ⁻¹' {yhat}, qCoeff f η e₁ x
      = deriv (⇑e₀ ∘ ⇑e₁.symm) (e₁ yhat) * ∑ᶠ x ∈ f ⁻¹' {yhat}, qCoeff f η e₀ x := by
  rw [mul_finsum_mem]
  apply finsum_mem_congr rfl
  intro x hx
  have hfx : f x = yhat := hx
  have hz₀t : chartAt ℂ x x ∈ (chartAt ℂ x).target := mem_chart_target ℂ x
  have hsymm0 : (chartAt ℂ x).symm (chartAt ℂ x x) = x :=
    (chartAt ℂ x).left_inv (mem_chart_source ℂ x)
  have hptr : (⇑e₀ ∘ f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) = e₀ (f x) := by
    simp only [Function.comp_apply, hsymm0]
  have houter : DifferentiableAt ℂ (⇑e₁ ∘ ⇑e₀.symm)
      ((⇑e₀ ∘ f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x)) := by
    rw [hptr, hfx]
    exact (analyticAt_transition_fun he₀ he₁ hyhat₀ hyhat₁).differentiableAt
  have hinner : DifferentiableAt ℂ (⇑e₀ ∘ f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) := by
    have h := analyticAt_of_mem_maximalAtlas (hf x) (chart_mem_maximalAtlas x)
      (mem_chart_source ℂ x) he₀ (by rw [hfx]; exact hyhat₀)
    exact h.differentiableAt
  have heq : (⇑e₁ ∘ f ∘ ⇑(chartAt ℂ x).symm) =ᶠ[𝓝 (chartAt ℂ x x)]
      (⇑e₁ ∘ ⇑e₀.symm) ∘ (⇑e₀ ∘ f ∘ ⇑(chartAt ℂ x).symm) := by
    have hcont : ContinuousAt (f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) := by
      have hfc : ContinuousAt f ((chartAt ℂ x).symm (chartAt ℂ x x)) := by
        rw [hsymm0]; exact (hf x).continuousAt
      exact hfc.comp ((chartAt ℂ x).continuousAt_symm hz₀t)
    have hmem : (f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) ∈ e₀.source := by
      simp only [Function.comp_apply, hsymm0]
      rw [hfx]; exact hyhat₀
    filter_upwards [hcont.preimage_mem_nhds (e₀.open_source.mem_nhds hmem)] with z hz
    have hz' : f ((chartAt ℂ x).symm z) ∈ e₀.source := hz
    simp only [Function.comp_apply, e₀.left_inv hz']
  have hD := deriv_eq_of_eventuallyEq_comp' houter hinner heq
  change (deriv (⇑e₁ ∘ f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x))⁻¹ * coeffAt x η
    = deriv (⇑e₀ ∘ ⇑e₁.symm) (e₁ yhat)
      * ((deriv (⇑e₀ ∘ f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x))⁻¹ * coeffAt x η)
  rw [hD, hptr, hfx, mul_inv]
  have hprod := deriv_transition_mul he₁ he₀ hyhat₁ hyhat₀
  have hTinv : (deriv (⇑e₁ ∘ ⇑e₀.symm) (e₀ yhat))⁻¹ = deriv (⇑e₀ ∘ ⇑e₁.symm) (e₁ yhat) :=
    (eq_inv_of_mul_eq_one_left hprod).symm
  rw [hTinv]
  ring

/-- The chart-compatibility law (CC1) of the trace's coefficient data: proved on the dense
subset of the overlap avoiding the two chart centers via `traceCoeffFun_eq_qSum`/`qSum_trans`,
and extended to the whole overlap by continuity. -/
theorem traceCoeffFun_compat (η : Form1 X) (y y' p : Y)
    (hp : p ∈ (traceChart hf hne y).source ∩ (traceChart hf hne y').source) :
    traceCoeffFun hf hne η y' (traceChart hf hne y' p)
      = deriv (⇑(traceChart hf hne y) ∘ ⇑(traceChart hf hne y').symm) (traceChart hf hne y' p)
        * traceCoeffFun hf hne η y (traceChart hf hne y p) := by
  set U : Set ℂ := ⇑(chartAt ℂ y') ''
    ((traceChart hf hne y).source ∩ (traceChart hf hne y').source) with hU_def
  have hsub' : (traceChart hf hne y).source ∩ (traceChart hf hne y').source
      ⊆ (chartAt ℂ y').source := by
    intro q hq
    rw [traceChart_source] at hq
    exact hq.2.1
  have hUopen : IsOpen U := by
    apply (chartAt ℂ y').isOpen_image_of_subset_source ?_ hsub'
    exact ((traceChart hf hne y).open_source).inter ((traceChart hf hne y').open_source)
  have hUsub : U ⊆ (traceChart hf hne y').target := by
    rintro z ⟨q, hq, rfl⟩
    exact (traceChart hf hne y').map_source hq.2
  set τ : ℂ → ℂ := ⇑(chartAt ℂ y) ∘ ⇑(chartAt ℂ y').symm with hτ_def
  have hmemτ : ∀ z ∈ U, z ∈ (chartAt ℂ y').target ∧ (chartAt ℂ y').symm z ∈ (chartAt ℂ y).source
      ∧ τ z ∈ (traceChart hf hne y).target := by
    rintro z ⟨q, hq, rfl⟩
    have hq1 : q ∈ (traceChart hf hne y).source := hq.1
    have hqsrc : q ∈ (chartAt ℂ y').source := hsub' hq
    have hql : (chartAt ℂ y').symm (chartAt ℂ y' q) = q := (chartAt ℂ y').left_inv hqsrc
    refine ⟨(chartAt ℂ y').map_source hqsrc, ?_, ?_⟩
    · rw [hql]
      rw [traceChart_source] at hq1
      exact hq1.1
    · show τ (chartAt ℂ y' q) ∈ (traceChart hf hne y).target
      have : τ (chartAt ℂ y' q) = chartAt ℂ y q := by
        change chartAt ℂ y ((chartAt ℂ y').symm (chartAt ℂ y' q)) = chartAt ℂ y q
        rw [hql]
      rw [this]
      exact (traceChart hf hne y).map_source hq1
  have hFcont : ContinuousOn (traceCoeffFun hf hne η y') U :=
    ((analyticOnNhd_traceCoeffFun hf hne η y').continuousOn).mono hUsub
  have hGcont : ContinuousOn
      (fun z => deriv τ z * traceCoeffFun hf hne η y (τ z)) U := by
    intro z hz
    obtain ⟨hzt, hzs, hzτ⟩ := hmemτ z hz
    have hτan : AnalyticAt ℂ τ z :=
      analyticAt_trans (chart_mem_maximalAtlas y) (chart_mem_maximalAtlas y') hzt hzs
    have hcan : AnalyticAt ℂ (traceCoeffFun hf hne η y) (τ z) :=
      analyticOnNhd_traceCoeffFun hf hne η y _ hzτ
    exact ((hτan.deriv.fun_mul (hcan.fun_comp hτan)).continuousAt).continuousWithinAt
  have hEqT : Set.EqOn (traceCoeffFun hf hne η y')
      (fun z => deriv τ z * traceCoeffFun hf hne η y (τ z))
      (U \ {chartAt ℂ y' y, chartAt ℂ y' y'}) := by
    rintro z ⟨⟨q, hq, rfl⟩, hznot⟩
    have hqsrc : q ∈ (chartAt ℂ y').source := hsub' hq
    have hql : (chartAt ℂ y').symm (chartAt ℂ y' q) = q := (chartAt ℂ y').left_inv hqsrc
    have hqy' : q ≠ y' := by
      rintro rfl
      exact hznot (by simp)
    have hqy : q ≠ y := by
      rintro rfl
      exact hznot (by simp)
    have hτq : τ (chartAt ℂ y' q) = chartAt ℂ y q := by
      change chartAt ℂ y ((chartAt ℂ y').symm (chartAt ℂ y' q)) = chartAt ℂ y q
      rw [hql]
    change traceCoeffFun hf hne η y' (chartAt ℂ y' q)
      = deriv τ (chartAt ℂ y' q) * traceCoeffFun hf hne η y (τ (chartAt ℂ y' q))
    rw [hτq, traceCoeffFun_eq_qSum hf hne η hq.2 hqy', traceCoeffFun_eq_qSum hf hne η hq.1 hqy]
    exact qSum_trans hf η (chart_mem_maximalAtlas y) (chart_mem_maximalAtlas y')
      (by rw [traceChart_source hf hne y] at hq; exact hq.1.1)
      (by rw [traceChart_source hf hne y'] at hq; exact hq.2.1)
  have hTU : U ⊆ closure (U \ {chartAt ℂ y' y, chartAt ℂ y' y'}) :=
    open_subset_closure_diff hUopen ((Set.finite_singleton _).insert _)
  have hEqU := ContinuousOn.eqOn_of_subset_closure hUopen hFcont hGcont hTU hEqT
  have hkey := hEqU (⟨p, hp, rfl⟩ : (chartAt ℂ y' : Y → ℂ) p ∈ U)
  have hpsrc : p ∈ (chartAt ℂ y').source := hsub' hp
  have hτp : τ (chartAt ℂ y' p) = chartAt ℂ y p := by
    change chartAt ℂ y ((chartAt ℂ y').symm (chartAt ℂ y' p)) = chartAt ℂ y p
    rw [(chartAt ℂ y').left_inv hpsrc]
  have hkey' : traceCoeffFun hf hne η y' (chartAt ℂ y' p)
      = deriv τ (chartAt ℂ y' p) * traceCoeffFun hf hne η y (τ (chartAt ℂ y' p)) := hkey
  rw [hτp] at hkey'
  exact hkey'

/-! ### Assembly: `traceForm` and `Form1.trace` -/

/-- The trace's coefficient data over the chart family `ι := Y`. -/
def traceData (η : Form1 X) : Form1CoeffData Y Y where
  chart y := traceChart hf hne y
  mem_maximalAtlas y := traceChart_mem_maximalAtlas hf hne y
  exists_mem y := ⟨y, mem_traceChart_source_self hf hne y⟩
  coeff y := traceCoeffFun hf hne η y
  analyticOnNhd y := analyticOnNhd_traceCoeffFun hf hne η y
  compat y y' p hp := traceCoeffFun_compat hf hne η y y' p hp

/-- The trace of a holomorphic 1-form along a nonconstant holomorphic map, as a raw `Form1 Y`. -/
def traceForm (η : Form1 X) : Form1 Y := Form1.ofCoeffs (traceData hf hne η)

theorem coeffIn_traceChart_traceForm (η : Form1 X) (y : Y) {w : ℂ}
    (hw : w ∈ (traceChart hf hne y).target) :
    coeffIn (traceChart hf hne y) (traceForm hf hne η) w = traceCoeffFun hf hne η y w :=
  Form1.coeffIn_ofCoeffs (traceData hf hne η) y hw

/-- Preferred-chart evaluation of the trace: the chart at index `yhat` restricts the preferred
chart at `yhat`, so the transition factor is `1`. -/
theorem coeffAt_traceForm (η : Form1 X) (yhat : Y) :
    coeffAt yhat (traceForm hf hne η) = traceCoeffFun hf hne η yhat (chartAt ℂ yhat yhat) := by
  have h : coeffAt yhat (Form1.ofCoeffs (traceData hf hne η))
      = deriv (⇑(traceChart hf hne yhat) ∘ ⇑(chartAt ℂ yhat).symm) (chartAt ℂ yhat yhat)
        * traceCoeffFun hf hne η yhat (traceChart hf hne yhat yhat) :=
    Form1.coeffAt_ofCoeffs (traceData hf hne η) (mem_traceChart_source_self hf hne yhat)
  unfold traceForm
  have hid : (⇑(traceChart hf hne yhat) ∘ ⇑(chartAt ℂ yhat).symm)
      =ᶠ[𝓝 (chartAt ℂ yhat yhat)] id := by
    filter_upwards [(chartAt ℂ yhat).open_target.mem_nhds (mem_chart_target ℂ yhat)] with z hz
    change chartAt ℂ yhat ((chartAt ℂ yhat).symm z) = z
    exact (chartAt ℂ yhat).right_inv hz
  rw [h, hid.deriv_eq, deriv_id, one_mul]
  rfl

/-- Pointwise additivity of the trace coefficient in `η`. -/
theorem traceCoeffFun_add (η η' : Form1 X) (y : Y) (w : ℂ) :
    traceCoeffFun hf hne (η + η') y w
      = traceCoeffFun hf hne η y w + traceCoeffFun hf hne η' y w := by
  unfold traceCoeffFun
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hcoeq : coeffIn ((stackAt hf hne y).A i).e (η + η')
      = fun v => coeffIn ((stackAt hf hne y).A i).e η v
        + coeffIn ((stackAt hf hne y).A i).e η' v := by
    funext v
    exact coeffIn_add _ η η' v
  rw [hcoeq, traceCoeff_fun_add ((stackAt hf hne y).mult_ne_zero i)
    (analyticAt_coeffIn_stack_zero hf hne η y i) (analyticAt_coeffIn_stack_zero hf hne η' y i)]
  ring

/-- Pointwise `ℂ`-homogeneity of the trace coefficient in `η`. -/
theorem traceCoeffFun_smul (c : ℂ) (η : Form1 X) (y : Y) (w : ℂ) :
    traceCoeffFun hf hne (c • η) y w = c * traceCoeffFun hf hne η y w := by
  unfold traceCoeffFun
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hcoeq : coeffIn ((stackAt hf hne y).A i).e (c • η)
      = fun v => c * coeffIn ((stackAt hf hne y).A i).e η v := by
    funext v
    exact coeffIn_smul _ c η v
  rw [hcoeq, traceCoeff_const_mul ((stackAt hf hne y).mult_ne_zero i)
    (analyticAt_coeffIn_stack_zero hf hne η y i) c]
  ring

theorem traceForm_add (η η' : Form1 X) :
    traceForm hf hne (η + η') = traceForm hf hne η + traceForm hf hne η' :=
  Form1.ext_coeffAt fun yhat => by
    rw [coeffAt_traceForm, coeffAt_add, coeffAt_traceForm, coeffAt_traceForm,
      traceCoeffFun_add]

theorem traceForm_smul (c : ℂ) (η : Form1 X) :
    traceForm hf hne (c • η) = c • traceForm hf hne η :=
  Form1.ext_coeffAt fun yhat => by
    rw [coeffAt_traceForm, coeffAt_smul, coeffAt_traceForm, traceCoeffFun_smul]

variable (f) in
/-- **`Form1.trace` (§6.1)**: the fibrewise trace of holomorphic 1-forms along a holomorphic
`f : X → Y`, as a `ℂ`-linear map `Form1 X →ₗ[ℂ] Form1 Y`. The zero map for constant `f`
(matching the gist's pullback convention on Jacobians). -/
def Form1.trace (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) : Form1 X →ₗ[ℂ] Form1 Y :=
  letI := Classical.dec (∃ c, ∀ x, f x = c)
  if hne : ∃ c, ∀ x, f x = c then 0 else
    { toFun := traceForm hf hne
      map_add' := traceForm_add hf hne
      map_smul' := fun c η => by
        simpa using traceForm_smul hf hne c η }

theorem Form1.trace_apply (η : Form1 X) :
    Form1.trace f hf η = traceForm hf hne η := by
  unfold Form1.trace
  rw [dif_neg hne]
  rfl

theorem Form1.trace_of_forall_eq (hc : ∃ c, ∀ x, f x = c) :
    Form1.trace f hf = 0 := by
  unfold Form1.trace
  rw [dif_pos hc]

/-! ### The regular-value formula -/

/-- `traceCoeff` at an unramified branch (`k = 1`, hypothesis form usable under
type-dependent `k`). -/
theorem traceCoeff_eq_of_eq_one {h : ℂ → ℂ} {k : ℕ} (hk : k = 1) (hh : AnalyticAt ℂ h 0) :
    traceCoeff h k = h := by
  subst hk
  exact traceCoeff_one hh

/-- **Regular-value evaluation of the trace**: at a regular value `yhat`, the preferred-chart
coefficient of `traceForm η` is the canonical fibre sum of `qCoeff` (every branch is unramified
there, so the repaired coefficient evaluates literally). -/
theorem coeffAt_traceForm_of_isRegularValue (η : Form1 X) {yhat : Y}
    (hyhat : RS.IsRegularValue f yhat) :
    coeffAt yhat (traceForm hf hne η) = ∑ᶠ x ∈ f ⁻¹' {yhat}, qCoeff f η (chartAt ℂ yhat) x := by
  rw [coeffAt_traceForm]
  have hterm : ∀ i : Fin (stackAt hf hne yhat).n,
      deriv (branchTrans hf hne yhat i) (chartAt ℂ yhat yhat)
        * traceCoeff (coeffIn ((stackAt hf hne yhat).A i).e η)
            (multiplicity f ((stackAt hf hne yhat).pt i))
            (branchTrans hf hne yhat i (chartAt ℂ yhat yhat))
      = qCoeff f η (chartAt ℂ yhat) ((stackAt hf hne yhat).pt i) := by
    intro i
    have hm1 : multiplicity f ((stackAt hf hne yhat).pt i) = 1 :=
      multiplicity_eq_one_of_isRegularValue hf hne hyhat ((stackAt hf hne yhat).maps_pt_eq i)
    have hval : branchTrans hf hne yhat i (chartAt ℂ yhat yhat) = 0 := by
      change ((stackAt hf hne yhat).A i).e' ((chartAt ℂ yhat).symm (chartAt ℂ yhat yhat)) = 0
      rw [(chartAt ℂ yhat).left_inv (mem_chart_source ℂ yhat)]
      have h := ((stackAt hf hne yhat).A i).map_eq_zero'
      rwa [(stackAt hf hne yhat).maps_pt_eq i] at h
    rw [hval, traceCoeff_eq_of_eq_one hm1 (analyticAt_coeffIn_stack_zero hf hne η yhat i)]
    have hq := qCoeff_eq_branch_term (stackAt hf hne yhat) i (chart_mem_maximalAtlas yhat)
      ((stackAt hf hne yhat).mem_source_pt i)
      (by rw [(stackAt hf hne yhat).maps_pt_eq i]; exact mem_chart_source ℂ yhat) η
    rw [hq, ((stackAt hf hne yhat).A i).map_eq_zero]
    have hJ : ((multiplicity f ((stackAt hf hne yhat).pt i) : ℂ)
        * (0 : ℂ) ^ ((multiplicity f ((stackAt hf hne yhat).pt i) : ℤ) - 1))⁻¹ = 1 := by
      rw [hm1]
      norm_num
    rw [hJ, mul_one, (stackAt hf hne yhat).maps_pt_eq i]
    rfl
  calc traceCoeffFun hf hne η yhat (chartAt ℂ yhat yhat)
      = ∑ i, qCoeff f η (chartAt ℂ yhat) ((stackAt hf hne yhat).pt i) :=
        Finset.sum_congr rfl fun i _ => hterm i
    _ = ∑ᶠ i, qCoeff f η (chartAt ℂ yhat) ((stackAt hf hne yhat).pt i) :=
        (finsum_eq_sum_of_fintype _).symm
    _ = ∑ᶠ x ∈ Set.range (stackAt hf hne yhat).pt, qCoeff f η (chartAt ℂ yhat) x :=
        (finsum_mem_range (stackAt hf hne yhat).pt_injective).symm
    _ = ∑ᶠ x ∈ f ⁻¹' {yhat}, qCoeff f η (chartAt ℂ yhat) x := by
        rw [(stackAt hf hne yhat).range_pt]

end RS

end
