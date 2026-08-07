/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Dbar.Operator
import LeanPool.JacobianDiffgeo.Forms.Analyticity
import LeanPool.JacobianDiffgeo.Surface.RealSmooth
import LeanPool.JacobianDiffgeo.PlanarStokes.Compat
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Topology.Algebra.Module.Determinant

/-!
# abel-theorem: the Serre area-pairing infrastructure (design §4.3, routing decision #2)

Unit: abel-theorem. Namespace `RS.Abel`.

The blueprint's routing decision #2 budgeted ONE "honest integration atom" for the whole
challenge: the Dolbeault-side Serre functional `(σ, ω) ↦ ∫∫_X σ ∧ ω` pairing a smooth
`(0,1)`-form `σ : Form01 X` against a holomorphic `1`-form `ω : Form1 X`. This file builds its
foundation:

* **`SurfPoU X`** — a finite smooth partition of unity subordinate to preferred-chart sources
  (from `RS.exists_smoothPartitionOfUnity` + compactness; `SurfPoU.nonempty`).
* **planar helpers** — the indicator-extension smoothness gadget
  (`contDiff_indicator_of_eq_zero_off`, `hasCompactSupport_indicator_of_eq_zero_off`), the
  chart-inverse `ContDiffOn` bridges (`contDiffOn_comp_symm_of_contMDiffOn`,
  `contDiffOn_comp_symm_real`), the holomorphic-Jacobian determinant identity
  (`det_fderiv_restrictScalars_eq_normSq`, the residue-theorem design's spike-verified fact),
  and the **biholomorphic change-of-variables atom** `integral_eq_integral_transition`: a planar
  integrand supported on the image of a chart overlap can be transported to the other chart at
  the cost of the `(1,1)`-density factor `Complex.normSq (deriv τ)` — exactly how `σ ∧ ω`
  transforms (`Form01.compat`'s `conj (deriv τ)` times `coeffIn_trans`'s `deriv τ`).
* **`pairing PU σ θ`** — the pairing itself, `∑ i, ∫ z, ψ_i(z) · σ_i(z) · ω_i(z) dA` over the
  fixed partition `PU`, with integrability (`integrable_pairingTerm`) and bilinearity
  (`pairing_add_left`/`pairing_smul_left`/`pairing_add_right`/`pairing_smul_right`).

`SerreFunctional.lean` proves the two analytic properties (dbar-exact forms pair to zero;
positivity against the conjugate form); `ChartSupported.lean` localizes the pairing for
single-chart-supported `(0,1)`-data. No independence-of-`PU` statement is ever needed: every
downstream conclusion is a `Prop` quantified over a single fixed `PU`.
-/

open scoped ContDiff Manifold
open IsManifold Metric Set MeasureTheory

noncomputable section

namespace RS.Abel

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## Planar helpers -/

section Planar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Indicator-extension smoothness gadget: if `F` is smooth on the open set `T` and vanishes on
`T \ K` for a compact `K ⊆ T`, then the indicator extension of `F` by `0` is globally smooth. -/
theorem contDiff_indicator_of_eq_zero_off {F : ℂ → E} {T K : Set ℂ} (hT : IsOpen T)
    (hK : IsCompact K) (hKT : K ⊆ T) (hF : ContDiffOn ℝ ∞ F T)
    (h0 : ∀ z ∈ T, z ∉ K → F z = 0) : ContDiff ℝ ∞ (T.indicator F) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ T
  · refine (hF.contDiffAt (hT.mem_nhds hz)).congr_of_eventuallyEq ?_
    filter_upwards [hT.mem_nhds hz] with w hw
    exact Set.indicator_of_mem hw F
  · have hzK : z ∉ K := fun h => hz (hKT h)
    refine (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq ?_
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hzK] with w hw
    by_cases hwT : w ∈ T
    · rw [Set.indicator_of_mem hwT, h0 w hwT hw]
    · exact Set.indicator_of_notMem hwT F

omit [NormedSpace ℝ E] in
/-- Companion to `contDiff_indicator_of_eq_zero_off`: the indicator extension has compact
support (inside `K`). -/
theorem hasCompactSupport_indicator_of_eq_zero_off {F : ℂ → E} {T K : Set ℂ}
    (hK : IsCompact K) (h0 : ∀ z ∈ T, z ∉ K → F z = 0) :
    HasCompactSupport (T.indicator F) := by
  refine HasCompactSupport.intro hK (fun z hz => ?_)
  by_cases hzT : z ∈ T
  · rw [Set.indicator_of_mem hzT, h0 z hzT hz]
  · exact Set.indicator_of_notMem hzT F

/-- Integrability of the indicator-extension gadget. -/
theorem integrable_indicator_of_eq_zero_off {F : ℂ → E} {T K : Set ℂ} (hT : IsOpen T)
    (hK : IsCompact K) (hKT : K ⊆ T) (hF : ContDiffOn ℝ ∞ F T)
    (h0 : ∀ z ∈ T, z ∉ K → F z = 0) : Integrable (T.indicator F) := by
  exact ((contDiff_indicator_of_eq_zero_off hT hK hKT hF
      h0).continuous).integrable_of_hasCompactSupport
    (hasCompactSupport_indicator_of_eq_zero_off hK h0)

end Planar

/-! ## Chart-inverse smoothness bridges -/

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- `ContMDiffOn` data on `X` reads as planar `ContDiffOn` data through the inverse of any
maximal-atlas chart (the "any-chart" analogue of `SmoothC.contDiffOn_comp_chartAt_symm`). -/
theorem contDiffOn_comp_symm_of_contMDiffOn {u : X → ℂ} {s : Set X}
    (hu : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ u s) {e : OpenPartialHomeomorph X ℂ}
    (he : e ∈ maximalAtlas 𝓘(ℂ) ω X) :
    ContDiffOn ℝ ∞ (u ∘ ⇑e.symm) (⇑e '' (s ∩ e.source)) := by
  have hsymm : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (⇑e.symm) e.target :=
    RS.contMDiffOn_real_of_holomorphicOn e.open_target
      (contMDiffOn_symm_of_mem_maximalAtlas he)
  have hcomp : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (u ∘ ⇑e.symm) (e.target ∩ ⇑e.symm ⁻¹' s) :=
    hu.comp (hsymm.mono inter_subset_left) (fun z hz => hz.2)
  have hsub : ⇑e '' (s ∩ e.source) ⊆ e.target ∩ ⇑e.symm ⁻¹' s := by
    rintro z ⟨y, ⟨hys, hye⟩, rfl⟩
    exact ⟨e.map_source hye, by rw [Set.mem_preimage, e.left_inv hye]; exact hys⟩
  exact contMDiffOn_iff_contDiffOn.mp (hcomp.mono hsub)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- The real-valued global version: a `ContMDiff` real function on `X` reads as planar
`ContDiffOn` data on any maximal-atlas chart target. -/
theorem contDiffOn_comp_symm_real {ψ : X → ℝ}
    (hψ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ ψ) {e : OpenPartialHomeomorph X ℂ}
    (he : e ∈ maximalAtlas 𝓘(ℂ) ω X) :
    ContDiffOn ℝ ∞ (ψ ∘ ⇑e.symm) e.target := by
  have hsymm : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (⇑e.symm) e.target :=
    RS.contMDiffOn_real_of_holomorphicOn e.open_target
      (contMDiffOn_symm_of_mem_maximalAtlas he)
  have hcomp : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ (ψ ∘ ⇑e.symm) e.target :=
    (hψ.contMDiffOn (s := Set.univ)).comp hsymm (fun z _ => Set.mem_univ _)
  exact contMDiffOn_iff_contDiffOn.mp hcomp

/-- Holomorphic-coefficient smoothness: the chart coefficient of a holomorphic `1`-form is
real-smooth on the chart target. -/
theorem contDiffOn_coeffIn (θ : RS.Form1 X) {e : OpenPartialHomeomorph X ℂ}
    (he : e ∈ maximalAtlas 𝓘(ℂ) ω X) :
    ContDiffOn ℝ ∞ (RS.coeffIn e θ) e.target := fun _z hz =>
  (((θ.analyticAt_coeffIn he hz).contDiffAt).restrict_scalars ℝ).contDiffWithinAt

/-! ## The holomorphic Jacobian determinant (residue-theorem design §1.6, spike-verified) -/

/-- The planar real Jacobian determinant of a holomorphic map is `normSq` of its complex
derivative. -/
theorem det_fderiv_eq_normSq_deriv {τ : ℂ → ℂ} {ζ : ℂ} (hτ : DifferentiableAt ℂ τ ζ) :
    (fderiv ℝ τ ζ).det = Complex.normSq (deriv τ ζ) := by
  have hr : fderiv ℝ τ ζ = (fderiv ℂ τ ζ).restrictScalars ℝ := hτ.fderiv_restrictScalars ℝ
  have hspan : fderiv ℂ τ ζ = ContinuousLinearMap.toSpanSingleton ℂ (deriv τ ζ) := by
    ext
    rw [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, fderiv_eq_deriv_mul]
    ring
  rw [hr, hspan]
  simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_eq]

/-! ## The biholomorphic change-of-variables atom -/

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- **The `(1,1)`-density change of variables between charts** (the "honest integration atom"'s
transport step): if `F` vanishes off `e '' (e.source ∩ e'.source)`, `G` vanishes off
`e' '' (e.source ∩ e'.source)`, and on that overlap image `G` is the `normSq (deriv τ)`-weighted
transport of `F` along the transition `τ = e ∘ e'.symm`, then the two plane integrals agree. -/
theorem integral_eq_integral_transition {e e' : OpenPartialHomeomorph X ℂ}
    (he : e ∈ maximalAtlas 𝓘(ℂ) ω X) (he' : e' ∈ maximalAtlas 𝓘(ℂ) ω X) {F G : ℂ → ℂ}
    (hF0 : ∀ z, z ∉ ⇑e '' (e.source ∩ e'.source) → F z = 0)
    (hG0 : ∀ w, w ∉ ⇑e' '' (e.source ∩ e'.source) → G w = 0)
    (hFG : ∀ w ∈ ⇑e' '' (e.source ∩ e'.source),
      G w = Complex.normSq (deriv (⇑e ∘ ⇑e'.symm) w) • F (e (e'.symm w))) :
    ∫ z : ℂ, F z = ∫ w : ℂ, G w := by
  set S : Set ℂ := ⇑e '' (e.source ∩ e'.source) with hS_def
  set S' : Set ℂ := ⇑e' '' (e.source ∩ e'.source) with hS'_def
  set τ : ℂ → ℂ := ⇑e ∘ ⇑e'.symm with hτ_def
  have hS'open : IsOpen S' :=
    e'.isOpen_image_of_subset_source (e.open_source.inter e'.open_source) inter_subset_right
  have hSopen : IsOpen S :=
    e.isOpen_image_of_subset_source (e.open_source.inter e'.open_source) inter_subset_left
  -- membership bookkeeping for points of `S'`
  have hmem : ∀ w ∈ S', e'.symm w ∈ e.source ∩ e'.source ∧ w ∈ e'.target := by
    rintro w ⟨q, hq, rfl⟩
    rw [e'.left_inv hq.2]
    exact ⟨hq, e'.map_source hq.2⟩
  have hτdiff : ∀ w ∈ S', DifferentiableAt ℂ τ w := by
    intro w hw
    obtain ⟨hq, hwt⟩ := hmem w hw
    exact RS.differentiableAt_trans he he' hwt hq.1
  -- the transition maps `S'` onto `S`
  have himage : τ '' S' = S := by
    apply Set.Subset.antisymm
    · rintro z ⟨w, hw, rfl⟩
      obtain ⟨hq, _⟩ := hmem w hw
      exact ⟨e'.symm w, hq, rfl⟩
    · rintro z ⟨q, hq, rfl⟩
      exact ⟨e' q, ⟨q, hq, rfl⟩, by simp only [hτ_def, Function.comp_apply, e'.left_inv hq.2]⟩
  have hinj : Set.InjOn τ S' := by
    rintro w₁ ⟨q₁, hq₁, rfl⟩ w₂ ⟨q₂, hq₂, rfl⟩ h
    simp only [hτ_def, Function.comp_apply, e'.left_inv hq₁.2, e'.left_inv hq₂.2] at h
    exact congrArg (⇑e') (e.injOn hq₁.1 hq₂.1 h)
  -- change of variables
  have hderiv : ∀ w ∈ S', HasFDerivWithinAt τ ((fderiv ℝ τ w : ℂ →L[ℝ] ℂ)) S' w := fun w hw =>
    (((hτdiff w hw).restrictScalars ℝ).hasFDerivAt).hasFDerivWithinAt
  have hcov := MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
    (μ := (volume : Measure ℂ)) hS'open.measurableSet hderiv hinj F
  rw [himage] at hcov
  -- glue whole-plane integrals to the set integrals
  have hFind : F = S.indicator F := by
    funext z
    by_cases hz : z ∈ S
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, hF0 z hz]
  have hGind : G = S'.indicator G := by
    funext w
    by_cases hw : w ∈ S'
    · rw [Set.indicator_of_mem hw]
    · rw [Set.indicator_of_notMem hw, hG0 w hw]
  calc ∫ z : ℂ, F z = ∫ z in S, F z := by
        conv_lhs => rw [hFind]
        rw [MeasureTheory.integral_indicator hSopen.measurableSet]
    _ = ∫ w in S', |(fderiv ℝ τ w).det| • F (τ w) := hcov
    _ = ∫ w in S', G w := by
        refine MeasureTheory.setIntegral_congr_fun hS'open.measurableSet (fun w hw => ?_)
        rw [hFG w hw, det_fderiv_eq_normSq_deriv (hτdiff w hw),
          abs_of_nonneg (Complex.normSq_nonneg _)]
        rfl
    _ = ∫ w : ℂ, G w := by
        conv_rhs => rw [hGind]
        rw [MeasureTheory.integral_indicator hS'open.measurableSet]

/-! ## The finite subordinate partition of unity -/

variable (X) in
/-- A finite smooth partition of unity on the compact surface `X`, subordinate to
preferred-chart sources: the fixed auxiliary datum the Serre pairing is built over. -/
structure SurfPoU where
  /-- The number of members. -/
  n : ℕ
  /-- The chart centers. -/
  pt : Fin n → X
  /-- The partition functions. -/
  ψ : Fin n → X → ℝ
  contMDiff : ∀ i, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ (ψ i)
  nonneg : ∀ i x, 0 ≤ ψ i x
  sum_eq_one : ∀ x, ∑ i, ψ i x = 1
  tsupport_subset : ∀ i, tsupport (ψ i) ⊆ (chartAt ℂ (pt i)).source

/-- Existence of a `SurfPoU` on a compact surface. -/
theorem SurfPoU.nonempty [T2Space X] [CompactSpace X] : Nonempty (SurfPoU X) := by
  obtain ⟨t, ht⟩ := IsCompact.elim_finite_subcover isCompact_univ
    (fun x : X => (chartAt ℂ x).source) (fun x => (chartAt ℂ x).open_source)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, mem_chart_source ℂ x⟩)
  set pt : Fin t.card → X := fun i => (t.equivFin.symm i : X) with hpt_def
  have hcov : (Set.univ : Set X) ⊆ ⋃ i : Fin t.card, (chartAt ℂ (pt i)).source := by
    intro x hx
    obtain ⟨y, hy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact Set.mem_iUnion.mpr ⟨t.equivFin ⟨y, hy.1⟩, by
      simpa [hpt_def, Equiv.symm_apply_apply] using hy.2⟩
  obtain ⟨p, hp⟩ := RS.exists_smoothPartitionOfUnity
    (fun i : Fin t.card => (chartAt ℂ (pt i)).source)
    (fun i => (chartAt ℂ (pt i)).open_source) hcov
  refine ⟨⟨t.card, pt, fun i => p i, fun i => (p i).contMDiff, fun i x => p.nonneg i x,
    fun x => ?_, fun i => hp i⟩⟩
  rw [← finsum_eq_sum_of_fintype (fun i => p i x)]
  exact p.sum_eq_one (Set.mem_univ x)

namespace SurfPoU

variable [T2Space X] [CompactSpace X] (PU : SurfPoU X)

/-- The `i`-th chart of the partition datum. -/
abbrev chart (i : Fin PU.n) : OpenPartialHomeomorph X ℂ := chartAt ℂ (PU.pt i)

omit [T2Space X] [CompactSpace X] in
theorem chart_mem_maximalAtlas (i : Fin PU.n) : PU.chart i ∈ maximalAtlas 𝓘(ℂ) ω X :=
  IsManifold.chart_mem_maximalAtlas _

/-- The compact planar carrier of the `i`-th partition member. -/
def K (i : Fin PU.n) : Set ℂ := ⇑(PU.chart i) '' tsupport (PU.ψ i)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] [T2Space X] in
theorem isCompact_K (i : Fin PU.n) : IsCompact (PU.K i) := by
  have hts : IsCompact (tsupport (PU.ψ i)) := IsCompact.of_isClosed_subset isCompact_univ
    (isClosed_tsupport _) (Set.subset_univ _)
  exact hts.image_of_continuousOn
    ((PU.chart i).continuousOn.mono (PU.tsupport_subset i))

omit [IsManifold 𝓘(ℂ, ℂ) ω X] [T2Space X] [CompactSpace X] in
theorem K_subset_target (i : Fin PU.n) : PU.K i ⊆ (PU.chart i).target := by
  rintro z ⟨x, hx, rfl⟩
  exact (PU.chart i).map_source (PU.tsupport_subset i hx)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] [T2Space X] [CompactSpace X] in
/-- Off the compact carrier, the transported partition function vanishes. -/
theorem psi_symm_eq_zero (i : Fin PU.n) {z : ℂ} (hz : z ∈ (PU.chart i).target)
    (hzK : z ∉ PU.K i) : PU.ψ i ((PU.chart i).symm z) = 0 := by
  by_contra h
  exact hzK ⟨(PU.chart i).symm z,
    subset_tsupport _ (by simpa [Function.mem_support] using h), (PU.chart i).right_inv hz⟩

omit [IsManifold 𝓘(ℂ, ℂ) ω X] [T2Space X] in
/-- The transported partition function vanishes on a whole neighborhood of any point outside
the compact carrier (including points outside the chart target). -/
theorem psi_symm_eventually_zero (i : Fin PU.n) {z : ℂ} (hzK : z ∉ PU.K i) :
    ∀ᶠ w in nhds z, ((PU.chart i).target).indicator
      (fun w => (PU.ψ i ((PU.chart i).symm w) : ℝ)) w = 0 := by
  filter_upwards [(PU.isCompact_K i).isClosed.isOpen_compl.mem_nhds hzK] with w hw
  by_cases hwT : w ∈ (PU.chart i).target
  · rw [Set.indicator_of_mem hwT, PU.psi_symm_eq_zero i hwT hw]
  · exact Set.indicator_of_notMem hwT _

/-- The complexified partition function read through an arbitrary chart. -/
def psiC (i : Fin PU.n) (e : OpenPartialHomeomorph X ℂ) : ℂ → ℂ :=
  fun w => ((PU.ψ i (e.symm w) : ℝ) : ℂ)

omit [T2Space X] [CompactSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem contDiffOn_psiC (i : Fin PU.n) {e : OpenPartialHomeomorph X ℂ}
    (he : e ∈ maximalAtlas 𝓘(ℂ) ω X) : ContDiffOn ℝ ∞ (PU.psiC i e) e.target :=
  Complex.ofRealCLM.contDiff.comp_contDiffOn
    (contDiffOn_comp_symm_real (PU.contMDiff i) he)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] [T2Space X] [CompactSpace X] in
/-- The complexified partition function vanishes near any target point whose source point is
outside the support. -/
theorem psiC_eventuallyEq_zero (i : Fin PU.n) {e : OpenPartialHomeomorph X ℂ} {z : ℂ}
    (hz : z ∈ e.target) (hy : e.symm z ∉ tsupport (PU.ψ i)) :
    PU.psiC i e =ᶠ[nhds z] 0 := by
  have hcont : ContinuousAt (⇑e.symm) z := e.symm.continuousAt (by simpa using hz)
  have hnhds : (tsupport (PU.ψ i))ᶜ ∈ nhds (e.symm z) :=
    (isClosed_tsupport _).isOpen_compl.mem_nhds hy
  filter_upwards [hcont.preimage_mem_nhds hnhds] with w hw
  simp only [psiC, Pi.zero_apply, Complex.ofReal_eq_zero]
  exact image_eq_zero_of_notMem_tsupport hw

omit [IsManifold 𝓘(ℂ, ℂ) ω X] [T2Space X] [CompactSpace X] in
theorem wirtingerDbar_psiC_eq_zero (i : Fin PU.n) {e : OpenPartialHomeomorph X ℂ} {z : ℂ}
    (hz : z ∈ e.target) (hy : e.symm z ∉ tsupport (PU.ψ i)) :
    RS.wirtingerDbar (PU.psiC i e) z = 0 := by
  rw [RS.wirtingerDbar_congr_nhds _ _ z (PU.psiC_eventuallyEq_zero i hz hy)]
  exact RS.wirtingerDbar_const z 0

omit [T2Space X] [CompactSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem differentiableAt_psiC (i : Fin PU.n) {e : OpenPartialHomeomorph X ℂ}
    (he : e ∈ maximalAtlas 𝓘(ℂ) ω X) {z : ℂ} (hz : z ∈ e.target) :
    DifferentiableAt ℝ (PU.psiC i e) z :=
  (((PU.contDiffOn_psiC i he).contDiffAt (e.open_target.mem_nhds hz)).differentiableAt
    (by norm_num))

omit [IsManifold 𝓘(ℂ, ℂ) ω X] [T2Space X] [CompactSpace X] in
/-- On a chart target, the complexified partition functions sum to `1` near every point. -/
theorem sum_psiC_eventuallyEq_one {e : OpenPartialHomeomorph X ℂ} {z : ℂ}
    (hz : z ∈ e.target) :
    (fun w => ∑ i, PU.psiC i e w) =ᶠ[nhds z] (fun _ => (1 : ℂ)) := by
  filter_upwards [e.open_target.mem_nhds hz] with w _
  simp only [psiC]
  rw [← Complex.ofReal_sum, PU.sum_eq_one (e.symm w), Complex.ofReal_one]

end SurfPoU

/-! ## Planar sum rule for `dbar` and eventual-vanishing helpers -/

theorem wirtingerDbar_finset_sum {ι' : Type*} (s : Finset ι') {f : ι' → ℂ → ℂ} {z : ℂ}
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) z) :
    RS.wirtingerDbar (fun w => ∑ i ∈ s, f i w) z = ∑ i ∈ s, RS.wirtingerDbar (f i) z := by
  induction s using Finset.cons_induction with
  | empty => simpa using RS.wirtingerDbar_const z 0
  | cons a s ha ih =>
      have hfa : DifferentiableAt ℝ (f a) z := hf a (Finset.mem_cons_self a s)
      have hfs : DifferentiableAt ℝ (fun w => ∑ i ∈ s, f i w) z :=
        DifferentiableAt.fun_sum (fun i hi => hf i (Finset.mem_cons_of_mem hi))
      have hadd := RS.wirtingerDbar_add (f a) (fun w => ∑ i ∈ s, f i w) z hfa hfs
      have hshape : (fun w => ∑ i ∈ Finset.cons a s ha, f i w)
          = f a + fun w => ∑ i ∈ s, f i w := by
        funext w; simp [Finset.sum_cons]
      rw [hshape, hadd, ih (fun i hi => hf i (Finset.mem_cons_of_mem hi)), Finset.sum_cons]

/-- Indicator functions vanishing off a compact carrier vanish on a neighborhood of any point
outside the carrier. -/
theorem indicator_eventuallyEq_zero_of_notMem {E : Type*} [Zero E] {F : ℂ → E} {T K : Set ℂ}
    (hK : IsCompact K) (h0 : ∀ z ∈ T, z ∉ K → F z = 0) {z : ℂ} (hz : z ∉ K) :
    T.indicator F =ᶠ[nhds z] 0 := by
  filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hz] with w hw
  by_cases hwT : w ∈ T
  · simp only [Set.indicator_of_mem hwT, h0 w hwT hw, Pi.zero_apply]
  · simp only [Set.indicator_of_notMem hwT, Pi.zero_apply]

/-! ## The pairing -/

variable [T2Space X] [CompactSpace X]

/-- The `i`-th planar integrand of the Serre pairing: `ψ_i · σ_i · ω_i` read in the `i`-th
chart, extended by `0` off the chart target. -/
def pairingTerm (PU : SurfPoU X) (σ : RS.Form01 X) (θ : RS.Form1 X) (i : Fin PU.n) : ℂ → ℂ :=
  ((PU.chart i).target).indicator
    (fun z => PU.ψ i ((PU.chart i).symm z) •
      (σ.coeffAt (PU.pt i) z * RS.coeffIn (PU.chart i) θ z))

omit [T2Space X] [CompactSpace X] in
/-- The core of the pairing integrand vanishes on the chart target off the compact carrier. -/
theorem pairingTerm_core_eq_zero_off (PU : SurfPoU X) (σ : RS.Form01 X) (θ : RS.Form1 X)
    (i : Fin PU.n) : ∀ z ∈ (PU.chart i).target, z ∉ PU.K i →
      PU.ψ i ((PU.chart i).symm z) • (σ.coeffAt (PU.pt i) z * RS.coeffIn (PU.chart i) θ z) = 0 := by
  intro z hz hzK
  rw [PU.psi_symm_eq_zero i hz hzK, zero_smul]

omit [T2Space X] [CompactSpace X] in
/-- Smoothness of the pairing integrand core on the chart target. -/
theorem contDiffOn_pairingTerm_core (PU : SurfPoU X) (σ : RS.Form01 X) (θ : RS.Form1 X)
    (i : Fin PU.n) : ContDiffOn ℝ ∞
      (fun z => PU.ψ i ((PU.chart i).symm z) •
        (σ.coeffAt (PU.pt i) z * RS.coeffIn (PU.chart i) θ z)) (PU.chart i).target := by
  have h1 : ContDiffOn ℝ ∞ (fun z => PU.ψ i ((PU.chart i).symm z)) (PU.chart i).target :=
    contDiffOn_comp_symm_real (PU.contMDiff i) (PU.chart_mem_maximalAtlas i)
  have h2 : ContDiffOn ℝ ∞
      (fun z => σ.coeffAt (PU.pt i) z * RS.coeffIn (PU.chart i) θ z) (PU.chart i).target :=
    (σ.contDiffOn_coeffAt (PU.pt i)).mul (contDiffOn_coeffIn θ (PU.chart_mem_maximalAtlas i))
  exact h1.smul h2

omit [T2Space X] in
theorem contDiff_pairingTerm (PU : SurfPoU X) (σ : RS.Form01 X) (θ : RS.Form1 X)
    (i : Fin PU.n) : ContDiff ℝ ∞ (pairingTerm PU σ θ i) :=
  contDiff_indicator_of_eq_zero_off (PU.chart i).open_target (PU.isCompact_K i)
    (PU.K_subset_target i) (contDiffOn_pairingTerm_core PU σ θ i)
    (pairingTerm_core_eq_zero_off PU σ θ i)

omit [T2Space X] in
theorem hasCompactSupport_pairingTerm (PU : SurfPoU X) (σ : RS.Form01 X) (θ : RS.Form1 X)
    (i : Fin PU.n) : HasCompactSupport (pairingTerm PU σ θ i) :=
  hasCompactSupport_indicator_of_eq_zero_off (PU.isCompact_K i)
    (pairingTerm_core_eq_zero_off PU σ θ i)

omit [T2Space X] in
theorem integrable_pairingTerm (PU : SurfPoU X) (σ : RS.Form01 X) (θ : RS.Form1 X)
    (i : Fin PU.n) : Integrable (pairingTerm PU σ θ i) :=
  ((contDiff_pairingTerm PU σ θ i).continuous).integrable_of_hasCompactSupport
    (hasCompactSupport_pairingTerm PU σ θ i)

/-- **The Serre area pairing** over the fixed partition datum `PU`:
`∑ i, ∫ z, ψ_i(z) σ_i(z) ω_i(z) dA(z)`. -/
def pairing (PU : SurfPoU X) (σ : RS.Form01 X) (θ : RS.Form1 X) : ℂ :=
  ∑ i, ∫ z : ℂ, pairingTerm PU σ θ i z

/-! ### Bilinearity -/

omit [T2Space X] [CompactSpace X] in
theorem pairingTerm_add_left (PU : SurfPoU X) (σ σ' : RS.Form01 X) (θ : RS.Form1 X)
    (i : Fin PU.n) : pairingTerm PU (σ + σ') θ i =
      fun z => pairingTerm PU σ θ i z + pairingTerm PU σ' θ i z := by
  funext z
  simp only [pairingTerm]
  by_cases hz : z ∈ (PU.chart i).target
  · simp only [Set.indicator_of_mem hz, RS.Form01.coeffAt_add, 
      Complex.real_smul]
    ring
  · simp [Set.indicator_of_notMem hz]

omit [T2Space X] [CompactSpace X] in
theorem pairingTerm_smul_left (PU : SurfPoU X) (c : ℂ) (σ : RS.Form01 X) (θ : RS.Form1 X)
    (i : Fin PU.n) : pairingTerm PU (c • σ) θ i = fun z => c * pairingTerm PU σ θ i z := by
  funext z
  simp only [pairingTerm]
  by_cases hz : z ∈ (PU.chart i).target
  · simp only [Set.indicator_of_mem hz, RS.Form01.coeffAt_smul, 
      Complex.real_smul]
    ring
  · simp [Set.indicator_of_notMem hz]

omit [T2Space X] [CompactSpace X] in
theorem pairingTerm_add_right (PU : SurfPoU X) (σ : RS.Form01 X) (θ θ' : RS.Form1 X)
    (i : Fin PU.n) : pairingTerm PU σ (θ + θ') i =
      fun z => pairingTerm PU σ θ i z + pairingTerm PU σ θ' i z := by
  funext z
  simp only [pairingTerm]
  by_cases hz : z ∈ (PU.chart i).target
  · simp only [Set.indicator_of_mem hz, RS.coeffIn_add, Complex.real_smul]
    ring
  · simp [Set.indicator_of_notMem hz]

omit [T2Space X] [CompactSpace X] in
theorem pairingTerm_smul_right (PU : SurfPoU X) (c : ℂ) (σ : RS.Form01 X) (θ : RS.Form1 X)
    (i : Fin PU.n) : pairingTerm PU σ (c • θ) i = fun z => c * pairingTerm PU σ θ i z := by
  funext z
  simp only [pairingTerm]
  by_cases hz : z ∈ (PU.chart i).target
  · simp only [Set.indicator_of_mem hz, RS.coeffIn_smul, Complex.real_smul]
    ring
  · simp [Set.indicator_of_notMem hz]

omit [T2Space X] in
theorem pairing_add_left (PU : SurfPoU X) (σ σ' : RS.Form01 X) (θ : RS.Form1 X) :
    pairing PU (σ + σ') θ = pairing PU σ θ + pairing PU σ' θ := by
  rw [pairing, pairing, pairing, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [pairingTerm_add_left]
  exact MeasureTheory.integral_add (integrable_pairingTerm PU σ θ i)
    (integrable_pairingTerm PU σ' θ i)

omit [T2Space X] [CompactSpace X] in
theorem pairing_smul_left (PU : SurfPoU X) (c : ℂ) (σ : RS.Form01 X) (θ : RS.Form1 X) :
    pairing PU (c • σ) θ = c * pairing PU σ θ := by
  rw [pairing, pairing, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [pairingTerm_smul_left]
  exact MeasureTheory.integral_const_mul c _

omit [T2Space X] in
theorem pairing_add_right (PU : SurfPoU X) (σ : RS.Form01 X) (θ θ' : RS.Form1 X) :
    pairing PU σ (θ + θ') = pairing PU σ θ + pairing PU σ θ' := by
  rw [pairing, pairing, pairing, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [pairingTerm_add_right]
  exact MeasureTheory.integral_add (integrable_pairingTerm PU σ θ i)
    (integrable_pairingTerm PU σ θ' i)

omit [T2Space X] [CompactSpace X] in
theorem pairing_smul_right (PU : SurfPoU X) (c : ℂ) (σ : RS.Form01 X) (θ : RS.Form1 X) :
    pairing PU σ (c • θ) = c * pairing PU σ θ := by
  rw [pairing, pairing, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [pairingTerm_smul_right]
  exact MeasureTheory.integral_const_mul c _

end RS.Abel

end
