/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Abel.AreaPairing

/-!
# abel-theorem: chart-supported `(0,1)`-forms and pairing localization (design §4.1 step 5)

Unit: abel-theorem. Namespace `RS.Abel`.

The packaging device for design step 5: a planar function `h` smooth on `ℂ`, supported in a
compact `K` inside the target of one maximal-atlas chart `e`, spreads to a global
`(0,1)`-form `ChartSupportedData.form` whose coefficient in any preferred chart is the
`conj (deriv τ)`-transported copy of `h` (exactly `Form01.compat`'s law) — the concrete global
object that a weak solution's chart-local `dbarf/f`-data assembles into.

Two consumption lemmas:

* `ChartSupportedData.coeffAt_center` / `coeffAt_center_of_notMem`: the coefficient at a chart
  center, active and inactive cases (feeding the `dbar`-matching of `UpgradeDischarge.lean`).
* **`pairing_form`** (the localization): `pairing PU D.form θ = ∫ z, h z · coeffIn e θ z` — the
  global PoU pairing of a chart-supported form collapses to ONE planar integral in the
  supporting chart. Proof: per PoU index, transport by the `(1,1)`-density change of variables
  (`integral_eq_integral_transition`), where the `conj (deriv)`-factor of the form's transported
  coefficient cancels against the transition's `normSq (deriv)` and `coeffIn_trans`
  (`deriv_trans_mul_deriv_trans_symm`), then sum `∑ᵢ ψᵢ = 1`.

Also here: the inverse-derivative units `deriv_trans_mul_deriv_trans_symm` /
`deriv_trans_ne_zero` (consumed again by the order bookkeeping in `UpgradeDischarge.lean`), and
`Form01.coeffAt_finsetSum`.
-/

open scoped ContDiff Manifold
open IsManifold Metric Set MeasureTheory


noncomputable section

namespace RS.Abel

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## Inverse-derivative units -/

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- The two transition derivatives at matched points multiply to `1`. -/
theorem deriv_trans_mul_deriv_trans_symm {e e' : OpenPartialHomeomorph X ℂ}
    (he : e ∈ maximalAtlas 𝓘(ℂ) ω X) (he' : e' ∈ maximalAtlas 𝓘(ℂ) ω X) {w : ℂ}
    (hw : w ∈ ⇑e' '' (e.source ∩ e'.source)) :
    deriv (⇑e ∘ ⇑e'.symm) w * deriv (⇑e' ∘ ⇑e.symm) (e (e'.symm w)) = 1 := by
  obtain ⟨q, hq, rfl⟩ := hw
  have hq' : (e'.symm) (e' q) = q := e'.left_inv hq.2
  have hwt : e' q ∈ e'.target := e'.map_source hq.2
  -- `deriv_trans_comp` with the roles `(e := e', e' := e, f := e')`
  have hcomp := RS.deriv_trans_comp (e := e') (e' := e) (f := e') he' he he' hwt
    (by rw [hq']; exact hq.2) (by rw [hq']; exact hq.1)
  -- the left side is the derivative of the identity near `e' q`
  have hid : deriv (⇑e' ∘ ⇑e'.symm) (e' q) = 1 := by
    have hev : (⇑e' ∘ ⇑e'.symm) =ᶠ[nhds (e' q)] id := by
      filter_upwards [e'.open_target.mem_nhds hwt] with w' hw'
      exact e'.right_inv hw'
    rw [hev.deriv_eq, deriv_id]
  rw [hid, hq'] at hcomp
  rw [hq']
  linear_combination -hcomp

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Transition derivatives never vanish. -/
theorem deriv_trans_ne_zero {e e' : OpenPartialHomeomorph X ℂ}
    (he : e ∈ maximalAtlas 𝓘(ℂ) ω X) (he' : e' ∈ maximalAtlas 𝓘(ℂ) ω X) {w : ℂ}
    (hw : w ∈ ⇑e' '' (e.source ∩ e'.source)) :
    deriv (⇑e ∘ ⇑e'.symm) w ≠ 0 :=
  left_ne_zero_of_mul_eq_one (deriv_trans_mul_deriv_trans_symm he he' hw)

/-! ## Finset sums of `(0,1)`-form coefficients -/

omit [T2Space X] in
theorem Form01.coeffAt_finsetSum {ι : Type*} (s : Finset ι) (F : ι → RS.Form01 X) (x : X)
    (z : ℂ) : (∑ k ∈ s, F k).coeffAt x z = ∑ k ∈ s, (F k).coeffAt x z := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, RS.Form01.coeffAt_add, ih]

/-! ## Chart-supported `(0,1)`-data -/

variable (X) in
/-- A planar `(0,1)`-coefficient supported compactly inside one maximal-atlas chart. -/
structure ChartSupportedData where
  /-- The supporting chart. -/
  e : OpenPartialHomeomorph X ℂ
  he : e ∈ maximalAtlas 𝓘(ℂ) ω X
  /-- The planar coefficient in the supporting chart. -/
  h : ℂ → ℂ
  smooth : ContDiff ℝ ∞ h
  /-- The compact planar carrier. -/
  K : Set ℂ
  hK : IsCompact K
  hKsub : K ⊆ e.target
  hsupp : Function.support h ⊆ K

namespace ChartSupportedData

variable (D : ChartSupportedData X)

/-- The source-side compact carrier. -/
def Ksrc : Set X := ⇑D.e.symm '' D.K

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem isCompact_Ksrc : IsCompact D.Ksrc :=
  D.hK.image_of_continuousOn (D.e.symm.continuousOn.mono (by simpa using D.hKsub))

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem Ksrc_subset_source : D.Ksrc ⊆ D.e.source := by
  rintro y ⟨z, hz, rfl⟩
  exact D.e.map_target (D.hKsub hz)

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem h_eq_zero_of_notMem_Ksrc {y : X} (hy : y ∈ D.e.source) (hyK : y ∉ D.Ksrc) :
    D.h (D.e y) = 0 := by
  by_contra hne
  have hzK : D.e y ∈ D.K := D.hsupp hne
  exact hyK ⟨D.e y, hzK, D.e.left_inv hy⟩

/-- The raw coefficient formula in the preferred chart at `x`. -/
def coeff (x : X) : ℂ → ℂ :=
  (⇑(chartAt ℂ x) '' ((chartAt ℂ x).source ∩ D.e.source)).indicator
    (fun z => (starRingEnd ℂ) (deriv (⇑D.e ∘ ⇑(chartAt ℂ x).symm) z) *
      D.h (D.e ((chartAt ℂ x).symm z)))

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem mem_coeffSet_iff (x : X) {z : ℂ} (hz : z ∈ (chartAt ℂ x).target) :
    (chartAt ℂ x).symm z ∈ D.e.source ↔
      z ∈ ⇑(chartAt ℂ x) '' ((chartAt ℂ x).source ∩ D.e.source) := by
  constructor
  · intro h1
    exact ⟨(chartAt ℂ x).symm z, ⟨(chartAt ℂ x).map_target hz, h1⟩,
      (chartAt ℂ x).right_inv hz⟩
  · rintro ⟨q, hq, rfl⟩
    rw [(chartAt ℂ x).left_inv hq.1]
    exact hq.2

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem coeffSet_subset_target (x : X) :
    ⇑(chartAt ℂ x) '' ((chartAt ℂ x).source ∩ D.e.source) ⊆ (chartAt ℂ x).target := by
  rintro z ⟨q, hq, rfl⟩
  exact (chartAt ℂ x).map_source hq.1

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- The coefficient vanishes near any target point whose source point avoids the compact
source carrier. -/
theorem coeff_eventuallyEq_zero (x : X) {z : ℂ} (hz : z ∈ (chartAt ℂ x).target)
    (hy : (chartAt ℂ x).symm z ∉ D.Ksrc) : D.coeff x =ᶠ[nhds z] 0 := by
  have hcont : ContinuousAt (⇑(chartAt ℂ x).symm) z :=
    (chartAt ℂ x).symm.continuousAt (by simpa using hz)
  have hnhds : (D.Ksrc)ᶜ ∈ nhds ((chartAt ℂ x).symm z) :=
    D.isCompact_Ksrc.isClosed.isOpen_compl.mem_nhds hy
  filter_upwards [hcont.preimage_mem_nhds hnhds] with w hw
  by_cases hwS : w ∈ ⇑(chartAt ℂ x) '' ((chartAt ℂ x).source ∩ D.e.source)
  · have hwsrc : (chartAt ℂ x).symm w ∈ D.e.source := by
      rcases hwS with ⟨q, hq, rfl⟩
      rw [(chartAt ℂ x).left_inv hq.1]
      exact hq.2
    rw [coeff, Set.indicator_of_mem hwS,
      D.h_eq_zero_of_notMem_Ksrc hwsrc hw, mul_zero]
    rfl
  · rw [coeff, Set.indicator_of_notMem hwS]
    rfl

/-- The chart-supported global `(0,1)`-form. -/
def form : RS.Form01 X where
  coeffAt := D.coeff
  coeffAt_zero_off x z hz :=
    Set.indicator_of_notMem (fun h1 => hz (D.coeffSet_subset_target x h1)) _
  contDiffOn_coeffAt x := by
    intro z hz
    by_cases hzS : z ∈ ⇑(chartAt ℂ x) '' ((chartAt ℂ x).source ∩ D.e.source)
    · -- smooth on the open overlap image
      have hSopen : IsOpen (⇑(chartAt ℂ x) '' ((chartAt ℂ x).source ∩ D.e.source)) :=
        (chartAt ℂ x).isOpen_image_of_subset_source
          ((chartAt ℂ x).open_source.inter D.e.open_source) inter_subset_left
      have hτ : AnalyticAt ℂ (⇑D.e ∘ ⇑(chartAt ℂ x).symm) z := by
        rcases hzS with ⟨q, hq, rfl⟩
        exact RS.analyticAt_trans D.he (IsManifold.chart_mem_maximalAtlas x)
          ((chartAt ℂ x).map_source hq.1) (by rw [(chartAt ℂ x).left_inv hq.1]; exact hq.2)
      have hτnhds : ∀ᶠ w in nhds z, AnalyticAt ℂ (⇑D.e ∘ ⇑(chartAt ℂ x).symm) w := by
        filter_upwards [hSopen.mem_nhds hzS] with w hw
        rcases hw with ⟨q, hq, rfl⟩
        exact RS.analyticAt_trans D.he (IsManifold.chart_mem_maximalAtlas x)
          ((chartAt ℂ x).map_source hq.1) (by rw [(chartAt ℂ x).left_inv hq.1]; exact hq.2)
      have hderiv : ContDiffAt ℝ ∞ (fun w => deriv (⇑D.e ∘ ⇑(chartAt ℂ x).symm) w) z := by
        have hda : AnalyticAt ℂ (deriv (⇑D.e ∘ ⇑(chartAt ℂ x).symm)) z := by
          have := hτ.deriv
          exact this
        exact hda.contDiffAt.restrict_scalars ℝ
      have hconjd : ContDiffAt ℝ ∞
          (fun w => (starRingEnd ℂ) (deriv (⇑D.e ∘ ⇑(chartAt ℂ x).symm) w)) z := by
        have h1 := Complex.conjCLE.contDiff.contDiffAt.comp z hderiv
        refine h1.congr_of_eventuallyEq ?_
        filter_upwards with w
        simp []
      have hhcomp : ContDiffAt ℝ ∞ (fun w => D.h (D.e ((chartAt ℂ x).symm w))) z := by
        have hτr : ContDiffAt ℝ ∞ (⇑D.e ∘ ⇑(chartAt ℂ x).symm) z :=
          hτ.contDiffAt.restrict_scalars ℝ
        exact (D.smooth.contDiffAt).comp z hτr
      refine ((hconjd.mul hhcomp).congr_of_eventuallyEq ?_).contDiffWithinAt
      filter_upwards [hSopen.mem_nhds hzS] with w hw
      rw [coeff, Set.indicator_of_mem hw]
    · -- vanishes near `z`
      have hy : (chartAt ℂ x).symm z ∉ D.Ksrc := by
        intro hmem
        exact hzS ((D.mem_coeffSet_iff x hz).mp (D.Ksrc_subset_source hmem))
      refine ((contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_).contDiffWithinAt
      filter_upwards [D.coeff_eventuallyEq_zero x hz hy] with w hw
      exact hw
  compat x y z hz := by
    have hzT : z ∈ (chartAt ℂ y).target := by
      rcases hz with ⟨q, hq, rfl⟩
      exact (chartAt ℂ y).map_source hq.2
    have hq := hz
    obtain ⟨q, hq', rfl⟩ := hq
    have hqy : (chartAt ℂ y).symm (chartAt ℂ y q) = q := (chartAt ℂ y).left_inv hq'.2
    have hxT : chartAt ℂ x q ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source hq'.1
    by_cases hqe : q ∈ D.e.source
    · -- both indicators active; chain rule for the transition derivatives
      have hmemy : chartAt ℂ y q ∈ ⇑(chartAt ℂ y) '' ((chartAt ℂ y).source ∩ D.e.source) :=
        ⟨q, ⟨hq'.2, hqe⟩, rfl⟩
      have hmemx : chartAt ℂ x q ∈ ⇑(chartAt ℂ x) '' ((chartAt ℂ x).source ∩ D.e.source) :=
        ⟨q, ⟨hq'.1, hqe⟩, rfl⟩
      have hchain := RS.deriv_trans_comp (e := D.e) (e' := chartAt ℂ x) (f := chartAt ℂ y)
        D.he (IsManifold.chart_mem_maximalAtlas x) (IsManifold.chart_mem_maximalAtlas y)
        hzT (by rw [hqy]; exact hqe) (by rw [hqy]; exact hq'.1)
      rw [coeff, Set.indicator_of_mem hmemy, coeff]
      rw [hqy] at hchain ⊢
      have hsymm_x : (chartAt ℂ x).symm (chartAt ℂ x q) = q := (chartAt ℂ x).left_inv hq'.1
      rw [Set.indicator_of_mem hmemx, hsymm_x, hchain, map_mul]
      ring
    · -- both sides vanish
      have hmemy : chartAt ℂ y q ∉ ⇑(chartAt ℂ y) '' ((chartAt ℂ y).source ∩ D.e.source) :=
        fun h1 => hqe (by
          have := (D.mem_coeffSet_iff y hzT).mpr h1
          rwa [hqy] at this)
      have hmemx : chartAt ℂ x q ∉ ⇑(chartAt ℂ x) '' ((chartAt ℂ x).source ∩ D.e.source) :=
        fun h1 => hqe (by
          have := (D.mem_coeffSet_iff x hxT).mpr h1
          rwa [(chartAt ℂ x).left_inv hq'.1] at this)
      rw [coeff, Set.indicator_of_notMem hmemy, hqy, coeff,
        Set.indicator_of_notMem hmemx, mul_zero]

/-- The coefficient at an active chart center. -/
theorem form_coeffAt_center {x : X} (hx : x ∈ D.e.source) :
    D.form.coeffAt x (chartAt ℂ x x)
      = (starRingEnd ℂ) (deriv (⇑D.e ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x)) *
        D.h (D.e x) := by
  have hmem : chartAt ℂ x x ∈ ⇑(chartAt ℂ x) '' ((chartAt ℂ x).source ∩ D.e.source) :=
    ⟨x, ⟨mem_chart_source ℂ x, hx⟩, rfl⟩
  change D.coeff x (chartAt ℂ x x) = _
  rw [coeff, Set.indicator_of_mem hmem, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)]

/-- The coefficient at an inactive chart center. -/
theorem form_coeffAt_center_of_notMem {x : X} (hx : x ∉ D.e.source) :
    D.form.coeffAt x (chartAt ℂ x x) = 0 := by
  have hmem : chartAt ℂ x x ∉ ⇑(chartAt ℂ x) '' ((chartAt ℂ x).source ∩ D.e.source) := by
    intro h1
    exact hx (by
      have := (D.mem_coeffSet_iff x (mem_chart_target ℂ x)).mpr h1
      rwa [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)] at this)
  change D.coeff x (chartAt ℂ x x) = 0
  rw [coeff, Set.indicator_of_notMem hmem]

end ChartSupportedData

/-! ## Pairing localization -/

variable [CompactSpace X]

omit [CompactSpace X] in
/-- **The localization lemma**: the global PoU pairing of a chart-supported `(0,1)`-form
collapses to a single planar integral in the supporting chart. -/
theorem pairing_form (PU : SurfPoU X) (D : ChartSupportedData X) (θ : RS.Form1 X) :
    pairing PU D.form θ = ∫ z : ℂ, D.h z * RS.coeffIn D.e θ z := by
  classical
  -- the transported per-index integrands in the supporting chart
  set G : Fin PU.n → ℂ → ℂ := fun i =>
    (⇑D.e '' ((chartAt ℂ (PU.pt i)).source ∩ D.e.source)).indicator
      (fun w => PU.ψ i (D.e.symm w) • (D.h w * RS.coeffIn D.e θ w)) with hG_def
  have hGsubT : ∀ i, ⇑D.e '' ((chartAt ℂ (PU.pt i)).source ∩ D.e.source) ⊆ D.e.target := by
    rintro i w ⟨q, hq, rfl⟩
    exact D.e.map_source hq.2
  have hGopen : ∀ i, IsOpen (⇑D.e '' ((chartAt ℂ (PU.pt i)).source ∩ D.e.source)) := fun i =>
    D.e.isOpen_image_of_subset_source
      (((chartAt ℂ (PU.pt i)).open_source).inter D.e.open_source) inter_subset_right
  -- gadget data for `G i`
  have hGK : ∀ i, IsCompact (⇑D.e '' (tsupport (PU.ψ i) ∩ D.Ksrc)) := by
    intro i
    exact (D.isCompact_Ksrc.inter_left (isClosed_tsupport _)).image_of_continuousOn
      (D.e.continuousOn.mono (Set.inter_subset_right.trans D.Ksrc_subset_source))
  have hGKsub : ∀ i, ⇑D.e '' (tsupport (PU.ψ i) ∩ D.Ksrc) ⊆
      ⇑D.e '' ((chartAt ℂ (PU.pt i)).source ∩ D.e.source) :=
    fun i => Set.image_mono (fun q hq =>
      ⟨PU.tsupport_subset i hq.1, D.Ksrc_subset_source hq.2⟩)
  have hGcore0 : ∀ i, ∀ w ∈ ⇑D.e '' ((chartAt ℂ (PU.pt i)).source ∩ D.e.source),
      w ∉ ⇑D.e '' (tsupport (PU.ψ i) ∩ D.Ksrc) →
      PU.ψ i (D.e.symm w) • (D.h w * RS.coeffIn D.e θ w) = 0 := by
    rintro i w ⟨q, hq, rfl⟩ hwK
    have hsymm : D.e.symm (D.e q) = q := D.e.left_inv hq.2
    have hqK : q ∉ tsupport (PU.ψ i) ∩ D.Ksrc := fun hmem => hwK ⟨q, hmem, rfl⟩
    by_cases hq1 : q ∈ tsupport (PU.ψ i)
    · have hq2 : q ∉ D.Ksrc := fun h1 => hqK ⟨hq1, h1⟩
      rw [D.h_eq_zero_of_notMem_Ksrc hq.2 hq2, zero_mul, smul_zero]
    · rw [hsymm, image_eq_zero_of_notMem_tsupport hq1, zero_smul]
  have hGcore_cd : ∀ i, ContDiffOn ℝ ∞
      (fun w => PU.ψ i (D.e.symm w) • (D.h w * RS.coeffIn D.e θ w))
      (⇑D.e '' ((chartAt ℂ (PU.pt i)).source ∩ D.e.source)) := by
    intro i
    have h1 : ContDiffOn ℝ ∞ (fun w => PU.ψ i (D.e.symm w)) D.e.target :=
      contDiffOn_comp_symm_real (PU.contMDiff i) D.he
    exact (h1.mono (hGsubT i)).smul
      (((D.smooth.contDiffOn).mul (contDiffOn_coeffIn θ D.he)).mono (hGsubT i))
  have hGint : ∀ i, Integrable (G i) := fun i =>
    integrable_indicator_of_eq_zero_off (hGopen i) (hGK i) (hGKsub i) (hGcore_cd i)
      (hGcore0 i)
  -- Step 1: per-index change of variables `∫ pairingTerm i = ∫ G i`
  have hstep1 : ∀ i, ∫ z : ℂ, pairingTerm PU (D.form) θ i z = ∫ w : ℂ, G i w := by
    intro i
    refine integral_eq_integral_transition (PU.chart_mem_maximalAtlas i) D.he
      (fun z hz => ?_) (fun w hw => ?_) (fun w hw => ?_)
    · -- `pairingTerm` vanishes off the overlap image in chart `i`
      rw [pairingTerm]
      by_cases hzT : z ∈ (PU.chart i).target
      · rw [Set.indicator_of_mem hzT]
        have hcoeff : D.form.coeffAt (PU.pt i) z = 0 := by
          change D.coeff (PU.pt i) z = 0
          rw [ChartSupportedData.coeff, Set.indicator_of_notMem]
          intro hmem
          exact hz hmem
        rw [hcoeff, zero_mul, smul_zero]
      · rw [Set.indicator_of_notMem hzT]
    · rw [hG_def]
      dsimp only
      rw [Set.indicator_of_notMem hw]
    · -- the transported identity
      obtain ⟨q, hq, rfl⟩ := hw
      have hsymm_e : D.e.symm (D.e q) = q := D.e.left_inv hq.2
      have hwT : D.e q ∈ D.e.target := D.e.map_source hq.2
      set τ : ℂ → ℂ := ⇑(PU.chart i) ∘ ⇑D.e.symm with hτ_def
      have hτw : τ (D.e q) = (PU.chart i) q := by
        rw [hτ_def]
        simp only [Function.comp_apply, hsymm_e]
      have hτmem : τ (D.e q) ∈
          ⇑(PU.chart i) '' ((PU.chart i).source ∩ D.e.source) := by
        rw [hτw]; exact ⟨q, hq, rfl⟩
      have hτT : τ (D.e q) ∈ (PU.chart i).target := by
        rw [hτw]; exact (PU.chart i).map_source hq.1
      have hsymm_i : (PU.chart i).symm (τ (D.e q)) = q := by
        rw [hτw]; exact (PU.chart i).left_inv hq.1
      have hwmem : D.e q ∈ ⇑D.e '' ((PU.chart i).source ∩ D.e.source) := ⟨q, hq, rfl⟩
      -- the coefficient of the chart-supported form at the transported point
      have hcoeff : D.form.coeffAt (PU.pt i) (τ (D.e q))
          = (starRingEnd ℂ) (deriv (⇑D.e ∘ ⇑(PU.chart i).symm) (τ (D.e q))) *
            D.h (D.e q) := by
        change D.coeff (PU.pt i) (τ (D.e q)) = _
        have hmem : τ (D.e q) ∈
            ⇑(chartAt ℂ (PU.pt i)) '' ((chartAt ℂ (PU.pt i)).source ∩ D.e.source) := by
          rw [hτw]; exact ⟨q, ⟨hq.1, hq.2⟩, rfl⟩
        rw [ChartSupportedData.coeff, Set.indicator_of_mem hmem, hsymm_i]
      -- the coefficient transition for `θ`
      have hT2 : RS.coeffIn D.e θ (D.e q)
          = deriv τ (D.e q) * RS.coeffIn (PU.chart i) θ (τ (D.e q)) := by
        have := RS.coeffIn_trans (PU.chart_mem_maximalAtlas i) D.he θ
          (z := D.e q) hwmem
        rw [this, hτ_def]
        simp only [Function.comp_apply]
      -- the inverse-derivative unit
      have hunit : deriv τ (D.e q) *
          deriv (⇑D.e ∘ ⇑(PU.chart i).symm) (τ (D.e q)) = 1 := by
        have := deriv_trans_mul_deriv_trans_symm (e := PU.chart i) (e' := D.e)
          (PU.chart_mem_maximalAtlas i) D.he hwmem
        rw [hτ_def]
        simpa using this
      -- assemble
      rw [hG_def]
      dsimp only
      rw [Set.indicator_of_mem hwmem, hsymm_e, ← hτw, pairingTerm,
        Set.indicator_of_mem hτT, hcoeff, hsymm_i, hT2]
      rw [Complex.real_smul, Complex.real_smul, Complex.real_smul,
        ← Complex.mul_conj (deriv τ (D.e q))]
      -- reduce to a ring identity using the unit relation
      have hconj_unit : (starRingEnd ℂ) (deriv τ (D.e q)) *
          (starRingEnd ℂ) (deriv (⇑D.e ∘ ⇑(PU.chart i).symm) (τ (D.e q))) = 1 := by
        rw [← map_mul, hunit, map_one]
      linear_combination (-((PU.ψ i q : ℝ) : ℂ) * D.h (D.e q) * deriv τ (D.e q) *
        RS.coeffIn (PU.chart i) θ (τ (D.e q))) * hconj_unit
  -- Step 2: sum the transported integrands
  have hstep2 : ∀ w, ∑ i, G i w = D.h w * RS.coeffIn D.e θ w := by
    intro w
    by_cases hw : w ∈ D.e.target
    · have huniform : ∀ i, G i w
          = PU.ψ i (D.e.symm w) • (D.h w * RS.coeffIn D.e θ w) := by
        intro i
        by_cases hyi : D.e.symm w ∈ (chartAt ℂ (PU.pt i)).source
        · have hmem : w ∈ ⇑D.e '' ((chartAt ℂ (PU.pt i)).source ∩ D.e.source) :=
            ⟨D.e.symm w, ⟨hyi, D.e.map_target hw⟩, D.e.right_inv hw⟩
          rw [hG_def]
          dsimp only
          rw [Set.indicator_of_mem hmem]
        · have hmem : w ∉ ⇑D.e '' ((chartAt ℂ (PU.pt i)).source ∩ D.e.source) := by
            rintro ⟨q, hq, rfl⟩
            rw [D.e.left_inv hq.2] at hyi
            exact hyi hq.1
          rw [hG_def]
          dsimp only
          rw [Set.indicator_of_notMem hmem,
            image_eq_zero_of_notMem_tsupport
              (fun hmem' => hyi (PU.tsupport_subset i hmem')), zero_smul]
      calc ∑ i, G i w = ∑ i, PU.ψ i (D.e.symm w) • (D.h w * RS.coeffIn D.e θ w) :=
            Finset.sum_congr rfl (fun i _ => huniform i)
        _ = (∑ i, PU.ψ i (D.e.symm w)) • (D.h w * RS.coeffIn D.e θ w) :=
            Finset.sum_smul.symm
        _ = D.h w * RS.coeffIn D.e θ w := by rw [PU.sum_eq_one (D.e.symm w), one_smul]
    · have hh0 : D.h w = 0 := by
        by_contra hne
        exact hw (D.hKsub (D.hsupp hne))
      have hzero : ∀ i, G i w = 0 := by
        intro i
        have hmem : w ∉ ⇑D.e '' ((chartAt ℂ (PU.pt i)).source ∩ D.e.source) :=
          fun h1 => hw (hGsubT i h1)
        rw [hG_def]
        dsimp only
        rw [Set.indicator_of_notMem hmem]
      rw [Finset.sum_congr rfl (fun i _ => hzero i), Finset.sum_const, smul_zero, hh0,
        zero_mul]
  -- assemble
  rw [pairing]
  calc ∑ i, ∫ z : ℂ, pairingTerm PU (D.form) θ i z
      = ∑ i, ∫ w : ℂ, G i w := Finset.sum_congr rfl (fun i _ => hstep1 i)
    _ = ∫ w : ℂ, ∑ i, G i w :=
        (MeasureTheory.integral_finsetSum _ (fun i _ => hGint i)).symm
    _ = ∫ w : ℂ, D.h w * RS.coeffIn D.e θ w := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
        exact hstep2 w

end RS.Abel

end
