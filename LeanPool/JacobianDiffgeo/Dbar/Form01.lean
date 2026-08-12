/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Surface
import LeanPool.JacobianDiffgeo.Forms.Analyticity

/-!
# `Form01 X`: smooth `(0,1)`-forms as chart-coefficient families (`Jacobian/Dbar/Form01.lean`)

Unit: dbar-solvability (`docs/design/dbar-solvability.md` D5/D8, §4.6).

Per design D5, `Form01 X` is **not** a bundled `ContMDiffSection` (unlike `Form1`, CC1): there is
no anti-linear Hom-bundle in mathlib at the pin, and the blueprint's `restrictScalars ℂ→ℝ`
diamond warning rules out building one. Instead `Form01 X` is a plain structure: a
`chartAt`-indexed family of coefficient functions (the coefficient of `dz-bar`), zero off chart
targets (junk-normalized so `ext` is honest), smooth on targets, with the anti-holomorphic
transition rule `coeff_y = conj (deriv τ) * (coeff_x ∘ τ)`. This mirrors the frozen CC1
`coeffIn` philosophy (`Jacobian/Forms/Coeffs.lean`) with `conj` inserted, reusing
`analyticAt_trans`/`deriv_trans_comp` from `Jacobian/Forms/Analyticity.lean`.

(Note: `η, η'` are used for `Form01` variables rather than the more suggestive `ω` — `ω` is a
reserved token in the ambient `ContDiff` scope's regularity level and cannot be reused as an
ordinary identifier.)
-/

open scoped ContDiff Manifold
open Set IsManifold

noncomputable section

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- A smooth `(0,1)`-form on `X`: a `chartAt`-indexed coefficient family for `dz-bar`, junk-zero off
chart targets, smooth on targets, related on overlaps by the anti-holomorphic transition rule. -/
structure Form01 (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] where
  /-- The coefficient function in the preferred chart at each point. -/
  coeffAt : X → ℂ → ℂ
  coeffAt_zero_off : ∀ x, ∀ z ∉ (chartAt ℂ x).target, coeffAt x z = 0
  contDiffOn_coeffAt : ∀ x, ContDiffOn ℝ ∞ (coeffAt x) (chartAt ℂ x).target
  compat : ∀ x y : X, ∀ z ∈ ⇑(chartAt ℂ y) '' ((chartAt ℂ x).source ∩ (chartAt ℂ y).source),
    coeffAt y z = (starRingEnd ℂ) (deriv (⇑(chartAt ℂ x) ∘ ⇑(chartAt ℂ y).symm) z) *
      coeffAt x (chartAt ℂ x ((chartAt ℂ y).symm z))

namespace Form01

/-- A `(0,1)`-form is determined by its preferred-chart coefficients on chart targets. -/
@[ext]
theorem ext {η η' : Form01 X}
    (h : ∀ x, ∀ z ∈ (chartAt ℂ x).target, η.coeffAt x z = η'.coeffAt x z) : η = η' := by
  have hcoeff : η.coeffAt = η'.coeffAt := by
    funext x z
    by_cases hz : z ∈ (chartAt ℂ x).target
    · exact h x z hz
    · rw [η.coeffAt_zero_off x z hz, η'.coeffAt_zero_off x z hz]
  obtain ⟨c1, _, _, _⟩ := η
  obtain ⟨c2, _, _, _⟩ := η'
  simp only at hcoeff
  subst hcoeff
  rfl

instance : Zero (Form01 X) where
  zero := ⟨fun _ _ => 0, fun _ _ _ => rfl, fun _ => contDiffOn_const, fun _ _ _ _ => by simp⟩

instance : Add (Form01 X) where
  add η η' := ⟨fun x z => η.coeffAt x z + η'.coeffAt x z,
    fun x z hz => by rw [η.coeffAt_zero_off x z hz, η'.coeffAt_zero_off x z hz, add_zero],
    fun x => (η.contDiffOn_coeffAt x).add (η'.contDiffOn_coeffAt x),
    fun x y z hz => by rw [η.compat x y z hz, η'.compat x y z hz]; ring⟩

instance : Neg (Form01 X) where
  neg η := ⟨fun x z => -η.coeffAt x z,
    fun x z hz => by rw [η.coeffAt_zero_off x z hz, neg_zero],
    fun x => (η.contDiffOn_coeffAt x).neg,
    fun x y z hz => by rw [η.compat x y z hz]; ring⟩

instance : Sub (Form01 X) where
  sub η η' := ⟨fun x z => η.coeffAt x z - η'.coeffAt x z,
    fun x z hz => by rw [η.coeffAt_zero_off x z hz, η'.coeffAt_zero_off x z hz, sub_zero],
    fun x => (η.contDiffOn_coeffAt x).sub (η'.contDiffOn_coeffAt x),
    fun x y z hz => by rw [η.compat x y z hz, η'.compat x y z hz]; ring⟩

instance : SMul ℂ (Form01 X) where
  smul c η := ⟨fun x z => c * η.coeffAt x z,
    fun x z hz => by rw [η.coeffAt_zero_off x z hz, mul_zero],
    fun x => contDiffOn_const.mul (η.contDiffOn_coeffAt x),
    fun x y z hz => by rw [η.compat x y z hz]; ring⟩

@[simp] theorem coeffAt_zero (x : X) (z : ℂ) : (0 : Form01 X).coeffAt x z = 0 := rfl

@[simp] theorem coeffAt_add (η η' : Form01 X) (x : X) (z : ℂ) :
    (η + η').coeffAt x z = η.coeffAt x z + η'.coeffAt x z := rfl

@[simp] theorem coeffAt_neg (η : Form01 X) (x : X) (z : ℂ) :
    (-η).coeffAt x z = -η.coeffAt x z := rfl

@[simp] theorem coeffAt_sub (η η' : Form01 X) (x : X) (z : ℂ) :
    (η - η').coeffAt x z = η.coeffAt x z - η'.coeffAt x z := rfl

@[simp] theorem coeffAt_smul (c : ℂ) (η : Form01 X) (x : X) (z : ℂ) :
    (c • η).coeffAt x z = c * η.coeffAt x z := rfl

instance : AddCommGroup (Form01 X) where
  add_assoc a b c := by ext x z _; simp; ring
  zero_add a := by ext x z _; simp
  add_zero a := by ext x z _; simp
  add_comm a b := by ext x z _; simp; ring
  neg_add_cancel a := by ext x z _; simp
  sub_eq_add_neg a b := by ext x z _; simp; ring
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Module ℂ (Form01 X) where
  smul_zero a := by ext x z _; simp
  smul_add a b c := by ext x z _; simp; ring
  add_smul a b c := by ext x z _; simp; ring
  zero_smul a := by ext x z _; simp
  one_smul a := by ext x z _; simp
  mul_smul a b c := by ext x z _; simp; ring

end Form01

/-! ### `Form01.ofCoeffs`: constructing forms from compatible chart-coefficient data

Transcribed from `Form1CoeffData`/`Form1.ofCoeffs` (`Jacobian/Forms/OfCoeffs.lean`), with a
`starRingEnd ℂ` (`conj`) inserted in the transition rule for the anti-holomorphic `(0,1)`-grading.
Unlike `Form1` (a bundled `ContMDiffSection`), `Form01` is a raw chart-coefficient structure, so
this construction is simpler than `Form1.ofCoeffs`: no covector/hom-bundle detour, just a direct
`X → ℂ → ℂ` assembly via a chosen covering-chart index per point (`idx`), verified independent of
the choice by the `compat` field + the transition chain rule (`RS.deriv_trans_comp`,
`RS.analyticAt_trans` from `Jacobian/Forms/Analyticity.lean`). Added under
dolbeault-comparison's authorization (needed by `GlueForm01.lean`'s `DbarGlueData.form`
constructor, design §6.1). -/

/-- Compatible smooth `(0,1)`-coefficient data over a covering family of `ω`-maximal-atlas
charts: a real-smooth coefficient function on each chart target, related on overlaps by the
`conj`-transition rule. -/
structure Form01CoeffData (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (ι : Type*) where
  /-- The covering chart family. -/
  chart : ι → OpenPartialHomeomorph X ℂ
  mem_maximalAtlas : ∀ i, chart i ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X
  exists_mem : ∀ x : X, ∃ i, x ∈ (chart i).source
  /-- The coefficient functions, one per chart. -/
  coeff : ι → ℂ → ℂ
  contDiffOn : ∀ i, ContDiffOn ℝ ∞ (coeff i) (chart i).target
  compat : ∀ i j, ∀ x ∈ (chart i).source ∩ (chart j).source,
    coeff j (chart j x) =
      (starRingEnd ℂ) (deriv (⇑(chart i) ∘ ⇑(chart j).symm) (chart j x)) * coeff i (chart i x)

namespace Form01CoeffData

variable {ι : Type*} (Data : Form01CoeffData X ι)

/-- A chosen chart index for each point. -/
def idx (x : X) : ι := (Data.exists_mem x).choose

theorem mem_source_idx (x : X) : x ∈ (Data.chart (Data.idx x)).source :=
  (Data.exists_mem x).choose_spec

open scoped Classical in
/-- The coefficient of the assembled `(0,1)`-form in the preferred chart at `x`, junk-`0` off the
chart target. -/
noncomputable def rawCoeffAt (x : X) (z : ℂ) : ℂ :=
  if _hz : z ∈ (chartAt ℂ x).target then
    (starRingEnd ℂ)
        (deriv (⇑(Data.chart (Data.idx ((chartAt ℂ x).symm z))) ∘ ⇑(chartAt ℂ x).symm) z) *
      Data.coeff (Data.idx ((chartAt ℂ x).symm z))
        (Data.chart (Data.idx ((chartAt ℂ x).symm z)) ((chartAt ℂ x).symm z))
  else 0

theorem rawCoeffAt_of_not_mem {x : X} {z : ℂ} (hz : z ∉ (chartAt ℂ x).target) :
    Data.rawCoeffAt x z = 0 := dite_eq_right hz

theorem rawCoeffAt_of_mem {x : X} {z : ℂ} (hz : z ∈ (chartAt ℂ x).target) :
    Data.rawCoeffAt x z =
      (starRingEnd ℂ)
          (deriv (⇑(Data.chart (Data.idx ((chartAt ℂ x).symm z))) ∘ ⇑(chartAt ℂ x).symm) z) *
        Data.coeff (Data.idx ((chartAt ℂ x).symm z))
          (Data.chart (Data.idx ((chartAt ℂ x).symm z)) ((chartAt ℂ x).symm z)) :=
  dite_eq_left hz

/-- **Master computation**: in the preferred chart at `x`, at a target point `z` whose base point
lies in the `i`-th data chart, the raw coefficient is the `i`-th coefficient transported by the
conjugated transition derivative — independent of the internally chosen index. -/
theorem rawCoeffAt_eq {x : X} (i : ι) {z : ℂ} (hz : z ∈ (chartAt ℂ x).target)
    (hp : (chartAt ℂ x).symm z ∈ (Data.chart i).source) :
    Data.rawCoeffAt x z =
      (starRingEnd ℂ) (deriv (⇑(Data.chart i) ∘ ⇑(chartAt ℂ x).symm) z) *
        Data.coeff i (Data.chart i ((chartAt ℂ x).symm z)) := by
  have hpj : (chartAt ℂ x).symm z ∈ (Data.chart (Data.idx ((chartAt ℂ x).symm z))).source :=
    Data.mem_source_idx _
  have hcompat := Data.compat i (Data.idx ((chartAt ℂ x).symm z)) ((chartAt ℂ x).symm z) ⟨hp, hpj⟩
  have hchain := deriv_trans_comp (Data.mem_maximalAtlas i)
    (Data.mem_maximalAtlas (Data.idx ((chartAt ℂ x).symm z)))
    (IsManifold.chart_mem_maximalAtlas x) hz hp hpj
  rw [Data.rawCoeffAt_of_mem hz, hcompat, hchain, map_mul]
  ring

/-- The preferred-chart coefficient functions of `Data.rawCoeffAt` are real-smooth on chart
targets. -/
theorem contDiffOn_rawCoeffAt (x : X) :
    ContDiffOn ℝ ∞ (Data.rawCoeffAt x) (chartAt ℂ x).target := by
  intro z₀ hz₀
  set p₀ := (chartAt ℂ x).symm z₀ with hp₀_def
  set i₀ := Data.idx p₀ with hi₀_def
  have hp₀ : p₀ ∈ (Data.chart i₀).source := Data.mem_source_idx p₀
  have hWopen : IsOpen (⇑(chartAt ℂ x) '' ((Data.chart i₀).source ∩ (chartAt ℂ x).source)) :=
    (chartAt ℂ x).isOpen_image_of_subset_source
      ((Data.chart i₀).open_source.inter (chartAt ℂ x).open_source) inter_subset_right
  have hz₀W : z₀ ∈ ⇑(chartAt ℂ x) '' ((Data.chart i₀).source ∩ (chartAt ℂ x).source) :=
    ⟨p₀, ⟨hp₀, (chartAt ℂ x).map_target hz₀⟩, (chartAt ℂ x).right_inv hz₀⟩
  have heq : Data.rawCoeffAt x =ᶠ[nhds z₀]
      fun w => (starRingEnd ℂ) (deriv (⇑(Data.chart i₀) ∘ ⇑(chartAt ℂ x).symm) w) *
        Data.coeff i₀ ((⇑(Data.chart i₀) ∘ ⇑(chartAt ℂ x).symm) w) := by
    filter_upwards [hWopen.mem_nhds hz₀W, (chartAt ℂ x).open_target.mem_nhds hz₀] with w hw hwt
    obtain ⟨q, hq, rfl⟩ := hw
    have hwp : (chartAt ℂ x).symm (chartAt ℂ x q) ∈ (Data.chart i₀).source := by
      rw [(chartAt ℂ x).left_inv hq.2]; exact hq.1
    exact Data.rawCoeffAt_eq i₀ hwt hwp
  have hτ : AnalyticAt ℂ (⇑(Data.chart i₀) ∘ ⇑(chartAt ℂ x).symm) z₀ :=
    analyticAt_trans (Data.mem_maximalAtlas i₀) (IsManifold.chart_mem_maximalAtlas x) hz₀ hp₀
  have hτReal : ContDiffAt ℝ ∞ (⇑(Data.chart i₀) ∘ ⇑(chartAt ℂ x).symm) z₀ :=
    (hτ.restrictScalars (𝕜 := ℝ)).contDiffAt
  have hτDerivReal : ContDiffAt ℝ ∞ (deriv (⇑(Data.chart i₀) ∘ ⇑(chartAt ℂ x).symm)) z₀ :=
    (hτ.deriv.restrictScalars (𝕜 := ℝ)).contDiffAt
  have hconjReal : ContDiffAt ℝ ∞ (starRingEnd ℂ)
      (deriv (⇑(Data.chart i₀) ∘ ⇑(chartAt ℂ x).symm) z₀) := by
    have hconjEq : (starRingEnd ℂ) = ⇑Complex.conjCLE := rfl
    rw [hconjEq]
    exact Complex.conjCLE.contDiff.contDiffAt
  have hzt₀ : (⇑(Data.chart i₀) ∘ ⇑(chartAt ℂ x).symm) z₀ ∈ (Data.chart i₀).target :=
    (Data.chart i₀).map_source hp₀
  have hcoeffReal : ContDiffAt ℝ ∞
      (fun w => Data.coeff i₀ ((⇑(Data.chart i₀) ∘ ⇑(chartAt ℂ x).symm) w)) z₀ := by
    have hcd : ContDiffAt ℝ ∞ (Data.coeff i₀) ((⇑(Data.chart i₀) ∘ ⇑(chartAt ℂ x).symm) z₀) :=
      (Data.contDiffOn i₀).contDiffAt ((Data.chart i₀).open_target.mem_nhds hzt₀)
    exact hcd.comp z₀ hτReal
  have hprodReal : ContDiffAt ℝ ∞
      (fun w => (starRingEnd ℂ) (deriv (⇑(Data.chart i₀) ∘ ⇑(chartAt ℂ x).symm) w) *
        Data.coeff i₀ ((⇑(Data.chart i₀) ∘ ⇑(chartAt ℂ x).symm) w)) z₀ :=
    (hconjReal.comp z₀ hτDerivReal).mul hcoeffReal
  exact (hprodReal.congr_of_eventuallyEq heq).contDiffWithinAt

/-- The `conj`-transition rule for `Data.rawCoeffAt` between any two PREFERRED charts (not just
data charts): the `compat` field of the assembled `Form01`. -/
theorem rawCoeffAt_trans (x y : X) {z : ℂ}
    (hz : z ∈ ⇑(chartAt ℂ y) '' ((chartAt ℂ x).source ∩ (chartAt ℂ y).source)) :
    Data.rawCoeffAt y z =
      (starRingEnd ℂ) (deriv (⇑(chartAt ℂ x) ∘ ⇑(chartAt ℂ y).symm) z) *
        Data.rawCoeffAt x (chartAt ℂ x ((chartAt ℂ y).symm z)) := by
  obtain ⟨p, ⟨hpx, hpy⟩, rfl⟩ := hz
  set i := Data.idx p with hi_def
  have hpi : p ∈ (Data.chart i).source := Data.mem_source_idx p
  have hzt : chartAt ℂ y p ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source hpy
  have hxt : chartAt ℂ x p ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source hpx
  have hpsymm_y : (chartAt ℂ y).symm (chartAt ℂ y p) = p := (chartAt ℂ y).left_inv hpy
  have hpsymm_x : (chartAt ℂ x).symm (chartAt ℂ x p) = p := (chartAt ℂ x).left_inv hpx
  have hLHS : Data.rawCoeffAt y (chartAt ℂ y p) =
      (starRingEnd ℂ) (deriv (⇑(Data.chart i) ∘ ⇑(chartAt ℂ y).symm) (chartAt ℂ y p)) *
        Data.coeff i (Data.chart i p) := by
    rw [Data.rawCoeffAt_eq i hzt (by rw [hpsymm_y]; exact hpi), hpsymm_y]
  have hRHS : Data.rawCoeffAt x (chartAt ℂ x p) =
      (starRingEnd ℂ) (deriv (⇑(Data.chart i) ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x p)) *
        Data.coeff i (Data.chart i p) := by
    rw [Data.rawCoeffAt_eq i hxt (by rw [hpsymm_x]; exact hpi), hpsymm_x]
  have hchain := deriv_trans_comp (Data.mem_maximalAtlas i) (IsManifold.chart_mem_maximalAtlas x)
    (IsManifold.chart_mem_maximalAtlas y) hzt (by rw [hpsymm_y]; exact hpi)
    (by rw [hpsymm_y]; exact hpx)
  rw [hpsymm_y] at hchain
  rw [hpsymm_y, hLHS, hRHS, hchain, map_mul]
  ring

end Form01CoeffData

/-- A `(0,1)`-form assembled from compatible chart-coefficient data (transcription of the CC1
`Form1.ofCoeffs` constructor for the `Form01` structure). -/
noncomputable def Form01.ofCoeffs {ι : Type*} (Data : Form01CoeffData X ι) : Form01 X where
  coeffAt := Data.rawCoeffAt
  coeffAt_zero_off _ _ hz := Data.rawCoeffAt_of_not_mem hz
  contDiffOn_coeffAt := Data.contDiffOn_rawCoeffAt
  compat _ _ _ hz := Data.rawCoeffAt_trans _ _ hz

@[simp] theorem Form01.coeffAt_ofCoeffs_apply {ι : Type*} (Data : Form01CoeffData X ι) (x : X)
    (z : ℂ) : (Form01.ofCoeffs Data).coeffAt x z = Data.rawCoeffAt x z := rfl

/-- The preferred-chart coefficient of `Form01.ofCoeffs Data` at the chart center of a point of
the `i`-th data chart's source, via the conjugated transition derivative — the shape
`GlueForm01.lean` consumes. -/
theorem Form01.coeffAt_ofCoeffs {ι : Type*} (Data : Form01CoeffData X ι) {x : X} {i : ι}
    (hx : x ∈ (Data.chart i).source) :
    (Form01.ofCoeffs Data).coeffAt x (chartAt ℂ x x) =
      (starRingEnd ℂ) (deriv (⇑(Data.chart i) ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x)) *
        Data.coeff i (Data.chart i x) := by
  have hz : chartAt ℂ x x ∈ (chartAt ℂ x).target := mem_chart_target ℂ x
  have hp : (chartAt ℂ x).symm (chartAt ℂ x x) ∈ (Data.chart i).source := by
    rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]; exact hx
  have h := Data.rawCoeffAt_eq i hz hp
  rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)] at h
  exact h

end RS
