/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Forms
import LeanPool.JacobianDiffgeo.Meromorphic

/-!
# `MFormData X`: raw chart-coefficient families for meromorphic 1-forms (D1–D3, data layer)

Unit: canonical-forms (`docs/design/canonical-forms.md` §2 D1–D3, §4.1). Blueprint: "Meromorphic
1-form systems and the canonical divisor `K`."

`MFormData X` is the RAW DATA CARRIER for meromorphic 1-forms: the meromorphic analogue of
`Form1`'s chart-coefficient API (`Jacobian/Forms/Coeffs.lean`) and of dbar's `Form01`
(`Jacobian/Dbar/Form01.lean`) — a `chartAt`-indexed family of coefficient functions, junk-zero off
the chart target, `MeromorphicOn` the target (mathlib's *unconditional* generalization of
`Form01`'s `ContDiffOn`/`Form1`'s `AnalyticOnNhd`, allowing poles), related on chart overlaps by
the CC1-style transition rule `coeffAt y z = deriv (chartAt x ∘ (chartAt y).symm) z *
coeffAt x (...)` — **no conjugate** (a meromorphic 1-form is still type `(1,0)`, unlike `Form01`'s
`(0,1)`-conjugate rule).

**Raw equality on `MFormData` is too fine** (meromorphic coefficient functions carry junk values
at poles, so "`ord = ⊤` everywhere" does not pin the raw values): the ACTUAL meromorphic-1-form
type is the quotient `RS.MForm X` by codiscrete/germ agreement (`Quotient.lean`, the same CC3
pattern as `ℳ X := MeroGermOn X univ`). Everything in this file is the foundation the quotient
descends from.

Main declarations:
* `RS.MFormData X` — the structure (D1); `RS.MFormData.ext`, `Zero`/`Add`/`Neg`/`Sub`/`SMul ℂ`/
  `AddCommGroup`/`Module ℂ` instances (D2), pointwise on `coeffAt`.
* `RS.MFormCoeffData X ι` / `RS.MFormData.ofCoeffs` (D3) — the arbitrary-chart-family constructor,
  mirroring `Form1CoeffData`/`Form1.ofCoeffs` (`Jacobian/Forms/OfCoeffs.lean`) with
  `AnalyticOnNhd ↦ MeromorphicOn`; not used by `MFormData.d`/`dlog` (built directly against
  `chartAt`
  in `Differential.lean`), offered for future covering-family constructions (e.g. laurent-tails).
-/

open scoped ContDiff Manifold
open Set IsManifold

noncomputable section

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- A meromorphic 1-form on `X`: the meromorphic analogue of `Form1`'s `coeffIn` API and
`Form01`'s chart-family structure, generalized to allow poles (D1). -/
structure MFormData (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] where
  /-- The coefficient function in the preferred chart at each point. -/
  coeffAt : X → ℂ → ℂ
  coeffAt_zero_off : ∀ x, ∀ z ∉ (chartAt ℂ x).target, coeffAt x z = 0
  meromorphicOn_coeffAt : ∀ x, MeromorphicOn (coeffAt x) (chartAt ℂ x).target
  compat : ∀ x y : X, ∀ z ∈ ⇑(chartAt ℂ y) '' ((chartAt ℂ x).source ∩ (chartAt ℂ y).source),
    coeffAt y z = deriv (⇑(chartAt ℂ x) ∘ ⇑(chartAt ℂ y).symm) z *
      coeffAt x (chartAt ℂ x ((chartAt ℂ y).symm z))

namespace MFormData

/-- A meromorphic 1-form is determined by its preferred-chart coefficients on chart targets. -/
@[ext]
theorem ext {θ η : MFormData X}
    (h : ∀ x, ∀ z ∈ (chartAt ℂ x).target, θ.coeffAt x z = η.coeffAt x z) : θ = η := by
  have hcoeff : θ.coeffAt = η.coeffAt := by
    funext x z
    by_cases hz : z ∈ (chartAt ℂ x).target
    · exact h x z hz
    · rw [θ.coeffAt_zero_off x z hz, η.coeffAt_zero_off x z hz]
  obtain ⟨c1, _, _, _⟩ := θ
  obtain ⟨c2, _, _, _⟩ := η
  simp only at hcoeff
  subst hcoeff
  rfl

instance : Zero (MFormData X) where
  zero := ⟨fun _ _ => 0, fun _ _ _ => rfl,
    fun x => (MeromorphicOn.const (U := (chartAt ℂ x).target) (0 : ℂ) : MeromorphicOn _ _),
    fun _ _ _ _ => by simp⟩

instance : Add (MFormData X) where
  add θ η := ⟨fun x z => θ.coeffAt x z + η.coeffAt x z,
    fun x z hz => by
      rw [θ.coeffAt_zero_off x z hz, η.coeffAt_zero_off x z hz, add_zero],
    fun x => (θ.meromorphicOn_coeffAt x).add (η.meromorphicOn_coeffAt x),
    fun x y z hz => by rw [θ.compat x y z hz, η.compat x y z hz]; ring⟩

instance : Neg (MFormData X) where
  neg θ := ⟨fun x z => -θ.coeffAt x z,
    fun x z hz => by rw [θ.coeffAt_zero_off x z hz, neg_zero],
    fun x => (θ.meromorphicOn_coeffAt x).neg,
    fun x y z hz => by rw [θ.compat x y z hz]; ring⟩

instance : Sub (MFormData X) where
  sub θ η := ⟨fun x z => θ.coeffAt x z - η.coeffAt x z,
    fun x z hz => by
      rw [θ.coeffAt_zero_off x z hz, η.coeffAt_zero_off x z hz, sub_zero],
    fun x => (θ.meromorphicOn_coeffAt x).sub (η.meromorphicOn_coeffAt x),
    fun x y z hz => by rw [θ.compat x y z hz, η.compat x y z hz]; ring⟩

instance : SMul ℂ (MFormData X) where
  smul c θ := ⟨fun x z => c * θ.coeffAt x z,
    fun x z hz => by rw [θ.coeffAt_zero_off x z hz, mul_zero],
    fun x => by
      have hc : MeromorphicOn (fun _ : ℂ => c) (chartAt ℂ x).target :=
        MeromorphicOn.const (U := (chartAt ℂ x).target) c
      exact hc.mul (θ.meromorphicOn_coeffAt x),
    fun x y z hz => by rw [θ.compat x y z hz]; ring⟩

@[simp] theorem coeffAt_zero (x : X) (z : ℂ) : (0 : MFormData X).coeffAt x z = 0 := rfl

@[simp] theorem coeffAt_add (θ η : MFormData X) (x : X) (z : ℂ) :
    (θ + η).coeffAt x z = θ.coeffAt x z + η.coeffAt x z := rfl

@[simp] theorem coeffAt_neg (θ : MFormData X) (x : X) (z : ℂ) :
    (-θ).coeffAt x z = -θ.coeffAt x z := rfl

@[simp] theorem coeffAt_sub (θ η : MFormData X) (x : X) (z : ℂ) :
    (θ - η).coeffAt x z = θ.coeffAt x z - η.coeffAt x z := rfl

@[simp] theorem coeffAt_smul (c : ℂ) (θ : MFormData X) (x : X) (z : ℂ) :
    (c • θ).coeffAt x z = c * θ.coeffAt x z := rfl

instance : AddCommGroup (MFormData X) where
  add_assoc a b c := by ext x z _; simp; ring
  zero_add a := by ext x z _; simp
  add_zero a := by ext x z _; simp
  add_comm a b := by ext x z _; simp; ring
  neg_add_cancel a := by ext x z _; simp
  sub_eq_add_neg a b := by ext x z _; simp; ring
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Module ℂ (MFormData X) where
  smul_zero a := by ext x z _; simp
  smul_add a b c := by ext x z _; simp; ring
  add_smul a b c := by ext x z _; simp; ring
  zero_smul a := by ext x z _; simp
  one_smul a := by ext x z _; simp
  mul_smul a b c := by ext x z _; simp; ring

end MFormData

/-! ### D3: constructing `MFormData` from arbitrary compatible chart data -/

/-- Compatible meromorphic coefficient data for a meromorphic 1-form, over a covering family of
`ω`-maximal-atlas charts (mirrors `Form1CoeffData`, `MeromorphicOn` in place of `AnalyticOnNhd`). -/
structure MFormCoeffData (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (ι : Type*) where
  /-- The covering chart family. -/
  chart : ι → OpenPartialHomeomorph X ℂ
  mem_maximalAtlas : ∀ i, chart i ∈ maximalAtlas 𝓘(ℂ) ω X
  exists_mem : ∀ x : X, ∃ i, x ∈ (chart i).source
  /-- The coefficient functions, one per chart. -/
  coeff : ι → ℂ → ℂ
  meromorphicOn : ∀ i, MeromorphicOn (coeff i) (chart i).target
  compat : ∀ i j, ∀ x ∈ (chart i).source ∩ (chart j).source,
    coeff j (chart j x) = deriv (⇑(chart i) ∘ ⇑(chart j).symm) (chart j x) * coeff i (chart i x)

namespace MFormCoeffData

variable {ι : Type*} (D : MFormCoeffData X ι)

/-- A chosen chart index for each point. -/
def idx (x : X) : ι := (D.exists_mem x).choose

theorem mem_source_idx (x : X) : x ∈ (D.chart (D.idx x)).source := (D.exists_mem x).choose_spec

/-- The coefficient of the assembled family, read through an arbitrary maximal-atlas chart `e'`,
using the per-point chosen index (mirrors `Form1CoeffData.toSection`, without the bundle layer:
`MFormData` has no covector-bundle backing, so this formula IS the assembled coefficient
    directly). -/
noncomputable def rawCoeffAt (e' : OpenPartialHomeomorph X ℂ) (z : ℂ) : ℂ :=
  deriv (⇑(D.chart (D.idx (e'.symm z))) ∘ ⇑e'.symm) z *
    D.coeff (D.idx (e'.symm z)) (D.chart (D.idx (e'.symm z)) (e'.symm z))

/-- **Master computation**: `rawCoeffAt` read through any maximal-atlas chart `e'`, at a point
whose base point lies in the `i`-th chart, equals the `i`-th coefficient transported by the
transition derivative — independent of the internal `idx` choice, by `compat`. -/
theorem rawCoeffAt_eq {e' : OpenPartialHomeomorph X ℂ}
    (he' : e' ∈ maximalAtlas 𝓘(ℂ) ω X) (i : ι) {z : ℂ} (hz : z ∈ e'.target)
    (hp : e'.symm z ∈ (D.chart i).source) :
    D.rawCoeffAt e' z = deriv (⇑(D.chart i) ∘ ⇑e'.symm) z * D.coeff i (D.chart i (e'.symm z)) := by
  set j := D.idx (e'.symm z) with hjdef
  have hpj : e'.symm z ∈ (D.chart j).source := D.mem_source_idx _
  have hcompat := D.compat i j (e'.symm z) ⟨hp, hpj⟩
  have hdt := deriv_trans_comp (D.mem_maximalAtlas i) (D.mem_maximalAtlas j) he' hz hp hpj
  change deriv (⇑(D.chart j) ∘ ⇑e'.symm) z * D.coeff j (D.chart j (e'.symm z)) = _
  rw [hcompat, hdt]
  ring

theorem meromorphicAt_rawCoeffAt (e' : OpenPartialHomeomorph X ℂ)
    (he' : e' ∈ maximalAtlas 𝓘(ℂ) ω X) {z₀ : ℂ} (hz₀ : z₀ ∈ e'.target) :
    MeromorphicAt (D.rawCoeffAt e') z₀ := by
  obtain ⟨i, hi⟩ := D.exists_mem (e'.symm z₀)
  have hWopen : IsOpen (⇑e' '' ((D.chart i).source ∩ e'.source)) :=
    e'.isOpen_image_of_subset_source ((D.chart i).open_source.inter e'.open_source)
      inter_subset_right
  have hzW : z₀ ∈ ⇑e' '' ((D.chart i).source ∩ e'.source) :=
    ⟨e'.symm z₀, ⟨hi, e'.map_target hz₀⟩, e'.right_inv hz₀⟩
  have heq : D.rawCoeffAt e' =ᶠ[nhds z₀]
      fun w => deriv (⇑(D.chart i) ∘ ⇑e'.symm) w * D.coeff i (D.chart i (e'.symm w)) := by
    filter_upwards [hWopen.mem_nhds hzW] with w hw
    obtain ⟨q, hq, rfl⟩ := hw
    have hwt : e' q ∈ e'.target := e'.map_source hq.2
    have hwp : e'.symm (e' q) ∈ (D.chart i).source := by rw [e'.left_inv hq.2]; exact hq.1
    exact D.rawCoeffAt_eq he' i hwt hwp
  have hpt : e' (e'.symm z₀) = z₀ := e'.right_inv hz₀
  obtain ⟨hτ, hτ'⟩ := analyticAt_transition he' (D.mem_maximalAtlas i) (e'.map_target hz₀) hi
  rw [hpt] at hτ hτ'
  have hcoeff : MeromorphicAt (fun w => D.coeff i ((⇑(D.chart i) ∘ ⇑e'.symm) w)) z₀ :=
    (meromorphicAt_comp_iff_of_deriv_ne_zero hτ hτ').2
      (D.meromorphicOn i _ ((D.chart i).map_source hi))
  exact MeromorphicAt.congr (hτ.deriv.meromorphicAt.mul hcoeff)
    (heq.symm.filter_mono nhdsWithin_le_nhds)

end MFormCoeffData

namespace MFormData

open scoped Classical in
/-- Assemble an `MFormData` from compatible chart-coefficient data (D3, mirrors
`Form1.ofCoeffs`). -/
noncomputable def ofCoeffs {ι : Type*} (D : MFormCoeffData X ι) : MFormData X where
  coeffAt x z := if z ∈ (chartAt ℂ x).target then D.rawCoeffAt (chartAt ℂ x) z else 0
  coeffAt_zero_off x z hz := ite_eq_right hz
  meromorphicOn_coeffAt x := by
    have hf : MeromorphicOn (D.rawCoeffAt (chartAt ℂ x)) (chartAt ℂ x).target :=
      fun z hz => D.meromorphicAt_rawCoeffAt (chartAt ℂ x) (chart_mem_maximalAtlas x) hz
    exact hf.congr (fun z hz => (ite_eq_left hz).symm) (chartAt ℂ x).open_target
  compat x y z hz := by
    obtain ⟨p, hp, rfl⟩ := hz
    have hyt : chartAt ℂ y p ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source hp.2
    have hxt : chartAt ℂ x p ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source hp.1
    have hsy : (chartAt ℂ y).symm (chartAt ℂ y p) = p := (chartAt ℂ y).left_inv hp.2
    have hsx : (chartAt ℂ x).symm (chartAt ℂ x p) = p := (chartAt ℂ x).left_inv hp.1
    change
      (if chartAt ℂ y p ∈ (chartAt ℂ y).target then D.rawCoeffAt (chartAt ℂ y) (chartAt ℂ y p)
        else 0) =
      deriv (⇑(chartAt ℂ x) ∘ ⇑(chartAt ℂ y).symm) (chartAt ℂ y p) *
        (if chartAt ℂ x ((chartAt ℂ y).symm (chartAt ℂ y p)) ∈ (chartAt ℂ x).target then
          D.rawCoeffAt (chartAt ℂ x) (chartAt ℂ x ((chartAt ℂ y).symm (chartAt ℂ y p))) else 0)
    rw [ite_eq_left hyt, hsy, ite_eq_left hxt]
    obtain ⟨i, hi⟩ := D.exists_mem p
    have hpi : (chartAt ℂ y).symm (chartAt ℂ y p) ∈ (D.chart i).source := by
      rw [hsy]; exact hi
    have hpx : (chartAt ℂ y).symm (chartAt ℂ y p) ∈ (chartAt ℂ x).source := by
      rw [hsy]; exact hp.1
    have hpi' : (chartAt ℂ x).symm (chartAt ℂ x p) ∈ (D.chart i).source := by
      rw [hsx]; exact hi
    have h1 := D.rawCoeffAt_eq (chart_mem_maximalAtlas y) i hyt hpi
    have h2 := D.rawCoeffAt_eq (chart_mem_maximalAtlas x) i hxt hpi'
    have h3 := deriv_trans_comp (D.mem_maximalAtlas i) (chart_mem_maximalAtlas x)
      (chart_mem_maximalAtlas y) hyt hpi hpx
    rw [hsy] at h1 h3
    rw [hsx] at h2
    rw [h1, h3, h2]
    ring

open scoped Classical in
/-- The coefficient of `MFormData.ofCoeffs D` in the `i`-th chart of the data, read at a point of
    the
preferred chart at `x`, is the given coefficient transported by the transition derivative
(mirrors `Form1.coeffAt_ofCoeffs`). -/
theorem coeffAt_ofCoeffs {ι : Type*} (D : MFormCoeffData X ι) {x : X} {i : ι}
    (_hx : x ∈ (D.chart i).source) {z : ℂ}
    (hz : z ∈ ⇑(chartAt ℂ x) '' ((D.chart i).source ∩ (chartAt ℂ x).source)) :
    (MFormData.ofCoeffs D).coeffAt x z =
      deriv (⇑(D.chart i) ∘ ⇑(chartAt ℂ x).symm) z *
        D.coeff i (D.chart i ((chartAt ℂ x).symm z)) := by
  obtain ⟨p, hp, rfl⟩ := hz
  have hxt : chartAt ℂ x p ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source hp.2
  have hp' : (chartAt ℂ x).symm (chartAt ℂ x p) ∈ (D.chart i).source := by
    rw [(chartAt ℂ x).left_inv hp.2]; exact hp.1
  change (if chartAt ℂ x p ∈ (chartAt ℂ x).target then D.rawCoeffAt (chartAt ℂ x) (chartAt ℂ x p)
    else 0) = _
  rw [ite_eq_left hxt]
  exact D.rawCoeffAt_eq (chart_mem_maximalAtlas x) i hxt hp'

end MFormData

end RS
