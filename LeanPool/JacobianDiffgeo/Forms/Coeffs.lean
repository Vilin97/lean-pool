/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Forms.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# The chart-coefficient API for holomorphic 1-forms (CC1)

For a chart `e` and a 1-form `η`, `RS.coeffIn e η : ℂ → ℂ` is the coefficient function
"`η = (coeffIn e η) dz`" in the chart: `coeffIn e η z = η (e.symm z) (d(e.symm)_z 1)`, junk off
`e.target`. `RS.coeffAt x η` is the coefficient in the preferred chart at the image of `x`.

Main results:
* `RS.coeffAt_eq_apply_one`, `RS.Form1.apply_eq_smul_coeffAt` — the canonical identification of
  the tangent fiber with `ℂ` in the preferred chart (all `TangentSpace ≡ ℂ ≡ Bundle.Trivial`
  defeq-crossings of this unit are concentrated here and in `evalC`).
* `RS.Form1.ext_coeffAt` — a form is determined by its preferred-chart coefficients.
* ℂ-linearity of `coeffIn`/`coeffAt` in the form (simp lemmas).
* `RS.coeffIn_trans` — the transition rule
  `coeffIn e' η z = deriv (e ∘ e.symm') z * coeffIn e η (e (e'.symm z))` on chart overlaps,
  for charts in the `ω`-maximal atlas (CC1 orientation).
* `RS.coeffIn_restr` — restricting the chart does not change the coefficient (`rfl`).

All downstream units interact with 1-forms exclusively through this API.
-/

open scoped ContDiff Manifold Bundle
open Set

noncomputable section

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- The coefficient function of a raw covector section in the chart `e`: for `z ∈ e.target`,
`coeffInFun e σ z = σ (e.symm z) (d(e.symm)_z 1)`. Junk (unspecified) off `e.target`. -/
def coeffInFun (e : OpenPartialHomeomorph X ℂ)
    (σ : ∀ x : X, TangentSpace 𝓘(ℂ) x →L[ℂ] Bundle.Trivial X ℂ x) (z : ℂ) : ℂ :=
  σ (e.symm z) (mfderiv 𝓘(ℂ) 𝓘(ℂ) e.symm z (1 : ℂ))

/-- The coefficient function of a 1-form in the chart `e`: for `z ∈ e.target`,
`coeffIn e η z = η (e.symm z) (d(e.symm)_z 1)`, i.e. "`η = (coeffIn e η) dz`" in the chart.
Junk (unspecified) off `e.target`. -/
def coeffIn (e : OpenPartialHomeomorph X ℂ) (η : Form1 X) (z : ℂ) : ℂ :=
  coeffInFun e (⇑η) z

theorem coeffIn_def (e : OpenPartialHomeomorph X ℂ) (η : Form1 X) :
    coeffIn e η = coeffInFun e ⇑η := rfl

/-- Coefficient in the preferred chart, at the image of the base point. -/
def coeffAt (x : X) (η : Form1 X) : ℂ := coeffIn (chartAt ℂ x) η (chartAt ℂ x x)

/-- Restricting a chart does not change the coefficient function (the underlying chart maps are
unchanged by `restr`). -/
@[simp]
theorem coeffIn_restr (e : OpenPartialHomeomorph X ℂ) (V : Set X) (η : Form1 X) :
    coeffIn (e.restr V) η = coeffIn e η := rfl

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
@[simp]
theorem coeffInFun_restr (e : OpenPartialHomeomorph X ℂ) (V : Set X)
    (σ : ∀ x : X, TangentSpace 𝓘(ℂ) x →L[ℂ] Bundle.Trivial X ℂ x) :
    coeffInFun (e.restr V) σ = coeffInFun e σ := rfl

/-! ### Linearity in the form -/

@[simp]
theorem coeffIn_add (e : OpenPartialHomeomorph X ℂ) (η η' : Form1 X) (z : ℂ) :
    coeffIn e (η + η') z = coeffIn e η z + coeffIn e η' z := by
  simp [coeffIn, coeffInFun]

@[simp]
theorem coeffIn_smul (e : OpenPartialHomeomorph X ℂ) (c : ℂ) (η : Form1 X) (z : ℂ) :
    coeffIn e (c • η) z = c * coeffIn e η z := by
  simp [coeffIn, coeffInFun]

@[simp]
theorem coeffIn_zero (e : OpenPartialHomeomorph X ℂ) (z : ℂ) :
    coeffIn e (0 : Form1 X) z = 0 := by
  simp [coeffIn, coeffInFun]

@[simp]
theorem coeffIn_neg (e : OpenPartialHomeomorph X ℂ) (η : Form1 X) (z : ℂ) :
    coeffIn e (-η) z = -coeffIn e η z := by
  simp [coeffIn, coeffInFun]

@[simp]
theorem coeffIn_sub (e : OpenPartialHomeomorph X ℂ) (η η' : Form1 X) (z : ℂ) :
    coeffIn e (η - η') z = coeffIn e η z - coeffIn e η' z := by
  simp [coeffIn, coeffInFun]

@[simp]
theorem coeffAt_add (x : X) (η η' : Form1 X) :
    coeffAt x (η + η') = coeffAt x η + coeffAt x η' := coeffIn_add ..

@[simp]
theorem coeffAt_smul (x : X) (c : ℂ) (η : Form1 X) :
    coeffAt x (c • η) = c * coeffAt x η := coeffIn_smul ..

@[simp]
theorem coeffAt_zero (x : X) : coeffAt x (0 : Form1 X) = 0 := coeffIn_zero ..

@[simp]
theorem coeffAt_neg (x : X) (η : Form1 X) : coeffAt x (-η) = -coeffAt x η := coeffIn_neg ..

@[simp]
theorem coeffAt_sub (x : X) (η η' : Form1 X) :
    coeffAt x (η - η') = coeffAt x η - coeffAt x η' := coeffIn_sub ..

/-! ### The concentrated defeq layer

Every `TangentSpace 𝓘(ℂ) q ≡ ℂ ≡ Bundle.Trivial X ℂ q` crossing of this unit happens in the
next few declarations, and nowhere else. -/

/-- The canonical (definitional) identification of a tangent fiber of a `ℂ`-charted space with
`ℂ`. `TangentSpace` is not reducible, so instance search does not see through it; this reducible
wrapper lets scalar formulas (`HMul` etc.) elaborate. -/
abbrev tangentCoord {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] {y : Y}
    (v : TangentSpace 𝓘(ℂ) y) : ℂ := v

/-- Non-dependent evaluation of a raw covector section, through the definitional equality
`TangentSpace 𝓘(ℂ) q ≡ ℂ ≡ Bundle.Trivial X ℂ q`. Point-congruences for the dependent
evaluation are done through this function. -/
def evalC (σ : ∀ x : X, TangentSpace 𝓘(ℂ) x →L[ℂ] Bundle.Trivial X ℂ x) (q : X) (w : ℂ) : ℂ :=
  σ q w

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem coeffInFun_eq_evalC (e : OpenPartialHomeomorph X ℂ)
    (σ : ∀ x : X, TangentSpace 𝓘(ℂ) x →L[ℂ] Bundle.Trivial X ℂ x) (z : ℂ) :
    coeffInFun e σ z = evalC σ (e.symm z) (mfderiv 𝓘(ℂ) 𝓘(ℂ) e.symm z (1 : ℂ)) := rfl

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Scalars pull out of the non-dependent evaluation (the fiberwise CLM is `ℂ`-linear). -/
theorem evalC_mul (σ : ∀ x : X, TangentSpace 𝓘(ℂ) x →L[ℂ] Bundle.Trivial X ℂ x)
    (q : X) (c w : ℂ) : evalC σ q (c * w) = c * evalC σ q w :=
  (σ q).map_smul c w

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- A continuous linear map between a tangent fiber of the model `ℂ` and a tangent fiber of `X`
(both definitionally `ℂ`) is multiplication by its value at `1`. -/
theorem tangentCLM_apply_eq_mul {w : ℂ} {q : X}
    (T : TangentSpace 𝓘(ℂ) w →L[ℂ] TangentSpace 𝓘(ℂ) q) (c : ℂ) :
    tangentCoord (T c) = c * tangentCoord (T (1 : ℂ)) := by
  have h : (c : TangentSpace 𝓘(ℂ) w) = c • ((1 : ℂ) : TangentSpace 𝓘(ℂ) w) := by
    change c = c * (1 : ℂ)
    rw [mul_one]
  -- `T.map_smul` is stated with `T`'s own module instances; naming the instance here (rather
  -- than letting `rw` unify through `TangentSpace`'s unfolding) keeps the rewrite syntactic.
  have hsmul : T (c • ((1 : ℂ) : TangentSpace 𝓘(ℂ) w)) =
      c • T ((1 : ℂ) : TangentSpace 𝓘(ℂ) w) :=
    T.map_smul c ((1 : ℂ) : TangentSpace 𝓘(ℂ) w)
  conv_lhs => rw [h, hsmul]
  rfl

/-- The `mfderiv` of the inverse of the preferred chart, at the image of the base point, is the
identity (canonical identification of the tangent fiber with `ℂ`). -/
theorem mfderiv_chartAt_symm_chartAt_self (x : X) :
    mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ x).symm (chartAt ℂ x x) = ContinuousLinearMap.id ℂ ℂ := by
  have h := mfderivWithin_range_extChartAt_symm (I := 𝓘(ℂ)) (x := x)
  simp only [extChartAt_coe_symm, extChartAt_coe, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.comp_id, Set.range_id,
    Function.comp_apply, id_eq, mfderivWithin_univ] at h
  exact h

/-- In the preferred chart, the coefficient at the base point is the evaluation at the canonical
tangent vector `1`. -/
theorem coeffAt_eq_apply_one (η : Form1 X) (x : X) : coeffAt x η = η x (1 : ℂ) := by
  have h0 : coeffAt x η =
      evalC (⇑η) ((chartAt ℂ x).symm (chartAt ℂ x x))
        (mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ x).symm (chartAt ℂ x x) (1 : ℂ)) := rfl
  have hpt : (chartAt ℂ x).symm (chartAt ℂ x x) = x :=
    (chartAt ℂ x).left_inv (mem_chart_source ℂ x)
  calc coeffAt x η
      = evalC (⇑η) ((chartAt ℂ x).symm (chartAt ℂ x x))
          (ContinuousLinearMap.id ℂ ℂ (1 : ℂ)) := by
        rw [h0, mfderiv_chartAt_symm_chartAt_self]; rfl
    _ = evalC (⇑η) x (ContinuousLinearMap.id ℂ ℂ (1 : ℂ)) := by rw [hpt]
    _ = η x (1 : ℂ) := by rw [ContinuousLinearMap.id_apply]; rfl

/-- Evaluation of a 1-form on a tangent vector, via the canonical identification: the fiber is
one-dimensional and `η x v = v * coeffAt x η`. -/
theorem Form1.apply_eq_smul_coeffAt (η : Form1 X) (x : X) (v : TangentSpace 𝓘(ℂ) x) :
    η x v = tangentCoord v * coeffAt x η := by
  rw [coeffAt_eq_apply_one]
  have h : (v : TangentSpace 𝓘(ℂ) x) = tangentCoord v • ((1 : ℂ) : TangentSpace 𝓘(ℂ) x) := by
    change v = tangentCoord v * (1 : ℂ)
    rw [mul_one]
  calc (η x) v = (η x) (tangentCoord v • ((1 : ℂ) : TangentSpace 𝓘(ℂ) x)) := by rw [← h]
    _ = tangentCoord v * η x (1 : ℂ) :=
        (η x).map_smul (tangentCoord v) ((1 : ℂ) : TangentSpace 𝓘(ℂ) x)

/-- The non-dependent-evaluation version of `Form1.apply_eq_smul_coeffAt`. -/
theorem evalC_eq_mul_coeffAt (η : Form1 X) (q : X) (w : ℂ) :
    evalC (⇑η) q w = w * coeffAt q η :=
  Form1.apply_eq_smul_coeffAt η q w

/-- A holomorphic 1-form is determined by its preferred-chart coefficients. -/
@[ext]
theorem Form1.ext_coeffAt {η η' : Form1 X} (h : ∀ x, coeffAt x η = coeffAt x η') : η = η' :=
  Form1.ext_apply fun x v => by
    rw [Form1.apply_eq_smul_coeffAt η, Form1.apply_eq_smul_coeffAt η', h]

/-! ### The transition rule -/

open IsManifold

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- The transition map between two charts, as read in the maximal atlas, is `C^ω` (hence
differentiable) at every point of the image of the overlap. -/
theorem differentiableAt_trans {e e' : OpenPartialHomeomorph X ℂ}
    (he : e ∈ maximalAtlas 𝓘(ℂ) ω X) (he' : e' ∈ maximalAtlas 𝓘(ℂ) ω X) {z : ℂ}
    (hzt : z ∈ e'.target) (hzs : e'.symm z ∈ e.source) :
    DifferentiableAt ℂ (⇑e ∘ ⇑e'.symm) z := by
  have hcompat := compatible_of_mem_maximalAtlas he' he
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at hcompat
  have h1 : ContDiffOn ℂ ω (⇑𝓘(ℂ) ∘ ⇑(e'.symm.trans e) ∘ ⇑𝓘(ℂ).symm)
      (⇑𝓘(ℂ).symm ⁻¹' (e'.symm.trans e).source ∩ Set.range ⇑𝓘(ℂ)) := hcompat.1
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_id,
    Function.id_comp, Set.preimage_id, Set.range_id, Set.inter_univ] at h1
  have hzsrc : z ∈ (e'.symm.trans e).source := by
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
    exact ⟨hzt, hzs⟩
  have hCD : ContDiffAt ℂ ω ⇑(e'.symm.trans e) z :=
    h1.contDiffAt ((e'.symm.trans e).open_source.mem_nhds hzsrc)
  have hD : DifferentiableAt ℂ ⇑(e'.symm.trans e) z := hCD.differentiableAt (by simp)
  have hcoe : ⇑(e'.symm.trans e) = ⇑e ∘ ⇑e'.symm := rfl
  rwa [hcoe] at hD

/-- **Transition rule** for chart coefficients (CC1 orientation): on the image of a chart
overlap, `coeffIn e' η z = deriv (e ∘ e'.symm) z * coeffIn e η (e (e'.symm z))`. -/
theorem coeffIn_trans {e e' : OpenPartialHomeomorph X ℂ}
    (he : e ∈ maximalAtlas 𝓘(ℂ) ω X) (he' : e' ∈ maximalAtlas 𝓘(ℂ) ω X)
    (η : Form1 X) {z : ℂ} (hz : z ∈ ⇑e' '' (e.source ∩ e'.source)) :
    coeffIn e' η z = deriv (⇑e ∘ ⇑e'.symm) z * coeffIn e η (e (e'.symm z)) := by
  -- basic membership facts
  have hzt : z ∈ e'.target := by
    obtain ⟨q, hq, rfl⟩ := hz
    exact e'.map_source hq.2
  have hps : e'.symm z ∈ e.source ∩ e'.source := by
    obtain ⟨q, hq, rfl⟩ := hz
    rwa [e'.left_inv hq.2]
  -- the overlap image is open
  have hWopen : IsOpen (⇑e' '' (e.source ∩ e'.source)) :=
    e'.isOpen_image_of_subset_source (e.open_source.inter e'.open_source) inter_subset_right
  -- near `z`, `e'.symm = e.symm ∘ (e ∘ e'.symm)`
  have heq : ⇑e'.symm =ᶠ[nhds z] (⇑e.symm ∘ (⇑e ∘ ⇑e'.symm)) := by
    filter_upwards [hWopen.mem_nhds hz] with w hw
    obtain ⟨q, hq, rfl⟩ := hw
    rw [Function.comp_apply, Function.comp_apply, e'.left_inv hq.2, e.left_inv hq.1]
  -- differentiability of the two factors
  have hτdiff : DifferentiableAt ℂ (⇑e ∘ ⇑e'.symm) z := differentiableAt_trans he he' hzt hps.1
  have hτm : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (⇑e ∘ ⇑e'.symm) z :=
    mdifferentiableAt_iff_differentiableAt.mpr hτdiff
  have hesymm : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (⇑e.symm) (e (e'.symm z)) := by
    have hmem : e (e'.symm z) ∈ e.target := e.map_source hps.1
    exact (contMDiffAt_symm_of_mem_maximalAtlas he hmem).mdifferentiableAt (by simp)
  -- chain rule (the point of the outer factor is stated in aligned form `e (e'.symm z)`)
  have hmf : mfderiv 𝓘(ℂ) 𝓘(ℂ) (⇑e'.symm) z =
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) (⇑e.symm) (e (e'.symm z))).comp
        (mfderiv 𝓘(ℂ) 𝓘(ℂ) (⇑e ∘ ⇑e'.symm) z) :=
    heq.mfderiv_eq.trans (mfderiv_comp z hesymm hτm)
  -- the model factor is the classical derivative
  have hτ1 : mfderiv 𝓘(ℂ) 𝓘(ℂ) (⇑e ∘ ⇑e'.symm) z (1 : ℂ) = deriv (⇑e ∘ ⇑e'.symm) z := by
    rw [mfderiv_eq_fderiv]
    rfl
  -- scalar form of the chain rule
  have hscal : tangentCoord (mfderiv 𝓘(ℂ) 𝓘(ℂ) (⇑e'.symm) z (1 : ℂ)) =
      deriv (⇑e ∘ ⇑e'.symm) z *
        tangentCoord (mfderiv 𝓘(ℂ) 𝓘(ℂ) (⇑e.symm) (e (e'.symm z)) (1 : ℂ)) := by
    have h1 : tangentCoord ((mfderiv 𝓘(ℂ) 𝓘(ℂ) (⇑e'.symm) z) (1 : ℂ)) =
        tangentCoord ((mfderiv 𝓘(ℂ) 𝓘(ℂ) (⇑e.symm) (e (e'.symm z)))
          ((mfderiv 𝓘(ℂ) 𝓘(ℂ) (⇑e ∘ ⇑e'.symm) z) (1 : ℂ))) := by
      rw [hmf]; rfl
    rw [h1, hτ1]
    exact tangentCLM_apply_eq_mul _ _
  -- both coefficients against the common `coeffAt (e'.symm z) η`
  have hcoeff : coeffAt (e.symm (e (e'.symm z))) η = coeffAt (e'.symm z) η := by
    rw [e.left_inv hps.1]
  have hL : coeffIn e' η z =
      tangentCoord (mfderiv 𝓘(ℂ) 𝓘(ℂ) (⇑e'.symm) z (1 : ℂ)) * coeffAt (e'.symm z) η :=
    evalC_eq_mul_coeffAt η (e'.symm z) (mfderiv 𝓘(ℂ) 𝓘(ℂ) (⇑e'.symm) z (1 : ℂ))
  have hR : coeffIn e η (e (e'.symm z)) =
      tangentCoord (mfderiv 𝓘(ℂ) 𝓘(ℂ) (⇑e.symm) (e (e'.symm z)) (1 : ℂ)) *
        coeffAt (e'.symm z) η := by
    have h := evalC_eq_mul_coeffAt η (e.symm (e (e'.symm z)))
        (mfderiv 𝓘(ℂ) 𝓘(ℂ) (⇑e.symm) (e (e'.symm z)) (1 : ℂ))
    rw [hcoeff] at h
    exact h
  rw [hL, hR, hscal, mul_assoc]

end RS

end
