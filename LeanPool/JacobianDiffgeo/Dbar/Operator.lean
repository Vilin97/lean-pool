/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Dbar.SolveDisk
import LeanPool.JacobianDiffgeo.Dbar.Form01

/-!
# The intrinsic `dbar` operator and `IsDbarOn` (`Jacobian/Dbar/Operator.lean`)

Unit: dbar-solvability (`docs/design/dbar-solvability.md` D6/D7, §4.7, §7.3-4).

`SmoothC X` is a hand-rolled subtype `{f : X → ℂ // ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ f}` with our OWN
`AddCommGroup`/`Module ℂ` instances (per design D6: mathlib's bundled `ContMDiffMap` ring/module
instances only give a `Module ℝ` for our target model `𝓘(ℝ,ℂ)`, and layering a competing `ℂ`
scalar action on mathlib's own type is exactly the `restrictScalars` diamond trap the blueprint
warns about — a private subtype dodges it). Closure under the ring/module operations, and the
chart-representative smoothness needed for `dbar`, are proved via the CC7 bridge
`contMDiffAt_real_iff_contDiffAt` (`Jacobian.Surface.RealSmooth`) and the composition
`ContMDiffOn.comp` with `contMDiffOn_extChartAt_symm` (mathlib), reduced to `ContDiffOn ℝ` via
`contMDiffOn_iff_contDiffOn` — this avoids needing any project-local "chart invariance for real
smoothness" lemma (`extChartAt 𝓘(ℂ) x` coincides with `chartAt ℂ x` definitionally, `Compat`
bridge facts checked in-line).

The intrinsic `dbar : SmoothC X →ₗ[ℂ] Form01 X` is chart-local `wirtingerDbar` of the chart
representative; `IsDbarAt`/`IsDbarOn` are the chart-free (evaluated-at-centers) local dbar-equation
predicates (D7); `exists_dbar_solution_chart_ball` transports Forster 13.2 (`SolveDisk.lean`)
through a chart.
-/

open scoped ContDiff Manifold
open Set IsManifold

noncomputable section

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### `SmoothC X`: real-smooth `ℂ`-valued functions, with `ℂ`-linear structure -/

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Real-smooth `ℂ`-valued functions on `X`, as a private subtype (D6). -/
def SmoothC (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] :
    Type _ :=
  {f : X → ℂ // ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f}

namespace SmoothC

instance : FunLike (SmoothC X) X ℂ where
  coe f := f.1
  coe_injective _ _ h := Subtype.ext h

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem contMDiff (f : SmoothC X) : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (⇑f) := f.2

/-- **Compat** (design §4.7): the chart representative of a `SmoothC` function is planar-smooth
on the whole chart target (not just at the chart's own centre): compose the globally `ContMDiff`
function with the (mathlib) chart-inverse smoothness `contMDiffOn_extChartAt_symm`, then reduce
`ContMDiff` on planar sets to `ContDiff` via `contMDiffOn_iff_contDiffOn`. -/
theorem contDiffOn_comp_chartAt_symm (f : SmoothC X) (x : X) :
    ContDiffOn ℝ ∞ (⇑f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x).target := by
  have hg : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (⇑f) Set.univ := f.contMDiff.contMDiffOn
  have hf' : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (⇑(chartAt ℂ x).symm) (chartAt ℂ x).target := by
    have h1 := contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, ℂ)) (n := (∞ : ℕ∞ω)) x
    have htarget : (extChartAt 𝓘(ℝ, ℂ) x).target = (chartAt ℂ x).target := by simp
    rwa [htarget] at h1
  have hcomp : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (⇑f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x).target :=
    hg.comp hf' (fun z _ => Set.mem_univ _)
  exact contMDiffOn_iff_contDiffOn.1 hcomp

theorem contDiffAt_comp_chartAt_symm_self (f : SmoothC X) (x : X) :
    ContDiffAt ℝ ∞ (⇑f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) :=
  (f.contDiffOn_comp_chartAt_symm x).contDiffAt
    ((chartAt ℂ x).open_target.mem_nhds (mem_chart_target ℂ x))

theorem differentiableAt_comp_chartAt_symm (f : SmoothC X) (x : X) {z : ℂ}
    (hz : z ∈ (chartAt ℂ x).target) :
    DifferentiableAt ℝ (⇑f ∘ ⇑(chartAt ℂ x).symm) z :=
  ((f.contDiffOn_comp_chartAt_symm x).contDiffAt
    ((chartAt ℂ x).open_target.mem_nhds hz)).differentiableAt (by norm_num)

/-- Chart-local closure helper: if the chart representatives of `f` are `ContDiffAt` at every
chart centre, `f` is `ContMDiff`. -/
private theorem contMDiff_of_chart_op {f : X → ℂ}
    (h : ∀ x, ContDiffAt ℝ ∞ (f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x)) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f := fun x => contMDiffAt_real_iff_contDiffAt.2 (h x)

instance : Add (SmoothC X) where
  add f g := ⟨fun x => f x + g x, contMDiff_of_chart_op fun x =>
    (f.contDiffAt_comp_chartAt_symm_self x).add (g.contDiffAt_comp_chartAt_symm_self x)⟩

instance : Neg (SmoothC X) where
  neg f := ⟨fun x => -f x, contMDiff_of_chart_op fun x =>
    (f.contDiffAt_comp_chartAt_symm_self x).neg⟩

instance : Sub (SmoothC X) where
  sub f g := ⟨fun x => f x - g x, contMDiff_of_chart_op fun x =>
    (f.contDiffAt_comp_chartAt_symm_self x).sub (g.contDiffAt_comp_chartAt_symm_self x)⟩

instance : Zero (SmoothC X) where
  zero := ⟨fun _ => 0, contMDiff_of_chart_op fun _ => contDiffAt_const⟩

instance : SMul ℂ (SmoothC X) where
  smul c f := ⟨fun x => c * f x, contMDiff_of_chart_op fun x =>
    (ContinuousLinearMap.mul ℝ ℂ c).contDiff.contDiffAt.comp _
      (f.contDiffAt_comp_chartAt_symm_self x)⟩

@[simp] theorem coe_add (f g : SmoothC X) (x : X) : (f + g) x = f x + g x := rfl
@[simp] theorem coe_neg (f : SmoothC X) (x : X) : (-f) x = -f x := rfl
@[simp] theorem coe_sub (f g : SmoothC X) (x : X) : (f - g) x = f x - g x := rfl
@[simp] theorem coe_zero (x : X) : (0 : SmoothC X) x = 0 := rfl
@[simp] theorem coe_smul (c : ℂ) (f : SmoothC X) (x : X) : (c • f) x = c * f x := rfl

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem ext' {f g : SmoothC X} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.coe_injective (funext h)

instance : AddCommGroup (SmoothC X) where
  add_assoc a b c := ext' fun x => by simp [add_assoc]
  zero_add a := ext' fun x => by simp
  add_zero a := ext' fun x => by simp
  add_comm a b := ext' fun x => by simp [add_comm]
  neg_add_cancel a := ext' fun x => by simp
  sub_eq_add_neg a b := ext' fun x => by simp [sub_eq_add_neg]
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Module ℂ (SmoothC X) where
  smul_zero a := ext' fun x => by simp
  smul_add a b c := ext' fun x => by simp [mul_add]
  add_smul a b c := ext' fun x => by simp [add_mul]
  zero_smul a := ext' fun x => by simp
  one_smul a := ext' fun x => by simp
  mul_smul a b c := ext' fun x => by simp [mul_assoc]

end SmoothC

/-! ### The intrinsic `dbar` -/

/-- The raw coefficient family underlying `dbar f`: chart-local `wirtingerDbar` of the chart
representative of `f`, junk-zero off the chart target. -/
private def dbarCoeffAt (f : SmoothC X) (x : X) : ℂ → ℂ :=
  (chartAt ℂ x).target.indicator (fun z => wirtingerDbar (⇑f ∘ ⇑(chartAt ℂ x).symm) z)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
private theorem dbarCoeffAt_of_mem (f : SmoothC X) (x : X) {z : ℂ} (hz : z ∈ (chartAt ℂ x).target) :
    dbarCoeffAt f x z = wirtingerDbar (⇑f ∘ ⇑(chartAt ℂ x).symm) z :=
  Set.indicator_of_mem hz _

private theorem dbarCoeffAt_compat (f : SmoothC X) (x y : X) (z : ℂ)
    (hz : z ∈ ⇑(chartAt ℂ y) '' ((chartAt ℂ x).source ∩ (chartAt ℂ y).source)) :
    dbarCoeffAt f y z = (starRingEnd ℂ) (deriv (⇑(chartAt ℂ x) ∘ ⇑(chartAt ℂ y).symm) z) *
      dbarCoeffAt f x (chartAt ℂ x ((chartAt ℂ y).symm z)) := by
  obtain ⟨p, ⟨hpx, hpy⟩, rfl⟩ := hz
  have hty : chartAt ℂ y p ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source hpy
  have htx : chartAt ℂ x p ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source hpx
  rw [(chartAt ℂ y).left_inv hpy, dbarCoeffAt_of_mem f y hty, dbarCoeffAt_of_mem f x htx]
  set τ : ℂ → ℂ := ⇑(chartAt ℂ x) ∘ ⇑(chartAt ℂ y).symm with hτ_def
  have hzs : (chartAt ℂ y).symm (chartAt ℂ y p) ∈ (chartAt ℂ x).source := by
    rw [(chartAt ℂ y).left_inv hpy]; exact hpx
  have hτ_an : AnalyticAt ℂ τ (chartAt ℂ y p) :=
    analyticAt_trans (chart_mem_maximalAtlas x) (chart_mem_maximalAtlas y) hty hzs
  have hτ_diff : DifferentiableAt ℂ τ (chartAt ℂ y p) := hτ_an.differentiableAt
  have hτ_pt : τ (chartAt ℂ y p) = chartAt ℂ x p := by
    simp only [hτ_def, Function.comp_apply, (chartAt ℂ y).left_inv hpy]
  have hFx_diff : DifferentiableAt ℝ (⇑f ∘ ⇑(chartAt ℂ x).symm) (τ (chartAt ℂ y p)) := by
    rw [hτ_pt]; exact f.differentiableAt_comp_chartAt_symm x htx
  have hWopen : IsOpen (⇑(chartAt ℂ y) '' ((chartAt ℂ x).source ∩ (chartAt ℂ y).source)) :=
    (chartAt ℂ y).isOpen_image_of_subset_source
      ((chartAt ℂ x).open_source.inter (chartAt ℂ y).open_source) inter_subset_right
  have hzW : chartAt ℂ y p ∈ ⇑(chartAt ℂ y) '' ((chartAt ℂ x).source ∩ (chartAt ℂ y).source) :=
    ⟨p, ⟨hpx, hpy⟩, rfl⟩
  have heq : (⇑f ∘ ⇑(chartAt ℂ y).symm) =ᶠ[nhds (chartAt ℂ y p)]
      (⇑f ∘ ⇑(chartAt ℂ x).symm) ∘ τ := by
    filter_upwards [hWopen.mem_nhds hzW] with w hw
    obtain ⟨q, ⟨hqx, hqy⟩, rfl⟩ := hw
    simp only [Function.comp_apply, hτ_def, (chartAt ℂ y).left_inv hqy,
      (chartAt ℂ x).left_inv hqx]
  rw [wirtingerDbar_congr_nhds _ _ (chartAt ℂ y p) heq,
    wirtingerDbar_comp_differentiableAt (⇑f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ y p) hFx_diff hτ_diff,
    hτ_pt]

/-- The intrinsic `dbar`, chart-locally the planar Wirtinger operator. -/
noncomputable def dbar : SmoothC X →ₗ[ℂ] Form01 X where
  toFun f :=
    { coeffAt := dbarCoeffAt f
      coeffAt_zero_off := fun x z hz => Set.indicator_of_notMem hz _
      contDiffOn_coeffAt := fun x => by
        apply (contDiffOn_wirtingerDbar (⇑f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x).open_target
          (f.contDiffOn_comp_chartAt_symm x)).congr
        intro z hz
        exact dbarCoeffAt_of_mem f x hz
      compat := dbarCoeffAt_compat f }
  map_add' f g := by
    apply Form01.ext
    intro x z hz
    change dbarCoeffAt (f + g) x z = dbarCoeffAt f x z + dbarCoeffAt g x z
    rw [dbarCoeffAt_of_mem (f + g) x hz, dbarCoeffAt_of_mem f x hz, dbarCoeffAt_of_mem g x hz]
    have heq : (⇑(f + g) : X → ℂ) ∘ ⇑(chartAt ℂ x).symm =
        (⇑f ∘ ⇑(chartAt ℂ x).symm) + (⇑g ∘ ⇑(chartAt ℂ x).symm) := by
      funext w; simp
    rw [heq]
    have hp := (chartAt ℂ x).map_target hz
    exact wirtingerDbar_add _ _ z (f.differentiableAt_comp_chartAt_symm x hz)
      (g.differentiableAt_comp_chartAt_symm x hz)
  map_smul' c f := by
    apply Form01.ext
    intro x z hz
    change dbarCoeffAt (c • f) x z = c * dbarCoeffAt f x z
    rw [dbarCoeffAt_of_mem (c • f) x hz, dbarCoeffAt_of_mem f x hz]
    have heq : (⇑(c • f) : X → ℂ) ∘ ⇑(chartAt ℂ x).symm =
        fun w => c * (⇑f ∘ ⇑(chartAt ℂ x).symm) w := by
      funext w; simp
    rw [heq, wirtingerDbar_const_mul _ z c (f.differentiableAt_comp_chartAt_symm x hz)]

@[simp]
theorem coeffAt_dbar (f : SmoothC X) (x : X) {z : ℂ} (hz : z ∈ (chartAt ℂ x).target) :
    (dbar f).coeffAt x z = wirtingerDbar (⇑f ∘ ⇑(chartAt ℂ x).symm) z :=
  dbarCoeffAt_of_mem f x hz

/-! ### `IsDbarAt` / `IsDbarOn` (D7): chart-free local `dbar`-equations -/

/-- `u` solves `dbaru = η` at `x`, evaluated in `x`'s own preferred chart. -/
def IsDbarAt (u : X → ℂ) (η : Form01 X) (x : X) : Prop :=
  wirtingerDbar (u ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) = η.coeffAt x (chartAt ℂ x x)

/-- `u` solves `dbaru = η` at every point of `s`. -/
def IsDbarOn (u : X → ℂ) (η : Form01 X) (s : Set X) : Prop := ∀ x ∈ s, IsDbarAt u η x

theorem isDbarOn_dbar (f : SmoothC X) : IsDbarOn (⇑f) (dbar f) Set.univ := by
  intro x _
  change wirtingerDbar (⇑f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) =
    (dbar f).coeffAt x (chartAt ℂ x x)
  rw [coeffAt_dbar f x (mem_chart_target ℂ x)]

/-- The chart-transition transport of the local `dbar`-equation: `IsDbarAt` at every point of `s`
(each evaluated in ITS OWN preferred chart) forces the coefficient equation for `η` to hold on
the WHOLE image of `s` under any single chart `x₀` whose source contains `s`, provided `u` is
`ContMDiff` there (needed to actually invoke the `(0,1)` chain rule, not just junk-`0`
`wirtingerDbar`). This is the key lemma underlying `dbar_eq_iff`,
`contMDiffOn_omega_of_isDbarOn_zero`, and `exists_dbar_solution_chart_ball`. -/
theorem eqOn_coeffAt_of_isDbarOn {x₀ : X} {s : Set X} (hs : IsOpen s)
    (hsub : s ⊆ (chartAt ℂ x₀).source)
    {u : X → ℂ} {η : Form01 X} (hu : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ u s)
    (h : ∀ x ∈ s, IsDbarAt u η x) :
    Set.EqOn (wirtingerDbar (u ∘ ⇑(chartAt ℂ x₀).symm)) (η.coeffAt x₀) (⇑(chartAt ℂ x₀) '' s) := by
  rintro z ⟨x, hx, rfl⟩
  have hxx₀ : x ∈ (chartAt ℂ x₀).source := hsub hx
  have hzt : chartAt ℂ x₀ x ∈ (chartAt ℂ x₀).target := (chartAt ℂ x₀).map_source hxx₀
  set σ : ℂ → ℂ := ⇑(chartAt ℂ x) ∘ ⇑(chartAt ℂ x₀).symm with hσ_def
  have hzs : (chartAt ℂ x₀).symm (chartAt ℂ x₀ x) ∈ (chartAt ℂ x).source := by
    rw [(chartAt ℂ x₀).left_inv hxx₀]; exact mem_chart_source ℂ x
  have hσ_an : AnalyticAt ℂ σ (chartAt ℂ x₀ x) :=
    analyticAt_trans (chart_mem_maximalAtlas x) (chart_mem_maximalAtlas x₀) hzt hzs
  have hσ_diff : DifferentiableAt ℂ σ (chartAt ℂ x₀ x) := hσ_an.differentiableAt
  have hσ_pt : σ (chartAt ℂ x₀ x) = chartAt ℂ x x := by
    simp only [hσ_def, Function.comp_apply, (chartAt ℂ x₀).left_inv hxx₀]
  have hu_diff : DifferentiableAt ℝ (u ∘ ⇑(chartAt ℂ x).symm) (σ (chartAt ℂ x₀ x)) := by
    rw [hσ_pt]
    exact (contMDiffAt_real_iff_contDiffAt.1
      ((hu x hx).contMDiffAt (hs.mem_nhds hx))).differentiableAt (by norm_num)
  have hWopen : IsOpen (⇑(chartAt ℂ x₀) '' ((chartAt ℂ x).source ∩ (chartAt ℂ x₀).source)) :=
    (chartAt ℂ x₀).isOpen_image_of_subset_source
      ((chartAt ℂ x).open_source.inter (chartAt ℂ x₀).open_source) inter_subset_right
  have hzW : chartAt ℂ x₀ x ∈ ⇑(chartAt ℂ x₀) '' ((chartAt ℂ x).source ∩ (chartAt ℂ x₀).source) :=
    ⟨x, ⟨mem_chart_source ℂ x, hxx₀⟩, rfl⟩
  have heq : (u ∘ ⇑(chartAt ℂ x₀).symm) =ᶠ[nhds (chartAt ℂ x₀ x)]
      (u ∘ ⇑(chartAt ℂ x).symm) ∘ σ := by
    filter_upwards [hWopen.mem_nhds hzW] with w hw
    obtain ⟨q, ⟨hqx, hqx₀⟩, rfl⟩ := hw
    simp only [Function.comp_apply, hσ_def, (chartAt ℂ x₀).left_inv hqx₀,
      (chartAt ℂ x).left_inv hqx]
  rw [wirtingerDbar_congr_nhds _ _ (chartAt ℂ x₀ x) heq,
    wirtingerDbar_comp_differentiableAt (u ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x₀ x) hu_diff hσ_diff,
    hσ_pt, h x hx]
  have hcompat := η.compat x x₀ (chartAt ℂ x₀ x) ⟨x, ⟨mem_chart_source ℂ x, hxx₀⟩, rfl⟩
  rw [(chartAt ℂ x₀).left_inv hxx₀] at hcompat
  rw [← hσ_def] at hcompat
  exact hcompat.symm

theorem dbar_eq_iff {f : SmoothC X} {η : Form01 X} : dbar f = η ↔ IsDbarOn (⇑f) η Set.univ := by
  refine ⟨fun h => h ▸ isDbarOn_dbar f, fun h => ?_⟩
  apply Form01.ext
  intro x z hz
  rw [coeffAt_dbar f x hz]
  have hxs : (chartAt ℂ x).symm z ∈ (chartAt ℂ x).source := (chartAt ℂ x).map_target hz
  have hmem : z ∈ ⇑(chartAt ℂ x) '' (chartAt ℂ x).source :=
    ⟨(chartAt ℂ x).symm z, hxs, (chartAt ℂ x).right_inv hz⟩
  exact eqOn_coeffAt_of_isDbarOn (chartAt ℂ x).open_source (Set.Subset.refl _)
    (f.contMDiff.contMDiffOn) (fun y _ => h y (Set.mem_univ y)) hmem

/-- `ContMDiffOn` on a fixed chart's target, transported from a `ContMDiffOn` hypothesis on `X`
via one composition with the (mathlib) chart-inverse smoothness — the "any-chart" analogue of
`SmoothC.contDiffOn_comp_chartAt_symm` for a merely-local `ContMDiffOn` hypothesis. -/
private theorem contDiffOn_comp_chartAt_symm_of_contMDiffOn {u : X → ℂ} {s : Set X}
    (hu : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ u s) (x₀ : X) :
    ContDiffOn ℝ ∞ (u ∘ ⇑(chartAt ℂ x₀).symm) (⇑(chartAt ℂ x₀) '' (s ∩ (chartAt ℂ x₀).source)) := by
  have hf' : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (⇑(chartAt ℂ x₀).symm) (chartAt ℂ x₀).target := by
    have h1 := contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, ℂ)) (n := (∞ : ℕ∞ω)) x₀
    have htarget : (extChartAt 𝓘(ℝ, ℂ) x₀).target = (chartAt ℂ x₀).target := by simp
    rwa [htarget] at h1
  have hsub : ⇑(chartAt ℂ x₀) '' (s ∩ (chartAt ℂ x₀).source) ⊆ (chartAt ℂ x₀).target := by
    rintro w ⟨y, ⟨_, hy⟩, rfl⟩; exact (chartAt ℂ x₀).map_source hy
  have hcomp : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (u ∘ ⇑(chartAt ℂ x₀).symm)
      (⇑(chartAt ℂ x₀) '' (s ∩ (chartAt ℂ x₀).source)) := by
    apply hu.comp (hf'.mono hsub)
    rintro w ⟨y, ⟨hys, hyx₀⟩, rfl⟩
    simp only [Set.mem_preimage, (chartAt ℂ x₀).left_inv hyx₀]
    exact hys
  exact contMDiffOn_iff_contDiffOn.1 hcomp

/-- Deliverable (iv): a smooth `dbar`-closed function is holomorphic. -/
theorem contMDiffOn_omega_of_isDbarOn_zero {u : X → ℂ} {s : Set X} (hs : IsOpen s)
    (hu : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ u s) (h : IsDbarOn u 0 s) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω u s := by
  intro x₀ hx₀
  have heqOn : Set.EqOn (wirtingerDbar (u ∘ ⇑(chartAt ℂ x₀).symm))
      ((0 : Form01 X).coeffAt x₀) (⇑(chartAt ℂ x₀) '' (s ∩ (chartAt ℂ x₀).source)) :=
    eqOn_coeffAt_of_isDbarOn (hs.inter (chartAt ℂ x₀).open_source) inter_subset_right
      (hu.mono inter_subset_left) (fun x hx => h x hx.1)
  have hzero : ∀ z ∈ ⇑(chartAt ℂ x₀) '' (s ∩ (chartAt ℂ x₀).source),
      wirtingerDbar (u ∘ ⇑(chartAt ℂ x₀).symm) z = 0 := fun z hz => heqOn hz
  have hxs₀ : x₀ ∈ s ∩ (chartAt ℂ x₀).source := ⟨hx₀, mem_chart_source ℂ x₀⟩
  have hWopen : IsOpen (⇑(chartAt ℂ x₀) '' (s ∩ (chartAt ℂ x₀).source)) :=
    (chartAt ℂ x₀).isOpen_image_of_subset_source (hs.inter (chartAt ℂ x₀).open_source)
      inter_subset_right
  have hzW : chartAt ℂ x₀ x₀ ∈ ⇑(chartAt ℂ x₀) '' (s ∩ (chartAt ℂ x₀).source) :=
    ⟨x₀, hxs₀, rfl⟩
  have hcdOn := contDiffOn_comp_chartAt_symm_of_contMDiffOn hu x₀
  have hdiffOn : DifferentiableOn ℂ (u ∘ ⇑(chartAt ℂ x₀).symm)
      (⇑(chartAt ℂ x₀) '' (s ∩ (chartAt ℂ x₀).source)) := by
    apply differentiableOn_of_wirtingerDbar_eq_zero (u ∘ ⇑(chartAt ℂ x₀).symm) hWopen _ hzero
    intro z hz
    exact (hcdOn.contDiffAt (hWopen.mem_nhds hz)).differentiableAt (by norm_num)
  have hanalytic := hdiffOn.analyticOnNhd hWopen
  have hOn : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω u (s ∩ (chartAt ℂ x₀).source) :=
    (contMDiffOn_iff_analyticOnNhd_of_subset_source (chart_mem_atlas ℂ x₀)
      inter_subset_right (hs.inter (chartAt ℂ x₀).open_source)).2 hanalytic
  exact (hOn.contMDiffAt ((hs.inter (chartAt ℂ x₀).open_source).mem_nhds hxs₀)).contMDiffWithinAt

/-- Deliverable (v): two smooth solutions of the same `dbar`-equation differ by a holomorphic
function. -/
theorem contMDiffOn_omega_sub_of_isDbarOn {u v : X → ℂ} {η : Form01 X} {s : Set X}
    (hs : IsOpen s) (hu : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ u s)
    (hv : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ v s) (h1 : IsDbarOn u η s) (h2 : IsDbarOn v η s) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (u - v) s := by
  have hzero : IsDbarOn (u - v) 0 s := by
    intro x hx
    have hequ : (u - v) ∘ ⇑(chartAt ℂ x).symm
        = (u ∘ ⇑(chartAt ℂ x).symm) - (v ∘ ⇑(chartAt ℂ x).symm) := by funext w; simp
    have hud : DifferentiableAt ℝ (u ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) :=
      (contMDiffAt_real_iff_contDiffAt.1
        ((hu x hx).contMDiffAt (hs.mem_nhds hx))).differentiableAt (by norm_num)
    have hvd : DifferentiableAt ℝ (v ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) :=
      (contMDiffAt_real_iff_contDiffAt.1
        ((hv x hx).contMDiffAt (hs.mem_nhds hx))).differentiableAt (by norm_num)
    change wirtingerDbar ((u - v) ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) = 0
    rw [hequ, wirtingerDbar_sub _ _ (chartAt ℂ x x) hud hvd, h1 x hx, h2 x hx, sub_self]
  have hcd : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (u - v) s := fun x hx => (hu x hx).sub (hv x hx)
  exact contMDiffOn_omega_of_isDbarOn_zero hs hcd hzero

/-! ### Chart-disk solvability -/

/-- Deliverable (vi): Forster 13.2, transported through a chart — `dbar` is surjective from
`SmoothC`-representatives onto `Form01` data supported in a chart disk. -/
theorem exists_dbar_solution_chart_ball {x₀ : X} {r : ℝ} (hr : 0 < r) {V : Set X}
    (hVs : V ⊆ (chartAt ℂ x₀).source)
    (hVim : ⇑(chartAt ℂ x₀) '' V = Metric.ball (chartAt ℂ x₀ x₀) r) (η : Form01 X) :
    ∃ u : X → ℂ, ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ u V ∧ IsDbarOn u η V := by
  classical
  have hballsub : Metric.ball (chartAt ℂ x₀ x₀) r ⊆ (chartAt ℂ x₀).target := by
    rw [← hVim]; rintro w ⟨y, hy, rfl⟩; exact (chartAt ℂ x₀).map_source (hVs hy)
  have hg_cd : ContDiffOn ℝ ∞ (η.coeffAt x₀) (Metric.ball (chartAt ℂ x₀ x₀) r) :=
    (η.contDiffOn_coeffAt x₀).mono hballsub
  obtain ⟨U, hU_cd, hU_dbar⟩ :=
      exists_dbar_solution_ball (η.coeffAt x₀) (chartAt ℂ x₀ x₀) r hr hg_cd
  have hVeq : V = (chartAt ℂ x₀).source ∩ ⇑(chartAt ℂ x₀) ⁻¹' (Metric.ball (chartAt ℂ x₀ x₀) r) :=
      by
    apply Set.Subset.antisymm
    · intro x hx
      exact ⟨hVs hx, hVim ▸ Set.mem_image_of_mem _ hx⟩
    · intro x hx
      rw [← hVim] at hx
      obtain ⟨y, hy, hxy⟩ := hx.2
      rwa [(chartAt ℂ x₀).injOn hx.1 (hVs hy) hxy.symm]
  have hVopen : IsOpen V := by
    rw [hVeq]
    exact (chartAt ℂ x₀).continuousOn.isOpen_inter_preimage (chartAt ℂ x₀).open_source
      Metric.isOpen_ball
  refine ⟨fun x => if _ : x ∈ V then U (chartAt ℂ x₀ x) else 0, ?_, ?_⟩
  · intro x hx
    have heq : (fun x => if _ : x ∈ V then U (chartAt ℂ x₀ x) else 0) =ᶠ[nhds x]
        (U ∘ ⇑(chartAt ℂ x₀)) := by
      filter_upwards [hVopen.mem_nhds hx] with w hw
      simp [hw]
    apply ContMDiffWithinAt.congr_of_eventuallyEq _
      (Filter.EventuallyEq.filter_mono heq nhdsWithin_le_nhds) (by simp [hx])
    apply ContMDiffAt.contMDiffWithinAt
    have h1 : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (⇑(chartAt ℂ x₀)) x := by
      have h2 := contMDiffOn_extChartAt (I := 𝓘(ℝ, ℂ)) (x := x₀) (n := (∞ : ℕ∞ω))
      have h3 : (extChartAt 𝓘(ℝ, ℂ) x₀ : X → ℂ) = ⇑(chartAt ℂ x₀) := rfl
      rw [h3] at h2
      exact h2.contMDiffAt ((chartAt ℂ x₀).open_source.mem_nhds (hVs hx))
    have h4 : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ U (chartAt ℂ x₀ x) :=
      hU_cd.contMDiffOn.contMDiffAt
        (Metric.isOpen_ball.mem_nhds (hVim ▸ Set.mem_image_of_mem _ hx))
    exact h4.comp x h1
  · intro x hx
    set u : X → ℂ := fun x => if _ : x ∈ V then U (chartAt ℂ x₀ x) else 0 with hu_def
    change wirtingerDbar (u ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) = η.coeffAt x (chartAt ℂ x x)
    have hxx₀ : x ∈ (chartAt ℂ x₀).source := hVs hx
    set τ : ℂ → ℂ := ⇑(chartAt ℂ x₀) ∘ ⇑(chartAt ℂ x).symm with hτ_def
    have hzs : (chartAt ℂ x).symm (chartAt ℂ x x) ∈ (chartAt ℂ x₀).source := by
      rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]; exact hxx₀
    have hτ_an : AnalyticAt ℂ τ (chartAt ℂ x x) :=
      analyticAt_trans (chart_mem_maximalAtlas x₀) (chart_mem_maximalAtlas x)
        (mem_chart_target ℂ x) hzs
    have hτ_diff : DifferentiableAt ℂ τ (chartAt ℂ x x) := hτ_an.differentiableAt
    have hτ_pt : τ (chartAt ℂ x x) = chartAt ℂ x₀ x := by
      simp only [hτ_def, Function.comp_apply, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
    have hU_diff : DifferentiableAt ℝ U (τ (chartAt ℂ x x)) := by
      rw [hτ_pt]
      exact (hU_cd.contDiffAt
        (Metric.isOpen_ball.mem_nhds (hVim ▸ Set.mem_image_of_mem _ hx))).differentiableAt
        (by norm_num)
    have hWopen : IsOpen (⇑(chartAt ℂ x) '' (V ∩ (chartAt ℂ x).source)) :=
      (chartAt ℂ x).isOpen_image_of_subset_source (hVopen.inter (chartAt ℂ x).open_source)
        inter_subset_right
    have hzW : chartAt ℂ x x ∈ ⇑(chartAt ℂ x) '' (V ∩ (chartAt ℂ x).source) :=
      ⟨x, ⟨hx, mem_chart_source ℂ x⟩, rfl⟩
    have heq : (u ∘ ⇑(chartAt ℂ x).symm) =ᶠ[nhds (chartAt ℂ x x)] U ∘ τ := by
      filter_upwards [hWopen.mem_nhds hzW] with w hw
      obtain ⟨q, ⟨hqV, hqx⟩, rfl⟩ := hw
      simp only [hu_def, Function.comp_apply, (chartAt ℂ x).left_inv hqx, hτ_def]
      rw [dite_eq_left hqV]
    rw [wirtingerDbar_congr_nhds _ _ (chartAt ℂ x x) heq,
      wirtingerDbar_comp_differentiableAt U (chartAt ℂ x x) hU_diff hτ_diff, hτ_pt]
    have hUdbar_pt : wirtingerDbar U (chartAt ℂ x₀ x) = η.coeffAt x₀ (chartAt ℂ x₀ x) :=
      hU_dbar (chartAt ℂ x₀ x) (hVim ▸ Set.mem_image_of_mem _ hx)
    rw [hUdbar_pt]
    have hcompat := η.compat x₀ x (chartAt ℂ x x) ⟨x, ⟨hxx₀, mem_chart_source ℂ x⟩, rfl⟩
    rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)] at hcompat
    rw [← hτ_def] at hcompat
    exact hcompat.symm

end RS
