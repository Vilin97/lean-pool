/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.CoordinateMetricVariation
public import LeanPool.PoincareGeometry.AlmostSchur.HessianSymmetry

/-! # The covariant Hessian in a tangent coordinate frame -/

@[expose] public noncomputable section
open Bundle FiberBundle Set AlmostSchur
open scoped Manifold ContDiff Topology
namespace LichnerowiczObata
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)

/-- The intrinsic Hessian equals the ordinary coordinate second derivative
minus the actual connection coefficient. Metric compatibility supplies the
identity; no coordinate formula is assumed for the Hessian. -/
theorem hessian_coordinate_eq_second_sub_connection
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    {f : M → ℝ} (c x : M) (hx : x ∈ (chartAt H c).source)
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f x) (u v : E) :
    let e := trivializationAt E TM c
    let q := f ∘ (extChartAt I c).symm
    hessian cov f x (e.symmL ℝ x u) (e.symmL ℝ x v) =
      fderiv ℝ (fderiv ℝ q) (extChartAt I c x) u v -
        fderiv ℝ q (extChartAt I c x) (frameConnectionCoefficients cov e b x u v) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let e := trivializationAt E TM c
  let q := f ∘ (extChartAt I c).symm
  let a := fun y => inner ℝ (gradient (I := I) f y) (e.symmL ℝ y v)
  have hx' : x ∈ (extChartAt I c).source := by simpa using hx
  have hz := (extChartAt I c).map_source hx'
  have htarget := (isOpen_extChartAt_target (I := I) c).mem_nhds hz
  have hci : ContMDiffAt 𝓘(ℝ, E) I 2 (extChartAt I c).symm (extChartAt I c x) :=
    (contMDiffWithinAt_extChartAt_symm_target c hz).contMDiffAt htarget
  have hq : ContDiffAt ℝ 2 q (extChartAt I c x) :=
    (hf.comp_of_eq hci ((extChartAt I c).left_inv hx')).contDiffAt
  have hnear : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ) f y :=
    ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp hf).mono
      (fun y hy => hy.mdifferentiableAt (by simp))
  have hcont : Filter.Tendsto (extChartAt I c).symm
      (𝓝 (extChartAt I c x)) (𝓝 x) := by
    simpa only [(extChartAt I c).left_inv hx'] using
      (continuousAt_extChartAt_symm' (I := I) hx').tendsto
  have heq : (a ∘ (extChartAt I c).symm) =ᶠ[𝓝 (extChartAt I c x)]
      (fun z => fderiv ℝ q z v) := by
    filter_upwards [htarget, hcont hnear] with z hzt hfz
    have hy : (extChartAt I c).symm z ∈ (chartAt H c).source := by
      simpa using (extChartAt I c).map_target hzt
    have h := fderiv_chart_comp f c ((extChartAt I c).symm z) hy hfz v
    simpa only [(extChartAt I c).right_inv hzt, Function.comp_apply, a,
      inner_gradient] using h.symm
  have hg := mdifferentiableAt_gradient hf
  have hv := mdifferentiableAt_coordinateConstSection (I := I) c x hx v
  have ha : MDifferentiableAt I 𝓘(ℝ) a x :=
    MDifferentiableAt.inner_bundle (F := E) (E := TM) hg hv
  have hh := CovariantDerivative.IsMetricCompatible.mvfderiv_inner_eq hm
    (fun y => e.symmL ℝ y u) hg hv
  change mvfderiv I a x (e.symmL ℝ x u) =
    hessian cov f x (e.symmL ℝ x u) (e.symmL ℝ x v) +
      inner ℝ (gradient (I := I) f x)
        (cov (fun y => e.symmL ℝ y v) x (e.symmL ℝ x u)) at hh
  rw [← fderiv_chart_comp a c x hx ha u, heq.fderiv_eq,
    covariantDerivative_coordinateConstant cov b c x hx u v, inner_gradient,
    ← fderiv_chart_comp f c x hx (hf.mdifferentiableAt (by norm_num))] at hh
  have hD : DifferentiableAt ℝ (fderiv ℝ q) (extChartAt I c x) :=
    (hq.fderiv_right (show (1 : ℕ∞ω) + 1 ≤ 2 by norm_num)).differentiableAt (by norm_num)
  rw [fderiv_clm_apply hD (differentiableAt_const v)] at hh
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply] at hh
  dsimp only
  linarith

end LichnerowiczObata
