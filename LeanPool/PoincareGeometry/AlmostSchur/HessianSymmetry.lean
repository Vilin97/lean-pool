/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.Hessian
public import LeanPool.PoincareGeometry.AlmostSchur.MetricConnectionCoordinates
public import LeanPool.PoincareGeometry.AlmostSchur.TorsionCoordinates
public import LeanPool.PoincareGeometry.AlmostSchur.GradientRegularity

/-!
# Symmetry of the intrinsic covariant Hessian

Metric compatibility differentiates the gradient pairing. The scalar
commutator in a chart equates its mixed directional derivatives, while
vanishing torsion cancels the covariant derivatives of the coordinate fields.
Gradient regularity is discharged using the actual Riesz gradient theorem.
-/

@[expose] public noncomputable section

open Bundle FiberBundle Set VectorField
open scoped Manifold ContDiff Topology

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)

/-- A coordinate-constant tangent field is differentiable on its chart. -/
theorem mdifferentiableAt_coordinateConstSection (c x : M)
    (hx : x ∈ (chartAt H c).source) (u : E) :
    MDiffAt (T% (fun y ↦ (trivializationAt E TM c).symmL ℝ y u)) x := by
  let e := trivializationAt E TM c
  have hxe : x ∈ e.baseSet := hx
  apply (e.mdifferentiableAt_section_iff I _ hxe).mpr
  apply mdifferentiableAt_const.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hxe] with y hy
  rw [← e.continuousLinearMapAt_apply_of_mem ℝ hy, e.continuousLinearMapAt_symmL hy]

variable [FiniteDimensional ℝ E] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
/-- The scalar commutator along coordinate-constant fields vanishes.
It is proved using the ordinary Lie-bracket commutator theorem in the chart;
the gradient hypothesis supplies only differentiability of its pairings. -/
theorem coordinate_gradient_pairing_commute
    {f : M → ℝ} (c x : M) (hx : x ∈ (chartAt H c).source)
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f x)
    (hg : MDiffAt (T% (gradient (I := I) f)) x) (u v : E) :
    let e := trivializationAt E TM c
    mvfderiv I (fun y ↦ inner ℝ (gradient (I := I) f y) (e.symmL ℝ y v)) x
        (e.symmL ℝ x u) =
      mvfderiv I (fun y ↦ inner ℝ (gradient (I := I) f y) (e.symmL ℝ y u)) x
        (e.symmL ℝ x v) := by
  let e := trivializationAt E TM c
  let a := fun w y ↦ inner ℝ (gradient (I := I) f y) (e.symmL ℝ y w)
  let q := f ∘ (extChartAt I c).symm
  have hx' : x ∈ (extChartAt I c).source := by simpa using hx
  have hz := (extChartAt I c).map_source hx'
  have htarget := (isOpen_extChartAt_target (I := I) c).mem_nhds hz
  have hci : ContMDiffAt 𝓘(ℝ, E) I 2 (extChartAt I c).symm (extChartAt I c x) :=
    (contMDiffWithinAt_extChartAt_symm_target c hz).contMDiffAt htarget
  have hq : ContDiffAt ℝ 2 q (extChartAt I c x) :=
    (hf.comp_of_eq hci ((extChartAt I c).left_inv hx')).contDiffAt
  have hnear : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ) f y :=
    ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp hf).mono
      (fun y hy ↦ hy.mdifferentiableAt (by simp))
  have hcont : Filter.Tendsto (extChartAt I c).symm
      (𝓝 (extChartAt I c x)) (𝓝 x) := by
    simpa only [(extChartAt I c).left_inv hx'] using
      (continuousAt_extChartAt_symm' (I := I) hx').tendsto
  have heq (w : E) : (a w ∘ (extChartAt I c).symm) =ᶠ[𝓝 (extChartAt I c x)]
      (fun z ↦ fderiv ℝ q z w) := by
    filter_upwards [htarget, hcont hnear] with z hzt hfz
    have hy : (extChartAt I c).symm z ∈ (chartAt H c).source := by
      simpa using (extChartAt I c).map_target hzt
    have h := fderiv_chart_comp f c ((extChartAt I c).symm z) hy hfz w
    simpa only [(extChartAt I c).right_inv hzt, Function.comp_apply, a,
      inner_gradient] using h.symm
  have ha (w : E) : MDifferentiableAt I 𝓘(ℝ) (a w) x :=
    MDifferentiableAt.inner_bundle (F := E) (E := TM) hg
      (mdifferentiableAt_coordinateConstSection c x hx w)
  have hmix := fderiv_apply_lieBracket (V := fun _ ↦ u) (W := fun _ ↦ v)
    hq (by simp) (differentiableAt_const v) (differentiableAt_const u)
  have hzero : lieBracket ℝ (fun _ : E ↦ u) (fun _ : E ↦ v) (extChartAt I c x) = 0 := by
    simp [lieBracket_eq]
  rw [hzero, map_zero] at hmix
  have hmixed := sub_eq_zero.mp hmix.symm
  change mvfderiv I (a v) x (e.symmL ℝ x u) = mvfderiv I (a u) x (e.symmL ℝ x v)
  rw [← fderiv_chart_comp (a v) c x hx (ha v) u,
    ← fderiv_chart_comp (a u) c x hx (ha u) v,
    (heq v).fderiv_eq, (heq u).fderiv_eq]
  exact hmixed

variable [CompleteSpace E]

/-- Symmetry at a point, with gradient differentiability made explicit as a
regularity input. Torsion need only vanish at that point. -/
theorem hessian_symmetric_of_mdifferentiableAt_gradient
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov)
    {f : M → ℝ} {x : M} (ht : cov.torsion x = 0)
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f x)
    (hg : MDiffAt (T% (gradient (I := I) f)) x) (u v : TM x) :
    hessian cov f x u v = hessian cov f x v u := by
  let e := trivializationAt E TM x
  let U := fun y ↦ e.symmL ℝ y (e.continuousLinearMapAt ℝ x u)
  let V := fun y ↦ e.symmL ℝ y (e.continuousLinearMapAt ℝ x v)
  have hx : x ∈ (chartAt H x).source := mem_chart_source H x
  have hxe : x ∈ e.baseSet := hx
  have hU : MDiffAt (T% U) x := mdifferentiableAt_coordinateConstSection x x hx _
  have hV : MDiffAt (T% V) x := mdifferentiableAt_coordinateConstSection x x hx _
  have hUx : U x = u := e.symmL_continuousLinearMapAt hxe u
  have hVx : V x = v := e.symmL_continuousLinearMapAt hxe v
  have hUV := cov.torsion_apply hU hV
  rw [ht, mlieBracket_tangent_symmL_eq_zero x x hx] at hUV
  have hc : cov V x (U x) = cov U x (V x) := by
    apply sub_eq_zero.mp
    simpa only [zero_apply, sub_zero] using hUV.symm
  have h1 := CovariantDerivative.IsMetricCompatible.mvfderiv_inner_eq hm U hg hV
  have h2 := CovariantDerivative.IsMetricCompatible.mvfderiv_inner_eq hm V hg hU
  have hmix := coordinate_gradient_pairing_commute x x hx hf hg
    (e.continuousLinearMapAt ℝ x u) (e.continuousLinearMapAt ℝ x v)
  change mvfderiv I (fun y ↦ inner ℝ (gradient (I := I) f y) (V y)) x (U x) =
    mvfderiv I (fun y ↦ inner ℝ (gradient (I := I) f y) (U y)) x (V x) at hmix
  rw [h1, h2] at hmix
  dsimp only at hmix
  rw [hc] at hmix
  have h := add_right_cancel hmix
  simpa only [hessian_apply, hUx, hVx] using h

/-- A C² scalar function has symmetric intrinsic Hessian for a
metric-compatible connection whose torsion vanishes at the point. -/
theorem hessian_symmetric_at
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov)
    {f : M → ℝ} {x : M} (ht : cov.torsion x = 0)
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f x) (u v : TM x) :
    hessian cov f x u v = hessian cov f x v u :=
  hessian_symmetric_of_mdifferentiableAt_gradient cov hm ht hf
    (mdifferentiableAt_gradient hf) u v

/-- Global C² Hessian symmetry, with gradient regularity derived from the
C¹ metric and no differential identities assumed. -/
theorem hessian_symmetric
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov)
    (ht : cov.torsion = 0) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (x : M) (u v : TM x) : hessian cov f x u v = hessian cov f x v u :=
  hessian_symmetric_at cov hm (congrFun ht x) (hf x) u v

end AlmostSchur
