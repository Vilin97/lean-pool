/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.SphereMetricImmersion

/-! # The intrinsic Hessian of an ambient height on a round sphere -/

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
  {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]

local notation "TM" => (TangentSpace I : M → Type _)

/-- Pulling an ambient height back by an actual metric-preserving
codimension-one sphere map gives the Obata Hessian equation. -/
theorem hessian_height_of_sphere_metric_immersion
    (cov : CovariantDerivative I E TM) (hmc : tangentMetricCompatible cov)
    (ht : cov.torsion = 0)
    {F : M → A} (hF : ContMDiff I 𝓘(ℝ, A) 2 F) {R : ℝ} (hR : 0 < R)
    (hn : ∀ y, ‖F y‖ = R)
    (hm : ∀ (y : M) (u v : TM y),
      inner ℝ (mvfderiv I F y u) (mvfderiv I F y v) = inner ℝ u v)
    (hdim : Module.finrank ℝ A = Module.finrank ℝ E + 1)
    (a : A) (x : M) (u v : TM x) :
    hessian cov (fun y => inner ℝ a (F y)) x u v =
      -(inner ℝ a (F x) / R ^ 2) * inner ℝ u v := by
  classical
  let e := trivializationAt E TM x
  let z := extChartAt I x x
  let Q := F ∘ (extChartAt I x).symm
  let ℓ : A →L[ℝ] ℝ := innerSL ℝ a
  let b := Module.finBasis ℝ E
  let u₀ := e.continuousLinearMapAt ℝ x u
  let v₀ := e.continuousLinearMapAt ℝ x v
  let Γ := frameConnectionCoefficients cov e b x
  have hx : x ∈ (chartAt H x).source := mem_chart_source H x
  have hx' : x ∈ (extChartAt I x).source := by simp
  have hz : z ∈ (extChartAt I x).target := (extChartAt I x).map_source hx'
  have hleft : (extChartAt I x).symm z = x := (extChartAt I x).left_inv hx'
  have htarget := (isOpen_extChartAt_target (I := I) x).mem_nhds hz
  have hci : ContMDiffAt 𝓘(ℝ, E) I 2 (extChartAt I x).symm z :=
    (contMDiffWithinAt_extChartAt_symm_target x hz).contMDiffAt htarget
  have hQ : ContDiffAt ℝ 2 Q z := ((hF x).comp_of_eq hci hleft).contDiffAt
  have hscalar : ContMDiff I 𝓘(ℝ, ℝ) 2 (fun y => inner ℝ a (F y)) :=
    ℓ.contDiff.contMDiff.comp hF
  have hu : e.symmL ℝ x u₀ = u := e.symmL_continuousLinearMapAt hx u
  have hv : e.symmL ℝ x v₀ = v := e.symmL_continuousLinearMapAt hx v
  have hc := hessian_coordinate_eq_second_sub_connection cov hmc b x x hx
    (hscalar x) u₀ v₀
  change hessian cov (fun y => inner ℝ a (F y)) x (e.symmL ℝ x u₀) (e.symmL ℝ x v₀) =
    fderiv ℝ (fderiv ℝ (fun y => ℓ (Q y))) z u₀ v₀ -
      fderiv ℝ (fun y => ℓ (Q y)) z (Γ u₀ v₀) at hc
  rw [hu, hv, second_fderiv_clm_comp_of_contDiffAt_two ℓ hQ] at hc
  have hd : fderiv ℝ (fun y => ℓ (Q y)) z = ℓ.comp (fderiv ℝ Q z) :=
    (ℓ.hasFDerivAt.comp z (hQ.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  have hg := sphere_metric_immersion_coordinate_second_derivative cov hmc ht b
    hF hR hn hm hdim x x hx u₀ v₀
  change fderiv ℝ (fderiv ℝ Q) z u₀ v₀ = fderiv ℝ Q z (Γ u₀ v₀) -
    (inner ℝ (e.symmL ℝ x u₀) (e.symmL ℝ x v₀) / R ^ 2) • F x at hg
  rw [hu, hv] at hg
  rw [hd, ContinuousLinearMap.comp_apply, hg, map_sub, map_smul] at hc
  change hessian cov (fun y => inner ℝ a (F y)) x u v =
    ℓ (fderiv ℝ Q z (Γ u₀ v₀)) - (inner ℝ u v / R ^ 2) * inner ℝ a (F x) -
      ℓ (fderiv ℝ Q z (Γ u₀ v₀)) at hc
  rw [hc]
  ring

end LichnerowiczObata
