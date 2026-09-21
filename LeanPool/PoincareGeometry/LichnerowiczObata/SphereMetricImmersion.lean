/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.SphereImmersionSecondDerivative
public import LeanPool.PoincareGeometry.LichnerowiczObata.HessianCoordinates

/-! # The Gauss formula from an intrinsic metric-preserving sphere map -/

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

/-- The Gauss formula uses the actual intrinsic connection coefficients.
Their symmetry and compatibility with the induced metric are derived from
torsion-freeness and metric compatibility, not supplied as extra bridges. -/
theorem sphere_metric_immersion_coordinate_second_derivative
    (cov : CovariantDerivative I E TM) (hmc : tangentMetricCompatible cov)
    (ht : cov.torsion = 0) {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    {F : M → A} (hF : ContMDiff I 𝓘(ℝ, A) 2 F) {R : ℝ} (hR : 0 < R)
    (hn : ∀ y, ‖F y‖ = R)
    (hm : ∀ (y : M) (u v : TM y),
      inner ℝ (mvfderiv I F y u) (mvfderiv I F y v) = inner ℝ u v)
    (hdim : Module.finrank ℝ A = Module.finrank ℝ E + 1)
    (c x : M) (hx : x ∈ (chartAt H c).source) (u v : E) :
    let e := trivializationAt E TM c
    let Q := F ∘ (extChartAt I c).symm
    let z := extChartAt I c x
    fderiv ℝ (fderiv ℝ Q) z u v =
      fderiv ℝ Q z (frameConnectionCoefficients cov e b x u v) -
        (inner ℝ (e.symmL ℝ x u) (e.symmL ℝ x v) / R ^ 2) • F x := by
  let e := trivializationAt E TM c
  let Q := F ∘ (extChartAt I c).symm
  let z := extChartAt I c x
  let Γ := frameConnectionCoefficients cov e b x
  have hx' : x ∈ (extChartAt I c).source := by simpa using hx
  have hz : z ∈ (extChartAt I c).target := (extChartAt I c).map_source hx'
  have hleft : (extChartAt I c).symm z = x := (extChartAt I c).left_inv hx'
  have htarget := (isOpen_extChartAt_target (I := I) c).mem_nhds hz
  have hci : ContMDiffAt 𝓘(ℝ, E) I 2 (extChartAt I c).symm z :=
    (contMDiffWithinAt_extChartAt_symm_target c hz).contMDiffAt htarget
  have hQ : ContDiffAt ℝ 2 Q z := ((hF x).comp_of_eq hci hleft).contDiffAt
  have hnorm : ∀ᶠ y in 𝓝 z, ‖Q y‖ ^ 2 = R ^ 2 :=
    Filter.Eventually.of_forall (fun y => by simp only [Q, Function.comp_apply, hn])
  have hcoord (y : E) (hy : y ∈ (extChartAt I c).target) (d w : E) :
      inner ℝ (fderiv ℝ Q y d) (fderiv ℝ Q y w) =
        coordinateMetricBilinear (I := I) c y d w := by
    have hy' : (extChartAt I c).symm y ∈ (chartAt H c).source := by
      simpa using (extChartAt I c).map_target hy
    have hd (a : E) := fderiv_chart_comp F c ((extChartAt I c).symm y) hy'
      ((hF _).mdifferentiableAt (by norm_num)) a
    rw [(extChartAt I c).right_inv hy] at hd
    change inner ℝ (fderiv ℝ Q y d) (fderiv ℝ Q y w) = _
    rw [hd d, hd w, hm]
    rfl
  have hcoordx (d w : E) : inner ℝ (fderiv ℝ Q z d) (fderiv ℝ Q z w) =
      inner ℝ (e.symmL ℝ x d) (e.symmL ℝ x w) := by
    have hh := hcoord z hz d w
    rw [coordinateMetricBilinear_apply, hleft] at hh
    exact hh
  have hinj : Function.Injective (fderiv ℝ Q z) := by
    intro d w hdw
    have hh := hcoordx (d - w) (d - w)
    rw [map_sub, hdw, sub_self, inner_zero_left] at hh
    have he := inner_self_eq_zero.mp hh.symm
    have he' := congrArg (e.continuousLinearMapAt ℝ x) he
    rw [e.continuousLinearMapAt_symmL hx, map_zero] at he'
    exact sub_eq_zero.mp he'
  have hmetric (d a w : E) : fderiv ℝ (fun y =>
        inner ℝ (fderiv ℝ Q y a) (fderiv ℝ Q y w)) z d =
      inner ℝ (fderiv ℝ Q z (Γ d a)) (fderiv ℝ Q z w) +
        inner ℝ (fderiv ℝ Q z a) (fderiv ℝ Q z (Γ d w)) := by
    have he : (fun y => inner ℝ (fderiv ℝ Q y a) (fderiv ℝ Q y w)) =ᶠ[𝓝 z]
        (fun y => coordinateMetricBilinear (I := I) c y a w) := by
      filter_upwards [htarget] with y hy using hcoord y hy a w
    rw [he.fderiv_eq, hcoordx, hcoordx]
    simpa only [coordinateMetricBilinear_apply, Function.comp_def, hleft] using
      fderiv_coordinateMetric_pairing_coefficients cov hmc b c x hx d a w
  have hs := sphere_immersion_second_derivative hR hQ hnorm hinj hdim Γ
    (frameConnectionCoefficients_symm cov ht b c x hx) hmetric u v
  rw [hcoordx] at hs
  simpa only [Q, Function.comp_apply, hleft] using hs

end LichnerowiczObata
