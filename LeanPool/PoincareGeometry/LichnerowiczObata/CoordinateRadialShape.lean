/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.RadialShapeOperator
public import LeanPool.PoincareGeometry.LichnerowiczObata.MetricBilinearRegularity
public import LeanPool.PoincareGeometry.LichnerowiczObata.FlowVariationEquation
public import LeanPool.PoincareGeometry.AlmostSchur.DivergenceCoordinates
public import LeanPool.PoincareGeometry.AlmostSchur.TorsionCoordinates

/-! # Radial shape identities in the actual tangent coordinates -/

@[expose] public noncomputable section
open Bundle FiberBundle Set AlmostSchur
open scoped Manifold ContDiff Topology BigOperators

namespace LichnerowiczObata
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "LC" => (leviCivitaConnection (I := I) (M := M))

omit [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/-- Differentiability of a section gives differentiability of its actual
coordinate vector field at an interior chart point. -/
theorem differentiableAt_coordinateVectorField (X : Π y : M, TM y)
    (c x : M) (hx : x ∈ (chartAt H c).source) (hX : MDiffAt (T% X) x) :
    DifferentiableAt ℝ (coordinateVectorField (I := I) c X) (extChartAt I c x) := by
  classical
  let e := trivializationAt E TM c
  let b := (stdOrthonormalBasis ℝ E).toBasis
  let a := fun i y => e.localFrameCoeff I b i y (X y)
  have heq : coordinateVectorField (I := I) c X =
      fun z => ∑ i, (a i ∘ (extChartAt I c).symm) z • b i := by
    funext z
    exact (localFrameCoeff_sum_coordinates e b X _).symm
  have hx' : x ∈ (extChartAt I c).source := by simpa using hx
  have hi : MDiffAt (extChartAt I c).symm (extChartAt I c x) := by
    simpa only [I.range_eq_univ, mdifferentiableWithinAt_univ] using
      (mdifferentiableWithinAt_extChartAt_symm (I := I) (x := c)
        ((extChartAt I c).map_source hx'))
  rw [heq]
  apply DifferentiableAt.fun_sum
  intro i _
  have ha : MDiffAt (a i) x := mdifferentiableAt_localFrameCoeff b hx hX i
  have hd := mdifferentiableAt_iff_differentiableAt.mp
    (ha.comp_of_eq (extChartAt I c x) hi ((extChartAt I c).left_inv hx'))
  exact hd.smul_const (b i)

omit [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/-- Torsion freeness converts the linearized vector field plus the flow-direction
connection term into the coordinate representation of the covariant derivative. -/
theorem fderiv_coordinateVectorField_add_connection
    (cov : CovariantDerivative I E TM) (ht : cov.torsion = 0)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    (X : Π y : M, TM y) (c x : M) (hx : x ∈ (chartAt H c).source)
    (hX : MDiffAt (T% X) x) (u : E) :
    let e := trivializationAt E TM c
    fderiv ℝ (coordinateVectorField c X) (extChartAt I c x) u +
      frameConnectionCoefficients cov e b x (e.continuousLinearMapAt ℝ x (X x)) u =
      e.continuousLinearMapAt ℝ x (cov X x (e.symmL ℝ x u)) := by
  dsimp only
  rw [frameConnectionCoefficients_symm cov ht b c x hx]
  exact (add_comm _ _).trans (covariantDerivative_chart cov b X c x hx hX u).symm

/-- On angular coordinate vectors, the radial linearization plus its connection
term is exactly multiplication by the spherical shape factor. -/
theorem coordinate_obataRadial_shape {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (hb : ∀ y, -a ≤ f y ∧ f y ≤ a)
    (hH : ∀ (y : M) (v w : TM y), hessian LC f y v w = -K * f y * inner ℝ v w)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    (c x : M) (hx : x ∈ (chartAt H c).source)
    (hreg : -a < f x ∧ f x < a) (u : E)
    (hangular : inner ℝ (gradient (I := I) (obataRadial K a f) x)
      ((trivializationAt E TM c).symmL ℝ x u) = 0) :
    let N := gradient (I := I) (obataRadial K a f)
    let e := trivializationAt E TM c
    fderiv ℝ (coordinateVectorField c N) (extChartAt I c x) u +
      frameConnectionCoefficients LC e b x (e.continuousLinearMapAt ℝ x (N x)) u =
      (Real.sqrt K * (Real.cos (Real.sqrt K * obataRadial K a f x) /
        Real.sin (Real.sqrt K * obataRadial K a f x))) • u := by
  dsimp only
  have hm : -1 < f x / a := (lt_div_iff₀ ha).2 (by nlinarith [hreg.1])
  have hp : f x / a < 1 := (div_lt_iff₀ ha).2 (by simpa using hreg.2)
  have hN := mdifferentiableAt_gradient (contMDiffAt_obataRadial (K := K) (hf x) hm.ne' hp.ne)
  rw [fderiv_coordinateVectorField_add_connection LC leviCivitaConnection_torsion b
    _ c x hx hN, cov_obataRadial_gradient hK ha hf hb hH hreg]
  simp only [hangular, zero_smul, sub_zero, map_smul,
    (trivializationAt E TM c).continuousLinearMapAt_symmL hx]

/-- The actual metric obeys spherical scaling along a radial coordinate solution
and two angular solutions of its linearized equation. -/
theorem hasDerivAt_coordinate_radial_metric {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (hb : ∀ y, -a ≤ f y ∧ f y ≤ a)
    (hH : ∀ (y : M) (v w : TM y), hessian LC f y v w = -K * f y * inner ℝ v w)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    (c x : M) (hx : x ∈ (chartAt H c).source) (hreg : -a < f x ∧ f x < a)
    {z u w : ℝ → E} {t : ℝ} (hz : z t = extChartAt I c x)
    (hd : HasDerivAt z (coordinateVectorField c (gradient (I := I) (obataRadial K a f)) (z t)) t)
    (hu : HasDerivAt u
      (fderiv ℝ (coordinateVectorField c (gradient (I := I) (obataRadial K a f))) (z t) (u t)) t)
    (hw : HasDerivAt w
      (fderiv ℝ (coordinateVectorField c (gradient (I := I) (obataRadial K a f))) (z t) (w t)) t)
    (hTu : inner ℝ (gradient (I := I) (obataRadial K a f) x)
      ((trivializationAt E TM c).symmL ℝ x (u t)) = 0)
    (hTw : inner ℝ (gradient (I := I) (obataRadial K a f) x)
      ((trivializationAt E TM c).symmL ℝ x (w t)) = 0) :
    HasDerivAt (fun s => coordinateMetricBilinear (I := I) c (z s) (u s) (w s))
      (2 * (Real.sqrt K * (Real.cos (Real.sqrt K * obataRadial K a f x) /
        Real.sin (Real.sqrt K * obataRadial K a f x))) *
          coordinateMetricBilinear (I := I) c (z t) (u t) (w t)) t := by
  have he : (extChartAt I c).symm (extChartAt I c x) = x :=
    (extChartAt I c).left_inv (by simpa using hx)
  have hd' : HasDerivAt z ((trivializationAt E TM c).continuousLinearMapAt ℝ x
      (gradient (I := I) (obataRadial K a f) x)) t := by
    have hd0 := hd
    rw [hz] at hd0
    simp only [coordinateVectorField] at hd0
    rw [he] at hd0
    exact hd0
  have hpair := hasDerivAt_coordinateMetric_pairing_connection LC
    leviCivitaConnection_metricCompatible b c x hx hz hd' hu hw
  have hsu := coordinate_obataRadial_shape hK ha hf hb hH b c x hx hreg (u t) hTu
  have hsw := coordinate_obataRadial_shape hK ha hf hb hH b c x hx hreg (w t) hTw
  dsimp only at hpair hsu hsw
  rw [hz] at hu hw hpair ⊢
  rw [hsu, hsw] at hpair
  convert hpair using 1
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

/-- Spatial derivatives of a C2 family of genuine radial solutions obey the
metric evolution equation; their variational ODE is derived, not assumed. -/
theorem hasDerivAt_radial_flow_metric {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (hb : ∀ y, -a ≤ f y ∧ f y ≤ a)
    (hH : ∀ (y : M) (v w : TM y), hessian LC f y v w = -K * f y * inner ℝ v w)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    (c x : M) (hx : x ∈ (chartAt H c).source) (hreg : -a < f x ∧ f x < a)
    {φ : E × ℝ → E} {U : Set (E × ℝ)} (hU : IsOpen U)
    (hφ : ContDiffOn ℝ 2 φ U)
    (hode : ∀ y ∈ U, HasDerivAt (fun s => φ (y.1, s))
      (coordinateVectorField c (gradient (I := I) (obataRadial K a f)) (φ y)) y.2)
    {p : E} {t : ℝ} (hpt : (p, t) ∈ U) (hpoint : φ (p, t) = extChartAt I c x)
    (v w : E)
    (hTv : inner ℝ (gradient (I := I) (obataRadial K a f) x)
      ((trivializationAt E TM c).symmL ℝ x (fderiv ℝ φ (p, t) (v, 0))) = 0)
    (hTw : inner ℝ (gradient (I := I) (obataRadial K a f) x)
      ((trivializationAt E TM c).symmL ℝ x (fderiv ℝ φ (p, t) (w, 0))) = 0) :
    HasDerivAt (fun s => coordinateMetricBilinear (I := I) c (φ (p, s))
      (fderiv ℝ φ (p, s) (v, 0)) (fderiv ℝ φ (p, s) (w, 0)))
      (2 * (Real.sqrt K * (Real.cos (Real.sqrt K * obataRadial K a f x) /
        Real.sin (Real.sqrt K * obataRadial K a f x))) *
          coordinateMetricBilinear (I := I) c (φ (p, t))
            (fderiv ℝ φ (p, t) (v, 0)) (fderiv ℝ φ (p, t) (w, 0))) t := by
  have hm : -1 < f x / a := (lt_div_iff₀ ha).2 (by nlinarith [hreg.1])
  have hp : f x / a < 1 := (div_lt_iff₀ ha).2 (by simpa using hreg.2)
  have hV : DifferentiableAt ℝ (coordinateVectorField c
      (gradient (I := I) (obataRadial K a f))) (φ (p, t)) := by
    rw [hpoint]
    exact differentiableAt_coordinateVectorField _ c x hx
      (mdifferentiableAt_gradient (contMDiffAt_obataRadial (K := K) (hf x) hm.ne' hp.ne))
  exact hasDerivAt_coordinate_radial_metric hK ha hf hb hH b c x hx hreg hpoint
    (hode (p, t) hpt)
    (hasDerivAt_flow_variation hU hφ hode hpt hV v)
    (hasDerivAt_flow_variation hU hφ hode hpt hV w) hTv hTw

end LichnerowiczObata
