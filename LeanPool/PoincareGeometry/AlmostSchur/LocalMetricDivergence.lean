/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.DensityDerivative

/-!
# Metric-connection divergence in coordinates

For the coordinate connection `∇_u X = DX(u) + Γ(u,X)`, metric compatibility
and zero torsion imply that its trace is exactly the density divergence for
`sqrt(det G) dx`. Thus the local Green identity uses the connection trace,
not a separately assumed integration identity. Global chart assembly remains
separate work.
-/

@[expose] public noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped Matrix.Norms.Elementwise

namespace AlmostSchur

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Trace of the coordinate covariant derivative `DX + Γ(·,X)`. -/
def localConnectionDivergence (Γ : V → V →L[ℝ] V →L[ℝ] V)
    (X : V → V) (x : V) : ℝ :=
  LinearMap.trace ℝ V (fderiv ℝ X x + (Γ x).flip (X x)).toLinearMap

/-- Coordinate form of metric compatibility for a connection matrix.
`G` is the Gram matrix in the fixed background basis, not an abstract scalar
substitute for a metric. -/
def localMetricCompatible (b : Module.Basis ι ℝ V) (G : V → Matrix ι ι ℝ)
    (Γ : V → V →L[ℝ] V →L[ℝ] V) (x : V) : Prop :=
  ∀ v, let A := LinearMap.toMatrix b b (Γ x v).toLinearMap
    fderiv ℝ G x v = A.transpose * G x + G x * A

omit [FiniteDimensional ℝ V] in
theorem localConnectionDivergence_eq_of_torsionFree
    (Γ : V → V →L[ℝ] V →L[ℝ] V) (X : V → V) (x : V)
    (htorsion : ∀ u v, Γ x u v = Γ x v u) :
    localConnectionDivergence Γ X x = localDivergence X x +
      LinearMap.trace ℝ V (Γ x (X x)).toLinearMap := by
  have heq : (Γ x).flip (X x) = Γ x (X x) := by
    ext v
    exact htorsion v (X x)
  simp [localConnectionDivergence, heq, localDivergence]

/-- A metric-compatible torsion-free connection preserves the metric density:
its actual trace equals `ρ⁻¹ div(ρX)`. -/
theorem localConnectionDivergence_eq_density
    (b : Module.Basis ι ℝ V) (G : V → Matrix ι ι ℝ)
    (Γ : V → V →L[ℝ] V →L[ℝ] V) (X : V → V) (x : V)
    (hG : DifferentiableAt ℝ G x) (hpos : (G x).PosDef)
    (hX : DifferentiableAt ℝ X x)
    (hcompat : localMetricCompatible b G Γ x)
    (htorsion : ∀ u v, Γ x u v = Γ x v u) :
    localConnectionDivergence Γ X x =
      localDensityDivergence (fun y => matrixDensity (G y)) X x := by
  have hd : DifferentiableAt ℝ (fun y => (G y).det) x :=
    ((determinantMultilinear (ι := ι)).hasFDerivAt (G x)).differentiableAt.comp x hG
  have hρ : DifferentiableAt ℝ (fun y => matrixDensity (G y)) x :=
    hd.sqrt hpos.det_pos.ne'
  have hder := fderiv_matrixDensity_of_metricCompatibility G x (X x)
    (LinearMap.toMatrix b b (Γ x (X x)).toLinearMap) hG hpos.det_pos (hcompat (X x))
  rw [← LinearMap.trace_eq_matrix_trace ℝ b] at hder
  rw [localConnectionDivergence_eq_of_torsionFree Γ X x htorsion,
    localDensityDivergence_eq _ X x hρ hX (matrixDensity_pos _ hpos), hder]
  field_simp [(matrixDensity_pos _ hpos).ne']

variable [MeasurableSpace V] [BorelSpace V] {μ : Measure V} [IsAddHaarMeasure μ]

/-- Local geometric Green identity for a positive-definite C1 metric and
its metric-compatible torsion-free connection, with compactly supported flux. -/
theorem integral_mul_localConnectionDivergence
    (b : Module.Basis ι ℝ V) (G : V → Matrix ι ι ℝ)
    (Γ : V → V →L[ℝ] V →L[ℝ] V) (f : V → ℝ) (X : V → V)
    (hG : ContDiff ℝ 1 G) (hpos : ∀ x, (G x).PosDef)
    (hf : ContDiff ℝ 1 f) (hX : ContDiff ℝ 1 X) (hc : HasCompactSupport X)
    (hcompat : ∀ x, localMetricCompatible b G Γ x)
    (htorsion : ∀ x u v, Γ x u v = Γ x v u) :
    ∫ x, f x * localConnectionDivergence Γ X x
        ∂localDensityMeasure μ (fun y => matrixDensity (G y)) =
      -∫ x, fderiv ℝ f x (X x)
        ∂localDensityMeasure μ (fun y => matrixDensity (G y)) := by
  have heq (x : V) := localConnectionDivergence_eq_density b G Γ X x
    (hG.differentiable (by norm_num) x) (hpos x)
    (hX.differentiable (by norm_num) x) (hcompat x) (htorsion x)
  simp_rw [heq]
  exact integral_mul_localDensityDivergence _ f X
    (contDiff_matrixDensity G hG (fun x => (hpos x).det_pos))
    (fun x => matrixDensity_pos _ (hpos x)) hf hX hc

end AlmostSchur
