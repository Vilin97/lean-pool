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

public import LeanPool.PoincareGeometry.AlmostSchur.LocalIntegration
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Coordinate compatibility of the metric volume density

`sqrt(det G)` transforms by the absolute Jacobian, including orientation-
reversing changes of coordinates. The change-of-variables and integrability
theorems use the actual Fréchet derivative of the coordinate map.
These results do not yet identify this density with intrinsic Hausdorff volume.
-/

@[expose] public noncomputable section
open MeasureTheory MeasureTheory.Measure Set

namespace AlmostSchur

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The volume density of a real Gram matrix. -/
def matrixDensity (G : Matrix ι ι ℝ) : ℝ := Real.sqrt G.det

theorem matrixDensity_nonneg (G : Matrix ι ι ℝ) : 0 ≤ matrixDensity G :=
  Real.sqrt_nonneg _

theorem matrixDensity_pos (G : Matrix ι ι ℝ) (hG : G.PosDef) : 0 < matrixDensity G :=
  Real.sqrt_pos.2 hG.det_pos

/-- Absolute Jacobian transformation; no orientation assumption is needed. -/
theorem matrixDensity_congruence (G P : Matrix ι ι ℝ) :
    matrixDensity (P.transpose * G * P) = |P.det| * matrixDensity G := by
  unfold matrixDensity
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have h : P.det * G.det * P.det = P.det ^ 2 * G.det := by ring
  rw [h, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [NormedSpace ℝ V] in
theorem continuous_matrixDensity (G : V → Matrix ι ι ℝ) (hG : Continuous G) :
    Continuous (fun x => matrixDensity (G x)) := hG.matrix_det.sqrt

/-- Pullback of the coordinate Gram matrix by the actual derivative. -/
def pullbackMetricMatrix (b : Module.Basis ι ℝ V) (F : V → V)
    (G : V → Matrix ι ι ℝ) (x : V) : Matrix ι ι ℝ :=
  let P := LinearMap.toMatrix b b (fderiv ℝ F x).toLinearMap
  P.transpose * G (F x) * P

theorem matrixDensity_pullback (b : Module.Basis ι ℝ V) (F : V → V)
    (G : V → Matrix ι ι ℝ) (x : V) :
    matrixDensity (pullbackMetricMatrix b F G x) =
      |(fderiv ℝ F x).det| * matrixDensity (G (F x)) := by
  rw [pullbackMetricMatrix, matrixDensity_congruence, LinearMap.det_toMatrix]

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  (μ : Measure V) [IsAddHaarMeasure μ]

/-- The density-weighted Bochner integral is unchanged by injective smooth
coordinate substitution, with its pullback Gram matrix computed from `DF`. -/
theorem integral_matrixDensity_changeVariables (b : Module.Basis ι ℝ V)
    (F : V → V) (G : V → Matrix ι ι ℝ) {s : Set V}
    (hs : MeasurableSet s) (hF : ∀ x ∈ s, DifferentiableAt ℝ F x)
    (hinj : InjOn F s) (f : V → ℝ) :
    ∫ y in F '' s, matrixDensity (G y) * f y ∂μ =
      ∫ x in s, matrixDensity (pullbackMetricMatrix b F G x) * f (F x) ∂μ := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul μ hs
    (fun x hx => (hF x hx).hasFDerivAt.hasFDerivWithinAt) hinj]
  simp_rw [matrixDensity_pullback, smul_eq_mul, mul_assoc]

/-- Integrability is transported as well; the Bochner identity above is not
being used to hide a nonintegrable, totalized-zero integral. -/
theorem integrableOn_matrixDensity_changeVariables (b : Module.Basis ι ℝ V)
    (F : V → V) (G : V → Matrix ι ι ℝ) {s : Set V}
    (hs : MeasurableSet s) (hF : ∀ x ∈ s, DifferentiableAt ℝ F x)
    (hinj : InjOn F s) (f : V → ℝ) :
    IntegrableOn (fun y => matrixDensity (G y) * f y) (F '' s) μ ↔
      IntegrableOn (fun x => matrixDensity (pullbackMetricMatrix b F G x) * f (F x)) s μ := by
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul μ hs
    (fun x hx => (hF x hx).hasFDerivAt.hasFDerivWithinAt) hinj]
  simp_rw [matrixDensity_pullback, smul_eq_mul, mul_assoc]

end AlmostSchur
