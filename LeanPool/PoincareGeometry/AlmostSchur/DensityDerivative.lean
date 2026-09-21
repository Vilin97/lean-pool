/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.MetricDensity
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Differentiating the metric density

Jacobi's determinant formula is derived from the continuous multilinear
determinant, rather than assumed. Its square-root version supplies the local
volume derivative needed to compare density divergence with connection trace.
-/

@[expose] public noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise

namespace AlmostSchur

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The determinant as a continuous multilinear map in its rows. -/
def determinantMultilinear : ContinuousMultilinearMap ℝ (fun _ : ι => ι → ℝ) ℝ :=
  { Matrix.detRowAlternating.toMultilinearMap with
    cont := continuous_id.matrix_det }

theorem determinantMultilinear_apply (G : Matrix ι ι ℝ) :
    determinantMultilinear G = G.det := rfl

/-- Jacobi's formula without an invertibility assumption. -/
theorem determinantMultilinear_linearDeriv (G B : Matrix ι ι ℝ) :
    determinantMultilinear.linearDeriv G B = (G.adjugate * B).trace := by
  erw [ContinuousMultilinearMap.linearDeriv_apply]
  change (∑ i, (G.updateRow i (B i)).det) = _
  calc
    (∑ i, (G.updateRow i (B i)).det) = ∑ i, ∑ j, G.adjugate j i * B i j := by
      apply Finset.sum_congr rfl
      intro i _
      have h := congrFun (Matrix.cramer_eq_adjugate_mulVec G.transpose (B i)) i
      simpa only [Matrix.cramer_transpose_apply, ← Matrix.adjugate_transpose,
        Matrix.mulVec, dotProduct, Matrix.transpose_apply] using! h
    _ = (G.adjugate * B).trace := by
      rw [Finset.sum_comm]
      rfl

variable {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]

theorem contDiff_matrixDensity {n : WithTop ℕ∞} (G : U → Matrix ι ι ℝ)
    (hG : ContDiff ℝ n G) (hpos : ∀ x, 0 < (G x).det) :
    ContDiff ℝ n (fun y => matrixDensity (G y)) := by
  have hd : ContDiff ℝ n (fun y => (G y).det) := by
    exact (determinantMultilinear (ι := ι)).contDiff.comp hG
  exact hd.sqrt (fun x => (hpos x).ne')

/-- Actual derivative of the determinant of a matrix field. -/
theorem fderiv_matrixDet_apply (G : U → Matrix ι ι ℝ) (x v : U)
    (hG : DifferentiableAt ℝ G x) :
    fderiv ℝ (fun y => (G y).det) x v =
      ((G x).adjugate * fderiv ℝ G x v).trace := by
  have h := (determinantMultilinear.hasFDerivAt (G x)).comp x hG.hasFDerivAt
  change fderiv ℝ (determinantMultilinear ∘ G) x v = _
  erw [h.fderiv]
  exact determinantMultilinear_linearDeriv _ _

/-- Derivative of `sqrt(det G)` at a strictly positive determinant. -/
theorem fderiv_matrixDensity_apply (G : U → Matrix ι ι ℝ) (x v : U)
    (hG : DifferentiableAt ℝ G x) (hpos : 0 < (G x).det) :
    fderiv ℝ (fun y => matrixDensity (G y)) x v =
      ((G x).adjugate * fderiv ℝ G x v).trace / (2 * matrixDensity (G x)) := by
  have hd := (determinantMultilinear.hasFDerivAt (G x)).comp x hG.hasFDerivAt
  have hs := (Real.hasDerivAt_sqrt hpos.ne').comp_hasFDerivAt x hd
  change fderiv ℝ (Real.sqrt ∘ (determinantMultilinear ∘ G)) x v = _
  erw [hs.fderiv]
  change (1 / (2 * matrixDensity (G x))) *
    determinantMultilinear.linearDeriv (G x) (fderiv ℝ G x v) = _
  rw [determinantMultilinear_linearDeriv]
  ring

/-- Metric compatibility in coordinates gives the logarithmic density
derivative. The compatibility equation is the usual bilinear product rule;
the determinant and trace consequences are proved here. -/
theorem fderiv_matrixDensity_of_metricCompatibility
    (G : U → Matrix ι ι ℝ) (x v : U) (Γ : Matrix ι ι ℝ)
    (hG : DifferentiableAt ℝ G x) (hpos : 0 < (G x).det)
    (hcompat : fderiv ℝ G x v = Γ.transpose * G x + G x * Γ) :
    fderiv ℝ (fun y => matrixDensity (G y)) x v =
      matrixDensity (G x) * Γ.trace := by
  rw [fderiv_matrixDensity_apply G x v hG hpos, hcompat, Matrix.mul_add,
    Matrix.trace_add]
  have hleft : ((G x).adjugate * (Γ.transpose * G x)).trace =
      (G x).det * Γ.trace := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle, Matrix.mul_adjugate,
      Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, Matrix.trace_transpose]
    rfl
  have hright : ((G x).adjugate * (G x * Γ)).trace = (G x).det * Γ.trace := by
    rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul,
      Matrix.one_mul, Matrix.trace_smul]
    rfl
  rw [hleft, hright]
  have hs : matrixDensity (G x) ^ 2 = (G x).det := Real.sq_sqrt hpos.le
  have hp : matrixDensity (G x) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  rw [← hs]
  field_simp
  ring

end AlmostSchur
