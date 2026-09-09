/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.InnerProductSpace.LaxMilgram
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Tactic.Abel
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Analysis.Distribution.Sobolev
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Tactic.Linarith
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Tactic.Module
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.ODE.PicardLindelof
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.LiftedGradientSpace

@[expose] public section

noncomputable section

/-!
Pointwise bounded coefficient fields act on genuine L² functions.  Their
pointwise positive quadratic bound supplies the Hilbert-space coercivity used
by the lifted pressure solver.  No multiplication operator is assumed.
-/


namespace EulerLiftedPressure

open MeasureTheory InnerProductSpace EulerCoerciveProjection EulerLiftedGradientSpace
open scoped ENNReal NNReal

section Multiplication

variable {α V : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem coefficientApply_memLp (A : α → V →L[ℝ] V) (hA : AEStronglyMeasurable A μ)
    (C : ℝ≥0) (hbound : ∀ x, ‖A x‖ ≤ C) (f : Lp V 2 μ) :
    MemLp (fun x => A x (f x)) 2 μ := by
  apply (Lp.memLp f).of_le_mul (c := (C : ℝ))
  · exact (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hA.prodMk (Lp.aestronglyMeasurable f))
  · exact Filter.Eventually.of_forall fun x =>
      ((A x).le_opNorm (f x)).trans
        (mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _))

/-- Pointwise bounded coefficient application represented as an L² element. -/
def coefficientApply (A : α → V →L[ℝ] V) (hA : AEStronglyMeasurable A μ)
    (C : ℝ≥0) (hbound : ∀ x, ‖A x‖ ≤ C) (f : Lp V 2 μ) : Lp V 2 μ :=
  (coefficientApply_memLp A hA C hbound f).toLp (fun x => A x (f x))

theorem coefficientApply_ae (A : α → V →L[ℝ] V) (hA : AEStronglyMeasurable A μ)
    (C : ℝ≥0) (hbound : ∀ x, ‖A x‖ ≤ C) (f : Lp V 2 μ) :
    coefficientApply A hA C hbound f =ᵐ[μ] fun x => A x (f x) :=
  (coefficientApply_memLp A hA C hbound f).coeFn_toLp

/-- The linear map induced by pointwise coefficient multiplication. -/
def coefficientLinearMap (A : α → V →L[ℝ] V) (hA : AEStronglyMeasurable A μ)
    (C : ℝ≥0) (hbound : ∀ x, ‖A x‖ ≤ C) : Lp V 2 μ →ₗ[ℝ] Lp V 2 μ where
  toFun := coefficientApply A hA C hbound
  map_add' f g := by
    apply Lp.ext
    filter_upwards [coefficientApply_ae A hA C hbound (f + g),
      coefficientApply_ae A hA C hbound f, coefficientApply_ae A hA C hbound g,
      Lp.coeFn_add f g,
      Lp.coeFn_add (coefficientApply A hA C hbound f) (coefficientApply A hA C hbound g)]
      with x hx₁ hx₂ hx₃ hx₄ hx₅
    simp only [Pi.add_apply] at hx₄ hx₅
    rw [hx₁, hx₅, hx₂, hx₃, hx₄, map_add]
  map_smul' r f := by
    simp only [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [coefficientApply_ae A hA C hbound (r • f),
      coefficientApply_ae A hA C hbound f, Lp.coeFn_smul r f,
      Lp.coeFn_smul r (coefficientApply A hA C hbound f)] with x hx₁ hx₂ hx₃ hx₄
    simp only [Pi.smul_apply] at hx₃ hx₄
    rw [hx₁, hx₄, hx₂, hx₃, map_smul]

theorem coefficientApply_norm_le (A : α → V →L[ℝ] V) (hA : AEStronglyMeasurable A μ)
    (C : ℝ≥0) (hbound : ∀ x, ‖A x‖ ≤ C) (f : Lp V 2 μ) :
    ‖coefficientApply A hA C hbound f‖ ≤ C * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [coefficientApply_ae A hA C hbound f] with x hx
  rw [hx]
  exact ((A x).le_opNorm (f x)).trans
    (mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _))

/-- The bounded operator induced by the actual coefficient field. -/
def coefficientOperator (A : α → V →L[ℝ] V) (hA : AEStronglyMeasurable A μ)
    (C : ℝ≥0) (hbound : ∀ x, ‖A x‖ ≤ C) : Lp V 2 μ →L[ℝ] Lp V 2 μ :=
  (coefficientLinearMap A hA C hbound).mkContinuous C
    (coefficientApply_norm_le A hA C hbound)

theorem coefficientOperator_ae (A : α → V →L[ℝ] V) (hA : AEStronglyMeasurable A μ)
    (C : ℝ≥0) (hbound : ∀ x, ‖A x‖ ≤ C) (f : Lp V 2 μ) :
    coefficientOperator A hA C hbound f =ᵐ[μ] fun x => A x (f x) :=
  coefficientApply_ae A hA C hbound f

theorem coefficientOperator_norm_le (A : α → V →L[ℝ] V) (hA : AEStronglyMeasurable A μ)
    (C : ℝ≥0) (hbound : ∀ x, ‖A x‖ ≤ C) :
    ‖coefficientOperator A hA C hbound‖ ≤ C := by
  exact ContinuousLinearMap.opNorm_le_bound _ C.coe_nonneg
    (coefficientApply_norm_le A hA C hbound)

/-- Pointwise coercivity yields the actual integral L² coercivity. -/
theorem coefficientOperator_coercive (A : α → V →L[ℝ] V) (hA : AEStronglyMeasurable A μ)
    (C : ℝ≥0) (hbound : ∀ x, ‖A x‖ ≤ C) (c : ℝ)
    (hpositive : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A x v, v⟫_ℝ) (f : Lp V 2 μ) :
    c * ‖f‖ ^ 2 ≤ ⟪coefficientOperator A hA C hbound f, f⟫_ℝ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def, L2.inner_def, ← integral_const_mul]
  apply integral_mono_ae ((L2.integrable_inner f f).const_mul c)
    (L2.integrable_inner (coefficientOperator A hA C hbound f) f)
  filter_upwards [coefficientOperator_ae A hA C hbound f] with x hx
  rw [hx, real_inner_self_eq_norm_sq]
  exact hpositive x (f x)

theorem coefficientOperator_comp_apply (A B : α → V →L[ℝ] V)
    (hA : AEStronglyMeasurable A μ) (hB : AEStronglyMeasurable B μ)
    (C D : ℝ≥0) (hA_bound : ∀ x, ‖A x‖ ≤ C) (hB_bound : ∀ x, ‖B x‖ ≤ D)
    (hAB : ∀ x v, A x (B x v) = v) (f : Lp V 2 μ) :
    coefficientOperator A hA C hA_bound (coefficientOperator B hB D hB_bound f) = f := by
  apply Lp.ext
  filter_upwards [coefficientOperator_ae A hA C hA_bound
      (coefficientOperator B hB D hB_bound f),
    coefficientOperator_ae B hB D hB_bound f] with x hx₁ hx₂
  rw [hx₁, hx₂, hAB]

/-- Pointwise symmetry gives symmetry of the actual L² multiplication operator. -/
theorem coefficientOperator_inner_swap (A : α → V →L[ℝ] V)
    (hA : AEStronglyMeasurable A μ) (C : ℝ≥0) (hbound : ∀ x, ‖A x‖ ≤ C)
    (hsym : ∀ x v w, ⟪A x v, w⟫_ℝ = ⟪v, A x w⟫_ℝ) (f g : Lp V 2 μ) :
    ⟪coefficientOperator A hA C hbound f, g⟫_ℝ =
      ⟪f, coefficientOperator A hA C hbound g⟫_ℝ := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coefficientOperator_ae A hA C hbound f,
    coefficientOperator_ae A hA C hbound g] with x hx₁ hx₂
  rw [hx₁, hx₂, hsym]

end Multiplication

section LiftedSolver

variable (period : ℝ) [Fact (0 < period)]

theorem existsUnique_lifted_pressure (κ : ℝ) (m : Vector3)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hA : AEStronglyMeasurable A (liftMeasure period))
    (C : ℝ≥0) (hbound : ∀ x, ‖A x‖ ≤ C) (c : ℝ) (hc : 0 < c)
    (hpositive : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A x v, v⟫_ℝ) (f : LiftL2 period) :
    ∃! p : gradientSpace period κ m,
      (gradientSpace period κ m).orthogonalProjectionOnto
        (coefficientOperator A hA C hbound (p : LiftL2 period)) =
      (gradientSpace period κ m).orthogonalProjectionOnto f :=
  existsUnique_projected_solution (gradientSpace period κ m)
    (coefficientOperator A hA C hbound) c hc
    (coefficientOperator_coercive A hA C hbound c hpositive) f

theorem exists_lifted_pressure_with_bound (κ : ℝ) (m : Vector3)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hA : AEStronglyMeasurable A (liftMeasure period))
    (C : ℝ≥0) (hbound : ∀ x, ‖A x‖ ≤ C) (c : ℝ) (hc : 0 < c)
    (hpositive : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A x v, v⟫_ℝ) (f : LiftL2 period) :
    ∃ p : gradientSpace period κ m,
      (gradientSpace period κ m).orthogonalProjectionOnto
        (coefficientOperator A hA C hbound (p : LiftL2 period)) =
        (gradientSpace period κ m).orthogonalProjectionOnto f ∧
      ‖p‖ ≤ c⁻¹ * ‖f‖ := by
  let hcoercive := coefficientOperator_coercive A hA C hbound c hpositive
  refine ⟨pressureSolver (gradientSpace period κ m)
    (coefficientOperator A hA C hbound) c hc hcoercive f, ?_, ?_⟩
  · exact pressureSolver_equation (gradientSpace period κ m)
      (coefficientOperator A hA C hbound) c hc hcoercive f
  · exact pressureSolver_apply_norm_le (gradientSpace period κ m)
      (coefficientOperator A hA C hbound) c hc hcoercive f

/-- Exact metric-pressure cancellation for pointwise inverse symmetric coefficient fields. -/
theorem metric_pressure_cancellation (κ : ℝ) (m : Vector3)
    (K G : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hK : AEStronglyMeasurable K (liftMeasure period))
    (hG : AEStronglyMeasurable G (liftMeasure period))
    (C D : ℝ≥0) (hK_bound : ∀ x, ‖K x‖ ≤ C) (hG_bound : ∀ x, ‖G x‖ ≤ D)
    (hK_sym : ∀ x v w, ⟪K x v, w⟫_ℝ = ⟪v, K x w⟫_ℝ)
    (hKG : ∀ x v, K x (G x v) = v) {e p : LiftL2 period}
    (he : e ∈ divergenceFreeSpace period κ m) (hp : p ∈ gradientSpace period κ m) :
    ⟪coefficientOperator K hK C hK_bound e,
      coefficientOperator G hG D hG_bound p⟫_ℝ = 0 := by
  rw [coefficientOperator_inner_swap K hK C hK_bound hK_sym,
    coefficientOperator_comp_apply K G hK hG C D hK_bound hG_bound hKG]
  rw [real_inner_comm]
  exact pressure_pairing_zero period κ m hp he

end LiftedSolver

end EulerLiftedPressure
