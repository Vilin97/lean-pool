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
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.TransportDerivatives

@[expose] public section

noncomputable section

/-!
Spatial pressure regularity in the genuine lifted L² space.  Coefficient
translations are actual pointwise translations, and pressure translation
covariance follows from the uniquely constructed projected equation.
-/


namespace EulerPressureSpatialRegularity

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerLiftedPressure
  EulerCoerciveProjection EulerInverseRegularity EulerMetricTransport EulerTransportDerivatives
open scoped ContDiff ENNReal NNReal Topology

/-- The existing Mathlib normed group instance for matrix coefficients, named to keep inference shallow. -/
local instance coefficientValueNormedGroup : NormedAddCommGroup (Vector3 →L[ℝ] Vector3) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- The existing Mathlib real normed-space instance for matrix coefficients. -/
local instance coefficientValueNormedSpace : NormedSpace ℝ (Vector3 →L[ℝ] Vector3) :=
  ContinuousLinearMap.toNormedSpace

/-- The existing Mathlib normed group instance for first coefficient derivatives. -/
local instance coefficientFirstNormedGroup :
    NormedAddCommGroup (LiftTangent →L[ℝ] Vector3 →L[ℝ] Vector3) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- The existing Mathlib real normed-space instance for first coefficient derivatives. -/
local instance coefficientFirstNormedSpace :
    NormedSpace ℝ (LiftTangent →L[ℝ] Vector3 →L[ℝ] Vector3) :=
  ContinuousLinearMap.toNormedSpace

section CoefficientDifferentiation

variable {α V : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem coefficientOperator_remainder_norm
    (A B D : α → V →L[ℝ] V)
    (hA : AEStronglyMeasurable A μ) (hB : AEStronglyMeasurable B μ)
    (hD : AEStronglyMeasurable D μ) (CA CB CD R : ℝ≥0)
    (hAb : ∀ x, ‖A x‖ ≤ CA) (hBb : ∀ x, ‖B x‖ ≤ CB) (hDb : ∀ x, ‖D x‖ ≤ CD)
    (t : ℝ) (hR : ∀ x, ‖A x - B x - t • D x‖ ≤ R) :
    ‖coefficientOperator A hA CA hAb - coefficientOperator B hB CB hBb -
      t • coefficientOperator D hD CD hDb‖ ≤ R := by
  apply ContinuousLinearMap.opNorm_le_bound _ R.coe_nonneg
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  let a := coefficientOperator A hA CA hAb f
  let b := coefficientOperator B hB CB hBb f
  let d := coefficientOperator D hD CD hDb f
  filter_upwards [coefficientOperator_ae A hA CA hAb f,
    coefficientOperator_ae B hB CB hBb f, coefficientOperator_ae D hD CD hDb f,
    Lp.coeFn_sub a b, Lp.coeFn_smul t d, Lp.coeFn_sub (a - b) (t • d)]
    with x ha hb hd hab htd hsub
  change ‖((a - b) - t • d) x‖ ≤ (R : ℝ) * ‖f x‖
  simp only [Pi.sub_apply, Pi.smul_apply] at hab htd hsub
  rw [hsub, hab, htd]
  change ‖a x - b x - t • d x‖ ≤ _
  rw [ha, hb, hd]
  change ‖(A x - B x - t • D x) (f x)‖ ≤ _
  exact ((A x - B x - t • D x).le_opNorm (f x)).trans
    (mul_le_mul_of_nonneg_right (hR x) (norm_nonneg _))

theorem uniform_derivative_remainder {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f f' : ℝ → W) (hf : ∀ s, HasDerivAt f (f' s) s) (L : ℝ≥0)
    (hL : ∀ s, ‖f' s - f' 0‖ ≤ L * |s|) (t : ℝ) :
    ‖f t - f 0 - t • f' 0‖ ≤ L * |t| ^ 2 := by
  have hd : ∀ s, HasDerivAt (fun u => f u - u • f' 0) (f' s - f' 0) s := by
    intro s
    convert (hf s).sub ((hasDerivAt_id s).smul_const (f' 0)) using 1
    · rfl
    · simp
  have hb : ∀ s ∈ Set.uIcc (0 : ℝ) t, ‖f' s - f' 0‖ ≤ (L : ℝ) * |t| := by
    intro s hs
    exact (hL s).trans (mul_le_mul_of_nonneg_left
      (by simpa using Set.abs_sub_left_of_mem_uIcc hs) L.coe_nonneg)
  have hm := (convex_uIcc (0 : ℝ) t).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s _ => (hd s).hasDerivWithinAt) hb Set.left_mem_uIcc Set.right_mem_uIcc
  simp only [zero_smul, sub_zero, Real.norm_eq_abs] at hm
  calc
    ‖f t - f 0 - t • f' 0‖ = ‖f t - t • f' 0 - f 0‖ := by congr 1; abel
    _ ≤ (L : ℝ) * |t| * |t| := hm
    _ = _ := by ring

theorem coefficientOperator_hasDerivAt
    (A A' : ℝ → α → V →L[ℝ] V)
    (hA : ∀ t, AEStronglyMeasurable (A t) μ)
    (hA' : AEStronglyMeasurable (A' 0) μ)
    (C D L : ℝ≥0) (hAb : ∀ t x, ‖A t x‖ ≤ C) (hDb : ∀ x, ‖A' 0 x‖ ≤ D)
    (hder : ∀ t x, HasDerivAt (fun s => A s x) (A' t x) t)
    (hLip : ∀ t x, ‖A' t x - A' 0 x‖ ≤ L * |t|) :
    HasDerivAt (fun t => coefficientOperator (A t) (hA t) C (hAb t))
      (coefficientOperator (A' 0) hA' D hDb) 0 := by
  apply (hasDerivAt_iff_tendsto
    (f := fun t => coefficientOperator (A t) (hA t) C (hAb t))
    (f' := coefficientOperator (A' 0) hA' D hDb) (x := (0 : ℝ))).mpr
  apply squeeze_zero
  · intro t
    positivity
  · intro t
    let R : ℝ≥0 := ⟨(L : ℝ) * |t| ^ 2, mul_nonneg L.coe_nonneg (sq_nonneg _)⟩
    have hr := coefficientOperator_remainder_norm (A t) (A 0) (A' 0)
      (hA t) (hA 0) hA' C C D R
      (hAb t) (hAb 0) hDb t
      (fun x => uniform_derivative_remainder (fun s => A s x) (fun s => A' s x)
        (fun s => hder s x) L (fun s => hLip s x) t)
    change ‖coefficientOperator (A t) (hA t) C (hAb t) -
      coefficientOperator (A 0) (hA 0) C (hAb 0) -
      t • coefficientOperator (A' 0) hA' D hDb‖ ≤ (L : ℝ) * |t| ^ 2 at hr
    simp only [sub_zero]
    calc
      _ ≤ ‖t‖⁻¹ * ((L : ℝ) * |t| ^ 2) :=
        mul_le_mul_of_nonneg_left hr (inv_nonneg.2 (norm_nonneg _))
      _ ≤ (L : ℝ) * |t| := by
        by_cases ht : t = 0
        · simp [ht]
        · rw [Real.norm_eq_abs]
          have ha : |t| ≠ 0 := abs_ne_zero.mpr ht
          field_simp
          exact le_rfl
  · simpa only [Pi.mul_def, abs_zero, mul_zero] using
      (continuous_const.mul continuous_abs).tendsto (0 : ℝ)

end CoefficientDifferentiation

theorem directionalDerivative_line_lipschitz
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : V → W) (hf : ContDiff ℝ ∞ f) (M : ℝ≥0)
    (hDD : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M) (a : V) (t : ℝ) :
    ‖fderiv ℝ f (t • a) a - fderiv ℝ f 0 a‖ ≤
      (M : ℝ) * ‖a‖ ^ 2 * |t| := by
  have hd : ∀ s : ℝ, HasDerivAt (fun u : ℝ => fderiv ℝ f (u • a) a)
      ((fderiv ℝ (fderiv ℝ f) (s • a) a) a) s := by
    intro s
    have hdf := (((hf.fderiv_right (m := ∞) (by simp)).differentiable
      (by simp)) (s • a)).hasFDerivAt
    have hline := hdf.comp_hasDerivAt s ((hasDerivAt_id s).smul_const a)
    simpa using hline.clm_apply (hasDerivAt_const s a)
  have hb : ∀ s ∈ (Set.univ : Set ℝ),
      ‖(fderiv ℝ (fderiv ℝ f) (s • a) a) a‖ ≤ (M : ℝ) * ‖a‖ ^ 2 := by
    intro s _
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ f) (s • a) a‖ * ‖a‖ :=
        (fderiv ℝ (fderiv ℝ f) (s • a) a).le_opNorm a
      _ ≤ (‖fderiv ℝ (fderiv ℝ f) (s • a)‖ * ‖a‖) * ‖a‖ :=
        mul_le_mul_of_nonneg_right
          ((fderiv ℝ (fderiv ℝ f) (s • a)).le_opNorm a) (norm_nonneg _)
      _ ≤ ((M : ℝ) * ‖a‖) * ‖a‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hDD _) (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by ring
  have hm := (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s _ => (hd s).hasDerivWithinAt) hb (Set.mem_univ (0 : ℝ)) (Set.mem_univ t)
  simpa only [zero_smul, sub_zero, Real.norm_eq_abs] using hm

section LiftedTranslation

variable (period : ℝ) [Fact (0 < period)]

/-- Pointwise coefficient translation on the actual cylinder. -/
def translatedCoefficient (a : LiftDomain period)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3) (x : LiftDomain period) := A (x + a)

theorem translatedCoefficient_measurable (a : LiftDomain period)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hA : AEStronglyMeasurable A (liftMeasure period)) :
    AEStronglyMeasurable (translatedCoefficient period a A) (liftMeasure period) :=
  hA.comp_measurePreserving (measurePreserving_translation period a)

/-- The one-parameter spatial/angular translation determined by a covering-space direction. -/
def translationPath (a : LiftTangent) (t : ℝ) : LiftDomain period :=
  coveringMap period (t • a)

omit [Fact (0 < period)] in
@[simp]
theorem translationPath_zero (a : LiftTangent) : translationPath period a 0 = 0 := by
  simp [translationPath, coveringMap]

/-- The actual directional derivative of the translated coefficient field. -/
def translatedCoefficientDerivative (a : LiftTangent)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3) (t : ℝ) (x : LiftDomain period) :=
  fderiv ℝ (localFieldLift period A x) (t • a) a

omit [Fact (0 < period)] in
theorem translatedCoefficient_path (a : LiftTangent)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3) (t : ℝ) (x : LiftDomain period) :
    translatedCoefficient period (translationPath period a t) A x =
      localFieldLift period A x (t • a) := rfl

omit [Fact (0 < period)] in
theorem translatedCoefficient_hasDerivAt (a : LiftTangent)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hA : ∀ x, ContDiff ℝ ∞ (localFieldLift period A x)) (t : ℝ) (x : LiftDomain period) :
    HasDerivAt (fun s => translatedCoefficient period (translationPath period a s) A x)
      (translatedCoefficientDerivative period a A t x) t := by
  have hd := (((hA x).differentiable (by simp)) (t • a)).hasFDerivAt
  simpa only [translatedCoefficient_path, translatedCoefficientDerivative, one_smul,
    Function.comp_def, id_eq] using
    hd.comp_hasDerivAt t ((hasDerivAt_id t).smul_const a)

theorem translatedCoefficientDerivative_measurable (a : LiftTangent)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hA : ∀ x, ContDiff ℝ ∞ (localFieldLift period A x)) :
    AEStronglyMeasurable (translatedCoefficientDerivative period a A 0) (liftMeasure period) := by
  have hc := (localFDeriv_continuous period A hA).clm_apply (g := fun _ => a) continuous_const
  change AEStronglyMeasurable (fun x => fderiv ℝ (localFieldLift period A x) (0 • a) a)
    (liftMeasure period)
  simpa only [zero_smul] using hc.aestronglyMeasurable (μ := liftMeasure period)

omit [Fact (0 < period)] in
theorem translatedCoefficientDerivative_bound (a : LiftTangent)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3) (D : ℝ≥0)
    (hD : ∀ x, ‖fderiv ℝ (localFieldLift period A x) 0‖ ≤ D) (x : LiftDomain period) :
    ‖translatedCoefficientDerivative period a A 0 x‖ ≤ (D : ℝ) * ‖a‖ := by
  simp only [translatedCoefficientDerivative, zero_smul]
  exact ((fderiv ℝ (localFieldLift period A x) 0).le_opNorm a).trans
    (mul_le_mul_of_nonneg_right (hD x) (norm_nonneg _))

omit [Fact (0 < period)] in
theorem translatedCoefficientDerivative_lipschitz (a : LiftTangent)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hA : ∀ x, ContDiff ℝ ∞ (localFieldLift period A x)) (M : ℝ≥0)
    (hDD : ∀ x y, ‖fderiv ℝ (fderiv ℝ (localFieldLift period A x)) y‖ ≤ M)
    (t : ℝ) (x : LiftDomain period) :
    ‖translatedCoefficientDerivative period a A t x -
      translatedCoefficientDerivative period a A 0 x‖ ≤ (M : ℝ) * ‖a‖ ^ 2 * |t| := by
  simpa only [translatedCoefficientDerivative, zero_smul] using
    directionalDerivative_line_lipschitz (localFieldLift period A x) (hA x) M (hDD x) a t

theorem coefficientOperator_translation (a : LiftDomain period)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hA : AEStronglyMeasurable A (liftMeasure period))
    (C : ℝ≥0) (hAb : ∀ x, ‖A x‖ ≤ C) (f : LiftL2 period) :
    translation period a (coefficientOperator A hA C hAb f) =
      coefficientOperator (translatedCoefficient period a A)
        (translatedCoefficient_measurable period a A hA) C (fun x => hAb (x + a))
        (translation period a f) := by
  apply Lp.ext
  filter_upwards [translation_ae period a (coefficientOperator A hA C hAb f),
    (measurePreserving_translation period a).quasiMeasurePreserving.ae
      (coefficientOperator_ae A hA C hAb f),
    coefficientOperator_ae (translatedCoefficient period a A)
      (translatedCoefficient_measurable period a A hA) C (fun x => hAb (x + a))
      (translation period a f), translation_ae period a f] with x hx₁ hx₂ hx₃ hx₄
  rw [hx₁, hx₂, hx₃, hx₄]
  rfl

/-- The concrete coercive pressure solution, viewed in ambient L². -/
def liftedPressure (κ : ℝ) (m : Vector3)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hA : AEStronglyMeasurable A (liftMeasure period))
    (C : ℝ≥0) (hAb : ∀ x, ‖A x‖ ≤ C) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A x v, v⟫_ℝ) (f : LiftL2 period) : LiftL2 period :=
  pressureSolver (gradientSpace period κ m) (coefficientOperator A hA C hAb) c hc
    (coefficientOperator_coercive A hA C hAb c hpos) f

theorem liftedPressure_mem (κ : ℝ) (m : Vector3)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hA : AEStronglyMeasurable A (liftMeasure period))
    (C : ℝ≥0) (hAb : ∀ x, ‖A x‖ ≤ C) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A x v, v⟫_ℝ) (f : LiftL2 period) :
    liftedPressure period κ m A hA C hAb c hc hpos f ∈ gradientSpace period κ m :=
  (pressureSolver (gradientSpace period κ m) (coefficientOperator A hA C hAb) c hc
    (coefficientOperator_coercive A hA C hAb c hpos) f).property

theorem liftedPressure_equation (κ : ℝ) (m : Vector3)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hA : AEStronglyMeasurable A (liftMeasure period))
    (C : ℝ≥0) (hAb : ∀ x, ‖A x‖ ≤ C) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A x v, v⟫_ℝ) (f : LiftL2 period) :
    gradientProjection period κ m
      (coefficientOperator A hA C hAb (liftedPressure period κ m A hA C hAb c hc hpos f)) =
      gradientProjection period κ m f := by
  exact congrArg Subtype.val (pressureSolver_equation (gradientSpace period κ m)
    (coefficientOperator A hA C hAb) c hc
    (coefficientOperator_coercive A hA C hAb c hpos) f)

theorem liftedPressure_unique (κ : ℝ) (m : Vector3)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hA : AEStronglyMeasurable A (liftMeasure period))
    (C : ℝ≥0) (hAb : ∀ x, ‖A x‖ ≤ C) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A x v, v⟫_ℝ) (f p : LiftL2 period)
    (hp : p ∈ gradientSpace period κ m)
    (heq : gradientProjection period κ m (coefficientOperator A hA C hAb p) =
      gradientProjection period κ m f) :
    p = liftedPressure period κ m A hA C hAb c hc hpos f := by
  let S := gradientSpace period κ m
  let G := coefficientOperator A hA C hAb
  let hG := coefficientOperator_coercive A hA C hAb c hpos
  have hsub : (⟨p, hp⟩ : S) = pressureSolver S G c hc hG f := by
    apply (coerciveEquiv (projectedOperator S G) c hc
      (projectedOperator_coercive S G c hG)).injective
    simp only [coerciveEquiv_apply]
    change S.orthogonalProjectionOnto (G p) =
      S.orthogonalProjectionOnto (G (pressureSolver S G c hc hG f : LiftL2 period))
    rw [pressureSolver_equation]
    exact Subtype.ext heq
  exact congrArg Subtype.val hsub

theorem liftedPressure_translation (κ : ℝ) (m : Vector3) (a : LiftDomain period)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hA : AEStronglyMeasurable A (liftMeasure period))
    (C : ℝ≥0) (hAb : ∀ x, ‖A x‖ ≤ C) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A x v, v⟫_ℝ) (f : LiftL2 period) :
    translation period a (liftedPressure period κ m A hA C hAb c hc hpos f) =
      liftedPressure period κ m (translatedCoefficient period a A)
        (translatedCoefficient_measurable period a A hA) C (fun x => hAb (x + a)) c hc
        (fun x v => hpos (x + a) v) (translation period a f) := by
  apply liftedPressure_unique period κ m (translatedCoefficient period a A)
    (translatedCoefficient_measurable period a A hA) C (fun x => hAb (x + a)) c hc
    (fun x v => hpos (x + a) v)
  · exact gradientSpace_translation_mem period κ m a
      (liftedPressure_mem period κ m A hA C hAb c hc hpos f)
  · rw [← coefficientOperator_translation period a A hA C hAb,
      ← gradientProjection_translation,
      liftedPressure_equation, gradientProjection_translation]

theorem liftedPressure_hasDerivAt (κ : ℝ) (m : Vector3)
    (A A' : ℝ → LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hA : ∀ t, AEStronglyMeasurable (A t) (liftMeasure period))
    (hA' : AEStronglyMeasurable (A' 0) (liftMeasure period))
    (C D L : ℝ≥0) (hAb : ∀ t x, ‖A t x‖ ≤ C) (hDb : ∀ x, ‖A' 0 x‖ ≤ D)
    (hder : ∀ t x, HasDerivAt (fun s => A s x) (A' t x) t)
    (hLip : ∀ t x, ‖A' t x - A' 0 x‖ ≤ L * |t|)
    (c : ℝ) (hc : 0 < c) (hpos : ∀ t x v, c * ‖v‖ ^ 2 ≤ ⟪A t x v, v⟫_ℝ)
    (f : ℝ → LiftL2 period) (f' : LiftL2 period) (hf : HasDerivAt f f' 0) :
    HasDerivAt (fun t => liftedPressure period κ m (A t) (hA t) C (hAb t) c hc
      (hpos t) (f t))
      (liftedPressure period κ m (A 0) (hA 0) C (hAb 0) c hc (hpos 0)
        (f' - coefficientOperator (A' 0) hA' D hDb
          (liftedPressure period κ m (A 0) (hA 0) C (hAb 0) c hc (hpos 0) (f 0)))) 0 := by
  let S := gradientSpace period κ m
  let G := fun t => coefficientOperator (A t) (hA t) C (hAb t)
  let G' := coefficientOperator (A' 0) hA' D hDb
  have hG : ∀ t u, c * ‖u‖ ^ 2 ≤ ⟪G t u, u⟫_ℝ :=
    fun t => coefficientOperator_coercive (A t) (hA t) C (hAb t) c (hpos t)
  have hGder : HasDerivAt G G' 0 :=
    coefficientOperator_hasDerivAt A A' hA hA' C D L hAb hDb hder hLip
  have hsol := hasDerivAt_coerciveSolution (fun t => projectedOperator S (G t)) c hc
    (fun t => projectedOperator_coercive S (G t) c (hG t))
    (fun t => S.orthogonalProjectionOnto (f t)) 0 (projectedOperator S G')
    (S.orthogonalProjectionOnto f')
    (hasDerivAt_projectedOperator S G 0 G' hGder)
    (S.orthogonalProjectionOnto.hasFDerivAt.comp_hasDerivAt 0 hf)
  have hval := S.subtypeL.hasFDerivAt.comp_hasDerivAt 0 hsol
  convert hval using 1
  · rfl
  · rfl
  · rfl
  · simp [liftedPressure, pressureSolver, projectedInverse, projectedOperator,
      S, G, G', ContinuousLinearMap.comp_apply, map_sub]

theorem pressure_translation_hasDerivAt (κ : ℝ) (m : Vector3) (a : LiftTangent)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hA : AEStronglyMeasurable A (liftMeasure period))
    (hAs : ∀ x, ContDiff ℝ ∞ (localFieldLift period A x))
    (C D M : ℝ≥0) (hAb : ∀ x, ‖A x‖ ≤ C)
    (hDA : ∀ x, ‖fderiv ℝ (localFieldLift period A x) 0‖ ≤ D)
    (hDDA : ∀ x y, ‖fderiv ℝ (fderiv ℝ (localFieldLift period A x)) y‖ ≤ M)
    (c : ℝ) (hc : 0 < c) (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A x v, v⟫_ℝ)
    (f f' : LiftL2 period)
    (hf : HasDerivAt (fun t => translation period (translationPath period a t) f) f' 0) :
    HasDerivAt (fun t => translation period (translationPath period a t)
      (liftedPressure period κ m A hA C hAb c hc hpos f))
      (liftedPressure period κ m A hA C hAb c hc hpos
        (f' - coefficientOperator (translatedCoefficientDerivative period a A 0)
          (translatedCoefficientDerivative_measurable period a A hAs) (D * ‖a‖₊)
          (fun x => translatedCoefficientDerivative_bound period a A D hDA x)
          (liftedPressure period κ m A hA C hAb c hc hpos f))) 0 := by
  let At := fun t => translatedCoefficient period (translationPath period a t) A
  let Ad := translatedCoefficientDerivative period a A
  have hAt : ∀ t, AEStronglyMeasurable (At t) (liftMeasure period) :=
    fun t => translatedCoefficient_measurable period (translationPath period a t) A hA
  have hAtb : ∀ t x, ‖At t x‖ ≤ C := fun t x => hAb (x + translationPath period a t)
  have hAtpos : ∀ t x v, c * ‖v‖ ^ 2 ≤ ⟪At t x v, v⟫_ℝ :=
    fun t x v => hpos (x + translationPath period a t) v
  have hAdb : ∀ x, ‖Ad 0 x‖ ≤ (D * ‖a‖₊ : ℝ≥0) :=
    fun x => translatedCoefficientDerivative_bound period a A D hDA x
  have hAdL : ∀ t x, ‖Ad t x - Ad 0 x‖ ≤ (M * ‖a‖₊ ^ 2 : ℝ≥0) * |t| := by
    intro t x
    simpa only [NNReal.coe_mul, NNReal.coe_pow, coe_nnnorm] using
      translatedCoefficientDerivative_lipschitz period a A hAs M hDDA t x
  have hsol := liftedPressure_hasDerivAt period κ m At Ad hAt
    (translatedCoefficientDerivative_measurable period a A hAs)
    C (D * ‖a‖₊) (M * ‖a‖₊ ^ 2) hAtb hAdb
    (translatedCoefficient_hasDerivAt period a A hAs) hAdL c hc hAtpos
    (fun t => translation period (translationPath period a t) f) f' hf
  have hcov : (fun t => liftedPressure period κ m (At t) (hAt t) C (hAtb t)
      c hc (hAtpos t) (translation period (translationPath period a t) f)) =
      fun t => translation period (translationPath period a t)
        (liftedPressure period κ m A hA C hAb c hc hpos f) := by
    funext t
    exact (liftedPressure_translation period κ m (translationPath period a t)
      A hA C hAb c hc hpos f).symm
  rw [hcov] at hsol
  have hzero : At 0 = A := by
    funext x
    simp [At, translatedCoefficient]
  simpa only [hzero, translationPath_zero, translation_zero] using hsol

theorem pressure_translation_derivative_norm (κ : ℝ) (m : Vector3) (a : LiftTangent)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hA : AEStronglyMeasurable A (liftMeasure period))
    (hAs : ∀ x, ContDiff ℝ ∞ (localFieldLift period A x))
    (C D M : ℝ≥0) (hAb : ∀ x, ‖A x‖ ≤ C)
    (hDA : ∀ x, ‖fderiv ℝ (localFieldLift period A x) 0‖ ≤ D)
    (hDDA : ∀ x y, ‖fderiv ℝ (fderiv ℝ (localFieldLift period A x)) y‖ ≤ M)
    (c : ℝ) (hc : 0 < c) (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A x v, v⟫_ℝ)
    (f f' : LiftL2 period)
    (hf : HasDerivAt (fun t => translation period (translationPath period a t) f) f' 0) :
    ‖deriv (fun t => translation period (translationPath period a t)
      (liftedPressure period κ m A hA C hAb c hc hpos f)) 0‖ ≤
        c⁻¹ * (‖f'‖ + (D : ℝ) * ‖a‖ *
          ‖liftedPressure period κ m A hA C hAb c hc hpos f‖) := by
  have hd := pressure_translation_hasDerivAt period κ m a A hA hAs C D M hAb hDA hDDA
    c hc hpos f f' hf
  rw [hd.deriv]
  refine (pressureSolver_apply_norm_le (gradientSpace period κ m)
    (coefficientOperator A hA C hAb) c hc
    (coefficientOperator_coercive A hA C hAb c hpos) _).trans ?_
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hc.le)
  refine (norm_sub_le _ _).trans (add_le_add_right ?_ ‖f'‖)
  exact coefficientApply_norm_le (translatedCoefficientDerivative period a A 0)
    (translatedCoefficientDerivative_measurable period a A hAs) (D * ‖a‖₊)
    (fun x => translatedCoefficientDerivative_bound period a A D hDA x)
    (liftedPressure period κ m A hA C hAb c hc hpos f)

end LiftedTranslation

end EulerPressureSpatialRegularity
