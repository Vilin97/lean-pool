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
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.MetricEnergyEvolution

@[expose] public section

noncomputable section

/-! Concrete L² transport and metric-energy evolution on the lifted cylinder. -/


namespace EulerLiftedMetricEvolution

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerLiftedPressure
  EulerMetricTransport EulerNoncompactTransport EulerMetricEnergyEvolution
open scoped ContDiff ENNReal NNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The actual directional transport derivative is square integrable under H¹ and bounded velocity. -/
theorem liftedTransport_memLp (κ : ℝ) (m : Vector3) (e z : LiftL2 period)
    (hDe : MemLp (fun x => fderiv ℝ (localFieldLift period (fun y => e y) x) 0)
      2 (liftMeasure period)) (B : ℝ≥0)
    (hzB : ∀ᵐ x ∂liftMeasure period, ‖z x‖ ≤ B) :
    MemLp (fun x => fderiv ℝ (localFieldLift period (fun y => e y) x) 0
      (transportDirection κ m (z x))) 2 (liftMeasure period) := by
  apply hDe.of_le_mul (c := (|κ| + ‖m‖) * B)
  · exact aestronglyMeasurable_apply period hDe.aestronglyMeasurable
      (transportDirection_aestronglyMeasurable period κ m z)
  filter_upwards [hzB] with x hx
  have hv := (transportDirection_norm_le κ m (z x)).trans
    (mul_le_mul_of_nonneg_left hx (add_nonneg (abs_nonneg _) (norm_nonneg _)))
  calc
    _ ≤ ‖fderiv ℝ (localFieldLift period (fun y => e y) x) 0‖ *
        ‖transportDirection κ m (z x)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖fderiv ℝ (localFieldLift period (fun y => e y) x) 0‖ * ((|κ| + ‖m‖) * B) :=
      mul_le_mul_of_nonneg_left hv (norm_nonneg _)
    _ = _ := by ring

/-- The genuine L² element represented by the lifted directional transport derivative. -/
def liftedTransport (κ : ℝ) (m : Vector3) (e z : LiftL2 period)
    (hDe : MemLp (fun x => fderiv ℝ (localFieldLift period (fun y => e y) x) 0)
      2 (liftMeasure period)) (B : ℝ≥0)
    (hzB : ∀ᵐ x ∂liftMeasure period, ‖z x‖ ≤ B) : LiftL2 period :=
  (liftedTransport_memLp period κ m e z hDe B hzB).toLp _

theorem liftedTransport_ae (κ : ℝ) (m : Vector3) (e z : LiftL2 period)
    (hDe : MemLp (fun x => fderiv ℝ (localFieldLift period (fun y => e y) x) 0)
      2 (liftMeasure period)) (B : ℝ≥0)
    (hzB : ∀ᵐ x ∂liftMeasure period, ‖z x‖ ≤ B) :
    liftedTransport period κ m e z hDe B hzB =ᵐ[liftMeasure period]
      fun x => fderiv ℝ (localFieldLift period (fun y => e y) x) 0
        (transportDirection κ m (z x)) :=
  (liftedTransport_memLp period κ m e z hDe B hzB).coeFn_toLp

/-- The Hilbert metric pairing equals the actual spatial transport integral. -/
theorem metric_transport_inner_eq (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hKm : AEStronglyMeasurable K (liftMeasure period)) (C : ℝ≥0) (hC : ∀ x, ‖K x‖ ≤ C)
    (e z : LiftL2 period)
    (hDe : MemLp (fun x => fderiv ℝ (localFieldLift period (fun y => e y) x) 0)
      2 (liftMeasure period)) (B : ℝ≥0)
    (hzB : ∀ᵐ x ∂liftMeasure period, ‖z x‖ ≤ B) :
    ⟪coefficientOperator K hKm C hC e, liftedTransport period κ m e z hDe B hzB⟫_ℝ =
      ∫ x, ⟪K x (e x), fderiv ℝ (localFieldLift period (fun y => e y) x) 0
        (transportDirection κ m (z x))⟫_ℝ ∂liftMeasure period := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coefficientOperator_ae K hKm C hC e, liftedTransport_ae period κ m e z hDe B hzB]
    with x hx hy
  rw [hx, hy]

/-- The transport bound required by the Hilbert energy theorem, with genuine spatial fields. -/
theorem metric_transport_inner_bound (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hKm : AEStronglyMeasurable K (liftMeasure period))
    (e z : LiftL2 period)
    (hK : ∀ x, ContDiff ℝ ∞ (localFieldLift period K x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period (fun y => e y) x))
    (hDe : MemLp (fun x => fderiv ℝ (localFieldLift period (fun y => e y) x) 0)
      2 (liftMeasure period))
    (hsym : ∀ x v w, ⟪K x v, w⟫_ℝ = ⟪v, K x w⟫_ℝ)
    (hz : z ∈ divergenceFreeSpace period κ m)
    (C D B : ℝ≥0) (hC : ∀ x, ‖K x‖ ≤ C)
    (hD : ∀ x, ‖fderiv ℝ (localFieldLift period K x) 0‖ ≤ D)
    (hzB : ∀ᵐ x ∂liftMeasure period, ‖z x‖ ≤ B) :
    |⟪coefficientOperator K hKm C hC e, liftedTransport period κ m e z hDe B hzB⟫_ℝ| ≤
      (1 / 2 : ℝ) * D * ((|κ| + ‖m‖) * B) * ‖e‖ ^ 2 := by
  rw [metric_transport_inner_eq]
  exact metric_transport_L2_H1_bound period κ m K e hK he hDe hsym hz C D B hC hD hzB

/-- A pointwise matrix family acting on the actual lifted L² space. -/
def metricFamily (K : ℝ → LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hKm : ∀ t, AEStronglyMeasurable (K t) (liftMeasure period))
    (C : ℝ≥0) (hC : ∀ t x, ‖K t x‖ ≤ C) : ℝ → LiftL2 period →L[ℝ] LiftL2 period :=
  fun t => coefficientOperator (K t) (hKm t) C (hC t)

/-- The metric norm estimate for the actual lifted transport-pressure equation. -/
theorem lifted_regularized_energy_evolution (κ : ℝ) (m : Vector3)
    (K : ℝ → LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hKm : ∀ t, AEStronglyMeasurable (K t) (liftMeasure period))
    (C : ℝ≥0) (hC : ∀ t x, ‖K t x‖ ≤ C)
    (e : ℝ → LiftL2 period) (t δ c : ℝ)
    (K' : LiftL2 period →L[ℝ] LiftL2 period) (e' z p forcing : LiftL2 period)
    (hδ : 0 < δ) (hc : 0 < c)
    (hKt : HasDerivAt (metricFamily period K hKm C hC) K' t) (het : HasDerivAt e e' t)
    (hKs : ∀ x, ContDiff ℝ ∞ (localFieldLift period (K t) x))
    (hes : ∀ x, ContDiff ℝ ∞ (localFieldLift period (fun y => e t y) x))
    (hDe : MemLp (fun x => fderiv ℝ (localFieldLift period (fun y => e t y) x) 0)
      2 (liftMeasure period))
    (hsym : ∀ x v w, ⟪K t x v, w⟫_ℝ = ⟪v, K t x w⟫_ℝ)
    (hpos : ∀ x v, c ^ 2 * ‖v‖ ^ 2 ≤ ⟪K t x v, v⟫_ℝ)
    (G : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hGm : AEStronglyMeasurable G (liftMeasure period)) (E : ℝ≥0) (hG : ∀ x, ‖G x‖ ≤ E)
    (hKG : ∀ x v, K t x (G x v) = v)
    (hep : e t ∈ divergenceFreeSpace period κ m) (hp : p ∈ gradientSpace period κ m)
    (hz : z ∈ divergenceFreeSpace period κ m) (D B : ℝ≥0)
    (hD : ∀ x, ‖fderiv ℝ (localFieldLift period (K t) x) 0‖ ≤ D)
    (hzB : ∀ᵐ x ∂liftMeasure period, ‖z x‖ ≤ B)
    (heq : e' + liftedTransport period κ m (e t) z hDe B hzB +
      coefficientOperator G hGm E hG p = forcing) :
    deriv (fun s => Real.sqrt (⟪metricFamily period K hKm C hC s (e s), e s⟫_ℝ + δ ^ 2)) t ≤
      ((‖K'‖ + (D : ℝ) * ((|κ| + ‖m‖) * B)) / (2 * c ^ 2)) *
        Real.sqrt (⟪metricFamily period K hKm C hC t (e t), e t⟫_ℝ + δ ^ 2) +
      ((C : ℝ) / c) * ‖forcing‖ := by
  let A := metricFamily period K hKm C hC
  let β : ℝ := (1 / 2 : ℝ) * D * ((|κ| + ‖m‖) * B)
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hsymL : ∀ v w, ⟪A t v, w⟫_ℝ = ⟪v, A t w⟫_ℝ :=
    coefficientOperator_inner_swap (K t) (hKm t) C (hC t) hsym
  have hposL : c ^ 2 * ‖e t‖ ^ 2 ≤ ⟪A t (e t), e t⟫_ℝ :=
    coefficientOperator_coercive (K t) (hKm t) C (hC t) (c ^ 2) hpos (e t)
  have hpL : ⟪A t (e t), coefficientOperator G hGm E hG p⟫_ℝ = 0 :=
    metric_pressure_cancellation period κ m (K t) G (hKm t) hGm C E (hC t) hG hsym hKG hep hp
  have htL := metric_transport_inner_bound period κ m (K t) (hKm t) (e t) z
    hKs hes hDe hsym hz C D B (hC t) hD hzB
  have h := regularized_metric_norm_evolution A e t δ c β K' e'
    (liftedTransport period κ m (e t) z hDe B hzB) (coefficientOperator G hGm E hG p)
    forcing hδ hc hβ hposL hKt het hsymL heq hpL htL
  have hA : ‖A t‖ ≤ C := coefficientOperator_norm_le (K t) (hKm t) C (hC t)
  have hb : 2 * β = (D : ℝ) * ((|κ| + ‖m‖) * B) := by dsimp [β]; ring
  rw [hb] at h
  exact h.trans (add_le_add_right (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hA hc.le) (norm_nonneg forcing)) _)

end EulerLiftedMetricEvolution
