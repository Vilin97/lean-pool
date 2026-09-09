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
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.SetIntegralL2

@[expose] public section

noncomputable section

/-! Classical smooth cylinder representatives obtained by Euclidean mollification. -/

namespace EulerCoverMollification

open MeasureTheory EulerSobolev EulerCylinderCoordinates EulerLiftedGradientSpace
  EulerMetricTransport
open scoped ContDiff ENNReal Convolution Topology

variable (period : ℝ) [Fact (0 < period)]

omit [Fact (0 < period)] in
theorem euclideanCover_add (z w : Domain 4) :
    euclideanCover period (z+w) = euclideanCover period z + euclideanCover period w := by
  simp [euclideanCover, coveringMap, map_add]

omit [Fact (0 < period)] in
theorem euclideanCover_sub (z w : Domain 4) :
    euclideanCover period (z-w) = euclideanCover period z - euclideanCover period w := by
  simp [euclideanCover, coveringMap, map_sub]

omit [Fact (0 < period)] in
theorem euclideanCover_surjective : Function.Surjective (euclideanCover period) := by
  intro x
  obtain ⟨v, hv⟩ := (coveringMap_isOpenQuotient period).surjective x
  refine ⟨coordinateEquiv.symm v, ?_⟩
  simpa only [euclideanCover, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply] using hv

section Integrability
variable {F : Type*} [NormedAddCommGroup F]

/-- L² cylinder fields have locally integrable periodic lifts to the Euclidean covering space. -/
theorem locallyIntegrable_cover (f : LiftDomain period → F) (hf : MemLp f 2 (liftMeasure period)) :
    LocallyIntegrable (f ∘ euclideanCover period) (volume : Measure (Domain 4)) := by
  intro x
  have hT : 0 < period := Fact.out
  let a : ℝ := x 0 - period/2
  have hsubset : Metric.ball x (period/4) ⊆ {z : Domain 4 | z 0 ∈ Set.Ioc a (a+period)} := by
    intro z hz
    have hd : ‖z-x‖ < period/4 := by simpa only [Metric.mem_ball, dist_eq_norm] using hz
    have hc : |z 0-x 0| ≤ ‖z-x‖ := PiLp.norm_apply_le (z-x) 0
    have hh := abs_le.mp (hc.trans hd.le)
    change a < z 0 ∧ z 0 ≤ a+period
    dsimp [a]
    constructor <;> linarith
  have hmeasure : (volume : Measure (Domain 4)).restrict (Metric.ball x (period/4)) ≤ stripMeasure
    period a :=
    Measure.restrict_mono hsubset le_rfl
  have hb : MemLp (f ∘ euclideanCover period) 2
      ((volume : Measure (Domain 4)).restrict (Metric.ball x (period/4))) :=
    MemLp.mono_measure hmeasure (memLp_cover period f hf a)
  have : Fact ((volume : Measure (Domain 4)) (Metric.ball x (period/4)) < ⊤) :=
    ⟨measure_ball_lt_top⟩
  exact ⟨Metric.ball x (period/4), Metric.ball_mem_nhds x (by positivity), hb.integrable (by
    norm_num)⟩

end Integrability

section Convolution
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Euclidean convolution of the periodic lift with a normalized compact bump. -/
noncomputable def coverConvolution (φ : ContDiffBump (0 : Domain 4)) (f : LiftDomain period → F) :
  Domain 4 → F :=
  φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (f ∘ euclideanCover period)

/-- The same convolution defined directly on the cylinder, with the usual negative translation. -/
noncomputable def cylinderConvolution (φ : ContDiffBump (0 : Domain 4))
    (f : LiftDomain period → F) (x : LiftDomain period) : F :=
  ∫ y : Domain 4, φ.normed volume y • f (x - euclideanCover period y)

omit [Fact (0 < period)] [CompleteSpace F] in
theorem cylinderConvolution_cover (φ : ContDiffBump (0 : Domain 4)) (f : LiftDomain period → F)
    (z : Domain 4) :
    cylinderConvolution period φ f (euclideanCover period z) = coverConvolution period φ f z := by
  rw [coverConvolution, convolution_def]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [ContinuousLinearMap.lsmul_apply, Function.comp_apply, euclideanCover_sub]

omit [CompleteSpace F] in
/-- The classical covering-space convolution is genuinely C∞. -/
theorem coverConvolution_smooth (φ : ContDiffBump (0 : Domain 4)) (f : LiftDomain period → F)
    (hf : MemLp f 2 (liftMeasure period)) : ContDiff ℝ ∞ (coverConvolution period φ f) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (φ.contDiff_normed (n := (⊤ : ℕ∞))) (locallyIntegrable_cover period f hf)

omit [CompleteSpace F] in
/-- The convolution descends to a C∞ cylinder field in the actual local covering coordinates. -/
theorem cylinderConvolution_smooth (φ : ContDiffBump (0 : Domain 4)) (f : LiftDomain period → F)
    (hf : MemLp f 2 (liftMeasure period)) :
    ∀ x, ContDiff ℝ ∞ (localFieldLift period (cylinderConvolution period φ f) x) := by
  intro x
  obtain ⟨z, hz⟩ := euclideanCover_surjective period x
  have he : localFieldLift period (cylinderConvolution period φ f) x =
      fun v => coverConvolution period φ f (z + coordinateEquiv.symm v) := by
    funext v
    rw [← cylinderConvolution_cover, euclideanCover_add, hz]
    congr 1
  rw [he]
  exact (coverConvolution_smooth period φ f hf).comp (contDiff_const.add
    coordinateEquiv.symm.contDiff)

omit [Fact (0 < period)] [CompleteSpace F] in
/-- The covering-space convolution is periodic in the angular direction. -/
theorem coverConvolution_periodic (φ : ContDiffBump (0 : Domain 4)) (f : LiftDomain period → F) :
    Function.Periodic (coverConvolution period φ f) (EuclideanSpace.single 0 period) := by
  intro z
  rw [← cylinderConvolution_cover, ← cylinderConvolution_cover, euclideanCover_add]
  have hz : euclideanCover period (EuclideanSpace.single 0 period) = 0 := by
    apply Prod.ext
    · ext i
      simp [euclideanCover, coveringMap]
    · simp [euclideanCover, coveringMap]
  rw [hz, add_zero]

/-- Normalized shrinking bump convolutions recover the original covering-space function almost everywhere. -/
theorem ae_coverConvolution_tendsto {φ : ℕ → ContDiffBump (0 : Domain 4)}
    (hφ : Filter.Tendsto (fun n => (φ n).rOut) Filter.atTop (𝓝 0))
    (hshape : ∀ᶠ n in Filter.atTop, (φ n).rOut ≤ 2*(φ n).rIn)
    (f : LiftDomain period → F) (hf : MemLp f 2 (liftMeasure period)) :
    ∀ᵐ z ∂(volume : Measure (Domain 4)), Filter.Tendsto (fun n => coverConvolution period (φ n) f z)
      Filter.atTop (𝓝 (f (euclideanCover period z))) :=
  ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hφ hshape (locallyIntegrable_cover
    period f hf)

end Convolution
end EulerCoverMollification
