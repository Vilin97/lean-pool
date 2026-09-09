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
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.LiftedPressure

@[expose] public section

noncomputable section

/-!
Transport integration by parts on the actual lifted cylinder.  Compactly
supported smooth energy fields are tested against the concrete weak-divergence
condition; boundary terms are eliminated by that proved weak formulation.
-/


namespace EulerMetricTransport

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerLiftedPressure
open scoped ContDiff ENNReal NNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- A field pulled back to real covering coordinates centered at a cylinder point. -/
def localFieldLift {W : Type*} (f : LiftDomain period → W) (x : LiftDomain period) :
    LiftTangent → W := fun h => f (x.1 + h.1, x.2 + (h.2 : AddCircle period))

section Fields

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

omit [Fact (0 < period)] [NormedAddCommGroup W] [NormedSpace ℝ W] in
theorem localFieldLift_cover (f : LiftDomain period → W) (z : LiftTangent) :
    localFieldLift period f (coveringMap period z) =
      fun h => localFieldLift period f 0 (z + h) := by
  funext h
  simp [localFieldLift, coveringMap]

omit [Fact (0 < period)] in
theorem fderiv_localFieldLift_cover (f : LiftDomain period → W) (z : LiftTangent) :
    fderiv ℝ (localFieldLift period f (coveringMap period z)) 0 =
      fderiv ℝ (localFieldLift period f 0) z := by
  rw [localFieldLift_cover, fderiv_comp_add_left, add_zero]

omit [Fact (0 < period)] in
theorem smoothField_continuous (f : LiftDomain period → W)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) : Continuous f := by
  apply (coveringMap_isOpenQuotient period).isQuotientMap.continuous_iff.mpr
  have heq : f ∘ coveringMap period = localFieldLift period f 0 := by
    funext z
    simp [localFieldLift, coveringMap]
  rw [heq]
  exact (hf 0).continuous

omit [Fact (0 < period)] in
theorem localFDeriv_continuous (f : LiftDomain period → W)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    Continuous (fun x => fderiv ℝ (localFieldLift period f x) 0) := by
  apply (coveringMap_isOpenQuotient period).isQuotientMap.continuous_iff.mpr
  have heq : (fun x => fderiv ℝ (localFieldLift period f x) 0) ∘ coveringMap period =
      fderiv ℝ (localFieldLift period f 0) := by
    funext z
    exact fderiv_localFieldLift_cover period f z
  rw [heq]
  exact (hf 0).continuous_fderiv (by simp)

end Fields

/-- The covering-space direction corresponding to one lifted gradient component. -/
def coordinateDirection (κ : ℝ) (m : Vector3) (i : Fin 3) : LiftTangent :=
  (κ • EuclideanSpace.single i 1, m i)

/-- The actual four dimensional transport vector associated with a lifted velocity. -/
def transportDirection (κ : ℝ) (m v : Vector3) : LiftTangent :=
  (κ • v, ⟪m, v⟫_ℝ)

/-- The vector of a scalar differential evaluated on the lifted coordinate directions. -/
def vectorOfLinear (κ : ℝ) (m : Vector3) (L : LiftTangent →L[ℝ] ℝ) : Vector3 :=
  WithLp.toLp 2 fun i => L (coordinateDirection κ m i)

theorem coordinateDirections_sum (κ : ℝ) (m v : Vector3) :
    ∑ i : Fin 3, v i • coordinateDirection κ m i = transportDirection κ m v := by
  have hrepr : ∑ i : Fin 3, v i • EuclideanSpace.single i 1 = v := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v
  apply Prod.ext
  · change (∑ i : Fin 3, v i • coordinateDirection κ m i).1 = κ • v
    calc
      (∑ i : Fin 3, v i • coordinateDirection κ m i).1 =
          ∑ i : Fin 3, v i • (κ • EuclideanSpace.single i 1) := by
            simp [Prod.fst_sum, coordinateDirection]
      _ = κ • ∑ i : Fin 3, v i • EuclideanSpace.single i 1 := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _
        exact smul_comm _ _ _
      _ = κ • v := by rw [hrepr]
  · change (∑ i : Fin 3, v i • coordinateDirection κ m i).2 = ⟪m, v⟫_ℝ
    simp [Prod.snd_sum, coordinateDirection, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct, mul_comm]

theorem vectorOfLinear_inner (κ : ℝ) (m v : Vector3) (L : LiftTangent →L[ℝ] ℝ) :
    ⟪vectorOfLinear κ m L, v⟫_ℝ = L (transportDirection κ m v) := by
  rw [← coordinateDirections_sum κ m v, map_sum]
  simp [vectorOfLinear, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    map_smul, smul_eq_mul]

omit [Fact (0 < period)] in
theorem liftedGradient_eq_vectorOfLinear (κ : ℝ) (m : Vector3)
    (φ : LiftDomain period → ℝ) (x : LiftDomain period) :
    liftedGradient period κ m φ x =
      vectorOfLinear κ m (fderiv ℝ (localLift period φ x) 0) := by
  apply PiLp.ext
  intro i
  have hd : coordinateDirection κ m i =
      κ • (EuclideanSpace.single i 1, (0 : ℝ)) + m i • ((0 : Vector3), (1 : ℝ)) := by
    ext <;> simp [coordinateDirection]
  change κ * (fderiv ℝ (localLift period φ x) 0) (EuclideanSpace.single i 1, 0) +
      m i * (fderiv ℝ (localLift period φ x) 0) (0, 1) =
    (fderiv ℝ (localLift period φ x) 0) (coordinateDirection κ m i)
  rw [hd, map_add, map_smul, map_smul]
  rfl

/-- The pointwise quadratic metric energy of a vector field. -/
def metricEnergy (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (e : LiftDomain period → Vector3) (x : LiftDomain period) : ℝ :=
  (1 / 2 : ℝ) * ⟪K x (e x), e x⟫_ℝ

omit [Fact (0 < period)] in
theorem metricEnergy_compact (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (e : LiftDomain period → Vector3) (he : HasCompactSupport e) :
    HasCompactSupport (metricEnergy period K e) := by
  apply he.mono
  intro x hx
  contrapose! hx
  simp only [Function.mem_support, not_not] at hx
  simp [Function.mem_support, metricEnergy, hx]

omit [Fact (0 < period)] in
theorem metricEnergy_smooth (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (e : LiftDomain period → Vector3)
    (hK : ∀ x, ContDiff ℝ ∞ (localFieldLift period K x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period e x)) (x : LiftDomain period) :
    ContDiff ℝ ∞ (localLift period (metricEnergy period K e) x) := by
  exact contDiff_const.mul (((hK x).clm_apply (he x)).inner ℝ (he x))

omit [Fact (0 < period)] in
theorem metricEnergy_fderiv (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (e : LiftDomain period → Vector3)
    (hK : ∀ x, ContDiff ℝ ∞ (localFieldLift period K x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period e x))
    (hsym : ∀ x v w, ⟪K x v, w⟫_ℝ = ⟪v, K x w⟫_ℝ)
    (x : LiftDomain period) (v : LiftTangent) :
    fderiv ℝ (localLift period (metricEnergy period K e) x) 0 v =
      ⟪K x (e x), fderiv ℝ (localFieldLift period e x) 0 v⟫_ℝ +
        (1 / 2 : ℝ) *
          ⟪(fderiv ℝ (localFieldLift period K x) 0 v) (e x), e x⟫_ℝ := by
  have hdK := ((hK x).differentiable (by simp)).differentiableAt.hasFDerivAt (x := 0)
  have hde := ((he x).differentiable (by simp)).differentiableAt.hasFDerivAt (x := 0)
  have hd := (((hdK.clm_apply hde).inner ℝ hde).const_mul (1 / 2 : ℝ)).fderiv
  have heq := congrArg (fun L : LiftTangent →L[ℝ] ℝ => L v) hd
  dsimp [localFieldLift] at heq
  change fderiv ℝ (localLift period (metricEnergy period K e) x) 0 v = _ at heq
  rw [heq]
  simp only [smul_apply, smul_eq_mul,
    ContinuousLinearMap.comp_apply, fderivInnerCLM_apply,
    ContinuousLinearMap.prod_apply, add_apply,
    ContinuousLinearMap.flip_apply, add_zero, inner_add_left]
  have hs : ⟪K x (fderiv ℝ (localFieldLift period e x) 0 v), e x⟫_ℝ =
      ⟪K x (e x), fderiv ℝ (localFieldLift period e x) 0 v⟫_ℝ := by
    rw [hsym]
    exact real_inner_comm _ _
  rw [hs]
  ring

omit [Fact (0 < period)] in
theorem metricEnergy_gradient_transport (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (e : LiftDomain period → Vector3)
    (hK : ∀ x, ContDiff ℝ ∞ (localFieldLift period K x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period e x))
    (hsym : ∀ x v w, ⟪K x v, w⟫_ℝ = ⟪v, K x w⟫_ℝ)
    (x : LiftDomain period) (z : Vector3) :
    ⟪liftedGradient period κ m (metricEnergy period K e) x, z⟫_ℝ =
      ⟪K x (e x),
        fderiv ℝ (localFieldLift period e x) 0 (transportDirection κ m z)⟫_ℝ +
      (1 / 2 : ℝ) * ⟪(fderiv ℝ (localFieldLift period K x) 0
        (transportDirection κ m z)) (e x), e x⟫_ℝ := by
  rw [liftedGradient_eq_vectorOfLinear, vectorOfLinear_inner]
  exact metricEnergy_fderiv period K e hK he hsym x _

theorem metric_transport_zero (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (e : LiftDomain period → Vector3) (hec : HasCompactSupport e)
    (hK : ∀ x, ContDiff ℝ ∞ (localFieldLift period K x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period e x))
    (hsym : ∀ x v w, ⟪K x v, w⟫_ℝ = ⟪v, K x w⟫_ℝ)
    {z : LiftL2 period} (hz : z ∈ divergenceFreeSpace period κ m) :
    ∫ x, (⟪K x (e x),
        fderiv ℝ (localFieldLift period e x) 0 (transportDirection κ m (z x))⟫_ℝ +
      (1 / 2 : ℝ) * ⟪(fderiv ℝ (localFieldLift period K x) 0
        (transportDirection κ m (z x))) (e x), e x⟫_ℝ) ∂liftMeasure period = 0 := by
  have htest := weak_divergence_test_integral period κ m hz (metricEnergy period K e)
    ⟨metricEnergy_compact period K e hec, metricEnergy_smooth period K e hK he⟩
  convert htest using 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x =>
    (metricEnergy_gradient_transport period κ m K e hK he hsym x (z x)).symm

/-- The compact vector coefficient whose pairing with velocity is the metric transport term. -/
def transportFlux (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (e : LiftDomain period → Vector3) (x : LiftDomain period) : Vector3 :=
  vectorOfLinear κ m ((innerSL ℝ (K x (e x))).comp
    (fderiv ℝ (localFieldLift period e x) 0))

omit [Fact (0 < period)] in
theorem transportFlux_inner (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (e : LiftDomain period → Vector3) (x : LiftDomain period) (z : Vector3) :
    ⟪transportFlux period κ m K e x, z⟫_ℝ =
      ⟪K x (e x),
        fderiv ℝ (localFieldLift period e x) 0 (transportDirection κ m z)⟫_ℝ := by
  rw [transportFlux, vectorOfLinear_inner]
  rfl

omit [Fact (0 < period)] in
theorem transportFlux_continuous (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (e : LiftDomain period → Vector3)
    (hK : ∀ x, ContDiff ℝ ∞ (localFieldLift period K x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period e x)) :
    Continuous (transportFlux period κ m K e) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  exact ((smoothField_continuous period K hK).clm_apply
    (smoothField_continuous period e he)).inner
      ((localFDeriv_continuous period e he).clm_apply continuous_const)

omit [Fact (0 < period)] in
theorem transportFlux_compact (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (e : LiftDomain period → Vector3) (he : HasCompactSupport e) :
    HasCompactSupport (transportFlux period κ m K e) := by
  apply he.mono
  intro x hx
  contrapose! hx
  simp only [Function.mem_support, not_not] at hx ⊢
  apply PiLp.ext
  intro i
  simp [transportFlux, vectorOfLinear, hx]

theorem compact_pairing_integrable (f : LiftDomain period → Vector3)
    (hf : Continuous f) (hfc : HasCompactSupport f) (z : LiftL2 period) :
    Integrable (fun x => ⟪f x, z x⟫_ℝ) (liftMeasure period) := by
  have hlp : MemLp f 2 (liftMeasure period) := hf.memLp_of_hasCompactSupport hfc
  apply (L2.integrable_inner (hlp.toLp f) z).congr
  filter_upwards [hlp.coeFn_toLp] with x hx
  rw [hx]

theorem metric_transport_integrable (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (e : LiftDomain period → Vector3) (hec : HasCompactSupport e)
    (hK : ∀ x, ContDiff ℝ ∞ (localFieldLift period K x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period e x)) (z : LiftL2 period) :
    Integrable (fun x => ⟪K x (e x),
      fderiv ℝ (localFieldLift period e x) 0 (transportDirection κ m (z x))⟫_ℝ)
      (liftMeasure period) := by
  simpa only [transportFlux_inner] using
    compact_pairing_integrable period (transportFlux period κ m K e)
      (transportFlux_continuous period κ m K e hK he)
      (transportFlux_compact period κ m K e hec) z

theorem metric_transport_by_parts (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (e : LiftDomain period → Vector3) (hec : HasCompactSupport e)
    (hK : ∀ x, ContDiff ℝ ∞ (localFieldLift period K x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period e x))
    (hsym : ∀ x v w, ⟪K x v, w⟫_ℝ = ⟪v, K x w⟫_ℝ)
    {z : LiftL2 period} (hz : z ∈ divergenceFreeSpace period κ m) :
    (∫ x, ⟪K x (e x),
      fderiv ℝ (localFieldLift period e x) 0 (transportDirection κ m (z x))⟫_ℝ
      ∂liftMeasure period) =
    -(∫ x, (1 / 2 : ℝ) * ⟪(fderiv ℝ (localFieldLift period K x) 0
        (transportDirection κ m (z x))) (e x), e x⟫_ℝ ∂liftMeasure period) := by
  have ht := metric_transport_integrable period κ m K e hec hK he z
  have hg := compact_pairing_integrable period
    (liftedGradient period κ m (metricEnergy period K e))
    (liftedGradient_continuous period κ m (metricEnergy period K e)
      (metricEnergy_smooth period K e hK he))
    (liftedGradient_hasCompactSupport period κ m (metricEnergy period K e)
      (metricEnergy_compact period K e hec)) z
  simp only [metricEnergy_gradient_transport period κ m K e hK he hsym] at hg
  have hq : Integrable (fun x => (1 / 2 : ℝ) *
      ⟪(fderiv ℝ (localFieldLift period K x) 0
        (transportDirection κ m (z x))) (e x), e x⟫_ℝ) (liftMeasure period) := by
    convert hg.sub ht using 1
    funext x
    simp
  have hzint := metric_transport_zero period κ m K e hec hK he hsym hz
  rw [integral_add ht hq] at hzint
  exact eq_neg_of_add_eq_zero_left hzint

theorem transportDirection_norm_le (κ : ℝ) (m v : Vector3) :
    ‖transportDirection κ m v‖ ≤ (|κ| + ‖m‖) * ‖v‖ := by
  rw [transportDirection, Prod.norm_mk, norm_smul, Real.norm_eq_abs]
  apply max_le
  · exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (norm_nonneg m))
      (norm_nonneg v)
  · exact (norm_inner_le_norm m v).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (abs_nonneg κ)) (norm_nonneg v))

theorem metric_transport_bound (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (e : LiftDomain period → Vector3) (hec : HasCompactSupport e)
    (hK : ∀ x, ContDiff ℝ ∞ (localFieldLift period K x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period e x))
    (hsym : ∀ x v w, ⟪K x v, w⟫_ℝ = ⟪v, K x w⟫_ℝ)
    {z : LiftL2 period} (hz : z ∈ divergenceFreeSpace period κ m)
    (C B : ℝ≥0)
    (hDK : ∀ x, ‖fderiv ℝ (localFieldLift period K x) 0‖ ≤ C)
    (hb : ∀ᵐ x ∂liftMeasure period, ‖transportDirection κ m (z x)‖ ≤ B) :
    |∫ x, ⟪K x (e x),
      fderiv ℝ (localFieldLift period e x) 0 (transportDirection κ m (z x))⟫_ℝ
      ∂liftMeasure period| ≤
      (1 / 2 : ℝ) * C * B * ∫ x, ‖e x‖ ^ 2 ∂liftMeasure period := by
  rw [metric_transport_by_parts period κ m K e hec hK he hsym hz, abs_neg]
  have heLp : MemLp e 2 (liftMeasure period) :=
    (smoothField_continuous period e he).memLp_of_hasCompactSupport hec
  have heint := heLp.norm.integrable_sq
  have hbound := norm_integral_le_of_norm_le
    (heint.const_mul ((1 / 2 : ℝ) * C * B)) (f := fun x => (1 / 2 : ℝ) *
      ⟪(fderiv ℝ (localFieldLift period K x) 0
        (transportDirection κ m (z x))) (e x), e x⟫_ℝ) ?_
  · simpa only [Real.norm_eq_abs, integral_const_mul] using hbound
  filter_upwards [hb] with x hx
  have hL : ‖fderiv ℝ (localFieldLift period K x) 0
      (transportDirection κ m (z x))‖ ≤ (C : ℝ) * B :=
    ((fderiv ℝ (localFieldLift period K x) 0).le_opNorm _).trans
      (mul_le_mul (hDK x) hx (norm_nonneg _) C.coe_nonneg)
  have hLe : ‖(fderiv ℝ (localFieldLift period K x) 0
      (transportDirection κ m (z x))) (e x)‖ ≤ (C : ℝ) * B * ‖e x‖ :=
    ((fderiv ℝ (localFieldLift period K x) 0
      (transportDirection κ m (z x))).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
  calc
    _ = (1 / 2 : ℝ) * ‖⟪(fderiv ℝ (localFieldLift period K x) 0
        (transportDirection κ m (z x))) (e x), e x⟫_ℝ‖ := by
          rw [norm_mul]
          norm_num
    _ ≤ (1 / 2 : ℝ) * (‖(fderiv ℝ (localFieldLift period K x) 0
        (transportDirection κ m (z x))) (e x)‖ * ‖e x‖) :=
      mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (by norm_num)
    _ ≤ (1 / 2 : ℝ) * (((C : ℝ) * B * ‖e x‖) * ‖e x‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hLe (norm_nonneg _)) (by norm_num)
    _ = _ := by ring

theorem metric_transport_L2_bound (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (e : LiftL2 period) (hec : HasCompactSupport (fun x => e x))
    (hK : ∀ x, ContDiff ℝ ∞ (localFieldLift period K x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period (fun y => e y) x))
    (hsym : ∀ x v w, ⟪K x v, w⟫_ℝ = ⟪v, K x w⟫_ℝ)
    {z : LiftL2 period} (hz : z ∈ divergenceFreeSpace period κ m)
    (C B : ℝ≥0)
    (hDK : ∀ x, ‖fderiv ℝ (localFieldLift period K x) 0‖ ≤ C)
    (hb : ∀ᵐ x ∂liftMeasure period, ‖transportDirection κ m (z x)‖ ≤ B) :
    |∫ x, ⟪K x (e x),
      fderiv ℝ (localFieldLift period (fun y => e y) x) 0
        (transportDirection κ m (z x))⟫_ℝ ∂liftMeasure period| ≤
      (1 / 2 : ℝ) * C * B * ‖e‖ ^ 2 := by
  have hn : (∫ x, ‖e x‖ ^ 2 ∂liftMeasure period) = ‖e‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
  simpa only [hn] using metric_transport_bound period κ m K (fun x => e x)
    hec hK he hsym hz C B hDK hb

end EulerMetricTransport
