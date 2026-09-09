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
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.SpatialSobolevInverse

@[expose] public section

noncomputable section

/-!
The closed lifted gradient space consists of distributionally curl-free
fields.  The proof uses actual compact scalar tests and mixed derivative
symmetry, then passes to the L² closure through continuous inner products.
-/


namespace EulerLiftedCurl

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerMetricTransport
  EulerTransportDerivatives EulerPressureSpatialRegularity EulerLiftedWeakDerivative
open scoped ContDiff ENNReal NNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Isometric inclusion of a scalar into the first Euclidean component. -/
def scalarEmbedding : ℝ →L[ℝ] Vector3 :=
  ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single (0 : Fin 3) 1)

omit [Fact (0 < period)] in
theorem scalarEmbedding_inner (r s : ℝ) :
    ⟪scalarEmbedding r, scalarEmbedding s⟫_ℝ = r * s := by
  simp [scalarEmbedding, inner_smul_left, inner_smul_right, mul_comm]

omit [Fact (0 < period)] in
theorem fieldDerivative_linear {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (L : V →L[ℝ] W)
    (f : LiftDomain period → V) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (a : LiftTangent) (x : LiftDomain period) :
    fieldDerivative period a (fun y => L (f y)) x = L (fieldDerivative period a f x) := by
  have hd := L.hasFDerivAt.comp (0 : LiftTangent)
    (((hf x).differentiable (by simp)) 0).hasFDerivAt
  have he := congrArg (fun D : LiftTangent →L[ℝ] W => D a) hd.fderiv
  exact he

omit [Fact (0 < period)] in
theorem scalar_embedding_smooth (φ : LiftDomain period → ℝ)
    (hφ : ∀ x, ContDiff ℝ ∞ (localFieldLift period φ x)) (x : LiftDomain period) :
    ContDiff ℝ ∞ (localFieldLift period (fun y => scalarEmbedding (φ y)) x) :=
  scalarEmbedding.contDiff.comp (hφ x)

omit [Fact (0 < period)] in
theorem scalar_embedding_compact (φ : LiftDomain period → ℝ) (hφ : HasCompactSupport φ) :
    HasCompactSupport (fun x => scalarEmbedding (φ x)) := by
  apply hφ.mono
  intro x hx
  contrapose! hx
  simp only [Function.mem_support, not_not] at hx ⊢
  rw [hx, map_zero]

/-- Genuine scalar integration by parts on the cylinder in any constant covering direction. -/
theorem scalar_integration_by_parts (a : LiftTangent) (φ ψ : LiftDomain period → ℝ)
    (hφc : HasCompactSupport φ) (hψc : HasCompactSupport ψ)
    (hφ : ∀ x, ContDiff ℝ ∞ (localFieldLift period φ x))
    (hψ : ∀ x, ContDiff ℝ ∞ (localFieldLift period ψ x)) :
    (∫ x, fieldDerivative period a φ x * ψ x ∂liftMeasure period) =
      -(∫ x, φ x * fieldDerivative period a ψ x ∂liftMeasure period) := by
  let F := fun x => scalarEmbedding (φ x)
  let G := fun x => scalarEmbedding (ψ x)
  let hFc := scalar_embedding_compact period φ hφc
  let hGc := scalar_embedding_compact period ψ hψc
  let hFs := scalar_embedding_smooth period φ hφ
  let hGs := scalar_embedding_smooth period ψ hψ
  have hi := strong_translation_derivative_weak period a
    (smoothFieldLp period F hFc hFs) (derivativeFieldLp period a F hFc hFs)
    (smoothFieldLp_translation_hasDerivAt period a F hFc hFs) G hGc hGs
  have hleft : (∫ x, ⟪(derivativeFieldLp period a F hFc hFs) x, G x⟫_ℝ
      ∂liftMeasure period) = ∫ x, fieldDerivative period a φ x * ψ x ∂liftMeasure period := by
    apply integral_congr_ae
    filter_upwards [derivativeFieldLp_ae period a F hFc hFs] with x hx
    rw [hx]
    change ⟪fieldDerivative period a (fun y => scalarEmbedding (φ y)) x,
      scalarEmbedding (ψ x)⟫_ℝ = _
    rw [fieldDerivative_linear period scalarEmbedding φ hφ, scalarEmbedding_inner]
  have hright : (∫ x, ⟪(smoothFieldLp period F hFc hFs) x, fieldDerivative period a G x⟫_ℝ
      ∂liftMeasure period) = ∫ x, φ x * fieldDerivative period a ψ x ∂liftMeasure period := by
    apply integral_congr_ae
    filter_upwards [smoothFieldLp_ae period F hFc hFs] with x hx
    rw [hx]
    change ⟪scalarEmbedding (φ x),
      fieldDerivative period a (fun y => scalarEmbedding (ψ y)) x⟫_ℝ = _
    rw [fieldDerivative_linear period scalarEmbedding ψ hψ, scalarEmbedding_inner]
  rw [hleft, hright] at hi
  exact hi

omit [Fact (0 < period)] in
theorem fieldDerivatives_commute {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (a b : LiftTangent) (f : LiftDomain period → W)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) :
    fieldDerivative period a (fieldDerivative period b f) x =
      fieldDerivative period b (fieldDerivative period a f) x := by
  have h := directional_transport_commutator a (fun _ : LiftTangent => b)
    (localFieldLift period f x) contDiff_const (hf x) 0
  change fderiv ℝ (localFieldLift period (fieldDerivative period b f) x) 0 a =
    fderiv ℝ (localFieldLift period (fieldDerivative period a f) x) 0 b
  rw [localFieldLift_fieldDerivative, localFieldLift_fieldDerivative]
  change fderiv ℝ (directionalDerivative b (localFieldLift period f x)) 0 a =
    fderiv ℝ (directionalDerivative a (localFieldLift period f x)) 0 b +
      fderiv ℝ (localFieldLift period f x) 0 (fderiv ℝ (fun _ : LiftTangent => b) 0 a) at h
  have hc : fderiv ℝ (fun _ : LiftTangent => b) 0 = 0 := by simp
  rw [hc, zero_apply, map_zero, add_zero] at h
  exact h

/-- A compact antisymmetric derivative test field for one lifted curl component. -/
def curlTest (κ : ℝ) (m : Vector3) (i j : Fin 3) (ψ : LiftDomain period → ℝ)
    (x : LiftDomain period) : Vector3 :=
  fieldDerivative period (coordinateDirection κ m j) ψ x • EuclideanSpace.single i 1 -
    fieldDerivative period (coordinateDirection κ m i) ψ x • EuclideanSpace.single j 1

omit [Fact (0 < period)] in
theorem curlTest_smooth (κ : ℝ) (m : Vector3) (i j : Fin 3) (ψ : LiftDomain period → ℝ)
    (hψ : ∀ x, ContDiff ℝ ∞ (localFieldLift period ψ x)) (x : LiftDomain period) :
    ContDiff ℝ ∞ (localFieldLift period (curlTest period κ m i j ψ) x) := by
  exact ((fieldDerivative_smooth period _ ψ hψ x).smul contDiff_const).sub
    ((fieldDerivative_smooth period _ ψ hψ x).smul contDiff_const)

omit [Fact (0 < period)] in
theorem curlTest_compact (κ : ℝ) (m : Vector3) (i j : Fin 3) (ψ : LiftDomain period → ℝ)
    (hψ : HasCompactSupport ψ) : HasCompactSupport (curlTest period κ m i j ψ) := by
  apply HasCompactSupport.intro hψ
  intro x hx
  have hd : ∀ a, fieldDerivative period a ψ x = 0 := by
    intro a
    change fieldFDeriv period ψ x a = 0
    rw [fieldFDeriv_zero_outside period ψ x hx]
    rfl
  simp [curlTest, hd]

omit [Fact (0 < period)] in
theorem vector_curlTest_inner (κ : ℝ) (m : Vector3) (i j : Fin 3)
    (ψ : LiftDomain period → ℝ) (x : LiftDomain period) (v : Vector3) :
    ⟪v, curlTest period κ m i j ψ x⟫_ℝ =
      v i * fieldDerivative period (coordinateDirection κ m j) ψ x -
        v j * fieldDerivative period (coordinateDirection κ m i) ψ x := by
  simp [curlTest, inner_sub_right, inner_smul_right, EuclideanSpace.inner_single_right, mul_comm]

omit [Fact (0 < period)] in
theorem liftedGradient_component (κ : ℝ) (m : Vector3) (φ : LiftDomain period → ℝ)
    (x : LiftDomain period) (i : Fin 3) :
    liftedGradient period κ m φ x i = fieldDerivative period (coordinateDirection κ m i) φ x := by
  rw [liftedGradient_eq_vectorOfLinear]
  rfl

theorem scalar_derivative_product_integrable (a b : LiftTangent)
    (φ ψ : LiftDomain period → ℝ) (hφc : HasCompactSupport φ)
    (hφ : ∀ x, ContDiff ℝ ∞ (localFieldLift period φ x))
    (hψ : ∀ x, ContDiff ℝ ∞ (localFieldLift period ψ x)) :
    Integrable (fun x => fieldDerivative period a φ x * fieldDerivative period b ψ x)
      (liftMeasure period) := by
  have hc := (smoothField_continuous period _ (fieldDerivative_smooth period a φ hφ)).mul
    (smoothField_continuous period _ (fieldDerivative_smooth period b ψ hψ))
  exact hc.integrable_of_hasCompactSupport (fieldDerivative_compact period a φ hφc).mul_right

theorem test_gradient_curl_integral (κ : ℝ) (m : Vector3) (i j : Fin 3)
    (φ ψ : LiftDomain period → ℝ) (hφc : HasCompactSupport φ) (hψc : HasCompactSupport ψ)
    (hφ : ∀ x, ContDiff ℝ ∞ (localFieldLift period φ x))
    (hψ : ∀ x, ContDiff ℝ ∞ (localFieldLift period ψ x)) :
    ∫ x, ⟪liftedGradient period κ m φ x, curlTest period κ m i j ψ x⟫_ℝ
      ∂liftMeasure period = 0 := by
  simp only [vector_curlTest_inner, liftedGradient_component]
  rw [integral_sub (scalar_derivative_product_integrable period _ _ φ ψ hφc hφ hψ)
    (scalar_derivative_product_integrable period _ _ φ ψ hφc hφ hψ)]
  have hi := scalar_integration_by_parts period (coordinateDirection κ m i) φ
    (fieldDerivative period (coordinateDirection κ m j) ψ) hφc
    (fieldDerivative_compact period _ ψ hψc) hφ (fieldDerivative_smooth period _ ψ hψ)
  have hj := scalar_integration_by_parts period (coordinateDirection κ m j) φ
    (fieldDerivative period (coordinateDirection κ m i) ψ) hφc
    (fieldDerivative_compact period _ ψ hψc) hφ (fieldDerivative_smooth period _ ψ hψ)
  rw [hi, hj]
  have heq : (fun x => φ x * fieldDerivative period (coordinateDirection κ m i)
      (fieldDerivative period (coordinateDirection κ m j) ψ) x) =
      fun x => φ x * fieldDerivative period (coordinateDirection κ m j)
        (fieldDerivative period (coordinateDirection κ m i) ψ) x := by
    funext x
    rw [fieldDerivatives_commute period _ _ ψ hψ]
  rw [heq, sub_self]

/-- The L² realization of an actual compact lifted curl test. -/
def curlTestLp (κ : ℝ) (m : Vector3) (i j : Fin 3) (ψ : LiftDomain period → ℝ)
    (hψc : HasCompactSupport ψ) (hψ : ∀ x, ContDiff ℝ ∞ (localFieldLift period ψ x)) :
    LiftL2 period := smoothFieldLp period (curlTest period κ m i j ψ)
      (curlTest_compact period κ m i j ψ hψc) (curlTest_smooth period κ m i j ψ hψ)

theorem curlTestLp_ae (κ : ℝ) (m : Vector3) (i j : Fin 3) (ψ : LiftDomain period → ℝ)
    (hψc : HasCompactSupport ψ) (hψ : ∀ x, ContDiff ℝ ∞ (localFieldLift period ψ x)) :
    curlTestLp period κ m i j ψ hψc hψ =ᵐ[liftMeasure period] curlTest period κ m i j ψ :=
  smoothFieldLp_ae period (curlTest period κ m i j ψ)
    (curlTest_compact period κ m i j ψ hψc) (curlTest_smooth period κ m i j ψ hψ)

theorem generator_curl_pairing (κ : ℝ) (m : Vector3) (i j : Fin 3)
    (ψ : LiftDomain period → ℝ) (hψc : HasCompactSupport ψ)
    (hψ : ∀ x, ContDiff ℝ ∞ (localFieldLift period ψ x))
    {g : LiftL2 period} (hg : g ∈ ({g : EulerLiftedGradientSpace.LiftL2 period | ∃ φ :
      EulerLiftedGradientSpace.LiftDomain period → ℝ, (HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞
      (EulerLiftedGradientSpace.localLift period φ x)) ∧ g =ᵐ[EulerLiftedGradientSpace.liftMeasure
      period] EulerLiftedGradientSpace.liftedGradient period κ m φ})) :
    ⟪g, curlTestLp period κ m i j ψ hψc hψ⟫_ℝ = 0 := by
  obtain ⟨φ, hφ, hgφ⟩ := hg
  rw [L2.inner_def]
  rw [← test_gradient_curl_integral period κ m i j φ ψ hφ.1 hψc hφ.2 hψ]
  apply integral_congr_ae
  filter_upwards [hgφ, curlTestLp_ae period κ m i j ψ hψc hψ] with x hx hy
  rw [hx, hy]

theorem gradient_curl_pairing (κ : ℝ) (m : Vector3) (i j : Fin 3)
    (ψ : LiftDomain period → ℝ) (hψc : HasCompactSupport ψ)
    (hψ : ∀ x, ContDiff ℝ ∞ (localFieldLift period ψ x))
    {p : LiftL2 period} (hp : p ∈ gradientSpace period κ m) :
    ⟪p, curlTestLp period κ m i j ψ hψc hψ⟫_ℝ = 0 := by
  let L := innerSL ℝ (curlTestLp period κ m i j ψ hψc hψ)
  have hspan : Submodule.span ℝ (({g : EulerLiftedGradientSpace.LiftL2 period | ∃ φ :
    EulerLiftedGradientSpace.LiftDomain period → ℝ, (HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞
    (EulerLiftedGradientSpace.localLift period φ x)) ∧ g =ᵐ[EulerLiftedGradientSpace.liftMeasure
    period] EulerLiftedGradientSpace.liftedGradient period κ m φ})) ≤ L.ker := by
    apply Submodule.span_le.mpr
    intro g hg
    change ⟪curlTestLp period κ m i j ψ hψc hψ, g⟫_ℝ = 0
    rw [real_inner_comm]
    exact generator_curl_pairing period κ m i j ψ hψc hψ hg
  have hclosed : IsClosed (L.ker : Set (LiftL2 period)) := L.isClosed_ker
  have hclosure : gradientSpace period κ m ≤ L.ker :=
    Submodule.topologicalClosure_minimal _ hspan hclosed
  have h := hclosure hp
  change ⟪curlTestLp period κ m i j ψ hψc hψ, p⟫_ℝ = 0 at h
  rwa [real_inner_comm] at h

/-- Every field in the closed lifted gradient space has zero distributional lifted curl. -/
theorem gradientSpace_weak_curl_zero (κ : ℝ) (m : Vector3)
    {p : LiftL2 period} (hp : p ∈ gradientSpace period κ m)
    (i j : Fin 3) (ψ : LiftDomain period → ℝ) (hψc : HasCompactSupport ψ)
    (hψ : ∀ x, ContDiff ℝ ∞ (localFieldLift period ψ x)) :
    ∫ x, ((p x) i * fieldDerivative period (coordinateDirection κ m j) ψ x -
      (p x) j * fieldDerivative period (coordinateDirection κ m i) ψ x)
      ∂liftMeasure period = 0 := by
  have h := gradient_curl_pairing period κ m i j ψ hψc hψ hp
  rw [L2.inner_def] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards [curlTestLp_ae period κ m i j ψ hψc hψ] with x hx
  rw [hx, vector_curlTest_inner]

end EulerLiftedCurl
