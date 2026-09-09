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
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PressureGevrey

@[expose] public section

noncomputable section

/-!
The smooth compactly supported limit step for the proposed Euler construction.
The hypotheses are summable uniform estimates for every actual iterated Fréchet
derivative of the increments. Smoothness and convergence of the limit are proved,
not assumed. The divergence is the usual coordinate trace of the first derivative.
-/

namespace EulerSmoothLimit

open Filter MeasureTheory
open scoped Topology ContDiff ENNReal

/-- The physical three-dimensional Euclidean space. -/
abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- The trace of a continuous linear map, written in the standard Euclidean coordinates. -/
noncomputable def coordinateTrace : (Space →L[ℝ] Space) →L[ℝ] ℝ :=
  ∑ i : Fin 3, (EuclideanSpace.proj i).comp
    (ContinuousLinearMap.apply ℝ Space (EuclideanSpace.single i 1))

/-- The coordinate formula is exactly the basis-independent linear-algebraic trace. -/
theorem coordinateTrace_eq_linearTrace (A : Space →L[ℝ] Space) :
    coordinateTrace A = LinearMap.trace ℝ Space A.toLinearMap := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis]
  simp [coordinateTrace, Matrix.trace, LinearMap.toMatrix_apply]

/-- Classical divergence, defined canonically as the trace of the Fréchet derivative. -/
noncomputable def divergence (f : Space → Space) (x : Space) : ℝ :=
  LinearMap.trace ℝ Space (fderiv ℝ f x).toLinearMap

theorem divergence_eq_coordinate_sum (f : Space → Space) (x : Space) :
    divergence f x = ∑ i : Fin 3, (fderiv ℝ f x (EuclideanSpace.single i 1)) i := by
  rw [divergence, ← coordinateTrace_eq_linearTrace]
  simp [coordinateTrace]

theorem divergence_eq_trace (f : Space → Space) (x : Space) :
    divergence f x = LinearMap.trace ℝ Space (fderiv ℝ f x).toLinearMap :=
  rfl

/-- Order-zero bounds prove actual pointwise convergence of the series. -/
theorem summable_values (f : ℕ → Space → Space) (v : ℕ → ℕ → ℝ)
    (hv : ∀ k, Summable (v k))
    (hb : ∀ k n x, ‖iteratedFDeriv ℝ k (f n) x‖ ≤ v k n) (x : Space) :
    Summable (fun n => f n x) := by
  apply Summable.of_norm_bounded (hv 0)
  intro n
  simpa only [norm_iteratedFDeriv_zero] using hb 0 n x

/-- Uniform convergence of the ordinary sequence of finite partial sums. -/
theorem uniform_convergence (f : ℕ → Space → Space) (v : ℕ → ℕ → ℝ)
    (hv : ∀ k, Summable (v k))
    (hb : ∀ k n x, ‖iteratedFDeriv ℝ k (f n) x‖ ≤ v k n) :
    TendstoUniformly (fun N x => ∑ n ∈ Finset.range N, f n x)
      (fun x => ∑' n, f n x) atTop := by
  apply tendstoUniformly_tsum_nat (hv 0)
  intro n x
  simpa only [norm_iteratedFDeriv_zero] using hb 0 n x

/-- Every order of differentiability is retained by the convergent series. -/
theorem contDiff_sum (f : ℕ → Space → Space) (v : ℕ → ℕ → ℝ)
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) (hv : ∀ k, Summable (v k))
    (hb : ∀ k n x, ‖iteratedFDeriv ℝ k (f n) x‖ ≤ v k n) :
    ContDiff ℝ ∞ (fun x => ∑' n, f n x) := by
  exact contDiff_tsum hf (fun k _ => hv k) (fun k n x _ => hb k n x)

/-- All iterated derivatives of the sum are the sums of the actual derivatives. -/
theorem iterated_derivative_sum (f : ℕ → Space → Space) (v : ℕ → ℕ → ℝ)
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) (hv : ∀ k, Summable (v k))
    (hb : ∀ k n x, ‖iteratedFDeriv ℝ k (f n) x‖ ≤ v k n) (k : ℕ) (x : Space) :
    iteratedFDeriv ℝ k (fun y => ∑' n, f n y) x = ∑' n, iteratedFDeriv ℝ k (f n) x := by
  exact iteratedFDeriv_tsum_apply hf (fun j _ => hv j) (fun j n y _ => hb j n y) le_top x

/-- Uniform convergence holds separately at every derivative order. -/
theorem uniform_derivative_convergence (f : ℕ → Space → Space) (v : ℕ → ℕ → ℝ)
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) (hv : ∀ k, Summable (v k))
    (hb : ∀ k n x, ‖iteratedFDeriv ℝ k (f n) x‖ ≤ v k n) (k : ℕ) :
    TendstoUniformly (fun N x => ∑ n ∈ Finset.range N, iteratedFDeriv ℝ k (f n) x)
      (iteratedFDeriv ℝ k (fun x => ∑' n, f n x)) atTop := by
  rw [iteratedFDeriv_tsum hf (fun j _ => hv j) (fun j n x _ => hb j n x) le_top]
  exact tendstoUniformly_tsum_nat (hv k) (fun n x => hb k n x)

/-- A common closed support set also contains the topological support of the sum. -/
theorem tsupport_sum_subset (f : ℕ → Space → Space) (K : Set Space) (hK : IsClosed K)
    (hsupp : ∀ n, Function.support (f n) ⊆ K) :
    tsupport (fun x => ∑' n, f n x) ⊆ K := by
  apply closure_minimal _ hK
  intro x hx
  by_contra hxK
  have hz : ∀ n, f n x = 0 := by
    intro n
    by_contra hn
    exact hxK (hsupp n hn)
  exact hx (by simp [hz])

/-- Compact support follows from the prescribed common compact set. -/
theorem compactSupport_sum (f : ℕ → Space → Space) (K : Set Space) (hK : IsCompact K)
    (hsupp : ∀ n, Function.support (f n) ⊆ K) :
    HasCompactSupport (fun x => ∑' n, f n x) :=
  hK.of_isClosed_subset (isClosed_tsupport _) (tsupport_sum_subset f K hK.isClosed hsupp)

/-- The divergence of the series is the series of the divergences. -/
theorem divergence_sum (f : ℕ → Space → Space) (v : ℕ → ℕ → ℝ)
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) (hv : ∀ k, Summable (v k))
    (hb : ∀ k n x, ‖iteratedFDeriv ℝ k (f n) x‖ ≤ v k n) (x : Space) :
    divergence (fun y => ∑' n, f n y) x = ∑' n, divergence (f n) x := by
  have hd : ∀ n y, ‖fderiv ℝ (f n) y‖ ≤ v 1 n := by
    intro n y
    simpa only [norm_iteratedFDeriv_one] using hb 1 n y
  have hsd : Summable (fun n => fderiv ℝ (f n) x) :=
    Summable.of_norm_bounded (hv 1) (fun n => hd n x)
  simp only [divergence, ← coordinateTrace_eq_linearTrace]
  rw [fderiv_tsum_apply (hv 1) (fun n => (hf n).differentiable (by simp)) hd
    (summable_values f v hv hb (0 : Space)) x]
  exact coordinateTrace.map_tsum hsd

/-- The solenoidal condition is preserved by the series. -/
theorem divergence_free_sum (f : ℕ → Space → Space) (v : ℕ → ℕ → ℝ)
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) (hv : ∀ k, Summable (v k))
    (hb : ∀ k n x, ‖iteratedFDeriv ℝ k (f n) x‖ ≤ v k n)
    (hdiv : ∀ n x, divergence (f n) x = 0) :
    ∀ x, divergence (fun y => ∑' n, f n y) x = 0 := by
  intro x
  rw [divergence_sum f v hf hv hb x]
  simp [hdiv]

/-- The common-support smooth limit belongs to every `L^p`, in particular to `L²`. -/
theorem memLp_sum (f : ℕ → Space → Space) (v : ℕ → ℕ → ℝ)
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) (hv : ∀ k, Summable (v k))
    (hb : ∀ k n x, ‖iteratedFDeriv ℝ k (f n) x‖ ≤ v k n)
    (K : Set Space) (hK : IsCompact K) (hsupp : ∀ n, Function.support (f n) ⊆ K)
    (p : ℝ≥0∞) : MemLp (fun x => ∑' n, f n x) p volume :=
  (contDiff_sum f v hf hv hb).continuous.memLp_of_hasCompactSupport
    (compactSupport_sum f K hK hsupp)

/-- Every derivative of the limit is also in every `L^p`. -/
theorem memLp_iterated_derivative_sum (f : ℕ → Space → Space) (v : ℕ → ℕ → ℝ)
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) (hv : ∀ k, Summable (v k))
    (hb : ∀ k n x, ‖iteratedFDeriv ℝ k (f n) x‖ ≤ v k n)
    (K : Set Space) (hK : IsCompact K) (hsupp : ∀ n, Function.support (f n) ⊆ K)
    (k : ℕ) (p : ℝ≥0∞) :
    MemLp (iteratedFDeriv ℝ k (fun x => ∑' n, f n x)) p volume := by
  have hc : Continuous (iteratedFDeriv ℝ k (fun x => ∑' n, f n x)) :=
    ContDiff.continuous_iteratedFDeriv (by simp) (contDiff_sum f v hf hv hb)
  exact hc.memLp_of_hasCompactSupport ((compactSupport_sum f K hK hsupp).iteratedFDeriv k)

/-- Finite kinetic energy is obtained as integrability of the squared Euclidean norm. -/
theorem finite_energy_sum (f : ℕ → Space → Space) (v : ℕ → ℕ → ℝ)
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) (hv : ∀ k, Summable (v k))
    (hb : ∀ k n x, ‖iteratedFDeriv ℝ k (f n) x‖ ≤ v k n)
    (K : Set Space) (hK : IsCompact K) (hsupp : ∀ n, Function.support (f n) ⊆ K) :
    Integrable (fun x => ‖∑' n, f n x‖ ^ 2) volume :=
  (memLp_sum f v hf hv hb K hK hsupp 2).integrable_norm_pow (by norm_num)

/-- Odd parity also passes to the pointwise series. -/
theorem odd_sum (f : ℕ → Space → Space) (hodd : ∀ n x, f n (-x) = -f n x) :
    ∀ x, (∑' n, f n (-x)) = -(∑' n, f n x) := by
  intro x
  simp [hodd, tsum_neg]

/--
Constructs the limit initial velocity with all required qualitative properties.
The pointwise `HasSum` and uniform-convergence conclusions ensure the result is
the actual series, and every derivative order is shown to commute with that sum.
-/
theorem smooth_compact_solenoidal_limit (f : ℕ → Space → Space) (v : ℕ → ℕ → ℝ)
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) (hv : ∀ k, Summable (v k))
    (hb : ∀ k n x, ‖iteratedFDeriv ℝ k (f n) x‖ ≤ v k n)
    (K : Set Space) (hK : IsCompact K) (hsupp : ∀ n, Function.support (f n) ⊆ K)
    (hdiv : ∀ n x, divergence (f n) x = 0) :
    ∃ u : Space → Space,
      (∀ x, HasSum (fun n => f n x) (u x)) ∧
      TendstoUniformly (fun N x => ∑ n ∈ Finset.range N, f n x) u atTop ∧
      ContDiff ℝ ∞ u ∧ tsupport u ⊆ K ∧ HasCompactSupport u ∧
      MemLp u 2 volume ∧ Integrable (fun x => ‖u x‖ ^ 2) volume ∧
      (∀ x, divergence u x = 0) ∧
      (∀ k x, iteratedFDeriv ℝ k u x = ∑' n, iteratedFDeriv ℝ k (f n) x) := by
  refine ⟨fun x => ∑' n, f n x, ?_⟩
  exact ⟨fun x => (summable_values f v hv hb x).hasSum,
    uniform_convergence f v hv hb,
    contDiff_sum f v hf hv hb,
    tsupport_sum_subset f K hK.isClosed hsupp,
    compactSupport_sum f K hK hsupp,
    memLp_sum f v hf hv hb K hK hsupp 2,
    finite_energy_sum f v hf hv hb K hK hsupp,
    divergence_free_sum f v hf hv hb hdiv,
    iterated_derivative_sum f v hf hv hb⟩

end EulerSmoothLimit
