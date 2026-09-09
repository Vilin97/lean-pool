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
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.Lagrangian

@[expose] public section

noncomputable section

namespace EulerVectorCalculus

open EulerSmoothLimit
open scoped ContDiff

/-- The ordinary coordinate derivative, evaluated using the Fréchet derivative. -/
def partialDerivative (f : Space → ℝ) (i : Fin 3) (x : Space) : ℝ :=
  fderiv ℝ f x (EuclideanSpace.single i 1)

/-- The three-dimensional curl of a vector potential in standard coordinates. -/
def curl (ψ : Fin 3 → Space → ℝ) (x : Space) : Space :=
  (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 3)).symm
    (fun i => partialDerivative (ψ (i + 2)) (i + 1) x -
      partialDerivative (ψ (i + 1)) (i + 2) x)

@[simp] theorem curl_apply (ψ : Fin 3 → Space → ℝ) (x : Space) (i : Fin 3) :
    curl ψ x i = partialDerivative (ψ (i + 2)) (i + 1) x -
      partialDerivative (ψ (i + 1)) (i + 2) x := rfl

theorem contDiff_partialDerivative (f : Space → ℝ) (hf : ContDiff ℝ ∞ f) (i : Fin 3) :
    ContDiff ℝ ∞ (partialDerivative f i) := by
  exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem contDiff_curl (ψ : Fin 3 → Space → ℝ) (hψ : ∀ i, ContDiff ℝ ∞ (ψ i)) :
    ContDiff ℝ ∞ (curl ψ) := by
  apply (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 3)).symm.contDiff.comp
  exact contDiff_pi.mpr (fun i =>
    (contDiff_partialDerivative _ (hψ _) _).sub (contDiff_partialDerivative _ (hψ _) _))

theorem partialDerivative_comm (f : Space → ℝ) (hf : ContDiff ℝ 2 f)
    (i j : Fin 3) (x : Space) :
    partialDerivative (partialDerivative f i) j x =
      partialDerivative (partialDerivative f j) i x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := 1) le_rfl).differentiable one_ne_zero).differentiableAt
  have he (a b : Fin 3) : partialDerivative (partialDerivative f a) b x =
      fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single b 1) (EuclideanSpace.single a 1) := by
    unfold partialDerivative
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  rw [he, he]
  exact (hf.contDiffAt.isSymmSndFDerivAt (n := 2) (by simp)).eq _ _

theorem fderiv_coordinate (f : Space → Space) (x : Space)
    (hf : DifferentiableAt ℝ f x) (i : Fin 3) (v : Space) :
    fderiv ℝ (fun y => f y i) x v = (fderiv ℝ f x v) i := by
  have he : HasFDerivAt (fun y => f y i)
      ((EuclideanSpace.proj i).comp (fderiv ℝ f x)) x :=
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (f x) i).comp x hf.hasFDerivAt
  rw [he.fderiv]
  rfl

theorem divergence_curl (ψ : Fin 3 → Space → ℝ)
    (hψ : ∀ i, ContDiff ℝ ∞ (ψ i)) (x : Space) : divergence (curl ψ) x = 0 := by
  have hc : DifferentiableAt ℝ (curl ψ) x :=
    ((contDiff_curl ψ hψ).differentiable (by simp)).differentiableAt
  have hp (f : Space → ℝ) (hf : ContDiff ℝ ∞ f) (i : Fin 3) :
      DifferentiableAt ℝ (partialDerivative f i) x :=
    ((contDiff_partialDerivative f hf i).differentiable (by simp)).differentiableAt
  have he (i : Fin 3) : (fderiv ℝ (curl ψ) x (EuclideanSpace.single i 1)) i =
      partialDerivative (partialDerivative (ψ (i + 2)) (i + 1)) i x -
        partialDerivative (partialDerivative (ψ (i + 1)) (i + 2)) i x := by
    rw [← fderiv_coordinate _ _ hc i]
    simp only [curl_apply]
    have hd : HasFDerivAt
        (fun y => partialDerivative (ψ (i + 2)) (i + 1) y -
          partialDerivative (ψ (i + 1)) (i + 2) y)
        (fderiv ℝ (partialDerivative (ψ (i + 2)) (i + 1)) x -
          fderiv ℝ (partialDerivative (ψ (i + 1)) (i + 2)) x) x :=
      (hp _ (hψ _) _).hasFDerivAt.sub (hp _ (hψ _) _).hasFDerivAt
    rw [hd.fderiv]
    rfl
  rw [divergence_eq_coordinate_sum, Fin.sum_univ_three, he, he, he]
  change partialDerivative (partialDerivative (ψ 2) 1) 0 x -
    partialDerivative (partialDerivative (ψ 1) 2) 0 x +
    (partialDerivative (partialDerivative (ψ 0) 2) 1 x -
    partialDerivative (partialDerivative (ψ 2) 0) 1 x) +
    (partialDerivative (partialDerivative (ψ 1) 0) 2 x -
    partialDerivative (partialDerivative (ψ 0) 1) 2 x) = 0
  rw [partialDerivative_comm (ψ 2) ((hψ 2).of_le (by simp)) 1 0 x,
    partialDerivative_comm (ψ 0) ((hψ 0).of_le (by simp)) 2 1 x,
    partialDerivative_comm (ψ 1) ((hψ 1).of_le (by simp)) 0 2 x]
  ring

theorem tsupport_curl_subset (ψ : Fin 3 → Space → ℝ) (K : Set Space)
    (hK : IsClosed K) (hψ : ∀ i, tsupport (ψ i) ⊆ K) :
    tsupport (curl ψ) ⊆ K := by
  apply closure_minimal _ hK
  intro x hx
  by_contra hnot
  have hzero : curl ψ x = 0 := by
    ext i
    have h₁ : x ∉ tsupport (ψ (i + 2)) := fun h => hnot (hψ _ h)
    have h₂ : x ∉ tsupport (ψ (i + 1)) := fun h => hnot (hψ _ h)
    simp [curl_apply, partialDerivative, fderiv_of_notMem_tsupport ℝ h₁,
      fderiv_of_notMem_tsupport ℝ h₂]
  exact hx hzero

theorem hasCompactSupport_curl (ψ : Fin 3 → Space → ℝ) (K : Set Space)
    (hK : IsCompact K) (hψ : ∀ i, tsupport (ψ i) ⊆ K) :
    HasCompactSupport (curl ψ) :=
  hK.of_isClosed_subset (isClosed_tsupport _) (tsupport_curl_subset ψ K hK.isClosed hψ)

theorem partialDerivative_odd_of_even (f : Space → ℝ) (hf : Differentiable ℝ f)
    (heven : ∀ x, f (-x) = f x) (i : Fin 3) (x : Space) :
    partialDerivative f i (-x) = -partialDerivative f i x := by
  have he : (fun y => f (-y)) = f := funext heven
  have hd : HasFDerivAt (fun y => f (-y))
      ((fderiv ℝ f (-x)).comp (-ContinuousLinearMap.id ℝ Space)) x :=
    (hf (-x)).hasFDerivAt.comp x (hasFDerivAt_id x).neg
  have hv := congrArg (fun A : Space →L[ℝ] ℝ => A (EuclideanSpace.single i 1)) hd.fderiv
  rw [he] at hv
  simp only [ContinuousLinearMap.comp_apply, neg_apply, ContinuousLinearMap.id_apply,
    map_neg] at hv
  exact neg_eq_iff_eq_neg.mp hv.symm

theorem odd_curl_of_even (ψ : Fin 3 → Space → ℝ)
    (hψ : ∀ i, Differentiable ℝ (ψ i)) (heven : ∀ i x, ψ i (-x) = ψ i x) (x : Space) :
    curl ψ (-x) = -curl ψ x := by
  ext i
  simp only [curl_apply, PiLp.neg_apply,
    partialDerivative_odd_of_even _ (hψ _) (heven _) _ _]
  ring

/-- The vector potential `-x × (L x) / 3` in cyclic coordinates. -/
def linearPotential (L : Space →L[ℝ] Space) (i : Fin 3) (x : Space) : ℝ :=
  (-1 / 3 : ℝ) * (x (i + 1) * (L x) (i + 2) - x (i + 2) * (L x) (i + 1))

theorem contDiff_linearPotential (L : Space →L[ℝ] Space) (i : Fin 3) :
    ContDiff ℝ ∞ (linearPotential L i) := by
  have hc (j : Fin 3) : ContDiff ℝ ∞ (fun x : Space => x j) :=
    (EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff
  have hL (j : Fin 3) : ContDiff ℝ ∞ (fun x : Space => L x j) := (hc j).comp L.contDiff
  exact contDiff_const.mul (((hc _).mul (hL _)).sub ((hc _).mul (hL _)))

theorem linearPotential_even (L : Space →L[ℝ] Space) (i : Fin 3) (x : Space) :
    linearPotential L i (-x) = linearPotential L i x := by
  simp [linearPotential, map_neg, PiLp.neg_apply]

theorem partialDerivative_linearPotential (L : Space →L[ℝ] Space) (i j : Fin 3)
    (x : Space) :
    partialDerivative (linearPotential L i) j x =
      -((EuclideanSpace.single j (1 : ℝ) : Space) (i + 1) * (L x) (i + 2) +
        x (i + 1) * (L (EuclideanSpace.single j 1)) (i + 2) -
        ((EuclideanSpace.single j (1 : ℝ) : Space) (i + 2) * (L x) (i + 1) +
        x (i + 2) * (L (EuclideanSpace.single j 1)) (i + 1))) / 3 := by
  have hc (a : Fin 3) := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 x a
  have hL (a : Fin 3) := (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (L x) a).comp x L.hasFDerivAt
  have hd := (((hc (i + 1)).mul (hL (i + 2))).sub
    ((hc (i + 2)).mul (hL (i + 1)))).const_mul (-1 / 3 : ℝ)
  change HasFDerivAt (linearPotential L i) _ x at hd
  unfold partialDerivative
  rw [hd.fderiv]
  simp only [sub_apply, add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, Function.comp_apply, PiLp.proj_apply, smul_eq_mul]
  ring

theorem curl_linearPotential (L : Space →L[ℝ] Space) (x : Space) :
    curl (linearPotential L) x = L x -
      (LinearMap.trace ℝ Space L.toLinearMap / 3) • x := by
  have hx : (∑ j : Fin 3, x j • (EuclideanSpace.single j 1 : Space)) = x := by
    simpa using (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr x
  have hL (i : Fin 3) : (L x) i =
      ∑ j : Fin 3, x j * (L (EuclideanSpace.single j 1)) i := by
    nth_rw 1 [← hx]
    simp [map_sum, map_smul, smul_eq_mul]
  rw [← coordinateTrace_eq_linearTrace]
  ext i
  fin_cases i <;>
    simp [curl_apply, partialDerivative_linearPotential, coordinateTrace,
      Fin.sum_univ_three, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul, hL] <;> ring

theorem curl_linearPotential_of_trace_zero (L : Space →L[ℝ] Space)
    (hL : LinearMap.trace ℝ Space L.toLinearMap = 0) (x : Space) :
    curl (linearPotential L) x = L x := by
  rw [curl_linearPotential, hL, zero_div, zero_smul, sub_zero]

theorem curl_congr_nhds (ψ φ : Fin 3 → Space → ℝ) (x : Space)
    (h : ∀ i, ψ i =ᶠ[nhds x] φ i) : curl ψ x = curl φ x := by
  ext i
  simp only [curl_apply, partialDerivative, (h (i + 2)).fderiv_eq,
    (h (i + 1)).fderiv_eq]

/-- A trace-free linear velocity has an odd, smooth, compactly supported,
divergence-free extension from any prescribed ball. -/
theorem compact_solenoidal_extension (L : Space →L[ℝ] Space)
    (hL : LinearMap.trace ℝ Space L.toLinearMap = 0)
    (r R : ℝ) (hr : 0 < r) (hrR : r < R) :
    ∃ u : Space → Space, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧
      tsupport u ⊆ Metric.closedBall 0 R ∧
      (∀ x, divergence u x = 0) ∧ (∀ x, u (-x) = -u x) ∧
      (∀ x ∈ Metric.ball 0 r, u x = L x) := by
  let χ : ContDiffBump (0 : Space) := ⟨r, R, hr, hrR⟩
  let ψ : Fin 3 → Space → ℝ := fun i x => χ x * linearPotential L i x
  have hψ (i : Fin 3) : ContDiff ℝ ∞ (ψ i) :=
    χ.contDiff.mul (contDiff_linearPotential L i)
  have hsupport (i : Fin 3) : tsupport (ψ i) ⊆ Metric.closedBall 0 R := by
    have hs : tsupport (ψ i) ⊆ tsupport χ := tsupport_mul_subset_left
    exact hs.trans_eq χ.tsupport_eq
  refine ⟨curl ψ, contDiff_curl ψ hψ,
    hasCompactSupport_curl ψ _ (isCompact_closedBall 0 R) hsupport,
    tsupport_curl_subset ψ _ Metric.isClosed_closedBall hsupport,
    divergence_curl ψ hψ, ?_, ?_⟩
  · intro x
    apply odd_curl_of_even ψ (fun i => (hψ i).differentiable (by simp))
    intro i y
    dsimp [ψ]
    rw [χ.neg, linearPotential_even]
  · intro x hx
    have hχ : (χ : Space → ℝ) =ᶠ[nhds x] 1 := χ.eventuallyEq_one_of_mem_ball hx
    have he (i : Fin 3) : ψ i =ᶠ[nhds x] linearPotential L i := by
      filter_upwards [hχ] with y hy
      change χ y * linearPotential L i y = linearPotential L i y
      rw [hy]
      exact one_mul _
    rw [curl_congr_nhds ψ (linearPotential L) x he,
      curl_linearPotential_of_trace_zero L hL]

end EulerVectorCalculus
