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
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.SmoothPressureRepresentative

@[expose] public section

noncomputable section

open Set MeasureTheory

namespace EulerTerminalEnergy

open InnerProductSpace

theorem integral_sq_le_length_mul (g : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hg : ContinuousOn g (Icc a b)) :
    (∫ t in a..b, g t) ^ 2 ≤ (b - a) * ∫ t in a..b, (g t) ^ 2 := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  let c := (∫ t in a..b, g t) / (b - a)
  have hgi := hg.intervalIntegrable_of_Icc (μ := volume) hab.le
  have hgs := (hg.pow 2).intervalIntegrable_of_Icc (μ := volume) hab.le
  change IntervalIntegrable (fun t => (g t) ^ 2) volume a b at hgs
  have hn := intervalIntegral.integral_nonneg (μ := volume) hab.le
    (fun t _ => sq_nonneg (g t - c))
  have hex : (fun t => (g t - c) ^ 2) =
      (fun t => (g t) ^ 2 - 2 * c * g t + c ^ 2) := by
    funext t
    ring
  rw [hex, intervalIntegral.integral_add (hgs.sub (hgi.const_mul (2 * c)))
    intervalIntegrable_const, intervalIntegral.integral_sub hgs (hgi.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hn
  simp only [smul_eq_mul] at hn
  have hlen : 0 < b - a := sub_pos.mpr hab
  have hc : c * (b - a) = ∫ t in a..b, g t := div_mul_cancel₀ _ hlen.ne'
  have := mul_nonneg hlen.le hn
  nlinarith [sq_nonneg ((b - a) * c - ∫ t in a..b, g t)]

theorem norm_integral_sq_le_length_mul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : ℝ → E) {a b : ℝ} (hab : a ≤ b)
    (hg : ContinuousOn g (Icc a b)) :
    ‖∫ t in a..b, g t‖ ^ 2 ≤ (b - a) * ∫ t in a..b, ‖g t‖ ^ 2 := by
  have hn := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := g) hab
  have hq := integral_sq_le_length_mul (fun t => ‖g t‖) hab hg.norm
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hq

theorem terminal_trace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (η v : ℝ → E) {S t : ℝ} (ht : t ≤ S)
    (hv : ContinuousOn v (Icc t S))
    (hη : ∀ s ∈ Icc t S, HasDerivAt η (v s) s) (hS : η S = 0) :
    ‖η t‖ ^ 2 ≤ (S - t) * ∫ s in t..S, ‖v s‖ ^ 2 := by
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hη s ((uIcc_of_le ht) ▸ hs))
    (hv.intervalIntegrable_of_Icc ht)
  have hn := norm_integral_sq_le_length_mul v ht hv
  simpa only [he, hS, zero_sub, norm_neg] using hn

theorem terminal_poincare {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (η v : ℝ → E) {S : ℝ} (hS0 : 0 ≤ S)
    (hv : ContinuousOn v (Icc 0 S))
    (hη : ∀ t ∈ Icc 0 S, HasDerivAt η (v t) t) (hS : η S = 0) :
    (∫ t in 0..S, ‖η t‖ ^ 2) ≤ S ^ 2 / 2 * ∫ t in 0..S, ‖v t‖ ^ 2 := by
  let energy := ∫ t in 0..S, ‖v t‖ ^ 2
  have hvi : IntervalIntegrable (fun t => ‖v t‖ ^ 2) volume 0 S :=
    (hv.norm.pow 2).intervalIntegrable_of_Icc hS0
  have hηc : ContinuousOn η (Icc 0 S) :=
    fun t ht => (hη t ht).continuousAt.continuousWithinAt
  have hp : ∀ t ∈ Icc 0 S, ‖η t‖ ^ 2 ≤ (S - t) * energy := by
    intro t ht
    have hsub : Icc t S ⊆ Icc 0 S := Icc_subset_Icc_left ht.1
    have htrace := terminal_trace η v ht.2 (hv.mono hsub)
      (fun s hs => hη s (hsub hs)) hS
    have hi := intervalIntegral.integral_mono_interval (μ := volume)
      ht.1 ht.2 (le_refl S) (Filter.Eventually.of_forall (fun t => sq_nonneg ‖v t‖)) hvi
    exact htrace.trans (mul_le_mul_of_nonneg_left hi (sub_nonneg.mpr ht.2))
  have hm := intervalIntegral.integral_mono_on (μ := volume) hS0
    ((hηc.norm.pow 2).intervalIntegrable_of_Icc hS0)
    (((continuous_const.sub continuous_id).mul continuous_const).intervalIntegrable
      (a := 0) (b := S)) hp
  have he : (∫ t in 0..S, (S - t) * energy) = S ^ 2 / 2 * energy := by
    have hic : IntervalIntegrable (fun _ : ℝ => S) volume 0 S := intervalIntegrable_const
    have hid : IntervalIntegrable (fun t : ℝ => t) volume 0 S :=
      continuous_id.intervalIntegrable 0 S
    rw [intervalIntegral.integral_mul_const,
      intervalIntegral.integral_sub hic hid,
      intervalIntegral.integral_const, integral_id]
    simp only [sub_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), smul_eq_mul]
    ring
  exact hm.trans_eq he

theorem localized_boundary_lower_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (M A R : E →L[ℝ] E) (Be Bc C₁ C₂ r L : ℝ)
    (hBc : 0 ≤ Bc) (hC : 0 ≤ L - Bc * C₁)
    (hA : ∀ z, 0 ≤ ⟪A z, z⟫_ℝ)
    (hM : ∀ z, -Be * ‖z‖ ^ 2 - Bc * ‖R z‖ ^ 2 ≤ ⟪M z, z⟫_ℝ)
    (hR : ∀ z, ‖R z‖ ^ 2 ≤ C₁ * ⟪A z, z⟫_ℝ + C₂ * r ^ 3 * ‖z‖ ^ 2)
    (z : E) :
    -(Be + C₂ * Bc * r ^ 3) * ‖z‖ ^ 2 ≤
      ⟪M z, z⟫_ℝ + L * ⟪A z, z⟫_ℝ := by
  have h1 := mul_le_mul_of_nonneg_left (hR z) hBc
  have h2 := mul_nonneg hC (hA z)
  nlinarith [hM z]

theorem mean_form_coercive {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (η v : ℝ → E) (H : ℝ → E →L[ℝ] E) (M A : E →L[ℝ] E)
    (S K B L : ℝ) (hS0 : 0 ≤ S) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hsmall : K * S ^ 2 / 2 + B * S ≤ 1 / 2)
    (hv : ContinuousOn v (Icc 0 S)) (hH : ContinuousOn H (Icc 0 S))
    (hη : ∀ t ∈ Icc 0 S, HasDerivAt η (v t) t) (hS : η S = 0)
    (hpot : ∀ t ∈ Icc 0 S, ∀ z, ⟪H t z, z⟫_ℝ ≤ K * ‖z‖ ^ 2)
    (hboundary : ∀ z, -B * ‖z‖ ^ 2 ≤ ⟪M z, z⟫_ℝ + L * ⟪A z, z⟫_ℝ) :
    (∫ t in 0..S, ‖v t‖ ^ 2) / 2 ≤
      (∫ t in 0..S, ‖v t‖ ^ 2 - ⟪H t (η t), η t⟫_ℝ) +
        ⟪M (η 0), η 0⟫_ℝ + L * ⟪A (η 0), η 0⟫_ℝ := by
  have hηc : ContinuousOn η (Icc 0 S) :=
    fun t ht => (hη t ht).continuousAt.continuousWithinAt
  have hvi : IntervalIntegrable (fun t => ‖v t‖ ^ 2) volume 0 S :=
    (hv.norm.pow 2).intervalIntegrable_of_Icc hS0
  have hηi : IntervalIntegrable (fun t => ‖η t‖ ^ 2) volume 0 S :=
    (hηc.norm.pow 2).intervalIntegrable_of_Icc hS0
  have hHi : IntervalIntegrable (fun t => ⟪H t (η t), η t⟫_ℝ) volume 0 S :=
    ((hH.clm_apply hηc).inner hηc).intervalIntegrable_of_Icc hS0
  have hip := intervalIntegral.integral_mono_on hS0 hHi (hηi.const_mul K)
    (fun t ht => hpot t ht (η t))
  rw [intervalIntegral.integral_const_mul] at hip
  have htrace := terminal_trace η v hS0 hv hη hS
  simp only [sub_zero] at htrace
  have hpoin := terminal_poincare η v hS0 hv hη hS
  have h1 := mul_le_mul_of_nonneg_left hpoin hK
  have h2 := mul_le_mul_of_nonneg_left htrace hB
  have he : 0 ≤ ∫ t in 0..S, ‖v t‖ ^ 2 :=
    intervalIntegral.integral_nonneg hS0 (fun t _ => sq_nonneg ‖v t‖)
  have h3 := mul_le_mul_of_nonneg_right hsmall he
  rw [intervalIntegral.integral_sub hvi hHi]
  nlinarith [hboundary (η 0)]

end EulerTerminalEnergy
