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
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketCoefficientControl

@[expose] public section

noncomputable section

open Set

namespace EulerPacketTargetCompression

open Real EulerPacketRay EulerPacketFrameRenewal EulerPacketFrameQuantitative

/-- The common `Θ^40` smallness regime guarantees every sign and
denominator condition used in the perturbed target compression estimate. -/
theorem target_compression_order40
    {β t Θ K e ε H P Q N : ℝ}
    (hβ : 0 < β) (hβupper : β ≤ 1) (ht : 0 < t) (htΘ : t ≤ Θ)
    (hΘ : 1 ≤ Θ) (hK : 1 ≤ K) (he : 0 ≤ e) (hε : 0 ≤ ε) (hεe : ε ≤ e) (hH : 0 ≤ H)
    (hsmall : 1000000 * K * e * Θ ^ 40 ≤ 1) (hscale : 1 ≤ β * t ^ 2)
    (hP : |P - β * t ^ 2| ≤ 800 * e * Θ ^ 5)
    (hQ : |Q + 2 * β * t| ≤ 800 * e * Θ ^ 5)
    (hN : |N - 1| ≤ 800 * e * Θ ^ 5) :
    0 < rayDenominator ε P Q N ∧
      H * ε * Q * P / rayDenominator ε P Q N ≤ -(H * ε) / (10 * t) := by
  let ρ := 800 * e * Θ ^ 5
  let M := K * e * Θ ^ 40
  have hΘpos : 0 < Θ := by linarith
  have hρ : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hMb : 1000000 * M ≤ 1 := by dsimp [M]; nlinarith only [hsmall]
  have hp (n : ℕ) (hn : n ≤ 40) : e * Θ ^ n ≤ M := scaled_power_le hΘ hK he hn
  have hρsmall : ρ ≤ 1 / 2 := by
    have hh := hp 5 (by decide)
    dsimp [ρ]
    nlinarith only [hh, hMb]
  have hρΘ : ρ * Θ ≤ 1 := by
    have hh := hp 6 (by decide)
    dsimp [ρ]
    nlinarith only [hh, hMb]
  have hβtΘ : 1 ≤ β * t * Θ := by
    have hh := mul_le_mul_of_nonneg_left htΘ (mul_nonneg hβ.le ht.le)
    nlinarith only [hh, hscale]
  have hρQ : ρ ≤ β * t := by
    apply (mul_le_mul_iff_right₀ hΘpos).mp
    nlinarith only [hρΘ, hβtΘ]
  have hQ₀ : |-2 * β * t| ≤ 2 * Θ ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_pos hβ, abs_of_pos ht]
    norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hh := mul_le_mul_of_nonneg_right hβupper ht.le
    have hΘ2 : Θ ≤ Θ ^ 2 := by nlinarith only [hΘ]
    nlinarith only [hh, htΘ, hΘ2]
  have hQabs : |Q| ≤ 3 * Θ ^ 2 := by
    have hh := abs_add_le (Q + 2 * β * t) (-2 * β * t)
    have hid : Q + 2 * β * t + -2 * β * t = Q := by ring
    rw [hid] at hh
    have hΘ2 : 1 ≤ Θ ^ 2 := one_le_pow₀ hΘ
    change |Q + 2 * β * t| ≤ ρ at hQ
    nlinarith only [hh, hQ, hQ₀, hρsmall, hΘ2]
  have hεQ : |ε * Q| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_nonneg hε]
    have hh := mul_le_mul hεe hQabs (abs_nonneg Q) he
    have hm := hp 2 (by decide)
    nlinarith only [hh, hm, hMb]
  have hPpos : 0 < P := by
    have hh := (abs_le.mp hP).1
    change ρ ≤ 1 / 2 at hρsmall
    dsimp [ρ] at hρsmall
    nlinarith only [hh, hρsmall, hscale]
  have hDpos : 0 < rayDenominator ε P Q N := by
    unfold rayDenominator
    have hh : 0 < P ^ 2 := sq_pos_of_pos hPpos
    positivity
  exact ⟨hDpos, perturbed_target_compression hβ ht hε hH hscale hρ hρsmall hρQ hP hQ hN hεQ⟩

/-- The full parent matrix has strictly negative target-ray compression
once its shear contribution dominates the older-gradient error. -/
theorem full_target_compression_negative
    {B E : Fin 3 → Fin 3 → ℝ} {H ε P Q N G t : ℝ}
    (ht : 0 < t) (hD : 0 < rayDenominator ε P Q N)
    (hB : ∀ i j, |B i j + E i j| ≤ G)
    (hShear : H * ε * Q * P / rayDenominator ε P Q N ≤ -(H * ε) / (10 * t))
    (hdominates : 30 * G * t < H * ε) :
    quadraticForm3 (parentEntry B E H) P (ε * Q) N / rayDenominator ε P Q N < 0 := by
  have hfull := parent_ray_compression (H := H) hD hB
  have hdom : 3 * G < H * ε / (10 * t) := (lt_div_iff₀ (by positivity : 0 < 10 * t)).mpr
    (by nlinarith only [hdominates])
  rw [neg_div] at hShear
  nlinarith only [hfull, hShear, hdom]

end EulerPacketTargetCompression
