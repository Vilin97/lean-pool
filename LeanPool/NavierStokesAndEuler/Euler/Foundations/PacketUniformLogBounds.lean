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
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketUniformScaleSums

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace EulerPacketUniformLogBounds

open Real EulerScale EulerPacketUniformScaleSums

/-- Every fixed polynomial logarithm is bounded by a simple product of
the stage and the square root of the scale. -/
theorem polynomial_log_bound {j X C p q : ℝ} (hj : 1 ≤ j) (hX : 1 ≤ X) :
    C + p * log j + q * log X ≤ (|C| + |p| + 2 * |q|) * j * sqrt X := by
  have hjp : 0 < j := by linarith
  have hXp : 0 < X := by linarith
  have hs : 1 ≤ sqrt X := one_le_sqrt.mpr hX
  have hsj : 1 ≤ j * sqrt X := one_le_mul_of_one_le_of_one_le hj hs
  have hlj : 0 ≤ log j := log_nonneg hj
  have hlX : 0 ≤ log X := log_nonneg hX
  have hljb : log j ≤ j := (log_le_sub_one_of_pos hjp).trans (by linarith)
  have hlXb : log X ≤ 2 * sqrt X := by
    have hh := log_le_sub_one_of_pos (sqrt_pos.mpr hXp)
    rw [log_sqrt hXp.le] at hh
    linarith
  have hCb : C ≤ |C| * j * sqrt X := by
    have hh := mul_le_mul_of_nonneg_left hsj (abs_nonneg C)
    nlinarith only [hh, le_abs_self C]
  have hp₁ := mul_le_mul_of_nonneg_right (le_abs_self p) hlj
  have hp₂ := mul_le_mul_of_nonneg_left hljb (abs_nonneg p)
  have hp₃ := mul_le_mul_of_nonneg_left hs (mul_nonneg (abs_nonneg p) hjp.le)
  have hq₁ := mul_le_mul_of_nonneg_right (le_abs_self q) hlX
  have hq₂ := mul_le_mul_of_nonneg_left hlXb (abs_nonneg q)
  have hq₃ := mul_le_mul_of_nonneg_right hj (mul_nonneg (by positivity : 0 ≤ 2 * |q|) (sqrt_nonneg
    X))
  nlinarith only [hCb, hp₁, hp₂, hp₃, hq₁, hq₂, hq₃]

/-- A single explicit lower bound on the initial scale absorbs the
polynomial logarithms at every subsequent quadratic stage. -/
theorem polynomial_logs_uniformly_absorbed
    (J A : ℕ) (hJ : 1 ≤ J)
    (hJA : (2 : ℝ) ^ (2 * A + 3) ≤ (J : ℝ) ^ 2)
    (x : ℕ → ℝ) (hx0 : 1 ≤ x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (C p q b : ℝ) (hb : 0 < b)
    (hlarge : (2 * (|C| + |p| + 2 * |q|) / b) ^ 2 * (J : ℝ) ^ (2 * A + 2) ≤ x 0) :
    ∀ n, C + p * log ((J + n : ℕ) : ℝ) + q * log (x n) ≤
      (b / 2) * (x n / ((J + n : ℕ) : ℝ) ^ A) := by
  let S := |C| + |p| + 2 * |q|
  let L := 2 * S / b
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hJp : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hx1 := quadratic_growth_one_le J hJ x hx0 hx
  have hgeom := polynomial_scale_geometric_lower J (2 * A + 2) hJ
    (by simpa only [show 2 * A + 2 + 1 = 2 * A + 3 by omega] using hJA) x (by linarith) hx
  intro n
  have hj1 : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
  have hj : (0 : ℝ) < (J + n : ℕ) := by linarith
  have hstart : L ^ 2 ≤ x 0 / (J : ℝ) ^ (2 * A + 2) := by
    apply (le_div_iff₀ (pow_pos hJp _)).2
    exact hlarge
  have hone : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hbase := mul_le_mul_of_nonneg_right hone
    (div_nonneg (le_trans zero_le_one hx0) (pow_nonneg hJp.le (2 * A + 2)))
  have hscale : L ^ 2 ≤ x n / ((J + n : ℕ) : ℝ) ^ (2 * A + 2) := by
    nlinarith only [hstart, hbase, hgeom n]
  have hsquare := (le_div_iff₀ (pow_pos hj (2 * A + 2))).mp hscale
  have hroot : L * ((J + n : ℕ) : ℝ) ^ (A + 1) ≤ sqrt (x n) := by
    have hp : (((J + n : ℕ) : ℝ) ^ (A + 1)) ^ 2 = ((J + n : ℕ) : ℝ) ^ (2 * A + 2) := by
      rw [← pow_mul]
      congr 1
      omega
    have hs := sq_sqrt (le_trans zero_le_one (hx1 n))
    have hn : 0 ≤ L * ((J + n : ℕ) : ℝ) ^ (A + 1) := by positivity
    nlinarith only [hsquare, hp, hs, hn, sqrt_nonneg (x n)]
  have hlog := polynomial_log_bound (C := C) (p := p) (q := q) hj1 (hx1 n)
  have hlogmul := mul_le_mul_of_nonneg_right hlog (pow_nonneg hj.le A)
  have hrootmul := mul_le_mul_of_nonneg_right hroot
    (mul_nonneg (div_nonneg hb.le (by norm_num : (0 : ℝ) ≤ 2)) (sqrt_nonneg (x n)))
  have hLS : (b / 2) * L = S := by dsimp [L]; field_simp
  have hid : (b / 2) * (x n / ((J + n : ℕ) : ℝ) ^ A) =
      ((b / 2) * x n) / ((J + n : ℕ) : ℝ) ^ A := by ring
  rw [hid]
  apply (le_div_iff₀ (pow_pos hj A)).2
  have hmul : S * ((J + n : ℕ) : ℝ) ^ (A + 1) * sqrt (x n) ≤ (b / 2) * x n := by
    calc
      _ = (L * ((J + n : ℕ) : ℝ) ^ (A + 1)) * ((b / 2) * sqrt (x n)) := by rw [← hLS]; ring
      _ ≤ sqrt (x n) * ((b / 2) * sqrt (x n)) := hrootmul
      _ = (b / 2) * (sqrt (x n)) ^ 2 := by ring
      _ = _ := by rw [sq_sqrt (le_trans zero_le_one (hx1 n))]
  rw [pow_succ] at hmul
  dsimp only [S] at hmul
  nlinarith only [hlogmul, hmul]

end EulerPacketUniformLogBounds
