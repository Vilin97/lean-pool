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
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.AnglePartition

@[expose] public section

noncomputable section

namespace EulerEnergyBootstrap

open Set Real

theorem radius_bounds (C B Δ ρ₀ S R₀ : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hΔ : 0 ≤ Δ) (hρ : 0 < ρ₀) (_hS : 0 ≤ S) (hR : 0 ≤ R₀)
    (hdecay : 2 * C * (B + Δ) * S ≤ ρ₀ / 2) (hscale : ρ₀ * R₀ ≤ 1)
    (t : ℝ) (ht : t ∈ Icc 0 S) :
    ρ₀ / 2 ≤ ρ₀ - 2 * C * (B + Δ) * t ∧
      0 < ρ₀ - 2 * C * (B + Δ) * t ∧
      (ρ₀ - 2 * C * (B + Δ) * t) * R₀ ≤ 1 := by
  have hl := mul_le_mul_of_nonneg_left ht.2 (show 0 ≤ 2 * C * (B + Δ) by positivity)
  have hn := mul_nonneg (show 0 ≤ 2 * C * (B + Δ) by positivity) ht.1
  constructor
  · linarith
  constructor
  · linarith
  · nlinarith

theorem shrinking_radius_cancels_loss (C B Δ ρ R₀ X : ℝ)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hΔ : 0 ≤ Δ) (hρ : 0 < ρ)
    (hR : 0 ≤ R₀) (hscale : ρ * R₀ ≤ 1) (hX : X ≤ Δ) :
    (-2 * C * (B + Δ)) / ρ + C * (ρ⁻¹ + R₀) * (B + X) ≤ 0 := by
  have hinv : R₀ ≤ ρ⁻¹ := by
    rw [inv_eq_one_div]
    exact (le_div_iff₀ hρ).2 (by nlinarith)
  have hp : C * (ρ⁻¹ + R₀) * (B + X) ≤ C * (ρ⁻¹ + R₀) * (B + Δ) := by
    gcongr
  have hq : C * (ρ⁻¹ + R₀) * (B + Δ) ≤ 2 * C * (B + Δ) / ρ := by
    calc
      _ ≤ C * (ρ⁻¹ + ρ⁻¹) * (B + Δ) := by gcongr
      _ = _ := by ring
  have hneg : (-2 * C * (B + Δ)) / ρ = -(2 * C * (B + Δ) / ρ) := by ring
  rw [hneg]
  linarith

/-- The shrinking-radius energy inequality closes without assuming the bootstrap conclusion. -/
theorem close_energy_estimate
    (X X' Y : ℝ → ℝ) (C B Δ r ρ₀ S R₀ : ℝ)
    (hC : 0 < C) (hB : 0 ≤ B) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (hr : 0 < r) (hρ : 0 < ρ₀) (hS : 0 ≤ S) (hR : 0 ≤ R₀)
    (hdecay : 2 * C * (B + Δ) * S ≤ ρ₀ / 2) (hscale : ρ₀ * R₀ ≤ 1)
    (hsmall : 2 * r * exp (3 * C * S) ≤ Δ / 2)
    (hcont : ContinuousOn X (Icc 0 S)) (hinit : X 0 ≤ 2 * r)
    (hder : ∀ t ∈ Ico 0 S, HasDerivAt X (X' t) t)
    (hY : ∀ t ∈ Ico 0 S, 0 ≤ Y t)
    (hineq : ∀ t ∈ Ico 0 S,
      X' t ≤ C * (X t + (X t) ^ 2 + r) +
        ((-2 * C * (B + Δ)) / (ρ₀ - 2 * C * (B + Δ) * t) +
          C * ((ρ₀ - 2 * C * (B + Δ) * t)⁻¹ + R₀) * (B + X t)) * Y t) :
    ∀ t ∈ Icc 0 S, X t ≤ 2 * r * exp (3 * C * t) ∧ X t ≤ Δ / 2 := by
  let F : ℝ → ℝ := fun t => 2 * r * exp (3 * C * t)
  have hF (t : ℝ) : HasDerivAt F (3 * C * F t) t := by
    have hlin : HasDerivAt (fun s : ℝ => 3 * C * s) (3 * C) t := by
      simpa using (hasDerivAt_id t).const_mul (3 * C)
    change HasDerivAt (fun s => 2 * r * exp (3 * C * s))
      (3 * C * (2 * r * exp (3 * C * t))) t
    exact (hlin.exp.const_mul (2 * r)).congr_deriv (by ring)
  have hFle (t : ℝ) (ht : t ∈ Icc 0 S) : F t ≤ Δ / 2 := by
    calc
      F t ≤ 2 * r * exp (3 * C * S) := by dsimp [F]; gcongr; exact ht.2
      _ ≤ _ := hsmall
  have hFp (t : ℝ) : 0 < F t := by dsimp [F]; positivity
  have hFbase (t : ℝ) (ht : 0 ≤ t) : 2 * r ≤ F t := by
    have he : 1 ≤ exp (3 * C * t) := one_le_exp_iff.mpr (by positivity)
    dsimp [F]
    nlinarith
  have hbound : ∀ t ∈ Icc 0 S, X t ≤ F t := by
    apply image_le_of_deriv_right_lt_deriv_boundary hcont
      (fun t ht => (hder t ht).hasDerivWithinAt)
    · simpa only [F, mul_zero, exp_zero, mul_one] using hinit
    · exact hF
    · intro t ht hXF
      have htc : t ∈ Icc 0 S := ⟨ht.1, ht.2.le⟩
      have hrad := radius_bounds C B Δ ρ₀ S R₀ hC.le hB hΔ.le hρ hS hR hdecay hscale t htc
      have hloss := shrinking_radius_cancels_loss C B Δ _ R₀ (X t)
        hC.le hB hΔ.le hrad.2.1 hR hrad.2.2 (by rw [hXF]; linarith [hFle t htc])
      have hlossY := mul_nonpos_of_nonpos_of_nonneg hloss (hY t ht)
      have hmain := hineq t ht
      have hFt := hFp t
      have hFΔ := hFle t htc
      have hFr := hFbase t ht.1
      rw [hXF] at hmain hlossY
      have hFsq : (F t) ^ 2 ≤ F t := by nlinarith
      have hCsq := mul_le_mul_of_nonneg_left hFsq hC.le
      have hCr := mul_le_mul_of_nonneg_left hFr hC.le
      have hpos := mul_pos hC hFt
      nlinarith
  intro t ht
  exact ⟨hbound t ht, (hbound t ht).trans (hFle t ht)⟩

/-- Uniform stability from a quadratic differential inequality and small initial error. -/
theorem quadratic_stability (X X' : ℝ → ℝ) (C ε S : ℝ)
    (hC : 0 < C) (hε : 0 < ε) (hS : 0 ≤ S)
    (hsmall : 2 * ε * exp (3 * C * S) ≤ 1 / 2)
    (hcont : ContinuousOn X (Icc 0 S)) (hinit : X 0 ≤ ε)
    (hder : ∀ t ∈ Ico 0 S, HasDerivAt X (X' t) t)
    (hineq : ∀ t ∈ Ico 0 S, X' t ≤ C * (X t + (X t) ^ 2)) :
    ∀ t ∈ Icc 0 S, X t ≤ 2 * ε * exp (3 * C * S) := by
  have hρ : 0 < 4 * C * S + 1 := by positivity
  have h := close_energy_estimate X X' (fun _ => 0) C 0 1 ε (4 * C * S + 1) S 0
    hC (by norm_num) (by norm_num) (by norm_num) hε hρ hS (by norm_num)
    (by nlinarith) (by simp) hsmall hcont (by linarith) hder
    (fun _ _ => le_rfl) (fun t ht => by
      have hi := hineq t ht
      simp only [mul_zero, add_zero]
      nlinarith)
  intro t ht
  exact (h t ht).1.trans (by gcongr; exact ht.2)

end EulerEnergyBootstrap
