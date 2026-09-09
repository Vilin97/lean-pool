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
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.IntervalTrace

@[expose] public section

noncomputable section

/-! Quantitative endpoint selection in the activation step, equations (26)–(27). -/

namespace EulerDNSelection

open InnerProductSpace

theorem positive_cross_sq_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (Λ : E →L[ℝ] E) (hΛ : Λ.IsPositive) (p q : E) :
    ⟪Λ p, q⟫_ℝ ^ 2 ≤ ⟪Λ p, p⟫_ℝ * ⟪Λ q, q⟫_ℝ := by
  have hsym : ⟪Λ q, p⟫_ℝ = ⟪Λ p, q⟫_ℝ := by
    rw [hΛ.inner_left_eq_inner_right, real_inner_comm]
  have hquad : ∀ t : ℝ, 0 ≤ ⟪Λ p, p⟫_ℝ * (t * t) +
      (2 * ⟪Λ p, q⟫_ℝ) * t + ⟪Λ q, q⟫_ℝ := by
    intro t
    have ht := hΛ.inner_nonneg_left (t • p + q)
    simp only [map_add, map_smul, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, hsym] at ht
    nlinarith
  have hd := discrim_le_zero hquad
  unfold discrim at hd
  nlinarith

/-- A positive semidefinite endpoint matrix, perturbed by a unit shear and a small
matrix with negative first diagonal entry, allows the required polarized output. -/
theorem select_endpoint
    (C ε a b d cpp cpq cqp cqq : ℝ)
    (hC : 1 ≤ C) (hε : 0 ≤ ε) (hsmall : 16 * (C + 1) * ε ≤ 1)
    (ha : 0 ≤ a) (had : b ^ 2 ≤ a * d) (hd : 0 ≤ d)
    (haC : a ≤ C) (hbC : |b| ≤ C)
    (hpp : cpp < 0) (hppε : |cpp| ≤ ε)
    (hpq : |cpq| ≤ ε) (hqp : |cqp| ≤ ε) (hqq : |cqq| ≤ ε) :
    ∃ yp yq : ℝ,
      (b - 1 - cqp) * yp + (d - cqq) * yq = 1 ∧
      -8 * (C + 1) ≤ (a - cpp) * yp + (b - cpq) * yq ∧
      (a - cpp) * yp + (b - cpq) * yq ≤ 0 ∧
      |yp| + |yq| ≤ 8 * (C + 1) := by
  have hεsmall : ε ≤ 1 / 16 := by
    nlinarith [mul_nonneg (show 0 ≤ C by linarith) hε]
  have hu : 0 < a - cpp := by linarith
  have huC : a - cpp ≤ C + ε := by
    have := (abs_le.mp hppε).1
    linarith
  rcases le_or_gt b (1 / 2) with hb | hb
  · let D := 1 + cqp - b
    have hD : 1 / 3 ≤ D := by
      have := (abs_le.mp hqp).1
      dsimp [D]
      linarith
    have hDpos : 0 < D := by linarith
    have hDne : D ≠ 0 := ne_of_gt hDpos
    have hquot : (a - cpp) / D ≤ 8 * (C + 1) := by
      apply (div_le_iff₀ hDpos).2
      nlinarith [mul_nonneg (show 0 ≤ C + 1 by linarith)
        (show 0 ≤ D - 1 / 3 by linarith)]
    have hinv : 1 / D ≤ 3 := (div_le_iff₀ hDpos).2 (by linarith)
    refine ⟨-1 / D, 0, ?_, ?_, ?_, ?_⟩
    · have heq : b - 1 - cqp = -D := by dsimp [D]; ring
      rw [heq, mul_zero, add_zero]
      field_simp
    · have heq : (a - cpp) * (-1 / D) + (b - cpq) * 0 = -(a - cpp) / D := by ring
      rw [heq, neg_div]
      linarith
    · have heq : (a - cpp) * (-1 / D) + (b - cpq) * 0 = -((a - cpp) / D) := by ring
      rw [heq]
      exact neg_nonpos.mpr (div_nonneg hu.le hDpos.le)
    · simp only [abs_zero, add_zero, abs_div, abs_neg, abs_one, abs_of_pos hDpos]
      linarith
  · let Δ := (a - cpp) * (d - cqq) - (b - 1 - cqp) * (b - cpq)
    have hbpos : 0 ≤ b := by linarith
    have hb_bound : b ≤ C := (abs_le.mp hbC).2
    have hud : b ^ 2 ≤ (a - cpp) * d := by
      nlinarith [mul_nonneg (show 0 ≤ -cpp by linarith) hd]
    have hucqq : (a - cpp) * cqq ≤ (C + ε) * ε :=
      (mul_le_mul_of_nonneg_left (abs_le.mp hqq).2 hu.le).trans
        (mul_le_mul_of_nonneg_right huC hε)
    have hbpq : -(C * ε) ≤ b * cpq := by
      have h₁ := mul_le_mul_of_nonneg_left (abs_le.mp hpq).1 hbpos
      have h₂ := mul_le_mul_of_nonneg_right hb_bound hε
      nlinarith
    have hbqp : -(C * ε) ≤ b * cqp := by
      have h₁ := mul_le_mul_of_nonneg_left (abs_le.mp hqp).1 hbpos
      have h₂ := mul_le_mul_of_nonneg_right hb_bound hε
      nlinarith
    have hprod : cqp * cpq ≤ ε ^ 2 := by
      calc
        cqp * cpq ≤ |cqp * cpq| := le_abs_self _
        _ = |cqp| * |cpq| := abs_mul _ _
        _ ≤ ε * ε := mul_le_mul hqp hpq (abs_nonneg _) hε
        _ = ε ^ 2 := by ring
    have hΔ : 1 / 4 ≤ Δ := by
      have hpq_upper := (abs_le.mp hpq).2
      have hεsq : ε ^ 2 ≤ ε := by nlinarith
      dsimp [Δ]
      nlinarith
    have hΔpos : 0 < Δ := by linarith
    have hΔne : Δ ≠ 0 := ne_of_gt hΔpos
    have hnum : |b - cpq| ≤ C + ε :=
      (abs_sub b cpq).trans (add_le_add hbC hpq)
    have huabs : |a - cpp| ≤ C + ε := by rwa [abs_of_pos hu]
    have hnorm : |-(b - cpq) / Δ| + |(a - cpp) / Δ| ≤ 8 * (C + 1) := by
      rw [abs_div, abs_div, abs_neg, abs_of_pos hΔpos, ← add_div]
      apply (div_le_iff₀ hΔpos).2
      nlinarith [mul_nonneg (show 0 ≤ C + 1 by linarith)
        (show 0 ≤ Δ - 1 / 4 by linarith)]
    refine ⟨-(b - cpq) / Δ, (a - cpp) / Δ, ?_, ?_, ?_, hnorm⟩
    · field_simp [hΔne]
      dsimp [Δ]
      ring
    · have heq : (a - cpp) * (-(b - cpq) / Δ) +
          (b - cpq) * ((a - cpp) / Δ) = 0 := by ring
      rw [heq]
      linarith
    · have heq : (a - cpp) * (-(b - cpq) / Δ) +
          (b - cpq) * ((a - cpp) / Δ) = 0 := by ring
      rw [heq]

/-- The endpoint choice at an arbitrary positive shear scale `h`. -/
theorem select_endpoint_scaled
    (C ε h a b d cpp cpq cqp cqq : ℝ)
    (hC : 1 ≤ C) (hε : 0 ≤ ε) (hsmall : 16 * (C + 1) * ε ≤ 1)
    (hh : 0 < h) (ha : 0 ≤ a) (had : b ^ 2 ≤ a * d) (hd : 0 ≤ d)
    (haC : a ≤ C * h) (hbC : |b| ≤ C * h)
    (hpp : cpp < 0) (hppε : |cpp| ≤ ε * h)
    (hpq : |cpq| ≤ ε * h) (hqp : |cqp| ≤ ε * h) (hqq : |cqq| ≤ ε * h) :
    ∃ yp yq : ℝ,
      (b - h - cqp) * yp + (d - cqq) * yq = 1 ∧
      -8 * (C + 1) ≤ (a - cpp) * yp + (b - cpq) * yq ∧
      (a - cpp) * yp + (b - cpq) * yq ≤ 0 ∧
      |yp| + |yq| ≤ 8 * (C + 1) / h := by
  have habs (x R : ℝ) (hx : |x| ≤ R * h) : |x / h| ≤ R := by
    rw [abs_div, abs_of_pos hh]
    exact (div_le_iff₀ hh).2 hx
  have hpsd : (b / h) ^ 2 ≤ (a / h) * (d / h) := by
    rw [div_pow, div_mul_div_comm, ← pow_two]
    exact div_le_div_of_nonneg_right had (sq_nonneg h)
  obtain ⟨yp, yq, hwq, hwpl, hwpu, hnorm⟩ := select_endpoint C ε
    (a / h) (b / h) (d / h) (cpp / h) (cpq / h) (cqp / h) (cqq / h)
    hC hε hsmall (div_nonneg ha hh.le) hpsd (div_nonneg hd hh.le)
    ((div_le_iff₀ hh).2 haC) (habs b C hbC)
    (div_neg_of_neg_of_pos hpp hh) (habs cpp ε hppε)
    (habs cpq ε hpq) (habs cqp ε hqp) (habs cqq ε hqq)
  have heqp : (a - cpp) * (yp / h) + (b - cpq) * (yq / h) =
      (a / h - cpp / h) * yp + (b / h - cpq / h) * yq := by ring
  have heqq : (b - h - cqp) * (yp / h) + (d - cqq) * (yq / h) =
      (b / h - 1 - cqp / h) * yp + (d / h - cqq / h) * yq := by
    field_simp
  refine ⟨yp / h, yq / h, heqq.trans hwq, heqp ▸ hwpl, heqp ▸ hwpu, ?_⟩
  rw [abs_div, abs_div, abs_of_pos hh, ← add_div]
  exact div_le_div_of_nonneg_right hnorm hh.le

theorem select_endpoint_hilbert {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (Λ B : E →L[ℝ] E) (p q : E)
    (C ε h : ℝ) (hΛ : Λ.IsPositive) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hpq : ⟪p, q⟫_ℝ = 0) (hC : 1 ≤ C) (hε : 0 ≤ ε) (hh : 0 < h)
    (hsmall : 16 * (C + 1) * ε ≤ 1) (hΛbound : ‖Λ‖ ≤ C * h)
    (hBbound : ‖B‖ ≤ ε * h) (hBpp : ⟪B p, p⟫_ℝ < 0) :
    ∃ yp yq : ℝ, let Y := yp • p + yq • q
      let w := Λ Y - B Y - (h * ⟪p, Y⟫_ℝ) • q
      ⟪w, q⟫_ℝ = 1 ∧ -8 * (C + 1) ≤ ⟪w, p⟫_ℝ ∧
        ⟪w, p⟫_ℝ ≤ 0 ∧ ‖Y‖ ≤ 8 * (C + 1) / h := by
  have hbound (T : E →L[ℝ] E) (v w : E) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
      |⟪T v, w⟫_ℝ| ≤ ‖T‖ := by
    calc
      |⟪T v, w⟫_ℝ| ≤ ‖T v‖ * ‖w‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖T‖ * ‖v‖) * ‖w‖ :=
        mul_le_mul_of_nonneg_right (T.le_opNorm v) (norm_nonneg w)
      _ = ‖T‖ := by rw [hv, hw, mul_one, mul_one]
  have hsym : ⟪Λ q, p⟫_ℝ = ⟪Λ p, q⟫_ℝ := by
    rw [hΛ.inner_left_eq_inner_right, real_inner_comm]
  obtain ⟨yp, yq, hwq, hwpl, hwpu, hnorm⟩ := select_endpoint_scaled C ε h
    ⟪Λ p, p⟫_ℝ ⟪Λ p, q⟫_ℝ ⟪Λ q, q⟫_ℝ
    ⟪B p, p⟫_ℝ ⟪B q, p⟫_ℝ ⟪B p, q⟫_ℝ ⟪B q, q⟫_ℝ
    hC hε hsmall hh (hΛ.inner_nonneg_left p) (positive_cross_sq_le Λ hΛ p q)
    (hΛ.inner_nonneg_left q)
    ((le_abs_self _).trans ((hbound Λ p p hp hp).trans hΛbound))
    ((hbound Λ p q hp hq).trans hΛbound) hBpp
    ((hbound B p p hp hp).trans hBbound) ((hbound B q p hq hp).trans hBbound)
    ((hbound B p q hp hq).trans hBbound) ((hbound B q q hq hq).trans hBbound)
  have hqp : ⟪q, p⟫_ℝ = 0 := (real_inner_comm _ _).trans hpq
  have hpp : ⟪p, p⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hp, one_pow]
  have hqq : ⟪q, q⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hq, one_pow]
  refine ⟨yp, yq, ?_, ?_, ?_, ?_⟩
  · convert hwq using 1
    simp only [map_add, map_smul, inner_sub_left, inner_add_left,
        inner_add_right, real_inner_smul_left, real_inner_smul_right,
        hpq, hpp, hqq]
    ring
  · convert hwpl using 1
    simp only [map_add, map_smul, inner_sub_left, inner_add_left,
        inner_add_right, real_inner_smul_left, real_inner_smul_right,
        hsym, hpq, hqp, hpp]
    ring
  · convert hwpu using 1
    simp only [map_add, map_smul, inner_sub_left, inner_add_left,
        inner_add_right, real_inner_smul_left, real_inner_smul_right,
        hsym, hpq, hqp, hpp]
    ring
  · calc
      ‖yp • p + yq • q‖ ≤ ‖yp • p‖ + ‖yq • q‖ := norm_add_le _ _
      _ = |yp| + |yq| := by rw [norm_smul, norm_smul, hp, hq]; simp
      _ ≤ 8 * (C + 1) / h := hnorm

end EulerDNSelection
