/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Development.IntervalArithmetic.Foundations.Development001










public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.MetricSpace.Contracting
/-!
# Moving sofa: related mathematical developments

* `LeanCert.Engine.AD.PartialCorrectness`.
* `LeanCert.Engine.IntervalEvalDyadic`.
* `LeanCert.Engine.AD.Dyadic`.
* `LeanCert.Engine.AD`.
* `LeanCert.Engine.Optimization.Box`.
* `LeanCert.Engine.Optimize`.
* `LeanCert.Engine.Optimization.Gradient`.
* `LeanCert.Engine.RootFinding.Krawczyk`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
/-!
# Automatic Differentiation - Partial Correctness Theorems

This file proves the correctness of the partial dual evaluator `evalDualOption`
which handles expressions with inv, log, and other domain-restricted functions.

## Main theorems

* `evalDualOption_val_correct` - Value component is correct when evalDualOption returns some
* `evalDualOption1_val_correct` - Single-variable version
* `evalFunc1_differentiableAt_of_evalDualOption` - Differentiability when evalDualOption succeeds
* `evalDualOption_der_correct` - Derivative component is correct
* `evalDualOption1_correct` - Combined correctness theorem

## Design notes

All theorems are FULLY PROVED with no sorry or axioms.
The key insight is that when evalDualOption returns `some`, the domain
constraints (nonzero for inv, positive for log) are satisfied.
-/

/-! ### Correctness of partial dual evaluator -/

public section

namespace LeanCert.Engine

open LeanCert.Core Filter
open scoped Topology

/-- The value component of evalDualOption is correct when it returns some.
    This theorem extends to expressions with inv. -/
theorem evalDualOption_val_correct (e : Expr)
    (ρ_real : Nat → ℝ) (ρ_dual : DualEnv) (D : DualInterval)
    (hsome : evalDualOption e ρ_dual = some D)
    (hρ : ∀ i, ρ_real i ∈ (ρ_dual i).val) :
    Expr.eval ρ_real e ∈ D.val := by
  induction e generalizing D with
  | const q =>
    simp only [evalDualOption, Option.some.injEq] at hsome
    rw [← hsome]
    simp only [Expr.eval_const, DualInterval.const]
    exact IntervalRat.mem_singleton q
  | var idx =>
    simp only [evalDualOption, Option.some.injEq] at hsome
    rw [← hsome]
    exact hρ idx
  | add e₁ e₂ ih₁ ih₂ =>
    simp only [evalDualOption] at hsome
    cases heq₁ : evalDualOption e₁ ρ_dual with
    | none => simp only [heq₁, reduceCtorEq] at hsome
    | some d₁ =>
      cases heq₂ : evalDualOption e₂ ρ_dual with
      | none => simp only [heq₁, heq₂, reduceCtorEq] at hsome
      | some d₂ =>
        simp only [heq₁, heq₂, Option.some.injEq] at hsome
        rw [← hsome]
        simp only [Expr.eval_add, DualInterval.add]
        exact IntervalRat.mem_add (ih₁ d₁ heq₁) (ih₂ d₂ heq₂)
  | mul e₁ e₂ ih₁ ih₂ =>
    simp only [evalDualOption] at hsome
    cases heq₁ : evalDualOption e₁ ρ_dual with
    | none => simp only [heq₁, reduceCtorEq] at hsome
    | some d₁ =>
      cases heq₂ : evalDualOption e₂ ρ_dual with
      | none => simp only [heq₁, heq₂, reduceCtorEq] at hsome
      | some d₂ =>
        simp only [heq₁, heq₂, Option.some.injEq] at hsome
        rw [← hsome]
        simp only [Expr.eval_mul, DualInterval.mul]
        exact IntervalRat.mem_mul (ih₁ d₁ heq₁) (ih₂ d₂ heq₂)
  | neg e' ih =>
    simp only [evalDualOption] at hsome
    cases heq : evalDualOption e' ρ_dual with
    | none => simp only [heq, reduceCtorEq] at hsome
    | some d =>
      simp only [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [Expr.eval_neg, DualInterval.neg]
      exact IntervalRat.mem_neg (ih d heq)
  | inv e' ih =>
    simp only [evalDualOption] at hsome
    cases heq : evalDualOption e' ρ_dual with
    | none => simp only [heq, reduceCtorEq] at hsome
    | some d =>
      simp only [heq, DualInterval.inv?] at hsome
      split at hsome
      · simp at hsome
      · next hnotzero =>
        simp only [Option.some.injEq] at hsome
        rw [← hsome]
        simp only [Expr.eval_inv]
        have hmem := ih d heq
        -- The denominator is nonzero because d.val doesn't contain zero and eval ∈ d.val
        have heval_ne : Expr.eval ρ_real e' ≠ 0 := by
          intro heq_zero
          rw [heq_zero] at hmem
          simp only [IntervalRat.mem_def] at hmem
          simp only [IntervalRat.containsZero, not_and, not_le] at hnotzero
          rcases le_or_gt d.val.lo 0 with hlo | hlo
          · have hhi_nonneg : (0 : ℚ) ≤ d.val.hi := by
              have h : (0 : ℝ) ≤ d.val.hi := hmem.2
              exact_mod_cast h
            exact absurd (hnotzero hlo) (not_lt.mpr hhi_nonneg)
          · have hlo_pos : (0 : ℝ) < d.val.lo := by exact_mod_cast hlo
            exact absurd hmem.1 (not_le.mpr hlo_pos)
        exact IntervalRat.mem_invNonzero hmem heval_ne
  | sin e' ih =>
    simp only [evalDualOption] at hsome
    cases heq : evalDualOption e' ρ_dual with
    | none => simp only [heq, reduceCtorEq] at hsome
    | some d =>
      simp only [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [Expr.eval_sin, DualInterval.sin]
      exact mem_sinInterval (ih d heq)
  | cos e' ih =>
    simp only [evalDualOption] at hsome
    cases heq : evalDualOption e' ρ_dual with
    | none => simp only [heq, reduceCtorEq] at hsome
    | some d =>
      simp only [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [Expr.eval_cos, DualInterval.cos]
      exact mem_cosInterval (ih d heq)
  | exp e' ih =>
    simp only [evalDualOption] at hsome
    cases heq : evalDualOption e' ρ_dual with
    | none => simp only [heq, reduceCtorEq] at hsome
    | some d =>
      simp only [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [Expr.eval_exp, DualInterval.exp]
      exact IntervalRat.mem_expInterval (ih d heq)
  | sinh e' ih =>
    simp only [evalDualOption] at hsome
    cases heq : evalDualOption e' ρ_dual with
    | none => simp only [heq, reduceCtorEq] at hsome
    | some d =>
      simp only [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [Expr.eval_sinh, DualInterval.sinh, sinhInterval]
      exact IntervalRat.mem_sinhComputable (ih d heq) 10
  | cosh e' ih =>
    simp only [evalDualOption] at hsome
    cases heq : evalDualOption e' ρ_dual with
    | none => simp only [heq, reduceCtorEq] at hsome
    | some d =>
      simp only [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [Expr.eval_cosh, DualInterval.cosh, coshInterval]
      exact IntervalRat.mem_coshComputable (ih d heq) 10
  | tanh _ _ =>
    simp only [evalDualOption] at hsome
    cases hsome
  | log e' ih =>
    simp only [evalDualOption] at hsome
    cases heq : evalDualOption e' ρ_dual with
    | none => simp only [heq, reduceCtorEq] at hsome
    | some d =>
      simp only [heq, DualInterval.logOption] at hsome
      split at hsome
      · rename_i hpos
        simp only [Option.some.injEq] at hsome
        rw [← hsome]
        simp only [Expr.eval_log]
        have hJ_mem := ih d heq
        exact IntervalRat.mem_logInterval hJ_mem
      · contradiction
  | atan e' ih =>
    simp only [evalDualOption] at hsome
    cases heq : evalDualOption e' ρ_dual with
    | none => simp only [heq, reduceCtorEq] at hsome
    | some d =>
      simp only [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [Expr.eval_atan, DualInterval.atan]
      exact mem_atanInterval (ih d heq)
  | arsinh e' ih =>
    simp only [evalDualOption] at hsome
    cases heq : evalDualOption e' ρ_dual with
    | none => simp only [heq, reduceCtorEq] at hsome
    | some d =>
      simp only [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [Expr.eval_arsinh, DualInterval.arsinh]
      exact mem_arsinhInterval (ih d heq)
  | atanh _ _ =>
    -- evalDualOption returns none for atanh, so hsome : none = some D is a contradiction
    simp only [evalDualOption] at hsome
    contradiction
  | sinc e' ih =>
    simp only [evalDualOption] at hsome
    cases heq : evalDualOption e' ρ_dual with
    | none => simp only [heq, reduceCtorEq] at hsome
    | some d =>
      simp only [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [Expr.eval_sinc, DualInterval.sinc]
      simp only [IntervalRat.mem_def, Rat.cast_neg, Rat.cast_one]
      exact Real.sinc_mem_Icc _
  | erf e' ih =>
    simp only [evalDualOption] at hsome
    cases heq : evalDualOption e' ρ_dual with
    | none => simp only [heq, reduceCtorEq] at hsome
    | some d =>
      simp only [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [Expr.eval_erf, DualInterval.erf]
      simp only [IntervalRat.mem_def, Rat.cast_neg, Rat.cast_one]
      exact Real.erf_mem_Icc _
  | sqrt e' ih =>
    simp only [evalDualOption] at hsome
    cases heq : evalDualOption e' ρ_dual with
    | none => simp only [heq, reduceCtorEq] at hsome
    | some d =>
      simp only [heq] at hsome
      -- hsome : DualInterval.sqrt? d = some D
      simp only [DualInterval.sqrt?] at hsome
      split at hsome
      · next hpos =>
        simp only [Option.some.injEq] at hsome
        rw [← hsome]
        simp only [Expr.eval_sqrt]
        exact IntervalRat.mem_sqrtInterval' (ih d heq)
      · exact absurd hsome (by simp)
  | namedConst c =>
    simp only [evalDualOption, Option.some.injEq] at hsome
    rw [← hsome]
    simp only [Expr.eval_namedConst, DualInterval.ofMathConst]
    exact c.mem_interval

/-- Single-variable version of evalDualOption_val_correct -/
theorem evalDualOption1_val_correct (e : Expr)
    (I : IntervalRat) (D : DualInterval) (x : ℝ) (hx : x ∈ I)
    (hsome : evalDualOption1 e I = some D) :
    Expr.eval (fun _ => x) e ∈ D.val := by
  apply evalDualOption_val_correct e (fun _ => x) (fun _ => DualInterval.varActive I)
  · exact hsome
  · intro _; exact hx

/-- Helper lemma: evalFunc1 for inv unfolds correctly -/
theorem evalFunc1_inv (e : Expr) :
    evalFunc1 (Expr.inv e) = fun t => (evalFunc1 e t)⁻¹ := rfl

/-- Expressions with inv are differentiable when the denominator is nonzero. -/
theorem evalFunc1_differentiableAt_of_evalDualOption (e : Expr)
    (I : IntervalRat) (D : DualInterval) (x : ℝ) (hx : x ∈ I)
    (hsome : evalDualOption1 e I = some D) :
    DifferentiableAt ℝ (evalFunc1 e) x := by
  induction e generalizing D with
  | const q => exact differentiableAt_const _
  | var _ => exact differentiableAt_id
  | add e₁ e₂ ih₁ ih₂ =>
    unfold evalDualOption1 evalDualOption at hsome
    cases heq₁ : evalDualOption e₁ _ with
    | none => rw [heq₁] at hsome; exact absurd hsome (by simp)
    | some d₁ =>
      cases heq₂ : evalDualOption e₂ _ with
      | none => rw [heq₁, heq₂] at hsome; exact absurd hsome (by simp)
      | some d₂ =>
        exact DifferentiableAt.add (ih₁ d₁ heq₁) (ih₂ d₂ heq₂)
  | mul e₁ e₂ ih₁ ih₂ =>
    unfold evalDualOption1 evalDualOption at hsome
    cases heq₁ : evalDualOption e₁ _ with
    | none => rw [heq₁] at hsome; exact absurd hsome (by simp)
    | some d₁ =>
      cases heq₂ : evalDualOption e₂ _ with
      | none => rw [heq₁, heq₂] at hsome; exact absurd hsome (by simp)
      | some d₂ =>
        exact DifferentiableAt.mul (ih₁ d₁ heq₁) (ih₂ d₂ heq₂)
  | neg e' ih =>
    unfold evalDualOption1 evalDualOption at hsome
    cases heq : evalDualOption e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      exact DifferentiableAt.neg (ih d heq)
  | inv e' ih =>
    unfold evalDualOption1 evalDualOption at hsome
    cases heq : evalDualOption e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      rw [heq] at hsome
      simp only [DualInterval.inv?] at hsome
      split at hsome
      · exact absurd hsome (by simp)
      · next hnotzero =>
        simp only [Option.some.injEq] at hsome
        have hval := evalDualOption1_val_correct e' I d x hx heq
        -- Denominator is nonzero
        have hne : evalFunc1 e' x ≠ 0 := by
          intro heq_zero
          -- hval has type: Expr.eval (fun x_1 => x) e' ∈ d.val
          -- need to convert to: evalFunc1 e' x = 0
          have hval' : evalFunc1 e' x ∈ d.val := hval
          rw [heq_zero] at hval'
          simp only [IntervalRat.mem_def] at hval'
          simp only [IntervalRat.containsZero, not_and, not_le] at hnotzero
          rcases le_or_gt d.val.lo 0 with hlo | hlo
          · have hhi_nonneg : (0 : ℚ) ≤ d.val.hi := by
              have h : (0 : ℝ) ≤ d.val.hi := hval'.2
              exact_mod_cast h
            exact absurd (hnotzero hlo) (not_lt.mpr hhi_nonneg)
          · have hlo_pos : (0 : ℝ) < d.val.lo := by exact_mod_cast hlo
            exact absurd hval'.1 (not_le.mpr hlo_pos)
        exact DifferentiableAt.inv (ih d heq) hne
  | sin e' ih =>
    unfold evalDualOption1 evalDualOption at hsome
    cases heq : evalDualOption e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      exact Real.differentiableAt_sin.comp x (ih d heq)
  | cos e' ih =>
    unfold evalDualOption1 evalDualOption at hsome
    cases heq : evalDualOption e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      exact Real.differentiableAt_cos.comp x (ih d heq)
  | exp e' ih =>
    unfold evalDualOption1 evalDualOption at hsome
    cases heq : evalDualOption e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      exact Real.differentiableAt_exp.comp x (ih d heq)
  | sinh e' ih =>
    unfold evalDualOption1 evalDualOption at hsome
    cases heq : evalDualOption e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      exact (ih d heq).sinh
  | cosh e' ih =>
    unfold evalDualOption1 evalDualOption at hsome
    cases heq : evalDualOption e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      exact (ih d heq).cosh
  | tanh _ _ =>
    unfold evalDualOption1 evalDualOption at hsome
    contradiction
  | log e' ih =>
    unfold evalDualOption1 evalDualOption at hsome
    cases heq : evalDualOption e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      rw [heq] at hsome
      simp only [DualInterval.logOption] at hsome
      split at hsome
      · next hpos =>
        simp only [Option.some.injEq] at hsome
        have hval := evalDualOption1_val_correct e' I d x hx heq
        -- The argument is positive, so log is differentiable
        have hpos_x : 0 < evalFunc1 e' x := by
          have hval' : evalFunc1 e' x ∈ d.val := hval
          simp only [IntervalRat.mem_def] at hval'
          simp only [IntervalRat.isPositive] at hpos
          have hlo_pos : (0 : ℝ) < d.val.lo := by exact_mod_cast hpos
          exact lt_of_lt_of_le hlo_pos hval'.1
        exact Real.differentiableAt_log (ne_of_gt hpos_x) |>.comp x (ih d heq)
      · exact absurd hsome (by simp)
  | atan e' ih =>
    unfold evalDualOption1 evalDualOption at hsome
    cases heq : evalDualOption e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      exact (Real.differentiable_arctan _).comp x (ih d heq)
  | arsinh e' ih =>
    unfold evalDualOption1 evalDualOption at hsome
    cases heq : evalDualOption e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      exact (Real.differentiable_arsinh _).comp x (ih d heq)
  | atanh _ _ =>
    -- evalDualOption returns none for atanh, so hsome is a contradiction
    simp only [evalDualOption1, evalDualOption] at hsome
    contradiction
  | sinc e' ih =>
    unfold evalDualOption1 evalDualOption at hsome
    cases heq : evalDualOption e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      -- sinc is differentiable everywhere
      -- sinc = dslope sin 0, which is differentiable:
      -- - At x ≠ 0: sinc x = sin x / x is differentiable
      -- - At x = 0: sinc is differentiable with derivative 0 (from sin's Taylor series)
      have hsinc_diff : Differentiable ℝ Real.sinc := Real.differentiable_sinc
      exact hsinc_diff.differentiableAt.comp x (ih d heq)
  | erf e' ih =>
    unfold evalDualOption1 evalDualOption at hsome
    cases heq : evalDualOption e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      -- erf is differentiable everywhere using FTC
      -- erf(x) = (2/√π) * ∫₀ˣ exp(-t²) dt
      -- By FTC, the integral of a continuous function is differentiable
      have herf_diff : Differentiable ℝ Real.erf := by
        unfold Real.erf
        apply Differentiable.const_mul
        -- Use FTC: for continuous f, ∫ t in a..x, f t is differentiable in x
        intro y
        have hcont : Continuous (fun t => Real.exp (-(t^2))) :=
          Real.continuous_exp.comp (continuous_neg.comp (continuous_pow 2))
        exact (hcont.integral_hasStrictDerivAt 0 y).hasStrictFDerivAt.differentiableAt
      exact herf_diff.differentiableAt.comp x (ih d heq)
  | sqrt e' ih =>
    unfold evalDualOption1 evalDualOption at hsome
    cases heq : evalDualOption e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      rw [heq] at hsome
      simp only [DualInterval.sqrt?] at hsome
      split at hsome
      · next hpos =>
        simp only [Option.some.injEq] at hsome
        have hval := evalDualOption1_val_correct e' I d x hx heq
        -- The argument is positive, so sqrt is differentiable
        have hpos_x : 0 < evalFunc1 e' x := by
          have hval' : evalFunc1 e' x ∈ d.val := hval
          simp only [IntervalRat.mem_def] at hval'
          simp only [IntervalRat.isPositive] at hpos
          have hlo_pos : (0 : ℝ) < d.val.lo := by exact_mod_cast hpos
          exact lt_of_lt_of_le hlo_pos hval'.1
        -- sqrt is differentiable at nonzero points
        have hne : evalFunc1 e' x ≠ 0 := ne_of_gt hpos_x
        exact (Real.hasDerivAt_sqrt hne).differentiableAt.comp x (ih d heq)
      · exact absurd hsome (by simp)
  | namedConst _ => exact differentiableAt_const _

/-- The derivative component of evalDualOption is correct when it returns some.
    For a supported expression (with inv) evaluated at a point x in the interval I,
    the derivative of the expression lies in the computed derivative interval.

    This extends the AD correctness theorem to expressions with inv. -/
private theorem evalDual?_der_correct_inv (e' : Expr)
    (I : IntervalRat) (D : DualInterval) (x : ℝ) (hx : x ∈ I)
    (hsome : evalDualOption1 (Expr.inv e') I = some D)
    (ih : ∀ D, evalDualOption1 e' I = some D → deriv (evalFunc1 e') x ∈ D.der) :
    deriv (evalFunc1 (Expr.inv e')) x ∈ D.der := by
  unfold evalDualOption1 evalDualOption at hsome
  cases heq : evalDualOption e' _ with
  | none => rw [heq] at hsome; exact absurd hsome (by simp)
  | some d =>
    rw [heq] at hsome
    simp only [DualInterval.inv?] at hsome
    split at hsome
    · exact absurd hsome (by simp)
    · next hnotzero =>
      simp only [Option.some.injEq] at hsome
      rw [← hsome]
      -- d(1/f) = -f'/f² = -f' * (1/f)²
      have hval := evalDualOption1_val_correct e' I d x hx heq
      have hval' : evalFunc1 e' x ∈ d.val := hval
      have hne : evalFunc1 e' x ≠ 0 := by
        intro heq_zero
        rw [heq_zero] at hval'
        simp only [IntervalRat.mem_def] at hval'
        simp only [IntervalRat.containsZero, not_and, not_le] at hnotzero
        rcases le_or_gt d.val.lo 0 with hlo | hlo
        · have hhi_nonneg : (0 : ℚ) ≤ d.val.hi := by
            have h : (0 : ℝ) ≤ d.val.hi := hval'.2
            exact_mod_cast h
          exact absurd (hnotzero hlo) (not_lt.mpr hhi_nonneg)
        · have hlo_pos : (0 : ℝ) < d.val.lo := by exact_mod_cast hlo
          exact absurd hval'.1 (not_le.mpr hlo_pos)
      have hd := evalFunc1_differentiableAt_of_evalDualOption e' I d x hx heq
      -- deriv (1/f) = deriv(f⁻¹ ∘ f) = -(f')/(f²) using chain rule
      -- We use: deriv (fun y => y⁻¹) (f x) * deriv f x = -(f x)⁻² * f'(x)
      rw [evalFunc1_inv]
      -- The goal is: deriv (fun t => (evalFunc1 e' t)⁻¹) x ∈ ...
      -- First show this equals the composition derivative
      have heq_fun : (fun t => (evalFunc1 e' t)⁻¹) = (fun y => y⁻¹) ∘ evalFunc1 e' := rfl
      rw [heq_fun, deriv_comp x (hasDerivAt_inv hne).differentiableAt hd]
      simp only [hasDerivAt_inv hne |>.deriv]
      -- Now goal is: -(evalFunc1 e' x ^ 2)⁻¹ * deriv (evalFunc1 e') x ∈ ...
      -- Which equals: -(deriv f * (1/f)²)
      have hder := ih d heq
      -- Construct the nonzero interval
      let I_nz : IntervalRat.IntervalRatNonzero := ⟨d.val, hnotzero⟩
      have hinv := IntervalRat.mem_invNonzero (I := I_nz) hval' hne
      have hinv_sq := IntervalRat.mem_mul hinv hinv
      have hprod := IntervalRat.mem_mul hder hinv_sq
      have hneg := IntervalRat.mem_neg hprod
      -- hneg : -(deriv (evalFunc1 e') x * ((evalFunc1 e' x)⁻¹ * (evalFunc1 e' x)⁻¹)) ∈ ...
      -- goal : -(evalFunc1 e' x ^ 2)⁻¹ * deriv (evalFunc1 e') x ∈ ...
      -- These are equal: -(a ^ 2)⁻¹ * b = -(b * (a⁻¹ * a⁻¹))
      have heq_val : -(evalFunc1 e' x ^ 2)⁻¹ * deriv (evalFunc1 e') x =
                     -(deriv (evalFunc1 e') x * ((evalFunc1 e' x)⁻¹ * (evalFunc1 e' x)⁻¹)) := by
        have h1 : (evalFunc1 e' x ^ 2)⁻¹ = (evalFunc1 e' x)⁻¹ * (evalFunc1 e' x)⁻¹ := by
          rw [sq, mul_inv]
        rw [h1]
        ring
      rw [heq_val]
      exact hneg

private theorem evalDual?_der_correct_log (e' : Expr)
    (I : IntervalRat) (D : DualInterval) (x : ℝ) (hx : x ∈ I)
    (hsome : evalDualOption1 (Expr.log e') I = some D)
    (ih : ∀ D, evalDualOption1 e' I = some D → deriv (evalFunc1 e') x ∈ D.der) :
    deriv (evalFunc1 (Expr.log e')) x ∈ D.der := by
  unfold evalDualOption1 evalDualOption at hsome
  cases heq : evalDualOption e' _ with
  | none => rw [heq] at hsome; exact absurd hsome (by simp)
  | some d =>
    rw [heq] at hsome
    simp only [DualInterval.logOption] at hsome
    split at hsome
    · next hpos =>
      simp only [Option.some.injEq] at hsome
      rw [← hsome]
      -- d(log f)/dx = f'/f
      have hval := evalDualOption1_val_correct e' I d x hx heq
      have hval' : evalFunc1 e' x ∈ d.val := hval
      have hpos_x : 0 < evalFunc1 e' x := by
        simp only [IntervalRat.mem_def] at hval'
        simp only [IntervalRat.isPositive] at hpos
        have hlo_pos : (0 : ℝ) < d.val.lo := by exact_mod_cast hpos
        exact lt_of_lt_of_le hlo_pos hval'.1
      have hne_x : evalFunc1 e' x ≠ 0 := ne_of_gt hpos_x
      have hd := evalFunc1_differentiableAt_of_evalDualOption e' I d x hx heq
      rw [evalFunc1_log]
      have heq_fun : (fun t => Real.log (evalFunc1 e' t)) = Real.log ∘ evalFunc1 e' := rfl
      rw [heq_fun, deriv_comp x (Real.differentiableAt_log hne_x) hd]
      simp only [Real.deriv_log (evalFunc1 e' x)]
      -- Goal: (evalFunc1 e' x)⁻¹ * deriv (evalFunc1 e') x ∈ ...
      -- From DualInterval.logOption: der' := d.der * invNonzero d.val
      have hder := ih d heq
      -- Build the nonzero interval from the positive interval
      have hnotzero : ¬IntervalRat.containsZero d.val := by
        simp only [IntervalRat.containsZero, IntervalRat.isPositive] at hpos ⊢
        intro ⟨hle, _⟩
        exact absurd hpos (not_lt.mpr hle)
      let I_nz : IntervalRat.IntervalRatNonzero := ⟨d.val, hnotzero⟩
      have hinv := IntervalRat.mem_invNonzero (I := I_nz) hval' hne_x
      -- Need to show: (evalFunc1 e' x)⁻¹ * deriv (evalFunc1 e') x ∈ d.der * invNonzero d.val
      -- But mem_mul expects the arguments in different order, so use commutativity
      have hmul := IntervalRat.mem_mul hder hinv
      convert hmul using 1
      ring
    · exact absurd hsome (by simp)

private theorem evalDual?_der_correct_erf (e' : Expr)
    (I : IntervalRat) (D : DualInterval) (x : ℝ) (hx : x ∈ I)
    (hsome : evalDualOption1 (Expr.erf e') I = some D)
    (ih : ∀ D, evalDualOption1 e' I = some D → deriv (evalFunc1 e') x ∈ D.der) :
    deriv (evalFunc1 (Expr.erf e')) x ∈ D.der := by
  unfold evalDualOption1 evalDualOption at hsome
  cases heq : evalDualOption e' _ with
  | none => rw [heq] at hsome; exact absurd hsome (by simp)
  | some d =>
    rw [heq, Option.some.injEq] at hsome
    rw [← hsome]
    simp only [DualInterval.erf]
    -- The derivative of erf ∘ f is (2/√π) * exp(-f(x)²) * f'(x)
    have hd_inner := evalFunc1_differentiableAt_of_evalDualOption e' I d x hx heq
    have herf_diff : Differentiable ℝ Real.erf := by
      unfold Real.erf
      apply Differentiable.const_mul
      intro y
      have hcont : Continuous (fun t => Real.exp (-(t^2))) :=
        Real.continuous_exp.comp (continuous_neg.comp (continuous_pow 2))
      exact (hcont.integral_hasStrictDerivAt 0 y).hasStrictFDerivAt.differentiableAt
    have heq_comp : (fun t => Real.erf (evalFunc1 e' t)) = Real.erf ∘ evalFunc1 e' := rfl
    rw [evalFunc1_erf, heq_comp, deriv_comp x herf_diff.differentiableAt hd_inner]
    -- deriv erf y = (2/√π) * exp(-y²) by FTC
    have hderiv_erf : ∀ y, deriv Real.erf y = (2 / Real.sqrt Real.pi) * Real.exp (-(y^2)) := by
      intro y
      unfold Real.erf
      rw [deriv_const_mul]
      · have hcont : Continuous (fun t => Real.exp (-(t^2))) :=
          Real.continuous_exp.comp (continuous_neg.comp (continuous_pow 2))
        rw [(hcont.integral_hasStrictDerivAt 0 y).hasDerivAt.deriv]
      · have hcont : Continuous (fun t => Real.exp (-(t^2))) :=
          Real.continuous_exp.comp (continuous_neg.comp (continuous_pow 2))
        exact (hcont.integral_hasStrictDerivAt 0 y).hasStrictFDerivAt.differentiableAt
    rw [hderiv_erf]
    -- Now goal: (2/√π) * exp(-(f(x))²) * f'(x) ∈ twoDivSqrtPi * expInterval(-val²) * der
    -- Factor: (2/√π) ∈ twoDivSqrtPi
    -- 2/√π ≈ 1.1284, twoDivSqrtPi = [1.128, 1.129]
    have hfactor : 2 / Real.sqrt Real.pi ∈ DualInterval.twoDivSqrtPi := by
      simp only [DualInterval.twoDivSqrtPi, IntervalRat.mem_def]
      -- From π bounds: 3.1415 < π < 3.1416 (Real.pi_gt_d4, Real.pi_lt_d4)
      -- So √π is between √3.1415 ≈ 1.7724 and √3.1416 ≈ 1.7724
      -- Thus 2/√π is between 2/1.7725 ≈ 1.1283 and 2/1.7723 ≈ 1.1285
      have hpi_lo : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
      have hpi_hi : Real.pi < (3.1416 : ℝ) := Real.pi_lt_d4
      have hsqrt_lo : (1.7724 : ℝ) < Real.sqrt Real.pi := by
        have h1 : (1.7724 : ℝ) ^ 2 < Real.pi := by
          have : (1.7724 : ℝ) ^ 2 = 3.14140176 := by ring
          linarith
        have h2 : (0 : ℝ) ≤ 1.7724 := by norm_num
        have h3 : (0 : ℝ) ≤ 1.7724 ^ 2 := by positivity
        calc (1.7724 : ℝ) = Real.sqrt (1.7724 ^ 2) := (Real.sqrt_sq h2).symm
          _ < Real.sqrt Real.pi := Real.sqrt_lt_sqrt h3 h1
      have hsqrt_hi : Real.sqrt Real.pi < (1.7725 : ℝ) := by
        have h1 : Real.pi < (1.7725 : ℝ) ^ 2 := by
          have : (1.7725 : ℝ) ^ 2 = 3.14175625 := by ring
          linarith
        have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
        rw [← Real.sqrt_sq (le_of_lt (by norm_num : (0 : ℝ) < 1.7725))]
        exact Real.sqrt_lt_sqrt (le_of_lt hpi_pos) h1
      constructor
      · -- Goal: ↑(1128 / 1000) ≤ 2 / √π
        have h1 : ((1128 / 1000 : ℚ) : ℝ) < 2 / 1.7725 := by norm_num
        have h2 : (2 : ℝ) / 1.7725 < 2 / Real.sqrt Real.pi := by
          apply div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 2)
          · exact Real.sqrt_pos.mpr Real.pi_pos
          · exact hsqrt_hi
        exact le_of_lt (lt_trans h1 h2)
      · -- Goal: 2 / √π ≤ ↑(1129 / 1000)
        have h1 : 2 / Real.sqrt Real.pi < (2 : ℝ) / 1.7724 := by
          apply div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 2)
          · norm_num
          · exact hsqrt_lo
        have h2 : (2 : ℝ) / 1.7724 < ((1129 / 1000 : ℚ) : ℝ) := by norm_num
        exact le_of_lt (lt_trans h1 h2)
    -- exp(-(f(x))²) ∈ expInterval(-val²)
    have hval := evalDualOption1_val_correct e' I d x hx heq
    have hval_sq := IntervalRat.mem_mul hval hval
    have hneg_val_sq := IntervalRat.mem_neg hval_sq
    have hexp := IntervalRat.mem_expInterval hneg_val_sq
    -- f'(x) ∈ d.der
    have hder := ih d heq
    -- Combine: (2/√π) * exp(-f(x)²) ∈ twoDivSqrtPi * expInterval(-val²)
    have hprod1 := IntervalRat.mem_mul hfactor hexp
    -- Full product: ((2/√π) * exp(-f(x)²)) * f'(x) ∈ (twoDivSqrtPi * expInterval(-val²)) * der
    have hprod2 := IntervalRat.mem_mul hprod1 hder
    convert hprod2 using 1
    ring_nf

private theorem evalDual?_der_correct_sqrt (e' : Expr)
    (I : IntervalRat) (D : DualInterval) (x : ℝ) (hx : x ∈ I)
    (hsome : evalDualOption1 (Expr.sqrt e') I = some D)
    (ih : ∀ D, evalDualOption1 e' I = some D → deriv (evalFunc1 e') x ∈ D.der) :
    deriv (evalFunc1 (Expr.sqrt e')) x ∈ D.der := by
  unfold evalDualOption1 evalDualOption at hsome
  cases heq : evalDualOption e' _ with
  | none => rw [heq] at hsome; exact absurd hsome (by simp)
  | some d =>
    rw [heq] at hsome
    simp only [DualInterval.sqrt?] at hsome
    split at hsome
    · next hpos =>
      simp only [Option.some.injEq] at hsome
      rw [← hsome]
      -- d(sqrt f)/dx = f'/(2*sqrt(f))
      have hval := evalDualOption1_val_correct e' I d x hx heq
      have hval' : evalFunc1 e' x ∈ d.val := hval
      have hpos_x : 0 < evalFunc1 e' x := by
        simp only [IntervalRat.mem_def] at hval'
        simp only [IntervalRat.isPositive] at hpos
        have hlo_pos : (0 : ℝ) < d.val.lo := by exact_mod_cast hpos
        exact lt_of_lt_of_le hlo_pos hval'.1
      have hne_x : evalFunc1 e' x ≠ 0 := ne_of_gt hpos_x
      have hd := evalFunc1_differentiableAt_of_evalDualOption e' I d x hx heq
      rw [evalFunc1_sqrt]
      have heq_fun : (fun t => Real.sqrt (evalFunc1 e' t)) = Real.sqrt ∘ evalFunc1 e' := rfl
      rw [heq_fun, deriv_comp x (Real.hasDerivAt_sqrt hne_x).differentiableAt hd]
      rw [(Real.hasDerivAt_sqrt hne_x).deriv]
      -- Goal: deriv (evalFunc1 e') x / (2 * √(evalFunc1 e' x)) ∈ d.der * sqrtDerivCoefBound
      have hder := ih d heq
      -- Show 1/(2*sqrt(f(x))) is in sqrtDerivCoefBound
      have hlo_le_val : (d.val.lo : ℝ) ≤ evalFunc1 e' x := by
        simp only [IntervalRat.mem_def] at hval'
        exact hval'.1
      have hlo_pos_real : (0 : ℝ) < (d.val.lo : ℚ) := by
        simp only [IntervalRat.isPositive] at hpos
        exact_mod_cast hpos
      -- Use our sqrtDerivCoef_bound theorem
      have hcoef_bound := DualInterval.sqrtDerivCoef_bound hlo_pos_real hlo_le_val
      -- The coefficient 1/(2*sqrt(f(x))) is positive and bounded
      have hcoef_pos : 0 ≤ 1 / (2 * Real.sqrt (evalFunc1 e' x)) := by
        apply div_nonneg (by norm_num)
        apply mul_nonneg (by norm_num)
        exact le_of_lt (Real.sqrt_pos.mpr hpos_x)
      have hcoef_mem : 1 / (2 * Real.sqrt (evalFunc1 e' x)) ∈ DualInterval.sqrtDerivCoefBound
        d.val.lo hpos := by
        simp only [DualInterval.sqrtDerivCoefBound, IntervalRat.mem_def]
        split
        · -- d.val.lo ≤ 1
          next hle_one =>
          constructor
          · simp only [Rat.cast_zero]
            exact hcoef_pos
          · -- Show 1/(2*sqrt(f(x))) ≤ 1/(2*lo)
            have hle_real : (d.val.lo : ℝ) ≤ 1 := by exact_mod_cast hle_one
            have h1 : max (1 / (2 * (d.val.lo : ℝ))) (1 / 2) = 1 / (2 * (d.val.lo : ℝ)) := by
              apply max_eq_left
              -- 1/2 ≤ 1/(2*lo) when lo ≤ 1
              apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
              calc 2 * (d.val.lo : ℝ) ≤ 2 * 1 := by nlinarith
                _ = 2 := by ring
            calc 1 / (2 * Real.sqrt (evalFunc1 e' x))
                ≤ max (1 / (2 * (d.val.lo : ℝ))) (1 / 2) := hcoef_bound
              _ = 1 / (2 * (d.val.lo : ℝ)) := h1
              _ = ↑(1 / (2 * d.val.lo)) := by push_cast; ring
        · -- d.val.lo > 1
          next hgt_one =>
          push Not at hgt_one
          constructor
          · simp only [Rat.cast_zero]
            exact hcoef_pos
          · -- Show 1/(2*sqrt(f(x))) ≤ 1/2
            have hgt_real : 1 < (d.val.lo : ℝ) := by exact_mod_cast hgt_one
            have h1 : max (1 / (2 * (d.val.lo : ℝ))) (1 / 2) = 1 / 2 := by
              apply max_eq_right
              -- 1/(2*lo) ≤ 1/2 when lo > 1
              apply div_le_div_of_nonneg_left (by norm_num) (by norm_num : (0:ℝ) < 2)
              calc (2 : ℝ) = 2 * 1 := by ring
                _ ≤ 2 * d.val.lo := by nlinarith
            calc 1 / (2 * Real.sqrt (evalFunc1 e' x))
                ≤ max (1 / (2 * (d.val.lo : ℝ))) (1 / 2) := hcoef_bound
              _ = 1 / 2 := h1
              _ = ↑(1 / 2 : ℚ) := by norm_num
      -- Combine: f'(x)/(2*sqrt(f(x))) = f'(x) * (1/(2*sqrt(f(x)))) ∈ d.der * sqrtDerivCoefBound
      have hmul := IntervalRat.mem_mul hder hcoef_mem
      convert hmul using 1
      field_simp [ne_of_gt (Real.sqrt_pos.mpr hpos_x)]
    · exact absurd hsome (by simp)

theorem evalDualOption_der_correct (e : Expr)
    (I : IntervalRat) (D : DualInterval) (x : ℝ) (hx : x ∈ I)
    (hsome : evalDualOption1 e I = some D) :
    deriv (evalFunc1 e) x ∈ D.der := by
  induction e generalizing D with
  | const q =>
    simp only [evalDualOption1, evalDualOption, Option.some.injEq] at hsome
    rw [← hsome]
    simp only [evalFunc1_const, deriv_const, DualInterval.const]
    convert IntervalRat.mem_singleton 0 using 1
    norm_cast
  | var _ =>
    simp only [evalDualOption1, evalDualOption, Option.some.injEq] at hsome
    rw [← hsome]
    simp only [evalFunc1_var, deriv_id, DualInterval.varActive]
    convert IntervalRat.mem_singleton 1 using 1
    norm_cast
  | add e₁ e₂ ih₁ ih₂ =>
    unfold evalDualOption1 evalDualOption at hsome
    cases heq₁ : evalDualOption e₁ _ with
    | none => rw [heq₁] at hsome; exact absurd hsome (by simp)
    | some d₁ =>
      cases heq₂ : evalDualOption e₂ _ with
      | none => rw [heq₁, heq₂] at hsome; exact absurd hsome (by simp)
      | some d₂ =>
        rw [heq₁, heq₂, Option.some.injEq] at hsome
        rw [← hsome]
        simp only [DualInterval.add]
        have hd₁ := evalFunc1_differentiableAt_of_evalDualOption e₁ I d₁ x hx heq₁
        have hd₂ := evalFunc1_differentiableAt_of_evalDualOption e₂ I d₂ x hx heq₂
        simp only [evalFunc1_add_pi, deriv_add hd₁ hd₂]
        exact IntervalRat.mem_add (ih₁ d₁ heq₁) (ih₂ d₂ heq₂)
  | mul e₁ e₂ ih₁ ih₂ =>
    unfold evalDualOption1 evalDualOption at hsome
    cases heq₁ : evalDualOption e₁ _ with
    | none => rw [heq₁] at hsome; exact absurd hsome (by simp)
    | some d₁ =>
      cases heq₂ : evalDualOption e₂ _ with
      | none => rw [heq₁, heq₂] at hsome; exact absurd hsome (by simp)
      | some d₂ =>
        rw [heq₁, heq₂, Option.some.injEq] at hsome
        rw [← hsome]
        simp only [DualInterval.mul]
        have hd₁ := evalFunc1_differentiableAt_of_evalDualOption e₁ I d₁ x hx heq₁
        have hd₂ := evalFunc1_differentiableAt_of_evalDualOption e₂ I d₂ x hx heq₂
        simp only [evalFunc1_mul_pi, deriv_mul hd₁ hd₂]
        have hval₁ := evalDualOption1_val_correct e₁ I d₁ x hx heq₁
        have hval₂ := evalDualOption1_val_correct e₂ I d₂ x hx heq₂
        exact IntervalRat.mem_add (IntervalRat.mem_mul (ih₁ d₁ heq₁) hval₂)
                                  (IntervalRat.mem_mul hval₁ (ih₂ d₂ heq₂))
  | neg e' ih =>
    unfold evalDualOption1 evalDualOption at hsome
    cases heq : evalDualOption e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      rw [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [DualInterval.neg, evalFunc1_neg_pi, deriv.neg]
      exact IntervalRat.mem_neg (ih d heq)
  | inv e' ih => exact evalDual?_der_correct_inv e' I D x hx hsome ih
  | sin e' ih =>
    unfold evalDualOption1 evalDualOption at hsome
    cases heq : evalDualOption e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      rw [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [DualInterval.sin]
      have hd := evalFunc1_differentiableAt_of_evalDualOption e' I d x hx heq
      rw [evalFunc1_sin, deriv_sin hd]
      exact IntervalRat.mem_mul (cos_mem_cosInterval_of_any _ _) (ih d heq)
  | cos e' ih =>
    unfold evalDualOption1 evalDualOption at hsome
    cases heq : evalDualOption e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      rw [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [DualInterval.cos]
      have hd := evalFunc1_differentiableAt_of_evalDualOption e' I d x hx heq
      rw [evalFunc1_cos, deriv_cos hd]
      exact IntervalRat.mem_mul (neg_sin_mem_neg_sinInterval _ _) (ih d heq)
  | exp e' ih =>
    unfold evalDualOption1 evalDualOption at hsome
    cases heq : evalDualOption e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      rw [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [DualInterval.exp]
      have hd := evalFunc1_differentiableAt_of_evalDualOption e' I d x hx heq
      rw [evalFunc1_exp, deriv_exp hd]
      have hval := evalDualOption1_val_correct e' I d x hx heq
      have hexp := IntervalRat.mem_expInterval hval
      exact IntervalRat.mem_mul hexp (ih d heq)
  | sinh e' ih =>
    unfold evalDualOption1 evalDualOption at hsome
    cases heq : evalDualOption e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      rw [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [DualInterval.sinh, coshInterval]
      have hd := evalFunc1_differentiableAt_of_evalDualOption e' I d x hx heq
      change deriv (fun t => Real.sinh (evalFunc1 e' t)) x ∈
        IntervalRat.mul (IntervalRat.coshComputable d.val 10) d.der
      have hder :
          HasDerivAt (fun t => Real.sinh (evalFunc1 e' t))
            (Real.cosh (evalFunc1 e' x) * deriv (evalFunc1 e') x) x :=
        (Real.hasDerivAt_sinh (evalFunc1 e' x)).comp x hd.hasDerivAt
      rw [hder.deriv]
      have hval := evalDualOption1_val_correct e' I d x hx heq
      have hcosh := IntervalRat.mem_coshComputable hval 10
      exact IntervalRat.mem_mul hcosh (ih d heq)
  | cosh e' ih =>
    unfold evalDualOption1 evalDualOption at hsome
    cases heq : evalDualOption e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      rw [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [DualInterval.cosh, sinhInterval]
      have hd := evalFunc1_differentiableAt_of_evalDualOption e' I d x hx heq
      change deriv (fun t => Real.cosh (evalFunc1 e' t)) x ∈
        IntervalRat.mul (IntervalRat.sinhComputable d.val 10) d.der
      have hder :
          HasDerivAt (fun t => Real.cosh (evalFunc1 e' t))
            (Real.sinh (evalFunc1 e' x) * deriv (evalFunc1 e') x) x :=
        (Real.hasDerivAt_cosh (evalFunc1 e' x)).comp x hd.hasDerivAt
      rw [hder.deriv]
      have hval := evalDualOption1_val_correct e' I d x hx heq
      have hsinh := IntervalRat.mem_sinhComputable hval 10
      exact IntervalRat.mem_mul hsinh (ih d heq)
  | tanh _ _ =>
    unfold evalDualOption1 evalDualOption at hsome
    contradiction
  | log e' ih => exact evalDual?_der_correct_log e' I D x hx hsome ih
  | atan e' ih =>
    unfold evalDualOption1 evalDualOption at hsome
    cases heq : evalDualOption e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      rw [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [DualInterval.atan]
      have hd := evalFunc1_differentiableAt_of_evalDualOption e' I d x hx heq
      rw [evalFunc1_atan]
      -- deriv (arctan ∘ f) x = (1 / (1 + f(x)²)) * f'(x)
      have heq_deriv := HasDerivAt.arctan (hd.hasDerivAt)
      rw [heq_deriv.deriv, mul_comm]
      -- The factor 1/(1+f(x)²) is in unitInterval
      have hfactor := DualInterval.arctan_deriv_factor_mem_unitInterval (evalFunc1 e' x)
      exact IntervalRat.mem_mul (ih d heq) hfactor
  | arsinh e' ih =>
    unfold evalDualOption1 evalDualOption at hsome
    cases heq : evalDualOption e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      rw [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [DualInterval.arsinh]
      have hd := evalFunc1_differentiableAt_of_evalDualOption e' I d x hx heq
      rw [evalFunc1_arsinh]
      -- deriv (arsinh ∘ f) x = (√(1 + f(x)²))⁻¹ • f'(x)
      have heq_deriv := HasDerivAt.arsinh (hd.hasDerivAt)
      rw [heq_deriv.deriv, smul_eq_mul, mul_comm]
      -- The factor 1/√(1+f(x)²) is in unitInterval
      have hfactor := DualInterval.arsinh_deriv_factor_mem_unitInterval (evalFunc1 e' x)
      exact IntervalRat.mem_mul (ih d heq) hfactor
  | atanh _ _ =>
    -- evalDualOption returns none for atanh, so hsome is a contradiction
    simp only [evalDualOption1, evalDualOption] at hsome
    contradiction
  | sinc e' ih =>
    unfold evalDualOption1 evalDualOption at hsome
    cases heq : evalDualOption e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      rw [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [DualInterval.sinc]
      -- The derivative of sinc ∘ f is sinc'(f(x)) * f'(x)
      -- sinc'(y) ∈ [-1, 1] for all y, and f'(x) ∈ d.der
      have hd_inner := evalFunc1_differentiableAt_of_evalDualOption e' I d x hx heq
      have heq_comp : (fun t => Real.sinc (evalFunc1 e' t)) = Real.sinc ∘ evalFunc1 e' := rfl
      rw [evalFunc1_sinc, heq_comp, deriv_comp x Real.differentiable_sinc.differentiableAt hd_inner]
      -- deriv sinc (evalFunc1 e' x) * deriv (evalFunc1 e') x ∈ sincDerivBound * d.der
      have hsinc_bound : deriv Real.sinc (evalFunc1 e' x) ∈ DualInterval.sincDerivBound := by
        simp only [DualInterval.sincDerivBound, IntervalRat.mem_def, Rat.cast_neg, Rat.cast_one]
        exact Real.deriv_sinc_mem_Icc (evalFunc1 e' x)
      have hder := ih d heq
      exact IntervalRat.mem_mul hsinc_bound hder
  | erf e' ih => exact evalDual?_der_correct_erf e' I D x hx hsome ih
  | sqrt e' ih => exact evalDual?_der_correct_sqrt e' I D x hx hsome ih
  | namedConst c =>
    simp only [evalDualOption1, evalDualOption, Option.some.injEq] at hsome
    rw [← hsome]
    simp only [evalFunc1_namedConst, deriv_const, DualInterval.ofMathConst]
    convert IntervalRat.mem_singleton 0 using 1
    norm_cast

/-- Combined correctness theorem for evalDualOption1 -/
theorem evalDualOption1_correct (e : Expr)
    (I : IntervalRat) (D : DualInterval) (x : ℝ) (hx : x ∈ I)
    (hsome : evalDualOption1 e I = some D) :
    Expr.eval (fun _ => x) e ∈ D.val ∧ deriv (evalFunc1 e) x ∈ D.der :=
  ⟨evalDualOption1_val_correct e I D x hx hsome, evalDualOption_der_correct e I D x hx hsome⟩

end LeanCert.Engine

end

end

section

/-
Copyright (c) 2025 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
/-!
# High-Performance Dyadic Interval Evaluator

This evaluator replaces `Rat` with `Dyadic` to prevent denominator explosion.
It is designed for complex expressions where the standard evaluator becomes slow.

## Main definitions

* `DyadicConfig` - Configuration for precision and Taylor depth
* `LeanCert.Internal.Dyadic.evalUnchecked` - Dyadic interval evaluator for expressions
* `evalIntervalDyadic_correct` - Correctness theorem

## Performance

In v1.0, every `Rat` multiplication required GCD normalization. For deep
expressions (e.g., Taylor series with 20+ terms, or optimization with 100+
iterations), denominators grow exponentially, causing timeouts.

In v1.1, Dyadic arithmetic uses bit-shifts instead of GCD. With `roundOut`,
we can enforce a maximum precision after each operation, keeping computation
bounded regardless of expression depth.

## Example

Consider computing `sin(sin(sin(x)))` with 15-term Taylor series:
- v1.0 (Rat): ~500ms per call, denominators grow to millions of digits
- v1.1 (Dyadic): ~5ms per call, precision stays at 53 bits

## Design notes

For transcendental functions (sin, cos, exp), we delegate to the existing
`IntervalRat` implementation with Taylor series, then convert the result
to `IntervalDyadic` with outward rounding. This reuses verified code while
gaining the performance benefits of Dyadic for polynomial operations.
-/

/-! ### Configuration -/

public section

namespace LeanCert.Engine

open LeanCert.Core

/-- Configuration for Dyadic interval evaluation.

* `precision` - Minimum exponent for outward rounding. A value of -53 gives
  IEEE double-like precision (~15 decimal digits). Use -100 for higher precision.
* `taylorDepth` - Number of Taylor terms for transcendental functions.
-/
structure DyadicConfig where
  /-- Minimum exponent (higher = coarser). -53 ≈ IEEE double precision. -/
  precision : Int := -53
  /-- Number of Taylor series terms for transcendental functions -/
  taylorDepth : Nat := 10
  deriving Repr, DecidableEq

/-- Default configuration with IEEE double-like precision -/
instance : Inhabited DyadicConfig := ⟨{}⟩

/-- High-precision configuration for critical calculations -/
def DyadicConfig.highPrecision : DyadicConfig :=
  { precision := -100, taylorDepth := 20 }

/-- Fast configuration for rapid evaluation (lower precision) -/
def DyadicConfig.fast : DyadicConfig :=
  { precision := -30, taylorDepth := 8 }

/-! ### Variable Environment -/

/-- Variable assignment as Dyadic intervals -/
abbrev IntervalDyadicEnv := Nat → IntervalDyadic

/-- Convert a rational interval environment to Dyadic -/
def toDyadicEnv (ρ : IntervalEnv) (prec : Int := -53) : IntervalDyadicEnv :=
  fun i => IntervalDyadic.ofIntervalRat (ρ i) prec

/-! ### Transcendental Function Wrappers -/

/-- Compute sin interval using rational Taylor series, convert to Dyadic -/
def sinIntervalDyadic (I : IntervalDyadic) (cfg : DyadicConfig) : IntervalDyadic :=
  let Irat := I.toIntervalRat
  let result := IntervalRat.sinComputable Irat cfg.taylorDepth
  IntervalDyadic.ofIntervalRat result cfg.precision

/-- Compute cos interval using rational Taylor series, convert to Dyadic -/
def cosIntervalDyadic (I : IntervalDyadic) (cfg : DyadicConfig) : IntervalDyadic :=
  let Irat := I.toIntervalRat
  let result := IntervalRat.cosComputable Irat cfg.taylorDepth
  IntervalDyadic.ofIntervalRat result cfg.precision

/-- Compute exp interval using rational Taylor series, convert to Dyadic -/
def expIntervalDyadic (I : IntervalDyadic) (cfg : DyadicConfig) : IntervalDyadic :=
  let Irat := I.toIntervalRat
  let result := IntervalRat.expComputable Irat cfg.taylorDepth
  IntervalDyadic.ofIntervalRat result cfg.precision

/-- Compute sinh interval using rational Taylor series, convert to Dyadic -/
def sinhIntervalDyadic (I : IntervalDyadic) (cfg : DyadicConfig) : IntervalDyadic :=
  let Irat := I.toIntervalRat
  let result := IntervalRat.sinhComputable Irat cfg.taylorDepth
  IntervalDyadic.ofIntervalRat result cfg.precision

/-- Compute cosh interval using rational Taylor series, convert to Dyadic -/
def coshIntervalDyadic (I : IntervalDyadic) (cfg : DyadicConfig) : IntervalDyadic :=
  let Irat := I.toIntervalRat
  let result := IntervalRat.coshComputable Irat cfg.taylorDepth
  IntervalDyadic.ofIntervalRat result cfg.precision

/-- atan interval: global bound [-2, 2] -/
def atanIntervalDyadic (_I : IntervalDyadic) (_cfg : DyadicConfig) : IntervalDyadic :=
  let neg2 := Core.Dyadic.ofInt (-2)
  let pos2 := Core.Dyadic.ofInt 2
  ⟨neg2, pos2, by rw [Dyadic.toRat_ofInt, Dyadic.toRat_ofInt]; norm_num⟩

/-- tanh interval: global bound [-1, 1] -/
def tanhIntervalDyadic (_I : IntervalDyadic) (_cfg : DyadicConfig) : IntervalDyadic :=
  let neg1 := Core.Dyadic.ofInt (-1)
  let pos1 := Core.Dyadic.ofInt 1
  ⟨neg1, pos1, by rw [Dyadic.toRat_ofInt, Dyadic.toRat_ofInt]; norm_num⟩

/-- arsinh interval: wide box bound via rational arsinhInterval -/
def arsinhIntervalDyadic (I : IntervalDyadic) (cfg : DyadicConfig) : IntervalDyadic :=
  let Irat := I.toIntervalRat
  let result := arsinhInterval Irat
  IntervalDyadic.ofIntervalRat result cfg.precision

/-- atanh interval: computable Taylor series via rational atanhComputable -/
def atanhIntervalDyadic (I : IntervalDyadic) (cfg : DyadicConfig) : IntervalDyadic :=
  let Irat := I.toIntervalRat
  let result := IntervalRat.atanhComputable Irat cfg.taylorDepth
  IntervalDyadic.ofIntervalRat result cfg.precision

/-- sinc interval: global bound [-1, 1] -/
def sincIntervalDyadic (_I : IntervalDyadic) (_cfg : DyadicConfig) : IntervalDyadic :=
  let neg1 := Core.Dyadic.ofInt (-1)
  let pos1 := Core.Dyadic.ofInt 1
  ⟨neg1, pos1, by rw [Dyadic.toRat_ofInt, Dyadic.toRat_ofInt]; norm_num⟩

/-- erf interval: global bound [-1, 1] -/
def erfIntervalDyadic (_I : IntervalDyadic) (_cfg : DyadicConfig) : IntervalDyadic :=
  let neg1 := Core.Dyadic.ofInt (-1)
  let pos1 := Core.Dyadic.ofInt 1
  ⟨neg1, pos1, by rw [Dyadic.toRat_ofInt, Dyadic.toRat_ofInt]; norm_num⟩

/-- Compute inv interval: convert to Rat, use invInterval, convert back to Dyadic -/
def invIntervalDyadic (I : IntervalDyadic) (cfg : DyadicConfig) : IntervalDyadic :=
  let Irat := I.toIntervalRat
  let result := invInterval Irat
  IntervalDyadic.ofIntervalRat result cfg.precision

/-- sqrt interval: uses conservative bound [0, max(hi, 1)] -/
def sqrtIntervalDyadic (I : IntervalDyadic) (cfg : DyadicConfig) : IntervalDyadic :=
  IntervalDyadic.sqrt I cfg.precision

/-- log interval: conservative global bound.
    For any x > 0, log(x) ∈ (-∞, ∞), but we use a finite interval.
    For x ∈ [lo, hi] with lo > 0:
    - log is monotone, so log(x) ∈ [log(lo), log(hi)]
    - Legacy total-evaluator fallback; strict callers reject this domain -/
def logIntervalDyadic (I : IntervalDyadic) (cfg : DyadicConfig) : IntervalDyadic :=
  -- Compute log using Taylor series via atanh reduction
  -- Convert to rational, compute, convert back with outward rounding
  let IRat := I.toIntervalRat
  if IRat.lo > 0 then
    let result := IntervalRat.logComputable IRat cfg.taylorDepth
    IntervalDyadic.ofIntervalRat result cfg.precision
  else
    -- Legacy heuristic sentinel for invalid input. It is not a sound log
    -- enclosure; `evalIntervalDyadicChecked` rejects this branch.
    ⟨Core.Dyadic.ofInt (-1000), Core.Dyadic.ofInt 1000, by simp [Dyadic.toRat_ofInt]⟩

/-- Real power from a cached logarithm interval.

    If `Real.log x ∈ logBase`, this computes an interval for
    `x ^ (p : ℝ)` as `exp(p * log x)` without recomputing `log x`.
    This is the hot-path primitive for cached finite sums with many terms of
    the form `x ^ q_k`. -/
def rpowFromCachedLogDyadic (logBase : IntervalDyadic) (p : ℚ)
    (cfg : DyadicConfig) : IntervalDyadic :=
  let pInterval := IntervalDyadic.ofIntervalRat (IntervalRat.singleton p) cfg.precision
  let pLogBase := (IntervalDyadic.mul pInterval logBase).roundOut cfg.precision
  expIntervalDyadic pLogBase cfg

/-- Real power x^p for x > 0 and rational p, computed via exp(p * log(x)).

    For x ∈ [lo, hi] with lo > 0 and rational exponent p:
    - x^p = exp(p * log(x))
    - We compute log(x), multiply by p, then apply exp

    This is the key operation for BKLNW-style sums where terms are x^(1/k - 1/3). -/
def rpowIntervalDyadic (base : IntervalDyadic) (p : ℚ) (cfg : DyadicConfig) : IntervalDyadic :=
  -- x^p = exp(p * log(x)) for x > 0
  let logBase := logIntervalDyadic base cfg
  rpowFromCachedLogDyadic logBase p cfg

/-- Correctness of `rpowFromCachedLogDyadic`: a cached interval containing
    `Real.log x` is enough to enclose `x ^ p`. -/
theorem mem_rpowFromCachedLogDyadic {x : ℝ} {logBase : IntervalDyadic}
    (hlog : Real.log x ∈ logBase) (hx_pos : 0 < x)
    (p : ℚ) (cfg : DyadicConfig) (hprec : cfg.precision ≤ 0 := by norm_num) :
    x ^ (p : ℝ) ∈ rpowFromCachedLogDyadic logBase p cfg := by
  simp only [rpowFromCachedLogDyadic]
  rw [Real.rpow_def_of_pos hx_pos, mul_comm]
  have hp_mem : (p : ℝ) ∈
      IntervalDyadic.ofIntervalRat (IntervalRat.singleton p) cfg.precision := by
    apply IntervalDyadic.mem_ofIntervalRat
    · exact IntervalRat.mem_singleton p
    · exact hprec
  have hmul := IntervalDyadic.mem_mul hp_mem hlog
  have hmul_rounded := IntervalDyadic.roundOut_contains hmul cfg.precision
  simp only [expIntervalDyadic]
  have hrat := IntervalDyadic.mem_toIntervalRat.mp hmul_rounded
  have hexp := IntervalRat.mem_expComputable hrat cfg.taylorDepth
  exact IntervalDyadic.mem_ofIntervalRat hexp cfg.precision hprec

/-- Correctness of rpowIntervalDyadic: if x ∈ base and base.lo > 0, then x^p ∈ result -/
theorem mem_rpowIntervalDyadic {x : ℝ} {base : IntervalDyadic} (hx : x ∈ base)
    (hpos : base.toIntervalRat.lo > 0) (p : ℚ) (cfg : DyadicConfig)
    (hprec : cfg.precision ≤ 0 := by norm_num) :
    x ^ (p : ℝ) ∈ rpowIntervalDyadic base p cfg := by
  simp only [rpowIntervalDyadic]
  have hx_pos : 0 < x := by
    have hlo := hx.1
    have hlo_pos : (0 : ℝ) < base.lo.toRat := by exact_mod_cast hpos
    linarith
  have hlog_mem : Real.log x ∈ logIntervalDyadic base cfg := by
    simp only [logIntervalDyadic, hpos, ↓reduceIte]
    have hrat := IntervalDyadic.mem_toIntervalRat.mp hx
    have hlog := IntervalRat.mem_logComputable hrat hpos cfg.taylorDepth
    exact IntervalDyadic.mem_ofIntervalRat hlog cfg.precision hprec
  exact mem_rpowFromCachedLogDyadic hlog_mem hx_pos p cfg hprec

/-! ### Main Evaluator -/

end LeanCert.Engine

namespace LeanCert.Internal.Dyadic

open LeanCert.Core LeanCert.Engine

/-- High-performance Dyadic interval evaluator.

This is the core function for v1.1. It evaluates expressions using Dyadic
arithmetic for polynomial operations (add, mul, neg) and delegates to
rational Taylor series for transcendentals.

Returns an interval guaranteed to contain all possible values of the expression
when `ExprSupportedCore` holds. For other expressions, it computes conservative
fallbacks (e.g., inv/log), but the core correctness theorem does not apply. -/
def evalUnchecked (e : Expr) (ρ : IntervalDyadicEnv) (cfg : DyadicConfig := {}) : IntervalDyadic :=
  match e with
  | Expr.const q =>
      -- Convert rational constant to Dyadic interval with outward rounding
      IntervalDyadic.ofIntervalRat (IntervalRat.singleton q) cfg.precision
  | Expr.var idx => ρ idx
  | Expr.add e₁ e₂ =>
      let I₁ := LeanCert.Internal.Dyadic.evalUnchecked e₁ ρ cfg
      let I₂ := LeanCert.Internal.Dyadic.evalUnchecked e₂ ρ cfg
      (IntervalDyadic.add I₁ I₂).roundOut cfg.precision
  | Expr.mul e₁ e₂ =>
      let I₁ := LeanCert.Internal.Dyadic.evalUnchecked e₁ ρ cfg
      let I₂ := LeanCert.Internal.Dyadic.evalUnchecked e₂ ρ cfg
      (IntervalDyadic.mul I₁ I₂).roundOut cfg.precision
  | Expr.neg e =>
      let I := LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg
      IntervalDyadic.neg I  -- Negation doesn't increase precision
  | Expr.inv e => invIntervalDyadic (LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg) cfg
  | Expr.exp e => expIntervalDyadic (LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg) cfg
  | Expr.sin e => sinIntervalDyadic (LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg) cfg
  | Expr.cos e => cosIntervalDyadic (LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg) cfg
  | Expr.log e => logIntervalDyadic (LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg) cfg
  | Expr.atan e => atanIntervalDyadic (LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg) cfg
  | Expr.arsinh e => arsinhIntervalDyadic (LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg) cfg
  | Expr.atanh e => atanhIntervalDyadic (LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg) cfg
  | Expr.sinc e => sincIntervalDyadic (LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg) cfg
  | Expr.erf e => erfIntervalDyadic (LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg) cfg
  | Expr.sinh e => sinhIntervalDyadic (LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg) cfg
  | Expr.cosh e => coshIntervalDyadic (LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg) cfg
  | Expr.tanh e => tanhIntervalDyadic (LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg) cfg
  | Expr.sqrt e => sqrtIntervalDyadic (LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg) cfg
  | Expr.namedConst c => IntervalDyadic.ofIntervalRat c.interval cfg.precision

end LeanCert.Internal.Dyadic

namespace LeanCert.Engine

open LeanCert.Core

/-! ### Correctness -/

/-- A real environment is contained in a Dyadic interval environment -/
def envMemDyadic (ρ_real : Nat → ℝ) (ρ_dyad : IntervalDyadicEnv) : Prop :=
  ∀ i, ρ_real i ∈ ρ_dyad i

/-- Domain validity for Dyadic evaluation.
    This is defined directly in terms of LeanCert.Internal.Dyadic.evalUnchecked to ensure
    compatibility.
    For log, we require the argument interval (converted to Rat) to have positive lower bound. -/
def evalDomainValidDyadic (e : Expr) (ρ : IntervalDyadicEnv) (cfg : DyadicConfig := {}) : Prop :=
  match e with
  | Expr.const _ => True
  | Expr.var _ => True
  | Expr.add e₁ e₂ => evalDomainValidDyadic e₁ ρ cfg ∧ evalDomainValidDyadic e₂ ρ cfg
  | Expr.mul e₁ e₂ => evalDomainValidDyadic e₁ ρ cfg ∧ evalDomainValidDyadic e₂ ρ cfg
  | Expr.neg e => evalDomainValidDyadic e ρ cfg
  | Expr.inv e => evalDomainValidDyadic e ρ cfg ∧
      ((LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg).toIntervalRat.lo > 0 ∨
       (LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg).toIntervalRat.hi < 0)
  | Expr.exp e => evalDomainValidDyadic e ρ cfg
  | Expr.sin e => evalDomainValidDyadic e ρ cfg
  | Expr.cos e => evalDomainValidDyadic e ρ cfg
  | Expr.log e => evalDomainValidDyadic e ρ cfg ∧ (LeanCert.Internal.Dyadic.evalUnchecked e ρ
    cfg).toIntervalRat.lo > 0
  | Expr.atan e => evalDomainValidDyadic e ρ cfg
  | Expr.arsinh e => evalDomainValidDyadic e ρ cfg
  | Expr.atanh e => evalDomainValidDyadic e ρ cfg ∧
      (LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg).toIntervalRat.lo > -1 ∧
      (LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg).toIntervalRat.hi < 1
  | Expr.sinc e => evalDomainValidDyadic e ρ cfg
  | Expr.erf e => evalDomainValidDyadic e ρ cfg
  | Expr.sinh e => evalDomainValidDyadic e ρ cfg
  | Expr.cosh e => evalDomainValidDyadic e ρ cfg
  | Expr.tanh e => evalDomainValidDyadic e ρ cfg
  | Expr.sqrt e => evalDomainValidDyadic e ρ cfg
  | Expr.namedConst _ => True

/-- Computable (Bool) domain validity check for Dyadic evaluation. -/
def checkDomainValidDyadic (e : Expr) (ρ : IntervalDyadicEnv) (cfg : DyadicConfig := {}) : Bool :=
  match e with
  | Expr.const _ => true
  | Expr.var _ => true
  | Expr.add e₁ e₂ => checkDomainValidDyadic e₁ ρ cfg && checkDomainValidDyadic e₂ ρ cfg
  | Expr.mul e₁ e₂ => checkDomainValidDyadic e₁ ρ cfg && checkDomainValidDyadic e₂ ρ cfg
  | Expr.neg e => checkDomainValidDyadic e ρ cfg
  | Expr.inv e => checkDomainValidDyadic e ρ cfg &&
      (decide ((LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg).toIntervalRat.lo > 0) ||
       decide ((LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg).toIntervalRat.hi < 0))
  | Expr.exp e => checkDomainValidDyadic e ρ cfg
  | Expr.sin e => checkDomainValidDyadic e ρ cfg
  | Expr.cos e => checkDomainValidDyadic e ρ cfg
  | Expr.log e => checkDomainValidDyadic e ρ cfg &&
      decide ((LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg).toIntervalRat.lo > 0)
  | Expr.atan e => checkDomainValidDyadic e ρ cfg
  | Expr.arsinh e => checkDomainValidDyadic e ρ cfg
  | Expr.atanh e => checkDomainValidDyadic e ρ cfg &&
      decide ((LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg).toIntervalRat.lo > -1) &&
      decide ((LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg).toIntervalRat.hi < 1)
  | Expr.sinc e => checkDomainValidDyadic e ρ cfg
  | Expr.erf e => checkDomainValidDyadic e ρ cfg
  | Expr.sinh e => checkDomainValidDyadic e ρ cfg
  | Expr.cosh e => checkDomainValidDyadic e ρ cfg
  | Expr.tanh e => checkDomainValidDyadic e ρ cfg
  | Expr.sqrt e => checkDomainValidDyadic e ρ cfg
  | Expr.namedConst _ => true

theorem checkDomainValidDyadic_correct (e : Expr) (ρ : IntervalDyadicEnv) (cfg : DyadicConfig) :
    checkDomainValidDyadic e ρ cfg = true → evalDomainValidDyadic e ρ cfg := by
  induction e with
  | const _ => intro; trivial
  | var _ => intro; trivial
  | add e₁ e₂ ih₁ ih₂ =>
    simp only [checkDomainValidDyadic, Bool.and_eq_true, evalDomainValidDyadic]
    intro ⟨h1, h2⟩; exact ⟨ih₁ h1, ih₂ h2⟩
  | mul e₁ e₂ ih₁ ih₂ =>
    simp only [checkDomainValidDyadic, Bool.and_eq_true, evalDomainValidDyadic]
    intro ⟨h1, h2⟩; exact ⟨ih₁ h1, ih₂ h2⟩
  | neg e ih =>
    simp only [checkDomainValidDyadic, evalDomainValidDyadic]; exact ih
  | inv e ih =>
    simp only [checkDomainValidDyadic, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq, evalDomainValidDyadic]
    intro ⟨h1, h2⟩; exact ⟨ih h1, h2⟩
  | exp e ih => simp only [checkDomainValidDyadic, evalDomainValidDyadic]; exact ih
  | sin e ih => simp only [checkDomainValidDyadic, evalDomainValidDyadic]; exact ih
  | cos e ih => simp only [checkDomainValidDyadic, evalDomainValidDyadic]; exact ih
  | log e ih =>
    simp only [checkDomainValidDyadic, Bool.and_eq_true, decide_eq_true_eq, evalDomainValidDyadic]
    intro ⟨h1, h2⟩; exact ⟨ih h1, h2⟩
  | atan e ih => simp only [checkDomainValidDyadic, evalDomainValidDyadic]; exact ih
  | arsinh e ih => simp only [checkDomainValidDyadic, evalDomainValidDyadic]; exact ih
  | atanh e ih =>
    simp only [checkDomainValidDyadic, Bool.and_eq_true, decide_eq_true_eq, evalDomainValidDyadic]
    intro ⟨⟨h1, h2⟩, h3⟩; exact ⟨ih h1, h2, h3⟩
  | sinc e ih => simp only [checkDomainValidDyadic, evalDomainValidDyadic]; exact ih
  | erf e ih => simp only [checkDomainValidDyadic, evalDomainValidDyadic]; exact ih
  | sinh e ih => simp only [checkDomainValidDyadic, evalDomainValidDyadic]; exact ih
  | cosh e ih => simp only [checkDomainValidDyadic, evalDomainValidDyadic]; exact ih
  | tanh e ih => simp only [checkDomainValidDyadic, evalDomainValidDyadic]; exact ih
  | sqrt e ih => simp only [checkDomainValidDyadic, evalDomainValidDyadic]; exact ih
  | namedConst _ => intro; trivial

end LeanCert.Engine

namespace LeanCert.Internal.Dyadic

open LeanCert.Core LeanCert.Engine

/-- Static data prepared once for repeated Dyadic evaluation.

The context is operation-independent: logarithm, exponential, trigonometric,
and inverse-hyperbolic kernels share certified constants and coefficient
families without changing the public evaluator configuration. -/
structure PreparedContext where
  /-- Precision and rounding settings shared by prepared interval computations. -/
  cfg : DyadicConfig
  /-- A precomputed rational enclosure of the natural logarithm of two. -/
  ln2 : IntervalRat
  /-- Precomputed rational coefficients for the exponential Taylor polynomial. -/
  expCoeffs : List ℚ
  /-- Precomputed rational coefficients for the sine Taylor polynomial. -/
  sinCoeffs : List ℚ
  /-- Precomputed rational coefficients for the cosine Taylor polynomial. -/
  cosCoeffs : List ℚ
  /-- Precomputed rational coefficients for the inverse hyperbolic tangent expansion. -/
  atanhCoeffs : List ℚ
  deriving Repr

/-- Deterministically prepare all configuration-dependent numerical data. -/
@[expose]
def prepareContext (cfg : DyadicConfig) : PreparedContext :=
  { cfg
    ln2 := IntervalRat.ln2Computable cfg.taylorDepth
    expCoeffs := IntervalRat.expTaylorCoeffs cfg.taylorDepth
    sinCoeffs := IntervalRat.sinTaylorCoeffs cfg.taylorDepth
    cosCoeffs := IntervalRat.cosTaylorCoeffs cfg.taylorDepth
    atanhCoeffs := IntervalRat.atanhTaylorCoeffs cfg.taylorDepth }

@[simp] theorem prepareContext_cfg (cfg : DyadicConfig) :
    (prepareContext cfg).cfg = cfg := rfl

/-- Logarithm kernel using the context's prepared certified constants. -/
def logIntervalPrepared (I : IntervalDyadic) (ctx : PreparedContext) : IntervalDyadic :=
  let IRat := I.toIntervalRat
  if IRat.lo > 0 then
    let result := IntervalRat.logComputablePrepared IRat ctx.cfg.taylorDepth ctx.ln2
      ctx.atanhCoeffs
    IntervalDyadic.ofIntervalRat result ctx.cfg.precision
  else
    ⟨Core.Dyadic.ofInt (-1000), Core.Dyadic.ofInt 1000, by simp [Dyadic.toRat_ofInt]⟩

theorem logIntervalPrepared_prepareContext (I : IntervalDyadic) (cfg : DyadicConfig) :
    logIntervalPrepared I (prepareContext cfg) = logIntervalDyadic I cfg := by
  simp [logIntervalPrepared, prepareContext, logIntervalDyadic,
    IntervalRat.logComputablePrepared_eq]

/-- Exponential kernel using the context's prepared Taylor coefficients. -/
def expIntervalPrepared (I : IntervalDyadic) (ctx : PreparedContext) : IntervalDyadic :=
  let result := IntervalRat.expComputableWithCoeffs I.toIntervalRat ctx.cfg.taylorDepth
    ctx.expCoeffs
  IntervalDyadic.ofIntervalRat result ctx.cfg.precision

theorem expIntervalPrepared_prepareContext (I : IntervalDyadic) (cfg : DyadicConfig) :
    expIntervalPrepared I (prepareContext cfg) = expIntervalDyadic I cfg := by
  simp [expIntervalPrepared, prepareContext, expIntervalDyadic,
    IntervalRat.expComputableWithCoeffs_eq]

/-- Sine kernel using the context's prepared Taylor coefficients. -/
def sinIntervalPrepared (I : IntervalDyadic) (ctx : PreparedContext) : IntervalDyadic :=
  let result := IntervalRat.sinComputableWithCoeffs I.toIntervalRat ctx.cfg.taylorDepth
    ctx.sinCoeffs
  IntervalDyadic.ofIntervalRat result ctx.cfg.precision

theorem sinIntervalPrepared_prepareContext (I : IntervalDyadic) (cfg : DyadicConfig) :
    sinIntervalPrepared I (prepareContext cfg) = sinIntervalDyadic I cfg := by
  simp [sinIntervalPrepared, prepareContext, sinIntervalDyadic,
    IntervalRat.sinComputableWithCoeffs_eq]

/-- Cosine kernel using the context's prepared Taylor coefficients. -/
def cosIntervalPrepared (I : IntervalDyadic) (ctx : PreparedContext) : IntervalDyadic :=
  let result := IntervalRat.cosComputableWithCoeffs I.toIntervalRat ctx.cfg.taylorDepth
    ctx.cosCoeffs
  IntervalDyadic.ofIntervalRat result ctx.cfg.precision

theorem cosIntervalPrepared_prepareContext (I : IntervalDyadic) (cfg : DyadicConfig) :
    cosIntervalPrepared I (prepareContext cfg) = cosIntervalDyadic I cfg := by
  simp [cosIntervalPrepared, prepareContext, cosIntervalDyadic,
    IntervalRat.cosComputableWithCoeffs_eq]

/-- Inverse-hyperbolic-tangent kernel using prepared Taylor coefficients. -/
def atanhIntervalPrepared (I : IntervalDyadic) (ctx : PreparedContext) : IntervalDyadic :=
  let result := IntervalRat.atanhComputableWithCoeffs I.toIntervalRat ctx.cfg.taylorDepth
    ctx.atanhCoeffs
  IntervalDyadic.ofIntervalRat result ctx.cfg.precision

theorem atanhIntervalPrepared_prepareContext (I : IntervalDyadic) (cfg : DyadicConfig) :
    atanhIntervalPrepared I (prepareContext cfg) = atanhIntervalDyadic I cfg := by
  simp [atanhIntervalPrepared, prepareContext, atanhIntervalDyadic,
    IntervalRat.atanhComputableWithCoeffs_eq]

/-- Evaluate an expression and its domain-validity bit in one traversal.
The value component is exactly `LeanCert.Internal.Dyadic.evalUnchecked`; the validity component is
exactly `checkDomainValidDyadic`. -/
def evalCached (e : Expr) (ρ : IntervalDyadicEnv)
    (cfg : DyadicConfig := {}) : IntervalDyadic × Bool :=
  match e with
  | .const q =>
      (IntervalDyadic.ofIntervalRat (IntervalRat.singleton q) cfg.precision, true)
  | .var idx => (ρ idx, true)
  | .add e₁ e₂ =>
      let r₁ := LeanCert.Internal.Dyadic.evalCached e₁ ρ cfg
      let r₂ := LeanCert.Internal.Dyadic.evalCached e₂ ρ cfg
      ((IntervalDyadic.add r₁.1 r₂.1).roundOut cfg.precision, r₁.2 && r₂.2)
  | .mul e₁ e₂ =>
      let r₁ := LeanCert.Internal.Dyadic.evalCached e₁ ρ cfg
      let r₂ := LeanCert.Internal.Dyadic.evalCached e₂ ρ cfg
      ((IntervalDyadic.mul r₁.1 r₂.1).roundOut cfg.precision, r₁.2 && r₂.2)
  | .neg e =>
      let r := LeanCert.Internal.Dyadic.evalCached e ρ cfg
      (IntervalDyadic.neg r.1, r.2)
  | .inv e =>
      let r := LeanCert.Internal.Dyadic.evalCached e ρ cfg
      let I := r.1.toIntervalRat
      (invIntervalDyadic r.1 cfg, r.2 && (decide (I.lo > 0) || decide (I.hi < 0)))
  | .exp e =>
      let r := LeanCert.Internal.Dyadic.evalCached e ρ cfg
      (expIntervalDyadic r.1 cfg, r.2)
  | .sin e =>
      let r := LeanCert.Internal.Dyadic.evalCached e ρ cfg
      (sinIntervalDyadic r.1 cfg, r.2)
  | .cos e =>
      let r := LeanCert.Internal.Dyadic.evalCached e ρ cfg
      (cosIntervalDyadic r.1 cfg, r.2)
  | .log e =>
      let r := LeanCert.Internal.Dyadic.evalCached e ρ cfg
      (logIntervalDyadic r.1 cfg, r.2 && decide (r.1.toIntervalRat.lo > 0))
  | .atan e =>
      let r := LeanCert.Internal.Dyadic.evalCached e ρ cfg
      (atanIntervalDyadic r.1 cfg, r.2)
  | .arsinh e =>
      let r := LeanCert.Internal.Dyadic.evalCached e ρ cfg
      (arsinhIntervalDyadic r.1 cfg, r.2)
  | .atanh e =>
      let r := LeanCert.Internal.Dyadic.evalCached e ρ cfg
      let I := r.1.toIntervalRat
      (atanhIntervalDyadic r.1 cfg,
        r.2 && decide (I.lo > -1) && decide (I.hi < 1))
  | .sinc e =>
      let r := LeanCert.Internal.Dyadic.evalCached e ρ cfg
      (sincIntervalDyadic r.1 cfg, r.2)
  | .erf e =>
      let r := LeanCert.Internal.Dyadic.evalCached e ρ cfg
      (erfIntervalDyadic r.1 cfg, r.2)
  | .sinh e =>
      let r := LeanCert.Internal.Dyadic.evalCached e ρ cfg
      (sinhIntervalDyadic r.1 cfg, r.2)
  | .cosh e =>
      let r := LeanCert.Internal.Dyadic.evalCached e ρ cfg
      (coshIntervalDyadic r.1 cfg, r.2)
  | .tanh e =>
      let r := LeanCert.Internal.Dyadic.evalCached e ρ cfg
      (tanhIntervalDyadic r.1 cfg, r.2)
  | .sqrt e =>
      let r := LeanCert.Internal.Dyadic.evalCached e ρ cfg
      (sqrtIntervalDyadic r.1 cfg, r.2)
  | .namedConst c => (IntervalDyadic.ofIntervalRat c.interval cfg.precision, true)

/-- Prepared evaluator: identical certificate semantics to `evalCached`, but
configuration-dependent data is shared across every evaluation. -/
def evalPreparedCached (e : Expr) (ρ : IntervalDyadicEnv)
    (ctx : PreparedContext) : IntervalDyadic × Bool :=
  match e with
  | .const q =>
      (IntervalDyadic.ofIntervalRat (IntervalRat.singleton q) ctx.cfg.precision, true)
  | .var idx => (ρ idx, true)
  | .add e₁ e₂ =>
      let r₁ := evalPreparedCached e₁ ρ ctx
      let r₂ := evalPreparedCached e₂ ρ ctx
      ((IntervalDyadic.add r₁.1 r₂.1).roundOut ctx.cfg.precision, r₁.2 && r₂.2)
  | .mul e₁ e₂ =>
      let r₁ := evalPreparedCached e₁ ρ ctx
      let r₂ := evalPreparedCached e₂ ρ ctx
      ((IntervalDyadic.mul r₁.1 r₂.1).roundOut ctx.cfg.precision, r₁.2 && r₂.2)
  | .neg e =>
      let r := evalPreparedCached e ρ ctx
      (IntervalDyadic.neg r.1, r.2)
  | .inv e =>
      let r := evalPreparedCached e ρ ctx
      let I := r.1.toIntervalRat
      (invIntervalDyadic r.1 ctx.cfg, r.2 && (decide (I.lo > 0) || decide (I.hi < 0)))
  | .exp e =>
      let r := evalPreparedCached e ρ ctx
      (expIntervalPrepared r.1 ctx, r.2)
  | .sin e =>
      let r := evalPreparedCached e ρ ctx
      (sinIntervalPrepared r.1 ctx, r.2)
  | .cos e =>
      let r := evalPreparedCached e ρ ctx
      (cosIntervalPrepared r.1 ctx, r.2)
  | .log e =>
      let r := evalPreparedCached e ρ ctx
      (logIntervalPrepared r.1 ctx, r.2 && decide (r.1.toIntervalRat.lo > 0))
  | .atan e =>
      let r := evalPreparedCached e ρ ctx
      (atanIntervalDyadic r.1 ctx.cfg, r.2)
  | .arsinh e =>
      let r := evalPreparedCached e ρ ctx
      (arsinhIntervalDyadic r.1 ctx.cfg, r.2)
  | .atanh e =>
      let r := evalPreparedCached e ρ ctx
      let I := r.1.toIntervalRat
      (atanhIntervalPrepared r.1 ctx,
        r.2 && decide (I.lo > -1) && decide (I.hi < 1))
  | .sinc e =>
      let r := evalPreparedCached e ρ ctx
      (sincIntervalDyadic r.1 ctx.cfg, r.2)
  | .erf e =>
      let r := evalPreparedCached e ρ ctx
      (erfIntervalDyadic r.1 ctx.cfg, r.2)
  | .sinh e =>
      let r := evalPreparedCached e ρ ctx
      (sinhIntervalDyadic r.1 ctx.cfg, r.2)
  | .cosh e =>
      let r := evalPreparedCached e ρ ctx
      (coshIntervalDyadic r.1 ctx.cfg, r.2)
  | .tanh e =>
      let r := evalPreparedCached e ρ ctx
      (tanhIntervalDyadic r.1 ctx.cfg, r.2)
  | .sqrt e =>
      let r := evalPreparedCached e ρ ctx
      (sqrtIntervalDyadic r.1 ctx.cfg, r.2)
  | .namedConst c =>
      (IntervalDyadic.ofIntervalRat c.interval ctx.cfg.precision, true)

end LeanCert.Internal.Dyadic

namespace LeanCert.Engine

open LeanCert.Core

theorem evalIntervalDyadicCached_fst (e : Expr) (ρ : IntervalDyadicEnv)
    (cfg : DyadicConfig := {}) :
    (LeanCert.Internal.Dyadic.evalCached e ρ cfg).1 = LeanCert.Internal.Dyadic.evalUnchecked e ρ
      cfg := by
  induction e <;> simp [LeanCert.Internal.Dyadic.evalCached,
    LeanCert.Internal.Dyadic.evalUnchecked, *]

theorem evalIntervalDyadicCached_snd (e : Expr) (ρ : IntervalDyadicEnv)
    (cfg : DyadicConfig := {}) :
    (LeanCert.Internal.Dyadic.evalCached e ρ cfg).2 = checkDomainValidDyadic e ρ cfg := by
  induction e <;>
    simp [LeanCert.Internal.Dyadic.evalCached, checkDomainValidDyadic,
      evalIntervalDyadicCached_fst, *]

theorem evalIntervalDyadicPreparedCached_fst (e : Expr) (ρ : IntervalDyadicEnv)
    (cfg : DyadicConfig := {}) :
    (LeanCert.Internal.Dyadic.evalPreparedCached e ρ
      (LeanCert.Internal.Dyadic.prepareContext cfg)).1 =
      LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg := by
  induction e <;>
    simp [LeanCert.Internal.Dyadic.evalPreparedCached,
      LeanCert.Internal.Dyadic.evalUnchecked,
      LeanCert.Internal.Dyadic.logIntervalPrepared_prepareContext,
      LeanCert.Internal.Dyadic.expIntervalPrepared_prepareContext,
      LeanCert.Internal.Dyadic.sinIntervalPrepared_prepareContext,
      LeanCert.Internal.Dyadic.cosIntervalPrepared_prepareContext,
      LeanCert.Internal.Dyadic.atanhIntervalPrepared_prepareContext, *]

theorem evalIntervalDyadicPreparedCached_snd (e : Expr) (ρ : IntervalDyadicEnv)
    (cfg : DyadicConfig := {}) :
    (LeanCert.Internal.Dyadic.evalPreparedCached e ρ
      (LeanCert.Internal.Dyadic.prepareContext cfg)).2 =
      checkDomainValidDyadic e ρ cfg := by
  induction e <;>
    simp [LeanCert.Internal.Dyadic.evalPreparedCached,
      checkDomainValidDyadic,
      evalIntervalDyadicPreparedCached_fst, *]

/-- Diagnose the first failed Dyadic domain check. -/
def diagnoseEvalIntervalDyadicFailure (e : Expr) (ρ : IntervalDyadicEnv)
    (cfg : DyadicConfig := {}) : EvalError :=
  match e with
  | .add e₁ e₂ | .mul e₁ e₂ =>
      if checkDomainValidDyadic e₁ ρ cfg then
        .nestedFailure "right operand" (diagnoseEvalIntervalDyadicFailure e₂ ρ cfg)
      else
        .nestedFailure "left operand" (diagnoseEvalIntervalDyadicFailure e₁ ρ cfg)
  | .neg e | .exp e | .sin e | .cos e | .atan e | .arsinh e | .sinc e |
      .erf e | .sinh e | .cosh e | .tanh e | .sqrt e =>
      .nestedFailure "unary operand" (diagnoseEvalIntervalDyadicFailure e ρ cfg)
  | .inv e =>
      if checkDomainValidDyadic e ρ cfg then
        .reciprocalContainsZero (LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg).toIntervalRat
      else
        .nestedFailure "reciprocal operand" (diagnoseEvalIntervalDyadicFailure e ρ cfg)
  | .log e =>
      if checkDomainValidDyadic e ρ cfg then
        .logNonpositive (LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg).toIntervalRat
      else
        .nestedFailure "logarithm operand" (diagnoseEvalIntervalDyadicFailure e ρ cfg)
  | .atanh e =>
      if checkDomainValidDyadic e ρ cfg then
        .atanhOutsideUnitBall (LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg).toIntervalRat
      else
        .nestedFailure "atanh operand" (diagnoseEvalIntervalDyadicFailure e ρ cfg)
  | .const _ | .var _ | .namedConst _ =>
      .unsupportedBackend "internal: total Dyadic expression unexpectedly failed"
termination_by e

/-- Checked Dyadic evaluator. The finite fallback branches of the legacy total
evaluator are never exposed after a failed domain check. -/
def evalIntervalDyadicChecked (e : Expr) (ρ : IntervalDyadicEnv)
    (cfg : DyadicConfig := {}) : EvalResult IntervalDyadic :=
  let cached := LeanCert.Internal.Dyadic.evalCached e ρ cfg
  if cached.2 then
    .ok cached.1
  else
    .error (diagnoseEvalIntervalDyadicFailure e ρ cfg)

/-- Domain validity is trivially true for ADSupported expressions (which exclude log). -/
theorem evalDomainValidDyadic_of_ExprSupported {e : Expr} (hsupp : ADSupported e)
    (ρ : IntervalDyadicEnv) (cfg : DyadicConfig := {}) : evalDomainValidDyadic e ρ cfg := by
  induction hsupp with
  | const _ => trivial
  | var _ => trivial
  | add _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | mul _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | neg _ ih => exact ih
  | sin _ ih => exact ih
  | cos _ ih => exact ih
  | exp _ ih => exact ih

/-- Fundamental correctness theorem for Dyadic evaluation.

This theorem states that for any supported expression and any real values
within the input intervals, the result of evaluating the expression is
contained in the computed Dyadic interval.

The proof follows the same structure as `evalIntervalCore_correct`, but
with additional steps for handling Dyadic ↔ Rat conversions and rounding.
Requires cfg.precision ≤ 0 (the default -53 satisfies this).

Note: Requires domain validity for log (positive argument interval). -/
theorem evalIntervalDyadic_correct (e : Expr) (hsupp : ExprSupportedCore e)
    (ρ_real : Nat → ℝ) (ρ_dyad : IntervalDyadicEnv)
    (hρ : envMemDyadic ρ_real ρ_dyad) (cfg : DyadicConfig := {})
    (hprec : cfg.precision ≤ 0 := by norm_num)
    (hdom : evalDomainValidDyadic e ρ_dyad cfg) :
    Expr.eval ρ_real e ∈ LeanCert.Internal.Dyadic.evalUnchecked e ρ_dyad cfg := by
  induction hsupp with
  | const q =>
    simp only [Expr.eval_const, LeanCert.Internal.Dyadic.evalUnchecked]
    apply IntervalDyadic.mem_ofIntervalRat
    · exact IntervalRat.mem_singleton q
    · exact hprec
  | var idx =>
    simp only [Expr.eval_var, LeanCert.Internal.Dyadic.evalUnchecked]
    exact hρ idx
  | add _ _ ih₁ ih₂ =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_add, LeanCert.Internal.Dyadic.evalUnchecked]
    have h := IntervalDyadic.mem_add (ih₁ hdom.1) (ih₂ hdom.2)
    exact IntervalDyadic.roundOut_contains h cfg.precision
  | mul _ _ ih₁ ih₂ =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_mul, LeanCert.Internal.Dyadic.evalUnchecked]
    have h := IntervalDyadic.mem_mul (ih₁ hdom.1) (ih₂ hdom.2)
    exact IntervalDyadic.roundOut_contains h cfg.precision
  | neg _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_neg, LeanCert.Internal.Dyadic.evalUnchecked]
    exact IntervalDyadic.mem_neg (ih hdom)
  | sin _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_sin, LeanCert.Internal.Dyadic.evalUnchecked, sinIntervalDyadic]
    have hrat := IntervalDyadic.mem_toIntervalRat.mp (ih hdom)
    have hsin := IntervalRat.mem_sinComputable hrat cfg.taylorDepth
    exact IntervalDyadic.mem_ofIntervalRat hsin cfg.precision hprec
  | cos _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_cos, LeanCert.Internal.Dyadic.evalUnchecked, cosIntervalDyadic]
    have hrat := IntervalDyadic.mem_toIntervalRat.mp (ih hdom)
    have hcos := IntervalRat.mem_cosComputable hrat cfg.taylorDepth
    exact IntervalDyadic.mem_ofIntervalRat hcos cfg.precision hprec
  | exp _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_exp, LeanCert.Internal.Dyadic.evalUnchecked, expIntervalDyadic]
    have hrat := IntervalDyadic.mem_toIntervalRat.mp (ih hdom)
    have hexp := IntervalRat.mem_expComputable hrat cfg.taylorDepth
    exact IntervalDyadic.mem_ofIntervalRat hexp cfg.precision hprec
  | sqrt _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_sqrt, LeanCert.Internal.Dyadic.evalUnchecked, sqrtIntervalDyadic]
    exact IntervalDyadic.mem_sqrt' (ih hdom) cfg.precision
  | sinh _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_sinh, LeanCert.Internal.Dyadic.evalUnchecked, sinhIntervalDyadic]
    have hrat := IntervalDyadic.mem_toIntervalRat.mp (ih hdom)
    have hsinh := IntervalRat.mem_sinhComputable hrat cfg.taylorDepth
    exact IntervalDyadic.mem_ofIntervalRat hsinh cfg.precision hprec
  | cosh _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_cosh, LeanCert.Internal.Dyadic.evalUnchecked, coshIntervalDyadic]
    have hrat := IntervalDyadic.mem_toIntervalRat.mp (ih hdom)
    have hcosh := IntervalRat.mem_coshComputable hrat cfg.taylorDepth
    exact IntervalDyadic.mem_ofIntervalRat hcosh cfg.precision hprec
  | @tanh e' _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_tanh, LeanCert.Internal.Dyadic.evalUnchecked, tanhIntervalDyadic]
    -- tanh x ∈ [-1, 1] for all x
    rw [IntervalDyadic.mem_def, Dyadic.toRat_ofInt, Dyadic.toRat_ofInt]
    simp only [Int.cast_neg, Int.cast_one, Rat.cast_neg, Rat.cast_one]
    set x := Expr.eval ρ_real e' with hx
    constructor
    -- tanh x ≥ -1: use tanh = sinh/cosh, cosh > 0, and -cosh ≤ sinh
    · rw [Real.tanh_eq_sinh_div_cosh]
      have hcosh : Real.cosh x > 0 := Real.cosh_pos x
      rw [le_div_iff₀ hcosh, neg_one_mul]
      rw [Real.sinh_eq, Real.cosh_eq]
      have h1 : Real.exp x > 0 := Real.exp_pos x
      linarith
    -- tanh x ≤ 1: use sinh ≤ cosh (since exp(-x) > 0)
    · rw [Real.tanh_eq_sinh_div_cosh]
      have hcosh : Real.cosh x > 0 := Real.cosh_pos x
      rw [div_le_one₀ hcosh]
      rw [Real.sinh_eq, Real.cosh_eq]
      have h2 : Real.exp (-x) > 0 := Real.exp_pos (-x)
      linarith
  | @erf e' _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_erf, LeanCert.Internal.Dyadic.evalUnchecked, erfIntervalDyadic]
    -- erf x ∈ [-1, 1] for all x
    rw [IntervalDyadic.mem_def, Dyadic.toRat_ofInt, Dyadic.toRat_ofInt]
    simp only [Int.cast_neg, Int.cast_one, Rat.cast_neg, Rat.cast_one]
    exact Real.erf_mem_Icc _
  | log _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_log, LeanCert.Internal.Dyadic.evalUnchecked, logIntervalDyadic]
    have hrat := IntervalDyadic.mem_toIntervalRat.mp (ih hdom.1)
    -- hdom.2 gives us the positivity condition: IRat.lo > 0
    -- This makes the if-condition true, so we take the positive branch
    have hpos : (LeanCert.Internal.Dyadic.evalUnchecked _ ρ_dyad cfg).toIntervalRat.lo > 0 := hdom.2
    simp only [hpos, ↓reduceIte]
    have hlog := IntervalRat.mem_logComputable hrat hpos cfg.taylorDepth
    exact IntervalDyadic.mem_ofIntervalRat hlog cfg.precision hprec
  | namedConst c =>
    simp only [Expr.eval_namedConst, LeanCert.Internal.Dyadic.evalUnchecked]
    exact IntervalDyadic.mem_ofIntervalRat c.mem_interval cfg.precision hprec

/-- Correctness of Dyadic evaluation for every expression whose recursively
checked domain conditions hold. -/
theorem evalIntervalDyadic_correct_of_domain (e : Expr)
    (ρ_real : Nat → ℝ) (ρ_dyad : IntervalDyadicEnv)
    (hρ : envMemDyadic ρ_real ρ_dyad) (cfg : DyadicConfig := {})
    (hprec : cfg.precision ≤ 0 := by norm_num)
    (hdom : evalDomainValidDyadic e ρ_dyad cfg) :
    Expr.eval ρ_real e ∈ LeanCert.Internal.Dyadic.evalUnchecked e ρ_dyad cfg := by
  induction e with
  | const q =>
    simp only [Expr.eval_const, LeanCert.Internal.Dyadic.evalUnchecked]
    apply IntervalDyadic.mem_ofIntervalRat
    · exact IntervalRat.mem_singleton q
    · exact hprec
  | var idx =>
    simp only [Expr.eval_var, LeanCert.Internal.Dyadic.evalUnchecked]
    exact hρ idx
  | add _ _ ih₁ ih₂ =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_add, LeanCert.Internal.Dyadic.evalUnchecked]
    have h := IntervalDyadic.mem_add (ih₁ hdom.1) (ih₂ hdom.2)
    exact IntervalDyadic.roundOut_contains h cfg.precision
  | mul _ _ ih₁ ih₂ =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_mul, LeanCert.Internal.Dyadic.evalUnchecked]
    have h := IntervalDyadic.mem_mul (ih₁ hdom.1) (ih₂ hdom.2)
    exact IntervalDyadic.roundOut_contains h cfg.precision
  | neg _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_neg, LeanCert.Internal.Dyadic.evalUnchecked]
    exact IntervalDyadic.mem_neg (ih hdom)
  | inv _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_inv, LeanCert.Internal.Dyadic.evalUnchecked, invIntervalDyadic]
    have hinner := ih hdom.1
    have hrat := IntervalDyadic.mem_toIntervalRat.mp hinner
    have hinv := mem_invInterval_nonzero hrat hdom.2
    exact IntervalDyadic.mem_ofIntervalRat hinv cfg.precision hprec
  | exp _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_exp, LeanCert.Internal.Dyadic.evalUnchecked, expIntervalDyadic]
    have hrat := IntervalDyadic.mem_toIntervalRat.mp (ih hdom)
    have hexp := IntervalRat.mem_expComputable hrat cfg.taylorDepth
    exact IntervalDyadic.mem_ofIntervalRat hexp cfg.precision hprec
  | sin _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_sin, LeanCert.Internal.Dyadic.evalUnchecked, sinIntervalDyadic]
    have hrat := IntervalDyadic.mem_toIntervalRat.mp (ih hdom)
    have hsin := IntervalRat.mem_sinComputable hrat cfg.taylorDepth
    exact IntervalDyadic.mem_ofIntervalRat hsin cfg.precision hprec
  | cos _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_cos, LeanCert.Internal.Dyadic.evalUnchecked, cosIntervalDyadic]
    have hrat := IntervalDyadic.mem_toIntervalRat.mp (ih hdom)
    have hcos := IntervalRat.mem_cosComputable hrat cfg.taylorDepth
    exact IntervalDyadic.mem_ofIntervalRat hcos cfg.precision hprec
  | log _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_log, LeanCert.Internal.Dyadic.evalUnchecked, logIntervalDyadic]
    have hrat := IntervalDyadic.mem_toIntervalRat.mp (ih hdom.1)
    have hpos : (LeanCert.Internal.Dyadic.evalUnchecked _ ρ_dyad cfg).toIntervalRat.lo > 0 := hdom.2
    simp only [hpos, ↓reduceIte]
    have hlog := IntervalRat.mem_logComputable hrat hpos cfg.taylorDepth
    exact IntervalDyadic.mem_ofIntervalRat hlog cfg.precision hprec
  | sinh _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_sinh, LeanCert.Internal.Dyadic.evalUnchecked, sinhIntervalDyadic]
    have hrat := IntervalDyadic.mem_toIntervalRat.mp (ih hdom)
    have hsinh := IntervalRat.mem_sinhComputable hrat cfg.taylorDepth
    exact IntervalDyadic.mem_ofIntervalRat hsinh cfg.precision hprec
  | cosh _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_cosh, LeanCert.Internal.Dyadic.evalUnchecked, coshIntervalDyadic]
    have hrat := IntervalDyadic.mem_toIntervalRat.mp (ih hdom)
    have hcosh := IntervalRat.mem_coshComputable hrat cfg.taylorDepth
    exact IntervalDyadic.mem_ofIntervalRat hcosh cfg.precision hprec
  | tanh e' ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_tanh, LeanCert.Internal.Dyadic.evalUnchecked, tanhIntervalDyadic]
    rw [IntervalDyadic.mem_def, Dyadic.toRat_ofInt, Dyadic.toRat_ofInt]
    simp only [Int.cast_neg, Int.cast_one, Rat.cast_neg, Rat.cast_one]
    set x := Expr.eval ρ_real e' with hx
    constructor
    · rw [Real.tanh_eq_sinh_div_cosh]
      have hcosh : Real.cosh x > 0 := Real.cosh_pos x
      rw [le_div_iff₀ hcosh, neg_one_mul]
      rw [Real.sinh_eq, Real.cosh_eq]
      have h1 : Real.exp x > 0 := Real.exp_pos x
      linarith
    · rw [Real.tanh_eq_sinh_div_cosh]
      have hcosh : Real.cosh x > 0 := Real.cosh_pos x
      rw [div_le_one₀ hcosh]
      rw [Real.sinh_eq, Real.cosh_eq]
      have h2 : Real.exp (-x) > 0 := Real.exp_pos (-x)
      linarith
  | atan e' ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_atan, LeanCert.Internal.Dyadic.evalUnchecked, atanIntervalDyadic]
    rw [IntervalDyadic.mem_def, Dyadic.toRat_ofInt, Dyadic.toRat_ofInt]
    simp only [Int.cast_neg, Int.cast_ofNat, Rat.cast_neg, Rat.cast_ofNat]
    set x := Expr.eval ρ_real e' with hx
    constructor
    · linarith [Real.neg_pi_div_two_lt_arctan x, Real.pi_lt_four]
    · linarith [Real.arctan_lt_pi_div_two x, Real.pi_lt_four]
  | sinc _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_sinc, LeanCert.Internal.Dyadic.evalUnchecked, sincIntervalDyadic]
    rw [IntervalDyadic.mem_def, Dyadic.toRat_ofInt, Dyadic.toRat_ofInt]
    simp only [Int.cast_neg, Int.cast_one, Rat.cast_neg, Rat.cast_one]
    exact Real.sinc_mem_Icc _
  | arsinh _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_arsinh, LeanCert.Internal.Dyadic.evalUnchecked, arsinhIntervalDyadic]
    have hrat := IntervalDyadic.mem_toIntervalRat.mp (ih hdom)
    have harsinh := mem_arsinhInterval hrat
    exact IntervalDyadic.mem_ofIntervalRat harsinh cfg.precision hprec
  | atanh _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    obtain ⟨hdom_sub, hlo_gt, hhi_lt⟩ := hdom
    simp only [Expr.eval_atanh, LeanCert.Internal.Dyadic.evalUnchecked, atanhIntervalDyadic]
    have hrat := IntervalDyadic.mem_toIntervalRat.mp (ih hdom_sub)
    have hatanh := IntervalRat.mem_atanhComputable hrat hlo_gt hhi_lt cfg.taylorDepth
    exact IntervalDyadic.mem_ofIntervalRat hatanh cfg.precision hprec
  | erf _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_erf, LeanCert.Internal.Dyadic.evalUnchecked, erfIntervalDyadic]
    rw [IntervalDyadic.mem_def, Dyadic.toRat_ofInt, Dyadic.toRat_ofInt]
    simp only [Int.cast_neg, Int.cast_one, Rat.cast_neg, Rat.cast_one]
    exact Real.erf_mem_Icc _
  | sqrt _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_sqrt, LeanCert.Internal.Dyadic.evalUnchecked, sqrtIntervalDyadic]
    exact IntervalDyadic.mem_sqrt' (ih hdom) cfg.precision
  | namedConst c =>
    simp only [Expr.eval_namedConst, LeanCert.Internal.Dyadic.evalUnchecked]
    exact IntervalDyadic.mem_ofIntervalRat c.mem_interval cfg.precision hprec

/-- Successful checked Dyadic evaluation encloses the true value for every
expression, provided outward-rounding precision is nonpositive. -/
theorem evalIntervalDyadicChecked_correct (e : Expr)
    (ρ_real : Nat → ℝ) (ρ_dyad : IntervalDyadicEnv)
    (hρ : envMemDyadic ρ_real ρ_dyad) (cfg : DyadicConfig := {})
    (hprec : cfg.precision ≤ 0 := by norm_num)
    (result : IntervalDyadic)
    (hsuccess : evalIntervalDyadicChecked e ρ_dyad cfg = .ok result) :
    Expr.eval ρ_real e ∈ result := by
  unfold evalIntervalDyadicChecked at hsuccess
  let cached := LeanCert.Internal.Dyadic.evalCached e ρ_dyad cfg
  cases hvalid : cached.2 with
  | false =>
    have : Except.error (diagnoseEvalIntervalDyadicFailure e ρ_dyad cfg) =
        Except.ok result := by
      simp [cached, hvalid] at hsuccess
    contradiction
  | true =>
    have hsuccess' : (Except.ok cached.1 : EvalResult IntervalDyadic) = Except.ok result := by
      simpa [cached, hvalid] using hsuccess
    injection hsuccess' with hresult
    subst result
    have hcheck : checkDomainValidDyadic e ρ_dyad cfg = true := by
      calc
        checkDomainValidDyadic e ρ_dyad cfg =
            (LeanCert.Internal.Dyadic.evalCached e ρ_dyad cfg).2 :=
          (evalIntervalDyadicCached_snd e ρ_dyad cfg).symm
        _ = cached.2 := rfl
        _ = true := hvalid
    have hsound := evalIntervalDyadic_correct_of_domain e
      ρ_real ρ_dyad hρ cfg hprec (checkDomainValidDyadic_correct e ρ_dyad cfg hcheck)
    change Expr.eval ρ_real e ∈ (LeanCert.Internal.Dyadic.evalCached e ρ_dyad cfg).1
    rw [evalIntervalDyadicCached_fst e ρ_dyad cfg]
    exact hsound

/-! ### Verification Checkers -/

/-- Check if expression is bounded above by q -/
def checkUpperBoundDyadic (e : Expr) (ρ : IntervalDyadicEnv) (q : ℚ)
    (cfg : DyadicConfig := {}) : Bool :=
  (LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg).upperBoundedBy q

/-- Check if expression is bounded below by q -/
def checkLowerBoundDyadic (e : Expr) (ρ : IntervalDyadicEnv) (q : ℚ)
    (cfg : DyadicConfig := {}) : Bool :=
  (LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg).lowerBoundedBy q

/-- Check if expression is bounded in interval [lo, hi] -/
def checkBoundsDyadic (e : Expr) (ρ : IntervalDyadicEnv) (lo hi : ℚ)
    (cfg : DyadicConfig := {}) : Bool :=
  let result := LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg
  result.lowerBoundedBy lo && result.upperBoundedBy hi

end LeanCert.Engine

end

end

section

/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
/-!
# Domain-aware automatic differentiation with Dyadic intervals

This module is the bounded-denominator counterpart of `AD.DomainChecked`.
Polynomial dual arithmetic is performed with Dyadic endpoints and outward
rounding after every addition and multiplication.  Transcendental values use
the same verified rational Taylor kernels as the Dyadic value evaluator and
are rounded back to Dyadic endpoints.

The public entry points are checked: unsupported syntax, invalid reciprocal or
logarithm domains, and positive rounding precisions return `EvalError` rather
than a finite interval.
-/

public section

namespace LeanCert.Engine

open LeanCert.Core

/-- A value interval and one directional derivative interval, both Dyadic. -/
structure DualIntervalDyadic where
  /-- The interval enclosing the function value. -/
  val : IntervalDyadic
  /-- The interval enclosing the derivative. -/
  der : IntervalDyadic
  deriving Repr

instance : Inhabited DualIntervalDyadic where
  default := ⟨default, default⟩

/-- An environment of Dyadic dual intervals. -/
abbrev DualDyadicEnv := Nat → DualIntervalDyadic

namespace DualIntervalDyadic

/-- The singleton dyadic interval at zero. -/
def zero : IntervalDyadic := IntervalDyadic.singleton Core.Dyadic.zero
/-- The singleton dyadic interval at one. -/
def one : IntervalDyadic := IntervalDyadic.singleton (Core.Dyadic.ofInt 1)

/-- Enclose a rational constant in a dyadic interval with zero derivative. -/
def const (q : ℚ) (cfg : DyadicConfig := {}) : DualIntervalDyadic :=
  ⟨IntervalDyadic.ofIntervalRat (IntervalRat.singleton q) cfg.precision, zero⟩

/-- An input interval whose derivative is the singleton one. -/
def varActive (I : IntervalDyadic) : DualIntervalDyadic := ⟨I, one⟩
/-- An input interval held constant, with singleton zero derivative. -/
def varPassive (I : IntervalDyadic) : DualIntervalDyadic := ⟨I, zero⟩

/-- Addition with dyadic interval propagation of values and derivatives. -/
def add (a b : DualIntervalDyadic) (cfg : DyadicConfig := {}) : DualIntervalDyadic :=
  ⟨IntervalDyadic.addRounded a.val b.val cfg.precision,
   IntervalDyadic.addRounded a.der b.der cfg.precision⟩

/-- Multiplication with dyadic interval propagation of values and derivatives. -/
def mul (a b : DualIntervalDyadic) (cfg : DyadicConfig := {}) : DualIntervalDyadic :=
  ⟨IntervalDyadic.mulRounded a.val b.val cfg.precision,
   IntervalDyadic.addRounded
     (IntervalDyadic.mulRounded a.der b.val cfg.precision)
     (IntervalDyadic.mulRounded a.val b.der cfg.precision)
     cfg.precision⟩

/-- Negation with dyadic interval propagation of values and derivatives. -/
def neg (a : DualIntervalDyadic) : DualIntervalDyadic :=
  ⟨IntervalDyadic.neg a.val, IntervalDyadic.neg a.der⟩

/-- Reciprocal with dyadic interval propagation of values and derivatives. -/
def inv (a : DualIntervalDyadic) (cfg : DyadicConfig := {}) : DualIntervalDyadic :=
  let invVal := invIntervalDyadic a.val cfg
  let invSq := IntervalDyadic.mulRounded invVal invVal cfg.precision
  ⟨invVal, IntervalDyadic.neg (IntervalDyadic.mulRounded a.der invSq cfg.precision)⟩

/-- Exponential with dyadic interval propagation of values and derivatives. -/
def exp (a : DualIntervalDyadic) (cfg : DyadicConfig := {}) : DualIntervalDyadic :=
  let value := expIntervalDyadic a.val cfg
  ⟨value, IntervalDyadic.mulRounded value a.der cfg.precision⟩

/-- Sine with dyadic interval propagation of values and derivatives. -/
def sin (a : DualIntervalDyadic) (cfg : DyadicConfig := {}) : DualIntervalDyadic :=
  ⟨sinIntervalDyadic a.val cfg,
   IntervalDyadic.mulRounded (cosIntervalDyadic a.val cfg) a.der cfg.precision⟩

/-- Cosine with dyadic interval propagation of values and derivatives. -/
def cos (a : DualIntervalDyadic) (cfg : DyadicConfig := {}) : DualIntervalDyadic :=
  ⟨cosIntervalDyadic a.val cfg,
   IntervalDyadic.mulRounded (IntervalDyadic.neg (sinIntervalDyadic a.val cfg))
     a.der cfg.precision⟩

/-- Natural logarithm with dyadic interval propagation of values and derivatives. -/
def log (a : DualIntervalDyadic) (cfg : DyadicConfig := {}) : DualIntervalDyadic :=
  ⟨logIntervalDyadic a.val cfg,
   IntervalDyadic.mulRounded (invIntervalDyadic a.val cfg) a.der cfg.precision⟩

end DualIntervalDyadic
end LeanCert.Engine

namespace LeanCert.Internal.AD.Dyadic

open LeanCert.Core LeanCert.Engine

/-- Total computational kernel.  Sound public use goes through the checked
entry points below. -/
def evalTotal (e : Expr) (rho : DualDyadicEnv) (cfg : DyadicConfig := {}) :
    DualIntervalDyadic :=
  match e with
  | .const q => DualIntervalDyadic.const q cfg
  | .var i => rho i
  | .add a b => DualIntervalDyadic.add (evalTotal a rho cfg) (evalTotal b rho cfg) cfg
  | .mul a b => DualIntervalDyadic.mul (evalTotal a rho cfg) (evalTotal b rho cfg) cfg
  | .neg a => DualIntervalDyadic.neg (evalTotal a rho cfg)
  | .inv a => DualIntervalDyadic.inv (evalTotal a rho cfg) cfg
  | .exp a => DualIntervalDyadic.exp (evalTotal a rho cfg) cfg
  | .sin a => DualIntervalDyadic.sin (evalTotal a rho cfg) cfg
  | .cos a => DualIntervalDyadic.cos (evalTotal a rho cfg) cfg
  | .log a => DualIntervalDyadic.log (evalTotal a rho cfg) cfg
  | _ => default

end LeanCert.Internal.AD.Dyadic

namespace LeanCert.Engine

open LeanCert.Core

/-- Value projection of a Dyadic dual environment. -/
def DualDyadicEnv.values (rho : DualDyadicEnv) : IntervalDyadicEnv := fun i => (rho i).val

/-- Dual environment selecting coordinate `idx`. -/
def mkDualDyadicEnv (rho : IntervalDyadicEnv) (idx : Nat) : DualDyadicEnv :=
  fun i => if i = idx then DualIntervalDyadic.varActive (rho i)
    else DualIntervalDyadic.varPassive (rho i)

@[simp] theorem mkDualDyadicEnv_values (rho : IntervalDyadicEnv) (idx : Nat) :
    (mkDualDyadicEnv rho idx).values = rho := by
  funext i
  by_cases hi : i = idx <;>
    simp [mkDualDyadicEnv, DualDyadicEnv.values, hi,
      DualIntervalDyadic.varActive, DualIntervalDyadic.varPassive]

/-- The deliberately small v1 Dyadic AD fragment. -/
def checkDyadicADFragment : Expr → Bool
  | .const _ | .var _ => true
  | .add a b | .mul a b => checkDyadicADFragment a && checkDyadicADFragment b
  | .neg a | .inv a | .exp a | .sin a | .cos a | .log a => checkDyadicADFragment a
  | _ => false

/-- Box-dependent domain check for the Dyadic AD kernel. -/
def checkDyadicADDomain (e : Expr) (rho : DualDyadicEnv) (cfg : DyadicConfig := {}) : Bool :=
  checkDyadicADFragment e && (LeanCert.Internal.Dyadic.evalCached e rho.values cfg).2

/-- Explain the first failed support or domain check. -/
def diagnoseDyadicADFailure (e : Expr) (rho : DualDyadicEnv)
    (cfg : DyadicConfig := {}) : EvalError :=
  if !checkDyadicADFragment e then
    .unsupportedFeature "Dyadic automatic differentiation"
  else
    diagnoseEvalIntervalDyadicFailure e rho.values cfg

/-- Checked Dyadic dual evaluation. -/
def evalDualDyadicChecked (e : Expr) (rho : DualDyadicEnv) (cfg : DyadicConfig := {}) :
    EvalResult DualIntervalDyadic :=
  if cfg.precision ≤ 0 then
    if checkDyadicADDomain e rho cfg then
      .ok (LeanCert.Internal.AD.Dyadic.evalTotal e rho cfg)
    else
      .error (diagnoseDyadicADFailure e rho cfg)
  else
    .error (.invalidConfiguration "Dyadic AD precision must be nonpositive")

/-- Checked value-and-derivative evaluation along coordinate `idx`. -/
def evalWithDerivDyadicChecked (e : Expr) (rho : IntervalDyadicEnv) (idx : Nat)
    (cfg : DyadicConfig := {}) : EvalResult DualIntervalDyadic :=
  evalDualDyadicChecked e (mkDualDyadicEnv rho idx) cfg

/-- Checked Dyadic derivative enclosure along coordinate `idx`. -/
def derivIntervalDyadicChecked (e : Expr) (rho : IntervalDyadicEnv) (idx : Nat)
    (cfg : DyadicConfig := {}) : EvalResult IntervalDyadic :=
  return (← evalWithDerivDyadicChecked e rho idx cfg).der

/-- Checked Dyadic derivative enclosure for a single-variable expression. -/
def derivIntervalDyadicChecked1 (e : Expr) (I : IntervalDyadic)
    (cfg : DyadicConfig := {}) : EvalResult IntervalDyadic :=
  derivIntervalDyadicChecked e (fun _ => I) 0 cfg

/-- Convenience boundary for callers whose boxes use rational endpoints. -/
def derivIntervalDyadicCheckedOfRat (e : Expr) (rho : IntervalEnv) (idx : Nat)
    (cfg : DyadicConfig := {}) : EvalResult IntervalDyadic :=
  if cfg.precision ≤ 0 then
    derivIntervalDyadicChecked e (toDyadicEnv rho cfg.precision) idx cfg
  else
    .error (.invalidConfiguration "Dyadic AD precision must be nonpositive")

/-- Single-variable rational-input convenience boundary. -/
def derivIntervalDyadicChecked1OfRat (e : Expr) (I : IntervalRat)
    (cfg : DyadicConfig := {}) : EvalResult IntervalDyadic :=
  derivIntervalDyadicCheckedOfRat e (fun _ => I) 0 cfg

/-- The value projection of the dual kernel is exactly the ordinary Dyadic
value kernel. -/
theorem evalTotalDyadic_val_of_fragment (e : Expr) (rho : DualDyadicEnv)
    (cfg : DyadicConfig) (hsupp : checkDyadicADFragment e = true) :
    (LeanCert.Internal.AD.Dyadic.evalTotal e rho cfg).val =
      LeanCert.Internal.Dyadic.evalUnchecked e rho.values cfg := by
  induction e with
  | const | var =>
      simp [LeanCert.Internal.AD.Dyadic.evalTotal, LeanCert.Internal.Dyadic.evalUnchecked,
        DualIntervalDyadic.const, DualDyadicEnv.values]
  | add a b iha ihb | mul a b iha ihb =>
      simp only [checkDyadicADFragment, Bool.and_eq_true] at hsupp
      simp [LeanCert.Internal.AD.Dyadic.evalTotal, LeanCert.Internal.Dyadic.evalUnchecked,
        DualIntervalDyadic.add, DualIntervalDyadic.mul, IntervalDyadic.addRounded,
        IntervalDyadic.mulRounded, iha hsupp.1, ihb hsupp.2]
  | neg a ih | inv a ih | exp a ih | sin a ih | cos a ih | log a ih =>
      simp only [checkDyadicADFragment] at hsupp
      simp [LeanCert.Internal.AD.Dyadic.evalTotal, LeanCert.Internal.Dyadic.evalUnchecked,
        DualIntervalDyadic.neg, DualIntervalDyadic.inv, DualIntervalDyadic.exp,
        DualIntervalDyadic.sin, DualIntervalDyadic.cos, DualIntervalDyadic.log, ih hsupp]
  | atan | arsinh | atanh | sinc | erf | sinh | cosh | tanh | sqrt | namedConst =>
      simp [checkDyadicADFragment] at hsupp

private theorem evalDualDyadicChecked_facts {e : Expr} {rho : DualDyadicEnv}
    {cfg : DyadicConfig} {D : DualIntervalDyadic}
    (hok : evalDualDyadicChecked e rho cfg = .ok D) :
    cfg.precision ≤ 0 ∧ checkDyadicADFragment e = true ∧
      evalDomainValidDyadic e rho.values cfg ∧
      D = LeanCert.Internal.AD.Dyadic.evalTotal e rho cfg := by
  simp only [evalDualDyadicChecked] at hok
  split at hok
  · rename_i hprec
    split at hok
    · rename_i hcheck
      have hparts : checkDyadicADFragment e = true ∧
          (LeanCert.Internal.Dyadic.evalCached e rho.values cfg).2 = true := by
        simpa only [checkDyadicADDomain, Bool.and_eq_true] using hcheck
      have hdomainCheck : checkDomainValidDyadic e rho.values cfg = true := by
        rw [← evalIntervalDyadicCached_snd e rho.values cfg]
        exact hparts.2
      exact ⟨hprec, hparts.1,
        checkDomainValidDyadic_correct e rho.values cfg hdomainCheck,
        (Except.ok.inj hok).symm⟩
    · contradiction
  · contradiction

private theorem evalTotalDyadic_val_correct_of_facts (e : Expr)
    (rhoReal : Nat → ℝ) (rho : DualDyadicEnv) (cfg : DyadicConfig)
    (hprec : cfg.precision ≤ 0) (hsupp : checkDyadicADFragment e = true)
    (hdom : evalDomainValidDyadic e rho.values cfg)
    (hrho : ∀ i, rhoReal i ∈ (rho i).val) :
    Expr.eval rhoReal e ∈ (LeanCert.Internal.AD.Dyadic.evalTotal e rho cfg).val := by
  rw [evalTotalDyadic_val_of_fragment e rho cfg hsupp]
  exact evalIntervalDyadic_correct_of_domain e rhoReal rho.values hrho cfg hprec hdom

/-- Golden theorem for successful checked Dyadic dual evaluation. -/
theorem evalDualDyadicChecked_val_correct (e : Expr)
    (rhoReal : Nat → ℝ) (rho : DualDyadicEnv) (cfg : DyadicConfig)
    (D : DualIntervalDyadic) (hrho : ∀ i, rhoReal i ∈ (rho i).val)
    (hok : evalDualDyadicChecked e rho cfg = .ok D) :
    Expr.eval rhoReal e ∈ D.val := by
  obtain ⟨hprec, hsupp, hdom, rfl⟩ := evalDualDyadicChecked_facts hok
  exact evalTotalDyadic_val_correct_of_facts e rhoReal rho cfg hprec hsupp hdom hrho

private theorem updateVar_mem_mkDualDyadicEnv_val
    (rhoReal : Nat → ℝ) (rho : IntervalDyadicEnv) (idx : Nat)
    (x : ℝ) (hx : x ∈ rho idx) (hrho : ∀ i, rhoReal i ∈ rho i) :
    ∀ i, Expr.updateVar rhoReal idx x i ∈ (mkDualDyadicEnv rho idx i).val := by
  intro i
  by_cases hi : i = idx
  · subst i
    simpa [Expr.updateVar, mkDualDyadicEnv, DualIntervalDyadic.varActive] using hx
  · simpa [Expr.updateVar, mkDualDyadicEnv, hi, DualIntervalDyadic.varPassive] using hrho i

private theorem evalAlong_differentiableAt_of_dyadic_facts (e : Expr)
    (rhoReal : Nat → ℝ) (rho : IntervalDyadicEnv) (idx : Nat) (cfg : DyadicConfig)
    (x : ℝ) (hx : x ∈ rho idx) (hrho : ∀ i, rhoReal i ∈ rho i)
    (hprec : cfg.precision ≤ 0) (hsupp : checkDyadicADFragment e = true)
    (hdom : evalDomainValidDyadic e rho cfg) :
    DifferentiableAt ℝ (Expr.evalAlong e rhoReal idx) x := by
  have hmem := updateVar_mem_mkDualDyadicEnv_val rhoReal rho idx x hx hrho
  have hmemValue : envMemDyadic (Expr.updateVar rhoReal idx x) rho := by
    intro i
    by_cases hi : i = idx
    · subst i
      simpa [Expr.updateVar] using hx
    · simpa [Expr.updateVar, hi] using hrho i
  induction e with
  | const => exact differentiableAt_const _
  | var i =>
      by_cases hi : i = idx
      · subst i
        simpa only [Expr.evalAlong_var_active] using differentiableAt_id
      · simpa only [Expr.evalAlong_var_passive _ _ _ hi] using
          differentiableAt_const (c := rhoReal i)
  | add a b iha ihb =>
      simp only [checkDyadicADFragment, Bool.and_eq_true] at hsupp
      simp only [evalDomainValidDyadic] at hdom
      simpa only [Expr.evalAlong_add_pi] using
        (iha hsupp.1 hdom.1).add (ihb hsupp.2 hdom.2)
  | mul a b iha ihb =>
      simp only [checkDyadicADFragment, Bool.and_eq_true] at hsupp
      simp only [evalDomainValidDyadic] at hdom
      simpa only [Expr.evalAlong_mul_pi] using
        (iha hsupp.1 hdom.1).mul (ihb hsupp.2 hdom.2)
  | neg a ih =>
      simp only [checkDyadicADFragment] at hsupp
      simp only [evalDomainValidDyadic] at hdom
      simpa only [Expr.evalAlong_neg_pi] using (ih hsupp hdom).neg
  | inv a ih =>
      simp only [checkDyadicADFragment] at hsupp
      simp only [evalDomainValidDyadic] at hdom
      have hval := evalIntervalDyadic_correct_of_domain a
        (Expr.updateVar rhoReal idx x) rho hmemValue cfg hprec hdom.1
      have hne : Expr.evalAlong a rhoReal idx x ≠ 0 := by
        rw [Expr.evalAlong_eq]
        intro hz
        rw [hz] at hval
        rcases hdom.2 with hpos | hneg
        · exact (not_lt_of_ge (IntervalDyadic.mem_toIntervalRat.mp hval).1)
            (by exact_mod_cast hpos)
        · exact (not_lt_of_ge (IntervalDyadic.mem_toIntervalRat.mp hval).2)
            (by exact_mod_cast hneg)
      exact DifferentiableAt.inv (ih hsupp hdom.1) hne
  | exp a ih =>
      simp only [checkDyadicADFragment] at hsupp
      simp only [evalDomainValidDyadic] at hdom
      exact Real.differentiableAt_exp.comp x (ih hsupp hdom)
  | sin a ih =>
      simp only [checkDyadicADFragment] at hsupp
      simp only [evalDomainValidDyadic] at hdom
      exact Real.differentiableAt_sin.comp x (ih hsupp hdom)
  | cos a ih =>
      simp only [checkDyadicADFragment] at hsupp
      simp only [evalDomainValidDyadic] at hdom
      exact Real.differentiableAt_cos.comp x (ih hsupp hdom)
  | log a ih =>
      simp only [checkDyadicADFragment] at hsupp
      simp only [evalDomainValidDyadic] at hdom
      have hval := evalIntervalDyadic_correct_of_domain a
        (Expr.updateVar rhoReal idx x) rho hmemValue cfg hprec hdom.1
      have hpos : 0 < Expr.evalAlong a rhoReal idx x := by
        rw [Expr.evalAlong_eq]
        exact lt_of_lt_of_le (by exact_mod_cast hdom.2)
          (IntervalDyadic.mem_toIntervalRat.mp hval).1
      exact (Real.differentiableAt_log (ne_of_gt hpos)).comp x (ih hsupp hdom.1)
  | atan | arsinh | atanh | sinc | erf | sinh | cosh | tanh | sqrt | namedConst =>
      simp [checkDyadicADFragment] at hsupp

/-- Successful checked Dyadic indexed AD proves differentiability throughout
the selected input interval. -/
theorem evalWithDerivDyadicChecked_differentiableAt (e : Expr)
    (rhoReal : Nat → ℝ) (rho : IntervalDyadicEnv) (idx : Nat) (cfg : DyadicConfig)
    (D : DualIntervalDyadic) (x : ℝ) (hx : x ∈ rho idx)
    (hrho : ∀ i, rhoReal i ∈ rho i)
    (hok : evalWithDerivDyadicChecked e rho idx cfg = .ok D) :
    DifferentiableAt ℝ (Expr.evalAlong e rhoReal idx) x := by
  obtain ⟨hprec, hsupp, hdom, _⟩ := evalDualDyadicChecked_facts hok
  exact evalAlong_differentiableAt_of_dyadic_facts e rhoReal rho idx cfg x hx hrho
    hprec hsupp (by simpa using hdom)
private theorem evalTotalDyadic_der_correct_of_facts (e : Expr)
    (rhoReal : Nat → ℝ) (rho : IntervalDyadicEnv) (idx : Nat) (cfg : DyadicConfig)
    (x : ℝ) (hx : x ∈ rho idx) (hrho : ∀ i, rhoReal i ∈ rho i)
    (hprec : cfg.precision ≤ 0) (hsupp : checkDyadicADFragment e = true)
    (hdom : evalDomainValidDyadic e rho cfg) :
    deriv (Expr.evalAlong e rhoReal idx) x ∈
      (LeanCert.Internal.AD.Dyadic.evalTotal e (mkDualDyadicEnv rho idx) cfg).der := by
  have hmemValue : envMemDyadic (Expr.updateVar rhoReal idx x) rho := by
    intro i
    by_cases hi : i = idx
    · subst i
      simpa [Expr.updateVar] using hx
    · simpa [Expr.updateVar, hi] using hrho i
  induction e with
  | const q =>
      simp only [Expr.evalAlong_const', deriv_const, LeanCert.Internal.AD.Dyadic.evalTotal,
        DualIntervalDyadic.const]
      norm_num [DualIntervalDyadic.zero, IntervalDyadic.mem_def, IntervalDyadic.singleton,
        Core.Dyadic.zero, Core.Dyadic.toRat]
  | var i =>
      by_cases hi : i = idx
      · subst i
        simp only [Expr.evalAlong_var_active, deriv_id, LeanCert.Internal.AD.Dyadic.evalTotal,
          mkDualDyadicEnv, ↓reduceIte, DualIntervalDyadic.varActive]
        simpa [DualIntervalDyadic.one, Core.Dyadic.toRat_ofInt] using
          IntervalDyadic.mem_singleton (Core.Dyadic.ofInt 1)
      · simp only [Expr.evalAlong_var_passive _ _ _ hi, deriv_const,
          LeanCert.Internal.AD.Dyadic.evalTotal, mkDualDyadicEnv, ite_eq_right hi,
          DualIntervalDyadic.varPassive]
        norm_num [DualIntervalDyadic.zero, IntervalDyadic.mem_def, IntervalDyadic.singleton,
          Core.Dyadic.zero, Core.Dyadic.toRat]
  | add a b iha ihb =>
      simp only [checkDyadicADFragment, Bool.and_eq_true] at hsupp
      simp only [evalDomainValidDyadic] at hdom
      have hda := evalAlong_differentiableAt_of_dyadic_facts a rhoReal rho idx cfg x hx hrho
        hprec hsupp.1 hdom.1
      have hdb := evalAlong_differentiableAt_of_dyadic_facts b rhoReal rho idx cfg x hx hrho
        hprec hsupp.2 hdom.2
      simp only [Expr.evalAlong_add_pi, deriv_add hda hdb,
        LeanCert.Internal.AD.Dyadic.evalTotal, DualIntervalDyadic.add,
        IntervalDyadic.addRounded]
      exact IntervalDyadic.roundOut_contains
        (IntervalDyadic.mem_add (iha hsupp.1 hdom.1) (ihb hsupp.2 hdom.2)) cfg.precision
  | mul a b iha ihb =>
      simp only [checkDyadicADFragment, Bool.and_eq_true] at hsupp
      simp only [evalDomainValidDyadic] at hdom
      have hda := evalAlong_differentiableAt_of_dyadic_facts a rhoReal rho idx cfg x hx hrho
        hprec hsupp.1 hdom.1
      have hdb := evalAlong_differentiableAt_of_dyadic_facts b rhoReal rho idx cfg x hx hrho
        hprec hsupp.2 hdom.2
      have hmemDual := updateVar_mem_mkDualDyadicEnv_val rhoReal rho idx x hx hrho
      have hva := evalTotalDyadic_val_correct_of_facts a
        (Expr.updateVar rhoReal idx x) (mkDualDyadicEnv rho idx) cfg hprec hsupp.1
        (by simpa using hdom.1) hmemDual
      have hvb := evalTotalDyadic_val_correct_of_facts b
        (Expr.updateVar rhoReal idx x) (mkDualDyadicEnv rho idx) cfg hprec hsupp.2
        (by simpa using hdom.2) hmemDual
      have hleft := IntervalDyadic.roundOut_contains
        (IntervalDyadic.mem_mul (iha hsupp.1 hdom.1) hvb) cfg.precision
      have hright := IntervalDyadic.roundOut_contains
        (IntervalDyadic.mem_mul hva (ihb hsupp.2 hdom.2)) cfg.precision
      simp only [Expr.evalAlong_mul_pi, deriv_mul hda hdb,
        LeanCert.Internal.AD.Dyadic.evalTotal, DualIntervalDyadic.mul,
        IntervalDyadic.mulRounded, IntervalDyadic.addRounded]
      exact IntervalDyadic.roundOut_contains (IntervalDyadic.mem_add hleft hright) cfg.precision
  | neg a ih =>
      simp only [checkDyadicADFragment] at hsupp
      simp only [evalDomainValidDyadic] at hdom
      have hd := evalAlong_differentiableAt_of_dyadic_facts a rhoReal rho idx cfg x hx hrho
        hprec hsupp hdom
      simp only [Expr.evalAlong_neg_pi, deriv.neg, LeanCert.Internal.AD.Dyadic.evalTotal,
        DualIntervalDyadic.neg]
      exact IntervalDyadic.mem_neg (ih hsupp hdom)
  | inv a ih =>
      simp only [checkDyadicADFragment] at hsupp
      simp only [evalDomainValidDyadic] at hdom
      have hval := evalIntervalDyadic_correct_of_domain a
        (Expr.updateVar rhoReal idx x) rho hmemValue cfg hprec hdom.1
      have hval' : Expr.evalAlong a rhoReal idx x ∈
          LeanCert.Internal.Dyadic.evalUnchecked a rho cfg := by
        simpa only [Expr.evalAlong_eq] using hval
      have hne : Expr.evalAlong a rhoReal idx x ≠ 0 := by
        intro hz
        rw [hz] at hval'
        rcases hdom.2 with hpos | hneg
        · exact (not_lt_of_ge (IntervalDyadic.mem_toIntervalRat.mp hval').1)
            (by exact_mod_cast hpos)
        · exact (not_lt_of_ge (IntervalDyadic.mem_toIntervalRat.mp hval').2)
            (by exact_mod_cast hneg)
      have hd := evalAlong_differentiableAt_of_dyadic_facts a rhoReal rho idx cfg x hx hrho
        hprec hsupp hdom.1
      rw [Expr.evalAlong_inv]
      have hcomp : (fun t => (Expr.evalAlong a rhoReal idx t)⁻¹) =
          (fun y : ℝ => y⁻¹) ∘ Expr.evalAlong a rhoReal idx := rfl
      rw [hcomp, deriv_comp x (hasDerivAt_inv hne).differentiableAt hd]
      simp only [(hasDerivAt_inv hne).deriv, LeanCert.Internal.AD.Dyadic.evalTotal,
        DualIntervalDyadic.inv]
      rw [evalTotalDyadic_val_of_fragment a (mkDualDyadicEnv rho idx) cfg hsupp]
      simp only [mkDualDyadicEnv_values]
      have hrat := IntervalDyadic.mem_toIntervalRat.mp hval'
      have hinvRat := mem_invInterval_nonzero hrat hdom.2
      have hinv : (Expr.evalAlong a rhoReal idx x)⁻¹ ∈
          invIntervalDyadic (LeanCert.Internal.Dyadic.evalUnchecked a rho cfg) cfg := by
        exact IntervalDyadic.mem_ofIntervalRat hinvRat cfg.precision hprec
      have hinvSq := IntervalDyadic.roundOut_contains
        (IntervalDyadic.mem_mul hinv hinv) cfg.precision
      have hprod := IntervalDyadic.roundOut_contains
        (IntervalDyadic.mem_mul (ih hsupp hdom.1) hinvSq) cfg.precision
      have hneg := IntervalDyadic.mem_neg hprod
      simpa [IntervalDyadic.mulRounded, pow_two, mul_assoc, mul_comm, mul_left_comm] using hneg
  | exp a ih =>
      simp only [checkDyadicADFragment] at hsupp
      simp only [evalDomainValidDyadic] at hdom
      have hd := evalAlong_differentiableAt_of_dyadic_facts a rhoReal rho idx cfg x hx hrho
        hprec hsupp hdom
      have hval := evalIntervalDyadic_correct_of_domain a
        (Expr.updateVar rhoReal idx x) rho hmemValue cfg hprec hdom
      have hexpRat := IntervalRat.mem_expComputable
        (IntervalDyadic.mem_toIntervalRat.mp hval) cfg.taylorDepth
      have hexp : Real.exp (Expr.evalAlong a rhoReal idx x) ∈
          expIntervalDyadic (LeanCert.Internal.Dyadic.evalUnchecked a rho cfg) cfg := by
        simpa [Expr.evalAlong_eq, expIntervalDyadic] using
          (IntervalDyadic.mem_ofIntervalRat hexpRat cfg.precision hprec)
      simp only [Expr.evalAlong_exp, deriv_exp hd, LeanCert.Internal.AD.Dyadic.evalTotal,
        DualIntervalDyadic.exp, IntervalDyadic.mulRounded]
      rw [evalTotalDyadic_val_of_fragment a (mkDualDyadicEnv rho idx) cfg hsupp]
      simp only [mkDualDyadicEnv_values]
      exact IntervalDyadic.roundOut_contains
        (IntervalDyadic.mem_mul hexp (ih hsupp hdom)) cfg.precision
  | sin a ih =>
      simp only [checkDyadicADFragment] at hsupp
      simp only [evalDomainValidDyadic] at hdom
      have hd := evalAlong_differentiableAt_of_dyadic_facts a rhoReal rho idx cfg x hx hrho
        hprec hsupp hdom
      have hval := evalIntervalDyadic_correct_of_domain a
        (Expr.updateVar rhoReal idx x) rho hmemValue cfg hprec hdom
      have hcosRat := IntervalRat.mem_cosComputable
        (IntervalDyadic.mem_toIntervalRat.mp hval) cfg.taylorDepth
      have hcos : Real.cos (Expr.evalAlong a rhoReal idx x) ∈
          cosIntervalDyadic (LeanCert.Internal.Dyadic.evalUnchecked a rho cfg) cfg := by
        simpa [Expr.evalAlong_eq, cosIntervalDyadic] using
          (IntervalDyadic.mem_ofIntervalRat hcosRat cfg.precision hprec)
      simp only [Expr.evalAlong_sin, deriv_sin hd, LeanCert.Internal.AD.Dyadic.evalTotal,
        DualIntervalDyadic.sin, IntervalDyadic.mulRounded]
      rw [evalTotalDyadic_val_of_fragment a (mkDualDyadicEnv rho idx) cfg hsupp]
      simp only [mkDualDyadicEnv_values]
      exact IntervalDyadic.roundOut_contains
        (IntervalDyadic.mem_mul hcos (ih hsupp hdom)) cfg.precision
  | cos a ih =>
      simp only [checkDyadicADFragment] at hsupp
      simp only [evalDomainValidDyadic] at hdom
      have hd := evalAlong_differentiableAt_of_dyadic_facts a rhoReal rho idx cfg x hx hrho
        hprec hsupp hdom
      have hval := evalIntervalDyadic_correct_of_domain a
        (Expr.updateVar rhoReal idx x) rho hmemValue cfg hprec hdom
      have hsinRat := IntervalRat.mem_sinComputable
        (IntervalDyadic.mem_toIntervalRat.mp hval) cfg.taylorDepth
      have hsin : Real.sin (Expr.evalAlong a rhoReal idx x) ∈
          sinIntervalDyadic (LeanCert.Internal.Dyadic.evalUnchecked a rho cfg) cfg := by
        simpa [Expr.evalAlong_eq, sinIntervalDyadic] using
          (IntervalDyadic.mem_ofIntervalRat hsinRat cfg.precision hprec)
      simp only [Expr.evalAlong_cos, deriv_cos hd, LeanCert.Internal.AD.Dyadic.evalTotal,
        DualIntervalDyadic.cos, IntervalDyadic.mulRounded]
      rw [evalTotalDyadic_val_of_fragment a (mkDualDyadicEnv rho idx) cfg hsupp]
      simp only [mkDualDyadicEnv_values]
      exact IntervalDyadic.roundOut_contains
        (IntervalDyadic.mem_mul (IntervalDyadic.mem_neg hsin) (ih hsupp hdom)) cfg.precision
  | log a ih =>
      simp only [checkDyadicADFragment] at hsupp
      simp only [evalDomainValidDyadic] at hdom
      have hval := evalIntervalDyadic_correct_of_domain a
        (Expr.updateVar rhoReal idx x) rho hmemValue cfg hprec hdom.1
      have hval' : Expr.evalAlong a rhoReal idx x ∈
          LeanCert.Internal.Dyadic.evalUnchecked a rho cfg := by
        simpa only [Expr.evalAlong_eq] using hval
      have hpos : 0 < Expr.evalAlong a rhoReal idx x :=
        lt_of_lt_of_le (by exact_mod_cast hdom.2)
          (IntervalDyadic.mem_toIntervalRat.mp hval').1
      have hd := evalAlong_differentiableAt_of_dyadic_facts a rhoReal rho idx cfg x hx hrho
        hprec hsupp hdom.1
      rw [Expr.evalAlong_log]
      have hcomp : (fun t => Real.log (Expr.evalAlong a rhoReal idx t)) =
          Real.log ∘ Expr.evalAlong a rhoReal idx := rfl
      rw [hcomp, deriv_comp x (Real.differentiableAt_log (ne_of_gt hpos)) hd]
      simp only [Real.deriv_log, LeanCert.Internal.AD.Dyadic.evalTotal,
        DualIntervalDyadic.log, IntervalDyadic.mulRounded]
      rw [evalTotalDyadic_val_of_fragment a (mkDualDyadicEnv rho idx) cfg hsupp]
      simp only [mkDualDyadicEnv_values]
      have hnz : (LeanCert.Internal.Dyadic.evalUnchecked a rho cfg).toIntervalRat.lo > 0 ∨
          (LeanCert.Internal.Dyadic.evalUnchecked a rho cfg).toIntervalRat.hi < 0 := Or.inl hdom.2
      have hinvRat := mem_invInterval_nonzero
        (IntervalDyadic.mem_toIntervalRat.mp hval') hnz
      have hinv : (Expr.evalAlong a rhoReal idx x)⁻¹ ∈
          invIntervalDyadic (LeanCert.Internal.Dyadic.evalUnchecked a rho cfg) cfg :=
        IntervalDyadic.mem_ofIntervalRat hinvRat cfg.precision hprec
      exact IntervalDyadic.roundOut_contains
        (IntervalDyadic.mem_mul hinv (ih hsupp hdom.1)) cfg.precision
  | atan | arsinh | atanh | sinc | erf | sinh | cosh | tanh | sqrt | namedConst =>
      simp [checkDyadicADFragment] at hsupp

/-- Golden theorem: successful checked Dyadic indexed AD encloses the true
partial derivative. -/
theorem evalWithDerivDyadicChecked_der_correct (e : Expr)
    (rhoReal : Nat → ℝ) (rho : IntervalDyadicEnv) (idx : Nat) (cfg : DyadicConfig)
    (D : DualIntervalDyadic) (x : ℝ) (hx : x ∈ rho idx)
    (hrho : ∀ i, rhoReal i ∈ rho i)
    (hok : evalWithDerivDyadicChecked e rho idx cfg = .ok D) :
    deriv (Expr.evalAlong e rhoReal idx) x ∈ D.der := by
  obtain ⟨hprec, hsupp, hdom, rfl⟩ := evalDualDyadicChecked_facts hok
  exact evalTotalDyadic_der_correct_of_facts e rhoReal rho idx cfg x hx hrho hprec hsupp
    (by simpa using hdom)

/-- Golden theorem for the derivative-only Dyadic API. -/
theorem derivIntervalDyadicChecked_correct (e : Expr)
    (rhoReal : Nat → ℝ) (rho : IntervalDyadicEnv) (idx : Nat) (cfg : DyadicConfig)
    (dI : IntervalDyadic) (x : ℝ) (hx : x ∈ rho idx)
    (hrho : ∀ i, rhoReal i ∈ rho i)
    (hok : derivIntervalDyadicChecked e rho idx cfg = .ok dI) :
    deriv (Expr.evalAlong e rhoReal idx) x ∈ dI := by
  simp only [derivIntervalDyadicChecked, bind, Except.bind] at hok
  cases hdual : evalWithDerivDyadicChecked e rho idx cfg with
  | error err => simp [hdual] at hok
  | ok D =>
      rw [hdual] at hok
      simp only [pure, Except.pure, Except.ok.injEq] at hok
      subst dI
      exact evalWithDerivDyadicChecked_der_correct e rhoReal rho idx cfg D x hx hrho hdual

/-- Golden theorem for rational input boxes converted to the Dyadic backend. -/
theorem derivIntervalDyadicCheckedOfRat_correct (e : Expr)
    (rhoReal : Nat → ℝ) (rho : IntervalEnv) (idx : Nat) (cfg : DyadicConfig)
    (dI : IntervalDyadic) (x : ℝ) (hx : x ∈ rho idx)
    (hrho : ∀ i, rhoReal i ∈ rho i)
    (hok : derivIntervalDyadicCheckedOfRat e rho idx cfg = .ok dI) :
    deriv (Expr.evalAlong e rhoReal idx) x ∈ dI := by
  simp only [derivIntervalDyadicCheckedOfRat] at hok
  split at hok
  · rename_i hprec
    apply derivIntervalDyadicChecked_correct e rhoReal
      (toDyadicEnv rho cfg.precision) idx cfg dI x
    · exact IntervalDyadic.mem_ofIntervalRat hx cfg.precision hprec
    · intro i
      exact IntervalDyadic.mem_ofIntervalRat (hrho i) cfg.precision hprec
    · exact hok
  · contradiction

/-- Compute the first `n` partial derivatives with the checked Dyadic backend. -/
def gradientIntervalDyadicChecked (e : Expr) (rho : IntervalDyadicEnv) (n : Nat)
    (cfg : DyadicConfig := {}) : EvalResult (List IntervalDyadic) :=
  if cfg.precision ≤ 0 then
    (List.range n).mapM fun i => derivIntervalDyadicChecked e rho i cfg
  else
    .error (.invalidConfiguration "Dyadic AD precision must be nonpositive")

/-- Rational-input convenience boundary for the first `n` Dyadic partials. -/
def gradientIntervalDyadicCheckedOfRat (e : Expr) (rho : IntervalEnv) (n : Nat)
    (cfg : DyadicConfig := {}) : EvalResult (List IntervalDyadic) :=
  if cfg.precision ≤ 0 then
    gradientIntervalDyadicChecked e (toDyadicEnv rho cfg.precision) n cfg
  else
    .error (.invalidConfiguration "Dyadic AD precision must be nonpositive")

private theorem derivIntervalsDyadicChecked_correct (e : Expr)
    (rhoReal : Nat → ℝ) (rho : IntervalDyadicEnv) (cfg : DyadicConfig)
    (hrho : ∀ i, rhoReal i ∈ rho i) (indices : List Nat)
    (gradient : List IntervalDyadic)
    (hok : indices.mapM (fun i => derivIntervalDyadicChecked e rho i cfg) = .ok gradient) :
    List.Forall₂ (fun i dI => deriv (Expr.evalAlong e rhoReal i) (rhoReal i) ∈ dI)
      indices gradient := by
  induction indices generalizing gradient with
  | nil =>
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hok
      subst gradient
      exact .nil
  | cons i indices ih =>
      simp only [List.mapM_cons] at hok
      cases hdi : derivIntervalDyadicChecked e rho i cfg with
      | error err =>
          rw [hdi] at hok
          simp only [bind, Except.bind] at hok
          cases hok
      | ok dI =>
          rw [hdi] at hok
          simp only [bind, Except.bind] at hok
          cases htail : indices.mapM (fun j => derivIntervalDyadicChecked e rho j cfg) with
          | error err =>
              rw [htail] at hok
              cases hok
          | ok tail =>
              rw [htail] at hok
              simp only [pure, Except.pure, Except.ok.injEq] at hok
              subst gradient
              exact .cons
                (derivIntervalDyadicChecked_correct e rhoReal rho i cfg dI
                  (rhoReal i) (hrho i) hrho hdi)
                (ih tail htail)

/-- Golden theorem for the checked Dyadic gradient API. -/
theorem gradientIntervalDyadicChecked_correct (e : Expr)
    (rhoReal : Nat → ℝ) (rho : IntervalDyadicEnv) (n : Nat) (cfg : DyadicConfig)
    (hrho : ∀ i, rhoReal i ∈ rho i) (gradient : List IntervalDyadic)
    (hok : gradientIntervalDyadicChecked e rho n cfg = .ok gradient) :
    List.Forall₂ (fun i dI => deriv (Expr.evalAlong e rhoReal i) (rhoReal i) ∈ dI)
      (List.range n) gradient := by
  simp only [gradientIntervalDyadicChecked] at hok
  split at hok
  · exact derivIntervalsDyadicChecked_correct e rhoReal rho cfg hrho
      (List.range n) gradient hok
  · contradiction

/-- Golden theorem for checked Dyadic gradients over rational input boxes. -/
theorem gradientIntervalDyadicCheckedOfRat_correct (e : Expr)
    (rhoReal : Nat → ℝ) (rho : IntervalEnv) (n : Nat) (cfg : DyadicConfig)
    (hrho : ∀ i, rhoReal i ∈ rho i) (gradient : List IntervalDyadic)
    (hok : gradientIntervalDyadicCheckedOfRat e rho n cfg = .ok gradient) :
    List.Forall₂ (fun i dI => deriv (Expr.evalAlong e rhoReal i) (rhoReal i) ∈ dI)
      (List.range n) gradient := by
  simp only [gradientIntervalDyadicCheckedOfRat] at hok
  split at hok
  · rename_i hprec
    apply gradientIntervalDyadicChecked_correct e rhoReal
      (toDyadicEnv rho cfg.precision) n cfg
    · intro i
      exact IntervalDyadic.mem_ofIntervalRat (hrho i) cfg.precision hprec
    · exact hok
  · contradiction

end LeanCert.Engine

end

end

section

/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
/-!
# Automatic Differentiation via Intervals

This module provides forward-mode automatic differentiation using interval
arithmetic. We compute both the value and derivative of an expression,
with rigorous bounds on both.

## Module Structure

* `AD.Basic` - Core types: `DualInterval`, basic operations (`add`, `mul`, `neg`)
* `AD.Transcendental` - Transcendental functions (`sin`, `cos`, `exp`, etc.)
* `AD.Eval` - Evaluators: `LeanCert.Internal.AD.evalUnchecked`, `evalDualOption`, `derivInterval`
* `AD.Correctness` - Correctness theorems for supported expressions
* `AD.PartialCorrectness` - Correctness for partial functions (inv, log, sqrt)
* `AD.Computable` - Taylor-based computable evaluators
* `AD.DomainChecked` - Computable AD with box-dependent checks for inv and log
* `AD.Dyadic` - Domain-aware AD with bounded-denominator Dyadic arithmetic

## Main definitions

* `DualInterval` - A pair of intervals representing (value, derivative)
* `LeanCert.Internal.AD.evalUnchecked` - Evaluate expression to get value and derivative intervals
* `evalDualOption` - Partial evaluator supporting inv, log, sqrt
* `LeanCert.Internal.AD.evalTotalCore` - Computable evaluator for native_decide
* `evalDualChecked`, `derivIntervalChecked` - Computable, structured-failure APIs for inv/log
* `evalDualDyadicChecked`, `derivIntervalDyadicChecked` - Checked Dyadic counterparts

## Main theorems

* `LeanCert.Engine.evalDualUnchecked_val_correct` - Value component is correct for supported
expressions
* `LeanCert.Engine.evalDualUnchecked_der_correct` - Derivative component is correct for supported
expressions
* `evalDualOption_val_correct`, `evalDualOption_der_correct` - Correctness with domain checks
* `LeanCert.Internal.AD.evalTotalCore_val_correct`, `LeanCert.Internal.AD.evalTotalCore_der_correct`
- Computable correctness
* `evalWithDerivChecked_der_correct`, `derivIntervalChecked_correct` - Golden theorems for
  successful domain-aware computation

All theorems are FULLY PROVED with no sorry or axioms.
-/

public section

end

end

section

/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
/-!
# N-Dimensional Boxes for Global Optimization

This file provides the `Box` type for representing n-dimensional domains
as products of intervals, along with helper functions for branch-and-bound
optimization.

## Main definitions

* `Box` - A list of intervals representing an n-dimensional box
* `Box.toEnv` - Convert a box to an interval environment
* `Box.mem` - Membership: a point (list of reals) is in a box
* `Box.widestDim` - Find the dimension with the largest width (for splitting)
* `Box.split` - Split a box along a given dimension
* `Box.volume` - Product of interval widths (heuristic measure)

## Design

A `Box` is represented as `List IntervalRat`, where the i-th element is the
interval for the i-th variable. This allows boxes of any dimension.

For expressions with `n` variables (var 0 through var n-1), a box should
have at least `n` intervals. The conversion `Box.toEnv` returns `default`
for out-of-bounds indices.
-/

/-! ### Box type and basic operations -/

public section

namespace LeanCert.Engine.Optimization

open LeanCert.Core
open LeanCert.Engine

/-- An n-dimensional box as a list of intervals.
    The i-th element is the interval for variable i. -/
abbrev Box := List IntervalRat

/-- A point in ℝⁿ represented as a list of reals -/
abbrev Point := List ℝ

/-- A rational point in ℚⁿ -/
abbrev PointQ := List ℚ

namespace Box

/-- Create a one-dimensional box from a single interval. -/
def ofInterval (I : IntervalRat) : Box := [I]

/-- Convert a box to an interval environment.
    Returns `default` for out-of-bounds indices (i.e., the whole real line approximation). -/
def toEnv (B : Box) : IntervalEnv :=
  fun i => B.getD i default

/-- The dimension (number of intervals) of a box -/
def dim (B : Box) : ℕ := B.length

/-- Check if a point is in a box.
    A point is in a box if each coordinate is in the corresponding interval. -/
def mem (p : Point) (B : Box) : Prop :=
  ∃ (h : p.length = B.length), ∀ i : Fin B.length, p[i.val]'(by rw [h]; exact i.isLt) ∈
    B[i.val]'(by exact i.isLt)

/-- Membership for a real function (environment) in a box.
    This is the key notion for correctness: ρ ∈ B means ρ i ∈ B[i] for all i < B.length. -/
def envMem (ρ : Nat → ℝ) (B : Box) : Prop :=
  ∀ i : Fin B.length, ρ i.val ∈ B[i.val]'(by exact i.isLt)

/-- envMem implies the general IntervalEnv membership for toEnv
    NOTE: For indices beyond the box dimension, we use the default interval [0,0].
    This means expressions should only use variables 0..B.length-1 for correct results. -/
theorem envMem_toEnv (ρ : Nat → ℝ) (B : Box) (h : envMem ρ B)
    (hzero : ∀ i, i ≥ B.length → ρ i = 0) :
    LeanCert.Engine.envMem ρ (toEnv B) := by
  intro i
  unfold toEnv
  by_cases hi : i < B.length
  · simp only [List.getD, List.getElem?_eq_getElem hi, Option.getD]
    exact h ⟨i, hi⟩
  · have hge : B.length ≤ i := not_lt.mp hi
    simp only [List.getD, List.getElem?_eq_none (not_lt.mp hi), Option.getD]
    rw [IntervalRat.mem_default]
    exact hzero i hge

/-! ### Width and dimension selection -/

/-- Width of an interval -/
def intervalWidth (I : IntervalRat) : ℚ := I.hi - I.lo

/-- Get the width of each dimension -/
def widths (B : Box) : List ℚ := B.map intervalWidth

/-- Find the index of the maximum element in a list (returns 0 for empty list) -/
def maxIdx (xs : List ℚ) : Nat :=
  match xs with
  | [] => 0
  | [_] => 0
  | x :: y :: rest =>
    let restMax := maxIdx (y :: rest)
    if x ≥ (y :: rest).getD restMax 0 then 0 else restMax + 1

/-- Find the dimension with the widest interval (heuristic for splitting).
    Returns 0 if the box is empty. -/
def widestDim (B : Box) : Nat :=
  maxIdx (widths B)

/-- Alternative: find widest dimension with explicit fold -/
def widestDim' (B : Box) : Nat :=
  let indexed := B.zipIdx.map fun (I, i) => (i, intervalWidth I)
  match indexed.argmax (·.2) with
  | some (i, _) => i
  | none => 0

/-! ### Box splitting -/

/-- Split a box along a given dimension by bisecting that interval.
    Returns the original box if the dimension is out of bounds. -/
def split (B : Box) (dim : Nat) : Box × Box :=
  if h : dim < B.length then
    let I := B[dim]'h
    let (I₁, I₂) := I.bisect
    let B₁ := B.set dim I₁
    let B₂ := B.set dim I₂
    (B₁, B₂)
  else
    (B, B)

/-- Split along the widest dimension -/
def splitWidest (B : Box) : Box × Box :=
  split B (widestDim B)

/-- Splitting preserves the number of box coordinates. -/
theorem split_length_eq (B : Box) (d : Nat) :
    (split B d).1.length = B.length ∧ (split B d).2.length = B.length := by
  simp only [split]
  split_ifs with h
  · constructor <;> simp only [List.length_set]
  · exact ⟨rfl, rfl⟩

/-- The lower child of a split is a semantic sub-box of its parent. -/
theorem envMem_of_envMem_split (B : Box) (d : Nat) (ρ : Nat → ℝ) :
    envMem ρ (split B d).1 → envMem ρ B := by
  intro h
  unfold split at h
  split_ifs at h with hd
  · intro ⟨i, hi⟩
    have hi' : i < (B.set d (B[d].bisect.1)).length := by
      simp only [List.length_set]
      exact hi
    have hmem := h ⟨i, hi'⟩
    simp only [List.getElem_set] at hmem
    split_ifs at hmem with heq
    · subst heq
      exact IntervalRat.mem_of_mem_bisect_left hmem
    · exact hmem
  · exact h

/-- The upper child of a split is a semantic sub-box of its parent. -/
theorem envMem_of_envMem_split_right (B : Box) (d : Nat) (ρ : Nat → ℝ) :
    envMem ρ (split B d).2 → envMem ρ B := by
  intro h
  unfold split at h
  split_ifs at h with hd
  · intro ⟨i, hi⟩
    have hi' : i < (B.set d (B[d].bisect.2)).length := by
      simp only [List.length_set]
      exact hi
    have hmem := h ⟨i, hi'⟩
    simp only [List.getElem_set] at hmem
    split_ifs at hmem with heq
    · subst heq
      exact IntervalRat.mem_of_mem_bisect_right hmem
    · exact hmem
  · exact h

/-! ### Volume and size heuristics -/

/-- Volume of a box (product of widths).
    Returns 0 for empty box. -/
def volume (B : Box) : ℚ :=
  (widths B).foldl (· * ·) 1

/-- Maximum width across all dimensions -/
def maxWidth (B : Box) : ℚ :=
  (widths B).foldl max 0

/-- Check if a box is "small" (max width below threshold) -/
def isSmall (B : Box) (threshold : ℚ) : Bool :=
  maxWidth B ≤ threshold

/-! ### Box construction helpers -/

/-- Create a box from a list of (lo, hi) pairs -/
def ofPairs (pairs : List (ℚ × ℚ)) : Box :=
  pairs.filterMap fun (lo, hi) =>
    if h : lo ≤ hi then some ⟨lo, hi, h⟩ else none

/-- Create a unit box [0,1]ⁿ -/
def unit (n : Nat) : Box :=
  List.replicate n ⟨0, 1, by norm_num⟩

/-- Create a symmetric box [-1,1]ⁿ -/
def symmetric (n : Nat) : Box :=
  List.replicate n ⟨-1, 1, by norm_num⟩

/-- Create a box from bounds: [lo₀, hi₀] × ... × [loₙ₋₁, hiₙ₋₁] -/
def ofBounds (los his : List ℚ) (_h : los.length = his.length) : Box :=
  (los.zip his).filterMap fun (lo, hi) =>
    if hle : lo ≤ hi then some ⟨lo, hi, hle⟩ else none

/-! ### Membership lemmas -/

/-- If a point is in a box, its i-th coordinate is in the i-th interval -/
theorem coord_mem_of_mem (p : Point) (B : Box) (h : mem p B) (i : Fin B.length) :
    p[i.val]'(by obtain ⟨hlen, _⟩ := h; rw [hlen]; exact i.isLt) ∈ B[i.val]'(by exact i.isLt) := by
  obtain ⟨hlen, hmem⟩ := h
  exact hmem i

/-- After splitting, any point in the original box is in one of the halves. -/
theorem mem_split_cases (B : Box) (d : Nat) (hd : d < B.length)
    (p : Point) (hp : mem p B) :
    mem p (split B d).1 ∨ mem p (split B d).2 := by
  simp only [split, hd, ↓reduceDIte]
  obtain ⟨hp_len, hp_mem⟩ := hp
  have hp_d : p[d]'(by rw [hp_len]; exact hd) ∈ B[d]'hd := hp_mem ⟨d, hd⟩
  have hbisect := IntervalRat.mem_bisect_or hp_d
  cases hbisect with
  | inl hleft =>
    left
    have hlen1 : (B.set d (B[d].bisect.1)).length = B.length := List.length_set
    use (by rw [hlen1]; exact hp_len)
    intro ⟨i, hi⟩
    have hi_orig : i < B.length := by rw [← hlen1]; exact hi
    by_cases h_eq : i = d
    · -- i = d: use the bisection result
      simp only [h_eq, List.getElem_set_self]
      convert hleft using 2
    · -- i ≠ d: use original membership
      have hne : d ≠ i := fun h => h_eq h.symm
      simp only [List.getElem_set_ne hne hi]
      have hp_i := hp_mem ⟨i, hi_orig⟩
      convert hp_i using 2
  | inr hright =>
    right
    have hlen2 : (B.set d (B[d].bisect.2)).length = B.length := List.length_set
    use (by rw [hlen2]; exact hp_len)
    intro ⟨i, hi⟩
    have hi_orig : i < B.length := by rw [← hlen2]; exact hi
    by_cases h_eq : i = d
    · simp only [h_eq, List.getElem_set_self]
      convert hright using 2
    · have hne : d ≠ i := fun h => h_eq h.symm
      simp only [List.getElem_set_ne hne hi]
      have hp_i := hp_mem ⟨i, hi_orig⟩
      convert hp_i using 2

/-- Environment membership after splitting. -/
theorem envMem_split_cases (B : Box) (d : Nat) (hd : d < B.length)
    (ρ : Nat → ℝ) (hρ : envMem ρ B) :
    envMem ρ (split B d).1 ∨ envMem ρ (split B d).2 := by
  simp only [split, hd, ↓reduceDIte]
  have hρ_d : ρ d ∈ B[d]'hd := hρ ⟨d, hd⟩
  have hbisect := IntervalRat.mem_bisect_or hρ_d
  -- After bisection, ρ d is in either the left or right half
  cases hbisect with
  | inl hleft =>
    left
    intro ⟨i, hi⟩
    -- After B.set d I₁, length is preserved
    have hlen : (B.set d (B[d].bisect.1)).length = B.length := List.length_set
    have hi_orig : i < B.length := by rw [← hlen]; exact hi
    by_cases h_eq : i = d
    · -- i = d: use the bisection result
      simp only [h_eq, List.getElem_set_self]
      exact hleft
    · -- i ≠ d: use original membership
      have hne : d ≠ i := fun h => h_eq h.symm
      simp only [List.getElem_set_ne hne hi]
      exact hρ ⟨i, hi_orig⟩
  | inr hright =>
    right
    intro ⟨i, hi⟩
    have hlen : (B.set d (B[d].bisect.2)).length = B.length := List.length_set
    have hi_orig : i < B.length := by rw [← hlen]; exact hi
    by_cases h_eq : i = d
    · simp only [h_eq, List.getElem_set_self]
      exact hright
    · have hne : d ≠ i := fun h => h_eq h.symm
      simp only [List.getElem_set_ne hne hi]
      exact hρ ⟨i, hi_orig⟩

end Box

end LeanCert.Engine.Optimization

end

end

section

/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
/-!
# Global Optimization via Branch-and-Bound

This file implements verified global optimization over intervals using
branch-and-bound with interval arithmetic and derivative bounds.

## Phase Status

**This module is now largely Phase 1 (verified).** The core correctness theorems
are fully proved for the ADSupported subset.

## Main definitions

* `minimizeInterval` - Find a lower bound on min f over an interval
* `maximizeInterval` - Find an upper bound on max f over an interval
* Correctness theorems (fully proved for ADSupported)

## Algorithm

Branch-and-bound with the following pruning rules:
1. **Interval evaluation**: If f([a,b]) = [lo, hi], then min f ≥ lo
2. **Monotonicity**: If f'([a,b]) > 0, f is increasing, so min is at a
3. **Subdivision**: Split interval and recurse

-/

/-! ### Optimization result -/

public section

namespace LeanCert.Engine

open LeanCert.Core

/-- Result of an optimization computation -/
structure OptResult where
  /-- Interval containing the optimum value -/
  valueBound : IntervalRat
  /-- Interval containing an optimizing point (if found) -/
  argBound : Option IntervalRat
  /-- Depth of search performed -/
  depth : ℕ

/-- Combine two subinterval bounds, preserving their lower and upper bounds. -/
noncomputable def OptResult.merge (r₁ r₂ : OptResult) : OptResult :=
  if h : r₁.valueBound.lo ≤ r₂.valueBound.lo then
    { valueBound :=
        { lo := r₁.valueBound.lo
          hi := min r₁.valueBound.hi r₂.valueBound.hi
          le := by
            apply le_min
            · exact r₁.valueBound.le
            · calc r₁.valueBound.lo ≤ r₂.valueBound.lo := h
                _ ≤ r₂.valueBound.hi := r₂.valueBound.le }
      argBound := r₁.argBound
      depth := max r₁.depth r₂.depth }
  else
    { valueBound :=
        { lo := r₂.valueBound.lo
          hi := min r₁.valueBound.hi r₂.valueBound.hi
          le := by
            apply le_min
            · calc r₂.valueBound.lo ≤ r₁.valueBound.lo := le_of_lt (not_le.mp h)
                _ ≤ r₁.valueBound.hi := r₁.valueBound.le
            · exact r₂.valueBound.le }
      argBound := r₂.argBound
      depth := max r₁.depth r₂.depth }

/-! ### Minimization -/

/-- Check if derivative interval is strictly positive -/
noncomputable def derivStrictlyPositive (e : Expr) (I : IntervalRat) (varIdx : Nat) : Bool :=
  let dI := derivInterval e (fun _ => I) varIdx
  0 < dI.lo

/-- Check if derivative interval is strictly negative -/
noncomputable def derivStrictlyNegative (e : Expr) (I : IntervalRat) (varIdx : Nat) : Bool :=
  let dI := derivInterval e (fun _ => I) varIdx
  dI.hi < 0

/-- Simple branch-and-bound minimization.

Returns an interval [lo, hi] such that:
- lo ≤ min_{x ∈ I} f(x)
- hi ≥ min_{x ∈ I} f(x)
-/
@[expose]
noncomputable def minimizeInterval (e : Expr) (I : IntervalRat) (varIdx : Nat)
    (maxDepth : ℕ) : OptResult :=
  go I maxDepth
where
  /-- Recursive interval minimization with a decreasing subdivision budget. -/
  go (J : IntervalRat) (depth : ℕ) : OptResult :=
    if depth = 0 then
      -- Base case: just use interval evaluation
      { valueBound := LeanCert.Internal.Rational.evalUnchecked1 e J
        argBound := some J
        depth := maxDepth }
    else
      -- Check monotonicity
      if derivStrictlyPositive e J varIdx then
        -- f is increasing, minimum is at left endpoint
        { valueBound := LeanCert.Internal.Rational.evalUnchecked1 e (IntervalRat.singleton J.lo)
          argBound := some (IntervalRat.singleton J.lo)
          depth := maxDepth - depth }
      else if derivStrictlyNegative e J varIdx then
        -- f is decreasing, minimum is at right endpoint
        { valueBound := LeanCert.Internal.Rational.evalUnchecked1 e (IntervalRat.singleton J.hi)
          argBound := some (IntervalRat.singleton J.hi)
          depth := maxDepth - depth }
      else
        -- Bisect and take the better bound
        let (J₁, J₂) := J.bisect
        let r₁ := go J₁ (depth - 1)
        let r₂ := go J₂ (depth - 1)
        OptResult.merge r₁ r₂
  termination_by depth
  decreasing_by all_goals omega

/-- Base case correctness: interval evaluation gives a valid lower bound.
    This theorem is FULLY PROVED - no sorry, no axioms. -/
theorem minimizeInterval_base_correct (e : Expr) (hsupp : ADSupported e)
    (I : IntervalRat) :
    ∀ x ∈ I, (LeanCert.Internal.Rational.evalUnchecked1 e I).lo ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  have h := evalInterval1_correct e hsupp x I hx
  simp only [IntervalRat.mem_def] at h
  exact h.1

/-! ### Derivative bounds and monotonicity -/

/-- For single-variable expressions evaluated with (fun _ => I), derivative is correct.
    We use evalWithDeriv1 which directly uses varActive for all variables. -/
theorem derivInterval_correct_evalWithDeriv1 (e : Expr) (hsupp : ADSupported e)
    (I : IntervalRat) (x : ℝ) (hx : x ∈ I) :
    deriv (evalFunc1 e) x ∈ (evalWithDeriv1 e I).der := by
  -- evalWithDeriv1 e I = LeanCert.Internal.AD.evalUnchecked e (fun _ => DualInterval.varActive I)
  -- This matches exactly what LeanCert.Engine.evalDualUnchecked_der_correct expects
  simp only [evalWithDeriv1]
  exact LeanCert.Engine.evalDualUnchecked_der_correct e hsupp I x hx

/-- Derivative is in derivInterval for expressions that only use var 0.
    FULLY PROVED - no sorry. -/
theorem derivInterval_correct_single (e : Expr) (hsupp : ADSupported e) (hvar0 : UsesOnlyVar0 e)
    (I : IntervalRat) (x : ℝ) (hx : x ∈ I) :
    deriv (evalFunc1 e) x ∈ derivInterval e (fun _ => I) 0 := by
  rw [derivInterval_eq_evalWithDeriv1_of_UsesOnlyVar0 e hvar0]
  exact derivInterval_correct_evalWithDeriv1 e hsupp I x hx

/-- If the derivative interval is strictly positive, derivative is positive everywhere -/
theorem deriv_pos_on_interval (e : Expr) (hsupp : ADSupported e) (hvar0 : UsesOnlyVar0 e)
    (I : IntervalRat) (hpos : 0 < (derivInterval e (fun _ => I) 0).lo) :
    ∀ x ∈ I, 0 < deriv (evalFunc1 e) x := by
  intro x hx
  have hmem := derivInterval_correct_single e hsupp hvar0 I x hx
  simp only [IntervalRat.mem_def] at hmem
  have hlo_cast : (0 : ℝ) < ((derivInterval e (fun _ => I) 0).lo : ℝ) := by exact_mod_cast hpos
  calc (0 : ℝ) < ((derivInterval e (fun _ => I) 0).lo : ℝ) := hlo_cast
    _ ≤ deriv (evalFunc1 e) x := hmem.1

/-- If the derivative interval is strictly negative, derivative is negative everywhere -/
theorem deriv_neg_on_interval (e : Expr) (hsupp : ADSupported e) (hvar0 : UsesOnlyVar0 e)
    (I : IntervalRat) (hneg : (derivInterval e (fun _ => I) 0).hi < 0) :
    ∀ x ∈ I, deriv (evalFunc1 e) x < 0 := by
  intro x hx
  have hmem := derivInterval_correct_single e hsupp hvar0 I x hx
  simp only [IntervalRat.mem_def] at hmem
  have hhi_cast : ((derivInterval e (fun _ => I) 0).hi : ℝ) < (0 : ℝ) := by exact_mod_cast hneg
  calc deriv (evalFunc1 e) x ≤ ((derivInterval e (fun _ => I) 0).hi : ℝ) := hmem.2
    _ < 0 := hhi_cast

/-- Strictly positive derivative implies strict monotonicity -/
theorem strictMonoOn_of_deriv_pos_interval (e : Expr) (hsupp : ADSupported e) (hvar0 :
  UsesOnlyVar0 e)
    (I : IntervalRat) (hpos : 0 < (derivInterval e (fun _ => I) 0).lo) :
    StrictMonoOn (evalFunc1 e) (Set.Icc (I.lo : ℝ) (I.hi : ℝ)) := by
  have hdiff := evalFunc1_differentiable e hsupp
  have hderiv_pos := deriv_pos_on_interval e hsupp hvar0 I hpos
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · exact hdiff.continuous.continuousOn
  · intro x hx
    -- Interior of Icc is Ioo, and Ioo ⊆ Icc
    rw [interior_Icc] at hx
    have hx_mem : x ∈ I := by
      simp only [IntervalRat.mem_def]
      exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    exact hderiv_pos x hx_mem

/-- Strictly negative derivative implies strict antitonicity -/
theorem strictAntiOn_of_deriv_neg_interval (e : Expr) (hsupp : ADSupported e) (hvar0 :
  UsesOnlyVar0 e)
    (I : IntervalRat) (hneg : (derivInterval e (fun _ => I) 0).hi < 0) :
    StrictAntiOn (evalFunc1 e) (Set.Icc (I.lo : ℝ) (I.hi : ℝ)) := by
  have hdiff := evalFunc1_differentiable e hsupp
  have hderiv_neg := deriv_neg_on_interval e hsupp hvar0 I hneg
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · exact hdiff.continuous.continuousOn
  · intro x hx
    -- Interior of Icc is Ioo
    rw [interior_Icc] at hx
    have hx_mem : x ∈ I := by
      simp only [IntervalRat.mem_def]
      exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    exact hderiv_neg x hx_mem

/-! ### Monotonicity-based bounds -/

/-- For increasing functions, minimum is at the left endpoint -/
theorem increasing_min_at_left (e : Expr) (hsupp : ADSupported e) (hvar0 : UsesOnlyVar0 e)
    (I : IntervalRat) (hpos : 0 < (derivInterval e (fun _ => I) 0).lo) :
    ∀ x ∈ I, evalFunc1 e I.lo ≤ evalFunc1 e x := by
  intro x hx
  have hmono := strictMonoOn_of_deriv_pos_interval e hsupp hvar0 I hpos
  simp only [IntervalRat.mem_def] at hx
  by_cases heq : (I.lo : ℝ) = x
  · rw [heq]
  · apply le_of_lt
    apply hmono
    · simp only [Set.mem_Icc]
      exact ⟨le_refl _, Rat.cast_le.mpr I.le⟩
    · simp only [Set.mem_Icc]; exact hx
    · exact lt_of_le_of_ne hx.1 heq

/-- For decreasing functions, minimum is at the right endpoint -/
theorem decreasing_min_at_right (e : Expr) (hsupp : ADSupported e) (hvar0 : UsesOnlyVar0 e)
    (I : IntervalRat) (hneg : (derivInterval e (fun _ => I) 0).hi < 0) :
    ∀ x ∈ I, evalFunc1 e I.hi ≤ evalFunc1 e x := by
  intro x hx
  have hmono := strictAntiOn_of_deriv_neg_interval e hsupp hvar0 I hneg
  simp only [IntervalRat.mem_def] at hx
  by_cases heq : x = (I.hi : ℝ)
  · rw [heq]
  · apply le_of_lt
    apply hmono
    · simp only [Set.mem_Icc]; exact hx
    · simp only [Set.mem_Icc]; exact ⟨(Rat.cast_le.mpr I.le), le_refl _⟩
    · exact lt_of_le_of_ne hx.2 heq

/-- Interval at left endpoint gives valid lower bound for increasing functions -/
theorem increasing_endpoint_bound (e : Expr) (hsupp : ADSupported e) (hvar0 : UsesOnlyVar0 e)
    (I : IntervalRat) (hpos : 0 < (derivInterval e (fun _ => I) 0).lo) :
    ∀ x ∈ I, (LeanCert.Internal.Rational.evalUnchecked1 e (IntervalRat.singleton I.lo)).lo ≤
      Expr.eval (fun _ => x) e := by
  intro x hx
  have hlo_mem : (I.lo : ℝ) ∈ IntervalRat.singleton I.lo := IntervalRat.mem_singleton I.lo
  have heval := evalInterval1_correct e hsupp I.lo (IntervalRat.singleton I.lo) hlo_mem
  simp only [IntervalRat.mem_def] at heval
  have hmin := increasing_min_at_left e hsupp hvar0 I hpos x hx
  simp only [evalFunc1] at hmin
  calc (LeanCert.Internal.Rational.evalUnchecked1 e (IntervalRat.singleton I.lo)).lo
      ≤ Expr.eval (fun _ => I.lo) e := by exact_mod_cast heval.1
    _ ≤ Expr.eval (fun _ => x) e := hmin

/-- Interval at right endpoint gives valid lower bound for decreasing functions -/
theorem decreasing_endpoint_bound (e : Expr) (hsupp : ADSupported e) (hvar0 : UsesOnlyVar0 e)
    (I : IntervalRat) (hneg : (derivInterval e (fun _ => I) 0).hi < 0) :
    ∀ x ∈ I, (LeanCert.Internal.Rational.evalUnchecked1 e (IntervalRat.singleton I.hi)).lo ≤
      Expr.eval (fun _ => x) e := by
  intro x hx
  have hhi_mem : (I.hi : ℝ) ∈ IntervalRat.singleton I.hi := IntervalRat.mem_singleton I.hi
  have heval := evalInterval1_correct e hsupp I.hi (IntervalRat.singleton I.hi) hhi_mem
  simp only [IntervalRat.mem_def] at heval
  have hmin := decreasing_min_at_right e hsupp hvar0 I hneg x hx
  simp only [evalFunc1] at hmin
  calc (LeanCert.Internal.Rational.evalUnchecked1 e (IntervalRat.singleton I.hi)).lo
      ≤ Expr.eval (fun _ => I.hi) e := by exact_mod_cast heval.1
    _ ≤ Expr.eval (fun _ => x) e := hmin

/-! ### Full optimization correctness -/

/-- Helper lemma for go correctness.
    FULLY PROVED for varIdx = 0 and UsesOnlyVar0 expressions. -/
theorem minimizeInterval_go_correct (e : Expr) (hsupp : ADSupported e) (hvar0 : UsesOnlyVar0 e)
    (maxDepth : ℕ) (depth : ℕ) (J : IntervalRat) :
    ∀ x ∈ J, (minimizeInterval.go e 0 maxDepth J depth).valueBound.lo
             ≤ Expr.eval (fun _ => x) e := by
  induction depth generalizing J with
  | zero =>
    -- Base case: depth = 0, just use interval evaluation
    intro x hx
    simp only [minimizeInterval.go, ↓reduceIte]
    exact minimizeInterval_base_correct e hsupp J x hx
  | succ n ih =>
    intro x hx
    -- Unfold the go definition for succ case
    -- Note: n + 1 ≠ 0, so we skip the first branch
    have hdepth : n + 1 ≠ 0 := Nat.succ_ne_zero n
    rw [minimizeInterval.go]
    simp only [hdepth, ↓reduceIte, OptResult.merge, Nat.add_sub_cancel]
    -- Now we branch on the derivative conditions
    split_ifs with hpos hneg hle
    · -- Derivative strictly positive: increasing function
      have hpos' : 0 < (derivInterval e (fun _ => J) 0).lo := by
        simp only [derivStrictlyPositive, decide_eq_true_eq] at hpos
        exact hpos
      exact increasing_endpoint_bound e hsupp hvar0 J hpos' x hx
    · -- Derivative strictly negative: decreasing function
      have hneg' : (derivInterval e (fun _ => J) 0).hi < 0 := by
        simp only [derivStrictlyNegative, decide_eq_true_eq] at hneg
        exact hneg
      exact decreasing_endpoint_bound e hsupp hvar0 J hneg' x hx
    · -- Bisection case, hle (r₁.lo ≤ r₂.lo)
      -- x is in one of the bisected intervals
      have hcases := IntervalRat.mem_bisect_or hx
      cases hcases with
      | inl h1 => exact ih J.bisect.1 x h1
      | inr h2 =>
        have h := ih J.bisect.2 x h2
        have hle_cast : ((minimizeInterval.go e 0 maxDepth (J.bisect.fst) n).valueBound.lo : ℝ)
            ≤ (minimizeInterval.go e 0 maxDepth (J.bisect.snd) n).valueBound.lo := by
              exact_mod_cast hle
        calc ((minimizeInterval.go e 0 maxDepth (J.bisect.fst) n).valueBound.lo : ℝ)
            ≤ (minimizeInterval.go e 0 maxDepth (J.bisect.snd) n).valueBound.lo := hle_cast
          _ ≤ Expr.eval (fun _ => x) e := h
    · -- Bisection case, ¬hle (r₁.lo > r₂.lo)
      have hcases := IntervalRat.mem_bisect_or hx
      cases hcases with
      | inl h1 =>
        have h := ih J.bisect.1 x h1
        have hlt := not_le.mp hle
        have hlt_cast : ((minimizeInterval.go e 0 maxDepth (J.bisect.snd) n).valueBound.lo : ℝ)
            ≤ (minimizeInterval.go e 0 maxDepth (J.bisect.fst) n).valueBound.lo := by
              exact_mod_cast (le_of_lt hlt)
        calc ((minimizeInterval.go e 0 maxDepth (J.bisect.snd) n).valueBound.lo : ℝ)
            ≤ (minimizeInterval.go e 0 maxDepth (J.bisect.fst) n).valueBound.lo := hlt_cast
          _ ≤ Expr.eval (fun _ => x) e := h
      | inr h2 => exact ih J.bisect.2 x h2

/-- Correctness: the minimum is in the computed interval.
    FULLY PROVED for varIdx = 0 and UsesOnlyVar0 expressions. -/
theorem minimizeInterval_correct (e : Expr) (hsupp : ADSupported e) (hvar0 : UsesOnlyVar0 e)
    (I : IntervalRat)
    (maxDepth : ℕ) :
    ∀ x ∈ I, (minimizeInterval e I 0 maxDepth).valueBound.lo ≤ Expr.eval (fun _ => x) e := by
  simp only [minimizeInterval]
  exact minimizeInterval_go_correct e hsupp hvar0 maxDepth maxDepth I

/-! ### Maximization -/

/-- Maximize by minimizing the negation -/
noncomputable def maximizeInterval (e : Expr) (I : IntervalRat) (varIdx : Nat)
    (maxDepth : ℕ) : OptResult :=
  let negResult := minimizeInterval (Expr.neg e) I varIdx maxDepth
  { valueBound := IntervalRat.neg negResult.valueBound
    argBound := negResult.argBound
    depth := negResult.depth }

/-- Correctness: the maximum is in the computed interval.
    FULLY PROVED for varIdx = 0 and UsesOnlyVar0 expressions. -/
theorem maximizeInterval_correct (e : Expr) (hsupp : ADSupported e) (hvar0 : UsesOnlyVar0 e)
    (I : IntervalRat)
    (maxDepth : ℕ) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ (maximizeInterval e I 0 maxDepth).valueBound.hi := by
  intro x hx
  -- max f = -min(-f)
  -- result.valueBound = neg (minimizeInterval (neg e) ...).valueBound
  -- result.valueBound.hi = -(minimizeInterval (neg e) ...).valueBound.lo
  -- We need: f(x) ≤ result.valueBound.hi
  --        = -(minimizeInterval (neg e) ...).valueBound.lo
  -- Equivalently: (minimizeInterval (neg e) ...).valueBound.lo ≤ -f(x)
  have hneg_supp : ADSupported (Expr.neg e) := ADSupported.neg hsupp
  have hneg_var0 : UsesOnlyVar0 (Expr.neg e) := UsesOnlyVar0.neg e hvar0
  have hmin := minimizeInterval_correct (Expr.neg e) hneg_supp hneg_var0 I maxDepth x hx
  simp only [Expr.eval_neg] at hmin
  -- hmin: (minimizeInterval (neg e) ...).valueBound.lo ≤ -f(x)
  -- Need: f(x) ≤ (maximizeInterval e ...).valueBound.hi
  --     = -(minimizeInterval (neg e) ...).valueBound.lo
  simp only [maximizeInterval, IntervalRat.neg]
  -- Goal: f(x) ≤ ↑(-(minimizeInterval (neg e) ...).valueBound.lo)
  -- From hmin: ↑(minimizeInterval (neg e) ...).valueBound.lo ≤ -f(x)
  -- So: f(x) ≤ -(minimizeInterval (neg e) ...).valueBound.lo
  have h : Expr.eval (fun _ => x) e ≤
           -(((minimizeInterval (Expr.neg e) I 0 maxDepth).valueBound.lo) : ℝ) := by
    have hcast : (((minimizeInterval (Expr.neg e) I 0 maxDepth).valueBound.lo) : ℝ)
                 ≤ -Expr.eval (fun _ => x) e := hmin
    linarith
  convert h using 1
  -- Need: ↑(-(minimizeInterval e.neg I 0 maxDepth).valueBound.lo) =
  --       -↑(minimizeInterval e.neg I 0 maxDepth).valueBound.lo
  simp only [Rat.cast_neg]

/-! ### Bounds checking -/

/-- Check if f(x) ≥ c for all x in I -/
noncomputable def checkLowerBound (e : Expr) (I : IntervalRat) (c : ℚ) (varIdx : Nat)
    (maxDepth : ℕ) : Bool :=
  let result := minimizeInterval e I varIdx maxDepth
  c ≤ result.valueBound.lo

/-- Check if f(x) ≤ c for all x in I -/
noncomputable def checkUpperBound (e : Expr) (I : IntervalRat) (c : ℚ) (varIdx : Nat)
    (maxDepth : ℕ) : Bool :=
  let result := maximizeInterval e I varIdx maxDepth
  result.valueBound.hi ≤ c

/-! ## N-Variable Optimization Infrastructure

The following section provides generalized optimization infrastructure that works
with arbitrary variable indices and multi-variable environments. This allows
optimizing along any coordinate while holding other variables fixed.

Key types:
- `IntervalEnv := Nat → IntervalRat` - maps variable indices to intervals
- `evalAlong e ρ idx` - evaluates `e` as a function of variable `idx`

The main advantage is that we can now optimize expressions with multiple variables
by fixing all but one variable and optimizing along that coordinate.
-/

/-! ### N-variable derivative bounds -/

/-- If the derivative interval along `idx` is strictly positive, derivative is positive everywhere.
    Generalized version that works with any variable index and environment. -/
theorem deriv_pos_on_interval_idx (e : Expr) (hsupp : ADSupported e)
    (ρ_real : Nat → ℝ) (ρ_int : IntervalEnv) (idx : Nat)
    (hρ : ∀ i, ρ_real i ∈ ρ_int i)
    (hpos : 0 < (derivInterval e ρ_int idx).lo) :
    ∀ x ∈ ρ_int idx, 0 < deriv (Expr.evalAlong e ρ_real idx) x := by
  intro x hx
  have hmem := derivInterval_correct_idx e hsupp ρ_real ρ_int idx hρ x hx
  simp only [IntervalRat.mem_def] at hmem
  have hlo_cast : (0 : ℝ) < ((derivInterval e ρ_int idx).lo : ℝ) := by exact_mod_cast hpos
  calc (0 : ℝ) < ((derivInterval e ρ_int idx).lo : ℝ) := hlo_cast
    _ ≤ deriv (Expr.evalAlong e ρ_real idx) x := hmem.1

/-- If the derivative interval along `idx` is strictly negative, derivative is negative everywhere.
    Generalized version that works with any variable index and environment. -/
theorem deriv_neg_on_interval_idx (e : Expr) (hsupp : ADSupported e)
    (ρ_real : Nat → ℝ) (ρ_int : IntervalEnv) (idx : Nat)
    (hρ : ∀ i, ρ_real i ∈ ρ_int i)
    (hneg : (derivInterval e ρ_int idx).hi < 0) :
    ∀ x ∈ ρ_int idx, deriv (Expr.evalAlong e ρ_real idx) x < 0 := by
  intro x hx
  have hmem := derivInterval_correct_idx e hsupp ρ_real ρ_int idx hρ x hx
  simp only [IntervalRat.mem_def] at hmem
  have hhi_cast : ((derivInterval e ρ_int idx).hi : ℝ) < (0 : ℝ) := by exact_mod_cast hneg
  calc deriv (Expr.evalAlong e ρ_real idx) x ≤ ((derivInterval e ρ_int idx).hi : ℝ) := hmem.2
    _ < 0 := hhi_cast

/-- Strictly positive derivative along `idx` implies strict monotonicity.
    Generalized n-variable version. -/
theorem strictMonoOn_of_deriv_pos_interval_idx (e : Expr) (hsupp : ADSupported e)
    (ρ_real : Nat → ℝ) (ρ_int : IntervalEnv) (idx : Nat)
    (hρ : ∀ i, ρ_real i ∈ ρ_int i)
    (hpos : 0 < (derivInterval e ρ_int idx).lo) :
    StrictMonoOn (Expr.evalAlong e ρ_real idx)
      (Set.Icc ((ρ_int idx).lo : ℝ) ((ρ_int idx).hi : ℝ)) := by
  have hdiff := evalAlong_differentiable e hsupp ρ_real idx
  have hderiv_pos := deriv_pos_on_interval_idx e hsupp ρ_real ρ_int idx hρ hpos
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · exact hdiff.continuous.continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    have hx_mem : x ∈ ρ_int idx := by
      simp only [IntervalRat.mem_def]
      exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    exact hderiv_pos x hx_mem

/-- Strictly negative derivative along `idx` implies strict antitonicity.
    Generalized n-variable version. -/
theorem strictAntiOn_of_deriv_neg_interval_idx (e : Expr) (hsupp : ADSupported e)
    (ρ_real : Nat → ℝ) (ρ_int : IntervalEnv) (idx : Nat)
    (hρ : ∀ i, ρ_real i ∈ ρ_int i)
    (hneg : (derivInterval e ρ_int idx).hi < 0) :
    StrictAntiOn (Expr.evalAlong e ρ_real idx)
      (Set.Icc ((ρ_int idx).lo : ℝ) ((ρ_int idx).hi : ℝ)) := by
  have hdiff := evalAlong_differentiable e hsupp ρ_real idx
  have hderiv_neg := deriv_neg_on_interval_idx e hsupp ρ_real ρ_int idx hρ hneg
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · exact hdiff.continuous.continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    have hx_mem : x ∈ ρ_int idx := by
      simp only [IntervalRat.mem_def]
      exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    exact hderiv_neg x hx_mem

/-! ### N-variable monotonicity-based bounds -/

/-- For increasing functions along `idx`, minimum is at the left endpoint.
    Generalized n-variable version. -/
theorem increasing_min_at_left_idx (e : Expr) (hsupp : ADSupported e)
    (ρ_real : Nat → ℝ) (ρ_int : IntervalEnv) (idx : Nat)
    (hρ : ∀ i, ρ_real i ∈ ρ_int i)
    (hpos : 0 < (derivInterval e ρ_int idx).lo) :
    ∀ x ∈ ρ_int idx,
      Expr.evalAlong e ρ_real idx (ρ_int idx).lo ≤ Expr.evalAlong e ρ_real idx x := by
  intro x hx
  have hmono := strictMonoOn_of_deriv_pos_interval_idx e hsupp ρ_real ρ_int idx hρ hpos
  simp only [IntervalRat.mem_def] at hx
  by_cases heq : ((ρ_int idx).lo : ℝ) = x
  · rw [heq]
  · apply le_of_lt
    apply hmono
    · simp only [Set.mem_Icc]
      exact ⟨le_refl _, Rat.cast_le.mpr (ρ_int idx).le⟩
    · simp only [Set.mem_Icc]; exact hx
    · exact lt_of_le_of_ne hx.1 heq

/-- For decreasing functions along `idx`, minimum is at the right endpoint.
    Generalized n-variable version. -/
theorem decreasing_min_at_right_idx (e : Expr) (hsupp : ADSupported e)
    (ρ_real : Nat → ℝ) (ρ_int : IntervalEnv) (idx : Nat)
    (hρ : ∀ i, ρ_real i ∈ ρ_int i)
    (hneg : (derivInterval e ρ_int idx).hi < 0) :
    ∀ x ∈ ρ_int idx,
      Expr.evalAlong e ρ_real idx (ρ_int idx).hi ≤ Expr.evalAlong e ρ_real idx x := by
  intro x hx
  have hmono := strictAntiOn_of_deriv_neg_interval_idx e hsupp ρ_real ρ_int idx hρ hneg
  simp only [IntervalRat.mem_def] at hx
  by_cases heq : x = ((ρ_int idx).hi : ℝ)
  · rw [heq]
  · apply le_of_lt
    apply hmono
    · simp only [Set.mem_Icc]; exact hx
    · simp only [Set.mem_Icc]; exact ⟨(Rat.cast_le.mpr (ρ_int idx).le), le_refl _⟩
    · exact lt_of_le_of_ne hx.2 heq

/-! ### N-variable minimization algorithm -/

/-- Check if derivative interval along `idx` is strictly positive -/
noncomputable def derivStrictlyPositiveIdx (e : Expr) (ρ : IntervalEnv) (idx : Nat) : Bool :=
  let dI := derivInterval e ρ idx
  0 < dI.lo

/-- Check if derivative interval along `idx` is strictly negative -/
noncomputable def derivStrictlyNegativeIdx (e : Expr) (ρ : IntervalEnv) (idx : Nat) : Bool :=
  let dI := derivInterval e ρ idx
  dI.hi < 0

/-- Update an interval environment at a specific index -/
def updateIntervalEnv (ρ : IntervalEnv) (idx : Nat) (J : IntervalRat) : IntervalEnv :=
  fun i => if i = idx then J else ρ i

/-- N-variable branch-and-bound minimization along coordinate `idx`.

Returns an interval [lo, hi] such that for any ρ_real with ρ_real i ∈ ρ i:
- lo ≤ min_{t ∈ ρ idx} evalAlong e ρ_real idx t
- hi ≥ min_{t ∈ ρ idx} evalAlong e ρ_real idx t
-/
@[expose]
noncomputable def minimizeIntervalIdx (e : Expr) (ρ : IntervalEnv) (idx : Nat)
    (maxDepth : ℕ) : OptResult :=
  go (ρ idx) maxDepth
where
  /-- Recursive coordinate minimization with a decreasing subdivision budget. -/
  go (J : IntervalRat) (depth : ℕ) : OptResult :=
    let ρ' := updateIntervalEnv ρ idx J
    if depth = 0 then
      -- Base case: just use interval evaluation
      { valueBound := LeanCert.Internal.Rational.evalUnchecked e ρ'
        argBound := some J
        depth := maxDepth }
    else
      -- Check monotonicity along idx
      if derivStrictlyPositiveIdx e ρ' idx then
        -- f is increasing along idx, minimum is at left endpoint
        let ρ_lo := updateIntervalEnv ρ idx (IntervalRat.singleton J.lo)
        { valueBound := LeanCert.Internal.Rational.evalUnchecked e ρ_lo
          argBound := some (IntervalRat.singleton J.lo)
          depth := maxDepth - depth }
      else if derivStrictlyNegativeIdx e ρ' idx then
        -- f is decreasing along idx, minimum is at right endpoint
        let ρ_hi := updateIntervalEnv ρ idx (IntervalRat.singleton J.hi)
        { valueBound := LeanCert.Internal.Rational.evalUnchecked e ρ_hi
          argBound := some (IntervalRat.singleton J.hi)
          depth := maxDepth - depth }
      else
        -- Bisect and take the better bound
        let (J₁, J₂) := J.bisect
        let r₁ := go J₁ (depth - 1)
        let r₂ := go J₂ (depth - 1)
        OptResult.merge r₁ r₂
  termination_by depth
  decreasing_by all_goals omega

/-! ### N-variable minimization correctness -/

/-- Base case correctness for n-variable optimization.
    Interval evaluation gives a valid lower bound. -/
theorem minimizeIntervalIdx_base_correct (e : Expr) (hsupp : ADSupported e)
    (ρ_int : IntervalEnv) :
    ∀ ρ_real : Nat → ℝ, (∀ i, ρ_real i ∈ ρ_int i) →
      (LeanCert.Internal.Rational.evalUnchecked e ρ_int).lo ≤ Expr.eval ρ_real e := by
  intro ρ_real hρ
  have h := evalInterval_correct e hsupp ρ_real ρ_int hρ
  simp only [IntervalRat.mem_def] at h
  exact h.1

/-- Helper lemma for go correctness in n-variable setting -/
theorem minimizeIntervalIdx_go_correct (e : Expr) (hsupp : ADSupported e)
    (ρ_int : IntervalEnv) (idx : Nat) (maxDepth depth : ℕ) (J : IntervalRat)
    (hJ_sub : ∀ t, t ∈ J → t ∈ ρ_int idx) :
    ∀ ρ_real : Nat → ℝ, (∀ i, ρ_real i ∈ ρ_int i) →
      ∀ t ∈ J,
        (minimizeIntervalIdx.go e ρ_int idx maxDepth J depth).valueBound.lo
          ≤ Expr.eval (Expr.updateVar ρ_real idx t) e := by
  induction depth generalizing J with
  | zero =>
    intro ρ_real hρ t ht
    rw [minimizeIntervalIdx.go]
    simp only [↓reduceIte]
    -- Base case: interval evaluation bounds all points
    have hρ' : ∀ i, (Expr.updateVar ρ_real idx t) i ∈ (updateIntervalEnv ρ_int idx J) i := by
      intro i
      simp only [Expr.updateVar, updateIntervalEnv]
      split_ifs with hi
      · exact ht
      · exact hρ i
    have heval := evalInterval_correct e hsupp (Expr.updateVar ρ_real idx t) (updateIntervalEnv
      ρ_int idx J) hρ'
    simp only [IntervalRat.mem_def] at heval
    exact heval.1
  | succ n ih =>
    intro ρ_real hρ t ht
    have hdepth : n + 1 ≠ 0 := Nat.succ_ne_zero n
    rw [minimizeIntervalIdx.go]
    simp only [hdepth, ↓reduceIte, OptResult.merge, Nat.add_sub_cancel]
    -- Note: ρ' in the go function is updateIntervalEnv ρ_int idx J
    split_ifs with hpos hneg hle
    · -- Derivative strictly positive: increasing function
      -- hpos : derivStrictlyPositiveIdx e (updateIntervalEnv ρ_int idx J) idx = true
      have hpos' : 0 < (derivInterval e (updateIntervalEnv ρ_int idx J) idx).lo := by
        simp only [derivStrictlyPositiveIdx, decide_eq_true_eq] at hpos
        exact hpos
      have hρ_lo : ∀ i, (Expr.updateVar ρ_real idx J.lo) i ∈
          (updateIntervalEnv ρ_int idx (IntervalRat.singleton J.lo)) i := by
        intro i
        simp only [Expr.updateVar, updateIntervalEnv]
        split_ifs with hi
        · exact IntervalRat.mem_singleton _
        · exact hρ i
      have heval := evalInterval_correct e hsupp (Expr.updateVar ρ_real idx J.lo)
        (updateIntervalEnv ρ_int idx (IntervalRat.singleton J.lo)) hρ_lo
      simp only [IntervalRat.mem_def] at heval
      -- Build membership for the derivative bound
      -- We use a modified ρ_real that has J.lo at index idx, since ρ_real idx is never used
      -- in the derivative computation (it gets replaced by the variable of differentiation)
      let ρ_real' := Expr.updateVar ρ_real idx (J.lo : ℝ)
      have hρ'_deriv : ∀ i, ρ_real' i ∈ (updateIntervalEnv ρ_int idx J) i := by
        intro i
        simp only [ρ_real', Expr.updateVar, updateIntervalEnv]
        split_ifs with hi
        · -- At idx: J.lo ∈ J
          simp only [IntervalRat.mem_def, Rat.cast_le]
          exact ⟨le_refl _, J.le⟩
        · exact hρ i
      -- Since evalAlong replaces ρ_real' idx with the variable x, monotonicity for ρ_real'
      -- is the same as for ρ_real
      have hmono' := strictMonoOn_of_deriv_pos_interval_idx e hsupp ρ_real'
        (updateIntervalEnv ρ_int idx J) idx hρ'_deriv hpos'
      -- evalAlong e ρ_real idx = evalAlong e ρ_real' idx because only ρ(idx) differs
      -- and evalAlong replaces it with the function argument
      have heq_along : ∀ x, Expr.evalAlong e ρ_real idx x = Expr.evalAlong e ρ_real' idx x := by
        intro x
        simp only [Expr.evalAlong]
        congr 1
        funext i
        simp only [Expr.updateVar, ρ_real']
        split_ifs with h1
        · rfl  -- i = idx: both give x
        · rfl  -- i ≠ idx: both give ρ_real i
      have hmono : StrictMonoOn (Expr.evalAlong e ρ_real idx)
          (Set.Icc ((updateIntervalEnv ρ_int idx J idx).lo : ℝ)
            ((updateIntervalEnv ρ_int idx J idx).hi : ℝ)) := by
        intro x hx y hy hxy
        rw [heq_along x, heq_along y]
        exact hmono' hx hy hxy
      simp only [IntervalRat.mem_def] at ht
      by_cases heq : (J.lo : ℝ) = t
      · calc (LeanCert.Internal.Rational.evalUnchecked e (updateIntervalEnv ρ_int idx
        (IntervalRat.singleton J.lo))).lo
            ≤ Expr.eval (Expr.updateVar ρ_real idx J.lo) e := heval.1
          _ = Expr.eval (Expr.updateVar ρ_real idx t) e := by rw [← heq]
      · have hlt : (J.lo : ℝ) < t := lt_of_le_of_ne ht.1 heq
        have hJlo_mem : (J.lo : ℝ) ∈ Set.Icc ((updateIntervalEnv ρ_int idx J idx).lo : ℝ)
            ((updateIntervalEnv ρ_int idx J idx).hi) := by
          simp only [Set.mem_Icc, updateIntervalEnv, ↓reduceIte]
          exact ⟨le_refl _, Rat.cast_le.mpr J.le⟩
        have ht_mem : t ∈ Set.Icc ((updateIntervalEnv ρ_int idx J idx).lo : ℝ)
            ((updateIntervalEnv ρ_int idx J idx).hi) := by
          simp only [Set.mem_Icc, updateIntervalEnv, ↓reduceIte]
          exact ht
        have hmono_at := hmono hJlo_mem ht_mem hlt
        simp only [Expr.evalAlong] at hmono_at
        calc (LeanCert.Internal.Rational.evalUnchecked e (updateIntervalEnv ρ_int idx
          (IntervalRat.singleton J.lo))).lo
            ≤ Expr.eval (Expr.updateVar ρ_real idx J.lo) e := heval.1
          _ ≤ Expr.eval (Expr.updateVar ρ_real idx t) e := le_of_lt hmono_at
    · -- Derivative strictly negative: decreasing function
      have hneg' : (derivInterval e (updateIntervalEnv ρ_int idx J) idx).hi < 0 := by
        simp only [derivStrictlyNegativeIdx, decide_eq_true_eq] at hneg
        exact hneg
      have hρ_hi : ∀ i, (Expr.updateVar ρ_real idx J.hi) i ∈
          (updateIntervalEnv ρ_int idx (IntervalRat.singleton J.hi)) i := by
        intro i
        simp only [Expr.updateVar, updateIntervalEnv]
        split_ifs with hi
        · exact IntervalRat.mem_singleton _
        · exact hρ i
      have heval := evalInterval_correct e hsupp (Expr.updateVar ρ_real idx J.hi)
        (updateIntervalEnv ρ_int idx (IntervalRat.singleton J.hi)) hρ_hi
      simp only [IntervalRat.mem_def] at heval
      -- We use a modified ρ_real that has J.hi at index idx
      let ρ_real' := Expr.updateVar ρ_real idx (J.hi : ℝ)
      have hρ'_deriv : ∀ i, ρ_real' i ∈ (updateIntervalEnv ρ_int idx J) i := by
        intro i
        simp only [ρ_real', Expr.updateVar, updateIntervalEnv]
        split_ifs with hi
        · simp only [IntervalRat.mem_def, Rat.cast_le]
          exact ⟨J.le, le_refl _⟩
        · exact hρ i
      have hmono' := strictAntiOn_of_deriv_neg_interval_idx e hsupp ρ_real'
        (updateIntervalEnv ρ_int idx J) idx hρ'_deriv hneg'
      have heq_along : ∀ x, Expr.evalAlong e ρ_real idx x = Expr.evalAlong e ρ_real' idx x := by
        intro x
        simp only [Expr.evalAlong]
        congr 1
        funext i
        simp only [Expr.updateVar, ρ_real']
        split_ifs with h1
        · rfl
        · rfl
      have hmono : StrictAntiOn (Expr.evalAlong e ρ_real idx)
          (Set.Icc ((updateIntervalEnv ρ_int idx J idx).lo : ℝ)
            ((updateIntervalEnv ρ_int idx J idx).hi : ℝ)) := by
        intro x hx y hy hxy
        rw [heq_along x, heq_along y]
        exact hmono' hx hy hxy
      simp only [IntervalRat.mem_def] at ht
      by_cases heq : t = (J.hi : ℝ)
      · calc (LeanCert.Internal.Rational.evalUnchecked e (updateIntervalEnv ρ_int idx
        (IntervalRat.singleton J.hi))).lo
            ≤ Expr.eval (Expr.updateVar ρ_real idx J.hi) e := heval.1
          _ = Expr.eval (Expr.updateVar ρ_real idx t) e := by rw [← heq]
      · have hlt : t < (J.hi : ℝ) := lt_of_le_of_ne ht.2 heq
        have ht_mem : t ∈ Set.Icc ((updateIntervalEnv ρ_int idx J idx).lo : ℝ)
            ((updateIntervalEnv ρ_int idx J idx).hi) := by
          simp only [Set.mem_Icc, updateIntervalEnv, ↓reduceIte]
          exact ht
        have hJhi_mem : (J.hi : ℝ) ∈ Set.Icc ((updateIntervalEnv ρ_int idx J idx).lo : ℝ)
            ((updateIntervalEnv ρ_int idx J idx).hi) := by
          simp only [Set.mem_Icc, updateIntervalEnv, ↓reduceIte]
          exact ⟨Rat.cast_le.mpr J.le, le_refl _⟩
        have hmono_at := hmono ht_mem hJhi_mem hlt
        simp only [Expr.evalAlong] at hmono_at
        calc (LeanCert.Internal.Rational.evalUnchecked e (updateIntervalEnv ρ_int idx
          (IntervalRat.singleton J.hi))).lo
            ≤ Expr.eval (Expr.updateVar ρ_real idx J.hi) e := heval.1
          _ ≤ Expr.eval (Expr.updateVar ρ_real idx t) e := le_of_lt hmono_at
    · -- Bisection case, hle (r₁.lo ≤ r₂.lo)
      have hcases := IntervalRat.mem_bisect_or ht
      cases hcases with
      | inl h1 =>
        have hsub1 : ∀ s, s ∈ J.bisect.1 → s ∈ ρ_int idx := fun s hs =>
          hJ_sub s (IntervalRat.mem_of_mem_bisect_left hs)
        exact ih J.bisect.1 hsub1 ρ_real hρ t h1
      | inr h2 =>
        have hsub2 : ∀ s, s ∈ J.bisect.2 → s ∈ ρ_int idx := fun s hs =>
          hJ_sub s (IntervalRat.mem_of_mem_bisect_right hs)
        have h := ih J.bisect.2 hsub2 ρ_real hρ t h2
        have hle_cast : ((minimizeIntervalIdx.go e ρ_int idx maxDepth (J.bisect.fst)
          n).valueBound.lo : ℝ)
            ≤ (minimizeIntervalIdx.go e ρ_int idx maxDepth (J.bisect.snd) n).valueBound.lo := by
              exact_mod_cast hle
        calc ((minimizeIntervalIdx.go e ρ_int idx maxDepth (J.bisect.fst) n).valueBound.lo : ℝ)
            ≤ (minimizeIntervalIdx.go e ρ_int idx maxDepth (J.bisect.snd) n).valueBound.lo :=
              hle_cast
          _ ≤ Expr.eval (Expr.updateVar ρ_real idx t) e := h
    · -- Bisection case, ¬hle (r₁.lo > r₂.lo)
      have hcases := IntervalRat.mem_bisect_or ht
      cases hcases with
      | inl h1 =>
        have hsub1 : ∀ s, s ∈ J.bisect.1 → s ∈ ρ_int idx := fun s hs =>
          hJ_sub s (IntervalRat.mem_of_mem_bisect_left hs)
        have h := ih J.bisect.1 hsub1 ρ_real hρ t h1
        have hlt := not_le.mp hle
        have hlt_cast : ((minimizeIntervalIdx.go e ρ_int idx maxDepth (J.bisect.snd)
          n).valueBound.lo : ℝ)
            ≤ (minimizeIntervalIdx.go e ρ_int idx maxDepth (J.bisect.fst) n).valueBound.lo := by
          exact_mod_cast (le_of_lt hlt)
        calc ((minimizeIntervalIdx.go e ρ_int idx maxDepth (J.bisect.snd) n).valueBound.lo : ℝ)
            ≤ (minimizeIntervalIdx.go e ρ_int idx maxDepth (J.bisect.fst) n).valueBound.lo :=
              hlt_cast
          _ ≤ Expr.eval (Expr.updateVar ρ_real idx t) e := h
      | inr h2 =>
        have hsub2 : ∀ s, s ∈ J.bisect.2 → s ∈ ρ_int idx := fun s hs =>
          hJ_sub s (IntervalRat.mem_of_mem_bisect_right hs)
        exact ih J.bisect.2 hsub2 ρ_real hρ t h2

/-- Correctness theorem for n-variable minimization:
    For any real environment ρ_real satisfying ρ_int, and any t in ρ_int idx,
    the computed lower bound is valid.

    FULLY PROVED - no sorry, no axioms. -/
theorem minimizeIntervalIdx_correct (e : Expr) (hsupp : ADSupported e)
    (ρ_int : IntervalEnv) (idx : Nat) (maxDepth : ℕ) :
    ∀ ρ_real : Nat → ℝ, (∀ i, ρ_real i ∈ ρ_int i) →
      ∀ t ∈ ρ_int idx,
        (minimizeIntervalIdx e ρ_int idx maxDepth).valueBound.lo
          ≤ Expr.eval (Expr.updateVar ρ_real idx t) e := by
  intro ρ_real hρ t ht
  simp only [minimizeIntervalIdx]
  exact minimizeIntervalIdx_go_correct e hsupp ρ_int idx maxDepth maxDepth (ρ_int idx)
    (fun s hs => hs) ρ_real hρ t ht

/-- N-variable maximization via minimization of negation -/
noncomputable def maximizeIntervalIdx (e : Expr) (ρ : IntervalEnv) (idx : Nat)
    (maxDepth : ℕ) : OptResult :=
  let negResult := minimizeIntervalIdx (Expr.neg e) ρ idx maxDepth
  { valueBound := IntervalRat.neg negResult.valueBound
    argBound := negResult.argBound
    depth := negResult.depth }

/-- Correctness theorem for n-variable maximization -/
theorem maximizeIntervalIdx_correct (e : Expr) (hsupp : ADSupported e)
    (ρ_int : IntervalEnv) (idx : Nat) (maxDepth : ℕ) :
    ∀ ρ_real : Nat → ℝ, (∀ i, ρ_real i ∈ ρ_int i) →
      ∀ t ∈ ρ_int idx,
        Expr.eval (Expr.updateVar ρ_real idx t) e
          ≤ (maximizeIntervalIdx e ρ_int idx maxDepth).valueBound.hi := by
  intro ρ_real hρ t ht
  have hneg_supp : ADSupported (Expr.neg e) := ADSupported.neg hsupp
  have hmin := minimizeIntervalIdx_correct (Expr.neg e) hneg_supp ρ_int idx maxDepth ρ_real hρ t ht
  simp only [Expr.eval_neg] at hmin
  simp only [maximizeIntervalIdx, IntervalRat.neg]
  have h : Expr.eval (Expr.updateVar ρ_real idx t) e ≤
           -(((minimizeIntervalIdx (Expr.neg e) ρ_int idx maxDepth).valueBound.lo) : ℝ) := by
    linarith
  convert h using 1
  simp only [Rat.cast_neg]

end LeanCert.Engine

end

end

section

/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
/-!
# Gradient Interval Computation for Optimization

This file provides functions to compute interval bounds on the gradient ∇f(B)
of an expression over a box B. This is used for monotonicity-based pruning
in branch-and-bound global optimization.

## Main definitions

* `gradientInterval` - Compute interval bounds on all partial derivatives over a box
* `gradientSignature` - Determine the sign of each partial derivative
* `canPruneToLo` / `canPruneToHi` - Check if a coordinate can be pruned by monotonicity

## Design

The gradient is computed by running forward-mode AD (from AD.lean) for each
coordinate direction. The result is a list of intervals, one per variable.

Monotonicity pruning: If ∂f/∂xᵢ > 0 on the entire box B, then f is minimized
when xᵢ = B[i].lo. We can shrink the box in that dimension to a point.
-/

/-! ### Gradient computation -/

public section

namespace LeanCert.Engine.Optimization

open LeanCert.Core
open LeanCert.Engine

/-- Compute the gradient interval: bounds on each partial derivative over a box.
    Returns a list of intervals, where the i-th interval contains ∂f/∂xᵢ for all x ∈ B. -/
noncomputable def gradientInterval (e : Expr) (B : Box) : List IntervalRat :=
  List.ofFn fun (i : Fin B.length) => derivInterval e (Box.toEnv B) i.val

/-- Compute gradient for n variables (explicit dimension) -/
noncomputable def gradientIntervalN (e : Expr) (B : Box) (n : Nat) : List IntervalRat :=
  (List.range n).map fun i => derivInterval e (Box.toEnv B) i

/-! ### Computable versions -/

/-- Create dual environment for differentiating with respect to variable `idx` (computable).
    Active variable gets der = 1, passive variables get der = 0. -/
@[expose]
def mkDualEnvCore (ρ : IntervalEnv) (idx : Nat) : DualEnv :=
  fun i => if i = idx then DualInterval.varActive (ρ i) else DualInterval.varPassive (ρ i)

/-- Evaluate with derivative with respect to variable `idx` (computable version) -/
@[expose]
def evalWithDerivCore (e : Expr) (ρ : IntervalEnv) (idx : Nat) (cfg : EvalConfig := {}) :
  DualInterval :=
  LeanCert.Internal.AD.evalTotalCore e (mkDualEnvCore ρ idx) cfg

/-- Computable derivative interval for multi-variable expressions.
    Computes the interval containing ∂f/∂xᵢ over the box. -/
@[expose]
def derivIntervalCoreN (e : Expr) (ρ : IntervalEnv) (idx : Nat) (cfg : EvalConfig := {}) :
  IntervalRat :=
  (evalWithDerivCore e ρ idx cfg).der

/-- Correctness of the computable derivative evaluator for an arbitrary
coordinate of a multivariate expression. -/
theorem evalDualTotalCore_der_correct_idx (e : Expr) (hsupp : ADSupported e)
    (ρ_real : Nat → ℝ) (ρ_int : IntervalEnv) (idx : Nat)
    (hρ : ∀ i, ρ_real i ∈ ρ_int i) (x : ℝ) (hx : x ∈ ρ_int idx)
    (cfg : EvalConfig) :
    deriv (Expr.evalAlong e ρ_real idx) x ∈
      (LeanCert.Internal.AD.evalTotalCore e (mkDualEnvCore ρ_int idx) cfg).der := by
  have hmem : ∀ i, Expr.updateVar ρ_real idx x i ∈
      (mkDualEnvCore ρ_int idx i).val := by
    simpa only [mkDualEnvCore, mkDualEnv] using
      (updateVar_mem_mkDualEnv_val ρ_real ρ_int idx x hx hρ)
  induction hsupp generalizing x with
  | const q =>
      simp only [Expr.evalAlong_const', deriv_const, LeanCert.Internal.AD.evalTotalCore,
        DualInterval.const]
      exact_mod_cast IntervalRat.mem_singleton 0
  | var i =>
      by_cases hi : i = idx
      · subst i
        simp only [Expr.evalAlong_var_active, LeanCert.Internal.AD.evalTotalCore, mkDualEnvCore,
          ↓reduceIte, DualInterval.varActive, deriv_id]
        exact_mod_cast IntervalRat.mem_singleton 1
      · simp only [Expr.evalAlong_var_passive _ _ _ hi, deriv_const,
        LeanCert.Internal.AD.evalTotalCore,
          mkDualEnvCore, ite_eq_right hi, DualInterval.varPassive]
        exact_mod_cast IntervalRat.mem_singleton 0
  | add h₁ h₂ ih₁ ih₂ =>
      have hd₁ := evalAlong_differentiable _ h₁ ρ_real idx
      have hd₂ := evalAlong_differentiable _ h₂ ρ_real idx
      simp only [Expr.evalAlong_add_pi, deriv_add (hd₁ x) (hd₂ x),
        LeanCert.Internal.AD.evalTotalCore,
        DualInterval.add]
      exact IntervalRat.mem_add (ih₁ x hx hmem) (ih₂ x hx hmem)
  | mul h₁ h₂ ih₁ ih₂ =>
      have hd₁ := evalAlong_differentiable _ h₁ ρ_real idx
      have hd₂ := evalAlong_differentiable _ h₂ ρ_real idx
      simp only [Expr.evalAlong_mul_pi, deriv_mul (hd₁ x) (hd₂ x),
        LeanCert.Internal.AD.evalTotalCore,
        DualInterval.mul]
      have hdom₁ := evalDomainValidDual_of_ExprSupported _ h₁
        (mkDualEnvCore ρ_int idx) cfg
      have hdom₂ := evalDomainValidDual_of_ExprSupported _ h₂
        (mkDualEnvCore ρ_int idx) cfg
      have hval₁ := LeanCert.Engine.evalDualTotalCore_val_correct _ h₁.toCore
        (Expr.updateVar ρ_real idx x) (mkDualEnvCore ρ_int idx) cfg hmem hdom₁
      have hval₂ := LeanCert.Engine.evalDualTotalCore_val_correct _ h₂.toCore
        (Expr.updateVar ρ_real idx x) (mkDualEnvCore ρ_int idx) cfg hmem hdom₂
      exact IntervalRat.mem_add (IntervalRat.mem_mul (ih₁ x hx hmem) hval₂)
        (IntervalRat.mem_mul hval₁ (ih₂ x hx hmem))
  | neg hs ih =>
      have hd := evalAlong_differentiable _ hs ρ_real idx
      simp only [Expr.evalAlong_neg_pi, deriv.neg, LeanCert.Internal.AD.evalTotalCore,
        DualInterval.neg]
      exact IntervalRat.mem_neg (ih x hx hmem)
  | @sin e' hs ih =>
      have hd := evalAlong_differentiable e' hs ρ_real idx
      simp only [Expr.evalAlong_sin, deriv_sin (hd.differentiableAt),
        LeanCert.Internal.AD.evalTotalCore,
        DualInterval.sinCore]
      have hdom := evalDomainValidDual_of_ExprSupported e' hs
        (mkDualEnvCore ρ_int idx) cfg
      have hval := LeanCert.Engine.evalDualTotalCore_val_correct e' hs.toCore
        (Expr.updateVar ρ_real idx x) (mkDualEnvCore ρ_int idx) cfg hmem hdom
      exact IntervalRat.mem_mul
        (IntervalRat.mem_cosComputable hval cfg.taylorDepth) (ih x hx hmem)
  | @cos e' hs ih =>
      have hd := evalAlong_differentiable e' hs ρ_real idx
      simp only [Expr.evalAlong_cos, deriv_cos (hd.differentiableAt),
        LeanCert.Internal.AD.evalTotalCore,
        DualInterval.cosCore]
      have hdom := evalDomainValidDual_of_ExprSupported e' hs
        (mkDualEnvCore ρ_int idx) cfg
      have hval := LeanCert.Engine.evalDualTotalCore_val_correct e' hs.toCore
        (Expr.updateVar ρ_real idx x) (mkDualEnvCore ρ_int idx) cfg hmem hdom
      exact IntervalRat.mem_mul
        (IntervalRat.mem_neg (IntervalRat.mem_sinComputable hval cfg.taylorDepth)) (ih x hx hmem)
  | @exp e' hs ih =>
      have hd := evalAlong_differentiable e' hs ρ_real idx
      simp only [Expr.evalAlong_exp, deriv_exp (hd.differentiableAt),
        LeanCert.Internal.AD.evalTotalCore,
        DualInterval.expCore]
      have hdom := evalDomainValidDual_of_ExprSupported e' hs
        (mkDualEnvCore ρ_int idx) cfg
      have hval := LeanCert.Engine.evalDualTotalCore_val_correct e' hs.toCore
        (Expr.updateVar ρ_real idx x) (mkDualEnvCore ρ_int idx) cfg hmem hdom
      exact IntervalRat.mem_mul
        (IntervalRat.mem_expComputable hval cfg.taylorDepth) (ih x hx hmem)

/-- Computable version of gradient interval for Core expressions.
    This can be used with `native_decide` for verified optimization. -/
def gradientIntervalCore (e : Expr) (B : Box) (cfg : EvalConfig := {}) : List IntervalRat :=
  (List.range B.length).map fun i => derivIntervalCoreN e (Box.toEnv B) i cfg

/-- Compute every partial derivative using the domain-aware checked AD path.
Unlike `gradientIntervalCore`, this rejects unsupported syntax, reciprocal
arguments containing zero, and nonpositive logarithm arguments instead of
returning a finite interval that could be mistaken for a certificate. -/
def gradientIntervalChecked (e : Expr) (B : Box) (cfg : EvalConfig := {}) :
    EvalResult (List IntervalRat) :=
  (List.range B.length).mapM fun i =>
    derivIntervalChecked e (Box.toEnv B) i cfg

private theorem derivIntervalsChecked_correct (e : Expr) (B : Box)
    (cfg : EvalConfig) (ρReal : Nat → ℝ)
    (hρ : ∀ i, ρReal i ∈ Box.toEnv B i) (indices : List Nat)
    (gradient : List IntervalRat)
    (hok : indices.mapM (fun i => derivIntervalChecked e (Box.toEnv B) i cfg) =
      .ok gradient) :
    List.Forall₂ (fun i dI => deriv (Expr.evalAlong e ρReal i) (ρReal i) ∈ dI)
      indices gradient := by
  induction indices generalizing gradient with
  | nil =>
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hok
      subst gradient
      exact .nil
  | cons i indices ih =>
      simp only [List.mapM_cons] at hok
      cases hdi : derivIntervalChecked e (Box.toEnv B) i cfg with
      | error err =>
          rw [hdi] at hok
          simp only [bind, Except.bind] at hok
          cases hok
      | ok dI =>
          rw [hdi] at hok
          simp only [bind, Except.bind] at hok
          cases htail : List.mapM
              (fun j => derivIntervalChecked e (Box.toEnv B) j cfg) indices with
          | error err =>
              rw [htail] at hok
              cases hok
          | ok tail =>
              rw [htail] at hok
              simp only [pure, Except.pure, Except.ok.injEq] at hok
              subst gradient
              exact .cons
                (derivIntervalChecked_correct e ρReal (Box.toEnv B) i cfg dI
                  (ρReal i) (hρ i) hρ hdi)
                (ih tail htail)

/-- Golden soundness theorem for a successfully computed checked gradient.
The output list is aligned with coordinates `0, …, B.length - 1`. -/
theorem gradientIntervalChecked_correct (e : Expr) (B : Box)
    (cfg : EvalConfig) (ρReal : Nat → ℝ)
    (hρ : Box.envMem ρReal B)
    (hzero : ∀ i, i ≥ B.length → ρReal i = 0)
    (gradient : List IntervalRat)
    (hok : gradientIntervalChecked e B cfg = .ok gradient) :
    List.Forall₂ (fun i dI => deriv (Expr.evalAlong e ρReal i) (ρReal i) ∈ dI)
      (List.range B.length) gradient := by
  exact derivIntervalsChecked_correct e B cfg ρReal
    (Box.envMem_toEnv ρReal B hρ hzero) (List.range B.length) gradient hok

/-! ### Sign classification -/

/-- Classification of an interval's sign -/
inductive IntervalSign where
  | positive     -- lo > 0 (strictly positive)
  | negative     -- hi < 0 (strictly negative)
  | nonpositive  -- hi ≤ 0
  | nonnegative  -- lo ≥ 0
  | indefinite   -- contains zero in interior
  deriving Repr, DecidableEq

/-- Classify the sign of an interval -/
def classifySign (I : IntervalRat) : IntervalSign :=
  if I.lo > 0 then .positive
  else if I.hi < 0 then .negative
  else if I.hi ≤ 0 then .nonpositive
  else if I.lo ≥ 0 then .nonnegative
  else .indefinite

/-- The gradient signature: sign of each partial derivative (noncomputable wrapper) -/
noncomputable def gradientSignature (e : Expr) (B : Box) : List IntervalSign :=
  (gradientIntervalN e B B.length).map classifySign

/-! ### Monotonicity predicates -/

/-- Check if interval is strictly positive -/
def isStrictlyPositive (I : IntervalRat) : Bool := I.lo > 0

/-- Check if interval is strictly negative -/
def isStrictlyNegative (I : IntervalRat) : Bool := I.hi < 0

/-- Check if interval is nonnegative -/
def isNonnegative (I : IntervalRat) : Bool := I.lo ≥ 0

/-- Check if interval is nonpositive -/
def isNonpositive (I : IntervalRat) : Bool := I.hi ≤ 0

/-! ### Pruning queries -/

/-- Can we prune coordinate i to its low endpoint for minimization?
    True if ∂f/∂xᵢ > 0 on B (f is increasing in xᵢ, so min is at lo). -/
def canPruneToLo (deriv_i : IntervalRat) : Bool :=
  isStrictlyPositive deriv_i

/-- Can we prune coordinate i to its high endpoint for minimization?
    True if ∂f/∂xᵢ < 0 on B (f is decreasing in xᵢ, so min is at hi). -/
def canPruneToHi (deriv_i : IntervalRat) : Bool :=
  isStrictlyNegative deriv_i

/-- Prune a box for minimization by fixing monotonic coordinates.
    Returns a (potentially smaller) box and a list of fixed coordinates. -/
def pruneBoxForMin (B : Box) (grad : List IntervalRat) : Box × List Nat :=
  let pruned := B.zipIdx.map fun (I, idx) =>
    match grad[idx]? with
    | some di =>
      if canPruneToLo di then
        -- ∂f/∂xᵢ > 0: fix xᵢ = I.lo
        (IntervalRat.singleton I.lo, some idx)
      else if canPruneToHi di then
        -- ∂f/∂xᵢ < 0: fix xᵢ = I.hi
        (IntervalRat.singleton I.hi, some idx)
      else
        (I, none)
    | none => (I, none)
  (pruned.map (·.1), pruned.filterMap (·.2))

/-! ### Correctness theorems -/

/-- The computed gradient interval contains the true partial derivatives.
    This follows from evalDual_der_correct_idx in AD.lean. -/
theorem gradientInterval_correct (e : Expr) (hsupp : ADSupported e)
    (B : Box) (ρ : Nat → ℝ) (hρ : Box.envMem ρ B)
    (hzero : ∀ i, i ≥ B.length → ρ i = 0)
    (i : Fin B.length) :
    deriv (Expr.evalAlong e ρ i.val) (ρ i.val) ∈
      ((gradientIntervalN e B B.length)[i.val]?).getD default := by
  -- The i-th element of gradientIntervalN is derivInterval e (toEnv B) i
  have hget : (gradientIntervalN e B B.length)[i.val]? =
      some (derivInterval e (Box.toEnv B) i.val) := by
    simp only [gradientIntervalN]
    rw [List.getElem?_map]
    simp only [List.getElem?_range i.isLt, Option.map_some]
  simp only [hget, Option.getD]
  -- Apply the AD correctness theorem
  have henv : ∀ j, ρ j ∈ Box.toEnv B j := Box.envMem_toEnv ρ B hρ hzero
  exact derivInterval_correct_idx e hsupp ρ (Box.toEnv B) i.val henv (ρ i.val) (henv i.val)

/-- If we prune a coordinate to lo because ∂f/∂xᵢ > 0, the minimum is preserved.
    Informal: if f is increasing in xᵢ on B, then min{f(x) : x ∈ B} = min{f(x) : xᵢ = B[i].lo}.
    NOTE: Requires ρ j = 0 for j ≥ B.length (standard assumption for box membership). -/
theorem pruneToLo_preserves_min (e : Expr) (hsupp : ADSupported e)
    (B : Box) (i : Fin B.length)
    (hgrad : isStrictlyPositive (derivInterval e (Box.toEnv B) i.val) = true) :
    ∀ (ρ : Nat → ℝ), Box.envMem ρ B → (∀ j, j ≥ B.length → ρ j = 0) →
      ∃ (ρ' : Nat → ℝ), Box.envMem ρ' B ∧ (∀ j, j ≥ B.length → ρ' j = 0) ∧
        ρ' i.val = B[i.val].lo ∧ Expr.eval ρ' e ≤ Expr.eval ρ e := by
  intro ρ hρ hzero
  -- The idea: if ∂f/∂xᵢ > 0 everywhere, then f(ρ) ≥ f(ρ[xᵢ := lo])
  -- We construct ρ' by replacing coordinate i with the low endpoint
  let ρ' : Nat → ℝ := fun j => if j = i.val then (B[i.val].lo : ℝ) else ρ j
  use ρ'
  constructor
  · -- ρ' ∈ B
    intro ⟨j, hj⟩
    by_cases h : j = i.val
    · subst h
      simp only [↓reduceIte, ρ', IntervalRat.mem_def]
      constructor
      · exact le_refl _
      · have := B[i.val].le
        exact_mod_cast this
    · simp only [ite_eq_right h, ρ']
      exact hρ ⟨j, hj⟩
  constructor
  · -- ρ' j = 0 for j ≥ B.length
    intro j hj
    simp only [ρ']
    have hne : j ≠ i.val := by
      intro heq
      rw [heq] at hj
      exact absurd i.isLt (not_lt.mpr hj)
    simp only [ite_eq_right hne]
    exact hzero j hj
  constructor
  · -- ρ' i = B[i].lo
    simp only [↓reduceIte, ρ']
  · -- f(ρ') ≤ f(ρ)
    -- Use the monotonicity theorem: if ∂f/∂xᵢ > 0, minimum is at left endpoint
    -- Convert the boolean condition to a real inequality
    simp only [isStrictlyPositive, decide_eq_true_eq] at hgrad
    -- Build the interval environment from the box
    let ρ_int : IntervalEnv := Box.toEnv B
    -- Show ρ ∈ ρ_int (membership in the interval environment)
    have hρ_int : ∀ j, ρ j ∈ ρ_int j := by
      intro j
      simp only [ρ_int, Box.toEnv, List.getD]
      by_cases hj : j < B.length
      · simp only [List.getElem?_eq_getElem hj, Option.getD]
        exact hρ ⟨j, hj⟩
      · simp only [List.getElem?_eq_none (not_lt.mp hj), Option.getD]
        rw [IntervalRat.mem_default]
        exact hzero j (not_lt.mp hj)
    -- Apply the monotonicity theorem
    have hmono := increasing_min_at_left_idx e hsupp ρ ρ_int i.val hρ_int hgrad
    -- The key fact: ρ i.val ∈ ρ_int i.val = B[i.val]
    have hρ_i_mem : ρ i.val ∈ ρ_int i.val := hρ_int i.val
    have hmin := hmono (ρ i.val) hρ_i_mem
    -- Now relate evalAlong to eval via ρ'
    -- evalAlong e ρ i.val t = eval (updateVar ρ i.val t) e
    simp only [Expr.evalAlong] at hmin
    -- Need: (ρ_int i.val).lo = B[i.val].lo
    have hlo_eq : (ρ_int i.val).lo = B[i.val].lo := by
      simp only [ρ_int, Box.toEnv, List.getD, List.getElem?_eq_getElem i.isLt, Option.getD]
    -- And: updateVar ρ i.val (ρ_int i.val).lo = ρ'
    have hρ'_eq : Expr.updateVar ρ i.val ((ρ_int i.val).lo : ℝ) = ρ' := by
      funext j
      simp only [Expr.updateVar, ρ']
      split_ifs with hj
      · simp only [hlo_eq]
      · rfl
    -- And: updateVar ρ i.val (ρ i.val) = ρ
    have hρ_eq : Expr.updateVar ρ i.val (ρ i.val) = ρ := Expr.updateVar_self ρ i.val
    rw [hρ'_eq, hρ_eq] at hmin
    exact hmin

/-- If we prune a coordinate to hi because ∂f/∂xᵢ < 0, the minimum is preserved.
    NOTE: Requires ρ j = 0 for j ≥ B.length (standard assumption for box membership). -/
theorem pruneToHi_preserves_min (e : Expr) (hsupp : ADSupported e)
    (B : Box) (i : Fin B.length)
    (hgrad : isStrictlyNegative (derivInterval e (Box.toEnv B) i.val) = true) :
    ∀ (ρ : Nat → ℝ), Box.envMem ρ B → (∀ j, j ≥ B.length → ρ j = 0) →
      ∃ (ρ' : Nat → ℝ), Box.envMem ρ' B ∧ (∀ j, j ≥ B.length → ρ' j = 0) ∧
        ρ' i.val = B[i.val].hi ∧ Expr.eval ρ' e ≤ Expr.eval ρ e := by
  intro ρ hρ hzero
  let ρ' : Nat → ℝ := fun j => if j = i.val then (B[i.val].hi : ℝ) else ρ j
  use ρ'
  constructor
  · -- ρ' ∈ B
    intro ⟨j, hj⟩
    by_cases h : j = i.val
    · subst h
      simp only [↓reduceIte, ρ', IntervalRat.mem_def]
      constructor
      · have := B[i.val].le
        exact_mod_cast this
      · exact le_refl _
    · simp only [ite_eq_right h, ρ']
      exact hρ ⟨j, hj⟩
  constructor
  · -- ρ' j = 0 for j ≥ B.length
    intro j hj
    simp only [ρ']
    have hne : j ≠ i.val := by
      intro heq
      rw [heq] at hj
      exact absurd i.isLt (not_lt.mpr hj)
    simp only [ite_eq_right hne]
    exact hzero j hj
  constructor
  · simp only [↓reduceIte, ρ']
  · -- f(ρ') ≤ f(ρ)
    -- Use the monotonicity theorem: if ∂f/∂xᵢ < 0, minimum is at right endpoint
    simp only [isStrictlyNegative, decide_eq_true_eq] at hgrad
    -- Build the interval environment from the box
    let ρ_int : IntervalEnv := Box.toEnv B
    -- Show ρ ∈ ρ_int
    have hρ_int : ∀ j, ρ j ∈ ρ_int j := by
      intro j
      simp only [ρ_int, Box.toEnv, List.getD]
      by_cases hj : j < B.length
      · simp only [List.getElem?_eq_getElem hj, Option.getD]
        exact hρ ⟨j, hj⟩
      · simp only [List.getElem?_eq_none (not_lt.mp hj), Option.getD]
        rw [IntervalRat.mem_default]
        exact hzero j (not_lt.mp hj)
    -- Apply the monotonicity theorem for decreasing functions
    have hmono := decreasing_min_at_right_idx e hsupp ρ ρ_int i.val hρ_int hgrad
    -- The key fact: ρ i.val ∈ ρ_int i.val = B[i.val]
    have hρ_i_mem : ρ i.val ∈ ρ_int i.val := hρ_int i.val
    have hmin := hmono (ρ i.val) hρ_i_mem
    -- Now relate evalAlong to eval via ρ'
    simp only [Expr.evalAlong] at hmin
    -- Need: (ρ_int i.val).hi = B[i.val].hi
    have hhi_eq : (ρ_int i.val).hi = B[i.val].hi := by
      simp only [ρ_int, Box.toEnv, List.getD, List.getElem?_eq_getElem i.isLt, Option.getD]
    -- And: updateVar ρ i.val (ρ_int i.val).hi = ρ'
    have hρ'_eq : Expr.updateVar ρ i.val ((ρ_int i.val).hi : ℝ) = ρ' := by
      funext j
      simp only [Expr.updateVar, ρ']
      split_ifs with hj
      · simp only [hhi_eq]
      · rfl
    -- And: updateVar ρ i.val (ρ i.val) = ρ
    have hρ_eq : Expr.updateVar ρ i.val (ρ i.val) = ρ := Expr.updateVar_self ρ i.val
    rw [hρ'_eq, hρ_eq] at hmin
    exact hmin

/-! ### Pruned box membership and correctness -/

/-- Helper: membership in the pruned box implies membership in the original box.
    The pruned box only shrinks coordinates, never expands them. -/
theorem pruneBoxForMin_subset (B : Box) (grad : List IntervalRat) :
    ∀ ρ, Box.envMem ρ (pruneBoxForMin B grad).1 → Box.envMem ρ B := by
  intro ρ hρ'
  let B' := (pruneBoxForMin B grad).1
  intro ⟨j, hj⟩
  have hj' : j < B'.length := by
    simp only [B', pruneBoxForMin, List.length_map, List.length_zipIdx]
    exact hj
  have hρ'_mem : ρ j ∈ B'[j] := hρ' ⟨j, hj'⟩
  -- Get the j-th element of B'
  simp only [B', pruneBoxForMin] at hρ'_mem
  rw [List.getElem_map, List.getElem_map] at hρ'_mem
  have h_zipIdx_len : j < (B.zipIdx).length := by simp only [List.length_zipIdx]; exact hj
  have h_zipIdx : (B.zipIdx)[j] = (B[j], j) := by
    rw [List.getElem_zipIdx (h := h_zipIdx_len)]
    simp only [Nat.zero_add]
  simp only [h_zipIdx] at hρ'_mem
  -- Now analyze the cases
  cases hgrad_j : grad[j]? with
  | none =>
    simp only [hgrad_j] at hρ'_mem
    exact hρ'_mem
  | some di =>
    simp only [hgrad_j] at hρ'_mem
    by_cases hlo : canPruneToLo di
    · simp only [hlo, ↓reduceIte] at hρ'_mem
      simp only [IntervalRat.mem_def]
      have hρ_eq : ρ j = B[j].lo := by
        simp only [IntervalRat.singleton, IntervalRat.mem_def] at hρ'_mem
        linarith [hρ'_mem.1, hρ'_mem.2]
      rw [hρ_eq]
      exact ⟨le_refl _, by exact_mod_cast B[j].le⟩
    · by_cases hhi : canPruneToHi di
      · simp only [hlo, Bool.false_eq_true, ↓reduceIte, hhi] at hρ'_mem
        simp only [IntervalRat.mem_def]
        have hρ_eq : ρ j = B[j].hi := by
          simp only [IntervalRat.singleton, IntervalRat.mem_def] at hρ'_mem
          linarith [hρ'_mem.1, hρ'_mem.2]
        rw [hρ_eq]
        exact ⟨by exact_mod_cast B[j].le, le_refl _⟩
      · simp only [hlo, Bool.false_eq_true, ↓reduceIte, hhi] at hρ'_mem
        exact hρ'_mem

/-- The pruned box has the same length as the original box -/
theorem pruneBoxForMin_length (B : Box) (grad : List IntervalRat) :
    (pruneBoxForMin B grad).1.length = B.length := by
  simp only [pruneBoxForMin, List.length_map, List.length_zipIdx]

/-- A positive computable derivative enclosure makes the objective increasing
along the selected coordinate. -/
theorem increasing_min_at_left_idx_core (e : Expr) (hsupp : ADSupported e)
    (ρ_real : Nat → ℝ) (ρ_int : IntervalEnv) (idx : Nat)
    (hρ : ∀ i, ρ_real i ∈ ρ_int i) (cfg : EvalConfig)
    (hpos : 0 < (derivIntervalCoreN e ρ_int idx cfg).lo) :
    ∀ x ∈ ρ_int idx,
      Expr.evalAlong e ρ_real idx (ρ_int idx).lo ≤ Expr.evalAlong e ρ_real idx x := by
  have hdiff := evalAlong_differentiable e hsupp ρ_real idx
  have hmono : StrictMonoOn (Expr.evalAlong e ρ_real idx)
      (Set.Icc ((ρ_int idx).lo : ℝ) ((ρ_int idx).hi : ℝ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · exact hdiff.continuous.continuousOn
    · intro x hx
      rw [interior_Icc] at hx
      have hx' : x ∈ ρ_int idx := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
      have hmem := evalDualTotalCore_der_correct_idx e hsupp ρ_real ρ_int idx hρ x hx' cfg
      exact lt_of_lt_of_le (by exact_mod_cast hpos) ((IntervalRat.mem_def _ _).mp hmem).1
  intro x hx
  rcases hx with ⟨hlo, hhi⟩
  by_cases heq : ((ρ_int idx).lo : ℝ) = x
  · exact heq ▸ le_rfl
  · exact le_of_lt (hmono
      ⟨le_rfl, by exact_mod_cast (ρ_int idx).le⟩ ⟨hlo, hhi⟩
      (lt_of_le_of_ne hlo heq))

/-- A negative computable derivative enclosure makes the objective decreasing
along the selected coordinate. -/
theorem decreasing_min_at_right_idx_core (e : Expr) (hsupp : ADSupported e)
    (ρ_real : Nat → ℝ) (ρ_int : IntervalEnv) (idx : Nat)
    (hρ : ∀ i, ρ_real i ∈ ρ_int i) (cfg : EvalConfig)
    (hneg : (derivIntervalCoreN e ρ_int idx cfg).hi < 0) :
    ∀ x ∈ ρ_int idx,
      Expr.evalAlong e ρ_real idx (ρ_int idx).hi ≤ Expr.evalAlong e ρ_real idx x := by
  have hdiff := evalAlong_differentiable e hsupp ρ_real idx
  have hmono : StrictAntiOn (Expr.evalAlong e ρ_real idx)
      (Set.Icc ((ρ_int idx).lo : ℝ) ((ρ_int idx).hi : ℝ)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    · exact hdiff.continuous.continuousOn
    · intro x hx
      rw [interior_Icc] at hx
      have hx' : x ∈ ρ_int idx := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
      have hmem := evalDualTotalCore_der_correct_idx e hsupp ρ_real ρ_int idx hρ x hx' cfg
      exact lt_of_le_of_lt ((IntervalRat.mem_def _ _).mp hmem).2 (by exact_mod_cast hneg)
  intro x hx
  rcases hx with ⟨hlo, hhi⟩
  by_cases heq : x = ((ρ_int idx).hi : ℝ)
  · exact heq ▸ le_rfl
  · exact le_of_lt (hmono ⟨hlo, hhi⟩
      ⟨by exact_mod_cast (ρ_int idx).le, le_rfl⟩
      (lt_of_le_of_ne hhi heq))

/-- **Main correctness theorem for pruneBoxForMin:**

    After pruning, for any point ρ in the original box B, there exists a point ρ'
    in the pruned box B' such that f(ρ') ≤ f(ρ).

    This means the minimum over B can be found by searching only in B'.

    The proof constructs ρ' by moving each coordinate to its endpoint when the
    gradient has a definite sign. For each coordinate:
    - If ∂f/∂xᵢ > 0 on B, move xᵢ to B[i].lo (f is increasing, min at left)
    - If ∂f/∂xᵢ < 0 on B, move xᵢ to B[i].hi (f is decreasing, min at right)
    - Otherwise, keep xᵢ = ρ[i]

    The proof then shows f(ρ') ≤ f(ρ) by induction on coordinates, using
    the monotonicity lemmas `increasing_min_at_left_idx` and `decreasing_min_at_right_idx`.
-/
private def prunePrefixEnvironment (B : Box) (grad : List IntervalRat) (ρ : Nat → ℝ) :
    Nat → (Nat → ℝ) := fun k j =>
  if h : j < k ∧ j < B.length then
    match grad[j]? with
    | some di =>
      if canPruneToLo di then (B[j].lo : ℝ)
      else if canPruneToHi di then (B[j].hi : ℝ)
      else ρ j
    | none => ρ j
  else if hj : j < B.length then ρ j
  else 0

private theorem prunePrefixEnvironment_mem (B : Box) (grad : List IntervalRat)
    (ρ : Nat → ℝ) (m : ℕ)
    (hρB : Box.envMem ρ B)
    : Box.envMem (prunePrefixEnvironment B grad ρ m) B := by
  let ρ_seq := prunePrefixEnvironment B grad ρ
  intro ⟨j, hj⟩
  simp only [prunePrefixEnvironment]
  by_cases h1 : j < m ∧ j < B.length
  · simp only [dite_eq_left h1]
    cases hgrad_j : grad[j]? with
    | none => exact hρB ⟨j, hj⟩
    | some dj =>
      simp only [IntervalRat.mem_def]
      by_cases hlo_j : canPruneToLo dj
      · simp only [hlo_j, ↓reduceIte]
        exact ⟨le_refl _, by exact_mod_cast B[j].le⟩
      · by_cases hhi_j : canPruneToHi dj
        · simp only [hlo_j, Bool.false_eq_true, ↓reduceIte, hhi_j]
          exact ⟨by exact_mod_cast B[j].le, le_refl _⟩
        · simp only [hlo_j, Bool.false_eq_true, ↓reduceIte, hhi_j]
          exact hρB ⟨j, hj⟩
  · simp only [dite_eq_right h1, dite_eq_left hj]
    exact hρB ⟨j, hj⟩

private theorem prunePrefixEnvironment_zero (B : Box) (grad : List IntervalRat)
    (ρ : Nat → ℝ) (m : ℕ)
    : ∀ j, j ≥ B.length → prunePrefixEnvironment B grad ρ m j = 0 := by
  let ρ_seq := prunePrefixEnvironment B grad ρ
  intro j hjge
  simp only [prunePrefixEnvironment]
  have h1 : ¬(j < m ∧ j < B.length) := fun h => absurd h.2 (not_lt.mpr hjge)
  simp only [dite_eq_right h1]
  have h2 : ¬(j < B.length) := not_lt.mpr hjge
  simp only [dite_eq_right h2]

private theorem prunePrefixEnvironment_step (e : Expr) (hsupp : ADSupported e)
    (B : Box) (cfg : EvalConfig) (ρ : Nat → ℝ) (hρB : Box.envMem ρ B) :
    ∀ m < B.length,
      Expr.eval (prunePrefixEnvironment B (gradientIntervalCore e B cfg) ρ (m + 1)) e ≤
        Expr.eval (prunePrefixEnvironment B (gradientIntervalCore e B cfg) ρ m) e := by
  let grad := gradientIntervalCore e B cfg
  let ρ_seq := prunePrefixEnvironment B grad ρ
  have hρ_seq_step : ∀ k j, k ≠ j → ρ_seq k j = ρ_seq (k + 1) j := by
    intro k j hne
    simp only [ρ_seq, prunePrefixEnvironment]
    by_cases h1 : j < k ∧ j < B.length
    · -- j < k and j < B.length: both difs are positive
      have h2 : j < k + 1 ∧ j < B.length := ⟨Nat.lt_of_lt_of_le h1.1 (Nat.le_succ k), h1.2⟩
      simp only [dite_eq_left h1, dite_eq_left h2]
    · by_cases h2 : j < k + 1 ∧ j < B.length
      · -- j < k + 1 but not (j < k ∧ j < B.length)
        have hj_ge_k : k ≤ j := by
          by_contra! hlt
          exact h1 ⟨hlt, h2.2⟩
        have hj_lt_k1 : j < k + 1 := h2.1
        have hj_eq_k : j = k := Nat.eq_of_le_of_lt_succ hj_ge_k hj_lt_k1
        exact absurd hj_eq_k.symm hne
      · -- Neither condition holds
        simp only [dite_eq_right h1, dite_eq_right h2]
  intro m hm
  change Expr.eval (ρ_seq (m + 1)) e ≤ Expr.eval (ρ_seq m) e
  cases hgrad_m : grad[m]? with
  | none =>
    have heq : ∀ j, ρ_seq (m + 1) j = ρ_seq m j := by
      intro j
      by_cases hj_eq : j = m
      · -- When j = m: both sides simplify to ρ m
        simp only [ρ_seq, prunePrefixEnvironment, hgrad_m, hj_eq]
        have h1 : ¬(m < m ∧ m < B.length) := fun h => Nat.lt_irrefl m h.1
        have h2 : m < m + 1 ∧ m < B.length := ⟨Nat.lt_succ_self m, hm⟩
        simp only [dite_eq_right h1, dite_eq_left h2, dite_eq_left hm]
      · exact (hρ_seq_step m j (Ne.symm hj_eq)).symm
    simp only [funext heq]
    exact le_refl _
  | some di =>
    by_cases hlo : canPruneToLo di
    · -- ∂f/∂x_m > 0, fixing x_m = lo decreases f
      have hcoord_m_before : ρ_seq m m = ρ m := by
        simp only [ρ_seq, prunePrefixEnvironment]
        have h1 : ¬(m < m ∧ m < B.length) := fun h => Nat.lt_irrefl m h.1
        simp only [dite_eq_right h1, dite_eq_left hm]
      have hcoord_m_after : ρ_seq (m + 1) m = B[m].lo := by
        simp only [ρ_seq, prunePrefixEnvironment, hgrad_m, hlo, ↓reduceIte]
        have h2 : m < m + 1 ∧ m < B.length := ⟨Nat.lt_succ_self m, hm⟩
        simp only [dite_eq_left h2]
      have hρ_seq_m_mem := prunePrefixEnvironment_mem B grad ρ m hρB
      have hρ_seq_m_zero := prunePrefixEnvironment_zero B grad ρ m
      have hgrad_di : derivIntervalCoreN e (Box.toEnv B) m cfg = di := by
        simp only [grad, gradientIntervalCore] at hgrad_m
        rw [List.getElem?_map, List.getElem?_range hm] at hgrad_m
        simp only [Option.map_some] at hgrad_m
        exact Option.some.inj hgrad_m
      let ρ_int : IntervalEnv := Box.toEnv B
      have hρ_int : ∀ j, ρ_seq m j ∈ ρ_int j := by
        intro j
        simp only [ρ_int, Box.toEnv, List.getD]
        by_cases hj : j < B.length
        · simp only [List.getElem?_eq_getElem hj, Option.getD]
          exact hρ_seq_m_mem ⟨j, hj⟩
        · simp only [List.getElem?_eq_none (not_lt.mp hj), Option.getD]
          rw [IntervalRat.mem_default]
          exact hρ_seq_m_zero j (not_lt.mp hj)
      have hpos : 0 < (derivIntervalCoreN e ρ_int m cfg).lo := by
        simp only [ρ_int]
        rw [hgrad_di]
        simp only [isStrictlyPositive, canPruneToLo] at hlo
        exact decide_eq_true_iff.mp hlo
      have hmono := increasing_min_at_left_idx_core e hsupp (ρ_seq m) ρ_int m
        hρ_int cfg hpos
      have hρ_m_mem : ρ_seq m m ∈ ρ_int m := hρ_int m
      have hmin := hmono (ρ_seq m m) hρ_m_mem
      have hlo_eq : (ρ_int m).lo = B[m].lo := by
        simp only [ρ_int, Box.toEnv, List.getD, List.getElem?_eq_getElem hm, Option.getD]
      simp only [Expr.evalAlong] at hmin
      have hupdate_self : Expr.updateVar (ρ_seq m) m (ρ_seq m m) = ρ_seq m :=
        Expr.updateVar_self (ρ_seq m) m
      have hρ_seq_update : ρ_seq (m + 1) = Expr.updateVar (ρ_seq m) m (B[m].lo : ℝ) := by
        funext j
        simp only [Expr.updateVar]
        by_cases hj_eq : j = m
        · subst hj_eq
          simp only [↓reduceIte]
          exact hcoord_m_after
        · simp only [ite_eq_right hj_eq]
          exact (hρ_seq_step m j (Ne.symm hj_eq)).symm
      have hupdate_lo : Expr.updateVar (ρ_seq m) m ((ρ_int m).lo : ℝ) = ρ_seq (m + 1) := by
        rw [hlo_eq, ← hρ_seq_update]
      rw [hupdate_lo, hupdate_self] at hmin
      exact hmin
    · by_cases hhi : canPruneToHi di
      · -- ∂f/∂x_m < 0, fixing x_m = hi decreases f
        have hcoord_m_before : ρ_seq m m = ρ m := by
          simp only [ρ_seq, prunePrefixEnvironment]
          have h1 : ¬(m < m ∧ m < B.length) := fun h => Nat.lt_irrefl m h.1
          simp only [dite_eq_right h1, dite_eq_left hm]
        have hcoord_m_after : ρ_seq (m + 1) m = B[m].hi := by
          simp only [ρ_seq, prunePrefixEnvironment, hgrad_m, hlo, Bool.false_eq_true,
            ↓reduceIte, hhi]
          have h2 : m < m + 1 ∧ m < B.length := ⟨Nat.lt_succ_self m, hm⟩
          simp only [dite_eq_left h2]
        have hρ_seq_m_mem := prunePrefixEnvironment_mem B grad ρ m hρB
        have hρ_seq_m_zero := prunePrefixEnvironment_zero B grad ρ m
        have hgrad_di : derivIntervalCoreN e (Box.toEnv B) m cfg = di := by
          simp only [grad, gradientIntervalCore] at hgrad_m
          rw [List.getElem?_map, List.getElem?_range hm] at hgrad_m
          simp only [Option.map_some] at hgrad_m
          exact Option.some.inj hgrad_m
        let ρ_int : IntervalEnv := Box.toEnv B
        have hρ_int : ∀ j, ρ_seq m j ∈ ρ_int j := by
          intro j
          simp only [ρ_int, Box.toEnv, List.getD]
          by_cases hj : j < B.length
          · simp only [List.getElem?_eq_getElem hj, Option.getD]
            exact hρ_seq_m_mem ⟨j, hj⟩
          · simp only [List.getElem?_eq_none (not_lt.mp hj), Option.getD]
            rw [IntervalRat.mem_default]
            exact hρ_seq_m_zero j (not_lt.mp hj)
        have hneg : (derivIntervalCoreN e ρ_int m cfg).hi < 0 := by
          simp only [ρ_int]
          rw [hgrad_di]
          simp only [isStrictlyNegative, canPruneToHi] at hhi
          exact decide_eq_true_iff.mp hhi
        have hmono := decreasing_min_at_right_idx_core e hsupp (ρ_seq m) ρ_int m
          hρ_int cfg hneg
        have hρ_m_mem : ρ_seq m m ∈ ρ_int m := hρ_int m
        have hmin := hmono (ρ_seq m m) hρ_m_mem
        have hhi_eq : (ρ_int m).hi = B[m].hi := by
          simp only [ρ_int, Box.toEnv, List.getD, List.getElem?_eq_getElem hm, Option.getD]
        simp only [Expr.evalAlong] at hmin
        have hupdate_self : Expr.updateVar (ρ_seq m) m (ρ_seq m m) = ρ_seq m :=
          Expr.updateVar_self (ρ_seq m) m
        have hρ_seq_update : ρ_seq (m + 1) = Expr.updateVar (ρ_seq m) m (B[m].hi : ℝ) := by
          funext j
          simp only [Expr.updateVar]
          by_cases hj_eq : j = m
          · subst hj_eq
            simp only [↓reduceIte]
            exact hcoord_m_after
          · simp only [ite_eq_right hj_eq]
            exact (hρ_seq_step m j (Ne.symm hj_eq)).symm
        have hupdate_hi : Expr.updateVar (ρ_seq m) m ((ρ_int m).hi : ℝ) = ρ_seq (m + 1) := by
          rw [hhi_eq, ← hρ_seq_update]
        rw [hupdate_hi, hupdate_self] at hmin
        exact hmin
      · -- No pruning at coord m: ρ_seq (m+1) = ρ_seq m at all coords
        have heq : ∀ j, ρ_seq (m + 1) j = ρ_seq m j := by
          intro j
          by_cases hj_eq : j = m
          · -- When j = m: need ρ_seq (m+1) m = ρ_seq m m
            simp only [ρ_seq, prunePrefixEnvironment, hgrad_m, hlo, Bool.false_eq_true,
              ↓reduceIte, hhi, hj_eq]
            have h1 : ¬(m < m ∧ m < B.length) := fun h => Nat.lt_irrefl m h.1
            have h2 : m < m + 1 ∧ m < B.length := ⟨Nat.lt_succ_self m, hm⟩
            simp only [dite_eq_right h1, dite_eq_left h2, dite_eq_left hm]
          · exact (hρ_seq_step m j (Ne.symm hj_eq)).symm
        simp only [funext heq]
        exact le_refl _

theorem pruneBoxForMin_correct (e : Expr) (hsupp : ADSupported e) (B : Box)
    (cfg : EvalConfig := {}) :
    let grad := gradientIntervalCore e B cfg
    let B' := (pruneBoxForMin B grad).1
    ∀ (ρ : Nat → ℝ), Box.envMem ρ B → (∀ i, i ≥ B.length → ρ i = 0) →
      ∃ (ρ' : Nat → ℝ), Box.envMem ρ' B' ∧ (∀ i, i ≥ B'.length → ρ' i = 0) ∧
        Expr.eval ρ' e ≤ Expr.eval ρ e := by
  intro grad B' ρ hρB hzero
  let ρ' : Nat → ℝ := fun j =>
    if h : j < B.length then
      match grad[j]? with
      | some di =>
        if canPruneToLo di then (B[j].lo : ℝ)
        else if canPruneToHi di then (B[j].hi : ℝ)
        else ρ j
      | none => ρ j
    else 0
  use ρ'
  constructor
  · -- ρ' ∈ B'
    intro ⟨j, hj'⟩
    have hB'_len : B'.length = B.length := pruneBoxForMin_length B grad
    have hj : j < B.length := by rw [← hB'_len]; exact hj'
    simp only [ρ', hj, ↓reduceDIte]
    simp only [B', pruneBoxForMin]
    rw [List.getElem_map, List.getElem_map]
    have h_zipIdx_len : j < (B.zipIdx).length := by simp only [List.length_zipIdx]; exact hj
    have h_zipIdx : (B.zipIdx)[j] = (B[j], j) := by
      rw [List.getElem_zipIdx (h := h_zipIdx_len)]
      simp only [Nat.zero_add]
    simp only [h_zipIdx]
    cases hgrad_j : grad[j]? with
    | none =>
      simp only [IntervalRat.mem_def]
      exact hρB ⟨j, hj⟩
    | some di =>
      simp only [IntervalRat.mem_def]
      by_cases hlo : canPruneToLo di
      · simp only [hlo, ↓reduceIte]
        exact IntervalRat.mem_singleton _
      · by_cases hhi : canPruneToHi di
        · simp only [hlo, Bool.false_eq_true, ↓reduceIte, hhi]
          exact IntervalRat.mem_singleton _
        · simp only [hlo, Bool.false_eq_true, ↓reduceIte, hhi]
          exact hρB ⟨j, hj⟩
  constructor
  · -- ρ' i = 0 for i ≥ B'.length
    intro i hi
    have hB'_len : B'.length = B.length := pruneBoxForMin_length B grad
    rw [hB'_len] at hi
    simp only [ρ', not_lt.mpr hi, ↓reduceDIte]
  · -- f(ρ') ≤ f(ρ)
    let ρ_seq := prunePrefixEnvironment B grad ρ
    have hρ_seq_zero : ∀ j, ρ_seq 0 j = if j < B.length then ρ j else 0 := by
      intro j
      simp only [ρ_seq, prunePrefixEnvironment]
      have h_neg : ¬(j < 0 ∧ j < B.length) := fun h => Nat.not_lt_zero j h.1
      simp only [dite_eq_right h_neg]
      split_ifs <;> rfl
    have hρ_seq_final : ∀ j, ρ_seq B.length j = ρ' j := by
      intro j
      simp only [ρ_seq, prunePrefixEnvironment, ρ']
      by_cases hj : j < B.length
      · -- j < B.length
        have h_and : j < B.length ∧ j < B.length := ⟨hj, hj⟩
        simp only [dite_eq_left h_and, dite_eq_left hj]
      · -- j ≥ B.length
        have h_nand : ¬(j < B.length ∧ j < B.length) := fun h => hj h.2
        simp only [dite_eq_right h_nand, dite_eq_right hj]
    have hstep := prunePrefixEnvironment_step e hsupp B cfg ρ hρB
    have hchain : ∀ n ≤ B.length, Expr.eval (ρ_seq n) e ≤ Expr.eval (ρ_seq 0) e := by
      intro n hn
      induction n with
      | zero => exact le_refl _
      | succ m ih =>
        have hm_lt : m < B.length := Nat.lt_of_succ_le hn
        calc Expr.eval (ρ_seq (m + 1)) e ≤ Expr.eval (ρ_seq m) e := hstep m hm_lt
          _ ≤ Expr.eval (ρ_seq 0) e := ih (Nat.le_of_lt hm_lt)
    have hfinal_eq : Expr.eval (ρ_seq B.length) e = Expr.eval ρ' e := by
      congr 1; funext j; exact hρ_seq_final j
    have hρ_seq0_eq : Expr.eval (ρ_seq 0) e = Expr.eval ρ e := by
      congr 1
      funext j
      rw [hρ_seq_zero]
      split_ifs with hj
      · rfl
      · exact (hzero j (not_lt.mp hj)).symm
    rw [← hfinal_eq, ← hρ_seq0_eq]
    exact hchain B.length (le_refl _)

end LeanCert.Engine.Optimization

end

end

section

/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
/-!
# Certified roots of differentiable systems

This module implements a strong, norm-form Krawczyk test for square systems in
LeanCert's `ADSupported` expression fragment. The center and rational
preconditioner are untrusted certificate data;
`krawczykCheck` verifies AD support, center containment, invertibility,
a strict infinity-norm contraction bound, and a strict self-map enclosure.

The golden theorem `krawczykCheck_sound` turns a successful Boolean check into
existence and uniqueness of a real root in the supplied box.
-/

public section

namespace LeanCert.Engine
open LeanCert.Core

/-- Use the singleton zero interval as the additive identity. -/
local instance intervalRatZero : Zero IntervalRat := ⟨IntervalRat.singleton 0⟩
/-- Use endpoint-wise interval addition for finite interval sums. -/
local instance intervalRatAdd : Add IntervalRat := ⟨IntervalRat.add⟩

private theorem intervalRat_ext {a b : IntervalRat} (hlo : a.lo = b.lo) (hhi : a.hi = b.hi) :
    a = b := by
  cases a
  cases b
  simp_all

/-- Natural scalar multiplication by repeated interval addition. -/
local instance : SMul Nat IntervalRat where
  smul n a :=
    { lo := (n : ℚ) * a.lo
      hi := (n : ℚ) * a.hi
      le := mul_le_mul_of_nonneg_left a.le (by positivity) }

/-- The additive commutative monoid of rational intervals. -/
local instance : AddCommMonoid IntervalRat :=
  Function.Injective.addCommMonoid
    (fun I : IntervalRat => (I.lo, I.hi))
    (by intro a b h; exact intervalRat_ext (congrArg Prod.fst h) (congrArg Prod.snd h))
    rfl (fun _ _ => rfl) (fun _ _ => rfl)

/-- Extend a finite real coordinate vector to an expression environment with zero defaults. -/
@[expose]
noncomputable def finEnv {n : Nat} (x : Fin n → ℝ) : Nat → ℝ :=
  fun i => if h : i < n then x ⟨i, h⟩ else 0

/-- Evaluate an expression in the environment of a finite real coordinate vector. -/
@[expose]
noncomputable def evalFin {n : Nat} (e : Expr) (x : Fin n → ℝ) : ℝ :=
  Expr.eval (finEnv x) e

theorem evalFin_differentiable {n : Nat} (e : Expr) (h : ADSupported e) :
    Differentiable ℝ (evalFin (n := n) e) := by
  induction h with
  | const q =>
      rw [show evalFin (n := n) (.const q) = (fun _ : Fin n → ℝ => (q : ℝ)) from rfl]
      exact differentiable_const _
  | var i =>
      by_cases hi : i < n
      · rw [show evalFin (n := n) (.var i) = (fun x : Fin n → ℝ => x ⟨i, hi⟩) by
          funext x; simp [evalFin, finEnv, hi]]
        exact differentiable_apply _
      · rw [show evalFin (n := n) (.var i) = (fun _ : Fin n → ℝ => 0) by
          funext x; simp [evalFin, finEnv, hi]]
        exact differentiable_const _
  | add h₁ h₂ ih₁ ih₂ =>
      rw [show evalFin (n := n) (.add _ _) = evalFin (n := n) _ + evalFin (n := n) _ from rfl]
      exact ih₁.add ih₂
  | mul h₁ h₂ ih₁ ih₂ =>
      rw [show evalFin (n := n) (.mul _ _) = evalFin (n := n) _ * evalFin (n := n) _ from rfl]
      exact ih₁.mul ih₂
  | neg h ih =>
      rw [show evalFin (n := n) (.neg _) = -evalFin (n := n) _ from rfl]
      exact ih.neg
  | sin h ih =>
      rw [show evalFin (n := n) (.sin _) = Real.sin ∘ evalFin (n := n) _ from rfl]
      exact Real.differentiable_sin.comp ih
  | cos h ih =>
      rw [show evalFin (n := n) (.cos _) = Real.cos ∘ evalFin (n := n) _ from rfl]
      exact Real.differentiable_cos.comp ih
  | exp h ih =>
      rw [show evalFin (n := n) (.exp _) = Real.exp ∘ evalFin (n := n) _ from rfl]
      exact Real.differentiable_exp.comp ih

theorem finEnv_update {n : Nat} (x : Fin n → ℝ) (j : Fin n) (t : ℝ) :
    finEnv (Function.update x j t) = Expr.updateVar (finEnv x) j.val t := by
  funext i
  by_cases hi : i < n
  · by_cases hij : i = j.val
    · subst i
      simp [finEnv, Expr.updateVar]
    · have hfin : (⟨i, hi⟩ : Fin n) ≠ j := by
        intro h
        exact hij (Fin.ext_iff.mp h)
      simp [finEnv, Expr.updateVar, hi, hij, hfin]
  · have hij : i ≠ j.val := by omega
    simp [finEnv, Expr.updateVar, hi, hij]

theorem fderiv_single_eq_deriv_evalAlong {n : Nat} (e : Expr) (h : ADSupported e)
    (x : Fin n → ℝ) (j : Fin n) :
    fderiv ℝ (evalFin (n := n) e) x (Pi.single j 1) =
      deriv (Expr.evalAlong e (finEnv x) j.val) (x j) := by
  have hout : HasFDerivAt (evalFin (n := n) e)
      (fderiv ℝ (evalFin (n := n) e) (Function.update x j (x j)))
      (Function.update x j (x j)) :=
    (evalFin_differentiable (n := n) e h).differentiableAt.hasFDerivAt
  have hcomp := hout.comp_hasDerivAt (x j) (hasDerivAt_update x j (x j))
  rw [Function.update_eq_self] at hcomp
  have heq : (evalFin (n := n) e ∘ Function.update x j) =
      Expr.evalAlong e (finEnv x) j.val := by
    funext t
    simp only [Function.comp_apply, evalFin, Expr.evalAlong_eq]
    rw [finEnv_update]
  rw [heq] at hcomp
  exact hcomp.deriv.symm

/-- Evaluate all coordinate expressions of a finite system. -/
@[expose]
noncomputable def systemEval {n : Nat} (F : Fin n → Expr) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => evalFin (F i) x

theorem systemEval_differentiable {n : Nat} (F : Fin n → Expr)
    (h : ∀ i, ADSupported (F i)) : Differentiable ℝ (systemEval F) := by
  rw [differentiable_pi]
  intro i
  exact evalFin_differentiable (F i) (h i)

/-- The matrix of coordinate partial derivatives of an expression system. -/
@[expose]
noncomputable def jacobianAt {n : Nat} (F : Fin n → Expr) (x : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toMatrix' (fderiv ℝ (systemEval F) x).toLinearMap

theorem jacobianAt_apply {n : Nat} (F : Fin n → Expr) (h : ∀ i, ADSupported (F i))
    (x : Fin n → ℝ) (i j : Fin n) :
    jacobianAt F x i j = deriv (Expr.evalAlong (F i) (finEnv x) j.val) (x j) := by
  rw [jacobianAt, LinearMap.toMatrix'_apply]
  change fderiv ℝ (systemEval F) x (Pi.single j 1) i = _
  rw [show systemEval F = (fun x i => evalFin (F i) x) from rfl]
  have hpi := fderiv_pi (𝕜 := ℝ) (x := x)
    (φ := fun i => evalFin (F i)) (fun i => (evalFin_differentiable (F i) (h i)).differentiableAt)
  rw [hpi]
  simp only [ContinuousLinearMap.coe_pi']
  exact fderiv_single_eq_deriv_evalAlong (F i) (h i) x j

/-- Extend a finite interval box to the evaluator’s indexed environment. -/
@[expose]
def finBoxEnv {n : Nat} (X : Fin n → IntervalRat) : IntervalEnv :=
  fun i => if h : i < n then X ⟨i, h⟩ else IntervalRat.singleton 0

/-- Coordinatewise membership of a real vector in a rational interval box. -/
@[expose]
def FinBoxMem {n : Nat} (x : Fin n → ℝ) (X : Fin n → IntervalRat) : Prop :=
  ∀ i, x i ∈ X i

/-- Enclose the Jacobian entries by interval automatic differentiation. -/
@[expose]
def intervalJacobian {n : Nat} (F : Fin n → Expr) (X : Fin n → IntervalRat)
    (cfg : EvalConfig := {}) : Matrix (Fin n) (Fin n) IntervalRat :=
  fun i j => Optimization.derivIntervalCoreN (F i) (finBoxEnv X) j.val cfg

theorem finEnv_mem_finBoxEnv {n : Nat} {x : Fin n → ℝ} {X : Fin n → IntervalRat}
    (hx : FinBoxMem x X) : ∀ i, finEnv x i ∈ finBoxEnv X i := by
  intro i
  by_cases hi : i < n
  · simpa [finEnv, finBoxEnv, hi] using hx ⟨i, hi⟩
  · simpa [finEnv, finBoxEnv, hi] using IntervalRat.mem_singleton 0

theorem jacobianAt_mem_intervalJacobian {n : Nat} (F : Fin n → Expr)
    (h : ∀ i, ADSupported (F i)) (X : Fin n → IntervalRat)
    (x : Fin n → ℝ) (hx : FinBoxMem x X) (cfg : EvalConfig) (i j : Fin n) :
    jacobianAt F x i j ∈ intervalJacobian F X cfg i j := by
  rw [jacobianAt_apply F h x i j]
  exact Optimization.evalDualTotalCore_der_correct_idx (F i) (h i) (finEnv x) (finBoxEnv X)
    j.val (finEnv_mem_finBoxEnv hx) (x j) (by
      simpa only [finBoxEnv, j.isLt, dite_true] using hx j) cfg

/-- Interpret a real matrix as a continuous linear map on finite coordinate vectors. -/
@[expose]
noncomputable def matrixCLM {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.mk (Matrix.mulVecLin A)

/-- The preconditioned Newton map `x ↦ x - Y (F x)`. -/
@[expose]
noncomputable def newtonMap {n : Nat} (Y : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin n → Expr) (x : Fin n → ℝ) : Fin n → ℝ :=
  x - Matrix.mulVec Y (systemEval F x)

theorem newtonMap_differentiable {n : Nat} (Y : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin n → Expr) (h : ∀ i, ADSupported (F i)) :
    Differentiable ℝ (newtonMap Y F) := by
  have hY : Differentiable ℝ (fun x => matrixCLM Y (systemEval F x)) :=
    (matrixCLM Y).differentiable.comp (systemEval_differentiable F h)
  rw [show newtonMap Y F = id - (fun x => matrixCLM Y (systemEval F x)) by
    funext x
    rfl]
  exact differentiable_id.sub hY

theorem newtonMap_fderiv_matrix {n : Nat} (Y : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin n → Expr) (h : ∀ i, ADSupported (F i)) (x : Fin n → ℝ) :
    LinearMap.toMatrix' (fderiv ℝ (newtonMap Y F) x).toLinearMap =
      1 - Y * jacobianAt F x := by
  have hF : HasFDerivAt (systemEval F) (fderiv ℝ (systemEval F) x) x :=
    (systemEval_differentiable F h).differentiableAt.hasFDerivAt
  have hY := (matrixCLM Y).hasFDerivAt.comp x hF
  have hg : HasFDerivAt (newtonMap Y F)
      (ContinuousLinearMap.id ℝ _ - (matrixCLM Y).comp (fderiv ℝ (systemEval F) x)) x := by
    change HasFDerivAt (fun z => z - matrixCLM Y (systemEval F z)) _ x
    exact (hasFDerivAt_id x).sub hY
  rw [hg.fderiv]
  change LinearMap.toMatrix' ((ContinuousLinearMap.id ℝ _ -
    (matrixCLM Y).comp (fderiv ℝ (systemEval F) x)).toLinearMap) = _
  rw [ContinuousLinearMap.toLinearMap_sub]
  change LinearMap.toMatrix' (1 -
    (matrixCLM Y).toLinearMap.comp (fderiv ℝ (systemEval F) x).toLinearMap) = _
  rw [map_sub, LinearMap.toMatrix'_one, LinearMap.toMatrix'_comp]
  have hmatY : LinearMap.toMatrix' (matrixCLM Y).toLinearMap = Y := by
    change LinearMap.toMatrix' (Matrix.mulVecLin Y) = Y
    exact LinearMap.toMatrix'_toLin' Y
  rw [hmatY]
  rfl

/-- The set of real vectors lying coordinatewise in the interval box. -/
@[expose]
def finBoxSet {n : Nat} (X : Fin n → IntervalRat) : Set (Fin n → ℝ) :=
  {x | FinBoxMem x X}

theorem finBoxSet_closed {n : Nat} (X : Fin n → IntervalRat) : IsClosed (finBoxSet X) := by
  have hi : ∀ i : Fin n, IsClosed {x : Fin n → ℝ | x i ∈ X i} := by
    intro i
    exact isClosed_Icc.preimage (continuous_apply i)
  have hinter := isClosed_iInter hi
  have heq : (⋂ i : Fin n, {x : Fin n → ℝ | x i ∈ X i}) = finBoxSet X := by
    ext x
    simp [finBoxSet, FinBoxMem]
  rw [← heq]
  exact hinter

theorem finBoxSet_convex {n : Nat} (X : Fin n → IntervalRat) : Convex ℝ (finBoxSet X) := by
  intro x hx y hy a b ha hb hab i
  simp only [finBoxSet, Set.mem_ofPred_eq, FinBoxMem, IntervalRat.mem_def] at hx hy ⊢
  specialize hx i
  specialize hy i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  constructor
  · calc
      (X i).lo = a * (X i).lo + b * (X i).lo := by
        calc
          ((X i).lo : ℝ) = 1 * (X i).lo := by ring
          _ = (a + b) * (X i).lo := by rw [hab]
          _ = _ := by ring
      _ ≤ a * x i + b * y i := add_le_add
        (mul_le_mul_of_nonneg_left hx.1 ha) (mul_le_mul_of_nonneg_left hy.1 hb)
  · calc
      a * x i + b * y i ≤ a * (X i).hi + b * (X i).hi := add_le_add
        (mul_le_mul_of_nonneg_left hx.2 ha) (mul_le_mul_of_nonneg_left hy.2 hb)
      _ = (X i).hi := by
        calc
          a * (X i).hi + b * (X i).hi = (a + b) * (X i).hi := by ring
          _ = 1 * (X i).hi := by rw [hab]
          _ = _ := by ring

theorem contraction_unique_fixedPoint_in_finBox {n : Nat}
    (X : Fin n → IntervalRat) (m : Fin n → ℝ) (hm : FinBoxMem m X)
    (g : (Fin n → ℝ) → (Fin n → ℝ)) (hmap : Set.MapsTo g (finBoxSet X) (finBoxSet X))
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hdiff : ∀ x ∈ finBoxSet X, DifferentiableAt ℝ g x)
    (hderiv : ∀ x ∈ finBoxSet X, ‖fderiv ℝ g x‖ ≤ q) :
    ∃! x, FinBoxMem x X ∧ g x = x := by
  let K : NNReal := ⟨q, hq0⟩
  have hlipOn : LipschitzOnWith K g (finBoxSet X) := by
    rw [lipschitzOnWith_iff_norm_sub_le]
    intro x hx y hy
    change ‖g x - g y‖ ≤ q * ‖x - y‖
    simpa [norm_sub_rev] using
      (finBoxSet_convex X).norm_image_sub_le_of_norm_fderiv_le hdiff hderiv hy hx
  have hlipRestr : LipschitzWith K (hmap.restrict g (finBoxSet X) (finBoxSet X)) :=
    lipschitzOnWith_iff_restrict.mp hlipOn
  have hcontract : ContractingWith K (hmap.restrict g (finBoxSet X) (finBoxSet X)) := by
    refine ⟨?_, hlipRestr⟩
    exact hq1
  obtain ⟨x, hx, hfix, _⟩ := hcontract.exists_fixedPoint'
    (finBoxSet_closed X).isComplete hmap hm (edist_ne_top m (g m))
  refine ⟨x, ⟨hx, hfix⟩, ?_⟩
  intro y hy
  have hl := (finBoxSet_convex X).norm_image_sub_le_of_norm_fderiv_le
    hdiff hderiv hx hy.1
  rw [hy.2, hfix] at hl
  have hzero : ‖y - x‖ = 0 := by nlinarith [norm_nonneg (y - x)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

open scoped Matrix.Norms.Operator

/-- The identity matrix represented by singleton rational intervals. -/
@[expose]
def intervalIdentity {n : Nat} : Matrix (Fin n) (Fin n) IntervalRat :=
  fun i j => IntervalRat.singleton (if i = j then 1 else 0)

/-- Multiply a rational matrix by an interval matrix using interval sums. -/
@[expose]
def ratMulInterval {n : Nat} (Y : Matrix (Fin n) (Fin n) ℚ)
    (J : Matrix (Fin n) (Fin n) IntervalRat) : Matrix (Fin n) (Fin n) IntervalRat :=
  fun i j => ∑ k, IntervalRat.scale (Y i k) (J k j)

/-- The interval matrix `I - Y J` enclosing the Newton-map derivative. -/
@[expose]
def preconditionedJacobian {n : Nat} (Y : Matrix (Fin n) (Fin n) ℚ)
    (J : Matrix (Fin n) (Fin n) IntervalRat) : Matrix (Fin n) (Fin n) IntervalRat :=
  fun i j => IntervalRat.sub (intervalIdentity i j) (ratMulInterval Y J i j)

theorem mem_interval_sum {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (I : ι → IntervalRat) (h : ∀ i ∈ s, x i ∈ I i) :
    (∑ i ∈ s, x i) ∈ ∑ i ∈ s, I i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      have hz : (0 : IntervalRat) = IntervalRat.singleton 0 :=
        intervalRat_ext rfl rfl
      rw [hz]
      norm_num [IntervalRat.mem_def, IntervalRat.singleton]
  | @insert a s ha ih =>
      simp only [Finset.mem_insert] at h
      simp only [Finset.sum_insert ha]
      exact IntervalRat.mem_add (h a (Or.inl rfl))
        (ih fun i hi => h i (Or.inr hi))

theorem mem_ratMulInterval {n : Nat} (Y : Matrix (Fin n) (Fin n) ℚ)
    (Jreal : Matrix (Fin n) (Fin n) ℝ) (J : Matrix (Fin n) (Fin n) IntervalRat)
    (hJ : ∀ i j, Jreal i j ∈ J i j) (i j : Fin n) :
    (Y.map (fun q => (q : ℝ)) * Jreal) i j ∈ ratMulInterval Y J i j := by
  simp only [Matrix.mul_apply, ratMulInterval]
  exact mem_interval_sum Finset.univ (fun k => (Y i k : ℝ) * Jreal k j)
    (fun k => IntervalRat.scale (Y i k) (J k j)) fun k _ =>
      IntervalRat.mem_scale (Y i k) (hJ k j)

theorem mem_preconditionedJacobian {n : Nat} (Y : Matrix (Fin n) (Fin n) ℚ)
    (Jreal : Matrix (Fin n) (Fin n) ℝ) (J : Matrix (Fin n) (Fin n) IntervalRat)
    (hJ : ∀ i j, Jreal i j ∈ J i j) (i j : Fin n) :
    (1 - Y.map (fun q => (q : ℝ)) * Jreal) i j ∈ preconditionedJacobian Y J i j := by
  apply IntervalRat.mem_sub
  · rw [Matrix.one_apply]
    unfold intervalIdentity
    split
    · norm_num [IntervalRat.mem_def, IntervalRat.singleton]
    · norm_num [IntervalRat.mem_def, IntervalRat.singleton]
  · exact mem_ratMulInterval Y Jreal J hJ i j

/-- The larger absolute endpoint, bounding absolute values in the interval. -/
@[expose]
def intervalAbsBound (I : IntervalRat) : ℚ := max |I.lo| |I.hi|

/-- The sum of absolute interval bounds in a selected matrix row. -/
@[expose]
def intervalMatrixRowBound {n : Nat} (A : Matrix (Fin n) (Fin n) IntervalRat)
    (i : Fin n) : ℚ := ∑ j, intervalAbsBound (A i j)

/-- The maximum interval row sum, bounding the matrix’s sup-norm operator norm. -/
@[expose]
def intervalMatrixBound {n : Nat} (A : Matrix (Fin n) (Fin n) IntervalRat) : ℚ :=
  (List.ofFn fun i => intervalMatrixRowBound A i).foldl max 0

theorem abs_le_intervalAbsBound {x : ℝ} {I : IntervalRat} (hx : x ∈ I) :
    |x| ≤ intervalAbsBound I := by
  rw [abs_le]
  constructor
  · have hlo : ((I.lo : ℚ) : ℝ) ≤ x := hx.1
    have habs : -|(I.lo : ℝ)| ≤ (I.lo : ℝ) := neg_abs_le _
    have hmax : |(I.lo : ℝ)| ≤ (intervalAbsBound I : ℝ) := by
      exact_mod_cast le_max_left |I.lo| |I.hi|
    linarith [neg_le_neg hmax]
  · have hhi : x ≤ ((I.hi : ℚ) : ℝ) := hx.2
    have habs : (I.hi : ℝ) ≤ |(I.hi : ℝ)| := le_abs_self _
    have hmax : |(I.hi : ℝ)| ≤ (intervalAbsBound I : ℝ) := by
      exact_mod_cast le_max_right |I.lo| |I.hi|
    linarith

private theorem le_foldl_max (xs : List ℚ) (a : ℚ) : a ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      exact le_trans (le_max_left _ _) (ih _)

private theorem foldl_max_mono {xs : List ℚ} {a b : ℚ} (hab : a ≤ b) :
    xs.foldl max a ≤ xs.foldl max b := by
  induction xs generalizing a b with
  | nil => simpa using hab
  | cons x xs ih =>
      simp only [List.foldl_cons]
      exact ih (max_le_max_right x hab)

private theorem le_foldl_max_of_mem {x : ℚ} {xs : List ℚ} (hx : x ∈ xs) :
    x ≤ xs.foldl max 0 := by
  induction xs with
  | nil => simp at hx
  | cons a as ih =>
      simp only [List.mem_cons] at hx
      simp only [List.foldl_cons]
      rcases hx with rfl | hx
      · exact le_trans (le_max_right _ _) (le_foldl_max as _)
      · exact le_trans (ih hx) (foldl_max_mono (le_max_left 0 a))

theorem intervalMatrixRowBound_le_bound {n : Nat} (A : Matrix (Fin n) (Fin n) IntervalRat)
    (i : Fin n) : intervalMatrixRowBound A i ≤ intervalMatrixBound A := by
  apply le_foldl_max_of_mem
  exact List.mem_ofFn.mpr ⟨i, rfl⟩

theorem matrix_norm_le_intervalMatrixBound {n : Nat}
    (R : Matrix (Fin n) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) IntervalRat)
    (hmem : ∀ i j, R i j ∈ A i j) :
    ‖R‖ ≤ (intervalMatrixBound A : ℝ) := by
  rw [Matrix.linfty_opNorm_def]
  have hbound0 : 0 ≤ intervalMatrixBound A := le_foldl_max _ 0
  let Q : NNReal := ⟨intervalMatrixBound A, by exact_mod_cast hbound0⟩
  change (↑((Finset.univ : Finset (Fin n)).sup fun i => ∑ j, ‖R i j‖₊) : ℝ) ≤ ↑Q
  apply NNReal.coe_le_coe.mpr
  refine Finset.sup_le fun i _ => ?_
  apply NNReal.coe_le_coe.mp
  simp only [NNReal.coe_sum, coe_nnnorm]
  change (∑ j, |R i j|) ≤ (intervalMatrixBound A : ℝ)
  calc
    (∑ j, |R i j|) ≤ ∑ j, (intervalAbsBound (A i j) : ℝ) :=
      Finset.sum_le_sum fun j _ => abs_le_intervalAbsBound (hmem i j)
    _ = (intervalMatrixRowBound A i : ℝ) := by
      simp [intervalMatrixRowBound]
    _ ≤ (intervalMatrixBound A : ℝ) := by
      exact_mod_cast intervalMatrixRowBound_le_bound A i

theorem newtonMap_fderiv_norm_le {n : Nat} (Y : Matrix (Fin n) (Fin n) ℚ)
    (F : Fin n → Expr) (h : ∀ i, ADSupported (F i)) (X : Fin n → IntervalRat)
    (x : Fin n → ℝ) (hx : FinBoxMem x X) (cfg : EvalConfig) :
    ‖fderiv ℝ (newtonMap (Y.map fun q => (q : ℝ)) F) x‖ ≤
      (intervalMatrixBound (preconditionedJacobian Y (intervalJacobian F X cfg)) : ℝ) := by
  rw [← Matrix.linfty_opNorm_toMatrix]
  rw [newtonMap_fderiv_matrix (Y.map fun q => (q : ℝ)) F h x]
  apply matrix_norm_le_intervalMatrixBound
  exact mem_preconditionedJacobian Y (jacobianAt F x) (intervalJacobian F X cfg)
    (jacobianAt_mem_intervalJacobian F h X x hx cfg)

/-- Represent a rational center by singleton intervals in the evaluation environment. -/
@[expose]
def pointIntervalEnv {n : Nat} (m : Fin n → ℚ) : IntervalEnv :=
  fun i => if h : i < n then IntervalRat.singleton (m ⟨i, h⟩) else IntervalRat.singleton 0

/-- Enclose the expression system at a rational center by interval evaluation. -/
def pointEvalIntervals {n : Nat} (F : Fin n → Expr) (m : Fin n → ℚ)
    (cfg : EvalConfig := {}) : Fin n → IntervalRat :=
  fun i => LeanCert.Internal.Rational.evalTotalCore (F i) (pointIntervalEnv m) cfg

/-- Multiply a rational matrix by an interval vector. -/
def intervalRatMatVec {n : Nat} (Y : Matrix (Fin n) (Fin n) ℚ)
    (v : Fin n → IntervalRat) : Fin n → IntervalRat :=
  fun i => ∑ j, IntervalRat.scale (Y i j) (v j)

/-- An interval enclosure of the preconditioned Newton map at the chosen center. -/
def newtonCenterInterval {n : Nat} (F : Fin n → Expr) (m : Fin n → ℚ)
    (Y : Matrix (Fin n) (Fin n) ℚ) (cfg : EvalConfig := {}) : Fin n → IntervalRat :=
  fun i => IntervalRat.sub (IntervalRat.singleton (m i))
    (intervalRatMatVec Y (pointEvalIntervals F m cfg) i)

theorem finEnv_ratCast_mem_pointIntervalEnv {n : Nat} (m : Fin n → ℚ) :
    ∀ i, finEnv (fun j => (m j : ℝ)) i ∈ pointIntervalEnv m i := by
  intro i
  by_cases hi : i < n
  · simpa [finEnv, pointIntervalEnv, hi] using IntervalRat.mem_singleton (m ⟨i, hi⟩)
  · simpa [finEnv, pointIntervalEnv, hi] using IntervalRat.mem_singleton 0

theorem systemEval_mem_pointEvalIntervals {n : Nat} (F : Fin n → Expr)
    (h : ∀ i, ADSupported (F i)) (m : Fin n → ℚ) (cfg : EvalConfig) (i : Fin n) :
    systemEval F (fun j => (m j : ℝ)) i ∈ pointEvalIntervals F m cfg i := by
  exact evalIntervalCore_correct (F i) (h i).toCore _ _
    (finEnv_ratCast_mem_pointIntervalEnv m) cfg
    (LeanCert.Engine.ADSupported.domainValid (h i) _ cfg)

theorem newtonMap_center_mem {n : Nat} (F : Fin n → Expr)
    (h : ∀ i, ADSupported (F i)) (m : Fin n → ℚ)
    (Y : Matrix (Fin n) (Fin n) ℚ) (cfg : EvalConfig) (i : Fin n) :
    newtonMap (Y.map fun q => (q : ℝ)) F (fun j => (m j : ℝ)) i ∈
      newtonCenterInterval F m Y cfg i := by
  apply IntervalRat.mem_sub
  · exact IntervalRat.mem_singleton (m i)
  · simp only [Matrix.mulVec, dotProduct, intervalRatMatVec]
    exact mem_interval_sum Finset.univ
      (fun j => (Y i j : ℝ) * systemEval F (fun k => (m k : ℝ)) j)
      (fun j => IntervalRat.scale (Y i j) (pointEvalIntervals F m cfg j))
      (fun j _ => IntervalRat.mem_scale (Y i j)
        (systemEval_mem_pointEvalIntervals F h m cfg j))

/-- The greater endpoint distance from the center in a selected coordinate. -/
@[expose]
def coordinateRadius {n : Nat} (X : Fin n → IntervalRat) (m : Fin n → ℚ)
    (i : Fin n) : ℚ := max (m i - (X i).lo) ((X i).hi - m i)

/-- The maximum coordinate radius of the box around the chosen center. -/
@[expose]
def boxRadius {n : Nat} (X : Fin n → IntervalRat) (m : Fin n → ℚ) : ℚ :=
  (List.ofFn fun i => coordinateRadius X m i).foldl max 0

theorem coordinateRadius_le_boxRadius {n : Nat} (X : Fin n → IntervalRat)
    (m : Fin n → ℚ) (i : Fin n) : coordinateRadius X m i ≤ boxRadius X m := by
  apply le_foldl_max_of_mem
  exact List.mem_ofFn.mpr ⟨i, rfl⟩

theorem abs_sub_center_le_coordinateRadius {n : Nat} {X : Fin n → IntervalRat}
    {m : Fin n → ℚ} {x : Fin n → ℝ} (hx : FinBoxMem x X) (i : Fin n) :
    |x i - (m i : ℝ)| ≤ coordinateRadius X m i := by
  rw [abs_le]
  constructor
  · have hlo := (hx i).1
    have hmax : m i - (X i).lo ≤ coordinateRadius X m i := le_max_left _ _
    have hmaxR : ((m i - (X i).lo : ℚ) : ℝ) ≤ (coordinateRadius X m i : ℝ) :=
      by exact_mod_cast hmax
    push_cast at hmaxR
    linarith
  · have hhi := (hx i).2
    have hmax : (X i).hi - m i ≤ coordinateRadius X m i := le_max_right _ _
    have hmaxR : (((X i).hi - m i : ℚ) : ℝ) ≤ (coordinateRadius X m i : ℝ) :=
      by exact_mod_cast hmax
    push_cast at hmaxR
    linarith

theorem boxRadius_nonneg {n : Nat} (X : Fin n → IntervalRat) (m : Fin n → ℚ) :
    0 ≤ boxRadius X m := le_foldl_max _ 0

theorem norm_sub_center_le_boxRadius {n : Nat} {X : Fin n → IntervalRat}
    {m : Fin n → ℚ} {x : Fin n → ℝ} (hx : FinBoxMem x X) :
    ‖x - (fun i => (m i : ℝ))‖ ≤ (boxRadius X m : ℝ) := by
  rw [pi_norm_le_iff_of_nonneg]
  · intro i
    rw [Real.norm_eq_abs]
    exact (abs_sub_center_le_coordinateRadius hx i).trans
      (by exact_mod_cast coordinateRadius_le_boxRadius X m i)
  · exact_mod_cast boxRadius_nonneg X m

/-- The rational interval with endpoints `-d` and `d`. -/
@[expose]
def symmetricInterval (d : ℚ) : IntervalRat :=
  { lo := -|d|
    hi := |d|
    le := neg_nonpos.mpr (abs_nonneg d) |>.trans (abs_nonneg d) }

/-- Enclose the Newton image using its center value and a uniform derivative bound. -/
def newtonImageEnclosure {n : Nat} (F : Fin n → Expr) (X : Fin n → IntervalRat)
    (m : Fin n → ℚ) (Y : Matrix (Fin n) (Fin n) ℚ) (cfg : EvalConfig := {}) :
    Fin n → IntervalRat :=
  let q := intervalMatrixBound (preconditionedJacobian Y (intervalJacobian F X cfg))
  let r := boxRadius X m
  fun i => IntervalRat.add (newtonCenterInterval F m Y cfg i) (symmetricInterval (q * r))

/-- Test whether both endpoints lie strictly inside another interval. -/
@[expose]
def intervalStrictInside (I X : IntervalRat) : Bool := X.lo < I.lo && I.hi < X.hi

theorem intervalStrictInside_sound {I X : IntervalRat} (h : intervalStrictInside I X = true) :
    ∀ x : ℝ, x ∈ I → x ∈ X := by
  intro x hx
  simp only [intervalStrictInside, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨le_trans (by exact_mod_cast h.1.le) hx.1, le_trans hx.2 (by exact_mod_cast h.2.le)⟩

theorem newtonMap_mapsTo_of_imageEnclosure {n : Nat} (F : Fin n → Expr)
    (h : ∀ i, ADSupported (F i)) (X : Fin n → IntervalRat) (m : Fin n → ℚ)
    (hm : FinBoxMem (fun i => (m i : ℝ)) X) (Y : Matrix (Fin n) (Fin n) ℚ)
    (cfg : EvalConfig)
    (hencl : ∀ i, intervalStrictInside (newtonImageEnclosure F X m Y cfg i) (X i) = true) :
    Set.MapsTo (newtonMap (Y.map fun q => (q : ℝ)) F) (finBoxSet X) (finBoxSet X) := by
  intro x hx i
  let q : ℚ := intervalMatrixBound (preconditionedJacobian Y (intervalJacobian F X cfg))
  let mr : Fin n → ℝ := fun i => (m i : ℝ)
  have hdiff : ‖newtonMap (Y.map fun q => (q : ℝ)) F x -
      newtonMap (Y.map fun q => (q : ℝ)) F mr‖ ≤ (q : ℝ) * ‖x - mr‖ := by
    apply (finBoxSet_convex X).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
    · intro z hz
      exact (newtonMap_differentiable (Y.map fun q => (q : ℝ)) F h).differentiableAt
    · intro z hz
      exact newtonMap_fderiv_norm_le Y F h X z hz cfg
    · exact hm
    · exact hx
  have hq0 : 0 ≤ q := le_foldl_max _ 0
  have hr0 : 0 ≤ boxRadius X m := boxRadius_nonneg X m
  have hnorm : ‖newtonMap (Y.map fun q => (q : ℝ)) F x -
      newtonMap (Y.map fun q => (q : ℝ)) F mr‖ ≤
      ((q * boxRadius X m : ℚ) : ℝ) := by
    calc
      _ ≤ (q : ℝ) * ‖x - mr‖ := hdiff
      _ ≤ (q : ℝ) * (boxRadius X m : ℝ) :=
        mul_le_mul_of_nonneg_left (norm_sub_center_le_boxRadius hx) (by exact_mod_cast hq0)
      _ = _ := by push_cast; rfl
  have hcoord : |(newtonMap (Y.map fun q => (q : ℝ)) F x -
      newtonMap (Y.map fun q => (q : ℝ)) F mr) i| ≤
      ((q * boxRadius X m : ℚ) : ℝ) :=
    (norm_le_pi_norm _ i).trans hnorm
  have herr : (newtonMap (Y.map fun q => (q : ℝ)) F x -
      newtonMap (Y.map fun q => (q : ℝ)) F mr) i ∈
      symmetricInterval (q * boxRadius X m) := by
    rw [abs_le] at hcoord
    simpa [symmetricInterval, IntervalRat.mem_def, abs_of_nonneg (mul_nonneg hq0 hr0)] using hcoord
  have hcenter := newtonMap_center_mem F h m Y cfg i
  have himage : newtonMap (Y.map fun q => (q : ℝ)) F x i ∈
      newtonImageEnclosure F X m Y cfg i := by
    have hadd := IntervalRat.mem_add hcenter herr
    simpa [newtonImageEnclosure, q, mr, Pi.sub_apply] using hadd
  exact intervalStrictInside_sound (hencl i) _ himage

/-- Rational center and preconditioner data for a checkable Krawczyk certificate. -/
structure KrawczykCert (n : Nat) where
  /-- The rational center used by the Newton-image enclosure. -/
  center : Fin n → ℚ
  /-- The rational matrix used to precondition the equation system. -/
  preconditioner : Matrix (Fin n) (Fin n) ℚ

/-- Coordinatewise containment of the rational center in the interval box. -/
@[expose]
def centerInside {n : Nat} (X : Fin n → IntervalRat) (m : Fin n → ℚ) : Prop :=
  ∀ i, (X i).lo ≤ m i ∧ m i ≤ (X i).hi

instance {n : Nat} (X : Fin n → IntervalRat) (m : Fin n → ℚ) :
    Decidable (centerInside X m) := by
  unfold centerInside
  infer_instance

/-- Check supported derivatives, center containment, invertibility, contraction and self-map
bounds. -/
def krawczykCheck {n : Nat} (F : Fin n → Expr) (X : Fin n → IntervalRat)
    (cert : KrawczykCert n) (cfg : EvalConfig := {}) : Bool :=
  decide (∀ i, (F i).checkADSupported = true) &&
  decide (centerInside X cert.center) &&
  decide (cert.preconditioner.det ≠ 0) &&
  decide (intervalMatrixBound
    (preconditionedJacobian cert.preconditioner (intervalJacobian F X cfg)) < 1) &&
  decide (∀ i, intervalStrictInside
    (newtonImageEnclosure F X cert.center cert.preconditioner cfg i) (X i) = true)

/-- Every expression in the finite system evaluates to zero at the given point. -/
@[expose]
def SystemZero {n : Nat} (F : Fin n → Expr) (x : Fin n → ℝ) : Prop :=
  ∀ i, evalFin (F i) x = 0

theorem centerInside_sound {n : Nat} {X : Fin n → IntervalRat} {m : Fin n → ℚ}
    (h : centerInside X m) : FinBoxMem (fun i => (m i : ℝ)) X := by
  intro i
  constructor
  · change ((X i).lo : ℝ) ≤ (m i : ℝ)
    exact_mod_cast (h i).1
  · change (m i : ℝ) ≤ ((X i).hi : ℝ)
    exact_mod_cast (h i).2

theorem fixedPoint_iff_systemZero {n : Nat} (F : Fin n → Expr)
    (Y : Matrix (Fin n) (Fin n) ℚ) (hdet : Y.det ≠ 0) (x : Fin n → ℝ) :
    newtonMap (Y.map fun q => (q : ℝ)) F x = x ↔ SystemZero F x := by
  let Yr : Matrix (Fin n) (Fin n) ℝ := Y.map fun q => (q : ℝ)
  have hdetR : Yr.det ≠ 0 := by
    simp only [Yr]
    exact_mod_cast hdet
  have hinj : Function.Injective Yr.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      (Yr.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hdetR))
  constructor
  · intro hfix
    have hmul : Yr.mulVec (systemEval F x) = 0 := by
      funext i
      have hi := congrFun hfix i
      change x i - Yr.mulVec (systemEval F x) i = x i at hi
      exact sub_eq_self.mp hi
    have hz : systemEval F x = 0 := hinj (by simpa using hmul)
    intro i
    exact congrFun hz i
  · intro hz
    have hs : systemEval F x = 0 := by
      funext i
      exact hz i
    funext i
    simp [newtonMap, hs]

theorem krawczykCheck_sound {n : Nat} (F : Fin n → Expr) (X : Fin n → IntervalRat)
    (cert : KrawczykCert n) (cfg : EvalConfig)
    (hcheck : krawczykCheck F X cert cfg = true) :
    ∃! x, FinBoxMem x X ∧ SystemZero F x := by
  simp only [krawczykCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  rcases hcheck with ⟨⟨⟨⟨hsupported, hcenter⟩, hdet⟩, hq⟩, hencl⟩
  have hsupp : ∀ i, ADSupported (F i) := fun i =>
    ((F i).checkADSupported_eq_true_iff).mp (hsupported i)
  let q : ℚ := intervalMatrixBound
    (preconditionedJacobian cert.preconditioner (intervalJacobian F X cfg))
  have hq0 : 0 ≤ q := le_foldl_max _ 0
  have hfixed := contraction_unique_fixedPoint_in_finBox X
    (fun i => (cert.center i : ℝ)) (centerInside_sound hcenter)
    (newtonMap (cert.preconditioner.map fun q => (q : ℝ)) F)
    (newtonMap_mapsTo_of_imageEnclosure F hsupp X cert.center
      (centerInside_sound hcenter) cert.preconditioner cfg hencl)
    (q : ℝ) (by exact_mod_cast hq0) (by exact_mod_cast hq)
    (fun x _ => (newtonMap_differentiable
      (cert.preconditioner.map fun q => (q : ℝ)) F hsupp).differentiableAt)
    (fun x hx => newtonMap_fderiv_norm_le cert.preconditioner F hsupp X x hx cfg)
  refine ⟨hfixed.choose, ⟨hfixed.choose_spec.1.1,
    (fixedPoint_iff_systemZero F cert.preconditioner hdet hfixed.choose).mp
      hfixed.choose_spec.1.2⟩, ?_⟩
  intro y hy
  exact hfixed.unique ⟨hy.1,
    (fixedPoint_iff_systemZero F cert.preconditioner hdet y).mpr hy.2⟩
    hfixed.choose_spec.1

end LeanCert.Engine

end

end
