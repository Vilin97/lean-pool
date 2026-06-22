/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/

import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Hermite Functions and Nuclear Structure of Schwartz Space

Hermite functions ψₙ(x) = cₙ · Hₙ(x) · exp(-x²/2) form an orthonormal basis
of L²(ℝ) that also lies in Schwartz space 𝓢(ℝ). The Schwartz seminorm
‖ψₙ‖_{k,m} grows polynomially in n, making the inclusion maps between
Sobolev-Hermite levels Hilbert-Schmidt (and their compositions trace-class).

This file provides:
- Definitions of Hermite functions (1D and multi-dimensional)
- Key properties as axioms (L² orthonormality, Schwartz membership, seminorm bounds)
- These properties are sufficient to prove `schwartz_nuclear` (in DyninMityagin.lean)

The polynomial infrastructure is available in
  ../auto1/lean/SpecialFunctions/Hermite/Basic.lean
(probabilist's Hermite polynomials with full algebraic proofs).

## References

- Reed-Simon, "Methods of Modern Mathematical Physics" Vol. 1, §V.3
- Folland, "Harmonic Analysis in Phase Space", Ch. 1
- Thangavelu, "Lectures on Hermite and Laguerre Expansions"
- DLMF Chapter 18 (Orthogonal Polynomials)
-/

open MeasureTheory Polynomial Real
open scoped ContDiff

noncomputable section

/-! ## Hermite Functions (1D)

The n-th Hermite function is:
  ψₙ(x) = (n! √π)^{-1/2} · Hₙ(x√2) · exp(-x²/2)
where Hₙ is the probabilist's Hermite polynomial (Mathlib's `hermite n`),
evaluated at x√2 to give the standard physicist's normalization.

This is equivalent to the physicist's convention:
  ψₙ(x) = (2ⁿ n! √π)^{-1/2} · Heₙ(x) · exp(-x²/2)
where Heₙ(x) = 2^{n/2} Hₙ(x√2) is the physicist's Hermite polynomial.

Key properties:
1. {ψₙ} forms an ONB of L²(ℝ)
2. Each ψₙ ∈ 𝓢(ℝ, ℝ) (Schwartz function)
3. ψₙ is an eigenfunction of the Fourier transform: ℱψₙ = (-i)ⁿ ψₙ
4. ψₙ is an eigenfunction of the harmonic oscillator: (-d²/dx² + x²)ψₙ = (2n+1)ψₙ
-/

/-- Normalization constant for the n-th Hermite function:
    cₙ = (n! · √π)^{-1/2}
-/
def hermiteFunctionNormConst (n : ℕ) : ℝ :=
  Real.sqrt ((n.factorial * Real.sqrt Real.pi)⁻¹)

/-- The n-th Hermite function ψₙ(x) = cₙ · Hₙ(x√2) · exp(-x²/2)
    where Hₙ is the probabilist's Hermite polynomial evaluated at x√2.
-/
def hermiteFunction (n : ℕ) (x : ℝ) : ℝ :=
  hermiteFunctionNormConst n *
  ((hermite n).map (Int.castRingHom ℝ)).eval (x * Real.sqrt 2) *
  Real.exp (-(x ^ 2) / 2)

/-! ## Key Properties (axioms — to be proved from Gaussian integral theory)

These are standard results from harmonic analysis. Proofs require:
- Gaussian integration: ∫ x^k exp(-x²) dx (partially in Mathlib)
- Recurrence-based orthogonality
- Schwartz space membership via polynomial bounds on derivatives

The polynomial algebraic infrastructure is available in auto1/lean/SpecialFunctions/Hermite/.
-/

/-- Hermite functions are continuous. -/
private lemma continuous_hermiteFunction (n : ℕ) : Continuous (hermiteFunction n) := by
  unfold hermiteFunction hermiteFunctionNormConst
  fun_prop

/-- |x|^k * exp(-b*x²) ≤ k! * exp(1/(2b)) for all x, using Taylor + completing the square. -/
private lemma pow_mul_exp_neg_le (k : ℕ) {b : ℝ} (hb : 0 < b) (x : ℝ) :
    |x| ^ k * Real.exp (-b * x ^ 2) ≤ ↑k.factorial * Real.exp (1 / (2 * b)) := by
  have hpow : |x| ^ k ≤ ↑k.factorial * Real.exp (|x|) := by
    have hfact_pos : (0 : ℝ) < ↑k.factorial := Nat.cast_pos.mpr k.factorial_pos
    have h : |x| ^ k / ↑k.factorial ≤ Real.exp (|x|) := le_trans
      (Finset.single_le_sum
        (fun i (_ : i ∈ Finset.range (k + 1)) =>
          div_nonneg (pow_nonneg (abs_nonneg x) i) (Nat.cast_nonneg' (i.factorial)))
        (Finset.mem_range.mpr (by omega) : k ∈ Finset.range (k + 1)))
      (Real.sum_le_exp_of_nonneg (abs_nonneg x) (k + 1))
    rwa [div_le_iff₀ hfact_pos, mul_comm] at h
  have hquad : |x| ≤ b / 2 * x ^ 2 + 1 / (2 * b) := by
    have heq : b / 2 * x ^ 2 + 1 / (2 * b) = (b ^ 2 * x ^ 2 + 1) / (2 * b) := by field_simp
    rw [heq, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * b)]
    nlinarith [sq_abs x, sq_nonneg (b * |x| - 1)]
  calc |x| ^ k * Real.exp (-b * x ^ 2)
      ≤ |x| ^ k * Real.exp (-(b / 2) * x ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg (abs_nonneg x) k)
        exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg x])
    _ ≤ ↑k.factorial * Real.exp (|x|) * Real.exp (-(b / 2) * x ^ 2) :=
        mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = ↑k.factorial * (Real.exp (|x|) * Real.exp (-(b / 2) * x ^ 2)) := by ring
    _ = ↑k.factorial * Real.exp (|x| + -(b / 2) * x ^ 2) := by rw [← Real.exp_add]
    _ ≤ ↑k.factorial * Real.exp (1 / (2 * b)) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg' _)
        exact Real.exp_le_exp.mpr (by linarith)

/-- Monomial times Gaussian is integrable: ∫ |x^k · exp(-b·x²)| dx < ∞.
    Uses the bound |x|^k ≤ k! · exp(|x|) (from Taylor series of exp) and
    |x| ≤ (b/2)·x² + 1/(2b) (completing the square) to get
    |x^k · exp(-b·x²)| ≤ k!·exp(1/(2b)) · exp(-(b/2)·x²).
-/
private lemma integrable_pow_mul_exp_neg_mul_sq (k : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : ℝ => x ^ k * Real.exp (-b * x ^ 2)) volume := by
  have hcont : Continuous (fun x : ℝ => x ^ k * Real.exp (-b * x ^ 2)) := by fun_prop
  set C : ℝ := ↑k.factorial * Real.exp (1 / (2 * b))
  refine Integrable.mono' ((integrable_exp_neg_mul_sq (half_pos hb)).const_mul C)
    hcont.aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
  -- Goal: |x|^k * exp(-b*x²) ≤ C * exp(-(b/2)*x²)
  -- Step 1: |x|^k ≤ k! * exp(|x|) from Taylor bound
  have hpow : |x| ^ k ≤ ↑k.factorial * Real.exp (|x|) := by
    have hfact_pos : (0 : ℝ) < ↑k.factorial := Nat.cast_pos.mpr k.factorial_pos
    have h : |x| ^ k / ↑k.factorial ≤ Real.exp (|x|) := le_trans
      (Finset.single_le_sum
        (fun i (_ : i ∈ Finset.range (k + 1)) =>
          div_nonneg (pow_nonneg (abs_nonneg x) i) (Nat.cast_nonneg' (i.factorial)))
        (Finset.mem_range.mpr (by omega) : k ∈ Finset.range (k + 1)))
      (Real.sum_le_exp_of_nonneg (abs_nonneg x) (k + 1))
    rwa [div_le_iff₀ hfact_pos, mul_comm] at h
  -- Step 2: |x| ≤ (b/2)·x² + 1/(2b) by completing the square
  have hquad : |x| ≤ b / 2 * x ^ 2 + 1 / (2 * b) := by
    have heq : b / 2 * x ^ 2 + 1 / (2 * b) = (b ^ 2 * x ^ 2 + 1) / (2 * b) := by
      field_simp
    rw [heq, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * b)]
    nlinarith [sq_abs x, sq_nonneg (b * |x| - 1)]
  -- Step 3: Factor exp(-b·x²) = exp(-(b/2)·x²) · exp(-(b/2)·x²) and combine
  have hfactor : Real.exp (-b * x ^ 2) =
      Real.exp (-(b / 2) * x ^ 2) * Real.exp (-(b / 2) * x ^ 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hfactor, show |x| ^ k * (Real.exp (-(b / 2) * x ^ 2) * Real.exp (-(b / 2) * x ^ 2)) =
    (|x| ^ k * Real.exp (-(b / 2) * x ^ 2)) * Real.exp (-(b / 2) * x ^ 2) from by ring]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  calc |x| ^ k * Real.exp (-(b / 2) * x ^ 2)
      ≤ ↑k.factorial * Real.exp (|x|) * Real.exp (-(b / 2) * x ^ 2) :=
        mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = ↑k.factorial * (Real.exp (|x|) * Real.exp (-(b / 2) * x ^ 2)) := by ring
    _ = ↑k.factorial * Real.exp (|x| + -(b / 2) * x ^ 2) := by
        rw [← Real.exp_add]
    _ ≤ ↑k.factorial * Real.exp (1 / (2 * b)) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg' _)
        exact Real.exp_le_exp.mpr (by linarith)

/-- For any polynomial p and b > 0, the function x ↦ p(x) · exp(-b·x²) is integrable.
    Proved by polynomial induction, reducing to monomial integrability.
-/
private lemma integrable_eval_mul_exp_neg_mul_sq (p : ℝ[X]) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : ℝ => p.eval x * Real.exp (-b * x ^ 2)) volume := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have : (fun x : ℝ => (p + q).eval x * Real.exp (-b * x ^ 2)) =
           (fun x => p.eval x * Real.exp (-b * x ^ 2)) +
           (fun x => q.eval x * Real.exp (-b * x ^ 2)) := by
      ext x; simp [Polynomial.eval_add, add_mul]
    rw [this]; exact hp.add hq
  | monomial k a =>
    simp only [Polynomial.eval_monomial]
    change Integrable (fun x : ℝ => a * x ^ k * Real.exp (-b * x ^ 2)) volume
    have heq : (fun x : ℝ => a * x ^ k * Real.exp (-b * x ^ 2)) =
               fun x => a * (x ^ k * Real.exp (-b * x ^ 2)) := by ext x; ring
    rw [heq]
    exact (integrable_pow_mul_exp_neg_mul_sq k hb).const_mul a

/-- For any polynomial P and b > 0, |P(x) * exp(-b*x²)| is uniformly bounded. -/
private lemma polynomial_eval_mul_exp_neg_bound (P : ℝ[X]) {b : ℝ} (hb : 0 < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |P.eval x * Real.exp (-b * x ^ 2)| ≤ C := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨Cp, hCp, hp⟩ := hp
    obtain ⟨Cq, hCq, hq⟩ := hq
    exact ⟨Cp + Cq, add_nonneg hCp hCq, fun x => by
      simp only [Polynomial.eval_add, add_mul]
      exact (abs_add_le _ _).trans (add_le_add (hp x) (hq x))⟩
  | monomial k a =>
    refine ⟨|a| * (↑k.factorial * Real.exp (1 / (2 * b))), by positivity, fun x => ?_⟩
    simp only [Polynomial.eval_monomial]
    rw [show a * x ^ k * Real.exp (-b * x ^ 2) =
      a * (x ^ k * Real.exp (-b * x ^ 2)) from by ring, abs_mul,
      show |x ^ k * Real.exp (-b * x ^ 2)| =
        |x| ^ k * Real.exp (-b * x ^ 2) from by
          rw [abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]]
    exact mul_le_mul_of_nonneg_left (pow_mul_exp_neg_le k hb x) (abs_nonneg a)

/-- Hermite functions are square-integrable. -/
theorem hermiteFunction_memLp (n : ℕ) :
    MemLp (hermiteFunction n) 2 MeasureTheory.volume := by
  have hcont := continuous_hermiteFunction n
  rw [← integrable_norm_rpow_iff hcont.aestronglyMeasurable two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat]
  -- Reduce to showing (hermiteFunction n)² is integrable (npow, avoiding rpow headaches)
  suffices h : Integrable (fun x : ℝ => (hermiteFunction n x) ^ 2) volume by
    exact h.congr (by
      filter_upwards with x
      rw [Real.norm_eq_abs]
      simp [sq_abs])
  -- Express (hermiteFunction n x)² as c² · (Q·Q)(x) · exp(-x²)
  -- where Q = (hermiteR n) ∘ (√2 · X), so Q(x) = Hₙ(x√2)
  set P := (hermite n).map (Int.castRingHom ℝ) with hP_def
  set c := hermiteFunctionNormConst n with hc_def
  set Q := P.comp (C (Real.sqrt 2) * X) with hQ_def
  have hQeval : ∀ x : ℝ, Q.eval x = P.eval (x * Real.sqrt 2) := by
    intro x; simp only [hQ_def, Polynomial.eval_comp, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]; congr 1; ring
  have h_eq : (fun x : ℝ => (hermiteFunction n x) ^ 2) =
              fun x => c ^ 2 * ((Q * Q).eval x * Real.exp (-1 * x ^ 2)) := by
    ext x
    unfold hermiteFunction
    simp only [← hc_def, ← hP_def, Polynomial.eval_mul, ← hQeval]
    have hexp : Real.exp (-(x ^ 2) / 2) * Real.exp (-(x ^ 2) / 2) = Real.exp (-1 * x ^ 2) := by
      rw [← Real.exp_add]; congr 1; ring
    calc (c * Q.eval x * Real.exp (-(x ^ 2) / 2)) ^ 2
        = c ^ 2 * Q.eval x ^ 2 *
          (Real.exp (-(x ^ 2) / 2) * Real.exp (-(x ^ 2) / 2)) := by ring
      _ = c ^ 2 * Q.eval x ^ 2 * Real.exp (-1 * x ^ 2) := by rw [hexp]
      _ = c ^ 2 * (Q.eval x * Q.eval x * Real.exp (-1 * x ^ 2)) := by ring
  rw [h_eq]
  exact (integrable_eval_mul_exp_neg_mul_sq (Q * Q) one_pos).const_mul (c ^ 2)

/-! ## Orthonormality proof infrastructure

We prove `hermiteFunction_orthonormal` via the IBP recurrence for
`J(n, m) = ∫ Hₙ(x) · Hₘ(x) · exp(-x²/2) dx`, where Hₙ = `hermite n` (probabilist's).
Key identity: `J(n, m+1) = n · J(n-1, m)`, giving `J(n,m) = δₙₘ · n! · √(2π)`.
-/

/-- Abbreviation: Hermite polynomial evaluated over ℝ. -/
abbrev hermiteR (n : ℕ) : ℝ[X] := (hermite n).map (Int.castRingHom ℝ)

/-- The derivative of the (n+1)-th Hermite polynomial is (n+1) times the n-th.
    Adapted from auto1's `probHermite_derivative`.
-/
theorem hermite_derivative (n : ℕ) :
    derivative (hermite (n + 1)) = (↑(n + 1) : ℤ[X]) * hermite n := by
  induction n with
  | zero => simp [hermite_succ, hermite_zero]
  | succ n ih =>
    change derivative (X * hermite (n + 1) - derivative (hermite (n + 1)))
        = (↑(n + 2) : ℤ[X]) * hermite (n + 1)
    rw [map_sub, derivative_mul, derivative_X, one_mul]
    simp only [ih]
    rw [derivative_mul, derivative_natCast, zero_mul, zero_add]
    have step : hermite (n + 1) + X * ((↑(n + 1) : ℤ[X]) * hermite n) -
        (↑(n + 1) : ℤ[X]) * derivative (hermite n) =
        hermite (n + 1) +
        (↑(n + 1) : ℤ[X]) * (X * hermite n - derivative (hermite n)) := by ring
    rw [step, ← hermite_succ,
        show (↑(n + 2) : ℤ[X]) = 1 + ↑(n + 1) from by push_cast; ring]
    ring

/-- Derivative of Hermite polynomial over ℝ. -/
private theorem hermiteR_derivative (n : ℕ) :
    derivative (hermiteR (n + 1)) = (↑(n + 1) : ℝ[X]) * hermiteR n := by
  simp only [hermiteR]
  rw [Polynomial.derivative_map, hermite_derivative, Polynomial.map_mul, Polynomial.map_natCast]

/-- The unnormalized Gaussian weight `exp(-x²/2)` (no `1/√(2π)` factor). -/
abbrev gaussian (x : ℝ) : ℝ := Real.exp (-(x ^ 2 / 2))

/-- Derivative of `Hₘ(x) · exp(-x²/2)` equals `-H_{m+1}(x) · exp(-x²/2)`.
    From `H_{m+1} = X·Hₘ - Hₘ'` and the product rule.
-/
private theorem deriv_hermiteEval_mul_gaussian (m : ℕ) (x : ℝ) :
    deriv (fun u => (hermiteR m).eval u * gaussian u) x =
    -((hermiteR (m + 1)).eval x) * gaussian x := by
  have hdiff_exp : DifferentiableAt ℝ (fun u : ℝ => Real.exp (-(u ^ 2 / 2))) x :=
    DifferentiableAt.exp (by fun_prop)
  have hd := deriv_fun_mul (hermiteR m).differentiable.differentiableAt hdiff_exp
  rw [hd]
  -- Convert deriv of polynomial eval via aeval
  have hpoly : deriv (fun u => (hermiteR m).eval u) x = (derivative (hermiteR m)).eval x := by
    have h1 : (fun u => (hermiteR m).eval u) = fun u => Polynomial.aeval u (hermiteR m) := by
      ext u; simp [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_id]
    rw [h1, Polynomial.deriv_aeval]
    simp [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_id]
  rw [hpoly]
  have hexp : deriv (fun u : ℝ => Real.exp (-(u ^ 2 / 2))) x = -x * gaussian x := by
    have h1 : HasDerivAt (fun u : ℝ => -(u ^ 2 / 2)) (-x) x := by
      have := ((hasDerivAt_pow 2 x).div_const 2).neg
      have hf : (fun u : ℝ => -(u ^ 2 / 2)) = -fun x => x ^ 2 / 2 := by ext u; simp
      have hv : (-x : ℝ) = -(↑2 * x ^ (2 - 1) / 2) := by norm_num
      rw [hf, hv]; exact this
    exact h1.exp.deriv.trans (mul_comm _ _)
  rw [hexp]
  -- Hermite recurrence: H_{m+1}(x) = x · Hₘ(x) - Hₘ'(x)
  have hrec : (hermiteR (m + 1)).eval x = x * (hermiteR m).eval x - (derivative (hermiteR m)).eval
    x := by
    have h1 : hermiteR (m + 1) = X * hermiteR m - derivative (hermiteR m) := by
      unfold hermiteR
      rw [hermite_succ, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_X,
        Polynomial.derivative_map]
    rw [h1]; simp [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X]
  rw [hrec]; ring

/-- Polynomial times `exp(-x²/2)` is integrable, via
`integrable_eval_mul_exp_neg_mul_sq`. -/
private theorem integrable_hermiteR_mul_gaussian (p : ℝ[X]) :
    Integrable (fun x : ℝ => p.eval x * gaussian x) volume := by
  have h : (fun x : ℝ => p.eval x * gaussian x) =
      fun x => p.eval x * Real.exp (-(1 / 2) * x ^ 2) := by
    ext x; change p.eval x * Real.exp (-(x ^ 2 / 2)) = _; congr 1; congr 1; ring
  rw [h]
  exact integrable_eval_mul_exp_neg_mul_sq p (by positivity : (0 : ℝ) < 1 / 2)

/-- Product of two Hermite polynomials times `exp(-x²/2)` is integrable. -/
private theorem integrable_hermiteProd_mul_gaussian (n m : ℕ) :
    Integrable (fun x : ℝ => (hermiteR n).eval x * (hermiteR m).eval x * gaussian x) volume := by
  have h : (fun x : ℝ => (hermiteR n).eval x * (hermiteR m).eval x * gaussian x) =
      fun x => (hermiteR n * hermiteR m).eval x * gaussian x := by
    ext x; simp [Polynomial.eval_mul, mul_assoc]
  rw [h]
  exact integrable_hermiteR_mul_gaussian (hermiteR n * hermiteR m)

/-- `fun x => Hₙ(x) * (-H_{m+1}(x) * exp(-x²/2))` is integrable. -/
private theorem integrable_hermite_mul_neg_hermite_gaussian (n m : ℕ) :
    Integrable (fun x : ℝ => (hermiteR n).eval x *
      (-(hermiteR (m + 1)).eval x * gaussian x)) volume := by
  have h : (fun x : ℝ => (hermiteR n).eval x * (-(hermiteR (m + 1)).eval x * gaussian x)) =
      fun x => -((hermiteR n * hermiteR (m + 1)).eval x * gaussian x) := by
    ext x; simp [Polynomial.eval_mul]; ring
  rw [h]
  exact (integrable_hermiteR_mul_gaussian (hermiteR n * hermiteR (m + 1))).neg

/-- `Hₘ(x) · exp(-x²/2)` is differentiable. -/
private theorem differentiable_hermiteEval_mul_gaussian (m : ℕ) :
    Differentiable ℝ (fun u => (hermiteR m).eval u * gaussian u) :=
  (hermiteR m).differentiable.mul
    (Differentiable.exp (by fun_prop : Differentiable ℝ (fun u : ℝ => -(u ^ 2 / 2))))

/-- The `J` integral: `∫ Hₙ(x) · Hₘ(x) · exp(-x²/2) dx`. -/
noncomputable def J (n m : ℕ) : ℝ :=
  ∫ x, (hermiteR n).eval x * ((hermiteR m).eval x * gaussian x)

/-- IBP recurrence: `J(n+1, m+1) = (n+1) · J(n, m)`. -/
private theorem J_succ_succ (n m : ℕ) : J (n + 1) (m + 1) = (↑(n + 1) : ℝ) * J n m := by
  unfold J
  -- We use IBP: ∫ f * g' = -∫ f' * g
  -- with f(x) = Hₙ₊₁(x) (polynomial) and g(x) = Hₘ(x)·exp(-x²/2)
  -- g'(x) = -H_{m+1}(x)·exp(-x²/2) (Step 2)
  -- f'(x) = (n+1)·Hₙ(x) (hermite_derivative)
  -- Set up: J(n+1, m+1) = ∫ Hₙ₊₁ · Hₘ₊₁ · G = -∫ Hₙ₊₁ · (d/dx[Hₘ·G])
  have hJ : ∫ x, (hermiteR (n + 1)).eval x * ((hermiteR (m + 1)).eval x * gaussian x) =
      -∫ x, (hermiteR (n + 1)).eval x *
        (deriv (fun u => (hermiteR m).eval u * gaussian u) x) := by
    have h_eq : ∀ x : ℝ, (hermiteR (n + 1)).eval x * ((hermiteR (m + 1)).eval x * gaussian x) =
        -((hermiteR (n + 1)).eval x *
          deriv (fun u => (hermiteR m).eval u * gaussian u) x) := by
      intro x; rw [deriv_hermiteEval_mul_gaussian]; ring
    simp_rw [h_eq, integral_neg]
  rw [hJ]
  -- Apply IBP with v = 1
  have h_int_fderiv_g : Integrable
      (fun x => fderiv ℝ (fun x => (hermiteR (n + 1)).eval x) x 1 *
        ((hermiteR m).eval x * gaussian x)) volume := by
    have : (fun x => fderiv ℝ (fun x => (hermiteR (n + 1)).eval x) x 1 *
        ((hermiteR m).eval x * gaussian x)) =
        fun x => ((↑(n + 1) : ℝ) * (hermiteR n).eval x) *
          ((hermiteR m).eval x * gaussian x) := by
      ext x
      rw [fderiv_apply_one_eq_deriv, Polynomial.deriv, hermiteR_derivative]
      simp [Polynomial.eval_mul, Polynomial.eval_natCast]
    rw [this]
    have : (fun x => ((↑(n + 1) : ℝ) * (hermiteR n).eval x) *
        ((hermiteR m).eval x * gaussian x)) =
        fun x => (↑(n + 1) : ℝ) *
          ((hermiteR n).eval x * (hermiteR m).eval x * gaussian x) := by
      ext x; ring
    rw [this]
    exact (integrable_hermiteProd_mul_gaussian n m).const_mul _
  have h_int_f_gderiv : Integrable
      (fun x => (hermiteR (n + 1)).eval x *
        (fderiv ℝ (fun u => (hermiteR m).eval u * gaussian u) x 1)) volume := by
    have : (fun x => (hermiteR (n + 1)).eval x *
        (fderiv ℝ (fun u => (hermiteR m).eval u * gaussian u) x 1)) =
        fun x => (hermiteR (n + 1)).eval x *
          deriv (fun u => (hermiteR m).eval u * gaussian u) x := by
      ext x; rw [fderiv_apply_one_eq_deriv]
    rw [this]
    have : (fun x => (hermiteR (n + 1)).eval x *
        deriv (fun u => (hermiteR m).eval u * gaussian u) x) =
        fun x => (hermiteR (n + 1)).eval x *
          (-(hermiteR (m + 1)).eval x * gaussian x) := by
      ext x; rw [deriv_hermiteEval_mul_gaussian]
    rw [this]
    exact integrable_hermite_mul_neg_hermite_gaussian (n + 1) m
  have h_int_f_g : Integrable
      (fun x => (hermiteR (n + 1)).eval x * ((hermiteR m).eval x * gaussian x))
      volume := by
    exact (integrable_hermiteProd_mul_gaussian (n + 1) m).congr
      (by filter_upwards; intro x; ring)
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (𝕜 := ℝ) (E := ℝ)
    (μ := volume)
    (f := fun x => (hermiteR (n + 1)).eval x)
    (g := fun u => (hermiteR m).eval u * gaussian u)
    (v := (1 : ℝ))
    h_int_fderiv_g h_int_f_gderiv h_int_f_g
    (fun x _ => (hermiteR (n + 1)).differentiable.differentiableAt)
    (fun x _ => (differentiable_hermiteEval_mul_gaussian m).differentiableAt)
  -- IBP gives: ∫ f * g' = -∫ f' * g
  -- So -∫ f * g' = ∫ f' * g
  simp only [fderiv_apply_one_eq_deriv] at hibp
  rw [neg_eq_iff_eq_neg.mpr hibp]
  -- Simplify deriv of polynomial and factor out constant
  have h_rw : ∀ x : ℝ, deriv (fun x => (hermiteR (n + 1)).eval x) x *
      ((hermiteR m).eval x * gaussian x) =
      (↑(n + 1) : ℝ) * ((hermiteR n).eval x * ((hermiteR m).eval x * gaussian x)) := by
    intro x
    rw [Polynomial.deriv, hermiteR_derivative]
    simp [Polynomial.eval_mul, Polynomial.eval_natCast]; ring
  simp_rw [h_rw, integral_const_mul]

/-- Symmetry of the J integral. -/
private theorem J_comm (n m : ℕ) : J n m = J m n := by
  unfold J; congr 1; ext x; ring

/-- Base case: `J(0, 0) = √(2π)`. -/
private theorem J_zero_zero : J 0 0 = Real.sqrt (2 * Real.pi) := by
  unfold J hermiteR
  simp only [hermite_zero]
  have h : (fun x : ℝ => (Polynomial.map (Int.castRingHom ℝ) (C 1)).eval x *
      ((Polynomial.map (Int.castRingHom ℝ) (C 1)).eval x * gaussian x)) =
      fun x => Real.exp (-(1 / 2) * x ^ 2) := by
    ext x; simp [gaussian]; ring
  rw [h, integral_gaussian (1 / 2)]
  congr 1; ring

/-- Base case: `J(k+1, 0) = 0` for all k.
    Proof: from `J_succ_succ` and `J_comm`, `(k+2)·J(k+1,0) = J(k+1,0)`, so `(k+1)·J(k+1,0) = 0`.
-/
private theorem J_succ_zero (k : ℕ) : J (k + 1) 0 = 0 := by
  -- J(k+2, 1) = (k+2) * J(k+1, 0) by J_succ_succ
  have h1 : J (k + 2) 1 = (↑(k + 2) : ℝ) * J (k + 1) 0 := J_succ_succ (k + 1) 0
  -- J(k+2, 1) = J(1, k+2) = 1 * J(0, k+1) = J(k+1, 0)
  have h2 : J (k + 2) 1 = J (k + 1) 0 := by
    rw [J_comm (k + 2) 1]
    show J 1 (k + 2) = J (k + 1) 0
    rw [show (1 : ℕ) = 0 + 1 from rfl, show k + 2 = (k + 1) + 1 from rfl,
        J_succ_succ 0 (k + 1)]
    simp [J_comm]
  -- So (k+2) * J(k+1, 0) = J(k+1, 0), hence (k+1) * J(k+1, 0) = 0
  have h3 : (↑(k + 1) : ℝ) * J (k + 1) 0 = 0 := by
    have h12 : (↑(k + 2) : ℝ) * J (k + 1) 0 - J (k + 1) 0 = 0 := by linarith
    have : (↑(k + 1) : ℝ) * J (k + 1) 0 =
        (↑(k + 2) : ℝ) * J (k + 1) 0 - J (k + 1) 0 := by push_cast; ring
    linarith
  have h4 : (↑(k + 1) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  exact (mul_eq_zero.mp h3).resolve_left h4

/-- `J(n, m) = if n = m then n! * √(2π) else 0`. -/
theorem J_eq : ∀ m n : ℕ,
    J n m = if n = m then ↑(n.factorial) * Real.sqrt (2 * Real.pi) else 0 := by
  intro m
  induction m with
  | zero =>
    intro n
    cases n with
    | zero => simp [J_zero_zero]
    | succ k => simp [J_succ_zero k]
  | succ m ih =>
    intro n
    cases n with
    | zero =>
      rw [J_comm, J_succ_zero]
      simp
    | succ k =>
      rw [J_succ_succ, ih]
      by_cases h : k = m
      · subst h; simp [Nat.factorial_succ, Nat.cast_mul]; ring
      · simp [h]

/-- Substitution lemma: ∫ Hₙ(x√2)·Hₘ(x√2)·exp(-x²) dx = (√2)⁻¹ · J(n,m).
    Uses the substitution u = √2·x and `integral_comp_mul_left`.
-/
private theorem integral_hermiteProd_gaussian_sq (n m : ℕ) :
    ∫ x, (hermiteR n).eval (x * Real.sqrt 2) *
      ((hermiteR m).eval (x * Real.sqrt 2) * Real.exp (-(x ^ 2))) =
    (Real.sqrt 2)⁻¹ * J n m := by
  -- The integrand equals g(√2·x) where g(u) = Hₙ(u)·(Hₘ(u)·exp(-u²/2))
  set g : ℝ → ℝ := fun u => (hermiteR n).eval u * ((hermiteR m).eval u * gaussian u)
  have hg_eq : ∀ x, (hermiteR n).eval (x * Real.sqrt 2) *
      ((hermiteR m).eval (x * Real.sqrt 2) * Real.exp (-(x ^ 2))) =
      g (Real.sqrt 2 * x) := by
    intro x
    simp only [g, gaussian, mul_comm (Real.sqrt 2) x]
    congr 1; congr 1; congr 1
    rw [mul_pow, Real.sq_sqrt two_pos.le]; ring
  simp_rw [hg_eq]
  rw [Measure.integral_comp_mul_left g (Real.sqrt 2),
    show |(Real.sqrt 2)⁻¹| = (Real.sqrt 2)⁻¹ from
      abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr two_pos)),
    smul_eq_mul]
  -- Goal: (√2)⁻¹ * ∫ g = (√2)⁻¹ * J n m
  congr 1

/-- Product of two Hermite functions expressed via J.
    `∫ ψₙ·ψₘ = cₙ·cₘ·(√2)⁻¹·J(n,m)` after substitution u = x√2.
-/
private theorem hermiteFunction_integral_eq (n m : ℕ) :
    ∫ x, hermiteFunction n x * hermiteFunction m x =
    hermiteFunctionNormConst n * hermiteFunctionNormConst m *
      ((Real.sqrt 2)⁻¹ * J n m) := by
  -- Rewrite integrand factoring out constants
  have h_integrand : (fun x => hermiteFunction n x * hermiteFunction m x) =
      fun x => hermiteFunctionNormConst n * hermiteFunctionNormConst m *
        ((hermiteR n).eval (x * Real.sqrt 2) *
         ((hermiteR m).eval (x * Real.sqrt 2) * Real.exp (-(x ^ 2)))) := by
    ext x; unfold hermiteFunction hermiteR
    set cn := hermiteFunctionNormConst n
    set cm := hermiteFunctionNormConst m
    set Hn := ((hermite n).map (Int.castRingHom ℝ)).eval (x * Real.sqrt 2)
    set Hm := ((hermite m).map (Int.castRingHom ℝ)).eval (x * Real.sqrt 2)
    set G := Real.exp (-(x ^ 2) / 2)
    show cn * Hn * G * (cm * Hm * G) = cn * cm * (Hn * (Hm * Real.exp (-(x ^ 2))))
    have hG : G * G = Real.exp (-(x ^ 2)) := by
      change Real.exp (-(x ^ 2) / 2) * Real.exp (-(x ^ 2) / 2) = Real.exp (-(x ^ 2))
      rw [← Real.exp_add]; congr 1; ring
    calc cn * Hn * G * (cm * Hm * G)
        = cn * cm * (Hn * Hm) * (G * G) := by ring
      _ = cn * cm * (Hn * Hm) * Real.exp (-(x ^ 2)) := by rw [hG]
      _ = cn * cm * (Hn * (Hm * Real.exp (-(x ^ 2)))) := by ring
  rw [h_integrand, integral_const_mul]
  congr 1
  exact integral_hermiteProd_gaussian_sq n m

/-- Hermite functions are orthonormal in L²(ℝ):
    ∫ ψₙ(x) ψₘ(x) dx = δₙₘ
-/
theorem hermiteFunction_orthonormal :
    ∀ n m : ℕ, ∫ x, hermiteFunction n x * hermiteFunction m x = if n = m then 1 else 0 := by
  intro n m
  rw [hermiteFunction_integral_eq, J_eq]
  split_ifs with h
  · -- n = m: cₙ² · (√2)⁻¹ · n! · √(2π) = 1
    subst h
    simp only [hermiteFunctionNormConst]
    have hfact : (0 : ℝ) < ↑n.factorial := Nat.cast_pos.mpr n.factorial_pos
    have hpi : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    have hsqrt2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr two_pos
    have h_sq : Real.sqrt ((↑n.factorial * Real.sqrt Real.pi)⁻¹) *
        Real.sqrt ((↑n.factorial * Real.sqrt Real.pi)⁻¹) =
        (↑n.factorial * Real.sqrt Real.pi)⁻¹ :=
      Real.mul_self_sqrt (inv_nonneg.mpr (mul_nonneg (Nat.cast_nonneg' _) (Real.sqrt_nonneg _)))
    rw [h_sq]
    have h2pi : Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi :=
      Real.sqrt_mul two_pos.le Real.pi
    rw [h2pi]
    field_simp
  · -- n ≠ m: cₙ · cₘ · (√2)⁻¹ · 0 = 0
    ring

-- hermiteFunction_complete is proved below, after the supporting lemmas.

/-- The Gaussian exp(-x²/2) as a Schwartz function. -/
noncomputable def gaussianSchwartz : SchwartzMap ℝ ℝ where
  toFun x := Real.exp (-(x ^ 2 / 2))
  smooth' := by fun_prop
  decay' := by
    intro k n
    set P := (Polynomial.hermite n).map (algebraMap ℤ ℝ)
    obtain ⟨C, hC_nonneg, hbound⟩ :=
      polynomial_eval_mul_exp_neg_bound (X ^ k * P) (by positivity : (0 : ℝ) < 1 / 2)
    refine ⟨C, fun x => ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs, Real.norm_eq_abs]
    have hiter : iteratedDeriv n (fun x => Real.exp (-(x ^ 2 / 2))) x =
        (-1 : ℝ) ^ n * Polynomial.aeval x (Polynomial.hermite n) *
        Real.exp (-(x ^ 2 / 2)) := by
      rw [iteratedDeriv_eq_iterate]
      exact Polynomial.deriv_gaussian_eq_hermite_mul_gaussian n x
    rw [hiter, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_pos (Real.exp_pos _)]
    have haeval : Polynomial.aeval x (Polynomial.hermite n) = P.eval x := by
      simp [P, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    rw [haeval]
    -- Goal: |x| ^ k * (|P.eval x| * exp(-(x²/2))) ≤ C
    -- Rewrite as |(X^k * P).eval x * exp(-(1/2)*x²)| ≤ C
    have hrw : |x| ^ k * (|P.eval x| * Real.exp (-(x ^ 2 / 2))) =
        |(X ^ k * P).eval x * Real.exp (-(1 / 2) * x ^ 2)| := by
      rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
          abs_mul, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
      ring_nf
    rw [hrw]
    exact hbound x

/-- Iterated derivCLM agrees pointwise with iterated deriv on any Schwartz function. -/
private lemma derivCLM_iterate_apply (n : ℕ) (g : SchwartzMap ℝ ℝ) (x : ℝ) :
    (⇑(SchwartzMap.derivCLM ℝ ℝ))^[n] g x = deriv^[n] (⇑g) x := by
  induction n generalizing g with
  | zero => rfl
  | succ n ih => exact ih _

/-- `x ^ k * exp(-x²/2)` is a Schwartz function, proved by iterating multiplication by x
    via `SchwartzMap.smulLeftCLM`.
-/
private lemma pow_mul_gaussian_schwartz (k : ℕ) :
    ∃ (φ : SchwartzMap ℝ ℝ), ∀ x, φ x = x ^ k * Real.exp (-(x ^ 2 / 2)) := by
  induction k with
  | zero =>
    exact ⟨gaussianSchwartz, fun x => by
      change Real.exp (-(x ^ 2 / 2)) = x ^ 0 * Real.exp (-(x ^ 2 / 2)); simp⟩
  | succ k ih =>
    obtain ⟨ψ, hψ⟩ := ih
    refine ⟨SchwartzMap.smulLeftCLM ℝ (fun x => x) ψ, fun x => ?_⟩
    rw [SchwartzMap.smulLeftCLM_apply_apply Function.HasTemperateGrowth.id']
    simp only [smul_eq_mul, hψ x]
    ring

/-- For any polynomial P, x ↦ P(x) · exp(-x²/2) is a Schwartz function. -/
private lemma poly_mul_gaussian_schwartz (P : ℝ[X]) :
    ∃ (φ : SchwartzMap ℝ ℝ), ∀ x, φ x = P.eval x * Real.exp (-(x ^ 2 / 2)) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨φp, hφp⟩ := hp
    obtain ⟨φq, hφq⟩ := hq
    exact ⟨φp + φq, fun x => by
      simp only [add_apply, Polynomial.eval_add, add_mul, hφp x, hφq x]⟩
  | monomial k a =>
    obtain ⟨ψ, hψ⟩ := pow_mul_gaussian_schwartz k
    exact ⟨a • ψ, fun x => by
      simp only [smul_apply, smul_eq_mul, Polynomial.eval_monomial, hψ x]
      ring⟩

/-- Each Hermite function is a Schwartz function. -/
theorem hermiteFunction_schwartz (n : ℕ) :
    ∃ (φ : SchwartzMap ℝ ℝ), ∀ x, φ x = hermiteFunction n x := by
  -- Hₙ(x√2) = Q(x) where Q is the composed polynomial
  set Q := (hermiteR n).comp (C (Real.sqrt 2) * X) with hQ_def
  obtain ⟨ψ, hψ⟩ := poly_mul_gaussian_schwartz Q
  refine ⟨hermiteFunctionNormConst n • ψ, fun x => ?_⟩
  simp only [smul_apply, smul_eq_mul, hψ x]
  unfold hermiteFunction
  -- Q.eval x = (hermiteR n).eval (x * √2) = (hermite n).map(...).eval (x * √2)
  have hQeval : Q.eval x = ((hermite n).map (Int.castRingHom ℝ)).eval (x * Real.sqrt 2) := by
    simp [hQ_def, hermiteR, Polynomial.eval_comp, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, mul_comm x (Real.sqrt 2)]
  rw [← hQeval]
  -- Handle exp argument and associativity: c * (Q * exp₁) = c * Q * exp₂
  have hexp : Real.exp (-(x ^ 2 / 2)) = Real.exp (-(x ^ 2) / 2) := by
    congr 1; ring
  rw [hexp, mul_assoc]

/-! ### Raising/Lowering Operators and Seminorm Bounds

We prove polynomial growth of Schwartz seminorms via:
1. Raising/lowering operator identities for Hermite functions
2. L² norm bounds from orthonormality
3. Agmon (Sobolev) inequality: ‖f‖_∞² ≤ 2‖f‖₂·‖f'‖₂
4. Assembly: seminorm ≤ C·(1+n)^s
-/

/-- Normalization constant is positive. -/
private lemma normConst_pos (n : ℕ) : 0 < hermiteFunctionNormConst n := by
  unfold hermiteFunctionNormConst
  exact Real.sqrt_pos.mpr (inv_pos.mpr (mul_pos
    (Nat.cast_pos.mpr n.factorial_pos) (Real.sqrt_pos.mpr Real.pi_pos)))

/-- Normalization constant is non-negative. -/
private lemma normConst_nonneg (n : ℕ) : 0 ≤ hermiteFunctionNormConst n :=
  le_of_lt (normConst_pos n)

/-- Square of normalization constant: cₙ² = (n!·√π)⁻¹ -/
private lemma normConst_sq (n : ℕ) :
    hermiteFunctionNormConst n * hermiteFunctionNormConst n =
    (↑n.factorial * Real.sqrt Real.pi)⁻¹ := by
  unfold hermiteFunctionNormConst
  exact Real.mul_self_sqrt (inv_nonneg.mpr (mul_nonneg (Nat.cast_nonneg' _) (Real.sqrt_nonneg _)))

/-- Normalization constant relation: cₙ = √(n+1) · c_{n+1} -/
private lemma normConst_succ (n : ℕ) :
    hermiteFunctionNormConst n = Real.sqrt (↑(n + 1)) * hermiteFunctionNormConst (n + 1) := by
  simp only [hermiteFunctionNormConst]
  rw [← Real.sqrt_mul (Nat.cast_nonneg' (n + 1))]
  congr 1
  rw [Nat.factorial_succ, Nat.cast_mul]
  have hfact : (0 : ℝ) < ↑n.factorial := Nat.cast_pos.mpr n.factorial_pos
  have hpi : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hn1 : (0 : ℝ) < ↑(n + 1) := Nat.cast_pos.mpr (Nat.succ_pos n)
  field_simp

/-- X · Hₙ₊₁ = Hₙ₊₂ + (n+1) · Hₙ in ℤ[X]. -/
lemma hermite_X_mul (n : ℕ) :
    X * hermite (n + 1) = hermite (n + 2) + (↑(n + 1) : ℤ[X]) * hermite n := by
  linear_combination -(hermite_succ (n + 1)) + hermite_derivative n

lemma hermiteR_recurrence_succ (n : ℕ) (t : ℝ) :
    t * (hermiteR (n + 1)).eval t =
    (hermiteR (n + 2)).eval t + ↑(n + 1) * (hermiteR n).eval t := by
  have h := congr_arg (fun p => (Polynomial.map (Int.castRingHom ℝ) p).eval t)
    (hermite_X_mul n)
  simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_X,
    Polynomial.map_natCast, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_natCast] at h
  linarith

/-- Hermite recurrence for n = 0: t · H₀(t) = H₁(t). -/
lemma hermiteR_recurrence_zero (t : ℝ) :
    t * (hermiteR 0).eval t = (hermiteR 1).eval t := by
  simp [hermiteR, hermite_zero, hermite_succ, Polynomial.eval_X,
    Polynomial.map_X]

/-- x·ψₙ expressed using normConst and hermiteR, factoring out the exponential. -/
private lemma mul_x_hermiteFunction_aux (n : ℕ) (x : ℝ) :
    x * hermiteFunction n x =
    hermiteFunctionNormConst n *
    (x * (hermiteR n).eval (x * Real.sqrt 2)) *
    Real.exp (-(x ^ 2) / 2) := by
  unfold hermiteFunction
  ring

/-- Key coefficient identity: c_n / √2 = √((n+1)/2) · c_{n+1}.
    Proof: c_n = √(n+1) · c_{n+1} (normConst_succ), so
    c_n/√2 = √(n+1)/√2 · c_{n+1} = √((n+1)/2) ·
    c_{n+1}.
-/
private lemma normConst_div_sqrt2 (n : ℕ) :
    hermiteFunctionNormConst n / Real.sqrt 2 =
    Real.sqrt ((↑(n + 1) : ℝ) / 2) * hermiteFunctionNormConst (n + 1) := by
  rw [normConst_succ n, mul_div_assoc, Real.sqrt_div (Nat.cast_nonneg' (n + 1))]
  ring

/-- Key coefficient identity: (n+1) · c_{n+1} / √2 = √((n+1)/2) · c_n.
    Proof: c_n = √(n+1) · c_{n+1}, so √(n+1) · c_{n+1} = c_n, and
    (n+1) · c_{n+1} / √2 =
    √(n+1) · √(n+1) · c_{n+1} / √2 = √(n+1)/√2 · c_n =
    √((n+1)/2) · c_n.
-/
private lemma normConst_mul_div_sqrt2 (n : ℕ) :
    ↑(n + 1) * hermiteFunctionNormConst (n + 1) / Real.sqrt 2 =
    Real.sqrt ((↑(n + 1) : ℝ) / 2) * hermiteFunctionNormConst n := by
  have hn1 : (0 : ℝ) ≤ ↑(n + 1) := Nat.cast_nonneg' (n + 1)
  have hc := normConst_succ n  -- c_n = √(n+1) * c_{n+1}
  -- Rewrite ↑(n+1) = √(n+1) * √(n+1)
  conv_lhs => rw [show (↑(n + 1) : ℝ) = Real.sqrt (↑(n + 1)) * Real.sqrt (↑(n + 1)) from
    (Real.mul_self_sqrt hn1).symm]
  -- ↑(n+1) * c_{n+1} / √2 = √(n+1) * (√(n+1) * c_{n+1}) / √2 = √(n+1) * c_n / √2
  rw [mul_assoc, hc.symm, mul_div_assoc, Real.sqrt_div hn1]
  ring

/-- Multiplication by x: x·ψₙ = √((n+1)/2)·ψ_{n+1} + √(n/2)·ψ_{n-1}. -/
theorem mul_x_hermiteFunction (n : ℕ) (x : ℝ) :
    x * hermiteFunction n x =
    Real.sqrt ((↑(n + 1) : ℝ) / 2) * hermiteFunction (n + 1) x +
    Real.sqrt ((↑n : ℝ) / 2) * hermiteFunction (n - 1) x := by
  have h2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)
  have h2ne : Real.sqrt 2 ≠ 0 := ne_of_gt h2pos
  -- Set up abbreviations
  set t := x * Real.sqrt 2 with ht_def
  set e := Real.exp (-(x ^ 2) / 2) with he_def
  -- Express x as t/√2
  have hx_eq : x = t / Real.sqrt 2 := by
    rw [ht_def, mul_div_cancel_right₀ x h2ne]
  cases n with
  | zero =>
    -- n = 0: second term vanishes since √(0/2) = 0
    simp only [Nat.cast_zero, zero_div, Real.sqrt_zero, zero_mul, add_zero, Nat.zero_sub]
    -- Need: x * ψ₀(x) = √(1/2) * ψ₁(x)
    unfold hermiteFunction
    -- Simplify t/√2 * √2 = t
    have ht_simp : t / Real.sqrt 2 * Real.sqrt 2 = t := div_mul_cancel₀ t h2ne
    rw [hx_eq]
    simp only [ht_simp]
    -- Use the recurrence: t * H₀(t) = H₁(t)
    have hrec := hermiteR_recurrence_zero t
    set e' := Real.exp (-(t / Real.sqrt 2) ^ 2 / 2) with he'_def
    -- LHS: (t/√2) * c₀ * H₀(t) * e' = c₀/√2 * (t * H₀(t)) * e'
    have lhs_eq : t / Real.sqrt 2 * (hermiteFunctionNormConst 0 * (hermiteR 0).eval t * e') =
      hermiteFunctionNormConst 0 / Real.sqrt 2 * (t * (hermiteR 0).eval t) * e' := by ring
    rw [lhs_eq, hrec, normConst_div_sqrt2 0]
    ring
  | succ n =>
    -- n = n' + 1: use three-term recurrence
    rw [show (n + 1 : ℕ) - 1 = n from by omega]
    unfold hermiteFunction
    -- Simplify t/√2 * √2 = t everywhere
    have ht_simp : t / Real.sqrt 2 * Real.sqrt 2 = t := div_mul_cancel₀ t h2ne
    -- Express x in terms of t
    rw [hx_eq]
    simp only [ht_simp]
    -- Now both sides use t = x * √2 as the argument to hermiteR
    -- Use the recurrence: t * H_{n+1}(t) = H_{n+2}(t) + (n+1) * H_n(t)
    have hrec := hermiteR_recurrence_succ n t
    -- LHS: (t/√2) * c_{n+1} * H_{n+1}(t) * e'
    -- where e' = exp(-(t/√2)²/2)
    -- Factor to: c_{n+1}/√2 * (t * H_{n+1}(t)) * e'
    set e' := Real.exp (-(t / Real.sqrt 2) ^ 2 / 2) with he'_def
    have lhs_eq : t / Real.sqrt 2 *
      (hermiteFunctionNormConst (n + 1) * (hermiteR (n + 1)).eval t * e') =
      hermiteFunctionNormConst (n + 1) / Real.sqrt 2 * (t * (hermiteR (n + 1)).eval t) * e' := by
      ring
    rw [lhs_eq, hrec]
    have key1 := normConst_div_sqrt2 (n + 1)
    have key2 := normConst_mul_div_sqrt2 n
    -- Distribute
    have expand : hermiteFunctionNormConst (n + 1) / Real.sqrt 2 *
      ((hermiteR (n + 2)).eval t + ↑(n + 1) * (hermiteR n).eval t) * e' =
      hermiteFunctionNormConst (n + 1) / Real.sqrt 2 * (hermiteR (n + 2)).eval t * e' +
      (↑(n + 1) * hermiteFunctionNormConst (n + 1) / Real.sqrt 2) * (hermiteR n).eval t * e' := by
      ring
    rw [expand, key1, key2]
    ring

/-- Hermite functions are smooth (ContDiff ℝ ⊤). -/
lemma hermiteFunction_contDiff (j : ℕ) (m : ℕ) :
    ContDiff ℝ m (hermiteFunction j) := by
  obtain ⟨φ, hφ⟩ := hermiteFunction_schwartz j
  have : hermiteFunction j = ⇑φ := funext fun x => (hφ x).symm
  rw [this]; exact φ.smooth _

/-- Derivative identity: ψₙ'(x) = √(n/2) ψ_{n-1}(x) - √((n+1)/2) ψ_{n+1}(x).
    Proved from the product rule on cₙ · Hₙ(x√2) · exp(-x²/2) and Hermite recurrence.
-/
theorem deriv_hermiteFunction (n : ℕ) (x : ℝ) :
    deriv (hermiteFunction n) x =
    Real.sqrt ((↑n : ℝ) / 2) * hermiteFunction (n - 1) x -
    Real.sqrt ((↑(n + 1) : ℝ) / 2) * hermiteFunction (n + 1) x := by
  have h2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)
  have h2ne : Real.sqrt 2 ≠ 0 := ne_of_gt h2pos
  -- Set up abbreviations
  set t := x * Real.sqrt 2 with ht_def
  set e := Real.exp (-(x ^ 2) / 2) with he_def
  -- Express x as t/√2
  have hx_eq : x = t / Real.sqrt 2 := by
    rw [ht_def, mul_div_cancel_right₀ x h2ne]
  -- Compute HasDerivAt for the polynomial part: chain rule
  -- H_n(u * √2) has derivative √2 * H_n'(u * √2) = √2 * (derivative H_n).eval(u * √2)
  have hpoly_hasderiv : HasDerivAt (fun u => (hermiteR n).eval (u * Real.sqrt 2))
      (Real.sqrt 2 * (Polynomial.derivative (hermiteR n)).eval (x * Real.sqrt 2)) x := by
    have h_inner : HasDerivAt (fun u : ℝ => u * Real.sqrt 2) (Real.sqrt 2) x := by
      have := (hasDerivAt_id x).mul_const (Real.sqrt 2)
      simpa using this
    have h_outer : HasDerivAt (fun u => (hermiteR n).eval u)
        ((Polynomial.derivative (hermiteR n)).eval (x * Real.sqrt 2)) (x * Real.sqrt 2) := by
      have : (fun u => (hermiteR n).eval u) = fun u => Polynomial.aeval u (hermiteR n) := by
        ext u; simp [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_id]
      rw [this]
      exact Polynomial.hasDerivAt_aeval (hermiteR n) (x * Real.sqrt 2)
    have hcomp := h_outer.comp x h_inner
    rwa [mul_comm] at hcomp
  -- Compute HasDerivAt for the exponential part
  have hexp_hasderiv : HasDerivAt (fun u : ℝ => Real.exp (-(u ^ 2) / 2)) (-x * e) x := by
    have h1 : HasDerivAt (fun u : ℝ => -(u ^ 2) / 2) (-x) x := by
      have := ((hasDerivAt_pow 2 x).neg.div_const 2)
      have hf : (fun u : ℝ => -u ^ 2 / 2) = fun x => (-fun x => x ^ 2) x / 2 := by ext u; simp
      have hv : (-x : ℝ) = -(↑2 * x ^ (2 - 1)) / 2 := by norm_num; ring
      rw [hf, hv]; exact this
    have h2 := h1.exp
    rw [he_def]
    convert h2 using 1; ring
  -- Compute HasDerivAt for the product poly * exp (pointwise, not Pi.mul)
  have hprod : HasDerivAt (fun u => (hermiteR n).eval (u * Real.sqrt 2) * Real.exp (-(u ^ 2) / 2))
      (Real.sqrt 2 * (Polynomial.derivative (hermiteR n)).eval (x * Real.sqrt 2) * e +
       (hermiteR n).eval (x * Real.sqrt 2) * (-x * e)) x := by
    have h := hpoly_hasderiv.mul hexp_hasderiv
    rw [he_def] at h
    exact h
  -- Compute HasDerivAt for the full hermiteFunction = c_n * (poly * exp)
  have hfn_eq : hermiteFunction n = fun u =>
      hermiteFunctionNormConst n * ((hermiteR n).eval (u * Real.sqrt 2) * Real.exp (-(u ^ 2) / 2))
        := by
    ext u; unfold hermiteFunction; ring
  have hfull := hprod.const_mul (hermiteFunctionNormConst n)
  rw [hfn_eq, hfull.deriv]
  -- Now the goal is algebraic:
  -- c_n * (√2 * (derivative H_n).eval t * e + H_n.eval t * (-x * e)) = RHS
  -- Case split on n
  cases n with
  | zero =>
    -- n = 0: derivative H_0 = 0, so deriv = c_0 * (0 - x * H_0(t)) * e = -x * ψ_0
    simp only [Nat.cast_zero, zero_div, Real.sqrt_zero, zero_mul, zero_sub, Nat.zero_sub]
    -- derivative of hermiteR 0 is 0
    have hd0 : Polynomial.derivative (hermiteR 0) = 0 := by
      simp [hermiteR, hermite_zero]
    rw [hd0, Polynomial.eval_zero, mul_zero, zero_mul, zero_add]
    -- Need: c_0 * (H_0(t) * (-x * e)) = -(√(1/2) * (c_1 * H_1(t) * e))
    unfold hermiteFunction
    have ht_simp : t / Real.sqrt 2 * Real.sqrt 2 = t := div_mul_cancel₀ t h2ne
    rw [hx_eq]
    simp only [ht_simp]
    have hrec := hermiteR_recurrence_zero t
    set e' := Real.exp (-(t / Real.sqrt 2) ^ 2 / 2) with he'_def
    have he_eq : e = e' := by
      rw [he_def, he'_def]; congr 1; rw [hx_eq]
    rw [he_eq]
    have lhs_eq : hermiteFunctionNormConst 0 *
      ((hermiteR 0).eval t * (-(t / Real.sqrt 2) * e')) =
      -(hermiteFunctionNormConst 0 / Real.sqrt 2) * (t * (hermiteR 0).eval t) * e' := by ring
    rw [lhs_eq, hrec, normConst_div_sqrt2 0]
    ring
  | succ n =>
    rw [show (n + 1 : ℕ) - 1 = n from by omega]
    have hd := hermiteR_derivative n
    rw [hd, Polynomial.eval_mul, Polynomial.eval_natCast]
    have hrec := hermiteR_recurrence_succ n t
    unfold hermiteFunction
    have ht_simp : t / Real.sqrt 2 * Real.sqrt 2 = t := div_mul_cancel₀ t h2ne
    rw [hx_eq]
    simp only [ht_simp]
    set e' := Real.exp (-(t / Real.sqrt 2) ^ 2 / 2) with he'_def
    have he_eq : e = e' := by
      rw [he_def, he'_def]; congr 1; rw [hx_eq]
    rw [he_eq]
    have key1 := normConst_mul_div_sqrt2 n
    have key2 := normConst_div_sqrt2 (n + 1)
    -- Rewrite √2 = √2*√2/√2 to factor out 1/√2
    have h_sqrt2_eq : Real.sqrt 2 = Real.sqrt 2 * Real.sqrt 2 / Real.sqrt 2 := by
      rw [mul_div_cancel_right₀ _ h2ne]
    have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)
    -- Rewrite the full LHS in one step:
    -- c_{n+1} * (√2 * (n+1) * H_n(t) * e' + H_{n+1}(t) * (-t/√2 * e'))
    -- After substituting recurrence for t * H_{n+1}(t), this equals
    -- (n+1)*c_{n+1}/√2 * H_n(t) * e' - c_{n+1}/√2 * H_{n+2}(t) * e'
    -- Step 1: Factor everything to c_{n+1}/√2
    -- √2 * (n+1) * H_n = (n+1) * H_n * √2*√2/√2 = 2*(n+1)*H_n/√2
    -- -(t/√2) * H_{n+1} = -t*H_{n+1}/√2
    -- So: c_{n+1}/√2 * (2*(n+1)*H_n(t) - t*H_{n+1}(t)) * e'
    -- Substitute recurrence: t*H_{n+1}(t) = H_{n+2}(t) + (n+1)*H_n(t)
    -- = c_{n+1}/√2 * (2*(n+1)*H_n(t) - H_{n+2}(t) - (n+1)*H_n(t)) * e'
    -- = c_{n+1}/√2 * ((n+1)*H_n(t) - H_{n+2}(t)) * e'
    -- = (n+1)*c_{n+1}/√2 * H_n(t) * e' - c_{n+1}/√2 * H_{n+2}(t) * e'
    have expand : hermiteFunctionNormConst (n + 1) *
      (Real.sqrt 2 * (↑(n + 1) * (hermiteR n).eval t) * e' +
       (hermiteR (n + 1)).eval t * (-(t / Real.sqrt 2) * e')) =
      (↑(n + 1) * hermiteFunctionNormConst (n + 1) / Real.sqrt 2) * (hermiteR n).eval t * e' -
      (hermiteFunctionNormConst (n + 1) / Real.sqrt 2) * (hermiteR (n + 2)).eval t * e' := by
      -- Use hrec and hsq2 to close this
      have lhs_factor : hermiteFunctionNormConst (n + 1) *
        (Real.sqrt 2 * (↑(n + 1) * (hermiteR n).eval t) * e' +
         (hermiteR (n + 1)).eval t * (-(t / Real.sqrt 2) * e')) =
        hermiteFunctionNormConst (n + 1) / Real.sqrt 2 *
        (Real.sqrt 2 * Real.sqrt 2 * (↑(n + 1) * (hermiteR n).eval t) -
         t * (hermiteR (n + 1)).eval t) * e' := by
        field_simp; ring
      rw [lhs_factor, hsq2, hrec]
      ring
    rw [expand, key1, key2]
    ring

/-- Hermite function squared is integrable. -/
private lemma hermiteFunction_sq_integrable (j : ℕ) :
    Integrable (fun x => hermiteFunction j x * hermiteFunction j x) volume := by
  exact (hermiteFunction_memLp j).integrable_mul (hermiteFunction_memLp j)

/-- L² norm squared of ψ_n equals 1, from orthonormality. -/
private lemma hermiteFunction_l2_sq (j : ℕ) :
    ∫ x, hermiteFunction j x * hermiteFunction j x = 1 := by
  have := hermiteFunction_orthonormal j j
  simp only [ite_true] at this; exact this

/-- The L² integral of (ψₙ')² equals (2n+1)/2, from the derivative identity and
orthonormality. -/
private lemma hermiteFunction_deriv_l2_sq (n : ℕ) :
    ∫ x, deriv (hermiteFunction n) x * deriv (hermiteFunction n) x = (2 * ↑n + 1) / 2 := by
  -- Define the three component functions
  let f_A : ℝ → ℝ := fun x =>
    ↑n / 2 * (hermiteFunction (n - 1) x * hermiteFunction (n - 1) x)
  let f_B : ℝ → ℝ := fun x =>
    ↑(n + 1) / 2 * (hermiteFunction (n + 1) x * hermiteFunction (n + 1) x)
  let f_C : ℝ → ℝ := fun x => 2 * Real.sqrt (↑n / 2) * Real.sqrt (↑(n + 1) / 2) *
      (hermiteFunction (n - 1) x * hermiteFunction (n + 1) x)
  -- Rewrite integrand as f_A + f_B - f_C
  have h_eq : (fun x => deriv (hermiteFunction n) x * deriv (hermiteFunction n) x) =
      fun x => f_A x + f_B x - f_C x := by
    ext x; simp only [f_A, f_B, f_C]
    rw [deriv_hermiteFunction]
    have h1 : Real.sqrt (↑n / 2) * Real.sqrt (↑n / 2) = ↑n / 2 :=
      Real.mul_self_sqrt (div_nonneg (Nat.cast_nonneg' n) (by norm_num))
    have h2 : Real.sqrt (↑(n + 1) / 2) * Real.sqrt (↑(n + 1) / 2) = ↑(n + 1) / 2 :=
      Real.mul_self_sqrt (div_nonneg (Nat.cast_nonneg' (n+1)) (by norm_num))
    nlinarith [h1, h2]
  rw [h_eq]
  -- Integrability
  have hA : Integrable f_A := (hermiteFunction_sq_integrable (n - 1)).const_mul _
  have hB : Integrable f_B := (hermiteFunction_sq_integrable (n + 1)).const_mul _
  have hC : Integrable f_C :=
    ((hermiteFunction_memLp (n - 1)).integrable_mul (hermiteFunction_memLp (n + 1))).const_mul _
  -- Split integral step by step using helper
  have split_add : ∀ (f g : ℝ → ℝ), Integrable f → Integrable g →
      ∫ x, f x + g x = (∫ x, f x) + ∫ x, g x :=
    fun f g hf hg => integral_add hf hg
  have split_sub : ∀ (f g : ℝ → ℝ), Integrable f → Integrable g →
      ∫ x, f x - g x = (∫ x, f x) - ∫ x, g x :=
    fun f g hf hg => integral_sub hf hg
  -- Convert pointwise to Pi form and split
  have step1 : ∫ x, f_A x + f_B x - f_C x =
      ∫ x, f_A x + (f_B x - f_C x) := by congr 1; ext x; ring
  rw [step1]
  simp only [show ∀ x, f_B x - f_C x = (f_B - f_C) x from fun x => rfl]
  rw [split_add _ _ hA (hB.sub hC)]
  simp only [show ∀ x, (f_B - f_C) x = f_B x - f_C x from fun x => rfl]
  rw [split_sub _ _ hB hC]
  simp only [f_A, f_B, f_C, integral_const_mul, hermiteFunction_l2_sq, mul_one]
  have hne : n - 1 ≠ n + 1 := by omega
  rw [hermiteFunction_orthonormal (n - 1) (n + 1), if_neg hne, mul_zero]
  push_cast; ring

/-- The squared hermiteFunction has a HasDerivAt using the chain/product rule. -/
private lemma hasDerivAt_hermiteFunction_sq (n : ℕ) (x : ℝ) :
    HasDerivAt (fun t => hermiteFunction n t * hermiteFunction n t)
      (2 * hermiteFunction n x * deriv (hermiteFunction n) x) x := by
  have hd : HasDerivAt (hermiteFunction n) (deriv (hermiteFunction n) x) x :=
    ((hermiteFunction_contDiff n 1).differentiable one_ne_zero x).hasDerivAt
  have := hd.mul hd
  have hf : (fun t => hermiteFunction n t * hermiteFunction n t)
      = hermiteFunction n * hermiteFunction n := rfl
  have hv : 2 * hermiteFunction n x * deriv (hermiteFunction n) x
      = deriv (hermiteFunction n) x * hermiteFunction n x
        + hermiteFunction n x * deriv (hermiteFunction n) x := by ring
  rw [hf, hv]; exact this

/-- The derivative of hermiteFunction n is in L² (as a MemLp function). -/
private lemma deriv_hermiteFunction_memLp (n : ℕ) :
    MemLp (deriv (hermiteFunction n)) 2 volume := by
  -- ψₙ' = √(n/2) ψ_{n-1} - √((n+1)/2) ψ_{n+1}, and each ψⱼ is in L²
  have h_eq : deriv (hermiteFunction n) =
      fun x => Real.sqrt (↑n / 2) * hermiteFunction (n - 1) x -
               Real.sqrt (↑(n + 1) / 2) * hermiteFunction (n + 1) x := by
    ext x; exact deriv_hermiteFunction n x
  rw [h_eq]
  exact (hermiteFunction_memLp (n - 1)).const_mul (Real.sqrt (↑n / 2))
    |>.sub ((hermiteFunction_memLp (n + 1)).const_mul (Real.sqrt (↑(n + 1) / 2)))

/-- The product ψₙ · ψₙ' is integrable (for Cauchy-Schwarz/FTC). -/
private lemma integrable_hermiteFunction_mul_deriv (n : ℕ) :
    Integrable (fun x => hermiteFunction n x * deriv (hermiteFunction n) x) volume :=
  (hermiteFunction_memLp n).integrable_mul (deriv_hermiteFunction_memLp n)

/-- A Schwartz function on ℝ tends to 0 at atBot. -/
private lemma schwartz_tendsto_atBot (φ : SchwartzMap ℝ ℝ) :
    Filter.Tendsto (fun x => φ x) Filter.atBot (nhds 0) := by
  have hza := ZeroAtInftyContinuousMapClass.zero_at_infty φ
  rw [cocompact_eq_atBot_atTop] at hza
  exact hza.mono_left le_sup_left

/-- A Schwartz function on ℝ tends to 0 at atTop. -/
private lemma schwartz_tendsto_atTop (φ : SchwartzMap ℝ ℝ) :
    Filter.Tendsto (fun x => φ x) Filter.atTop (nhds 0) := by
  have hza := ZeroAtInftyContinuousMapClass.zero_at_infty φ
  rw [cocompact_eq_atBot_atTop] at hza
  exact hza.mono_left le_sup_right

/-- ψₙ(x)² → 0 as x → -∞. -/
private lemma hermiteFunction_sq_tendsto_atBot (n : ℕ) :
    Filter.Tendsto (fun x => hermiteFunction n x * hermiteFunction n x)
      Filter.atBot (nhds 0) := by
  obtain ⟨φ, hφ⟩ := hermiteFunction_schwartz n
  have heq : (fun x => hermiteFunction n x * hermiteFunction n x) =
      fun x => φ x * φ x := by ext x; rw [← hφ x]
  rw [heq, show (0 : ℝ) = 0 * 0 from (mul_zero 0).symm]
  exact (schwartz_tendsto_atBot φ).mul (schwartz_tendsto_atBot φ)

/-- ψₙ(x)² → 0 as x → +∞. -/
private lemma hermiteFunction_sq_tendsto_atTop (n : ℕ) :
    Filter.Tendsto (fun x => hermiteFunction n x * hermiteFunction n x)
      Filter.atTop (nhds 0) := by
  obtain ⟨φ, hφ⟩ := hermiteFunction_schwartz n
  have heq : (fun x => hermiteFunction n x * hermiteFunction n x) =
      fun x => φ x * φ x := by ext x; rw [← hφ x]
  rw [heq, show (0 : ℝ) = 0 * 0 from (mul_zero 0).symm]
  exact (schwartz_tendsto_atTop φ).mul (schwartz_tendsto_atTop φ)

/-- Agmon-type sup bound: |ψₙ(x)| grows at most polynomially in n.
    Uses FTC + Cauchy-Schwarz + orthonormality + derivative identity:
    |ψₙ(x)|² ≤ 2‖ψₙ‖₂ · ‖ψₙ'‖₂ = 2√((2n+1)/2) ≤ C·(1+n)^{1/2}.
-/
theorem hermiteFunction_sup_bound :
    ∃ (C : ℝ) (s : ℝ), 0 < C ∧ 0 ≤ s ∧
    ∀ (n : ℕ) (x : ℝ), |hermiteFunction n x| ≤ C * (1 + ↑n) ^ s := by
  -- We use FTC + AM-GM: |ψ_n(x)|² ≤ ||ψ_n||₂² + ||ψ_n'||₂² = 1 + (2n+1)/2 ≤ 2(1+n)
  -- Hence |ψ_n(x)| ≤ √2 · (1+n)^{1/2}
  refine ⟨Real.sqrt 2, 1 / 2, Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2),
    by norm_num, fun n a => ?_⟩
  -- Step 1: FTC gives ψ_n(a)² = ∫_{-∞}^a 2·ψ_n·ψ_n' dt
  -- First establish the FTC setup
  set f := fun t => hermiteFunction n t * hermiteFunction n t with hf_def
  set f' := fun t => 2 * (hermiteFunction n t * deriv (hermiteFunction n) t) with hf'_def
  have hderiv : ∀ t ∈ Set.Iic a, HasDerivAt f (f' t) t := by
    intro t _
    have := hasDerivAt_hermiteFunction_sq n t
    simp only [hf'_def, mul_assoc] at this ⊢
    exact this
  have hf'_int : IntegrableOn f' (Set.Iic a) volume :=
    ((integrable_hermiteFunction_mul_deriv n).const_mul 2).integrableOn
  have htend : Filter.Tendsto f Filter.atBot (nhds 0) :=
    hermiteFunction_sq_tendsto_atBot n
  have hFTC := MeasureTheory.integral_Iic_of_hasDerivAt_of_tendsto' hderiv hf'_int htend
  -- FTC gives: ∫_{Iic a} f' = f(a) - 0 = ψ_n(a)²
  -- Step 2: |ψ_n(a)²| ≤ ∫_ℝ |f'|
  have hfa : f a = hermiteFunction n a * hermiteFunction n a := rfl
  rw [sub_zero] at hFTC
  -- From FTC: f a = ∫_{Iic a} f'
  -- |f a| ≤ ∫_{Iic a} |f'| ≤ ∫_ℝ |f'|
  -- Integrability of |f'|
  have hf'_abs_int : Integrable (fun t => |f' t|) volume :=
    ((integrable_hermiteFunction_mul_deriv n).const_mul 2).abs
  -- Step 2: ψ_n(a)² ≤ ∫_ℝ |f'|
  have h_sq_bound : hermiteFunction n a * hermiteFunction n a ≤ ∫ t, |f' t| := by
    calc hermiteFunction n a * hermiteFunction n a
        = f a := rfl
      _ ≤ |f a| := le_abs_self _
      _ = |∫ t in Set.Iic a, f' t| := by rw [hFTC]
      _ ≤ ∫ t in Set.Iic a, |f' t| := by
          rw [show |∫ t in Set.Iic a, f' t| = ‖∫ t in Set.Iic a, f' t‖ from
              (Real.norm_eq_abs _).symm]
          exact le_trans (norm_integral_le_integral_norm _)
            (le_of_eq (integral_congr_ae (Filter.Eventually.of_forall
              (fun t => Real.norm_eq_abs (f' t)))))
      _ ≤ ∫ t, |f' t| :=
          MeasureTheory.setIntegral_le_integral hf'_abs_int
            (Filter.Eventually.of_forall (fun t => abs_nonneg _))
  -- Step 3: AM-GM bound: |2·f·f'| ≤ f² + f'², so ∫|f'| ≤ ∫f² + ∫f'²
  have h_amgm : ∀ t : ℝ,
      |f' t| ≤ hermiteFunction n t * hermiteFunction n t +
      deriv (hermiteFunction n) t * deriv (hermiteFunction n) t := by
    intro t
    change |2 * (hermiteFunction n t * deriv (hermiteFunction n) t)| ≤ _
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2), abs_mul]
    -- 2 * (|a| * |b|) ≤ a² + b² from AM-GM: 2ab ≤ a² + b²
    have hab := two_mul_le_add_sq (|hermiteFunction n t|) (|deriv (hermiteFunction n) t|)
    rw [mul_assoc] at hab
    calc 2 * (|hermiteFunction n t| * |deriv (hermiteFunction n) t|)
        ≤ |hermiteFunction n t| ^ 2 + |deriv (hermiteFunction n) t| ^ 2 := hab
      _ = hermiteFunction n t * hermiteFunction n t +
          deriv (hermiteFunction n) t * deriv (hermiteFunction n) t := by
          rw [sq_abs, sq_abs]; simp [sq]
  -- Integrability of (ψ_n')²
  have hderiv_sq_int :
      Integrable (fun x => deriv (hermiteFunction n) x * deriv (hermiteFunction n) x) volume :=
    (deriv_hermiteFunction_memLp n).integrable_mul (deriv_hermiteFunction_memLp n)
  have h_int_bound : ∫ t, |f' t| ≤
      (∫ t, hermiteFunction n t * hermiteFunction n t) +
      (∫ t, deriv (hermiteFunction n) t * deriv (hermiteFunction n) t) := by
    calc ∫ t, |f' t|
        ≤ ∫ t, (hermiteFunction n t * hermiteFunction n t +
                deriv (hermiteFunction n) t * deriv (hermiteFunction n) t) :=
          MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall (fun t => abs_nonneg _))
            ((hermiteFunction_sq_integrable n).add hderiv_sq_int)
            (Filter.Eventually.of_forall h_amgm)
      _ = (∫ t, hermiteFunction n t * hermiteFunction n t) +
          (∫ t, deriv (hermiteFunction n) t * deriv (hermiteFunction n) t) :=
          integral_add (hermiteFunction_sq_integrable n) hderiv_sq_int
  -- Step 4: Substitute known L² norms
  rw [hermiteFunction_l2_sq, hermiteFunction_deriv_l2_sq] at h_int_bound
  -- Now h_int_bound : ∫|2ff'| ≤ 1 + (2n+1)/2
  -- And h_sq_bound : ψ_n(a)² ≤ ∫|2ff'|
  -- So ψ_n(a)² ≤ 1 + (2n+1)/2 = (2n+3)/2
  have h_sq_final : hermiteFunction n a * hermiteFunction n a ≤ 1 + (2 * ↑n + 1) / 2 :=
    le_trans h_sq_bound h_int_bound
  -- Step 5: (2n+3)/2 ≤ 2·(1+n) and take square roots
  -- 1 + (2n+1)/2 = (2n+3)/2 ≤ 2(1+n) since 2n+3 ≤ 4+4n iff 0 ≤ 2+2n
  have h_arith : 1 + (2 * (↑n : ℝ) + 1) / 2 ≤ 2 * (1 + ↑n) := by
    have : (0 : ℝ) ≤ ↑n := Nat.cast_nonneg n
    linarith
  have h_sq_le : hermiteFunction n a * hermiteFunction n a ≤ 2 * (1 + ↑n) :=
    le_trans h_sq_final h_arith
  -- Now |ψ_n(a)|² ≤ 2·(1+n), so |ψ_n(a)| ≤ √(2·(1+n)) = √2 · (1+n)^{1/2}
  have h1n_pos : (0 : ℝ) < 1 + ↑n := by positivity
  have h1n_nonneg : (0 : ℝ) ≤ 1 + ↑n := le_of_lt h1n_pos
  -- |f|² = f * f
  have habs_sq : |hermiteFunction n a| ^ 2 ≤ 2 * (1 + ↑n) := by
    rw [sq_abs, sq]; exact h_sq_le
  -- |f| ≤ √(2*(1+n))
  have h_abs_le : |hermiteFunction n a| ≤ Real.sqrt (2 * (1 + ↑n)) := by
    rw [← Real.sqrt_sq (abs_nonneg _)]
    exact Real.sqrt_le_sqrt habs_sq
  -- √(2*(1+n)) = √2 * √(1+n)
  have h_sqrt_split : Real.sqrt (2 * (1 + ↑n)) = Real.sqrt 2 * Real.sqrt (1 + ↑n) :=
    Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) _
  -- √(2*(1+n)) = √2 * (1+n)^{1/2}
  rw [h_sqrt_split] at h_abs_le
  conv at h_abs_le => rhs; rw [show Real.sqrt (1 + ↑n) = (1 + ↑n) ^ ((1:ℝ) / 2)
    from Real.sqrt_eq_rpow _]
  exact h_abs_le

/-- Pointwise bound on |x|^k · ‖d^m ψₙ(x)‖ ≤ C · (1+n)^s.
    Proved via raising/lowering operators, L² bounds, and Agmon inequality.
-/
private theorem hermiteFunction_pointwise_bound (k m : ℕ) :
    ∃ (C : ℝ) (s : ℝ), 0 < C ∧ 0 ≤ s ∧
    ∀ (n : ℕ) (x : ℝ),
    |x| ^ k * ‖iteratedDeriv m (hermiteFunction n) x‖ ≤
    C * (1 + ↑n) ^ s := by
  induction m with
  | zero =>
    -- For m = 0, iteratedDeriv 0 f = f, reduce to bounding |x|^k |ψ_n(x)|
    induction k with
    | zero =>
      -- Base case: k=0, m=0. Use hermiteFunction_sup_bound.
      obtain ⟨C, s, hC, hs, hbound⟩ := hermiteFunction_sup_bound
      exact ⟨C, s, hC, hs, fun n x => by
        simp only [pow_zero, one_mul, iteratedDeriv_zero, Real.norm_eq_abs]
        exact hbound n x⟩
    | succ k ih =>
      -- Step k → k+1 (m=0): use mul_x_hermiteFunction
      -- |x|^{k+1} |ψ_n| = |x|^k |x·ψ_n| ≤ |x|^k (√((n+1)/2)|ψ_{n+1}| + √(n/2)|ψ_{n-1}|)
      obtain ⟨C, s, hC, hs, hbound⟩ := ih
      refine ⟨C * ((2 : ℝ) ^ s + 1), s + 1, by positivity, by linarith, fun n x => ?_⟩
      simp only [iteratedDeriv_zero, Real.norm_eq_abs] at hbound ⊢
      -- |x|^{k+1} * |ψ_n(x)| = |x|^k * |x * ψ_n(x)|
      rw [pow_succ, mul_assoc, ← abs_mul]
      -- Use mul_x_hermiteFunction: x·ψ_n = √((n+1)/2)·ψ_{n+1} + √(n/2)·ψ_{n-1}
      rw [mul_x_hermiteFunction]
      -- Triangle inequality + rearrange
      have h_tri : |Real.sqrt ((↑(n + 1) : ℝ) / 2) * hermiteFunction (n + 1) x +
          Real.sqrt ((↑n : ℝ) / 2) * hermiteFunction (n - 1) x| ≤
          Real.sqrt ((↑(n + 1) : ℝ) / 2) * |hermiteFunction (n + 1) x| +
          Real.sqrt ((↑n : ℝ) / 2) * |hermiteFunction (n - 1) x| :=
        (abs_add_le _ _).trans (by rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
          abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)])
      -- Bound each term
      have h_main : |x| ^ k *
          (Real.sqrt ((↑(n + 1) : ℝ) / 2) * |hermiteFunction (n + 1) x| +
           Real.sqrt ((↑n : ℝ) / 2) * |hermiteFunction (n - 1) x|) ≤
          C * ((2 : ℝ) ^ s + 1) * (1 + ↑n) ^ (s + 1) := by
        -- Rearrange: |x|^k * (a + b) = a' + b' where a' uses IH at n+1, b' at n-1
        have hrearr : |x| ^ k *
            (Real.sqrt ((↑(n + 1) : ℝ) / 2) * |hermiteFunction (n + 1) x| +
             Real.sqrt ((↑n : ℝ) / 2) * |hermiteFunction (n - 1) x|) =
            Real.sqrt ((↑(n + 1) : ℝ) / 2) * (|x| ^ k * |hermiteFunction (n + 1) x|) +
            Real.sqrt ((↑n : ℝ) / 2) * (|x| ^ k * |hermiteFunction (n - 1) x|) := by ring
        rw [hrearr]
        -- Apply IH to each term
        have hb1 := hbound (n + 1) x
        have hb2 := hbound (n - 1) x
        -- Arithmetic bound (tested separately)
        have hsqrt1 : Real.sqrt ((↑(n + 1) : ℝ) / 2) ≤ 1 + (↑n : ℝ) := by
          rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 1 + ↑n)]
          apply Real.sqrt_le_sqrt; push_cast
          have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          nlinarith [sq_nonneg ((n : ℝ) + 1)]
        have hsqrt2 : Real.sqrt ((↑n : ℝ) / 2) ≤ 1 + (↑n : ℝ) := by
          rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ 1 + ↑n)]
          apply Real.sqrt_le_sqrt
          have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          nlinarith [sq_nonneg ((n : ℕ) : ℝ)]
        have hrpow1 : (1 + ↑(n + 1) : ℝ) ^ s ≤
            (2 : ℝ) ^ s * (1 + ↑n) ^ s := by
          rw [← Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2)
            (by positivity : (0 : ℝ) ≤ 1 + ↑n)]
          apply Real.rpow_le_rpow (by positivity) _ hs; push_cast; linarith
        have hrpow2 : (1 + ↑(n - 1) : ℝ) ^ s ≤ (1 + (↑n : ℝ)) ^ s := by
          apply Real.rpow_le_rpow (by positivity) _ hs
          have : (↑(n - 1) : ℝ) ≤ (↑n : ℝ) := Nat.cast_le.mpr (Nat.sub_le n 1)
          linarith
        have hrpow_split : (1 + (↑n : ℝ)) ^ (s + 1) = (1 + ↑n) ^ s * (1 + ↑n) := by
          rw [Real.rpow_add (by positivity : (0:ℝ) < 1 + ↑n), Real.rpow_one]
        calc Real.sqrt ((↑(n + 1) : ℝ) / 2) * (|x| ^ k * |hermiteFunction (n + 1) x|) +
             Real.sqrt ((↑n : ℝ) / 2) * (|x| ^ k * |hermiteFunction (n - 1) x|)
            ≤ Real.sqrt ((↑(n + 1) : ℝ) / 2) * (C * (1 + ↑(n + 1)) ^ s) +
              Real.sqrt ((↑n : ℝ) / 2) * (C * (1 + ↑(n - 1)) ^ s) := by gcongr
          _ ≤ (1 + ↑n) * (C * ((2:ℝ) ^ s * (1 + ↑n) ^ s)) +
              (1 + ↑n) * (C * (1 + ↑n) ^ s) := by gcongr
          _ = C * ((2:ℝ) ^ s + 1) * ((1 + ↑n) ^ s * (1 + ↑n)) := by ring
          _ = C * ((2:ℝ) ^ s + 1) * (1 + ↑n) ^ (s + 1) := by rw [hrpow_split]
      calc |x| ^ k * |Real.sqrt ((↑(n + 1) : ℝ) / 2) * hermiteFunction (n + 1) x +
              Real.sqrt ((↑n : ℝ) / 2) * hermiteFunction (n - 1) x|
          ≤ |x| ^ k * (Real.sqrt ((↑(n + 1) : ℝ) / 2) * |hermiteFunction (n + 1) x| +
              Real.sqrt ((↑n : ℝ) / 2) * |hermiteFunction (n - 1) x|) := by
            gcongr
        _ ≤ C * ((2 : ℝ) ^ s + 1) * (1 + ↑n) ^ (s + 1) := h_main
  | succ m ih =>
    -- Step m → m+1: use deriv_hermiteFunction + iteratedDeriv linearity
    -- iteratedDeriv (m+1) ψ_n = iteratedDeriv m (ψ_n')
    --   = √(n/2) · iteratedDeriv m ψ_{n-1} - √((n+1)/2) · iteratedDeriv m ψ_{n+1}
    obtain ⟨C, s, hC, hs, hbound⟩ := ih
    refine ⟨C * ((2 : ℝ) ^ s + 1), s + 1, by positivity, by linarith, fun n x => ?_⟩
    -- iteratedDeriv (m+1) ψ_n = iteratedDeriv m (deriv ψ_n)
    rw [iteratedDeriv_succ']
    -- deriv ψ_n = √(n/2) · ψ_{n-1} - √((n+1)/2) · ψ_{n+1}
    have hderiv_eq : deriv (hermiteFunction n) =
        fun x => Real.sqrt ((↑n : ℝ) / 2) * hermiteFunction (n - 1) x -
                 Real.sqrt ((↑(n + 1) : ℝ) / 2) * hermiteFunction (n + 1) x := by
      ext x; exact deriv_hermiteFunction n x
    rw [hderiv_eq]
    -- Linearity of iteratedDeriv: split const_mul and sub
    have hcd1 : ContDiffAt ℝ m
        (fun x => Real.sqrt ((↑n : ℝ) / 2) * hermiteFunction (n - 1) x) x :=
      ((hermiteFunction_contDiff (n - 1) m).const_smul (Real.sqrt ((↑n : ℝ) / 2))).contDiffAt
    have hcd2 : ContDiffAt ℝ m
        (fun x => Real.sqrt ((↑(n + 1) : ℝ) / 2) *
          hermiteFunction (n + 1) x) x :=
      ((hermiteFunction_contDiff (n + 1) m).const_smul
        (Real.sqrt ((↑(n + 1) : ℝ) / 2))).contDiffAt
    rw [iteratedDeriv_fun_sub hcd1 hcd2]
    simp only [iteratedDeriv_const_mul_field]
    -- Goal: |x|^k times the norm of the derivative recurrence is bounded by
    --       ≤ C*(2^s+1)*(1+n)^(s+1)
    -- Triangle inequality: ‖a - b‖ ≤ ‖a‖ + ‖b‖
    have h_tri :
        ‖Real.sqrt ((↑n : ℝ) / 2) * iteratedDeriv m (hermiteFunction (n - 1)) x -
          Real.sqrt ((↑(n + 1) : ℝ) / 2) *
            iteratedDeriv m (hermiteFunction (n + 1)) x‖ ≤
          ‖Real.sqrt ((↑n : ℝ) / 2) * iteratedDeriv m (hermiteFunction (n - 1)) x‖ +
          ‖Real.sqrt ((↑(n + 1) : ℝ) / 2) *
            iteratedDeriv m (hermiteFunction (n + 1)) x‖ :=
      norm_sub_le _ _
    calc |x| ^ k * ‖Real.sqrt ((↑n : ℝ) / 2) * iteratedDeriv m (hermiteFunction (n - 1)) x -
            Real.sqrt ((↑(n + 1) : ℝ) / 2) * iteratedDeriv m (hermiteFunction (n + 1)) x‖
        ≤ |x| ^ k *
            (‖Real.sqrt ((↑n : ℝ) / 2) *
                iteratedDeriv m (hermiteFunction (n - 1)) x‖ +
              ‖Real.sqrt ((↑(n + 1) : ℝ) / 2) *
                iteratedDeriv m (hermiteFunction (n + 1)) x‖) := by
          gcongr
      _ = |x| ^ k *
            (Real.sqrt ((↑n : ℝ) / 2) *
                ‖iteratedDeriv m (hermiteFunction (n - 1)) x‖ +
              Real.sqrt ((↑(n + 1) : ℝ) / 2) *
                ‖iteratedDeriv m (hermiteFunction (n + 1)) x‖) := by
          congr 1
          rw [norm_mul, norm_mul, Real.norm_of_nonneg (Real.sqrt_nonneg _),
              Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      _ = Real.sqrt ((↑n : ℝ) / 2) *
            (|x| ^ k * ‖iteratedDeriv m (hermiteFunction (n - 1)) x‖) +
          Real.sqrt ((↑(n + 1) : ℝ) / 2) *
            (|x| ^ k * ‖iteratedDeriv m (hermiteFunction (n + 1)) x‖) := by
          ring
      _ ≤ Real.sqrt ((↑n : ℝ) / 2) * (C * (1 + ↑(n - 1)) ^ s) +
          Real.sqrt ((↑(n + 1) : ℝ) / 2) * (C * (1 + ↑(n + 1)) ^ s) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left (hbound (n - 1) x) (Real.sqrt_nonneg _)
          · exact mul_le_mul_of_nonneg_left (hbound (n + 1) x) (Real.sqrt_nonneg _)
      _ ≤ (1 + ↑n) * (C * (1 + ↑n) ^ s) +
          (1 + ↑n) * (C * ((2:ℝ) ^ s * (1 + ↑n) ^ s)) := by
          apply add_le_add
          · apply mul_le_mul _ _ (by positivity) (by positivity)
            · rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 1 + ↑n)]
              apply Real.sqrt_le_sqrt
              have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
              nlinarith [sq_nonneg ((n : ℕ) : ℝ)]
            · apply mul_le_mul_of_nonneg_left _ (le_of_lt hC)
              apply Real.rpow_le_rpow (by positivity) _ hs
              have : (↑(n - 1) : ℝ) ≤ (↑n : ℝ) := Nat.cast_le.mpr (Nat.sub_le n 1)
              linarith
          · apply mul_le_mul _ _ (by positivity) (by positivity)
            · rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ 1 + ↑n)]
              apply Real.sqrt_le_sqrt; push_cast
              have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
              nlinarith [sq_nonneg ((n : ℝ) + 1)]
            · apply mul_le_mul_of_nonneg_left _ (le_of_lt hC)
              rw [← Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2)
                (by positivity : (0 : ℝ) ≤ 1 + ↑n)]
              apply Real.rpow_le_rpow (by positivity) _ hs; push_cast; linarith
      _ = C * ((2:ℝ) ^ s + 1) * ((1 + ↑n) ^ s * (1 + ↑n)) := by ring
      _ = C * ((2:ℝ) ^ s + 1) * (1 + ↑n) ^ (s + 1) := by
          rw [Real.rpow_add (by positivity : (0:ℝ) < 1 + ↑n), Real.rpow_one]

/-- Schwartz seminorm bound: ‖ψₙ‖_{k,m} grows at most polynomially in n.
    Specifically, there exist constants C, s depending on k, m such that
    ‖ψₙ‖_{k,m} ≤ C · (1 + n)^s.

    This is the key property ensuring that the inclusion between Sobolev-Hermite
    levels is Hilbert-Schmidt. The exponent s depends on the seminorm order:
    for the Schwartz seminorm p_{k,m}(f) = sup_x (1+|x|)^k |f^(m)(x)|,
    we have ‖ψₙ‖_{k,m} ≤ C_{k,m} · (1+n)^{(k+m)/2 + 1/4}.
-/
theorem hermiteFunction_seminorm_bound (k m : ℕ) :
    ∃ (C : ℝ) (s : ℝ), 0 < C ∧ 0 ≤ s ∧
    ∀ n : ℕ, SchwartzMap.seminorm ℝ k m
      (Classical.choose (hermiteFunction_schwartz n)) ≤ C * (1 + n) ^ s := by
  obtain ⟨C, s, hC, hs, hbound⟩ := hermiteFunction_pointwise_bound k m
  refine ⟨C, s, hC, hs, fun n => ?_⟩
  apply SchwartzMap.seminorm_le_bound' ℝ k m
  · positivity
  · intro x
    have hext : ⇑(Classical.choose (hermiteFunction_schwartz n)) = hermiteFunction n :=
      funext (Classical.choose_spec (hermiteFunction_schwartz n))
    simp only [hext]
    exact hbound n x

/-! ## Sobolev-Hermite Spaces

Using the Hermite expansion f = ∑ₙ cₙ ψₙ (where cₙ = ∫ f ψₙ),
the Sobolev-Hermite space of order s is:
  Hˢ = { f : ∑ₙ (1+n)^{2s} |cₙ|² < ∞ }

The inclusion Hˢ⁺¹ ↪ Hˢ is diagonal with eigenvalues (1+n)^{-1},
and ∑ₙ (1+n)^{-2} = π²/6 < ∞, so each inclusion is Hilbert-Schmidt.

The Schwartz space equals ∩ₛ Hˢ, and the Schwartz topology is generated
by the Sobolev-Hermite norms.
-/

/-- The Hilbert-Schmidt sum for the inclusion between Sobolev-Hermite levels:
    ∑_{n=0}^{N-1} (1+n)^{-2s} is bounded for s > 1/2, uniformly in N.
-/
theorem sobolevHermite_hs_sum_bound (s : ℝ) (hs : 1 / 2 < s) :
    ∃ C : ℝ, ∀ N : ℕ, ∑ i ∈ Finset.range N, ((1 + (i : ℝ)) ^ (-2 * s)) ≤ C := by
  -- The series ∑ (1+n)^{-2s} converges when 2s > 1, so partial sums are bounded by tsum
  have hexp : -2 * s < -1 := by linarith
  have hsumm : Summable (fun i : ℕ => (1 + (i : ℝ)) ^ (-2 * s)) := by
    have h := (summable_nat_add_iff (f := fun n => (↑n : ℝ) ^ (-2 * s)) 1).mpr
      (Real.summable_nat_rpow.mpr hexp)
    simp only [Nat.cast_add, Nat.cast_one] at h
    exact h.congr (fun m => by rw [add_comm])
  exact ⟨∑' (i : ℕ), (1 + (i : ℝ)) ^ (-2 * s), fun N =>
    hsumm.sum_le_tsum (Finset.range N) (fun i _ =>
      Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 1 + ↑i) _)⟩

/-! ### Proof of Hermite completeness

We now prove `hermiteFunction_complete` (stated as an axiom above).
Phase 1: Show ∫ f·xᵏ·exp(-x²/2) = 0 using the `mul_x_hermiteFunction` recurrence.
Phase 2-3: Conclude f = 0 via Schwartz density in L².
-/

/-- ψₙ(x) = cₙ · (hermiteR n).eval(x·√2) · exp(-x²/2), so
    (hermiteR n).eval(x·√2) · exp(-x²/2) = cₙ⁻¹ · ψₙ(x).
-/
private lemma hermiteR_eval_mul_gaussian_eq (n : ℕ) (x : ℝ) :
    (hermiteR n).eval (x * Real.sqrt 2) * Real.exp (-(x ^ 2 / 2)) =
    (hermiteFunctionNormConst n)⁻¹ * hermiteFunction n x := by
  unfold hermiteFunction
  rw [show -(x ^ 2 / 2) = -(x ^ 2) / 2 from by ring]
  rw [show hermiteFunctionNormConst n * (hermiteR n).eval (x * Real.sqrt 2) *
    Real.exp (-(x ^ 2) / 2) = hermiteFunctionNormConst n *
    ((hermiteR n).eval (x * Real.sqrt 2) * Real.exp (-(x ^ 2) / 2)) from by ring]
  rw [inv_mul_cancel_left₀ (ne_of_gt (normConst_pos n))]

/-- If f ∈ L² is orthogonal to all ψₙ, then ∫ f · (hermiteR n).eval(x√2) · G = 0. -/
private lemma integral_f_hermiteR_gaussian_zero
    (f : ℝ → ℝ) (_hf : MemLp f 2 volume)
    (horth : ∀ n, ∫ x, f x * hermiteFunction n x = 0)
    (n : ℕ) :
    ∫ x, f x * ((hermiteR n).eval (x * Real.sqrt 2) * Real.exp (-(x ^ 2 / 2))) = 0 := by
  simp_rw [hermiteR_eval_mul_gaussian_eq]
  rw [show (fun x => f x * ((hermiteFunctionNormConst n)⁻¹ * hermiteFunction n x)) =
      fun x => (hermiteFunctionNormConst n)⁻¹ * (f x * hermiteFunction n x) from by ext x; ring]
  rw [integral_const_mul, horth n, mul_zero]

/-- Phase 1: If f ∈ L² is orthogonal to all Hermite functions, then
    ∫ f(x) · x^k · exp(-x²/2) dx = 0 for all k.
-/
private lemma integral_f_xpow_gaussian_zero
    (f : ℝ → ℝ) (hf : MemLp f 2 volume)
    (horth : ∀ n, ∫ x, f x * hermiteFunction n x = 0) :
    ∀ k : ℕ, ∫ x, f x * (x ^ k * Real.exp (-(x ^ 2 / 2))) = 0 := by
  have h_sqrt2_pos : (0 : ℝ) < Real.sqrt 2 :=
    Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  have h_sqrt2_ne : Real.sqrt 2 ≠ 0 := ne_of_gt h_sqrt2_pos
  have h_sqrt2_sq : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have h_pG_memLp : ∀ (p : ℝ[X]),
      MemLp (fun x => p.eval x * Real.exp (-(x ^ 2 / 2))) 2 volume := by
    intro p
    obtain ⟨φ, hφ⟩ := poly_mul_gaussian_schwartz p
    exact MemLp.ae_eq (Filter.Eventually.of_forall hφ) (φ.memLp 2 volume)
  have h_integrable : ∀ (p : ℝ[X]),
      Integrable (fun x => f x * (p.eval x * Real.exp (-(x ^ 2 / 2)))) volume := by
    intro p
    have h_int := L2.integrable_inner (𝕜 := ℝ) (MemLp.toLp f hf) (MemLp.toLp _ (h_pG_memLp p))
    refine h_int.congr ?_
    filter_upwards [MemLp.coeFn_toLp hf, MemLp.coeFn_toLp (h_pG_memLp p)] with x hfx hpGx
    rw [hfx, hpGx, real_inner_eq_re_inner ℝ, RCLike.inner_apply', conj_trivial, RCLike.re_to_real]
  have h_mono_integrable : ∀ (c : ℝ) (i : ℕ),
      Integrable (fun x => c * (f x * (x ^ i * Real.exp (-(x ^ 2 / 2))))) volume := by
    intro c i
    have : (fun x : ℝ => c * (f x * (x ^ i * Real.exp (-(x ^ 2 / 2))))) =
        fun x => c * (f x * ((Polynomial.X ^ i).eval x * Real.exp (-(x ^ 2 / 2)))) := by
      ext x; simp [Polynomial.eval_pow, Polynomial.eval_X]
    rw [this]
    exact (h_integrable (Polynomial.X ^ i)).const_mul c
  have h_hermiteR_zero : ∀ n, ∫ x, f x * ((hermiteR n).eval (x * Real.sqrt 2) *
      Real.exp (-(x ^ 2 / 2))) = 0 := integral_f_hermiteR_gaussian_zero f hf horth
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  set Q := (hermiteR k).comp (Polynomial.C (Real.sqrt 2) * Polynomial.X) with hQ_def
  have hQeval : ∀ x : ℝ, Q.eval x = (hermiteR k).eval (x * Real.sqrt 2) := by
    intro x
    simp [hQ_def, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, mul_comm x (Real.sqrt 2)]
  have hR_natDeg : (hermiteR k).natDegree = k :=
    ((hermite_monic k).natDegree_map (Int.castRingHom ℝ)).trans natDegree_hermite
  have hR_monic : (hermiteR k).Monic := (hermite_monic k).map (Int.castRingHom ℝ)
  have hCX_natDeg : (Polynomial.C (Real.sqrt 2) * Polynomial.X).natDegree = 1 :=
    Polynomial.natDegree_C_mul_X _ h_sqrt2_ne
  have hCX_lead : (Polynomial.C (Real.sqrt 2) * Polynomial.X).leadingCoeff = Real.sqrt 2 :=
    Polynomial.leadingCoeff_C_mul_X (Real.sqrt 2)
  have hCX_ne : (Polynomial.C (Real.sqrt 2) * Polynomial.X).natDegree ≠ 0 := by
    rw [hCX_natDeg]; exact one_ne_zero
  have hQ_natDeg : Q.natDegree = k := by
    rw [hQ_def, Polynomial.natDegree_comp, hCX_natDeg, mul_one, hR_natDeg]
  have hQ_lead : Q.leadingCoeff = Real.sqrt 2 ^ k := by
    rw [hQ_def, Polynomial.leadingCoeff_comp hCX_ne, hR_monic, one_mul,
      hCX_lead, hR_natDeg]
  have h_sqrt2_pow_ne : Real.sqrt 2 ^ k ≠ 0 := pow_ne_zero k h_sqrt2_ne
  set R := Q - Polynomial.C (Real.sqrt 2 ^ k) * Polynomial.X ^ k with hR_def
  have hQR : ∀ x : ℝ, Q.eval x = Real.sqrt 2 ^ k * x ^ k + R.eval x := by
    intro x
    simp [hR_def, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
  have hR_deg : R.natDegree < k ∨ k = 0 := by
    by_cases hk : k = 0
    · right; exact hk
    · left
      rw [hR_def]
      have hmon_deg : (Polynomial.C (Real.sqrt 2 ^ k) * Polynomial.X ^ k).natDegree = k :=
        Polynomial.natDegree_C_mul_X_pow k _ h_sqrt2_pow_ne
      have hmon_lead : (Polynomial.C (Real.sqrt 2 ^ k) * Polynomial.X ^ k).leadingCoeff =
          Real.sqrt 2 ^ k :=
        Polynomial.leadingCoeff_C_mul_X_pow _ _
      have h_cancel : Q.leadingCoeff = (Polynomial.C (Real.sqrt 2 ^ k) * Polynomial.X ^
        k).leadingCoeff := by
        rw [hQ_lead, hmon_lead]
      have hQ_ne : Q ≠ 0 := by
        intro h; exact h_sqrt2_pow_ne (hQ_lead ▸ Polynomial.leadingCoeff_eq_zero.mpr h)
      have hmon_ne : Polynomial.C (Real.sqrt 2 ^ k) * Polynomial.X ^ k ≠ 0 := by
        intro h; exact h_sqrt2_pow_ne (hmon_lead.symm.trans (Polynomial.leadingCoeff_eq_zero.mpr h))
      have h_same_deg : Q.degree = (Polynomial.C (Real.sqrt 2 ^ k) * Polynomial.X ^ k).degree := by
        rw [Polynomial.degree_eq_natDegree hQ_ne, Polynomial.degree_eq_natDegree hmon_ne,
          hQ_natDeg, hmon_deg]
      have h_deg_lt := Polynomial.degree_sub_lt h_same_deg hQ_ne h_cancel
      rw [Polynomial.degree_eq_natDegree hQ_ne, hQ_natDeg] at h_deg_lt
      by_cases hR_zero : Q - Polynomial.C (Real.sqrt 2 ^ k) * Polynomial.X ^ k = 0
      · rw [hR_zero]; exact Nat.pos_of_ne_zero hk
      · rwa [Polynomial.degree_eq_natDegree hR_zero, Nat.cast_lt] at h_deg_lt
  have h_xpow : ∀ x : ℝ, x ^ k = (Real.sqrt 2 ^ k)⁻¹ * (Q.eval x - R.eval x) := by
    intro x
    have hsub : Q.eval x - R.eval x = Real.sqrt 2 ^ k * x ^ k := by linarith [hQR x]
    rw [hsub, inv_mul_cancel_left₀ h_sqrt2_pow_ne]
  have h_rewrite : ∀ x : ℝ,
      f x * (x ^ k * Real.exp (-(x ^ 2 / 2))) =
      (Real.sqrt 2 ^ k)⁻¹ * (f x * (Q.eval x * Real.exp (-(x ^ 2 / 2)))) -
      (Real.sqrt 2 ^ k)⁻¹ * (f x * (R.eval x * Real.exp (-(x ^ 2 / 2)))) := by
    intro x; rw [h_xpow x]; ring
  simp_rw [h_rewrite]
  rw [integral_sub ((h_integrable Q).const_mul _) ((h_integrable R).const_mul _),
    integral_const_mul, integral_const_mul]
  have hQ_zero : ∫ x, f x * (Q.eval x * Real.exp (-(x ^ 2 / 2))) = 0 := by
    simp_rw [hQeval]; exact h_hermiteR_zero k
  rw [hQ_zero, mul_zero, zero_sub]
  suffices hR_zero : ∫ x, f x * (R.eval x * Real.exp (-(x ^ 2 / 2))) = 0 by
    rw [hR_zero, mul_zero, neg_zero]
  rcases hR_deg with hR_lt | hk0
  · have hR_eval : ∀ x : ℝ, R.eval x * Real.exp (-(x ^ 2 / 2)) =
        ∑ i ∈ Finset.range (R.natDegree + 1),
          R.coeff i * (x ^ i * Real.exp (-(x ^ 2 / 2))) := by
      intro x; rw [Polynomial.eval_eq_sum_range x, Finset.sum_mul]; congr 1; ext i; ring
    have h_eq_sum : ∫ x, f x * (R.eval x * Real.exp (-(x ^ 2 / 2))) =
        ∑ i ∈ Finset.range (R.natDegree + 1),
          R.coeff i * ∫ x, f x * (x ^ i * Real.exp (-(x ^ 2 / 2))) := by
      simp_rw [hR_eval, Finset.mul_sum]
      rw [integral_finsetSum _ (fun i _ => ?_)]
      · congr 1; ext i
        rw [show (fun x => f x * (R.coeff i * (x ^ i * Real.exp (-(x ^ 2 / 2))))) =
          fun x => R.coeff i * (f x * (x ^ i * Real.exp (-(x ^ 2 / 2)))) from by ext x; ring,
          integral_const_mul]
      · change Integrable (fun x => f x * (R.coeff i * (x ^ i * Real.exp (-(x ^ 2 / 2))))) volume
        rw [show (fun x => f x * (R.coeff i * (x ^ i * Real.exp (-(x ^ 2 / 2))))) =
          fun x => R.coeff i * (f x * (x ^ i * Real.exp (-(x ^ 2 / 2)))) from by ext x; ring]
        exact h_mono_integrable _ _
    rw [h_eq_sum]
    apply Finset.sum_eq_zero
    intro i hi
    rw [ih i (by have := Finset.mem_range.mp hi; omega), mul_zero]
  · subst hk0
    have hQ_const : Q = Polynomial.C 1 := by
      simp [hQ_def, hermiteR, hermite_zero, Polynomial.map_one, Polynomial.one_comp]
    have hR_zero_poly : R = 0 := by simp [hR_def, hQ_const, pow_zero, mul_one]
    simp [hR_zero_poly]

private lemma integral_f_poly_gaussian_zero
    (f : ℝ → ℝ) (hf : MemLp f 2 volume)
    (horth : ∀ n, ∫ x, f x * hermiteFunction n x = 0)
    (P : ℝ[X]) :
    ∫ x, f x * (P.eval x * Real.exp (-(x ^ 2 / 2))) = 0 := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    have h_split : (fun x => f x * ((p + q).eval x * Real.exp (-(x ^ 2 / 2)))) =
        (fun x => f x * (p.eval x * Real.exp (-(x ^ 2 / 2))) +
                   f x * (q.eval x * Real.exp (-(x ^ 2 / 2)))) := by
      ext x; simp [Polynomial.eval_add, add_mul, mul_add]
    rw [h_split]
    have h_int_poly : ∀ (r : ℝ[X]),
        Integrable (fun x => f x * (r.eval x * Real.exp (-(x ^ 2 / 2)))) volume := by
      intro r
      obtain ⟨φ, hφ⟩ := poly_mul_gaussian_schwartz r
      have hrG : MemLp (fun x => r.eval x * Real.exp (-(x ^ 2 / 2))) 2 volume :=
        MemLp.ae_eq (Filter.Eventually.of_forall hφ) (φ.memLp 2 volume)
      refine (L2.integrable_inner (𝕜 := ℝ) (MemLp.toLp f hf) (MemLp.toLp _ hrG)).congr ?_
      filter_upwards [MemLp.coeFn_toLp hf, MemLp.coeFn_toLp hrG] with x hfx hrGx
      rw [hfx, hrGx, real_inner_eq_re_inner ℝ, RCLike.inner_apply', conj_trivial,
        RCLike.re_to_real]
    rw [integral_add (h_int_poly p) (h_int_poly q), hp, hq, add_zero]
  | monomial k a =>
    simp only [Polynomial.eval_monomial]
    have h_rw : (fun x => f x * (a * x ^ k * Real.exp (-(x ^ 2 / 2)))) =
        fun x => a * (f x * (x ^ k * Real.exp (-(x ^ 2 / 2)))) := by
      ext x; ring
    rw [h_rw, integral_const_mul, integral_f_xpow_gaussian_zero f hf horth k, mul_zero]

/-  Phase 2-3: Conclude f = 0 a.e. from moment vanishing. -/

/-- g := f · exp(-x²/2) is integrable when f ∈ L² (by Cauchy-Schwarz). -/
private lemma integrable_f_mul_gaussian
    (f : ℝ → ℝ) (hf : MemLp f 2 volume) :
    Integrable (fun x => f x * Real.exp (-(x ^ 2 / 2))) volume := by
  obtain ⟨φ, hφ⟩ := poly_mul_gaussian_schwartz (1 : ℝ[X])
  have hG : MemLp (fun x => Real.exp (-(x ^ 2 / 2))) 2 volume := by
    have h1 : MemLp (fun x => (1 : ℝ[X]).eval x * Real.exp (-(x ^ 2 / 2))) 2 volume :=
      MemLp.ae_eq (Filter.Eventually.of_forall hφ) (φ.memLp 2 volume)
    exact MemLp.ae_eq (Filter.Eventually.of_forall (fun x => by simp)) h1
  exact (L2.integrable_inner (𝕜 := ℝ) (MemLp.toLp f hf)
    (MemLp.toLp _ hG)).congr
    (by filter_upwards [MemLp.coeFn_toLp hf, MemLp.coeFn_toLp hG] with x hfx hGx
        rw [hfx, hGx, real_inner_eq_re_inner ℝ, RCLike.inner_apply', conj_trivial,
          RCLike.re_to_real])

/-- |f(x)| * exp(-x²/4) is integrable when f ∈ L², by Cauchy-Schwarz:
    f ∈ L², exp(-x²/4) ∈ L² (since exp(-x²/4)² = exp(-x²/2)).
-/
private lemma integrable_f_mul_half_gaussian
    (f : ℝ → ℝ) (hf : MemLp f 2 volume) :
    Integrable (fun x => f x * Real.exp (-(x ^ 2 / 4))) volume := by
  have hG : MemLp (fun x => Real.exp (-(x ^ 2 / 4))) 2 volume := by
    have hmeas : AEStronglyMeasurable (fun x => Real.exp (-(x ^ 2 / 4))) volume :=
      Measurable.aestronglyMeasurable (by fun_prop)
    rw [memLp_two_iff_integrable_sq hmeas]
    have h_sq : (fun x => Real.exp (-(x ^ 2 / 4)) ^ 2) =
        (fun x => Real.exp (-(1/2) * x ^ 2)) := by
      ext x; rw [sq, ← Real.exp_add]; congr 1; ring
    rw [h_sq]
    exact integrable_exp_neg_mul_sq (by positivity)
  exact (L2.integrable_inner (𝕜 := ℝ) (MemLp.toLp f hf)
    (MemLp.toLp _ hG)).congr
    (by filter_upwards [MemLp.coeFn_toLp hf, MemLp.coeFn_toLp hG] with x hfx hGx
        rw [hfx, hGx, real_inner_eq_re_inner ℝ, RCLike.inner_apply', conj_trivial,
          RCLike.re_to_real])

/-- g(x) * exp(c|x|) is integrable, where g(x) = f(x) * exp(-x²/2), by completing the square:
    |g(x)| * exp(c|x|) = |f(x)| * exp(-x²/2 + c|x|) ≤ exp(c²) * |f(x)| * exp(-x²/4).
-/
private lemma integrable_g_mul_exp_linear
    (f : ℝ → ℝ) (hf : MemLp f 2 volume) (c : ℝ) :
    Integrable (fun x => ‖f x * Real.exp (-(x ^ 2 / 2))‖ * Real.exp (c * |x|)) volume := by
  have hfg := integrable_f_mul_half_gaussian f hf
  -- The bound: ‖g(x)‖ * exp(c|x|) ≤ exp(c²) * |f(x) * exp(-x²/4)|
  -- Use Integrable.mono' with the nonneg bound
  apply (hfg.norm.const_mul (Real.exp (c ^ 2))).mono'
  · apply AEStronglyMeasurable.mul
    · exact (hf.aestronglyMeasurable.mul
        (Measurable.aestronglyMeasurable (by fun_prop))).norm
    · exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards with x
    -- Goal: ‖‖f x * exp(-x²/2)‖ * exp(c*|x|)‖ ≤ exp(c²) * ‖f x * exp(-x²/4)‖
    have hexp1 : (0 : ℝ) < Real.exp (-(x ^ 2 / 2)) := Real.exp_pos _
    have hexp2 : (0 : ℝ) < Real.exp (c * |x|) := Real.exp_pos _
    have hexp3 : (0 : ℝ) < Real.exp (-(x ^ 2 / 4)) := Real.exp_pos _
    simp only [norm_mul, Real.norm_eq_abs, abs_of_pos hexp1, abs_of_pos hexp2,
      abs_of_pos hexp3, abs_abs]
    calc |f x| * Real.exp (-(x ^ 2 / 2)) * Real.exp (c * |x|)
        = |f x| * Real.exp (-(x ^ 2 / 2) + c * |x|) := by
          rw [mul_assoc, ← Real.exp_add]
      _ ≤ |f x| * Real.exp (c ^ 2 + -(x ^ 2 / 4)) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          apply Real.exp_le_exp_of_le
          nlinarith [sq_nonneg (|x| / 2 - c), sq_abs x]
      _ = Real.exp (c ^ 2) * (|f x| * Real.exp (-(x ^ 2 / 4))) := by
          rw [Real.exp_add]; ring

/-- The L^1 Fourier transform of g(x) = f(x) exp(-x^2/2) vanishes when all
    polynomial moments of g are zero. Uses DCT with partial sums of exp.
-/
private lemma fourierIntegral_f_mul_gaussian_eq_zero
    (f : ℝ → ℝ) (hf : MemLp f 2 volume)
    (h_moments : ∀ k : ℕ, ∫ x, f x * (x ^ k * Real.exp (-(x ^ 2 / 2))) = 0) :
    ∀ ξ : ℝ, VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ)
      (fun x => (↑(f x * Real.exp (-(x ^ 2 / 2))) : ℂ)) ξ = 0 := by
  intro ξ
  -- Abbreviations
  set g : ℝ → ℝ := fun x => f x * Real.exp (-(x ^ 2 / 2)) with hg_def
  set g_ℂ : ℝ → ℂ := fun x => (↑(g x) : ℂ) with hg_ℂ_def
  -- Rewrite Fourier integral using exp form
  rw [Real.vector_fourierIntegral_eq_integral_exp_smul]
  -- In ℂ, • is just multiplication
  simp_rw [smul_eq_mul]
  -- Define the complex exponential argument; innerₗ ℝ x ξ = ⟪x,ξ⟫_ℝ
  set z : ℝ → ℂ := fun x => ↑(-2 * π * innerₗ ℝ x ξ) * Complex.I with hz_def
  -- Partial sums: F N x = (∑ k in range N, z(x)^k / k!) * g_ℂ(x)
  let expPartialSum : ℂ → ℕ → ℂ := fun w N =>
    Finset.sum (Finset.range N) fun k => w ^ k / (Nat.factorial k : ℂ)
  let F : ℕ → ℝ → ℂ := fun N x => expPartialSum (z x) N * g_ℂ x
  -- The integrand
  set target : ℝ → ℂ := fun x => Complex.exp (z x) * g_ℂ x with htarget_def
  -- Step 1: F N → target pointwise (from power series of exp)
  have h_pw : ∀ x, Filter.Tendsto (fun N => F N x) Filter.atTop (nhds (target x)) := by
    intro x
    apply Filter.Tendsto.mul_const
    rw [Complex.exp_eq_exp_ℂ]
    exact (NormedSpace.expSeries_div_hasSum_exp (z x)).tendsto_sum_nat
  -- Step 2: Dominating function
  set bound : ℝ → ℝ := fun x => ‖g x‖ * Real.exp (2 * π * |ξ| * |x|) with hbound_def
  -- Helper: innerₗ ℝ x ξ = x * ξ for ℝ
  have inner_eq : ∀ y : ℝ, innerₗ ℝ y ξ = y * ξ := by
    intro y; rw [innerₗ_apply_apply, real_inner_eq_re_inner ℝ, RCLike.inner_apply, conj_trivial,
      RCLike.re_to_real, mul_comm]
  -- Helper: ‖z x‖ = 2π|x||ξ|
  have norm_z : ∀ y : ℝ, ‖z y‖ ≤ 2 * π * |ξ| * |y| := by
    intro y
    simp only [z, Complex.norm_mul, Complex.norm_I, mul_one, Complex.norm_real, inner_eq,
      Real.norm_eq_abs]
    -- Goal: |-2 * π * (y * ξ)| ≤ 2 * π * |ξ| * |y|
    have : |-2 * π * (y * ξ)| = 2 * π * |ξ| * |y| := by
      have h1 : (-2 : ℝ) * π * (y * ξ) = -(2 * π * (y * ξ)) := by ring
      rw [h1, abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π), abs_mul]
      ring
    linarith
  -- Step 3: ‖F N x‖ ≤ bound x
  have h_bound : ∀ N, ∀ᵐ x ∂volume, ‖F N x‖ ≤ bound x := by
    intro N
    filter_upwards with x
    change ‖expPartialSum (z x) N * g_ℂ x‖ ≤ _
    -- ‖a * b‖ ≤ ‖a‖ * ‖b‖, and ‖g_ℂ x‖ = ‖g x‖
    have hgn : ‖g_ℂ x‖ = ‖g x‖ := by simp [g_ℂ, Complex.norm_real, Real.norm_eq_abs]
    -- Partial sum bound
    have h_ps : ‖expPartialSum (z x) N‖ ≤ Real.exp (2 * π * |ξ| * |x|) :=
      calc ‖expPartialSum (z x) N‖
          = ‖∑ k ∈ Finset.range N, z x ^ k / (Nat.factorial k : ℂ)‖ := rfl
        _ ≤ ∑ k ∈ Finset.range N, ‖z x ^ k / (Nat.factorial k : ℂ)‖ := norm_sum_le _ _
        _ = ∑ k ∈ Finset.range N, ‖z x‖ ^ k / (Nat.factorial k) := by
            congr 1; ext k
            rw [norm_div, norm_pow, Complex.norm_natCast]
        _ ≤ Real.exp ‖z x‖ :=
            Real.sum_le_exp_of_nonneg (norm_nonneg _) N
        _ ≤ Real.exp (2 * π * |ξ| * |x|) :=
            Real.exp_le_exp_of_le (norm_z x)
    simp only [hbound_def]
    calc ‖expPartialSum (z x) N * g_ℂ x‖
        ≤ ‖expPartialSum (z x) N‖ * ‖g_ℂ x‖ := norm_mul_le _ _
      _ = ‖expPartialSum (z x) N‖ * ‖g x‖ := by rw [hgn]
      _ ≤ Real.exp (2 * π * |ξ| * |x|) * ‖g x‖ :=
          mul_le_mul_of_nonneg_right h_ps (norm_nonneg _)
      _ = ‖g x‖ * Real.exp (2 * π * |ξ| * |x|) := mul_comm _ _
  -- Step 4: Bound is integrable
  have h_bound_int : Integrable bound volume := by
    have key := integrable_g_mul_exp_linear f hf (2 * π * |ξ|)
    -- key : Integrable (fun x => ‖f x * exp(-x²/2)‖ * exp((2π|ξ|) * |x|))
    -- bound x = ‖g x‖ * exp(2π|ξ| * |x|)
    -- These are the same since g = f * exp(-x²/2) and mul is assoc
    exact key.congr (by filter_upwards with x; simp [hbound_def, g, mul_assoc])
  -- Step 5: F N is measurable
  have hg_ℂ_meas : AEStronglyMeasurable g_ℂ volume :=
    RCLike.continuous_ofReal.comp_aestronglyMeasurable
      (hf.aestronglyMeasurable.mul (Measurable.aestronglyMeasurable (by fun_prop)))
  have hz_cont : Continuous z := by
    simp only [z, inner_eq]
    fun_prop
  have h_summand_cont : ∀ k : ℕ,
      Continuous (fun x : ℝ => z x ^ k / (Nat.factorial k : ℂ)) :=
    fun k => (hz_cont.pow k).div_const _
  have h_meas : ∀ N, AEStronglyMeasurable (F N) volume := by
    intro N
    change AEStronglyMeasurable (fun x => expPartialSum (z x) N * g_ℂ x) volume
    apply AEStronglyMeasurable.mul _ hg_ℂ_meas
    exact Finset.aestronglyMeasurable_fun_sum _ (fun k _ =>
      (h_summand_cont k).measurable.aestronglyMeasurable)
  -- Step 6: Apply DCT
  have h_DCT := tendsto_integral_of_dominated_convergence bound h_meas h_bound_int h_bound
    (Filter.Eventually.of_forall h_pw)
  -- Factor z(x)^k = c^k * ↑(x^k) where c = ↑(-2πξ) * I
  set c : ℂ := ↑(-2 * π * ξ) * Complex.I with hc_def
  have h_zk : ∀ (k : ℕ) (y : ℝ), z y ^ k = c ^ k * ↑(y ^ k) := by
    intro k y
    simp only [z, innerₗ_apply_apply]
    rw [show @inner ℝ ℝ _ y ξ = y * ξ from by
      rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply, conj_trivial, RCLike.re_to_real,
        mul_comm]]
    rw [show (↑(-2 * π * (y * ξ)) : ℂ) * Complex.I = c * ↑y from by
      simp only [c]; push_cast; ring]
    rw [mul_pow, Complex.ofReal_pow]
  -- Integrability helper: each monomial-Gaussian product is integrable
  have h_mono_int : ∀ k : ℕ,
      Integrable (fun y => f y * (y ^ k * Real.exp (-(y ^ 2 / 2)))) volume := by
    intro k
    obtain ⟨φ, hφ⟩ := poly_mul_gaussian_schwartz (Polynomial.X ^ k)
    have hpG : MemLp (fun y => y ^ k * Real.exp (-(y ^ 2 / 2))) 2 volume :=
      MemLp.ae_eq (Filter.Eventually.of_forall (fun y => by simp [hφ y, Polynomial.eval_pow,
        Polynomial.eval_X])) (φ.memLp 2 volume)
    exact (L2.integrable_inner (𝕜 := ℝ) (MemLp.toLp f hf) (MemLp.toLp _ hpG)).congr
      (by filter_upwards [MemLp.coeFn_toLp hf, MemLp.coeFn_toLp hpG] with x hfx hGx
          rw [hfx, hGx, real_inner_eq_re_inner ℝ, RCLike.inner_apply', conj_trivial,
            RCLike.re_to_real])
  -- Helper: rewrite summand as constant times moment integrand
  have h_summand_eq : ∀ k : ℕ, (fun y => z y ^ k / (Nat.factorial k : ℂ) * g_ℂ y) =
      fun y => (c ^ k / (Nat.factorial k : ℂ)) *
        (↑(f y * (y ^ k * Real.exp (-(y ^ 2 / 2)))) : ℂ) := by
    intro k; ext y; rw [h_zk]; simp only [g_ℂ, g]; push_cast; ring
  -- Each summand is integrable
  have h_summand_int : ∀ k : ℕ,
      Integrable (fun y => z y ^ k / (Nat.factorial k : ℂ) * g_ℂ y) volume := by
    intro k; rw [h_summand_eq]; exact (h_mono_int k).ofReal.const_mul _
  -- Step 7: Each ∫ F N = 0
  have h_zero : ∀ N, ∫ x, F N x = 0 := by
    intro N
    change ∫ x, expPartialSum (z x) N * g_ℂ x = 0
    simp only [expPartialSum, Finset.sum_mul]
    rw [integral_finsetSum _ (fun k _ => h_summand_int k)]
    apply Finset.sum_eq_zero
    intro k _
    rw [h_summand_eq]
    calc ∫ y, c ^ k / ↑k.factorial * (↑(f y * (y ^ k * Real.exp (-(y ^ 2 / 2)))) : ℂ)
        = c ^ k / ↑k.factorial * ∫ y, (↑(f y * (y ^ k * Real.exp (-(y ^ 2 / 2)))) : ℂ) :=
          integral_const_mul _ _
      _ = c ^ k / ↑k.factorial * ↑(∫ y, f y * (y ^ k * Real.exp (-(y ^ 2 / 2)))) :=
          congr_arg _ integral_ofReal
      _ = 0 := by rw [h_moments k, Complex.ofReal_zero, mul_zero]
  -- Step 8: Limit of zeros is zero
  exact tendsto_nhds_unique h_DCT
    (tendsto_const_nhds.congr (fun N => (h_zero N).symm))

/-- If ĝ = 0 and φ is smooth compactly supported, then ∫ φ · g = 0.
    Uses Parseval identity and Fourier inversion for Schwartz functions.
-/
private lemma integral_smul_f_mul_gaussian_eq_zero
    (f : ℝ → ℝ) (hf : MemLp f 2 volume)
    (h_moments : ∀ k : ℕ, ∫ x, f x * (x ^ k * Real.exp (-(x ^ 2 / 2))) = 0)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    ∫ x, φ x • (f x * Real.exp (-(x ^ 2 / 2))) = 0 := by
  -- Abbreviations: g(x) = f(x) * exp(-x²/2), g_ℂ = ↑g
  set g : ℝ → ℝ := fun x => f x * Real.exp (-(x ^ 2 / 2)) with hg_def
  set g_ℂ : ℝ → ℂ := fun x => (↑(g x) : ℂ) with hg_ℂ_def
  -- Step 1: Fourier transform of g_ℂ vanishes
  have hFT := fourierIntegral_f_mul_gaussian_eq_zero f hf h_moments
  -- Step 2: g and g_ℂ are integrable
  have hg_int : Integrable g volume := integrable_f_mul_gaussian f hf
  have hg_ℂ_int : Integrable g_ℂ volume := hg_int.ofReal
  -- Step 3: Lift φ to ℂ-valued Schwartz map
  have hφc_ℂ : HasCompactSupport (Complex.ofRealCLM ∘ φ) := hφc.comp_left rfl
  have hφd_ℂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ φ) := by fun_prop
  set ψ : SchwartzMap ℝ ℂ := hφc_ℂ.toSchwartzMap hφd_ℂ
  -- Step 4: η = 𝓕⁻¹ ψ (Schwartz), integrable
  set η : SchwartzMap ℝ ℂ := FourierTransform.fourierInv ψ
  have hη_int : Integrable (η : ℝ → ℂ) volume := η.integrable
  -- Step 5: Fourier inversion: 𝓕(𝓕⁻¹ ψ) = ψ
  have hFF : FourierTransform.fourier η = ψ := FourierTransform.fourier_fourierInv_eq ψ
  -- Step 6: The FT of g_ℂ (as used in Parseval) agrees with hFT
  have hFT_g : ∀ ξ, VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ)
      g_ℂ ξ = 0 := fun ξ => hFT ξ
  -- Step 7: Apply Parseval / self-adjoint identity for L^1 Fourier transform
  have hParseval := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := innerₗ ℝ) (e := Real.fourierChar) (μ := volume) (ν := volume)
    Real.continuous_fourierChar continuous_inner hη_int hg_ℂ_int
  -- Step 8: L.flip = L for innerₗ ℝ, and RHS has 𝓕(g_ℂ) = 0
  simp only [flip_innerₗ, hFT_g, smul_zero, integral_zero] at hParseval
  -- hParseval : ∫ (𝓕 η)(ξ) • g_ℂ(ξ) = 0
  -- Step 9: 𝓕(η) = ψ = ofRealCLM ∘ φ as functions
  have h_FT_eta : ∀ ξ, VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ)
      (η : ℝ → ℂ) ξ = (↑(φ ξ) : ℂ) :=
    fun ξ => congr_fun (congr_arg DFunLike.coe hFF) ξ
  -- Step 10: Rewrite Parseval to get ∫ ↑(φ ξ) • g_ℂ(ξ) = 0
  simp only [h_FT_eta] at hParseval
  -- Step 11: Extract real integral from ℂ integral
  suffices h : (↑(∫ x, φ x • g x) : ℂ) = 0 by exact_mod_cast h
  calc (↑(∫ x, φ x • g x) : ℂ)
      = ∫ x, ((↑(φ x • g x)) : ℂ) := integral_ofReal.symm
    _ = ∫ x, (↑(φ x) : ℂ) • g_ℂ x := by
        congr 1; funext x; simp [hg_ℂ_def, smul_eq_mul, Complex.ofReal_mul]
    _ = 0 := hParseval

private theorem hermiteFunction_complete_proof :
    ∀ f : ℝ → ℝ, MemLp f 2 volume →
    (∀ n, ∫ x, f x * hermiteFunction n x = 0) →
    f =ᵐ[volume] 0 := by
  intro f hf horth
  have h_moments := integral_f_xpow_gaussian_zero f hf horth
  suffices hg : (fun x => f x * Real.exp (-(x ^ 2 / 2))) =ᵐ[volume] 0 by
    filter_upwards [hg] with x hx
    have hexp_pos : Real.exp (-(x ^ 2 / 2)) > 0 := Real.exp_pos _
    exact (mul_eq_zero.mp hx).resolve_right (ne_of_gt hexp_pos)
  have hg_loc : LocallyIntegrable (fun x => f x * Real.exp (-(x ^ 2 / 2))) volume :=
    (integrable_f_mul_gaussian f hf).locallyIntegrable
  exact ae_eq_zero_of_integral_contDiff_smul_eq_zero hg_loc
    (integral_smul_f_mul_gaussian_eq_zero f hf h_moments)

/-- Hermite functions form a complete system in L²(ℝ):
    if ∫ f ψₙ = 0 for all n, then f = 0 a.e.
-/
theorem hermiteFunction_complete :
    ∀ f : ℝ → ℝ, MemLp f 2 volume →
    (∀ n, ∫ x, f x * hermiteFunction n x = 0) →
    f =ᵐ[volume] 0 :=
  hermiteFunction_complete_proof

/-! ## Multi-dimensional Hermite Functions

For ℝᵈ, Hermite functions are tensor products:
  Ψ_α(x) = ∏ᵢ ψ_{αᵢ}(xᵢ)  for multi-index α = (α₁, ..., αd)

These form an ONB of L²(ℝᵈ) and lie in 𝓢(ℝᵈ, ℝ).
-/

-- Multi-index Hermite function for ℝᵈ
-- (Definition deferred until the 1D properties are proved)

/-! ## Schwartz Hermite Expansion (General D, F)

The 5 Hermite infrastructure definitions and theorems (basis, coefficients, expansion,
seminorm growth, coefficient decay) are now proved in `HermiteTensorProduct.lean` via
multi-dimensional tensor products of 1D Hermite functions.

The previous axiom declarations have been removed. Import `HermiteTensorProduct` to
access `schwartzHermiteBasis`, `schwartzHermiteCoeff`, `schwartz_hermite_expansion`,
`schwartz_hermite_seminorm_growth`, and `schwartz_hermite_coefficient_decay`.
-/

end
