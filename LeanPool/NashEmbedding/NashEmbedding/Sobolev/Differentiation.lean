/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wiygul
-/
module


/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Claude Fable 5 (Anthropic), Claude Opus 4.7 (Anthropic)
  — at the request of David Wiygul
-/
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Tactic
public import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Basic
public import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Summability

/-!
# Term-by-term differentiation of Fourier series

If `∑ |bₘ| < ∞` and `∑ |mⱼ| |bₘ| < ∞`, then the Fourier series
`f(θ) = ∑ bₘ eₘ(θ)` is continuously differentiable with
`∂f/∂θⱼ(θ) = ∑ i mⱼ bₘ eₘ(θ)`.
-/

@[expose] public section

open scoped BigOperators
open NashEmbedding.Sobolev Complex

noncomputable
section

namespace NashEmbedding.Sobolev

variable {n : ℕ}

/-- The formal partial derivative coefficients: for direction `j`, the coefficient
of `eₘ` in `∂f/∂θⱼ` is `i · mⱼ · bₘ`. -/
def partialCoeff (j : Fin n) (b : (Fin n → ℤ) → ℂ) (m : Fin n → ℤ) : ℂ :=
  Complex.I * (m j : ℂ) * b m

/-
Norm bound for partial coefficients.
-/
lemma norm_partialCoeff (j : Fin n) (b : (Fin n → ℤ) → ℂ) (m : Fin n → ℤ) :
    ‖partialCoeff j b m‖ = |(m j : ℝ)| * ‖b m‖ := by
  unfold partialCoeff; norm_num;

/-
**Term-by-term differentiation.**
Under absolute summability of `b` and `m ↦ |mⱼ| |bₘ|`,
the function `θ ↦ ∑' m, b m * eₘ(θ)` has partial derivative in direction `j`
equal to `∑' m, i mⱼ bₘ eₘ(θ)` at each `θ`.
-/
theorem hasDerivAt_fourierSeries_partial
    (hn : 0 < n)
    {b : (Fin n → ℤ) → ℂ}
    (hb : Summable (fun m => ‖b m‖))
    (j : Fin n)
    (hbj : Summable (fun m => ‖partialCoeff j b m‖))
    (θ : Fin n → ℝ) :
    HasDerivAt (fun t : ℝ => ∑' m : Fin n → ℤ,
        b m * fourierExp n m (Function.update θ j t))
      (∑' m : Fin n → ℤ, partialCoeff j b m * fourierExp n m θ)
      (θ j) := by
  rw [ hasDerivAt_iff_tendsto_slope_zero ];
  -- Apply the fact that the derivative of a sum is the sum of the derivatives.
  have h_deriv_sum : Filter.Tendsto (fun t : ℝ => ∑' m : Fin n → ℤ, (b m * (fourierExp n m
      (Function.update θ j (θ j + t)) - fourierExp n m (Function.update θ j (θ j)))) / t)
      (nhdsWithin 0 {0}ᶜ) (nhds (∑' m : Fin n → ℤ, partialCoeff j b m * fourierExp n m θ)) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun m => ‖partialCoeff j b m‖)
      ?_ ?_ ?_
    · exact hbj;
    · intro m;
      have h_deriv : HasDerivAt (fun t : ℝ => fourierExp n m (Function.update θ j t)) (Complex.I
          * (m j : ℂ) * fourierExp n m θ) (θ j) := by
        unfold fourierExp;
        simp +decide only [Function.update_apply, mul_ite, Finset.sum_ite, Finset.filter_eq',
          Finset.mem_univ, ↓reduceIte, Finset.sum_singleton, Finset.filter_ne',
          Finset.sum_erase_eq_sub, ofReal_add, ofReal_mul, ofReal_intCast, ofReal_sub, ofReal_sum];
        convert HasDerivAt.comp ( θ j ) ( Complex.hasDerivAt_exp _ ) ( HasDerivAt.const_mul
            Complex.I <| HasDerivAt.add ( HasDerivAt.const_mul ( m j : ℂ ) <| hasDerivAt_id _ |>
            HasDerivAt.ofReal_comp ) <| hasDerivAt_const _ ((∑ x, ((m x : ℂ) * (θ x : ℂ))) - (m
            j : ℂ) * (θ j : ℂ)) ) using 1
        all_goals (first
          | rfl
          | (simp only [Pi.add_apply, id_eq]; push_cast; ring))
      convert h_deriv.tendsto_slope_zero.const_mul ( b m ) using 2 <;> norm_num [
          div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, partialCoeff ];
    · -- We'll use the fact that |exp(i * x) - exp(i * y)| ≤ |x - y| for any real numbers x and y.
      have h_exp_diff : ∀ x y : ℝ, ‖Complex.exp (Complex.I * x) - Complex.exp (Complex.I * y)‖ ≤
          |x - y| := by
        -- Use the fact that $|e^{ix} - e^{iy}| = 2 |\sin((x - y) / 2)|$.
        have h_exp_diff : ∀ x y : ℝ, ‖Complex.exp (Complex.I * x) - Complex.exp (Complex.I * y)‖
            = 2 * |Real.sin ((x - y) / 2)| := by
          norm_num [ Complex.norm_def, Complex.normSq, Complex.exp_re, Complex.exp_im ];
          intro x y; rw [ Real.sqrt_eq_iff_mul_self_eq ] <;> norm_num <;> ring <;> norm_num [
              Real.sin_sq, Real.cos_sq ] <;> ring;
          · rw [ Real.cos_sub ]; ring;
          · nlinarith [ sq_nonneg ( Real.cos x - Real.cos y ), sq_nonneg ( Real.sin x - Real.sin
              y ), Real.cos_sq' x, Real.cos_sq' y ];
        -- Use the fact that $|\sin(z)| \leq |z|$ for any real number $z$.
        have h_sin_bound : ∀ z : ℝ, |Real.sin z| ≤ |z| := by
          exact fun z => Real.abs_sin_le_abs;
        grind +revert;
      filter_upwards [ self_mem_nhdsWithin ] with t ht k; simp_all +decide only [fourierExp,
        partialCoeff, Function.update_eq_self, Complex.norm_div, Complex.norm_mul, norm_real,
        Real.norm_eq_abs];
      rw [ div_le_iff₀ ( abs_pos.mpr ht ) ];
      convert mul_le_mul_of_nonneg_left ( h_exp_diff ( ∑ x : Fin n, ( k x : ℝ ) * (
          Function.update θ j ( θ j + t ) x ) ) ( ∑ x : Fin n, ( k x : ℝ ) * ( θ x ) ) ) (
          norm_nonneg ( b k ) ) using 1; norm_num [ Finset.sum_update_of_mem ]; ring;
      simp +decide [ Function.update_apply]; ring;
      simp +decide [Finset.sum_ite, Finset.filter_eq', Finset.filter_ne']; ring;
      norm_num [ mul_assoc, mul_comm, mul_left_comm, abs_mul ];
  convert h_deriv_sum using 2;
  rw [ ← Summable.tsum_sub ];
  · simp +decide [ div_eq_inv_mul, mul_sub,   mul_left_comm, ← tsum_mul_left ];
  · exact Summable.of_norm <| by simpa [ norm_fourierExp ] using hb;
  · exact .of_norm <| by simpa [ norm_fourierExp ] using hb;

end NashEmbedding.Sobolev

end
