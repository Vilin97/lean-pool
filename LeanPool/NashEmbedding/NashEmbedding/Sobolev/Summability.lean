/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wiygul
-/

/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Claude Fable 5 (Anthropic), Claude Opus 4.7 (Anthropic)
  — at the request of David Wiygul
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Tactic
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Basic

/-!
# Summability and Cauchy–Schwarz for Sobolev sequences

This file contains:
* The summability of `(1 + |m|²)^{-s}` over `ℤⁿ` for `2s > n` (integral test).
* The Cauchy–Schwarz bound: if `a ∈ ℓ²_(s)` and `2s > n`, then `∑ |aₘ| < ∞`
  with the bound `∑ |aₘ| ≤ C · ‖a‖_(s)`.
* Absolute and uniform convergence of Fourier series under ℓ¹ summability.
-/

open scoped BigOperators
open NashEmbedding.Sobolev

noncomputable section

namespace NashEmbedding.Sobolev

variable {n : ℕ}

/-! ## Summability of the weight -/

/-
The series `∑_{m ∈ ℤⁿ} (1 + |m|²)^{-s}` converges when `2s > n`.
-/
theorem summable_weight_neg {s : ℝ} (hn : 0 < n) (hs : (n : ℝ) < 2 * s) :
    Summable (fun m : Fin n → ℤ => weight n (-s) m) := by
  -- AM–GM bounds the n-dimensional weight `(1 + |m|²)^{-s}` above by a product
  -- of one-dimensional factors `∏ᵢ (1 + mᵢ²)^{-s/n}`, reducing multivariate
  -- summability to the one-dimensional series `∑_{k ∈ ℤ} (1 + k²)^{-s/n}`,
  -- which converges since `2s > n`, i.e. `s/n > 1/2`.
  have h_comparison : ∀ m : Fin n → ℤ, 0 < s → (1 + (∑ i : Fin n, ((m i) : ℝ) ^ 2)) ^ (-s) ≤ (∏
      i : Fin n, (1 + (m i : ℝ) ^ 2) ^ (-s / n)) := by
    intro m hs_pos
    have h_prod : (∏ i : Fin n, (1 + (m i : ℝ) ^ 2)) ^ (1 / n : ℝ) ≤ 1 + (∑ i : Fin n, ((m i) :
        ℝ) ^ 2) := by
      have := @Real.geom_mean_le_arith_mean;
      specialize this Finset.univ ( fun _i => 1 ) ( fun _i => ( 1 + ( m _i : ℝ ) ^ 2 ) );
          norm_num at *;
      refine (this hn (fun _ => by positivity)).trans ?_
      rw [div_le_iff₀ (by positivity)]
      norm_num [Finset.sum_add_distrib]
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hsum0 : 0 ≤ ∑ i : Fin n, (m i : ℝ) ^ 2 :=
        Finset.sum_nonneg fun _ _ => sq_nonneg _
      nlinarith
    rw [ Real.finsetProd_rpow _ _ fun i _ => by positivity ];
    rw [neg_div, Real.rpow_neg (by positivity),
      Real.rpow_neg (Finset.prod_nonneg fun _ _ => by positivity)]
    apply inv_anti₀ (Real.rpow_pos_of_pos (Finset.prod_pos fun _ _ => by positivity) _)
    convert Real.rpow_le_rpow (by positivity) h_prod (le_of_lt hs_pos) using 1
    rw [← Real.rpow_mul (Finset.prod_nonneg fun _ _ => by positivity)]
    ring
  -- Since \(s > n/2\), we have \(s/n > 1/2\), and thus \(\sum_{m \in \mathbb{Z}} (1 +
  -- m^2)^{-s/n}\) converges.
  have h_summable_one_dim : Summable (fun m : ℤ => (1 + (m : ℝ) ^ 2) ^ (-s / n)) := by
    have h_summable_one_dim : Summable (fun m : ℕ => (1 + (m : ℝ) ^ 2) ^ (-s / n)) := by
      have h_summable_one_dim : Summable (fun m : ℕ => (m : ℝ) ^ (-2 * s / n)) := by
        exact Real.summable_nat_rpow.2 ( by rw [ div_lt_iff₀ ( by positivity ) ]; linarith );
      rw [ ← summable_nat_add_iff 1 ] at *;
      refine .of_nonneg_of_le ( fun m => Real.rpow_nonneg ( by positivity ) _ ) ( fun m => ?_ )
          h_summable_one_dim;
      rw [ show ( -2 * s / n : ℝ ) = -s / n + -s / n by ring, Real.rpow_add ] <;> norm_num <;>
          try positivity;
      rw [← Real.mul_rpow (by positivity) (by positivity)]
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith)
        (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))
    have h_split : ∑' m : ℤ, (1 + (m : ℝ) ^ 2) ^ (-s / n) = ∑' m : ℕ, (1 + (m : ℝ) ^ 2) ^ (-s /
        n) + ∑' m : ℕ, (1 + ((-m - 1) : ℝ) ^ 2) ^ (-s / n) := by
      rw [ ← Equiv.tsum_eq ( Equiv.intEquivNat.symm ) ];
      rw [ ← tsum_even_add_odd ] <;> norm_num [ Equiv.intEquivNat ];
      · norm_num [ Equiv.intEquivNatSumNat ];
        exact tsum_congr fun m => by ring;
      · convert h_summable_one_dim using 1; rfl
      · convert h_summable_one_dim.comp_injective ( show Function.Injective ( fun k : ℕ => k + 1
          ) from fun a b h => by simpa using h ) using 1
        ext; simp [Equiv.intEquivNatSumNat];
        congr 2; ring
    contrapose! h_split;
    rw [ tsum_eq_zero_of_not_summable h_split ];
    exact ne_of_lt ( add_pos_of_pos_of_nonneg ( lt_of_lt_of_le ( by positivity ) (
        Summable.le_tsum ( h_summable_one_dim ) 0 fun _ _ => by positivity ) ) ( tsum_nonneg fun
        _ => by positivity ) );
  refine .of_nonneg_of_le ( fun m => ?_ ) ( fun m => ?_ ) ( show Summable ( fun m : Fin n → ℤ =>
      ∏ i : Fin n, ( 1 + ( m i : ℝ ) ^ 2 ) ^ ( -s / n ) ) from ?_ );
  · exact Real.rpow_nonneg ( add_nonneg zero_le_one ( Finset.sum_nonneg fun _ _ => sq_nonneg _ )
      ) _;
  · exact h_comparison m ( by linarith [ show ( n : ℝ ) ≥ 1 by norm_cast ] );
  · have h_prod_summable : ∀ {k : ℕ}, Summable (fun m : Fin k → ℤ => ∏ i : Fin k, (1 + (m i : ℝ)
      ^ 2) ^ (-s / n)) := by
      intro k
      induction k with
      | zero => exact ⟨_, hasSum_fintype _⟩
      | succ k ih =>
        simp only [Fin.prod_univ_succ]
        have h_prod_summable : Summable (fun m : ℤ × (Fin k → ℤ) => (1 + (m.1 : ℝ) ^ 2) ^ (-s /
          n) * ∏ i : Fin k, (1 + (m.2 i : ℝ) ^ 2) ^ (-s / n)) := by
          exact .of_norm <| by simpa using Summable.mul_norm ( h_summable_one_dim.norm ) (
              ih.norm );
        convert h_prod_summable.comp_injective ( show Function.Injective ( fun m : Fin ( k + 1 )
            → ℤ => ( m 0, fun i => m ( Fin.succ i ) ) ) from fun m m' h => by simpa [
            funext_iff, Fin.forall_fin_succ ] using h ) using 1
        rfl
    exact h_prod_summable

/-! ## Cauchy–Schwarz bound -/

/-
**Cauchy–Schwarz for Sobolev sequences.** If `2s > n` and `a ∈ ℓ²_(s)`,
then `∑ |aₘ|` converges, i.e., `a ∈ ℓ¹(ℤⁿ)`.
-/
theorem summable_norm_of_memSobolev {s : ℝ} (hn : 0 < n)
    (hs : (n : ℝ) < 2 * s)
    {a : (Fin n → ℤ) → ℂ} (ha : MemSobolev n s a) :
    Summable (fun m : Fin n → ℤ => ‖a m‖) := by
  -- Since $\sum_m (1 + |m|^2)^{-s}$ converges, we can apply the Cauchy-Schwarz inequality.
  have h_cauchy_schwarz : Summable (fun m : (Fin n → ℤ) => (Real.sqrt (weight n (-s) m)) *
      (Real.sqrt (weight n s m * ‖a m‖ ^ 2))) := by
    refine .of_nonneg_of_le ( fun m => mul_nonneg ( Real.sqrt_nonneg _ ) ( Real.sqrt_nonneg _ )
        ) ( fun m => ?_ ) ( ( show Summable fun m : Fin n → ℤ => weight n ( -s ) m + weight n s m
        * ‖a m‖ ^ 2 from ?_ ) );
    · nlinarith only [sq_nonneg (Real.sqrt (weight n (-s) m) -
          Real.sqrt (weight n s m * ‖a m‖ ^ 2)),
        Real.mul_self_sqrt (le_of_lt (weight_pos (-s) m)),
        Real.mul_self_sqrt (mul_nonneg (le_of_lt (weight_pos s m)) (sq_nonneg ‖a m‖))]
    · exact Summable.add ( summable_weight_neg hn hs ) ha;
  convert h_cauchy_schwarz using 2;
  unfold weight; norm_num [ mul_assoc, mul_comm, mul_left_comm, Real.sqrt_mul, Real.sqrt_sq,
      le_of_lt ( weight_pos _ _ ) ];
  rw [ ← Real.sqrt_mul ( by positivity ), ← Real.rpow_add ( by positivity ), add_neg_cancel,
      Real.rpow_zero, Real.sqrt_one, mul_one ]

/-
**Cauchy–Schwarz bound.** If `2s > n` and `a ∈ ℓ²_(s)`, then
`(∑ |aₘ|)² ≤ (∑ (1+|m|²)^{-s}) · ‖a‖²_(s)`.
-/
theorem tsum_norm_sq_le {s : ℝ} (hn : 0 < n)
    (hs : (n : ℝ) < 2 * s)
    {a : (Fin n → ℤ) → ℂ} (ha : MemSobolev n s a) :
    (∑' m : Fin n → ℤ, ‖a m‖) ^ 2 ≤
      (∑' m : Fin n → ℤ, weight n (-s) m) * sobolevNormSq n s a := by
  -- Apply the Cauchy-Schwarz inequality to the sums.
  have h_cauchy_schwarz : ∀ (u v : (Fin n → ℤ) → ℝ), (Summable (fun m => u m ^ 2)) → (Summable
      (fun m => v m ^ 2)) → (∑' m, u m * v m) ^ 2 ≤ (∑' m, u m ^ 2) * (∑' m, v m ^ 2) := by
    intros u v hu hv
    have h_cauchy_schwarz : ∀ (N : Finset (Fin n → ℤ)), (∑ m ∈ N, u m * v m) ^ 2 ≤ (∑ m ∈ N, u m
        ^ 2) * (∑ m ∈ N, v m ^ 2) := by
      exact fun N => Finset.sum_mul_sq_le_sq_mul_sq N u v;
    have h_cauchy_schwarz : Filter.Tendsto (fun N : Finset (Fin n → ℤ) => (∑ m ∈ N, u m * v m) ^
        2) Filter.atTop (nhds ((∑' m, u m * v m) ^ 2)) := by
      refine Filter.Tendsto.pow ?_ _;
      refine Summable.hasSum ?_;
      refine .of_norm ?_;
      refine Summable.of_nonneg_of_le (fun m => abs_nonneg _) ?_ (hu.add hv)
      intro m
      rw [Real.norm_eq_abs, abs_mul]
      nlinarith only [sq_nonneg (|u m| - |v m|),
        abs_mul_abs_self (u m), abs_mul_abs_self (v m)]
    exact le_of_tendsto_of_tendsto' h_cauchy_schwarz ( Filter.Tendsto.mul ( hu.hasSum ) (
        hv.hasSum ) ) fun N => by aesop;
  convert h_cauchy_schwarz ( fun m => Real.sqrt ( weight n ( -s ) m ) ) ( fun m => Real.sqrt (
      weight n s m ) * ‖a m‖ ) _ _ using 1;
  · norm_num [ ← mul_assoc, ← Real.sqrt_mul ( weight_nonneg _ _ ), weight_mul ];
    norm_num [ weight_zero ];
  · simp +decide only [sobolevNormSq, Real.sq_sqrt (weight_nonneg _ _), mul_pow];
  · simpa only [ Real.sq_sqrt ( weight_nonneg _ _ ) ] using summable_weight_neg hn hs;
  · simpa only [ MemSobolev, mul_pow, Real.sq_sqrt ( weight_nonneg _ _ ) ] using ha

/-! ## Uniform convergence of Fourier series -/

/-
If `∑ |aₘ| < ∞`, the Fourier series `∑ aₘ eₘ(θ)` converges
absolutely and uniformly on `ℝⁿ`.
-/
theorem hasSum_fourierSeries
    {a : (Fin n → ℤ) → ℂ} (ha : Summable (fun m => ‖a m‖))
    (θ : Fin n → ℝ) :
    HasSum (fun m => a m * fourierExp n m θ) (∑' m, a m * fourierExp n m θ) := by
  refine Summable.hasSum ?_;
  exact .of_norm <| by simpa [ norm_fourierExp ] using ha;

/-
Under ℓ¹ summability, the Fourier series defines a continuous function.
-/
theorem continuous_fourierSeries
    {a : (Fin n → ℤ) → ℂ}
    (ha : Summable (fun m => ‖a m‖)) :
    Continuous (fun θ : Fin n → ℝ => ∑' m : Fin n → ℤ, a m * fourierExp n m θ) := by
  -- Since the partial sums are continuous and converge uniformly, the limit is continuous.
  have h_cont : ∀ m, Continuous (fun θ : (Fin n) → ℝ => a m * fourierExp n m θ) := by
    exact fun m => continuous_const.mul <| Complex.continuous_exp.comp <| by continuity;
  refine continuous_tsum (u := fun m => ‖a m‖) h_cont ha ?_
  intro m x
  simp +decide [norm_fourierExp]

/-
The sup norm of the Fourier series is bounded by the ℓ¹ norm.
-/
theorem sup_norm_fourierSeries_le
    {a : (Fin n → ℤ) → ℂ}
    (ha : Summable (fun m => ‖a m‖))
    (θ : Fin n → ℝ) :
    ‖∑' m : Fin n → ℤ, a m * fourierExp n m θ‖ ≤ ∑' m : Fin n → ℤ, ‖a m‖ := by
  convert norm_tsum_le_tsum_norm ?_ using 1;
  · unfold fourierExp; norm_num [ Complex.norm_exp ] ;
  · simpa [ norm_fourierExp ] using ha

end NashEmbedding.Sobolev

end
