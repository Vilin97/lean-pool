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
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Data.Int.Star
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic
import Mathlib.Topology.Separation.CompletelyRegular
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Basic
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Distribution

/-!
# Sobolev Multiplication on the Torus

This file proves Peetre's inequality and the first Sobolev multiplication
theorem: H^s_{2πℤⁿ}(ℝⁿ) is invariant under multiplication by smooth
periodic functions (represented by their rapidly decaying Fourier
coefficient sequences).

## Main results

* `peetre_weight` — Peetre's inequality for the Sobolev weight function
* `sobolev_mul_seq` — First multiplication theorem (sequence side)
* `smoothMulDistrib` — Distribution-side product definition
* `sobolev_mul_dist` — First multiplication theorem (distribution side)
-/

open scoped BigOperators ComplexConjugate
open Complex Real NashEmbedding.Sobolev


noncomputable section

namespace NashEmbedding.Sobolev

variable {n : ℕ}

/-! ## Additional weight lemmas -/

/-
The weight is invariant under negation of the index:
`w_t(-m) = w_t(m)`, since `(-m_i)² = m_i²`.
-/
lemma weight_neg (t : ℝ) (m : Fin n → ℤ) : weight n t (-m) = weight n t m := by
  unfold weight; norm_num;

/-! ## Peetre's inequality -/

/-
The base of the weight satisfies a submultiplicative triangle inequality:
`1 + |m|² ≤ 2(1 + |m - j|²)(1 + |j|²)`.

*Proof.* Each coordinate satisfies `m_i² ≤ 2(m_i - j_i)² + 2j_i²`
(expand `((m_i - j_i) + j_i)²` and use AM–QM). Summing gives
`|m|² ≤ 2|m-j|² + 2|j|²`. Then
`1 + 2a + 2b ≤ 2(1 + a)(1 + b)` for `a, b ≥ 0`
(since `2(1+a)(1+b) = 2 + 2a + 2b + 2ab ≥ 1 + 2a + 2b`).
-/
lemma weight_base_submul (m j : Fin n → ℤ) :
    1 + ∑ i : Fin n, (m i : ℝ) ^ 2 ≤
      2 * (1 + ∑ i : Fin n, ((m i : ℝ) - (j i : ℝ)) ^ 2) *
          (1 + ∑ i : Fin n, (j i : ℝ) ^ 2) := by
  -- Expanding the sum of squares and applying the AM-GM inequality to each term.
  have h_expand : ∀ i, (m i : ℝ) ^ 2 ≤ 2 * (m i - j i) ^ 2 + 2 * (j i) ^ 2 := by
    exact fun i => by linarith [ sq_nonneg ( m i - 2 * j i : ℝ ) ];
  have := Finset.sum_le_sum fun i ( hi : i ∈ Finset.univ ) => h_expand i;
  -- Apply the inequality term by term to the sum.
  norm_cast at *;
  norm_num [ Finset.sum_add_distrib, ← Finset.mul_sum _ _ _ ] at *;
  nlinarith [ show 0 ≤ ∑ i, ( m i - j i ) ^ 2 from Finset.sum_nonneg fun _ _ => sq_nonneg _,
      show 0 ≤ ∑ i, j i ^ 2 from Finset.sum_nonneg fun _ _ => sq_nonneg _ ]

/-
**Peetre's inequality.** For all `s ∈ ℝ` and `m, j ∈ ℤⁿ`:
`weight n s m ≤ 2^|s| · weight n |s| (m - j) · weight n s j`.
-/
lemma peetre_weight (s : ℝ) (m j : Fin n → ℤ) :
    weight n s m ≤ (2 : ℝ) ^ (abs s) * weight n (abs s) (m - j) * weight n s j := by
  by_cases hs : 0 ≤ s <;> simp_all? +decide [ weight ];
  · rw [ abs_of_nonneg hs ];
    rw [ ← Real.mul_rpow, ← Real.mul_rpow ] <;> try positivity;
    apply Real.rpow_le_rpow
      (add_nonneg zero_le_one <| Finset.sum_nonneg fun _ _ => sq_nonneg _) _ hs
    exact_mod_cast weight_base_submul m j
  · have h_submul : (1 + ∑ i, (m i : ℝ) ^ 2) ≥ (1 + ∑ i, ((m i : ℝ) - (j i : ℝ)) ^ 2)⁻¹ * (1 + ∑
      i, (j i : ℝ) ^ 2) / 2 := by
      field_simp;
      have h_submul : (1 + ∑ i, (j i : ℝ) ^ 2) ≤ 2 * (1 + ∑ i, ((m i : ℝ) - (j i : ℝ)) ^ 2) * (1
          + ∑ i, (m i : ℝ) ^ 2) := by
        have := weight_base_submul j m
        exact this.trans ( by rw [ show ( ∑ i : Fin n, ( j i - m i : ℝ ) ^ 2 ) = ∑ i : Fin n, (
            m i - j i : ℝ ) ^ 2 by exact Finset.sum_congr rfl fun _ _ => by ring ] );
      linarith;
    refine le_trans ( Real.rpow_le_rpow_of_nonpos ?_ h_submul hs.le ) ?_;
    · exact div_pos ( mul_pos ( inv_pos.mpr ( add_pos_of_pos_of_nonneg zero_lt_one (
        Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ) ) ( add_pos_of_pos_of_nonneg zero_lt_one (
        Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ) ) zero_lt_two;
    · rw [ Real.div_rpow ( by positivity ) ( by positivity ), Real.mul_rpow ( by positivity ) (
        by positivity ), Real.inv_rpow ( by positivity ) ];
      rw [ abs_of_neg hs, Real.rpow_neg ( by positivity ), Real.rpow_neg ( by positivity ) ];
          ring_nf; norm_num

/-! ## Translation invariance of tsum -/

/-
Translation invariance: `∑' m, f(m - i) = ∑' m, f(m)`.
-/
lemma tsum_sub_shift
    {f : (Fin n → ℤ) → ℝ}  (i : Fin n → ℤ) :
    ∑' m, f (m - i) = ∑' m, f m := by
  conv_rhs => rw [ ← Equiv.tsum_eq ( Equiv.subRight i ) ];
  rfl

/-! ## Young's convolution inequality (ℓ¹ ⊛ ℓ²) -/

/-
Summability of the convolution at each point (for non-negative real sequences).
-/
lemma conv_abs_summable
    {f g : (Fin n → ℤ) → ℝ}
    (hf_nn : ∀ m, 0 ≤ f m) (hg_nn : ∀ m, 0 ≤ g m)
    (hf : Summable f) (hg_sq : Summable (fun m => g m ^ 2))
    (m : Fin n → ℤ) :
    Summable (fun i => f i * g (m - i)) := by
  refine .of_nonneg_of_le ( fun i => mul_nonneg ( hf_nn i ) ( hg_nn _ ) ) ( fun i => ?_ ) (
      hf.mul_right ( Real.sqrt ( ∑' m, g m ^ 2 ) ) );
  exact mul_le_mul_of_nonneg_left ( Real.le_sqrt_of_sq_le ( Summable.le_tsum ( hg_sq ) ( m - i )
      ( fun _ _ => sq_nonneg _ ) ) ) ( hf_nn i )

/-
**Young's convolution inequality** for ℓ¹ ⊛ ℓ² on `ℤⁿ`.
If `f ∈ ℓ¹` and `g ∈ ℓ²` are non-negative, then `f ⊛ g ∈ ℓ²` with
`‖f ⊛ g‖_{ℓ²}² ≤ ‖f‖_{ℓ¹}² · ‖g‖_{ℓ²}²`.
-/
theorem young_conv_sq_bound
    {f g : (Fin n → ℤ) → ℝ}
    (hf_nn : ∀ m, 0 ≤ f m) (hg_nn : ∀ m, 0 ≤ g m)
    (hf : Summable f) (hg_sq : Summable (fun m => g m ^ 2)) :
    Summable (fun m => (∑' i, f i * g (m - i)) ^ 2) ∧
    ∑' m, (∑' i, f i * g (m - i)) ^ 2 ≤
      (∑' i, f i) ^ 2 * ∑' m, g m ^ 2 := by
  have h_conv_abs_summable : ∀ m, Summable (fun i => f i * g (m - i)) := by
    intro m
    apply conv_abs_summable hf_nn hg_nn hf hg_sq m;
  have h_cauchy_schwarz : ∀ m, (∑' i, f i * g (m - i)) ^ 2 ≤ (∑' i, f i) * (∑' i, f i * g (m -
      i) ^ 2) := by
    intro m;
    have h_cauchy_schwarz : ∀ (u v : (Fin n → ℤ) → ℝ), (∀ i, 0 ≤ u i) → (∀ i, 0 ≤ v i) →
        Summable (fun i => u i) → Summable (fun i => u i * v i ^ 2) → (∑' i, u i * v i) ^ 2 ≤
        (∑' i, u i) * (∑' i, u i * v i ^ 2) := by
      intros u v hu hv hu_sum hv_sum
      have h_cauchy_schwarz : ∀ (N : Finset (Fin n → ℤ)), (∑ i ∈ N, u i * v i) ^ 2 ≤ (∑ i ∈ N, u
          i) * (∑ i ∈ N, u i * v i ^ 2) := by
        intro N;
        have h_cauchy_schwarz : ∀ (u v : (Fin n → ℤ) → ℝ), (∀ i, 0 ≤ u i) → (∀ i, 0 ≤ v i) → (∑
            i ∈ N, u i * v i) ^ 2 ≤ (∑ i ∈ N, u i) * (∑ i ∈ N, u i * v i ^ 2) := by
          intros u v hu hv
          have h_cauchy_schwarz : ∀ (i j : Fin n → ℤ), u i * v i * u j * v j ≤ (u i * u j * v i
              ^ 2 + u i * u j * v j ^ 2) / 2 := by
            intro i j
            nlinarith only [sq_nonneg (v i - v j), mul_nonneg (hu i) (hu j),
              mul_nonneg (hu i) (hv j), mul_nonneg (hv i) (hu j), mul_nonneg (hv i) (hv j)]
          have h_cauchy_schwarz : ∑ i ∈ N, ∑ j ∈ N, u i * v i * u j * v j ≤ ∑ i ∈ N, ∑ j ∈ N, (u
              i * u j * v i ^ 2 + u i * u j * v j ^ 2) / 2 := by
            exact Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => h_cauchy_schwarz i j;
          convert h_cauchy_schwarz using 1 <;> norm_num [ Finset.sum_add_distrib, ←
              Finset.mul_sum _ _ _, ← Finset.sum_div ]; ring;
          · simp +decide only [sq, Finset.mul_sum _ _ _, mul_comm, mul_left_comm];
          · simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, mul_assoc, mul_comm,
              mul_left_comm, Finset.sum_add_distrib ]; ring;
            simp +decide [ mul_assoc, Finset.mul_sum _ _ _ ]; ring;
        exact h_cauchy_schwarz u v hu hv;
      have h_cauchy_schwarz : Filter.Tendsto (fun N : Finset (Fin n → ℤ) => (∑ i ∈ N, u i * v i)
          ^ 2) Filter.atTop (nhds ((∑' i, u i * v i) ^ 2)) := by
        refine Filter.Tendsto.pow ?_ _;
        refine Summable.hasSum ?_;
        have h_cauchy_schwarz : Summable (fun i => u i * v i) := by
          have h_cauchy_schwarz : ∀ i, u i * v i ≤ u i + u i * v i ^ 2 := by
            exact fun i => by nlinarith only [ hu i, hv i, sq_nonneg ( v i - 1 ) ];
          exact Summable.of_nonneg_of_le ( fun i => mul_nonneg ( hu i ) ( hv i ) )
              h_cauchy_schwarz ( hu_sum.add hv_sum );
        exact h_cauchy_schwarz;
      exact le_of_tendsto_of_tendsto' h_cauchy_schwarz ( Filter.Tendsto.mul ( hu_sum.hasSum ) (
          hv_sum.hasSum ) ) fun N => by aesop;
    apply h_cauchy_schwarz f (fun i => g (m - i)) hf_nn (fun i => hg_nn (m - i)) hf;
    refine .of_nonneg_of_le ( fun i => mul_nonneg ( hf_nn i ) ( sq_nonneg _ ) ) ( fun i =>
        mul_le_mul_of_nonneg_left ( show g ( m - i ) ^ 2 ≤ ∑' j, g j ^ 2 from ?_ ) ( hf_nn i ) )
        ( hf.mul_right _ );
    exact Summable.le_tsum ( hg_sq ) ( m - i ) ( fun _ _ => sq_nonneg _ );
  have h_fubini : ∑' m, ∑' i, f i * g (m - i) ^ 2 = ∑' i, f i * ∑' m, g (m - i) ^ 2 := by
    rw [ Summable.tsum_comm ];
    · simp +decide only [← tsum_mul_left];
    · have h_fubini : Summable (fun p : (Fin n → ℤ) × (Fin n → ℤ) => f p.1 * g p.2 ^ 2) := by
        exact .of_norm <| by simpa using Summable.mul_norm ( hf.norm ) ( hg_sq.norm );
      convert h_fubini.comp_injective ( show Function.Injective ( fun p : ( Fin n → ℤ ) × ( Fin
          n → ℤ ) => ( p.1, p.2 - p.1 ) ) from fun p q h => by aesop ) using 1
      funext p; simp [Function.uncurry, Function.comp]
  have h_translation_invariance : ∀ i, ∑' m, g (m - i) ^ 2 = ∑' m, g m ^ 2 := by
    exact fun i => Equiv.tsum_eq ( Equiv.subRight i ) fun m => g m ^ 2;
  simp_all? +decide [ tsum_mul_right, tsum_mul_left ];
  refine ⟨ ?_, ?_ ⟩;
  · refine Summable.of_nonneg_of_le ( fun m => sq_nonneg _ ) ( fun m => h_cauchy_schwarz m ) ?_;
    refine Summable.mul_left _ ?_;
    contrapose! h_fubini;
    rw [ tsum_eq_zero_of_not_summable h_fubini ]; norm_num;
    constructor;
    · intro H;
      have h_zero : ∀ m, f m = 0 := by
        exact fun m => le_antisymm ( le_trans ( Summable.le_tsum ( hf ) m ( fun _ _ => hf_nn _ )
            ) H.le ) ( hf_nn m );
      exact h_fubini <| by simpa [ h_zero ] using summable_zero;
    · intro H; simp_all +decide [ tsum_eq_zero_of_not_summable ] ;
      -- Since $\sum' m, g m ^ 2 = 0$, we have $g m = 0$ for all $m$.
      have h_g_zero : ∀ m, g m = 0 := by
        exact fun m => sq_eq_zero_iff.mp ( le_antisymm ( le_trans ( Summable.le_tsum ( hg_sq ) m
            ( fun _ _ => sq_nonneg _ ) ) H.le ) ( sq_nonneg _ ) );
      exact h_fubini <| by simpa [ h_g_zero ] using summable_zero;
  · refine le_trans ( Summable.tsum_le_tsum h_cauchy_schwarz ?_ ?_ ) ?_;
    · refine Summable.of_nonneg_of_le ( fun m => sq_nonneg _ ) ( fun m => h_cauchy_schwarz m ) ?_;
      refine Summable.mul_left _ ?_;
      contrapose! h_fubini;
      rw [ tsum_eq_zero_of_not_summable h_fubini ]; norm_num;
      constructor;
      · intro H;
        have h_zero : ∀ m, f m = 0 := by
          exact fun m => le_antisymm ( le_trans ( Summable.le_tsum ( hf ) m ( fun _ _ => hf_nn _
              ) ) H.le ) ( hf_nn m );
        exact h_fubini <| by simpa [ h_zero ] using summable_zero;
      · intro H; simp_all +decide [ tsum_eq_zero_of_not_summable ] ;
        -- Since $\sum' m, g m ^ 2 = 0$, we have $g m = 0$ for all $m$.
        have h_g_zero : ∀ m, g m = 0 := by
          exact fun m => sq_eq_zero_iff.mp ( le_antisymm ( le_trans ( Summable.le_tsum ( hg_sq )
              m ( fun _ _ => sq_nonneg _ ) ) H.le ) ( sq_nonneg _ ) );
        exact h_fubini <| by simpa [ h_g_zero ] using summable_zero;
    · refine Summable.mul_left _ ?_;
      contrapose! h_fubini;
      rw [ tsum_eq_zero_of_not_summable h_fubini ]; norm_num;
      constructor <;> intro h <;> simp_all +decide [ tsum_eq_zero_of_not_summable ];
      · -- Since $f$ is non-negative and its sum is zero, $f$ must be zero everywhere.
        have h_f_zero : ∀ m, f m = 0 := by
          exact fun m => le_antisymm ( le_trans ( Summable.le_tsum ( hf ) m ( fun _ _ => hf_nn _
              ) ) h.le ) ( hf_nn m );
        exact h_fubini <| by simpa [ h_f_zero ] using summable_zero;
      · -- Since $\sum' m, g m ^ 2 = 0$, we have $g m = 0$ for all $m$.
        have h_g_zero : ∀ m, g m = 0 := by
          exact fun m => sq_eq_zero_iff.mp ( le_antisymm ( le_trans ( Summable.le_tsum ( hg_sq )
              m ( fun _ _ => sq_nonneg _ ) ) h.le ) ( sq_nonneg _ ) );
        exact h_fubini <| by simpa [ h_g_zero ] using summable_zero;
    · rw [ tsum_mul_left, h_fubini, sq, mul_assoc ]

/-! ## First Sobolev multiplication theorem (sequence side) -/

/-
**First Sobolev multiplication theorem (sequence side).**
If `a ∈ ℓ²_{(s)}(ℤⁿ)` and the sequence `b` satisfies the weighted ℓ¹ condition
`∑ ‖b_i‖ · (1 + |i|²)^{|s|/2} < ∞`, then the convolution `b ⊛ a` belongs to
`ℓ²_{(s)}(ℤⁿ)` and satisfies the norm bound
`‖b ⊛ a‖_{(s)} ≤ 2^{|s|/2} · (∑ ‖b_i‖ · (1 + |i|²)^{|s|/2}) · ‖a‖_{(s)}`.
-/
theorem sobolev_mul_seq {s : ℝ}
    {a : (Fin n → ℤ) → ℂ} (ha : MemSobolev n s a)
    {b : (Fin n → ℤ) → ℂ}
    (hb : Summable (fun i => ‖b i‖ * weight n (abs s / 2) i)) :
    MemSobolev n s (fun m => ∑' i, b i * a (m - i)) ∧
    Real.sqrt (sobolevNormSq n s (fun m => ∑' i, b i * a (m - i))) ≤
      (2 : ℝ) ^ (abs s / 2) * (∑' i, ‖b i‖ * weight n (abs s / 2) i) *
      Real.sqrt (sobolevNormSq n s a) := by
  have h_peetre : ∀ m : Fin n → ℤ, (weight n s m) * ‖∑' i, b i * a (m - i)‖ ^ 2 ≤ (2 ^ (|s| / 2
      : ℝ)) ^ 2 * (∑' i, ‖b i‖ * (weight n (|s| / 2) i) * Real.sqrt (weight n s (m - i)) * ‖a (m
      - i)‖) ^ 2 := by
    intro m
    have h_peetre_step : Real.sqrt (weight n s m) * ‖∑' i, b i * a (m - i)‖ ≤ 2 ^ (|s| / 2 : ℝ)
        * ∑' i, ‖b i‖ * (weight n (|s| / 2) i) * Real.sqrt (weight n s (m - i)) * ‖a (m - i)‖ := by
      have h_peetre_step : ∀ i : Fin n → ℤ, Real.sqrt (weight n s m) * ‖b i * a (m - i)‖ ≤ 2 ^
          (|s| / 2 : ℝ) * ‖b i‖ * (weight n (|s| / 2) i) * Real.sqrt (weight n s (m - i)) * ‖a
          (m - i)‖ := by
        intro i
        have h_peetre_step : Real.sqrt (weight n s m) ≤ 2 ^ (|s| / 2 : ℝ) * weight n (|s| / 2) i
            * Real.sqrt (weight n s (m - i)) := by
          have h_peetre : weight n s m ≤ (2 : ℝ) ^ (|s|) * weight n (|s|) i * weight n s (m - i)
              := by
            convert peetre_weight s m ( m - i ) using 1; ring;
          convert Real.sqrt_le_sqrt h_peetre using 1;
          have htwo : (2 : ℝ) ^ |s| = (2 ^ (|s| / 2)) ^ 2 := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
            ring
          have hweight : weight n |s| i = (weight n (|s| / 2) i) ^ 2 := by
            unfold weight
            rw [← Real.rpow_natCast, ← Real.rpow_mul
              (add_nonneg zero_le_one <| Finset.sum_nonneg fun _ _ => sq_nonneg _)]
            ring
          rw [htwo, hweight]
          rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
            Real.sqrt_sq (by positivity), Real.sqrt_sq (weight_nonneg _ _)]
        convert mul_le_mul_of_nonneg_right h_peetre_step ( norm_nonneg ( b i * a ( m - i ) ) )
            using 1
        all_goals (first | rfl | (norm_num; ring))
      by_cases h : Summable ( fun i => b i * a ( m - i ) ) <;> simp_all +decide only [ge_iff_le];
      · refine le_trans ( mul_le_mul_of_nonneg_left ( norm_tsum_le_tsum_norm ?_ ) (
          Real.sqrt_nonneg _ ) ) ?_;
        · exact h.norm;
        · rw [ ← tsum_mul_left ];
          rw [ ← tsum_mul_left ];
          refine Summable.tsum_le_tsum ?_ ?_ ?_;
          · intro i
            simpa only [mul_assoc] using h_peetre_step i
          · exact Summable.mul_left _ ( by simpa using h.norm );
          · refine Summable.mul_left _ ?_;
            have h_summable : Summable (fun i => ‖b i‖ * (weight n (|s| / 2) i) * Real.sqrt
                (weight n s (m - i)) * ‖a (m - i)‖) := by
              have h_sqrt : ∀ i, Real.sqrt (weight n s (m - i)) * ‖a (m - i)‖ ≤ Real.sqrt
                  (sobolevNormSq n s a) := by
                intro i
                have h_sqrt : weight n s (m - i) * ‖a (m - i)‖ ^ 2 ≤ sobolevNormSq n s a := by
                  exact Summable.le_tsum ( ha ) ( m - i ) ( fun _ _ => mul_nonneg (
                      weight_nonneg _ _ ) ( sq_nonneg _ ) );
                exact Real.le_sqrt_of_sq_le ( by nlinarith [ Real.mul_self_sqrt ( show 0 ≤
                    weight n s ( m - i ) by exact weight_nonneg _ _ ) ] )
              have h_summable : Summable (fun i => ‖b i‖ * (weight n (|s| / 2) i) * Real.sqrt
                  (sobolevNormSq n s a)) := by
                exact hb.mul_right _;
              apply Summable.of_nonneg_of_le
                (fun i => mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _)
                  (weight_nonneg _ _)) (Real.sqrt_nonneg _)) (norm_nonneg _)) _ h_summable
              intro i
              have hbweight := mul_nonneg (norm_nonneg (b i)) (weight_nonneg (|s| / 2) i)
              nlinarith [h_sqrt i]
            simpa only [ mul_assoc ] using h_summable;
      · rw [tsum_eq_zero_of_not_summable h, norm_zero, mul_zero]
        exact mul_nonneg (Real.rpow_nonneg zero_le_two _) (tsum_nonneg fun _ =>
          mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) (weight_nonneg _ _))
            (Real.sqrt_nonneg _)) (norm_nonneg _))
    convert pow_le_pow_left₀ ( by positivity ) h_peetre_step 2 using 1
    all_goals (first
      | rfl
      | (rw [ mul_pow, Real.sq_sqrt <| weight_nonneg _ _ ])
      | ring)
  have h_young : Summable (fun m => (∑' i, ‖b i‖ * (weight n (|s| / 2) i) * Real.sqrt (weight n
      s (m - i)) * ‖a (m - i)‖) ^ 2) ∧
    ∑' m, (∑' i, ‖b i‖ * (weight n (|s| / 2) i) * Real.sqrt (weight n s (m - i)) * ‖a (m - i)‖)
        ^ 2 ≤
    (∑' i, ‖b i‖ * (weight n (|s| / 2) i)) ^ 2 * ∑' m, (weight n s m) * ‖a m‖ ^ 2 := by
      have := @young_conv_sq_bound n ( fun i => ‖b i‖ * weight n ( |s| / 2 ) i ) ( fun m =>
          Real.sqrt ( weight n s m ) * ‖a m‖ ) ?_ ?_ ?_ ?_;
      · simp_all +decide [ mul_assoc, mul_pow, Real.sq_sqrt ( weight_nonneg _ _ ) ];
      · exact fun m => mul_nonneg ( norm_nonneg _ ) ( weight_nonneg _ _ );
      · exact fun m => mul_nonneg ( Real.sqrt_nonneg _ ) ( norm_nonneg _ );
      · exact hb;
      · simp_all? +decide [ mul_pow, Real.sq_sqrt ( weight_nonneg _ _ ) ];
        exact ha;
  have h_summable : Summable (fun m => (weight n s m) * ‖∑' i, b i * a (m - i)‖ ^ 2) := by
    exact Summable.of_nonneg_of_le ( fun m => mul_nonneg ( weight_nonneg _ _ ) ( sq_nonneg _ ) )
        h_peetre ( h_young.1.mul_left _ );
  have h_sqrt : Real.sqrt (∑' m, (weight n s m) * ‖∑' i, b i * a (m - i)‖ ^ 2) ≤ Real.sqrt ((2 ^
      (|s| / 2 : ℝ)) ^ 2 * (∑' i, ‖b i‖ * (weight n (|s| / 2) i)) ^ 2 * ∑' m, (weight n s m) *
      ‖a m‖ ^ 2) := by
    refine Real.sqrt_le_sqrt ?_;
    refine le_trans ( Summable.tsum_le_tsum h_peetre h_summable ?_ ) ?_;
    · exact Summable.mul_left _ h_young.1;
    · rw [ tsum_mul_left ]; nlinarith [ show 0 ≤ ( 2 ^ ( |s| / 2 ) : ℝ ) ^ 2 by positivity ];
  refine ⟨h_summable, h_sqrt.trans_eq ?_⟩
  unfold sobolevNormSq
  rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq (by
      positivity), Real.sqrt_sq (tsum_nonneg fun _ => mul_nonneg (norm_nonneg _) (weight_nonneg
      _ _))]

/-! ## Distribution-side multiplication -/

/-- Multiplication of a distribution `φ ∈ X_n^*` by a sequence `b : ℤⁿ → ℂ`
of Fourier coefficients (representing a smooth periodic function).
The product is defined via convolution on the Fourier side:
`(b · φ)^_m = ∑_i b_i · φ̂_{m-i}`. -/
def smoothMulDistrib (n : ℕ) (b : (Fin n → ℤ) → ℂ) (φ : TrigPolyDual n) :
    TrigPolyDual n :=
  seqToDual n (fun m => ∑' i, b i * fourierCoeffDistrib φ (m - i))

/-- The Fourier coefficients of the product distribution are the convolution
of `b` with the Fourier coefficients of `φ`. -/
lemma fourierCoeffDistrib_smoothMulDistrib (b : (Fin n → ℤ) → ℂ) (φ : TrigPolyDual n) :
    fourierCoeffDistrib (smoothMulDistrib n b φ) =
      fun m => ∑' i, b i * fourierCoeffDistrib φ (m - i) :=
  fourierCoeffDistrib_seqToDual _

/-- **First Sobolev multiplication theorem (distribution side).**
If `φ ∈ H^s_{2πℤⁿ}(ℝⁿ)` and `b` has weighted ℓ¹ decay, then the product
`b · φ ∈ H^s_{2πℤⁿ}(ℝⁿ)` with the norm bound:
`‖b · φ‖_{(s)} ≤ 2^{|s|/2} · (∑ |b_m| (1+|m|²)^{|s|/2}) · ‖φ‖_{(s)}`. -/
theorem sobolev_mul_dist {s : ℝ}
    {b : (Fin n → ℤ) → ℂ}
    (hb : Summable (fun i => ‖b i‖ * weight n (abs s / 2) i))
    {φ : TrigPolyDual n} (hφ : MemSobolevDistrib n s φ) :
    MemSobolevDistrib n s (smoothMulDistrib n b φ) ∧
    Real.sqrt (sobolevNormSqDistrib n s (smoothMulDistrib n b φ)) ≤
      (2 : ℝ) ^ (abs s / 2) *
        (∑' i, ‖b i‖ * weight n (abs s / 2) i) *
      Real.sqrt (sobolevNormSqDistrib n s φ) := by
  -- Transport via fourierCoeffDistrib_smoothMulDistrib and sobolev_mul_seq.
  have key := sobolev_mul_seq hφ hb
  unfold MemSobolevDistrib sobolevNormSqDistrib
  rw [fourierCoeffDistrib_smoothMulDistrib]
  exact key

end NashEmbedding.Sobolev

end
