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
public import Mathlib.Tactic
public import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Basic
public import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Summability
public import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Distribution
public import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Multiplication

/-!
# Second Sobolev Multiplication Theorem

This file proves that H^s_{2πℤⁿ}(ℝⁿ) is closed under pointwise
multiplication when 2s > n, with the norm bound
‖u·v‖²_{(s)} ≤ K_tilde_{n,s} · ‖u‖²_{(s)} · ‖v‖²_{(s)}.

## Main results

* `seqConv` — convolution of two sequences on ℤⁿ
* `sobolevMulDistrib` — product of two distributions
* `sobolevEmbedConstSq` — the squared Sobolev embedding constant
* `mt2Const` — the constant for the second multiplication theorem
* `second_multiplication_theorem_seq` — sequence-side result
* `second_multiplication_theorem` — distribution-side result
-/

@[expose] public section

open scoped BigOperators ComplexConjugate
open Complex Real NashEmbedding.Sobolev


noncomputable
section

namespace NashEmbedding.Sobolev

variable {n : ℕ}

/-! ## Definitions -/

/-- Convolution of two sequences on ℤⁿ. -/
noncomputable def seqConv
    (a b : (Fin n → ℤ) → ℂ) (m : Fin n → ℤ) : ℂ :=
  ∑' i, a i * b (m - i)

/-- Product of two distributions via Fourier coefficient convolution. -/
noncomputable def sobolevMulDistrib (u v : TrigPolyDual n) : TrigPolyDual n :=
  seqToDual n (seqConv (fourierCoeffDistrib u) (fourierCoeffDistrib v))

/-- The squared Sobolev embedding constant C²_{n,s} = ∑_j (1+|j|²)^{-s}. -/
noncomputable def sobolevEmbedConstSq (n : ℕ) (s : ℝ) : ℝ :=
  ∑' (j : Fin n → ℤ), weight n (-s) j

/-- The constant K_tilde_{n,s} = 4 · 2^{2s} · C²_{n,s}. -/
noncomputable def mt2Const (n : ℕ) (s : ℝ) : ℝ :=
  4 * (2 : ℝ) ^ (2 * s) * sobolevEmbedConstSq n s

/-! ## Helper lemmas -/

/-
The half-power weight inequality:
`(1 + |i+j|²)^{s/2} ≤ 2^s · ((1+|i|²)^{s/2} + (1+|j|²)^{s/2})` for `s ≥ 0`.
-/
lemma half_power_weight_ineq {s : ℝ} (hs : 0 ≤ s) (i j : Fin n → ℤ) :
    weight n (s / 2) (i + j) ≤
      (2 : ℝ) ^ s * (weight n (s / 2) i + weight n (s / 2) j) := by
  unfold weight;
  -- Apply the inequality $(a+b)^2 \leq 2(a^2 + b^2)$ to each term in the sum.
  have h_ineq : ∀ k : Fin n, ((i k + j k) : ℝ) ^ 2 ≤ 2 * ((i k : ℝ) ^ 2 + (j k : ℝ) ^ 2) := by
    exact fun k => by linarith [ sq_nonneg ( i k - j k : ℝ ) ];
  -- Apply the inequality $(a+b)^2 \leq 2(a^2 + b^2)$ to the sum.
  have h_sum_ineq : (1 + ∑ k, ((i k + j k) : ℝ) ^ 2) ≤ 2 * (1 + ∑ k, (i k : ℝ) ^ 2) + 2 * (1 + ∑
      k, (j k : ℝ) ^ 2) := by
    have := Finset.sum_le_sum fun k ( _ : k ∈ Finset.univ ) => h_ineq k; norm_num [
        Finset.sum_add_distrib, two_mul, add_assoc ] at this ⊢; linarith;
  -- Apply the inequality $(a+b)^{s/2} \leq 2^{s/2} (a^{s/2} + b^{s/2})$ to the sum.
  have h_sum_ineq_pow : (2 * (1 + ∑ k, (i k : ℝ) ^ 2) + 2 * (1 + ∑ k, (j k : ℝ) ^ 2)) ^ (s / 2)
      ≤ 2 ^ (s / 2) * ((1 + ∑ k, (i k : ℝ) ^ 2) ^ (s / 2) + (1 + ∑ k, (j k : ℝ) ^ 2) ^ (s / 2))
      * 2 ^ (s / 2) := by
    have h_sum_ineq_pow : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → (a + b) ^ (s / 2) ≤ 2 ^ (s / 2) * (a ^ (s /
        2) + b ^ (s / 2)) := by
      intros a b ha hb
      have h_ineq : (a + b) ^ (s / 2) ≤ (2 * max a b) ^ (s / 2) := by
        exact Real.rpow_le_rpow (by positivity)
          (by linarith [le_max_left a b, le_max_right a b]) (by positivity)
      rw [ Real.mul_rpow ( by positivity ) ( by positivity ) ] at h_ineq;
      exact h_ineq.trans (mul_le_mul_of_nonneg_left (by
        rw [max_def_lt]
        split_ifs <;> linarith [Real.rpow_nonneg ha (s / 2), Real.rpow_nonneg hb (s / 2)])
        (by positivity))
    convert h_sum_ineq_pow ( 2 * ( 1 + ∑ k, ( i k : ℝ ) ^ 2 ) ) ( 2 * ( 1 + ∑ k, ( j k : ℝ ) ^ 2
        ) ) ( by positivity ) ( by positivity ) using 1
    all_goals (first
      | rfl
      | (ring; done)
      | (rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2) (by positivity),
          Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2) (by positivity)]; ring))
  convert le_trans _ h_sum_ineq_pow using 1
  all_goals (first
    | rfl
    | (rw [ mul_right_comm, ← Real.rpow_add ] <;> norm_num)
    | (exact Real.rpow_le_rpow ( add_nonneg zero_le_one <| Finset.sum_nonneg fun _ _ =>
        sq_nonneg _ ) (by exact_mod_cast h_sum_ineq) ( by positivity )))

/-
`weight n s m = weight n (s/2) m * weight n (s/2) m`.
-/
lemma weight_half_mul (s : ℝ) (m : Fin n → ℤ) :
    weight n s m = weight n (s / 2) m * weight n (s / 2) m := by
  rw [weight_mul]
  congr 1
  ring

/-
Summability of `‖a m‖^2` when `a ∈ ℓ²_{(s)}` and `s ≥ 0`.
-/
lemma summable_normSq_of_memSobolev {s : ℝ} (hs : 0 ≤ s)
    {a : (Fin n → ℤ) → ℂ} (ha : MemSobolev n s a) :
    Summable (fun m => ‖a m‖ ^ 2) := by
  exact ha.of_nonneg_of_le ( fun m => sq_nonneg _ ) fun m => le_mul_of_one_le_left ( sq_nonneg _
      ) ( by exact le_trans ( by norm_num [ weight_zero ] ) ( weight_mono hs m ) )

/-
Summability of the convolution at each point when both sequences
are in `ℓ²_{(s)}` and `2s > n`.
-/
lemma seqConv_summable {s : ℝ} (hn : 0 < n) (hs : (n : ℝ) < 2 * s)
    {a b : (Fin n → ℤ) → ℂ} (ha : MemSobolev n s a) (hb : MemSobolev n s b)
    (m : Fin n → ℤ) : Summable (fun i => a i * b (m - i)) := by
  have ha_norm := summable_norm_of_memSobolev hn hs ha
  have hb_norm := summable_norm_of_memSobolev hn hs hb
  apply Summable.of_norm
  simpa only [norm_mul] using Summable.of_nonneg_of_le
    (fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun i => mul_le_mul_of_nonneg_left
      (hb_norm.le_tsum (m - i) (fun _ _ => norm_nonneg _)) (norm_nonneg _))
    (ha_norm.mul_right _)

/-
Squared norm through half-weight:
`sobolevNormSq n s a = ∑' m, (weight n (s/2) m * ‖a m‖) ^ 2`.
-/
lemma sobolevNormSq_half_weight (s : ℝ) (a : (Fin n → ℤ) → ℂ) :
    sobolevNormSq n s a = ∑' m, (weight n (s / 2) m * ‖a m‖) ^ 2 := by
  exact tsum_congr fun m => by rw [ mul_pow, weight_half_mul ]; ring;

/-- Young's bound applied to the weighted convolution (one direction):
For `f ∈ ℓ¹` nonneg, `g ∈ ℓ²` nonneg,
`∑' m, (∑' i, f i * g (m - i))^2 ≤ (∑' i, f i)^2 * ∑' m, g m^2`.
This is just `young_conv_sq_bound` but we record the specific instantiation. -/
lemma young_l1_l2_bound
    {f g : (Fin n → ℤ) → ℝ}
    (hf_nn : ∀ m, 0 ≤ f m) (hg_nn : ∀ m, 0 ≤ g m)
    (hf : Summable f) (hg_sq : Summable (fun m => g m ^ 2)) :
    Summable (fun m => (∑' i, f i * g (m - i)) ^ 2) ∧
    ∑' m, (∑' i, f i * g (m - i)) ^ 2 ≤
      (∑' i, f i) ^ 2 * ∑' m, g m ^ 2 :=
  young_conv_sq_bound hf_nn hg_nn hf hg_sq

/-! ## Intermediate lemmas for the second multiplication theorem -/

/-
Summability of the α⋅|b| convolution term at each point.
-/
lemma summable_alpha_abs_b {s : ℝ}
    {a b : (Fin n → ℤ) → ℂ}
    (ha : MemSobolev n s a) (hb_l1 : Summable (fun m => ‖b m‖))
    (m : Fin n → ℤ) :
    Summable (fun i => (weight n (s / 2) i * ‖a i‖) * ‖b (m - i)‖) := by
  have h_conv : Summable (fun j => ‖b j‖ * (weight n (s / 2) (m - j) * ‖a (m - j)‖)) := by
    have h_f : Summable (fun j => ‖b j‖) := hb_l1
    have h_g : Summable (fun j => (weight n (s / 2) j * ‖a j‖) ^ 2) := by
      convert ha using 2; ring;
      unfold MemSobolev; norm_num [ weight ] ; ring;
      exact iff_of_eq (by
        congr
        ext
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        ring)
    have h_conv : Summable (fun j => ‖b j‖ * (weight n (s / 2) (m - j) * ‖a (m - j)‖)) := by
      have h_conv : Summable (fun j => ‖b j‖ ^ 2) := by
        exact Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun j => by
          have hbound := h_f.le_tsum j (fun _ _ => norm_nonneg _)
          nlinarith only [norm_nonneg (b j), hbound]) (h_f.mul_left _)
      have h_conv : Summable (fun j => (weight n (s / 2) (m - j) * ‖a (m - j)‖) ^ 2) := by
        exact h_g.comp_injective ( sub_right_injective )
      exact Summable.of_nonneg_of_le
        (fun j => mul_nonneg (norm_nonneg _) (mul_nonneg (weight_nonneg _ _) (norm_nonneg _)))
        (fun j => by
          nlinarith only [sq_nonneg (‖b j‖ - weight n (s / 2) (m - j) * ‖a (m - j)‖),
            norm_nonneg (b j),
            mul_nonneg (weight_nonneg (s / 2) (m - j)) (norm_nonneg (a (m - j)))])
        (Summable.add ‹Summable fun j => ‖b j‖ ^ 2› h_conv)
    convert h_conv using 1
  convert h_conv.comp_injective ( show Function.Injective ( fun i => m - i ) from fun x y hxy =>
      by simpa using hxy ) using 2
  all_goals (first | rfl | simp +decide [ mul_assoc, mul_comm ])

/-
Summability of the |a|⋅β convolution term at each point.
-/
lemma summable_abs_a_beta {s : ℝ}
    {a b : (Fin n → ℤ) → ℂ}
    (ha_l1 : Summable (fun m => ‖a m‖)) (hb : MemSobolev n s b)
    (m : Fin n → ℤ) :
    Summable (fun i => ‖a i‖ * (weight n (s / 2) (m - i) * ‖b (m - i)‖)) := by
  convert conv_abs_summable _ _ _ _ m using 1;
  rotate_left;
  · exact fun m => ‖a m‖
  · exact fun m => weight n ( s / 2 ) m * ‖b m‖
  · grind +splitImp;
  · exact fun m => mul_nonneg ( weight_nonneg _ _ ) ( norm_nonneg _ );
  · exact ha_l1;
  · convert hb using 2; ring;
    unfold MemSobolev; norm_num [ weight ] ; ring;
    exact iff_of_eq (by
      congr
      ext
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      ring)
  · rfl

/-
Unsquared pointwise bound: weight n (s/2) m * ‖seqConv a b m‖ ≤ 2^s * (T1 + T2).
-/
lemma seqConv_unsquared_bound {s : ℝ} (hs : 0 ≤ s)
    {a b : (Fin n → ℤ) → ℂ}
    (ha_l1 : Summable (fun m => ‖a m‖))
    (hb_l1 : Summable (fun m => ‖b m‖))
    (ha : MemSobolev n s a) (hb : MemSobolev n s b)
    (m : Fin n → ℤ) :
    weight n (s / 2) m * ‖seqConv a b m‖ ≤
      (2 : ℝ) ^ s *
        (∑' i, (weight n (s / 2) i * ‖a i‖) * ‖b (m - i)‖ +
         ∑' i, ‖a i‖ * (weight n (s / 2) (m - i) * ‖b (m - i)‖)) := by
  refine le_trans ( mul_le_mul_of_nonneg_left ( norm_tsum_le_tsum_norm ?_ ) ( weight_nonneg _ _
      ) ) ?_;
  · simp +zetaDelta only [Complex.norm_mul] at *;
    exact .of_nonneg_of_le ( fun i => mul_nonneg ( norm_nonneg _ ) ( norm_nonneg _ ) ) ( fun i
        => mul_le_mul_of_nonneg_left ( show ‖b ( m - i )‖ ≤ ∑' j, ‖b j‖ from Summable.le_tsum (
        hb_l1 ) ( m - i ) ( fun _ _ => norm_nonneg _ ) ) ( norm_nonneg _ ) ) ( ha_l1.mul_right _ );
  · rw [ ← Summable.tsum_add ];
    · rw [ ← tsum_mul_left, ← tsum_mul_left ];
      refine Summable.tsum_le_tsum ?_ ?_ ?_;
      · intro i
        have h_ineq : weight n (s / 2) m ≤ 2 ^ s * (weight n (s / 2) i + weight n (s / 2) (m -
            i)) := by
          convert half_power_weight_ineq hs i ( m - i ) using 1; ring;
        convert mul_le_mul_of_nonneg_right h_ineq ( mul_nonneg ( norm_nonneg ( a i ) ) (
            norm_nonneg ( b ( m - i ) ) ) ) using 1;
        · ring
          rw [ norm_mul, mul_assoc ];
        · ring;
      · exact Summable.mul_left _ ( Summable.of_nonneg_of_le ( fun _ => by positivity ) ( fun _
          => by simpa [ mul_assoc ] using mul_le_mul_of_nonneg_left ( Summable.le_tsum ( hb_l1 )
          ( m - ‹_› ) ( by norm_num ) ) ( norm_nonneg ( a ‹_› ) ) ) ( ha_l1.mul_right _ ) );
      · refine Summable.mul_left _ ?_;
        refine Summable.add ?_ ?_;
        · convert summable_alpha_abs_b ha hb_l1 m using 1;
        · convert summable_abs_a_beta ha_l1 hb m using 1;
    · have := summable_alpha_abs_b ha hb_l1 m;
      convert this using 1;
    · convert summable_abs_a_beta ha_l1 hb m using 1

/-
Pointwise bound (squared version).
-/
lemma seqConv_pointwise_bound {s : ℝ} (hs : 0 ≤ s)
    {a b : (Fin n → ℤ) → ℂ}
    (ha_l1 : Summable (fun m => ‖a m‖))
    (hb_l1 : Summable (fun m => ‖b m‖))
    (ha : MemSobolev n s a) (hb : MemSobolev n s b)
    (m : Fin n → ℤ) :
    weight n s m * ‖seqConv a b m‖ ^ 2 ≤
      2 * (2 : ℝ) ^ (2 * s) *
        ((∑' i, (weight n (s / 2) i * ‖a i‖) * ‖b (m - i)‖) ^ 2 +
         (∑' i, ‖a i‖ * (weight n (s / 2) (m - i) * ‖b (m - i)‖)) ^ 2) := by
  have h_sq : (weight n (s / 2) m * ‖seqConv a b m‖) ^ 2 ≤ (2 : ℝ) ^ (2 * s) * ((∑' i, (weight n
      (s / 2) i * ‖a i‖) * ‖b (m - i)‖) + (∑' i, ‖a i‖ * (weight n (s / 2) (m - i) * ‖b (m -
      i)‖))) ^ 2 := by
    have h_sq : (weight n (s / 2) m * ‖seqConv a b m‖) ^ 2 ≤ ((2 : ℝ) ^ s * (∑' i, (weight n (s
        / 2) i * ‖a i‖) * ‖b (m - i)‖ + ∑' i, ‖a i‖ * (weight n (s / 2) (m - i) * ‖b (m - i)‖)))
        ^ 2 := by
      exact pow_le_pow_left₀ (mul_nonneg (weight_nonneg _ _) (norm_nonneg _))
        (seqConv_unsquared_bound hs ha_l1 hb_l1 ha hb m) _
    convert h_sq using 1; rw [ mul_pow, two_mul, Real.rpow_add ] <;> norm_num;
    exact Or.inl <| by ring;
  rw [ weight_half_mul ];
  nlinarith [ sq_nonneg ( ∑' i, weight n ( s / 2 ) i * ‖a i‖ * ‖b ( m - i )‖ - ∑' i, ‖a i‖ * (
      weight n ( s / 2 ) ( m - i ) * ‖b ( m - i )‖ ) ), Real.rpow_pos_of_pos zero_lt_two ( 2 * s ) ]

/-
Young + embedding bound for the α ⊛ |b| term:
`∑' m, (∑' i, α_i * ‖b (m-i)‖)^2 ≤ C²·‖b‖²·‖a‖²`
where α_i = weight n (s/2) i * ‖a i‖.
-/
lemma young_alpha_b_bound {s : ℝ} (hn : 0 < n) (hs : (n : ℝ) < 2 * s)
    {a b : (Fin n → ℤ) → ℂ}
    (ha : MemSobolev n s a) (hb : MemSobolev n s b) :
    Summable (fun m => (∑' i, (weight n (s / 2) i * ‖a i‖) * ‖b (m - i)‖) ^ 2) ∧
    ∑' m, (∑' i, (weight n (s / 2) i * ‖a i‖) * ‖b (m - i)‖) ^ 2 ≤
      sobolevEmbedConstSq n s * sobolevNormSq n s b * sobolevNormSq n s a := by
  have := @young_conv_sq_bound;
  have h_comm : ∀ m, ∑' i, weight n (s / 2) i * ‖a i‖ * ‖b (m - i)‖ = ∑' j, ‖b j‖ * (weight n (s
      / 2) (m - j) * ‖a (m - j)‖) := by
    intro m; rw [ ← Equiv.tsum_eq ( Equiv.subLeft m ) ] ; simp +decide [  mul_comm ];
  have := @this n ( fun m => ‖b m‖ ) ( fun m => weight n ( s / 2 ) m * ‖a m‖ ) ?_ ?_ ?_ ?_ <;>
      simp_all +decide only [mul_comm, mul_assoc, mul_pow, mul_left_comm, true_and, ge_iff_le,
        norm_nonneg, implies_true];
  · have h_summable : (∑' i, ‖b i‖) ^ 2 ≤ sobolevEmbedConstSq n s * sobolevNormSq n s b := by
      convert tsum_norm_sq_le hn ( by linarith : ( n : ℝ ) < 2 * s ) hb using 1
      unfold sobolevEmbedConstSq
      rfl
    convert this.2.trans ( mul_le_mul_of_nonneg_right h_summable <| tsum_nonneg fun _ => by
        positivity ) using 1
    all_goals (first
      | rfl
      | (ring; done)
      | (rw [ show sobolevNormSq n s a = ∑' m, ‖a m‖ ^ 2 * weight n ( s * ( 1 / 2 ) ) m ^ 2 by
            convert sobolevNormSq_half_weight s a using 3
            all_goals (first | rfl | ring) ]; ring))
  · exact fun m => mul_nonneg ( norm_nonneg _ ) ( weight_nonneg _ _ );
  · exact summable_norm_of_memSobolev hn ( by linarith ) hb;
  · have := ha;
    convert this using 2; ring;
    unfold MemSobolev; ring;
    rw [ show weight n s = fun m => weight n ( s * ( 1 / 2 ) ) m * weight n ( s * ( 1 / 2 ) ) m
        by ext m; rw [ weight_half_mul ] ; ring ] ; norm_num [ mul_assoc, mul_comm,
        mul_left_comm, sq ]

/-
Young + embedding bound for the |a| ⊛ β term:
`∑' m, (∑' i, ‖a i‖ * β_{m-i})^2 ≤ C²·‖a‖²·‖b‖²`
where β_j = weight n (s/2) j * ‖b j‖.
-/
lemma young_a_beta_bound {s : ℝ} (hn : 0 < n) (hs : (n : ℝ) < 2 * s)
    {a b : (Fin n → ℤ) → ℂ}
    (ha : MemSobolev n s a) (hb : MemSobolev n s b) :
    Summable (fun m => (∑' i, ‖a i‖ * (weight n (s / 2) (m - i) * ‖b (m - i)‖)) ^ 2) ∧
    ∑' m, (∑' i, ‖a i‖ * (weight n (s / 2) (m - i) * ‖b (m - i)‖)) ^ 2 ≤
      sobolevEmbedConstSq n s * sobolevNormSq n s a * sobolevNormSq n s b := by
  have := summable_norm_of_memSobolev hn hs ha;
  have h_summable_b : Summable (fun m => (weight n (s / 2) m * ‖b m‖) ^ 2) := by
    convert hb using 2; ring;
    unfold MemSobolev; norm_num [ sq, mul_assoc, mul_comm, mul_left_comm, weight ] ;
    exact iff_of_eq (by
      congr
      ext m
      rw [← Real.rpow_add (add_pos_of_pos_of_nonneg zero_lt_one
        (Finset.sum_nonneg fun _ _ => mul_self_nonneg _))]
      ring)
  have := @young_conv_sq_bound n ( fun m => ‖a m‖ ) ( fun m => weight n ( s / 2 ) m * ‖b m‖ ) ?_
      ?_ ?_ ?_ <;> norm_num at *;
  · have := tsum_norm_sq_le hn hs ha;
    refine ⟨by tauto, ?_⟩
    have hnonneg : 0 ≤ ∑' m : Fin n → ℤ, (weight n (s / 2) m * ‖b m‖) ^ 2 :=
      tsum_nonneg fun _ => sq_nonneg _
    have hnorm : (∑' m : Fin n → ℤ, (weight n (s / 2) m * ‖b m‖) ^ 2) =
        sobolevNormSq n s b := by rw [sobolevNormSq_half_weight]
    nlinarith!
  · exact fun m => mul_nonneg ( Real.rpow_nonneg ( add_nonneg zero_le_one ( Finset.sum_nonneg
      fun _ _ => sq_nonneg _ ) ) _ ) ( norm_nonneg _ );
  · exact this;
  · convert h_summable_b using 1

/-! ## Main theorems -/

/-
**Second Sobolev multiplication theorem (sequence side).**
For `2s > n > 0`, if `a, b ∈ ℓ²_{(s)}(ℤⁿ)`, then
`seqConv a b ∈ ℓ²_{(s)}(ℤⁿ)` with norm bound
`‖a⊛b‖²_{(s)} ≤ mt2Const n s · ‖a‖²_{(s)} · ‖b‖²_{(s)}`.
-/
theorem second_multiplication_theorem_seq
    {n : ℕ} {s : ℝ} (hn : 0 < n) (hs : (n : ℝ) < 2 * s)
    {a b : (Fin n → ℤ) → ℂ}
    (ha : MemSobolev n s a) (hb : MemSobolev n s b) :
    And (MemSobolev n s (seqConv a b))
        (sobolevNormSq n s (seqConv a b)
           ≤ mt2Const n s * sobolevNormSq n s a * sobolevNormSq n s b) := by
  -- Now apply the lemmas to obtain the summability and bound.
  have h_summable : Summable (fun m => weight n s m * ‖seqConv a b m‖ ^ 2) := by
    have hs_nonneg : 0 ≤ s := by
      have hn_nonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    refine .of_nonneg_of_le (fun m => mul_nonneg (weight_nonneg _ _) (sq_nonneg _))
      (fun m => seqConv_pointwise_bound hs_nonneg
        (summable_norm_of_memSobolev hn hs ha) (summable_norm_of_memSobolev hn hs hb) ha hb m) ?_
    exact Summable.mul_left _ (Summable.add (by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using (young_alpha_b_bound hn hs ha hb).1)
      (by
        simpa only [mul_assoc, mul_comm, mul_left_comm] using
          (young_a_beta_bound hn hs ha hb).1))
  refine And.intro ?_ ?_;
  · exact h_summable;
  · have := @seqConv_pointwise_bound n s;
    specialize this ( by linarith [ show ( n : ℝ ) ≥ 1 by norm_cast ] ) (
        summable_norm_of_memSobolev hn hs ha ) ( summable_norm_of_memSobolev hn hs hb ) ha hb;
    refine le_trans ( Summable.tsum_le_tsum this ?_ ?_ ) ?_;
    · exact h_summable;
    · exact Summable.mul_left _ ( Summable.add ( young_alpha_b_bound hn hs ha hb |>.1 ) (
        young_a_beta_bound hn hs ha hb |>.1 ) );
    · rw [ tsum_mul_left, Summable.tsum_add ];
      · unfold mt2Const;
        have := young_alpha_b_bound hn hs ha hb; have := young_a_beta_bound hn hs ha hb;
            nlinarith [ Real.rpow_pos_of_pos zero_lt_two ( 2 * s ) ];
      · exact young_alpha_b_bound hn hs ha hb |>.1;
      · exact young_a_beta_bound hn hs ha hb |>.1

/-
**Second Sobolev multiplication theorem (distribution side).**
-/
theorem second_multiplication_theorem
    {n : ℕ} {s : ℝ} (hn : 0 < n) (hs : (n : ℝ) < 2 * s)
    {u v : TrigPolyDual n}
    (hu : MemSobolevDistrib n s u) (hv : MemSobolevDistrib n s v) :
    And (MemSobolevDistrib n s (sobolevMulDistrib u v))
        (sobolevNormSqDistrib n s (sobolevMulDistrib u v)
           ≤ mt2Const n s * sobolevNormSqDistrib n s u * sobolevNormSqDistrib n s v) := by
  unfold MemSobolevDistrib sobolevNormSqDistrib sobolevMulDistrib;
  convert second_multiplication_theorem_seq hn hs hu hv using 1;
  · rw [ fourierCoeffDistrib_seqToDual ];
  · rw [ fourierCoeffDistrib_seqToDual ]

end NashEmbedding.Sobolev

end
