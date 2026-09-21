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
import Mathlib
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Basic
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Summability
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Distribution
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Multiplication
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.MultiplicationSharp

/-!
# Third Sobolev Multiplication Theorem

This file proves the third Sobolev multiplication theorem, the technical
bootstrap inequality used in Nash's isometric embedding theorem.

## Main results

* `mt3KSq`, `mt3LSq`, `mt3BStar`, `mt3AConstSq`, `mt3BConstSq` — constants
* `third_multiplication_theorem_seq` — sequence-side result
* `third_multiplication_theorem` — distribution-side result
-/

open scoped BigOperators ComplexConjugate
open Complex Real NashEmbedding.Sobolev


noncomputable section

namespace NashEmbedding.Sobolev

variable {n : ℕ}

/-! ## Definitions -/

noncomputable def mt3KSq (n : Nat) (r : Real) : Real :=
  tsum (fun (j : Fin n → Int) => weight n (-r) j)

noncomputable def mt3LSq (n : Nat) (r : Real) : Real :=
  tsum (fun (j : Fin n → Int) => weight n (1 - r) j)

noncomputable def mt3BStar (k : Nat) : Real :=
  64 * (k : Real) ^ 2 * ((2 : Real) ^ (2 * (k : Real) - 1) - 2)

noncomputable def mt3AConstSq (n : Nat) (r : Real) : Real :=
  8 * mt3KSq n r

noncomputable def mt3BConstSq (n : Nat) (k : Nat) (r : Real) : Real :=
  4 * mt3BStar k * mt3LSq n r

/-! ## Basic properties of constants -/

lemma mt3BStar_nonneg {k : ℕ} (hk : 1 ≤ k) : 0 ≤ mt3BStar k :=
  mul_nonneg ( mul_nonneg ( by norm_num ) ( sq_nonneg _ ) ) ( sub_nonneg.mpr ( by exact le_trans ( by norm_num ) ( Real.rpow_le_rpow_of_exponent_le ( by norm_num ) ( show ( 2 * k - 1 : ℝ ) ≥ 1 by linarith [ show ( k : ℝ ) ≥ 1 by norm_cast ] ) ) ) )

/-! ## Helper lemmas for the refined weight inequality -/

/-
For k ≥ 1 and |ρ| ≤ 1/(2k), we have (1+ρ)^k ≤ 2.
    Proof: For ρ < 0, (1+ρ) ∈ (0,1] so (1+ρ)^k ≤ 1 ≤ 2.
    For ρ ≥ 0, use (1+ρ) ≤ exp(ρ), so (1+ρ)^k ≤ exp(kρ) ≤ exp(1/2) < 2.
-/
lemma one_add_pow_le_two {k : ℕ} (hk : 1 ≤ k) {ρ : ℝ}
    (hρ : |ρ| ≤ 1 / (2 * (k : ℝ))) :
    (1 + ρ) ^ k ≤ 2 := by
  by_cases hρ_neg : ρ < 0;
  · exact le_trans ( pow_le_one₀ ( by linarith [ abs_le.mp hρ, show ( 1 : ℝ ) / ( 2 * k ) ≤ 1 by rw [ div_le_iff₀ ] <;> norm_cast <;> linarith ] ) ( by linarith [ abs_le.mp hρ, show ( 1 : ℝ ) / ( 2 * k ) ≤ 1 by rw [ div_le_iff₀ ] <;> norm_cast <;> linarith ] ) ) ( by norm_num );
  · -- For ρ ≥ 0, use (1+ρ) ≤ exp(ρ), so (1+ρ)^k ≤ exp(kρ) ≤ exp(1/2) < 2.
    have h_exp : (1 + ρ) ^ k ≤ Real.exp (k * ρ) := by
      rw [ ← Real.rpow_natCast, Real.rpow_def_of_pos ( by linarith ) ] ; norm_num ; ring_nf;
      exact mul_le_mul_of_nonneg_right ( le_trans ( Real.log_le_sub_one_of_pos ( by linarith ) ) ( by linarith ) ) ( Nat.cast_nonneg _ );
    refine le_trans h_exp ?_;
    rw [ ← Real.log_le_log_iff ( by positivity ) ( by positivity ), Real.log_exp ];
    exact le_trans ( mul_le_mul_of_nonneg_left ( le_of_abs_le hρ ) ( Nat.cast_nonneg _ ) ) ( by rw [ mul_div, div_le_iff₀ ] <;> nlinarith [ Real.log_two_gt_d9, show ( k : ℝ ) ≥ 1 by norm_cast ] )

/-
Case B of the refined weight inequality:
    If `∑ j_l² ≤ ∑ i_l² / (64 * k²)`, then
    `weight n k (i + j) ≤ 2 * weight n k i`.
-/
lemma refined_weight_case_b {k : ℕ} (hk : 1 ≤ k) (i j : Fin n → ℤ)
    (hsmall : ∑ l, (j l : ℝ) ^ 2 ≤ ∑ l, (i l : ℝ) ^ 2 / (64 * (k : ℝ) ^ 2)) :
    weight n (k : ℝ) (i + j) ≤ 2 * weight n (k : ℝ) i := by
  -- Applying the inequality $(1 + \rho)^k \leq 2$ to $\rho$.
  have h_rho : (1 + (2 * (∑ l, (i l : ℝ) * (j l : ℝ)) + (∑ l, ((j l : ℝ) ^ 2))) / (1 + (∑ l, ((i l : ℝ) ^ 2)))) ^ k ≤ 2 := by
    refine' one_add_pow_le_two hk _;
    -- We have $|2 \cdot \sum i_l \cdot j_l| \leq 2 \cdot \sqrt{S_i} \cdot \sqrt{S_j}$ (Cauchy-Schwarz).
    have h_cauchy_schwarz : |2 * ∑ l : Fin n, ((i l : ℝ) * (j l : ℝ))| ≤ 2 * Real.sqrt (∑ l : Fin n, ((i l : ℝ) ^ 2)) * Real.sqrt (∑ l : Fin n, ((j l : ℝ) ^ 2)) := by
      -- By the Cauchy-Schwarz inequality, we have that for any vectors $u$ and $v$ of equal length, $(∑ l, u l * v l)^2 ≤ (∑ l, u l^2) * (∑ l, v l^2)$.
      have h_cauchy_schwarz : ∀ (u v : Fin n → ℝ), (∑ l, u l * v l)^2 ≤ (∑ l, u l^2) * (∑ l, v l^2) := by
        exact fun u v => Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v;
      rw [ abs_mul, abs_two ];
      rw [ mul_assoc ] ; exact mul_le_mul_of_nonneg_left ( Real.abs_le_sqrt <| by simpa using h_cauchy_schwarz _ _ ) zero_le_two |> le_trans <| by rw [ Real.sqrt_mul <| Finset.sum_nonneg fun _ _ => sq_nonneg _ ] ;
    generalize_proofs at *; (
    -- We have $\sqrt{S_j} \leq \sqrt{S_i / (64k^2)} = \sqrt{S_i} / (8k)$.
    have h_sqrt_bound : Real.sqrt (∑ l : Fin n, ((j l : ℝ) ^ 2)) ≤ Real.sqrt (∑ l : Fin n, ((i l : ℝ) ^ 2)) / (8 * k) := by
      convert Real.sqrt_le_sqrt hsmall using 1 ; ring_nf ; norm_num [ show k ≠ 0 by linarith ] ;
      norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ] ; ring
    generalize_proofs at *; (
    rw [ abs_div, abs_of_nonneg ( by positivity : ( 0 : ℝ ) ≤ 1 + ∑ l : Fin n, ( i l : ℝ ) ^ 2 ) ] ; rw [ div_le_div_iff₀ ] <;> try positivity;
    rw [ le_div_iff₀ ( by positivity ) ] at h_sqrt_bound;
    cases abs_cases ( 2 * ∑ l : Fin n, ( i l : ℝ ) * j l + ∑ l : Fin n, ( j l : ℝ ) ^ 2 ) <;> cases abs_cases ( 2 * ∑ l : Fin n, ( i l : ℝ ) * j l ) <;> nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast, Real.sqrt_nonneg ( ∑ l : Fin n, ( i l : ℝ ) ^ 2 ), Real.sqrt_nonneg ( ∑ l : Fin n, ( j l : ℝ ) ^ 2 ), Real.mul_self_sqrt ( show 0 ≤ ∑ l : Fin n, ( i l : ℝ ) ^ 2 by exact Finset.sum_nonneg fun _ _ => sq_nonneg _ ), Real.mul_self_sqrt ( show 0 ≤ ∑ l : Fin n, ( j l : ℝ ) ^ 2 by exact Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ]));
  -- By definition of `weight`, we know that `weight n k (i + j) = (1 + ∑ l, (i l + j l : ℝ) ^ 2) ^ k`.
  simp [weight];
  convert mul_le_mul_of_nonneg_right h_rho ( pow_nonneg ( show 0 ≤ 1 + ∑ l : Fin n, ( i l : ℝ ) ^ 2 by exact add_nonneg zero_le_one <| Finset.sum_nonneg fun _ _ => sq_nonneg _ ) k ) using 1
  all_goals (first
    | rfl
    | (rw [ ← mul_pow, add_mul, div_mul_cancel₀ _ ( by exact ne_of_gt <| add_pos_of_pos_of_nonneg zero_lt_one <| Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ]; norm_num [ add_sq, Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, mul_assoc, mul_comm, mul_left_comm ]; ring))

/-! ## Refined weight inequality -/

/-
The refined weight inequality for integer exponents k ≥ 1:
    `weight n k (i+j) ≤ 2·(weight n k i + weight n k j)
       + B*_k·(weight n (k-1) i · weight n 1 j + weight n 1 i · weight n (k-1) j)`
-/
lemma refined_weight_ineq {k : ℕ} (hk : 1 ≤ k) (i j : Fin n → ℤ) :
    weight n (k : ℝ) (i + j) ≤
      2 * (weight n (k : ℝ) i + weight n (k : ℝ) j) +
      mt3BStar k * (weight n ((k : ℝ) - 1) i * weight n 1 j +
                     weight n 1 i * weight n ((k : ℝ) - 1) j) := by
  by_cases hB : ∑ l, (j l : ℝ) ^ 2 ≤ ∑ l, (i l : ℝ) ^ 2 / (64 * (k : ℝ) ^ 2);
  · refine le_add_of_le_of_nonneg ?_ ?_;
    · exact le_trans ( refined_weight_case_b hk i j hB ) ( by linarith [ show 0 ≤ weight n ( k : ℝ ) j from weight_nonneg _ _ ] );
    · exact mul_nonneg ( mt3BStar_nonneg hk ) ( add_nonneg ( mul_nonneg ( weight_nonneg _ _ ) ( weight_nonneg _ _ ) ) ( mul_nonneg ( weight_nonneg _ _ ) ( weight_nonneg _ _ ) ) );
  · by_cases hA : ∑ l, (i l : ℝ) ^ 2 ≤ ∑ l, (j l : ℝ) ^ 2 / (64 * (k : ℝ) ^ 2);
    · -- Apply the refined weight case b to (j, i) instead.
      have h_case_b : weight n (k : ℝ) (j + i) ≤ 2 * weight n (k : ℝ) j := by
        apply refined_weight_case_b hk j i hA;
      rw [ add_comm ] at h_case_b;
      refine le_add_of_le_of_nonneg ?_ ?_;
      · exact h_case_b.trans ( mul_le_mul_of_nonneg_left ( le_add_of_nonneg_left <| by exact Real.rpow_nonneg ( add_nonneg zero_le_one <| Finset.sum_nonneg fun _ _ => sq_nonneg _ ) _ ) zero_le_two );
      · exact mul_nonneg ( mt3BStar_nonneg hk ) ( add_nonneg ( mul_nonneg ( weight_nonneg _ _ ) ( weight_nonneg _ _ ) ) ( mul_nonneg ( weight_nonneg _ _ ) ( weight_nonneg _ _ ) ) );
    · -- Case C: S_j > S_i/(64k²) AND S_i > S_j/(64k²). Then:
      -- S_i < 64k²*S_j, so X = 1+S_i ≤ 1+64k²*S_j ≤ 64k²*(1+S_j) = 64k²*Y (using 1 ≤ 64k² since k ≥ 1).
      -- Similarly Y ≤ 64k²*X.
      have hX : (1 + ∑ l, (i l : ℝ) ^ 2) ≤ 64 * (k : ℝ) ^ 2 * (1 + ∑ l, (j l : ℝ) ^ 2) := by
        norm_num [ ← Finset.sum_div _ _ _ ] at *;
        rw [ div_lt_iff₀ ] at hB <;> nlinarith [ show ( k : ℝ ) ^ 2 ≥ 1 by norm_cast; nlinarith ]
      have hY : (1 + ∑ l, (j l : ℝ) ^ 2) ≤ 64 * (k : ℝ) ^ 2 * (1 + ∑ l, (i l : ℝ) ^ 2) := by
        norm_num [ ← Finset.sum_div _ _ _ ] at *;
        rw [ div_lt_iff₀ ] at hA <;> nlinarith [ show ( k : ℝ ) ^ 2 ≥ 1 by norm_cast; nlinarith ];
      -- Step C1: 1+S_{i+j} ≤ 2(X+Y). Since S_{i+j} = ∑(i_l+j_l)² ≤ 2S_i+2S_j (by (a+b)² ≤ 2a²+2b²), we get 1+S_{i+j} ≤ 1+2S_i+2S_j ≤ 2(1+S_i)+2(1+S_j) = 2X+2Y = 2(X+Y).
      have hC1 : 1 + ∑ l, ((i l + j l) : ℝ) ^ 2 ≤ 2 * (1 + ∑ l, (i l : ℝ) ^ 2 + 1 + ∑ l, (j l : ℝ) ^ 2) := by
        have hC1 : ∑ l, ((i l + j l) : ℝ) ^ 2 ≤ 2 * (∑ l, (i l : ℝ) ^ 2 + ∑ l, (j l : ℝ) ^ 2) := by
          rw [ ← Finset.sum_add_distrib, Finset.mul_sum _ _ _ ];
          exact Finset.sum_le_sum fun _ _ => by linarith [ sq_nonneg ( i ‹_› - j ‹_› : ℝ ) ] ;
        linarith;
      -- Step C2: Use add_pow_le for Nat.pow. (X+Y)^k ≤ 2^{k-1}*(X^k+Y^k). So (2(X+Y))^k = 2^k*(X+Y)^k ≤ 2^k*2^{k-1}*(X^k+Y^k) = 2^{2k-1}*(X^k+Y^k).
      have hC2 : (1 + ∑ l, ((i l + j l) : ℝ) ^ 2) ^ k ≤ 2 ^ (2 * k - 1) * ((1 + ∑ l, (i l : ℝ) ^ 2) ^ k + (1 + ∑ l, (j l : ℝ) ^ 2) ^ k) := by
        have hC2 : (1 + ∑ l, (i l : ℝ) ^ 2 + 1 + ∑ l, (j l : ℝ) ^ 2) ^ k ≤ 2 ^ (k - 1) * ((1 + ∑ l, (i l : ℝ) ^ 2) ^ k + (1 + ∑ l, (j l : ℝ) ^ 2) ^ k) := by
          have hC2 : ∀ (x y : ℝ), 0 ≤ x → 0 ≤ y → (x + y) ^ k ≤ 2 ^ (k - 1) * (x ^ k + y ^ k) := by
            exact fun x y a a_1 => add_pow_le a a_1 k;
          convert hC2 ( 1 + ∑ l, ( i l : ℝ ) ^ 2 ) ( 1 + ∑ l, ( j l : ℝ ) ^ 2 ) ( by exact add_nonneg zero_le_one <| Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ( by exact add_nonneg zero_le_one <| Finset.sum_nonneg fun _ _ => sq_nonneg _ ) using 1 ; ring;
        refine le_trans ( pow_le_pow_left₀ ( by exact add_nonneg zero_le_one <| Finset.sum_nonneg fun _ _ => sq_nonneg _ ) hC1 _ ) ?_;
        rw [ mul_pow ];
        convert mul_le_mul_of_nonneg_left hC2 ( pow_nonneg zero_le_two k ) using 1 ; rw [ show 2 * k - 1 = k - 1 + k by omega ] ; ring;
      -- Step C4: Since X ≤ 64k²*Y, X^k = X^{k-1}*X ≤ 64k²*X^{k-1}*Y. Similarly Y^k ≤ 64k²*X*Y^{k-1}. So (X^k+Y^k) ≤ 64k²*(X^{k-1}*Y + X*Y^{k-1}).
      have hC4 : (1 + ∑ l, (i l : ℝ) ^ 2) ^ k + (1 + ∑ l, (j l : ℝ) ^ 2) ^ k ≤ 64 * (k : ℝ) ^ 2 * ((1 + ∑ l, (i l : ℝ) ^ 2) ^ (k - 1) * (1 + ∑ l, (j l : ℝ) ^ 2) + (1 + ∑ l, (i l : ℝ) ^ 2) * (1 + ∑ l, (j l : ℝ) ^ 2) ^ (k - 1)) := by
        rcases k with ( _ | k ) <;> simp_all +decide [ pow_succ' ];
        nlinarith [ pow_nonneg ( show 0 ≤ 1 + ∑ x : Fin n, ( i x : ℝ ) * i x by exact add_nonneg zero_le_one <| Finset.sum_nonneg fun _ _ => mul_self_nonneg _ ) k, pow_nonneg ( show 0 ≤ 1 + ∑ x : Fin n, ( j x : ℝ ) * j x by exact add_nonneg zero_le_one <| Finset.sum_nonneg fun _ _ => mul_self_nonneg _ ) k ];
      unfold weight mt3BStar;
      rcases k with ( _ | k ) <;> norm_num [ Nat.mul_succ, pow_succ' ] at *;
      norm_cast at * ; norm_num [ Nat.mul_succ, pow_succ' ] at *;
      rw [ Int.subNatNat_of_le ( by linarith ) ] ; norm_cast ; norm_num [ Nat.mul_succ, pow_succ' ] at *;
      rw [ Int.subNatNat_eq_coe ] ; push_cast ; nlinarith [ pow_pos ( zero_lt_two' ℤ ) ( 2 * k ) ]

/-! ## Half-power form of the refined weight inequality -/

/-
The half-power form: take square roots of the refined weight inequality.
-/
lemma refined_weight_half {k : ℕ} (hk : 1 ≤ k) (i j : Fin n → ℤ) :
    weight n ((k : ℝ) / 2) (i + j) ≤
      Real.sqrt 2 * (weight n ((k : ℝ) / 2) i + weight n ((k : ℝ) / 2) j) +
      Real.sqrt (mt3BStar k) *
        (weight n (((k : ℝ) - 1) / 2) i * weight n (1 / 2 : ℝ) j +
         weight n (1 / 2 : ℝ) i * weight n (((k : ℝ) - 1) / 2) j) := by
  have h_sqrt : (weight n (k / 2 : ℝ) (i + j)) ^ 2 ≤ 2 * ((weight n (k / 2 : ℝ) i) ^ 2 + (weight n (k / 2 : ℝ) j) ^ 2) + mt3BStar k * ((weight n ((k - 1) / 2 : ℝ) i * weight n (1 / 2 : ℝ) j) ^ 2 + (weight n (1 / 2 : ℝ) i * weight n ((k - 1) / 2 : ℝ) j) ^ 2) := by
    convert refined_weight_ineq hk i j using 1;
    · convert weight_half_mul ( k : ℝ ) ( i + j ) |> Eq.symm using 1 ; ring;
    · norm_num [ weight_mul ] ; ring;
      norm_num [ sq, weight_mul ] ; ring;
  have h_sqrt : (weight n (k / 2 : ℝ) (i + j)) ≤ Real.sqrt (2 * ((weight n (k / 2 : ℝ) i) ^ 2 + (weight n (k / 2 : ℝ) j) ^ 2)) + Real.sqrt (mt3BStar k * ((weight n ((k - 1) / 2 : ℝ) i * weight n (1 / 2 : ℝ) j) ^ 2 + (weight n (1 / 2 : ℝ) i * weight n ((k - 1) / 2 : ℝ) j) ^ 2)) := by
    have h_sqrt : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
      exact fun x y hx hy => Real.sqrt_le_iff.mpr ⟨ by positivity, by nlinarith only [ Real.sqrt_nonneg x, Real.sqrt_nonneg y, Real.mul_self_sqrt hx, Real.mul_self_sqrt hy ] ⟩;
    exact le_trans ( Real.le_sqrt_of_sq_le ‹_› ) ( h_sqrt _ _ ( by positivity ) ( by exact mul_nonneg ( mt3BStar_nonneg hk ) ( by positivity ) ) );
  refine le_trans h_sqrt ?_;
  gcongr;
  · rw [ Real.sqrt_mul ( by positivity ) ];
    exact mul_le_mul_of_nonneg_left ( Real.sqrt_le_iff.mpr ⟨ by exact add_nonneg ( weight_nonneg _ _ ) ( weight_nonneg _ _ ), by nlinarith only [ weight_nonneg ( k / 2 : ℝ ) i, weight_nonneg ( k / 2 : ℝ ) j ] ⟩ ) ( Real.sqrt_nonneg _ );
  · rw [ Real.sqrt_mul ( by exact le_trans ( by norm_num ) ( mt3BStar_nonneg hk ) ) ];
    gcongr;
    rw [ Real.sqrt_le_left ] <;> nlinarith only [ show 0 ≤ weight n ( ( k - 1 ) / 2 ) i * weight n ( 1 / 2 ) j by exact mul_nonneg ( weight_nonneg _ _ ) ( weight_nonneg _ _ ), show 0 ≤ weight n ( 1 / 2 ) i * weight n ( ( k - 1 ) / 2 ) j by exact mul_nonneg ( weight_nonneg _ _ ) ( weight_nonneg _ _ ) ]

/-! ## Phase 1b: weighted ℓ²_(r) → ℓ¹ via Cauchy–Schwarz -/

/-- Summability of the weighted norm sum `∑ w^{1/2}_j · ‖b_j‖`. -/
lemma summable_weighted_norm {r : ℝ} (hn : 0 < n) (hr : 1 + (n : ℝ) / 2 < r)
    {b : (Fin n → ℤ) → ℂ} (hb : MemSobolev n r b) :
    Summable (fun j => weight n (1 / 2 : ℝ) j * ‖b j‖) := by
  have := @summable_norm_of_memSobolev n ( r - 1 );
  specialize this hn ( by linarith ) ( show MemSobolev n ( r - 1 ) ( fun m => weight n ( 1 / 2 ) m * b m ) from ?_ );
  · refine' .of_nonneg_of_le ( fun m => _ ) ( fun m => _ ) hb;
    · exact mul_nonneg ( le_of_lt ( weight_pos _ _ ) ) ( sq_nonneg _ );
    · norm_num [ weight ];
      rw [ abs_of_nonneg ( by positivity ), mul_pow, ← Real.rpow_natCast _ 2, ← Real.rpow_mul ( by positivity ) ] ; ring_nf ; norm_num;
      rw [ ← Real.rpow_add_one ( by exact ne_of_gt ( add_pos_of_pos_of_nonneg zero_lt_one ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ) ) ] ; ring_nf ; norm_num;
  · convert this using 2 ; norm_num [ abs_of_nonneg, weight_nonneg ]

/-- Phase 1b (squared form):
    `(∑ w^{1/2}_j |b_j|)² ≤ L²_r · ‖b‖²_{(r)}` -/
lemma tsum_weighted_norm_sq_le {r : ℝ} (hn : 0 < n) (hr : 1 + (n : ℝ) / 2 < r)
    {b : (Fin n → ℤ) → ℂ} (hb : MemSobolev n r b) :
    (∑' j, weight n (1 / 2 : ℝ) j * ‖b j‖) ^ 2 ≤
      mt3LSq n r * sobolevNormSq n r b := by
  have h_sobolev_eq : sobolevNormSq n r b
                    = ∑' (j : Fin n → ℤ), ‖b j‖ ^ 2 * (weight n (r - 1) j * weight n 2⁻¹ j ^ 2) := by
    unfold sobolevNormSq
    refine tsum_congr fun j => ?_
    have hp : (0 : ℝ) < 1 + ∑ i, (j i : ℝ)^2 :=
      add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    unfold weight
    have h_pow_sq : ((1 + ∑ i, (j i : ℝ)^2) ^ (2⁻¹ : ℝ)) ^ 2
                  = (1 + ∑ i, (j i : ℝ)^2) := by
      rw [sq, ← Real.rpow_add hp]; norm_num
    have h_r_id : (1 + ∑ i, (j i : ℝ)^2) ^ r
                = (1 + ∑ i, (j i : ℝ)^2) ^ (r - 1) * ((1 + ∑ i, (j i : ℝ)^2) ^ (2⁻¹ : ℝ)) ^ 2 := by
      rw [h_pow_sq, ← Real.rpow_add_one (ne_of_gt hp) (r - 1)]
      congr 1; ring
    rw [h_r_id]; ring
  have h_apply_tsum_norm_sq_le : (∑' j : Fin n → ℤ, ‖(weight n (1 / 2) j : ℂ) * b j‖) ^ 2 ≤
    (∑' j : Fin n → ℤ, weight n (1 - r) j) * (∑' j : Fin n → ℤ, weight n (r - 1) j * ‖(weight n (1 / 2) j : ℂ) * b j‖ ^ 2) := by
      have := @tsum_norm_sq_le;
      convert @this n ( r - 1 ) hn ( by linarith ) ( fun j => ( weight n ( 1 / 2 ) j : ℂ ) * b j ) _ using 1
      all_goals (first
        | rfl
        | (unfold sobolevNormSq; norm_num [ mul_pow ])
        | (exact h_sobolev_eq)
        | (refine' .of_nonneg_of_le ( fun m => _ ) ( fun m => _ ) hb
           · exact mul_nonneg ( Real.rpow_nonneg ( add_nonneg zero_le_one ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ) _ ) ( sq_nonneg _ )
           · norm_num [ weight ]
             rw [ abs_of_nonneg ( by positivity ), mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ), mul_comm ] ; norm_num
             rw [ show ( 1 + ∑ i : Fin n, ( m i : ℝ ) ^ 2 ) ^ r = ( 1 + ∑ i : Fin n, ( m i : ℝ ) ^ 2 ) ^ ( r - 1 ) * ( 1 + ∑ i : Fin n, ( m i : ℝ ) ^ 2 ) by rw [ ← Real.rpow_add_one ( by exact ne_of_gt <| add_pos_of_pos_of_nonneg zero_lt_one <| Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ] ; ring ] ; linarith))
  simp_all +decide [ mul_pow, mul_assoc, mul_comm, mul_left_comm, tsum_mul_left, tsum_mul_right, norm_mul, norm_pow ];
  convert h_apply_tsum_norm_sq_le using 3
  all_goals (first
    | rfl
    | (exact h_sobolev_eq)
    | (exact funext fun _ => by rw [ abs_of_nonneg ( weight_nonneg _ _ ) ]))

/-! ## Young-type bounds for the four convolution terms -/

/-
Young bound for S1: ∑ (α^k ⊛ |b|)² ≤ (∑|b|)² · ‖a‖²_{(k)}
-/
lemma mt3_young_S1
    {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 1 + (n : ℝ) / 2 < r)
    {k : ℕ} (hkr : r ≤ (k : ℝ))
    {a b : (Fin n → ℤ) → ℂ}
    (ha : MemSobolev n (k : ℝ) a) (hb : MemSobolev n r b) :
    Summable (fun m => (∑' i, weight n ((k : ℝ) / 2) i * ‖a i‖ * ‖b (m - i)‖) ^ 2) ∧
    ∑' m, (∑' i, weight n ((k : ℝ) / 2) i * ‖a i‖ * ‖b (m - i)‖) ^ 2 ≤
      mt3KSq n r * sobolevNormSq n r b * sobolevNormSq n (k : ℝ) a := by
  have h_summable : Summable (fun m => (weight n (k / 2) m * ‖a m‖) ^ 2) := by
    convert ha using 1;
    unfold MemSobolev; norm_num [ mul_pow, weight ] ;
    exact iff_of_eq ( by congr; ext m; rw [ ← Real.rpow_natCast _ 2, ← Real.rpow_mul ( by exact add_nonneg zero_le_one <| Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ] ; norm_num );
  have h_summable_b : Summable (fun m => ‖b m‖) := by
    have := summable_norm_of_memSobolev hn ( show ( n : ℝ ) < 2 * r by linarith ) hb; aesop;
  have := @young_conv_sq_bound n;
  have := @this ( fun m => ‖b m‖ ) ( fun m => weight n ( k / 2 ) m * ‖a m‖ ) ?_ ?_ ?_ ?_ <;> norm_num at *;
  · refine' ⟨ _, _ ⟩;
    · convert this.1 using 1
      all_goals (first | rfl | (ext m; rw [ ← Equiv.tsum_eq ( Equiv.subLeft m ) ]; norm_num [ mul_assoc, mul_comm, mul_left_comm ]))
    · have hlhs : (∑' m : Fin n → ℤ, (∑' i, weight n (↑k / 2) i * ‖a i‖ * ‖b (m - i)‖) ^ 2)
                = (∑' m : Fin n → ℤ, (∑' i, ‖b i‖ * (weight n (↑k / 2) (m - i) * ‖a (m - i)‖)) ^ 2) := by
        refine tsum_congr fun m => ?_
        rw [ ← Equiv.tsum_eq ( Equiv.subLeft m ) ] ; norm_num [ mul_assoc, mul_comm, mul_left_comm ]
      have hb_bound : (∑' i : Fin n → ℤ, ‖b i‖) ^ 2 ≤ mt3KSq n r * sobolevNormSq n r b :=
        tsum_norm_sq_le hn (by linarith : (n : ℝ) < 2 * r) hb
      have ha_eq : (∑' m : Fin n → ℤ, (weight n (↑k / 2) m * ‖a m‖) ^ 2) = sobolevNormSq n (↑k) a :=
        (sobolevNormSq_half_weight (↑k) a).symm
      have hmid : (∑' i : Fin n → ℤ, ‖b i‖) ^ 2 * (∑' m : Fin n → ℤ, (weight n (↑k / 2) m * ‖a m‖) ^ 2)
                ≤ mt3KSq n r * sobolevNormSq n r b * sobolevNormSq n (↑k) a := by
        rw [ha_eq]
        exact mul_le_mul_of_nonneg_right hb_bound
          (by unfold sobolevNormSq; exact tsum_nonneg fun _ => mul_nonneg (weight_nonneg _ _) (sq_nonneg _))
      calc (∑' m : Fin n → ℤ, (∑' i, weight n (↑k / 2) i * ‖a i‖ * ‖b (m - i)‖) ^ 2)
          = (∑' m : Fin n → ℤ, (∑' i, ‖b i‖ * (weight n (↑k / 2) (m - i) * ‖a (m - i)‖)) ^ 2) := hlhs
        _ ≤ (∑' i : Fin n → ℤ, ‖b i‖) ^ 2 * (∑' m : Fin n → ℤ, (weight n (↑k / 2) m * ‖a m‖) ^ 2) := this.2
        _ ≤ mt3KSq n r * sobolevNormSq n r b * sobolevNormSq n (↑k) a := hmid
  · exact fun m => mul_nonneg ( Real.rpow_nonneg ( add_nonneg zero_le_one ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ) _ ) ( norm_nonneg _ );
  · assumption;
  · convert h_summable using 1

/-
Young bound for S2: ∑ (|a| ⊛ β^k)² ≤ (∑|a|)² · ‖b‖²_{(k)}
-/
lemma mt3_young_S2
    {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 1 + (n : ℝ) / 2 < r)
    {k : ℕ} (hkr : r ≤ (k : ℝ))
    {a b : (Fin n → ℤ) → ℂ}
    (ha : MemSobolev n r a) (hb : MemSobolev n (k : ℝ) b) :
    Summable (fun m => (∑' i, ‖a i‖ * (weight n ((k : ℝ) / 2) (m - i) * ‖b (m - i)‖)) ^ 2) ∧
    ∑' m, (∑' i, ‖a i‖ * (weight n ((k : ℝ) / 2) (m - i) * ‖b (m - i)‖)) ^ 2 ≤
      mt3KSq n r * sobolevNormSq n r a * sobolevNormSq n (k : ℝ) b := by
  have := @young_conv_sq_bound n;
  have := @this ( fun i => ‖a i‖ ) ( fun i => weight n ( k / 2 ) i * ‖b i‖ ) ?_ ?_ ?_ ?_ <;> norm_num at *;
  · refine ⟨ this.1, this.2.trans ?_ ⟩;
    refine' mul_le_mul _ _ _ _;
    · convert tsum_norm_sq_le hn ( by linarith : ( n : ℝ ) < 2 * r ) ha using 1
      all_goals rfl
    · rw [ sobolevNormSq_half_weight ];
    · exact tsum_nonneg fun _ => sq_nonneg _;
    · exact mul_nonneg ( tsum_nonneg fun _ => by exact Real.rpow_nonneg ( by exact add_nonneg zero_le_one <| Finset.sum_nonneg fun _ _ => sq_nonneg _ ) _ ) ( tsum_nonneg fun _ => by exact mul_nonneg ( by exact Real.rpow_nonneg ( by exact add_nonneg zero_le_one <| Finset.sum_nonneg fun _ _ => sq_nonneg _ ) _ ) <| sq_nonneg _ );
  · exact fun m => mul_nonneg ( weight_nonneg _ _ ) ( norm_nonneg _ );
  · exact summable_norm_of_memSobolev hn ( by linarith ) ha;
  · convert hb using 1;
    unfold MemSobolev; ring;
    unfold weight; ring;
    exact iff_of_eq ( by congr; ext m; rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; ring )

/-
Young bound for S3: ∑ (α^{k-1} ⊛ β^1)² ≤ (∑ w^{1/2}|b|)² · ‖a‖²_{(k-1)}
-/
lemma mt3_young_S3
    {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 1 + (n : ℝ) / 2 < r)
    {k : ℕ} (hkr : r ≤ (k : ℝ))
    {a b : (Fin n → ℤ) → ℂ}
    (ha : MemSobolev n ((k : ℝ) - 1) a) (hb : MemSobolev n r b) :
    Summable (fun m => (∑' i, weight n (((k : ℝ) - 1) / 2) i * ‖a i‖ *
        (weight n (1 / 2 : ℝ) (m - i) * ‖b (m - i)‖)) ^ 2) ∧
    ∑' m, (∑' i, weight n (((k : ℝ) - 1) / 2) i * ‖a i‖ *
        (weight n (1 / 2 : ℝ) (m - i) * ‖b (m - i)‖)) ^ 2 ≤
      mt3LSq n r * sobolevNormSq n r b * sobolevNormSq n ((k : ℝ) - 1) a := by
  let f := fun m => weight n (1 / 2 : ℝ) m * ‖b m‖
  let g := fun m => weight n (((k : ℝ) - 1) / 2) m * ‖a m‖
  have hf : Summable f := summable_weighted_norm hn hr hb
  have hg : Summable (fun m => g m ^ 2) := by
    apply ha.congr
    intro m
    dsimp [g]
    rw [weight_half_mul ((k : ℝ) - 1) m]
    ring
  have hbound := young_conv_sq_bound
    (f := f) (g := g)
    (fun m => mul_nonneg (weight_nonneg _ _) (norm_nonneg _))
    (fun m => mul_nonneg (weight_nonneg _ _) (norm_nonneg _)) hf hg
  have hcomm : (fun m => (∑' i, g i * f (m - i)) ^ 2) =
      (fun m => (∑' i, f i * g (m - i)) ^ 2) := by
    funext m
    congr 1
    rw [← Equiv.tsum_eq (Equiv.subLeft m)]
    apply tsum_congr
    intro i
    simp only [Equiv.subLeft_apply, sub_sub_cancel, mul_comm]
  change Summable (fun m => (∑' i, g i * f (m - i)) ^ 2) ∧ _
  refine ⟨hcomm.symm ▸ hbound.1, ?_⟩
  change (∑' m, (∑' i, g i * f (m - i)) ^ 2) ≤ _
  rw [hcomm]
  apply hbound.2.trans
  change (∑' i, f i) ^ 2 * (∑' m, g m ^ 2) ≤ _
  rw [← sobolevNormSq_half_weight ((k : ℝ) - 1) a]
  exact mul_le_mul_of_nonneg_right (tsum_weighted_norm_sq_le hn hr hb)
    (tsum_nonneg fun m => mul_nonneg (weight_nonneg _ _) (sq_nonneg _))

/-
Young bound for S4: ∑ (α^1 ⊛ β^{k-1})² ≤ (∑ w^{1/2}|a|)² · ‖b‖²_{(k-1)}
-/
lemma mt3_young_S4
    {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 1 + (n : ℝ) / 2 < r)
    {k : ℕ} (hkr : r ≤ (k : ℝ))
    {a b : (Fin n → ℤ) → ℂ}
    (ha : MemSobolev n r a) (hb : MemSobolev n ((k : ℝ) - 1) b) :
    Summable (fun m => (∑' i, weight n (1 / 2 : ℝ) i * ‖a i‖ *
        (weight n (((k : ℝ) - 1) / 2) (m - i) * ‖b (m - i)‖)) ^ 2) ∧
    ∑' m, (∑' i, weight n (1 / 2 : ℝ) i * ‖a i‖ *
        (weight n (((k : ℝ) - 1) / 2) (m - i) * ‖b (m - i)‖)) ^ 2 ≤
      mt3LSq n r * sobolevNormSq n r a * sobolevNormSq n ((k : ℝ) - 1) b := by
  have := @young_conv_sq_bound;
  specialize @this n ( fun i => weight n ( 1 / 2 ) i * ‖a i‖ ) ( fun i => weight n ( ( k - 1 ) / 2 ) i * ‖b i‖ ) ; norm_num at *;
  refine' this ( fun m => mul_nonneg ( weight_nonneg _ _ ) ( norm_nonneg _ ) ) ( fun m => mul_nonneg ( weight_nonneg _ _ ) ( norm_nonneg _ ) ) _ _ |> fun h => ⟨ h.1, h.2.trans _ ⟩;
  · convert summable_weighted_norm hn ( show 1 + ( n : ℝ ) / 2 < r by linarith ) ha using 1;
  · convert hb using 1;
    unfold MemSobolev; norm_num [ mul_pow, weight ] ;
    exact iff_of_eq ( by congr; ext; rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by exact add_nonneg zero_le_one <| Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ] ; ring );
  · refine' mul_le_mul _ _ _ _;
    · convert tsum_weighted_norm_sq_le hn hr ha using 1;
    · rw [ show sobolevNormSq n ( k - 1 ) b = ∑' m : Fin n → ℤ, ( weight n ( ( k - 1 ) / 2 ) m * ‖b m‖ ) ^ 2 from ?_ ];
      exact sobolevNormSq_half_weight (↑k - 1) b;
    · exact tsum_nonneg fun _ => sq_nonneg _;
    · exact mul_nonneg ( tsum_nonneg fun _ => weight_nonneg _ _ ) ( tsum_nonneg fun _ => mul_nonneg ( weight_nonneg _ _ ) ( sq_nonneg _ ) )

/-! ## Pointwise bounds -/

/-
Unsquared pointwise bound: weight^{k/2}_m · ‖c_m‖ ≤ √2·(S1+S2) + √B*·(S3+S4).
-/
lemma mt3_unsquared_bound {k : ℕ} (hk : 1 ≤ k)
    (hn : 0 < n) {r : ℝ} (hr : 1 + (n : ℝ) / 2 < r) (hkr : r ≤ (k : ℝ))
    {a b : (Fin n → ℤ) → ℂ}
    (ha : MemSobolev n (k : ℝ) a) (hb : MemSobolev n (k : ℝ) b)
    (m : Fin n → ℤ) :
    weight n ((k : ℝ) / 2) m * ‖seqConv a b m‖ ≤
      Real.sqrt 2 *
        (∑' i, weight n ((k : ℝ) / 2) i * ‖a i‖ * ‖b (m - i)‖ +
         ∑' i, ‖a i‖ * (weight n ((k : ℝ) / 2) (m - i) * ‖b (m - i)‖)) +
      Real.sqrt (mt3BStar k) *
        (∑' i, weight n (((k : ℝ) - 1) / 2) i * ‖a i‖ *
            (weight n (1/2 : ℝ) (m - i) * ‖b (m - i)‖) +
         ∑' i, weight n (1/2 : ℝ) i * ‖a i‖ *
            (weight n (((k : ℝ) - 1) / 2) (m - i) * ‖b (m - i)‖)) := by
  have h_bound : ∀ i : Fin n → ℤ, weight n ((k : ℝ) / 2) m * ‖a i * b (m - i)‖ ≤
    Real.sqrt 2 * (weight n ((k : ℝ) / 2) i * ‖a i‖ * ‖b (m - i)‖ + ‖a i‖ * weight n ((k : ℝ) / 2) (m - i) * ‖b (m - i)‖) +
    Real.sqrt (mt3BStar k) * (weight n (((k : ℝ) - 1) / 2) i * ‖a i‖ * weight n (1 / 2 : ℝ) (m - i) * ‖b (m - i)‖ + weight n (1 / 2 : ℝ) i * ‖a i‖ * weight n (((k : ℝ) - 1) / 2) (m - i) * ‖b (m - i)‖) := by
      intro i
      have h_bound : weight n ((k : ℝ) / 2) m ≤
        Real.sqrt 2 * (weight n ((k : ℝ) / 2) i + weight n ((k : ℝ) / 2) (m - i)) +
        Real.sqrt (mt3BStar k) * (weight n (((k : ℝ) - 1) / 2) i * weight n (1 / 2 : ℝ) (m - i) +
                                   weight n (1 / 2 : ℝ) i * weight n (((k : ℝ) - 1) / 2) (m - i)) := by
        convert refined_weight_half hk i ( m - i ) using 1
        all_goals (first | rfl | norm_num)
      convert mul_le_mul_of_nonneg_right h_bound ( norm_nonneg ( a i * b ( m - i ) ) ) using 1
      all_goals (first | rfl | (norm_num; ring))
  have h_summable : Summable (fun i : Fin n → ℤ => weight n ((k : ℝ) / 2) i * ‖a i‖ * ‖b (m - i)‖) ∧ Summable (fun i : Fin n → ℤ => ‖a i‖ * weight n ((k : ℝ) / 2) (m - i) * ‖b (m - i)‖) ∧ Summable (fun i : Fin n → ℤ => weight n (((k : ℝ) - 1) / 2) i * ‖a i‖ * weight n (1 / 2 : ℝ) (m - i) * ‖b (m - i)‖) ∧ Summable (fun i : Fin n → ℤ => weight n (1 / 2 : ℝ) i * ‖a i‖ * weight n (((k : ℝ) - 1) / 2) (m - i) * ‖b (m - i)‖) := by
    refine' ⟨ _, _, _, _ ⟩;
    · convert summable_alpha_abs_b ( show 0 ≤ ( k : ℝ ) by positivity ) ha ( summable_norm_of_memSobolev hn ( by linarith ) hb ) m using 1;
    · convert summable_abs_a_beta ( show 0 ≤ ( k : ℝ ) by positivity ) ( show Summable fun m => ‖a m‖ from ?_ ) ( show MemSobolev n ( k : ℝ ) b from hb ) m using 1;
      · ac_rfl;
      · exact summable_norm_of_memSobolev hn ( by linarith [ show ( k : ℝ ) ≥ 1 by norm_cast ] ) ha;
    · have h_summable : Summable (fun i : Fin n → ℤ => weight n ((k : ℝ) - 1) i * ‖a i‖ ^ 2) ∧ Summable (fun i : Fin n → ℤ => weight n 1 i * ‖b i‖ ^ 2) := by
        constructor;
        · refine' Summable.of_nonneg_of_le ( fun i => mul_nonneg ( weight_nonneg _ _ ) ( sq_nonneg _ ) ) ( fun i => mul_le_mul_of_nonneg_right ( weight_mono ( by linarith ) _ ) ( sq_nonneg _ ) ) ha;
        · refine' hb.of_nonneg_of_le ( fun i => mul_nonneg ( weight_nonneg _ _ ) ( sq_nonneg _ ) ) ( fun i => mul_le_mul_of_nonneg_right ( weight_mono ( show ( 1 : ℝ ) ≤ k by norm_cast ) _ ) ( sq_nonneg _ ) );
      have h_summable : Summable (fun i : Fin n → ℤ => weight n ((k : ℝ) - 1) i * ‖a i‖ ^ 2 + weight n 1 (m - i) * ‖b (m - i)‖ ^ 2) := by
        exact Summable.add h_summable.1 ( h_summable.2.comp_injective ( sub_right_injective ) );
      refine' .of_nonneg_of_le ( fun i => _ ) ( fun i => _ ) h_summable;
      · exact mul_nonneg ( mul_nonneg ( mul_nonneg ( weight_nonneg _ _ ) ( norm_nonneg _ ) ) ( weight_nonneg _ _ ) ) ( norm_nonneg _ );
      · have h_weight_prod : weight n ((k : ℝ) - 1) i = weight n ((k - 1) / 2) i * weight n ((k - 1) / 2) i ∧ weight n 1 (m - i) = weight n (1 / 2) (m - i) * weight n (1 / 2) (m - i) := by
          unfold weight; ring; norm_num;
          exact ⟨ by rw [ ← Real.rpow_natCast _ 2, ← Real.rpow_mul ( by exact add_nonneg zero_le_one <| Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ] ; ring, by rw [ ← Real.rpow_natCast _ 2, ← Real.rpow_mul ( by exact add_nonneg zero_le_one <| Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ] ; norm_num ⟩;
        rw [ h_weight_prod.1, h_weight_prod.2 ];
        nlinarith only [ sq_nonneg ( weight n ( ( k - 1 ) / 2 ) i * ‖a i‖ - weight n ( 1 / 2 ) ( m - i ) * ‖b ( m - i )‖ ) ];
    · have h_summable : Summable (fun i : Fin n → ℤ => weight n (1 / 2 : ℝ) i * ‖a i‖) := by
        have h_summable_a : Summable (fun i : Fin n → ℤ => ‖a i‖ * weight n (1 / 2) i) := by
          have := summable_weighted_norm hn (by linarith : 1 + (n : ℝ) / 2 < k) (by
          exact ha : MemSobolev n k a)
          simpa only [ mul_comm ] using this;
        simpa only [ mul_comm ] using h_summable_a;
      have h_summable : Summable (fun i : Fin n → ℤ => weight n (1 / 2 : ℝ) i * ‖a i‖ * (weight n ((k - 1) / 2 : ℝ) (m - i) * ‖b (m - i)‖)) := by
        have h_bounded : ∃ C, ∀ i : Fin n → ℤ, weight n ((k - 1) / 2 : ℝ) (m - i) * ‖b (m - i)‖ ≤ C := by
          have h_bounded : ∃ C, ∀ i : Fin n → ℤ, weight n ((k - 1) / 2 : ℝ) i * ‖b i‖ ≤ C := by
            have h_summable : Summable (fun i : Fin n → ℤ => weight n (k : ℝ) i * ‖b i‖ ^ 2) := by
              exact hb
            have h_bounded : ∃ C, ∀ i : Fin n → ℤ, weight n (k : ℝ) i * ‖b i‖ ^ 2 ≤ C := by
              exact ⟨ _, fun i => Summable.le_tsum h_summable i <| fun _ _ => mul_nonneg ( weight_nonneg _ _ ) ( sq_nonneg _ ) ⟩;
            obtain ⟨ C, hC ⟩ := h_bounded;
            use Real.sqrt C;
            intro i
            have h_weight : weight n ((k - 1) / 2 : ℝ) i ^ 2 ≤ weight n (k : ℝ) i := by
              rw [ show ( k : ℝ ) = ( k - 1 ) / 2 + ( k - 1 ) / 2 + 1 by ring ] ; norm_num [ weight ] ; ring_nf ; norm_num;
              rw [ ← Real.rpow_natCast _ 2, ← Real.rpow_mul ( by exact add_nonneg zero_le_one <| Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ] ; ring_nf;
              exact_mod_cast Real.rpow_le_rpow_of_exponent_le ( show 1 + ∑ x : Fin n, ( i x : ℝ ) ^ 2 ≥ 1 by exact le_add_of_nonneg_right <| Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ( show ( -1 + k : ℝ ) ≤ k by linarith );
            exact Real.le_sqrt_of_sq_le ( by nlinarith [ hC i, show 0 ≤ weight n ( ( k - 1 ) / 2 : ℝ ) i from weight_nonneg _ _ ] );
          exact ⟨ h_bounded.choose, fun i => h_bounded.choose_spec _ ⟩
        exact Summable.of_nonneg_of_le ( fun i => mul_nonneg ( mul_nonneg ( weight_nonneg _ _ ) ( norm_nonneg _ ) ) ( mul_nonneg ( weight_nonneg _ _ ) ( norm_nonneg _ ) ) ) ( fun i => mul_le_mul_of_nonneg_left ( h_bounded.choose_spec i ) ( mul_nonneg ( weight_nonneg _ _ ) ( norm_nonneg _ ) ) ) ( h_summable.mul_right _ );
      simpa only [ mul_assoc ] using h_summable;
  have h_summable : Summable (fun i : Fin n → ℤ => a i * b (m - i)) := by
    have h_summable : Summable (fun i : Fin n → ℤ => ‖a i‖ * ‖b (m - i)‖) := by
      have h_summable : Summable (fun i : Fin n → ℤ => ‖a i‖) ∧ Summable (fun i : Fin n → ℤ => ‖b i‖) := by
        exact ⟨ summable_norm_of_memSobolev hn ( by linarith ) ha, summable_norm_of_memSobolev hn ( by linarith ) hb ⟩;
      exact Summable.of_nonneg_of_le ( fun i => mul_nonneg ( norm_nonneg _ ) ( norm_nonneg _ ) ) ( fun i => mul_le_mul_of_nonneg_left ( Summable.le_tsum ( h_summable.2 ) ( m - i ) ( by norm_num ) ) ( norm_nonneg _ ) ) ( h_summable.1.mul_right _ );
    exact .of_norm <| by simpa using h_summable;
  have h_summable : weight n ((k : ℝ) / 2) m * ‖∑' i : Fin n → ℤ, a i * b (m - i)‖ ≤ ∑' i : Fin n → ℤ, weight n ((k : ℝ) / 2) m * ‖a i * b (m - i)‖ := by
    rw [ tsum_mul_left ];
    exact mul_le_mul_of_nonneg_left ( norm_tsum_le_tsum_norm ( by simpa using h_summable.norm ) ) ( weight_nonneg _ _ );
  refine le_trans h_summable <| le_trans ( Summable.tsum_le_tsum h_bound ?_ ?_ ) ?_;
  · exact Summable.mul_left _ ( by simpa [ norm_mul ] using Summable.norm ‹Summable fun i : Fin n → ℤ => a i * b ( m - i ) › );
  · exact Summable.add ( Summable.mul_left _ ( Summable.add ( by tauto ) ( by tauto ) ) ) ( Summable.mul_left _ ( Summable.add ( by tauto ) ( by tauto ) ) );
  · rw [ Summable.tsum_add, Summable.tsum_mul_left, Summable.tsum_mul_left ];
    · simp_all +decide [ mul_assoc, Summable.tsum_add ];
    · exact Summable.add ( by tauto ) ( by tauto );
    · exact Summable.add ( by tauto ) ( by tauto );
    · exact Summable.mul_left _ ( Summable.add ( by tauto ) ( by tauto ) );
    · exact Summable.mul_left _ ( Summable.add ( by tauto ) ( by tauto ) )

/-
Squared pointwise bound derived from the unsquared version.
-/
lemma mt3_pointwise_sq_bound {k : ℕ} (hk : 1 ≤ k)
    (hn : 0 < n) {r : ℝ} (hr : 1 + (n : ℝ) / 2 < r) (hkr : r ≤ (k : ℝ))
    {a b : (Fin n → ℤ) → ℂ}
    (ha : MemSobolev n (k : ℝ) a) (hb : MemSobolev n (k : ℝ) b)
    (m : Fin n → ℤ) :
    weight n (k : ℝ) m * ‖seqConv a b m‖ ^ 2 ≤
      8 * ((∑' i, weight n ((k : ℝ) / 2) i * ‖a i‖ * ‖b (m - i)‖) ^ 2 +
           (∑' i, ‖a i‖ * (weight n ((k : ℝ) / 2) (m - i) * ‖b (m - i)‖)) ^ 2) +
      4 * mt3BStar k *
        ((∑' i, weight n (((k : ℝ) - 1) / 2) i * ‖a i‖ *
            (weight n (1/2 : ℝ) (m - i) * ‖b (m - i)‖)) ^ 2 +
         (∑' i, weight n (1/2 : ℝ) i * ‖a i‖ *
            (weight n (((k : ℝ) - 1) / 2) (m - i) * ‖b (m - i)‖)) ^ 2) := by
  have h_sq : (weight n ((k : ℝ) / 2) m * ‖seqConv a b m‖)^2 ≤ (Real.sqrt 2 * ( (∑' i, weight n ((k : ℝ) / 2) i * ‖a i‖ * ‖b (m - i)‖) + (∑' i, ‖a i‖ * (weight n ((k : ℝ) / 2) (m - i) * ‖b (m - i)‖)) ) + Real.sqrt (mt3BStar k) * ( (∑' i, weight n (((k : ℝ) - 1) / 2) i * ‖a i‖ * (weight n (1/2 : ℝ) (m - i) * ‖b (m - i)‖)) + (∑' i, weight n (1/2 : ℝ) i * ‖a i‖ * (weight n (((k : ℝ) - 1) / 2) (m - i) * ‖b (m - i)‖)) ))^2 := by
    apply_rules [ pow_le_pow_left₀, mt3_unsquared_bound ]
    exact mul_nonneg ( weight_nonneg _ _ ) ( norm_nonneg _ )
  refine le_trans ?_ ( h_sq.trans ?_ )
  · rw [ weight_half_mul ] ; ring_nf ; norm_num
  · have h_sq : ∀ x y : ℝ, (Real.sqrt 2 * x + Real.sqrt (mt3BStar k) * y)^2 ≤ 2 * 2 * x^2 + 2 * mt3BStar k * y^2 := by
      intro x y; nlinarith only [ sq_nonneg ( Real.sqrt 2 * x - Real.sqrt ( mt3BStar k ) * y ), Real.mul_self_sqrt ( show 0 ≤ 2 by norm_num ), Real.mul_self_sqrt ( show 0 ≤ mt3BStar k by exact mt3BStar_nonneg hk ) ]
    refine le_trans ( h_sq _ _ ) ?_
    nlinarith only [ sq_nonneg ( ( ∑' i : Fin n → ℤ, weight n ( k / 2 ) i * ‖a i‖ * ‖b ( m - i )‖ ) - ( ∑' i : Fin n → ℤ, ‖a i‖ * ( weight n ( k / 2 ) ( m - i ) * ‖b ( m - i )‖ ) ) ), sq_nonneg ( ( ∑' i : Fin n → ℤ, weight n ( ( k - 1 ) / 2 ) i * ‖a i‖ * ( weight n ( 1 / 2 ) ( m - i ) * ‖b ( m - i )‖ ) ) - ( ∑' i : Fin n → ℤ, weight n ( 1 / 2 ) i * ‖a i‖ * ( weight n ( ( k - 1 ) / 2 ) ( m - i ) * ‖b ( m - i )‖ ) ) ), show 0 ≤ mt3BStar k from mt3BStar_nonneg hk ]

/-! ## Main theorems -/

theorem third_multiplication_theorem_seq
    {n : Nat} (hn : 0 < n) {r : Real} (hr : 1 + (n : Real) / 2 < r)
    {k : Nat} (hkr : r ≤ (k : Real))
    {a b : (Fin n → Int) → Complex}
    (ha : MemSobolev n k a) (hb : MemSobolev n k b) :
    And (MemSobolev n k (seqConv a b))
        (sobolevNormSq n k (seqConv a b)
           ≤ mt3AConstSq n r
              * (sobolevNormSq n k a * sobolevNormSq n r b
                 + sobolevNormSq n r a * sobolevNormSq n k b)
             + mt3BConstSq n k r
              * (sobolevNormSq n ((k : Real) - 1) a * sobolevNormSq n r b
                 + sobolevNormSq n r a * sobolevNormSq n ((k : Real) - 1) b)) := by
  -- Apply the second multiplication theorem to get the MemSobolev part.
  have h_mem : MemSobolev n (k : ℝ) (seqConv a b) := by
    exact second_multiplication_theorem_seq hn ( by linarith ) ha hb |>.1;
  refine' ⟨ h_mem, _ ⟩;
  have h_sum : ∀ m : Fin n → ℤ, weight n (k : ℝ) m * ‖seqConv a b m‖ ^ 2 ≤
    8 * ((∑' i, weight n ((k : ℝ) / 2) i * ‖a i‖ * ‖b (m - i)‖) ^ 2 +
         (∑' i, ‖a i‖ * (weight n ((k : ℝ) / 2) (m - i) * ‖b (m - i)‖)) ^ 2) +
    4 * mt3BStar k *
      ((∑' i, weight n (((k : ℝ) - 1) / 2) i * ‖a i‖ *
          (weight n (1/2 : ℝ) (m - i) * ‖b (m - i)‖)) ^ 2 +
       (∑' i, weight n (1/2 : ℝ) i * ‖a i‖ *
          (weight n (((k : ℝ) - 1) / 2) (m - i) * ‖b (m - i)‖)) ^ 2) := by
            apply mt3_pointwise_sq_bound;
            exacts [ Nat.one_le_iff_ne_zero.mpr ( by rintro rfl; norm_num at *; linarith [ show ( n : ℝ ) ≥ 1 by norm_cast ] ), hn, hr, hkr, ha, hb ];
  refine' le_trans ( Summable.tsum_le_tsum h_sum _ _ ) _;
  · convert h_mem using 1
    all_goals rfl
  · refine' Summable.add _ _;
    · have := mt3_young_S1 hn hr hkr ha ( show MemSobolev n r b from ?_ );
      · have := mt3_young_S2 hn hr hkr ( show MemSobolev n r a from ?_ ) hb;
        · exact Summable.mul_left _ ( Summable.add ( by tauto ) ( by tauto ) );
        · exact ha.mono ( by linarith );
      · exact hb.mono ( by linarith );
    · refine' Summable.mul_left _ _;
      refine' Summable.add _ _;
      · convert mt3_young_S3 hn hr hkr _ _ |>.1 using 1;
        · exact ha.mono ( by linarith );
        · exact hb.mono ( by linarith );
      · convert mt3_young_S4 hn hr hkr _ _ |>.1 using 1;
        · exact ha.mono ( by linarith );
        · exact MemSobolev.mono hb ( by linarith );
  · rw [ Summable.tsum_add ];
    · refine' add_le_add _ _;
      · rw [ tsum_mul_left, Summable.tsum_add ];
        · have := mt3_young_S1 hn hr hkr ha ( show MemSobolev n r b from ?_ );
          · have := mt3_young_S2 hn hr hkr ( show MemSobolev n r a from ?_ ) hb;
            · unfold mt3AConstSq; nlinarith;
            · exact ha.mono ( by linarith );
          · exact hb.mono ( by linarith );
        · have := mt3_young_S1 hn hr hkr ha ( show MemSobolev n r b from ?_ );
          · exact this.1;
          · exact hb.mono ( by linarith );
        · convert mt3_young_S2 hn hr hkr ( show MemSobolev n r a from ?_ ) ( show MemSobolev n ( k : ℝ ) b from ?_ ) |>.1 using 1;
          · exact ha.mono ( by linarith );
          · exact hb;
      · rw [ tsum_mul_left, Summable.tsum_add ];
        · unfold mt3BConstSq;
          rw [ mul_assoc ];
          rw [ mul_assoc, mul_assoc ];
          gcongr;
          · exact mt3BStar_nonneg ( Nat.one_le_iff_ne_zero.mpr ( by rintro rfl; norm_num at *; linarith [ show ( n : ℝ ) ≥ 1 by norm_cast ] ) );
          · convert add_le_add ( mt3_young_S3 hn hr hkr ( show MemSobolev n ( ( k : ℝ ) - 1 ) a from ?_ ) ( show MemSobolev n r b from ?_ ) |>.2 ) ( mt3_young_S4 hn hr hkr ( show MemSobolev n r a from ?_ ) ( show MemSobolev n ( ( k : ℝ ) - 1 ) b from ?_ ) |>.2 ) using 1;
            · ring;
            · exact MemSobolev.mono ha ( by linarith );
            · exact MemSobolev.mono hb ( by linarith );
            · exact ha.mono ( by linarith );
            · exact MemSobolev.mono hb ( by linarith );
        · convert mt3_young_S3 hn hr hkr _ _ |>.1 using 1;
          · exact ha.mono ( by linarith );
          · exact hb.mono ( by linarith );
        · convert mt3_young_S4 hn hr hkr _ _ |>.1 using 1;
          · exact ha.mono ( by linarith );
          · exact MemSobolev.mono hb ( by linarith );
    · refine' Summable.mul_left _ _;
      refine' Summable.add _ _;
      · have := mt3_young_S1 hn ( by linarith ) ( by linarith ) ha hb;
        exact this.1;
      · apply (mt3_young_S2 hn hr hkr (by
        exact ha.mono ( by linarith )) (by
        exact hb)).left;
    · have := mt3_young_S3 hn hr hkr ( show MemSobolev n ( ( k : ℝ ) - 1 ) a from ?_ ) ( show MemSobolev n r b from ?_ );
      · have := mt3_young_S4 hn hr hkr ( show MemSobolev n r a from ?_ ) ( show MemSobolev n ( ( k : ℝ ) - 1 ) b from ?_ );
        · exact Summable.mul_left _ ( Summable.add ( by tauto ) ( by tauto ) );
        · exact ha.mono ( by linarith );
        · exact MemSobolev.mono hb ( by linarith );
      · exact ha.mono ( by linarith );
      · grind +suggestions

theorem third_multiplication_theorem
    {n : Nat} (hn : 0 < n) {r : Real} (hr : 1 + (n : Real) / 2 < r)
    {k : Nat} (hkr : r ≤ (k : Real))
    {u v : TrigPolyDual n}
    (hu : MemSobolevDistrib n k u) (hv : MemSobolevDistrib n k v) :
    And (MemSobolevDistrib n k (sobolevMulDistrib u v))
        (sobolevNormSqDistrib n k (sobolevMulDistrib u v)
           ≤ mt3AConstSq n r
              * (sobolevNormSqDistrib n k u * sobolevNormSqDistrib n r v
                 + sobolevNormSqDistrib n r u * sobolevNormSqDistrib n k v)
             + mt3BConstSq n k r
              * (sobolevNormSqDistrib n ((k : Real) - 1) u * sobolevNormSqDistrib n r v
                 + sobolevNormSqDistrib n r u * sobolevNormSqDistrib n ((k : Real) - 1) v)) := by
  unfold MemSobolevDistrib at *;
  unfold sobolevNormSqDistrib;
  convert third_multiplication_theorem_seq hn hr hkr hu hv using 1;
  · unfold sobolevMulDistrib;
    rw [ fourierCoeffDistrib_seqToDual ];
  · unfold sobolevMulDistrib;
    rw [ fourierCoeffDistrib_seqToDual ]

end NashEmbedding.Sobolev

end
