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

/-!
# Compact Inclusion of Weighted ℓ² Spaces

For `s < t`, the inclusion map `ℓ²_(t)(ℤⁿ) → ℓ²_(s)(ℤⁿ)` is a compact operator.

The proof uses the fact that the inclusion is given by pointwise multiplication
by `(1 + |m|²)^{(s-t)/2}`, which tends to 0 as `|m| → ∞` when `s < t`,
making it a compact (in fact, approximable by finite-rank) operator.

In this file we state the result in the following concrete form:
any sequence in the unit ball of `ℓ²_(t)` has a subsequence that converges in `ℓ²_(s)`.
-/

open scoped BigOperators
open NashEmbedding.Sobolev

noncomputable section

namespace NashEmbedding.Sobolev

variable {n : ℕ}

/-
Auxiliary: the ratio `weight n s m / weight n t m = weight n (s - t) m`,
which tends to 0 when `s < t`.
-/
lemma weight_ratio (s t : ℝ) (m : Fin n → ℤ) :
    weight n s m / weight n t m = weight n (s - t) m := by
  unfold weight;
  rw [ Real.rpow_sub ( by exact add_pos_of_pos_of_nonneg zero_lt_one ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ) ]

/-
When `s < t`, the weight ratio `(1 + |m|²)^{(s-t)/2}` tends to 0
as `m` varies over `Fin n → ℤ` and `|m| → ∞`.
-/
lemma weight_tendsto_zero_of_lt {s t : ℝ} (hst : s < t) :
    Filter.Tendsto (fun m : Fin n → ℤ => weight n ((s - t) / 2) m)
      (Filter.cofinite) (nhds 0) := by
  -- The weight ratio `(1 + |m|²)^{(s-t)/2}` tends to 0 as `|m| → ∞`.
  have h_weight_ratio_zero : Filter.Tendsto (fun m : ℝ => (1 + m) ^ ((s - t) / 2)) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun m : ℝ => m ^ ((s - t) / 2)) Filter.atTop (nhds 0) := by
      have := tendsto_rpow_neg_atTop (show 0 < -((s - t) / 2) by linarith)
      simpa using this
    have h2 : Filter.Tendsto (fun m : ℝ => 1 + m) Filter.atTop Filter.atTop :=
      tendsto_const_nhds.add_atTop Filter.tendsto_id
    simpa [Function.comp_def] using h1.comp h2
  refine h_weight_ratio_zero.comp ?_;
  refine' Filter.tendsto_atTop.2 fun x => _;
  refine' Set.Finite.subset ( Set.finite_Icc ( -⌈x⌉₊ : Fin n → ℤ ) ⌈x⌉₊ ) _;
  intro m hm; constructor <;> intro i <;> norm_num at *;
  · exact neg_le.mpr ( Int.le_of_lt_add_one <| by rw [ ← @Int.cast_lt ℝ ] ; push_cast; nlinarith [ Nat.le_ceil x, Finset.single_le_sum ( fun a _ => sq_nonneg ( m a : ℝ ) ) ( Finset.mem_univ i ) ] );
  · exact Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℝ ] ; push_cast; nlinarith [ Nat.le_ceil x, Finset.single_le_sum ( fun a _ => sq_nonneg ( m a : ℝ ) ) ( Finset.mem_univ i ) ] )

/-
**Compact inclusion of weighted ℓ² spaces (concrete version).**
For `s < t`, if `(aₖ)` is a sequence in the unit ball of `ℓ²_(t)`,
then there exists a subsequence converging in the `ℓ²_(s)` norm.
More precisely: if `sobolevNormSq n t (a k) ≤ 1` for all `k`,
then there exist a function `φ : ℕ → ℕ` (strictly monotone) and
a limit `b` such that `sobolevNormSq n s (a (φ k) - b) → 0`.
-/
theorem compactInclusion_lp_weighted {s t : ℝ} (hst : s < t)
    (a : ℕ → (Fin n → ℤ) → ℂ)
    (ha_mem : ∀ k, MemSobolev n t (a k))
    (ha_bdd : ∀ k, sobolevNormSq n t (a k) ≤ 1) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧
    ∃ (b : (Fin n → ℤ) → ℂ), MemSobolev n s b ∧
      Filter.Tendsto (fun k => sobolevNormSq n s (fun m => a (φ k) m - b m))
        Filter.atTop (nhds 0) := by
  -- This is a standard but technically involved argument. It requires:
  -- - Countable diagonal extraction (exists in Mathlib as `tendsto_subseq_of_bounded` or similar)
  -- - The key estimate using the weight ratio
  obtain ⟨φ, hφ_mono, a_lim⟩ : ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ a_lim : ((Fin n) → ℤ) → ℂ, ∀ m, (Filter.Tendsto (fun k => (a (φ k) m)) Filter.atTop (nhds (a_lim m))) := by
    -- By the properties of the ℓ² space, the sequence (a k) is pointwise bounded.
    have h_pointwise_bounded : ∀ m : Fin n → ℤ, ∃ C : ℝ, ∀ k, ‖(a k m)‖ ≤ C := by
      intro m
      use 1 / Real.sqrt (weight n t m);
      intro k
      have h_norm_sq : weight n t m * ‖a k m‖ ^ 2 ≤ 1 := by
        exact le_trans ( Summable.le_tsum ( ha_mem k |> fun h => h ) m ( fun _ _ => mul_nonneg ( Real.rpow_nonneg ( add_nonneg zero_le_one ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ) _ ) ( sq_nonneg _ ) ) ) ( ha_bdd k );
      rw [ le_div_iff₀ ] <;> nlinarith [ show 0 < weight n t m from weight_pos t m, Real.sqrt_nonneg ( weight n t m ), Real.mul_self_sqrt ( show 0 ≤ weight n t m from weight_nonneg t m ) ];
    have h_compact : IsCompact (Set.pi Set.univ fun m : Fin n → ℤ => Metric.closedBall (0 : ℂ) (Classical.choose (h_pointwise_bounded m))) := by
      exact isCompact_univ_pi fun m => ProperSpace.isCompact_closedBall _ _;
    have := h_compact.isSeqCompact fun k => show a k ∈ Set.pi Set.univ fun m => Metric.closedBall 0 ( Classical.choose ( h_pointwise_bounded m ) ) from fun m _ => mem_closedBall_zero_iff.mpr ( Classical.choose_spec ( h_pointwise_bounded m ) k );
    exact ⟨ this.choose_spec.2.choose, this.choose_spec.2.choose_spec.1, this.choose, fun m => tendsto_pi_nhds.mp this.choose_spec.2.choose_spec.2 m ⟩;
  obtain ⟨ a_lim, ha_lim ⟩ := a_lim;
  -- We show that `a_lim` belongs to `ℓ²_(t)` and that `‖a_lim - a(φ(k))‖²_(s)` tends to zero.
  have ha_lim_mem : MemSobolev n t a_lim := by
    -- By the dominated convergence theorem, we can interchange the limit and the sum.
    have h_dominated : ∀ N : Finset ((Fin n) → ℤ), ∑ m ∈ N, weight n t m * ‖a_lim m‖ ^ 2 ≤ 1 := by
      intro N
      have h_dominated : ∀ k, ∑ m ∈ N, weight n t m * ‖a (φ k) m‖ ^ 2 ≤ 1 := by
        exact fun k => le_trans ( Summable.sum_le_tsum ( N ) ( fun _ _ => mul_nonneg ( weight_nonneg _ _ ) ( sq_nonneg _ ) ) ( ha_mem _ ) ) ( ha_bdd _ );
      exact le_of_tendsto_of_tendsto' ( tendsto_finsetSum _ fun m _ => Filter.Tendsto.mul ( tendsto_const_nhds ) ( Filter.Tendsto.pow ( Filter.Tendsto.norm ( ha_lim m ) ) 2 ) ) tendsto_const_nhds h_dominated;
    refine' summable_of_sum_le _ _;
    exacts [ 1, fun m => mul_nonneg ( weight_nonneg _ _ ) ( sq_nonneg _ ), h_dominated ]
  have ha_lim_conv : Filter.Tendsto (fun k => sobolevNormSq n s (fun m => (a (φ k) m) - (a_lim m))) Filter.atTop (nhds 0) := by
    -- For any ε > 0, choose a finite set F ⊂ ℤⁿ such that ∑_{m ∉ F} weight(s-t) m < ε.
    have h_eps : ∀ ε > 0, ∃ F : Finset ((Fin n) → ℤ), ∀ k, (∑' m, weight n s m * ‖(a (φ k) m) - (a_lim m)‖ ^ 2) ≤ (∑ m ∈ F, weight n s m * ‖(a (φ k) m) - (a_lim m)‖ ^ 2) + ε := by
      intro ε hε_pos
      obtain ⟨F, hF⟩ : ∃ F : Finset ((Fin n) → ℤ), ∀ m ∉ F, weight n (s - t) m < ε / 4 := by
        have h_eps : Filter.Tendsto (fun m : ((Fin n) → ℤ) => weight n ((s - t) / 2) m) (Filter.cofinite) (nhds 0) := by
          exact weight_tendsto_zero_of_lt ( by linarith );
        have := h_eps.eventually ( gt_mem_nhds <| show 0 < Real.sqrt ( ε / 4 ) by positivity );
        obtain ⟨ F, hF ⟩ := this.exists_finset;
        use F;
        intro m hm; replace hm : weight n ((s - t) / 2) m < Real.sqrt (ε / 4) := by
          simpa using (hF m).not.mp hm
        simp_all +decide [ weight ] ;
        have hX : (0:ℝ) ≤ 1 + ∑ i : Fin n, ((m i : ℝ) ^ 2) :=
          add_nonneg zero_le_one <| Finset.sum_nonneg fun _ _ => sq_nonneg _
        convert pow_lt_pow_left₀ hm ( Real.rpow_nonneg hX _ ) two_ne_zero using 1
        all_goals first
        | rfl
        | (rw [div_pow, Real.sq_sqrt hε_pos.le, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 4)])
        | (rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hX]; congr 1; push_cast; ring)
      use F;
      intro k
      have h_split : ∑' m, weight n s m * ‖(a (φ k) m) - (a_lim m)‖ ^ 2 = ∑ m ∈ F, weight n s m * ‖(a (φ k) m) - (a_lim m)‖ ^ 2 + ∑' m, weight n s m * ‖(a (φ k) m) - (a_lim m)‖ ^ 2 * (if m ∈ F then 0 else 1) := by
        have h_split : ∑' m, weight n s m * ‖(a (φ k) m) - (a_lim m)‖ ^ 2 = ∑' m, weight n s m * ‖(a (φ k) m) - (a_lim m)‖ ^ 2 * (if m ∈ F then 1 else 0) + ∑' m, weight n s m * ‖(a (φ k) m) - (a_lim m)‖ ^ 2 * (if m ∈ F then 0 else 1) := by
          rw [ ← Summable.tsum_add ] ; congr ; ext m ; aesop;
          · refine' summable_of_ne_finset_zero _;
            exacts [ F, fun m hm => by rw [ if_neg hm ] ; ring ];
          · have h_summable : Summable (fun m => weight n s m * ‖(a (φ k) m) - (a_lim m)‖ ^ 2) := by
              have h_summable : Summable (fun m => weight n t m * ‖(a (φ k) m) - (a_lim m)‖ ^ 2) := by
                have h_summable : Summable (fun m => weight n t m * ‖a (φ k) m‖ ^ 2) ∧ Summable (fun m => weight n t m * ‖a_lim m‖ ^ 2) := by
                  exact ⟨ ha_mem _, ha_lim_mem ⟩;
                have h_summable : Summable (fun m => weight n t m * (‖a (φ k) m‖ ^ 2 + ‖a_lim m‖ ^ 2)) := by
                  simpa only [ mul_add ] using h_summable.1.add h_summable.2;
                refine' .of_nonneg_of_le ( fun m => mul_nonneg ( weight_nonneg _ _ ) ( sq_nonneg _ ) ) ( fun m => _ ) ( h_summable.mul_left 2 );
                have h_triangle : ‖a (φ k) m - a_lim m‖ ^ 2 ≤ 2 * (‖a (φ k) m‖ ^ 2 + ‖a_lim m‖ ^ 2) := by
                  nlinarith only [ norm_nonneg ( a ( φ k ) m - a_lim m ), norm_sub_le ( a ( φ k ) m ) ( a_lim m ), sq_nonneg ( ‖a ( φ k ) m‖ - ‖a_lim m‖ ) ];
                nlinarith only [ h_triangle, weight_nonneg t m ];
              refine' .of_nonneg_of_le ( fun m => mul_nonneg ( weight_nonneg _ _ ) ( sq_nonneg _ ) ) ( fun m => mul_le_mul_of_nonneg_right ( weight_mono hst.le _ ) ( sq_nonneg _ ) ) h_summable;
            exact Summable.of_nonneg_of_le ( fun m => mul_nonneg ( mul_nonneg ( weight_nonneg _ _ ) ( sq_nonneg _ ) ) ( by split_ifs <;> norm_num ) ) ( fun m => mul_le_of_le_one_right ( mul_nonneg ( weight_nonneg _ _ ) ( sq_nonneg _ ) ) ( by split_ifs <;> norm_num ) ) h_summable;
        convert h_split using 2;
        rw [ tsum_eq_sum ];
        exacts [ Finset.sum_congr rfl fun x hx => by rw [ if_pos hx, mul_one ], fun x hx => by rw [ if_neg hx, MulZeroClass.mul_zero ] ];
      -- For the second sum, we use the fact that $|a(φ(k)) m - a_lim m|^2 \leq 2(|a(φ(k)) m|^2 + |a_lim m|^2)$ and the boundedness of the norms.
      have h_second_sum : ∑' m, weight n s m * ‖(a (φ k) m) - (a_lim m)‖ ^ 2 * (if m ∈ F then 0 else 1) ≤ 2 * ∑' m, weight n t m * (‖(a (φ k) m)‖ ^ 2 + ‖(a_lim m)‖ ^ 2) * weight n (s - t) m * (if m ∈ F then 0 else 1) := by
        have h_second_sum : ∀ m, weight n s m * ‖(a (φ k) m) - (a_lim m)‖ ^ 2 ≤ 2 * weight n t m * (‖(a (φ k) m)‖ ^ 2 + ‖(a_lim m)‖ ^ 2) * weight n (s - t) m := by
          intro m
          have h_second_sum : weight n s m = weight n t m * weight n (s - t) m := by
            grind +suggestions;
          rw [ h_second_sum ];
          have h_second_sum : ‖(a (φ k) m) - (a_lim m)‖ ^ 2 ≤ 2 * (‖(a (φ k) m)‖ ^ 2 + ‖(a_lim m)‖ ^ 2) := by
            nlinarith only [ norm_nonneg ( a ( φ k ) m - a_lim m ), norm_sub_le ( a ( φ k ) m ) ( a_lim m ), sq_nonneg ( ‖a ( φ k ) m‖ - ‖a_lim m‖ ) ];
          nlinarith only [ h_second_sum, show 0 ≤ weight n t m * weight n ( s - t ) m by exact mul_nonneg ( weight_nonneg _ _ ) ( weight_nonneg _ _ ) ];
        rw [ ← tsum_mul_left ];
        refine' Summable.tsum_le_tsum _ _ _;
        · intro m; specialize h_second_sum m; split_ifs <;> simp_all +decide [ mul_assoc ] ;
        · have h_summable : Summable (fun m => weight n s m * ‖(a (φ k) m) - (a_lim m)‖ ^ 2) := by
            have h_summable : Summable (fun m => weight n t m * ‖(a (φ k) m) - (a_lim m)‖ ^ 2) := by
              have h_summable : Summable (fun m => weight n t m * ‖a (φ k) m‖ ^ 2) ∧ Summable (fun m => weight n t m * ‖a_lim m‖ ^ 2) := by
                exact ⟨ ha_mem ( φ k ), ha_lim_mem ⟩;
              have h_summable : Summable (fun m => weight n t m * (‖a (φ k) m‖ ^ 2 + ‖a_lim m‖ ^ 2)) := by
                simpa only [ mul_add ] using h_summable.1.add h_summable.2;
              refine' .of_nonneg_of_le ( fun m => mul_nonneg ( weight_nonneg _ _ ) ( sq_nonneg _ ) ) ( fun m => _ ) ( h_summable.mul_left 2 );
              have h_triangle : ‖a (φ k) m - a_lim m‖ ^ 2 ≤ 2 * (‖a (φ k) m‖ ^ 2 + ‖a_lim m‖ ^ 2) := by
                nlinarith only [ norm_nonneg ( a ( φ k ) m - a_lim m ), norm_sub_le ( a ( φ k ) m ) ( a_lim m ), sq_nonneg ( ‖a ( φ k ) m‖ - ‖a_lim m‖ ) ];
              nlinarith only [ h_triangle, weight_nonneg t m ];
            refine' .of_nonneg_of_le ( fun m => mul_nonneg ( weight_nonneg _ _ ) ( sq_nonneg _ ) ) ( fun m => _ ) h_summable;
            exact mul_le_mul_of_nonneg_right ( weight_mono hst.le m ) ( sq_nonneg _ );
          exact Summable.of_nonneg_of_le ( fun m => mul_nonneg ( mul_nonneg ( weight_nonneg _ _ ) ( sq_nonneg _ ) ) ( by split_ifs <;> norm_num ) ) ( fun m => mul_le_of_le_one_right ( mul_nonneg ( weight_nonneg _ _ ) ( sq_nonneg _ ) ) ( by split_ifs <;> norm_num ) ) h_summable;
        · have h_summable : Summable (fun m => weight n t m * (‖(a (φ k) m)‖ ^ 2 + ‖(a_lim m)‖ ^ 2)) := by
            have h_summable : Summable (fun m => weight n t m * ‖(a (φ k) m)‖ ^ 2) ∧ Summable (fun m => weight n t m * ‖(a_lim m)‖ ^ 2) := by
              exact ⟨ ha_mem ( φ k ), ha_lim_mem ⟩;
            simpa only [ mul_add ] using h_summable.1.add h_summable.2;
          refine' Summable.mul_left _ _;
          refine' Summable.of_nonneg_of_le ( fun m => _ ) ( fun m => _ ) ( h_summable.mul_right ( ε / 4 ) );
          · exact mul_nonneg ( mul_nonneg ( mul_nonneg ( weight_nonneg _ _ ) ( by positivity ) ) ( weight_nonneg _ _ ) ) ( by positivity );
          · split_ifs <;> simp_all +decide [ mul_assoc ];
            · exact mul_nonneg ( weight_nonneg _ _ ) ( mul_nonneg ( add_nonneg ( sq_nonneg _ ) ( sq_nonneg _ ) ) ( by positivity ) );
            · exact mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( le_of_lt ( hF m ‹_› ) ) ( by positivity ) ) ( by exact Real.rpow_nonneg ( by exact add_nonneg zero_le_one ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ) _ );
      -- Since $weight n (s - t) m < ε / 4$ for $m ∉ F$, we can bound the second sum.
      have h_second_sum_bound : ∑' m, weight n t m * (‖(a (φ k) m)‖ ^ 2 + ‖(a_lim m)‖ ^ 2) * weight n (s - t) m * (if m ∈ F then 0 else 1) ≤ (ε / 4) * ∑' m, weight n t m * (‖(a (φ k) m)‖ ^ 2 + ‖(a_lim m)‖ ^ 2) := by
        rw [ ← tsum_mul_left ];
        refine' Summable.tsum_le_tsum _ _ _;
        · intro m; split_ifs <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
          · exact mul_nonneg ( add_nonneg ( sq_nonneg _ ) ( sq_nonneg _ ) ) ( mul_nonneg ( by positivity ) ( weight_nonneg _ _ ) );
          · exact mul_le_mul_of_nonneg_left ( by nlinarith only [ hF m ‹_›, show 0 ≤ weight n t m from weight_nonneg _ _ ] ) ( by positivity );
        · have h_second_sum_bound : Summable (fun m => weight n t m * (‖(a (φ k) m)‖ ^ 2 + ‖(a_lim m)‖ ^ 2)) := by
            have h_second_sum_bound : Summable (fun m => weight n t m * ‖(a (φ k) m)‖ ^ 2) ∧ Summable (fun m => weight n t m * ‖(a_lim m)‖ ^ 2) := by
              exact ⟨ ha_mem ( φ k ), ha_lim_mem ⟩;
            simpa only [ mul_add ] using h_second_sum_bound.1.add h_second_sum_bound.2;
          refine' Summable.of_nonneg_of_le ( fun m => _ ) ( fun m => _ ) h_second_sum_bound;
          · exact mul_nonneg ( mul_nonneg ( mul_nonneg ( weight_nonneg _ _ ) ( by positivity ) ) ( weight_nonneg _ _ ) ) ( by positivity );
          · split_ifs <;> norm_num;
            · exact mul_nonneg ( weight_nonneg _ _ ) ( add_nonneg ( sq_nonneg _ ) ( sq_nonneg _ ) );
            · exact mul_le_of_le_one_right ( mul_nonneg ( weight_nonneg _ _ ) ( add_nonneg ( sq_nonneg _ ) ( sq_nonneg _ ) ) ) ( weight_le_one_of_nonpos ( by linarith ) _ );
        · refine' Summable.mul_left _ _;
          have := ha_mem ( φ k );
          convert this.add ha_lim_mem using 1
          ext m; ring
      -- Since $\sum' m, weight n t m * (‖a (φ k) m‖ ^ 2 + ‖a_lim m‖ ^ 2) \leq 2$, we can bound the second sum.
      have h_second_sum_final : ∑' m, weight n t m * (‖a (φ k) m‖ ^ 2 + ‖a_lim m‖ ^ 2) ≤ 2 := by
        have h_second_sum_final : ∑' m, weight n t m * ‖a (φ k) m‖ ^ 2 ≤ 1 ∧ ∑' m, weight n t m * ‖a_lim m‖ ^ 2 ≤ 1 := by
          apply And.intro;
          · exact ha_bdd ( φ k );
          · have h_second_sum_final : ∀ N : Finset ((Fin n) → ℤ), ∑ m ∈ N, weight n t m * ‖a_lim m‖ ^ 2 ≤ 1 := by
              intro N
              have h_second_sum_final : ∀ k, ∑ m ∈ N, weight n t m * ‖a (φ k) m‖ ^ 2 ≤ 1 := by
                intro k;
                exact le_trans ( Summable.sum_le_tsum _ ( fun _ _ => mul_nonneg ( weight_nonneg _ _ ) ( sq_nonneg _ ) ) ( ha_mem _ ) ) ( ha_bdd _ );
              exact le_of_tendsto_of_tendsto' ( tendsto_finsetSum _ fun m _ => Filter.Tendsto.mul ( tendsto_const_nhds ) ( Filter.Tendsto.pow ( Filter.Tendsto.norm ( ha_lim m ) ) 2 ) ) tendsto_const_nhds h_second_sum_final;
            contrapose! h_second_sum_final;
            exact ( Summable.hasSum ( show Summable _ from by exact ( by { by_contra h; rw [ tsum_eq_zero_of_not_summable h ] at h_second_sum_final; linarith } ) ) ) |> fun h => h.eventually ( lt_mem_nhds h_second_sum_final ) |> fun h => h.exists;
        convert add_le_add h_second_sum_final.1 h_second_sum_final.2 using 1
        · rw [ ← Summable.tsum_add ] ; congr ; ext m ; ring
          · exact ha_mem ( φ k );
          · exact ha_lim_mem;
        · norm_num;
      nlinarith;
    rw [ Metric.tendsto_nhds ];
    intro ε hε_pos
    obtain ⟨F, hF⟩ := h_eps (ε / 2) (half_pos hε_pos);
    -- Since `a(φ(k))` converges pointwise to `a_lim`, the sum over `F` tends to zero.
    have h_sum_F_zero : Filter.Tendsto (fun k => ∑ m ∈ F, weight n s m * ‖(a (φ k) m) - (a_lim m)‖ ^ 2) Filter.atTop (nhds 0) := by
      exact le_trans ( tendsto_finsetSum _ fun m _ => Filter.Tendsto.mul tendsto_const_nhds <| Filter.Tendsto.pow ( Filter.Tendsto.norm <| Filter.Tendsto.sub ( ha_lim m ) tendsto_const_nhds ) _ ) <| by norm_num;
    filter_upwards [ h_sum_F_zero.eventually ( gt_mem_nhds <| half_pos hε_pos ) ] with k hk using abs_lt.mpr ⟨ by linarith! [ show 0 ≤ ∑' m : Fin n → ℤ, weight n s m * ‖a ( φ k ) m - a_lim m‖ ^ 2 from tsum_nonneg fun _ => mul_nonneg ( Real.rpow_nonneg ( by exact add_nonneg zero_le_one <| Finset.sum_nonneg fun _ _ => sq_nonneg _ ) _ ) <| sq_nonneg _ ], by linarith! [ hF k ] ⟩;
  exact ⟨ φ, hφ_mono, a_lim, MemSobolev.mono ha_lim_mem hst.le, ha_lim_conv ⟩

end NashEmbedding.Sobolev

end
