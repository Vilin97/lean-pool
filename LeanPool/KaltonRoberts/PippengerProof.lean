/-
Copyright (c) 2026 Ho Boon Suan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ho Boon Suan
-/

/-
# Pippenger expander construction proof

This file contains the probabilistic counting argument proving existence of
expanders for the four rows needed by the Kalton-Roberts bound.
-/
import LeanPool.KaltonRoberts.Defs

/-!
# Pippenger expander construction proof

Probabilistic counting argument proving existence of expanders for the rows
needed by the Kalton-Roberts bound.
-/

namespace KaltonRoberts

open Finset BigOperators

/-! ## Counting constrained permutations -/

/-
Base case: with no constraint, we get all permutations.
-/
theorem card_perm_constrained_zero (n t : ℕ) (_ht : t ≤ n) :
    Fintype.card {σ : Equiv.Perm (Fin n) //
      ∀ (i : Fin n), i.val < 0 → (σ i).val < t} =
    n.factorial := by
  simp +zetaDelta only [
    not_lt_zero,
    IsEmpty.forall_iff,
    implies_true,
    Fintype.card_subtype_true] at *
  rw [ Fintype.card_perm ]; norm_num

/-
Step: adding one more constraint multiplies by (t-s)/(n-s).
Formally: card(s+1) * (n - s) = card(s) * (t - s).
-/
theorem card_perm_constrained_step (n s t : ℕ) (hs : s < t) (ht : t ≤ n) :
    Fintype.card {σ : Equiv.Perm (Fin n) //
      ∀ (i : Fin n), i.val < s + 1 → (σ i).val < t} * (n - s) =
    Fintype.card {σ : Equiv.Perm (Fin n) //
      ∀ (i : Fin n), i.val < s → (σ i).val < t} * (t - s) := by
  rw [ Fintype.card_subtype, Fintype.card_subtype ];
  have h_card_perm : (Finset.filter (fun σ : Equiv.Perm (Fin n) => ∀ i : Fin n, i.val < s → (σ
    i).val < t) Finset.univ).card * (t - s) =
    (Finset.filter (fun σ : Equiv.Perm (Fin n) => ∀ i : Fin n, i.val < s + 1 → (σ i).val < t)
      Finset.univ).card * (n - s) := by
    have h_available_card : ∀ σ : Equiv.Perm (Fin n), (∀ i : Fin n, i.val < s → (σ i).val < t) →
      (Finset.filter (fun i : Fin n => i.val ≥ s ∧ (σ i).val < t) Finset.univ).card = t - s := by
        intro σ hσ
        have h_card_perm_aux : (Finset.filter (fun i : Fin n => (σ i).val < t) Finset.univ).card = t
          := by
          have h_card_perm_aux : (Finset.filter (fun i : Fin n => (i : ℕ) < t) Finset.univ).card = t
            := by
            rw [ Finset.card_eq_of_bijective ];
            · use fun i hi => ⟨ i, by linarith ⟩;
            · grind;
            · grind;
            · aesop;
          convert h_card_perm_aux using 1;
          rw [ Finset.card_filter, Finset.card_filter ];
          conv_rhs => rw [ ← Equiv.sum_comp σ ];
        have h_card_perm_aux : (Finset.filter (fun i : Fin n => i.val < s ∧ (σ i).val < t)
          Finset.univ).card = s := by
          rw [
            show
              Finset.filter
                  (fun i : Fin n => (i : ℕ) < s ∧ (σ i : ℕ) < t) Finset.univ =
                Finset.Iio ⟨s, by linarith⟩ from
              Finset.ext fun x => by aesop]
          aesop
        have h_card_perm_aux : (Finset.filter (fun i : Fin n => (σ i).val < t) Finset.univ).card =
          (Finset.filter (fun i : Fin n => i.val < s ∧ (σ i).val < t) Finset.univ).card +
            (Finset.filter (fun i : Fin n => i.val ≥ s ∧ (σ i).val < t) Finset.univ).card := by
          rw [ ← Finset.card_union_of_disjoint ];
          · congr with i; by_cases hi : ( i : ℕ ) < s <;> aesop;
          · exact Finset.disjoint_filter.mpr fun _ _ _ _ => by linarith;
        exact eq_tsub_of_add_eq ( by linarith )
    have h_first_sum : (Finset.filter (fun σ : Equiv.Perm (Fin n) => ∀ i : Fin n, i.val < s → (σ
      i).val < t) Finset.univ).card * (t - s) =
      (Finset.filter (fun σ : Equiv.Perm (Fin n) => ∀ i : Fin n, i.val < s → (σ i).val < t)
        Finset.univ).sum (fun σ => (Finset.filter (fun i : Fin n => i.val ≥ s ∧ (σ i).val < t)
          Finset.univ).card) := by
        rw [ Finset.sum_congr rfl fun x hx => h_available_card x <| Finset.mem_filter.mp hx |>.2 ];
          aesop;
    have h_double_count : (Finset.filter (fun σ : Equiv.Perm (Fin n) => ∀ i : Fin n, i.val < s → (σ
      i).val < t) Finset.univ).sum (fun σ => (Finset.filter (fun i : Fin n => i.val ≥ s ∧ (σ i).val
        < t) Finset.univ).card) =
      (Finset.filter (fun i : Fin n => i.val ≥ s) Finset.univ).sum (fun i => (Finset.filter (fun σ :
        Equiv.Perm (Fin n) => (σ i).val < t ∧ ∀ j : Fin n, j.val < s → (σ j).val < t)
          Finset.univ).card) := by
        simp +decide only [card_filter];
        rw [ Finset.sum_comm ];
        rw [ Finset.sum_filter ];
        congr with i
        by_cases hi : ( i : ℕ ) ≥ s
        · simp +decide only [hi, sum_boole, Nat.cast_id, true_and, ite_true]
          exact congr_arg Finset.card ( by ext; aesop )
        · simp +decide only [hi, sum_boole, Nat.cast_id, false_and, ite_false,
            Finset.sum_const_zero]
    have h_swap_card : ∀ i : Fin n, i.val ≥ s → (Finset.filter (fun σ : Equiv.Perm (Fin n) => (σ
      i).val < t ∧ ∀ j : Fin n, j.val < s → (σ j).val < t) Finset.univ).card =
      (Finset.filter (fun σ : Equiv.Perm (Fin n) => ∀ j : Fin n, j.val < s + 1 → (σ j).val < t)
        Finset.univ).card := by
        intro i hi
        let k : Fin n := ⟨s, by linarith [Fin.is_lt i]⟩
        have hk_value : (k : ℕ) = s := rfl
        apply Finset.card_bij (fun σ _ => σ * Equiv.swap i k);
        · intro σ hσ
          rw [Finset.mem_filter] at hσ
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          intro j hj
          by_cases hj_boundary : j = k
          · subst j
            simpa [Equiv.swap_apply_def, k] using hσ.2.1
          · have hj_small : (j : ℕ) < s := by
              have hj_ne : (j : ℕ) ≠ s := by
                intro h
                exact hj_boundary (Fin.ext (by simpa [hk_value] using h))
              omega
            have hji : j ≠ i := by
              intro h
              have h_value : (j : ℕ) = (i : ℕ) :=
                congrArg (fun x : Fin n => (x : ℕ)) h
              omega
            simpa [Equiv.swap_apply_def, hji, hj_boundary] using hσ.2.2 j hj_small
        · aesop;
        · intro σ hσ
          use σ * Equiv.swap i k
          rw [Finset.mem_filter] at hσ
          refine ⟨?_, ?_⟩
          · rw [Finset.mem_filter]
            refine ⟨Finset.mem_univ _, ?_⟩
            constructor
            · have hk_lt : (k : ℕ) < s + 1 := by omega
              simpa [Equiv.swap_apply_def, k] using hσ.2 k hk_lt
            · intro j hj_small
              have hji : j ≠ i := by
                intro h
                have h_value : (j : ℕ) = (i : ℕ) :=
                  congrArg (fun x : Fin n => (x : ℕ)) h
                omega
              have hjk : j ≠ k := by
                intro h
                have h_value : (j : ℕ) = s := by
                  simpa [hk_value] using congrArg (fun x : Fin n => (x : ℕ)) h
                omega
              have hj_succ : (j : ℕ) < s + 1 := by omega
              simpa [Equiv.swap_apply_def, hji, hjk] using hσ.2 j hj_succ
          · simp [mul_assoc]
    rw [h_first_sum, h_double_count]
    rw [Finset.sum_congr rfl fun x hx => h_swap_card x <| Finset.mem_filter.mp hx |>.2]
    rw [show (Finset.univ.filter fun x : Fin n => s ≤ (x : ℕ)) =
        Finset.Ici ⟨s, by linarith⟩ by
      ext x
      simp [Fin.le_def]]
    simp [Nat.mul_comm]
  exact h_card_perm.symm

/-- The number of permutations of `Fin n` that map the first `s` elements
into `{0, …, t-1}` is `t.descFactorial s * (n - s)!`. -/
theorem card_perm_constrained (n s t : ℕ) (hs : s ≤ t) (ht : t ≤ n) :
    Fintype.card {σ : Equiv.Perm (Fin n) //
      ∀ (i : Fin n), i.val < s → (σ i).val < t} =
    t.descFactorial s * (n - s).factorial := by
  induction s with
  | zero =>
    simp only [
      not_lt_zero,
      IsEmpty.forall_iff,
      implies_true,
      Fintype.card_subtype_true,
      Nat.descFactorial_zero,
      tsub_zero,
      one_mul]
    rw [Fintype.card_perm, Fintype.card_fin]
  | succ s ih =>
    have hs' : s < t := Nat.lt_of_succ_le hs
    have hs'' : s ≤ t := le_of_lt hs'
    have hns : s < n := lt_of_lt_of_le hs' ht
    have step := card_perm_constrained_step n s t hs' ht
    rw [ih hs''] at step
    rw [Nat.descFactorial_succ]
    have hns' : 0 < n - s := Nat.sub_pos_of_lt hns
    have h_fac : (n - s).factorial = (n - s) * (n - (s + 1)).factorial := by
      rw [show n - s = (n - (s + 1)) + 1 from by omega, Nat.factorial_succ]
    rw [h_fac] at step
    nlinarith [Nat.factorial_pos (n - (s + 1))]

/-! ## Binomial coefficient bounds -/

/-
`C(n,k) ≤ (e*n/k)^k` for `0 < k ≤ n`.
-/
theorem choose_le_exp_pow (n k : ℕ) (hk : 0 < k) (_hkn : k ≤ n) :
    (n.choose k : ℝ) ≤ (Real.exp 1 * ↑n / ↑k) ^ k := by
  -- We'll use the fact that $C(n,k) \leq \frac{n^k}{k!}$.
  have h_choose_le : (Nat.choose n k : ℝ) ≤ (n ^ k) / (Nat.factorial k) := by
    exact Nat.choose_le_pow_div k n
  refine le_trans h_choose_le ?_;
  -- We'll use the fact that $k! \geq (k/e)^k$.
  have h_factorial_ge : (Nat.factorial k : ℝ) ≥ (k / Real.exp 1) ^ k := by
    field_simp;
    rw [ div_pow, div_le_iff₀ ] <;> first | positivity | have := Real.exp_one_lt_d9.le; norm_num at
      *;
    rw [← div_le_iff₀' (by positivity)]
    rw [Real.exp_eq_exp_ℝ]
    norm_num [NormedSpace.exp_eq_tsum_div]
    exact Summable.le_tsum
      (show Summable _ from Real.summable_pow_div_factorial _)
      k
      (fun _ _ => by positivity)
  convert div_le_div_of_nonneg_left _ _ h_factorial_ge using 1 <;>
    ring_nf <;>
    norm_num [hk.ne', Real.exp_ne_zero]
  · ring;
  · positivity

/-
`n.choose k ≤ exp(hEntropy n k)` for `0 < k < n`.
-/
theorem choose_le_exp_h_entropy (n k : ℕ) (hk : 0 < k) (hkn : k < n) :
    (n.choose k : ℝ) ≤ Real.exp (hEntropy (↑n) (↑k)) := by
  -- We can use the fact that $n^n / (k^k * (n-k)^{n-k}) = e^{hEntropy n k}$ to rewrite the goal.
  have h_exp : (n : ℝ)^n / (k^k * (n - k)^(n - k)) = Real.exp (hEntropy n k) := by
    unfold hEntropy;
      rw [
        Real.exp_sub,
        Real.exp_sub,
        mul_comm _ (Real.log _),
        mul_comm _ (Real.log _),
        mul_comm _ (Real.log _),
        Real.exp_mul,
        Real.exp_mul,
        Real.exp_mul,
        Real.exp_log,
        Real.exp_log,
        Real.exp_log] <;>
        norm_cast <;>
        try linarith
    · simp +decide only [Nat.cast_pow, Rat.divInt_eq_div, Int.cast_pow, Int.cast_natCast,
        Int.cast_mul, Int.cast_subNatNat, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast,
        Rat.cast_mul, Rat.cast_sub, div_div]
      rw [Int.subNatNat_of_le hkn.le]
      norm_cast
    · grind +qlia;
  rw [ ← h_exp, le_div_iff₀ ];
  · rw_mod_cast [ ← Nat.add_sub_of_le hkn.le, add_pow ];
    norm_num [ Int.subNatNat_eq_coe, hkn.le ];
    exact le_trans ( by ring_nf; norm_num ) ( Finset.single_le_sum ( fun x _ => mul_nonneg (
      mul_nonneg ( pow_nonneg ( Nat.cast_nonneg _ ) _ ) ( pow_nonneg ( sub_nonneg.mpr (
        Nat.cast_le.mpr hkn.le ) ) _ ) ) ( Nat.cast_nonneg _ ) ) ( Finset.mem_range.mpr (
          Nat.lt_succ_of_le hkn.le ) ) );
  · exact mul_pos ( by positivity ) ( pow_pos ( by norm_num; linarith ) _ )

/-
`n.choose k ≥ exp(hEntropy n k) / (n + 1)` for `0 < k < n`.
-/
theorem choose_ge_exp_h_entropy_div (n k : ℕ) (hk : 0 < k) (hkn : k < n) :
    Real.exp (hEntropy (↑n) (↑k)) / ((n : ℝ) + 1) ≤ (n.choose k : ℝ) := by
  -- By the binomial theorem, we have $\sum_{j=0}^{n} \binom{n}{j} \left(\frac{k}{n}\right)^j
  -- \left(\frac{n-k}{n}\right)^{n-j} = 1$.
  have binom_sum : ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * (k / n : ℝ) ^ j * ((n - k) / n :
    ℝ) ^ (n - j) = 1 := by
    have := add_pow ( k / n : ℝ ) ( ( n - k ) / n ) n;
    simp_all +decide only [← add_div, add_sub_cancel, mul_assoc, mul_comm, mul_left_comm]
    rw [ ← this, div_self ( by norm_cast; linarith ), one_pow ];
  -- The $j=k$ term is the maximum term in the binomial sum.
  have max_term : (n.choose k : ℝ) * (k / n : ℝ) ^ k * ((n - k) / n : ℝ) ^ (n - k) ≥ (1 : ℝ) / (n +
    1) := by
    -- The ratio of consecutive terms in the binomial sum is greater than 1 for $j < k$ and less
    -- than or equal to 1 for $j \geq k$.
    have ratio_gt_one : ∀ j ∈ Finset.range k, (n.choose (j + 1) : ℝ) * (k / n : ℝ) ^ (j + 1) * ((n -
      k) / n : ℝ) ^ (n - (j + 1)) > (n.choose j : ℝ) * (k / n : ℝ) ^ j * ((n - k) / n : ℝ) ^ (n - j)
        := by
      intro j hj
      have h_ratio : (n.choose (j + 1) : ℝ) * (k / n : ℝ) ^ (j + 1) * ((n - k) / n : ℝ) ^ (n - (j +
        1)) / ((n.choose j : ℝ) * (k / n : ℝ) ^ j * ((n - k) / n : ℝ) ^ (n - j)) = (n - j) / (j + 1)
          * (k / n : ℝ) / ((n - k) / n : ℝ) := by
        rw [ div_eq_div_iff ];
        · rw [
            show
              (n.choose (j + 1) : ℝ) =
                (n.choose j : ℝ) * (n - j) / (j + 1) from
              ?_
            ];
          · rw [show n - j = (n - (j + 1)) + 1 by
              rw [tsub_add_eq_add_tsub (by linarith [Finset.mem_range.mp hj])]
              simp +decide]
            ring
          · rw [eq_div_iff] <;> norm_cast
            rw [Int.subNatNat_of_le (by linarith [Finset.mem_range.mp hj])]
            norm_cast
            rw [Nat.choose_succ_right_eq]
        · exact mul_ne_zero ( mul_ne_zero ( Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <| Nat.choose_pos
          <| by linarith [ Finset.mem_range.mp hj ] ) <| pow_ne_zero _ <| div_ne_zero (
            Nat.cast_ne_zero.mpr hk.ne' ) <| Nat.cast_ne_zero.mpr <| by linarith ) <| pow_ne_zero _
              <| div_ne_zero ( sub_ne_zero_of_ne <| by norm_cast; linarith ) <| Nat.cast_ne_zero.mpr
                <| by linarith;
        · exact div_ne_zero
            (sub_ne_zero_of_ne (by
              norm_cast
              linarith))
            (by
              norm_cast
              linarith)
      contrapose! h_ratio;
      refine ne_of_lt ( lt_of_le_of_lt ( div_le_one_of_le₀ h_ratio ?_ ) ?_ )
      · exact mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg ( by positivity ) _ ) ) (
        pow_nonneg ( div_nonneg ( sub_nonneg.mpr ( Nat.cast_le.mpr hkn.le ) ) ( Nat.cast_nonneg _ )
          ) _ );
      · field_simp;
          rw [lt_div_iff₀] <;>
            nlinarith only [
              show (j : ℝ) + 1 ≤ k by
                norm_cast
                linarith [Finset.mem_range.mp hj],
              show (k : ℝ) < n by norm_cast,
              show (n : ℝ) > 0 by
                norm_cast
                linarith,
              mul_lt_mul_of_pos_left
                (show (j : ℝ) + 1 < n by
                  norm_cast
                  linarith [Finset.mem_range.mp hj])
                (show (n : ℝ) > 0 by
                  norm_cast
                  linarith)]
    -- The ratio of consecutive terms in the binomial sum is less than or equal to 1 for $j \geq k$.
    have ratio_le_one : ∀ j ∈ Finset.Ico k n, (n.choose (j + 1) : ℝ) * (k / n : ℝ) ^ (j + 1) * ((n -
      k) / n : ℝ) ^ (n - (j + 1)) ≤ (n.choose j : ℝ) * (k / n : ℝ) ^ j * ((n - k) / n : ℝ) ^ (n - j)
        := by
      intro j hj
      have h_ratio : (n.choose (j + 1) : ℝ) * (k / n : ℝ) ^ (j + 1) * ((n - k) / n : ℝ) ^ (n - (j +
        1)) = (n.choose j : ℝ) * (k / n : ℝ) ^ j * ((n - k) / n : ℝ) ^ (n - j) * ((n - j) * k) / ((j
          + 1) * (n - k)) := by
        rw [ Nat.cast_choose, Nat.cast_choose ] <;> try linarith [ Finset.mem_Ico.mp hj ];
        field_simp;
        rw [eq_div_iff (sub_ne_zero_of_ne <| by norm_cast; linarith)]
        rw [show n - j = n - (j + 1) + 1 by
          rw [tsub_add_eq_add_tsub (by linarith [Finset.mem_Ico.mp hj])]
          simp +decide]
        push_cast [Nat.factorial_succ]
        ring_nf
        rw [ Nat.cast_sub ( by linarith [ Finset.mem_Ico.mp hj ] ) ]; push_cast; ring;
      rw [ h_ratio, div_le_iff₀ ];
        · exact
            mul_le_mul_of_nonneg_left
              (by
                nlinarith only [
                  show (j : ℝ) ≥ k by
                    exact_mod_cast Finset.mem_Ico.mp hj |>.1,
                  show (j : ℝ) < n by
                    exact_mod_cast Finset.mem_Ico.mp hj |>.2])
              (by
                exact
                  mul_nonneg
                    (mul_nonneg
                      (Nat.cast_nonneg _)
                      (pow_nonneg (by positivity) _))
                    (pow_nonneg
                      (div_nonneg
                        (sub_nonneg.mpr (Nat.cast_le.mpr hkn.le))
                        (Nat.cast_nonneg _)) _))
      · exact mul_pos ( by positivity ) ( sub_pos.mpr ( Nat.cast_lt.mpr hkn ) );
    -- By the properties of the binomial sum and the ratios, we can conclude that the $k$-th term is
    -- the maximum term.
    have max_term : ∀ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * (k / n : ℝ) ^ j * ((n - k) / n :
      ℝ) ^ (n - j) ≤ (n.choose k : ℝ) * (k / n : ℝ) ^ k * ((n - k) / n : ℝ) ^ (n - k) := by
      intro j hj
      by_cases hjk : j < k;
      · have h_seq : ∀ m ∈ Finset.Icc j k, (n.choose m : ℝ) * (k / n : ℝ) ^ m * ((n - k) / n : ℝ) ^
        (n - m) ≥ (n.choose j : ℝ) * (k / n : ℝ) ^ j * ((n - k) / n : ℝ) ^ (n - j) := by
          intro m hm; induction Finset.mem_Icc.mp hm |>.1 <;> norm_num at *;
          grind;
        grind +revert;
      · induction j with
        | zero =>
          norm_num at *
          linarith
        | succ j ih =>
          norm_num at *
          grind
    have := Finset.sum_le_sum max_term
    simp_all +decide only [
      sum_range_succ,
      Nat.choose_self,
      Nat.cast_one,
      one_mul,
      tsub_self,
      pow_zero,
      mul_one,
      mem_range,
      gt_iff_lt,
      mem_Ico,
      and_imp,
      Order.lt_add_one_iff,
      sum_const,
      card_range,
      nsmul_eq_mul,
      Nat.cast_add,
      one_div,
      ge_iff_le]
    rwa [inv_eq_one_div, div_le_iff₀' (by positivity)]
  -- Therefore, $C(n,k) \geq \frac{\exp(h(n,k))}{n+1}$ by simplifying the expression.
  have h_simplified : (n.choose k : ℝ) * (Real.exp (hEntropy n k))⁻¹ ≥ 1 / (n + 1) := by
    convert max_term using 1; norm_num [ hEntropy ]; ring_nf;
    norm_num [
      Real.exp_add,
      Real.exp_sub,
      Real.exp_neg,
      Real.exp_nat_mul,
      Real.exp_log (show 0 < (n : ℝ) by
        norm_cast
        linarith),
      Real.exp_log (show 0 < (k : ℝ) by norm_cast),
      Real.exp_log
        (show 0 < (n - k : ℝ) by
          exact sub_pos.mpr (Nat.cast_lt.mpr hkn))]
    ring_nf;
    rw [show (n : ℕ) = k + (n - k) by rw [Nat.add_sub_cancel' hkn.le]]
    norm_num [
      pow_add,
      mul_assoc,
      mul_comm,
      mul_left_comm,
      ne_of_gt (show 0 < (n : ℝ) by
        norm_cast
        linarith),
      ne_of_gt
        (show 0 < (n - k : ℝ) by
          exact sub_pos.mpr (Nat.cast_lt.mpr hkn))]
    ring_nf;
    simp +decide [
      mul_left_comm ((n - k : ℕ) ^ k : ℝ),
      mul_assoc,
      ne_of_gt (show 0 < (n - k : ℕ) from Nat.sub_pos_of_lt hkn)]
  field_simp at h_simplified;
  rwa [ div_le_iff₀' <| by positivity ]

/-! ## Descending factorial ratio bound -/

/-
`descFactorial a k / descFactorial b k ≤ (a/b)^k` when `a ≤ b`, `k ≤ a`.
-/
theorem desc_fact_ratio_le (a b k : ℕ) (hab : a ≤ b) (hka : k ≤ a) :
    (a.descFactorial k : ℝ) / (b.descFactorial k : ℝ) ≤ ((a : ℝ) / b) ^ k := by
  induction k with
  | zero =>
    norm_num [Nat.descFactorial]
  | succ k ih =>
    simp_all +decide only [Nat.descFactorial_succ, Nat.cast_mul]
    rw [pow_succ']
    refine le_trans ?_
      (mul_le_mul_of_nonneg_left (ih (Nat.le_of_succ_le hka)) (by positivity))
    rw [mul_div_mul_comm]
    exact mul_le_mul_of_nonneg_right
      (by
        rw [div_le_div_iff₀] <;> norm_cast <;>
          nlinarith [
            Nat.sub_add_cancel (Nat.le_of_succ_le hka),
            Nat.sub_add_cancel (by linarith : k ≤ b)])
      (by positivity)

/-! ## Geometric and exponential tail bounds -/

/-
Geometric series: `∑_{i=0}^{d-1} q^(i+1) ≤ q/(1-q)` for `0 ≤ q < 1`.
-/
theorem geom_sum_le (d : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∑ i ∈ Finset.range d, q ^ (i + 1) ≤ q / (1 - q) := by
  ring_nf;
  rw [ ← Finset.mul_sum _ _ _, ← tsum_geometric_of_lt_one hq0 hq1 ]; exact
    mul_le_mul_of_nonneg_left ( Summable.sum_le_tsum ( Finset.range d ) ( fun _ _ => by positivity )
      ( by exact summable_geometric_of_lt_one hq0 hq1 ) ) hq0;

theorem sum_Icc_one_pow_le_geom (D : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∑ m ∈ Finset.Icc 1 D, q ^ m ≤ q / (1 - q) := by
  have hEq : (∑ m ∈ Finset.Icc 1 D, q ^ m) =
      ∑ i ∈ Finset.range D, q ^ (i + 1) := by
    induction D with
    | zero =>
        simp
    | succ D ih =>
        rw [Finset.sum_range_succ]
        by_cases hD : 1 ≤ D + 1
        · rw [Finset.sum_Icc_succ_top hD, ih]
        · have hD0 : D = 0 := by omega
          subst D
          simp
  rw [hEq]
  exact geom_sum_le D q hq0 hq1

theorem bad_sum_split
    (A D N : ℕ) (T : ℕ → ℝ) (q B : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hB0 : 0 ≤ B)
    (hcard_N : (Finset.Icc 1 A).card ≤ N)
    (hsmall : ∀ m, m ∈ Finset.Icc 1 A → m ≤ D → T m ≤ q ^ m)
    (hmid : ∀ m, m ∈ Finset.Icc 1 A → D < m → T m ≤ B) :
    ∑ m ∈ Finset.Icc 1 A, T m ≤ q / (1 - q) + (N : ℝ) * B := by
  classical
  let s := Finset.Icc 1 A
  rw [← Finset.sum_filter_add_sum_filter_not s (fun m => m ≤ D) T]
  apply add_le_add
  · calc
      ∑ x ∈ s.filter (fun m => m ≤ D), T x
          ≤ ∑ x ∈ s.filter (fun m => m ≤ D), q ^ x := by
            apply Finset.sum_le_sum
            intro m hm
            exact hsmall m (Finset.mem_of_mem_filter m hm) (Finset.mem_filter.mp hm).2
      _ ≤ ∑ x ∈ Finset.Icc 1 D, q ^ x := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro m hm
              have hs : m ∈ s := Finset.mem_of_mem_filter m hm
              have hmD : m ≤ D := (Finset.mem_filter.mp hm).2
              rcases Finset.mem_Icc.mp hs with ⟨hm1, _⟩
              exact Finset.mem_Icc.mpr ⟨hm1, hmD⟩
            · intro m hmD hnot
              positivity
      _ ≤ q / (1 - q) := sum_Icc_one_pow_le_geom D q hq0 hq1
  · calc
      ∑ x ∈ s.filter (fun m => ¬m ≤ D), T x
          ≤ ∑ x ∈ s.filter (fun m => ¬m ≤ D), B := by
            apply Finset.sum_le_sum
            intro m hm
            have hs : m ∈ s := Finset.mem_of_mem_filter m hm
            have hDm : D < m := Nat.lt_of_not_ge (Finset.mem_filter.mp hm).2
            exact hmid m hs hDm
      _ = ((s.filter (fun m => ¬m ≤ D)).card : ℝ) * B := by simp
      _ ≤ (N : ℝ) * B := by
            apply mul_le_mul_of_nonneg_right _ hB0
            have hcard : (s.filter (fun m => ¬m ≤ D)).card ≤ N :=
              le_trans (Finset.card_filter_le s (fun m => ¬m ≤ D)) (by simpa [s] using hcard_N)
            exact_mod_cast hcard

/-
Exponential decay beats quadratic eventually.
-/
theorem exp_decay_beats_poly (η : ℝ) (hη : 0 < η) :
    ∀ᶠ (N : ℕ) in Filter.atTop,
      (N : ℝ) ^ 2 * Real.exp (-η * ↑N) < 1 / 2 := by
  -- We'll use the fact that $N^2 e^{-\eta N}$ tends to $0$ as $N$ tends to infinity.
  have h_lim : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * Real.exp (-η * N)) Filter.atTop (nhds 0)
    := by
    have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2;
    convert this.comp ( tendsto_natCast_atTop_atTop.const_mul_atTop hη ) |> ( ·.mul_const ( η ^ 2 )
      ⁻¹ ) using 2 <;> norm_num; ring_nf;
    norm_num [ mul_right_comm, hη.ne' ];
  exact h_lim.eventually ( gt_mem_nhds <| by norm_num )

theorem exp_decay_beats_poly_const (C η : ℝ) (hη : 0 < η) :
    ∀ᶠ (N : ℕ) in Filter.atTop,
      C * (N : ℝ) ^ 2 * Real.exp (-η * ↑N) < 1 / 2 := by
  have h_lim_base :
      Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * Real.exp (-η * N))
        Filter.atTop (nhds 0) := by
    have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2
    convert this.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hη)
      |> (·.mul_const (η ^ 2)⁻¹) using 2 <;> norm_num; ring_nf
    norm_num [mul_right_comm, hη.ne']
  have h_lim :
      Filter.Tendsto (fun N : ℕ => C * ((N : ℝ) ^ 2 * Real.exp (-η * N)))
        Filter.atTop (nhds 0) := by
    simpa using h_lim_base.const_mul C
  have h_ev : ∀ᶠ N : ℕ in Filter.atTop,
      C * ((N : ℝ) ^ 2 * Real.exp (-η * N)) < 1 / 2 :=
    h_lim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  filter_upwards [h_ev] with N hN
  simpa [mul_assoc] using hN

/-! ## Entropy bounds for Pippenger bad events -/

theorem h_entropy_scale (t a b : ℝ) (ht : t ≠ 0) (ha : a ≠ 0)
    (hb : b ≠ 0) (hab : a - b ≠ 0) :
    hEntropy (t * a) (t * b) = t * hEntropy a b := by
  unfold hEntropy
  rw [Real.log_mul ht ha, Real.log_mul ht hb]
  have htab : t * a - t * b = t * (a - b) := by ring
  rw [htab, Real.log_mul ht hab]
  ring

theorem h_entropy_scale_nat
    (N A B : ℕ) (a b : ℝ)
    (hN : (N : ℝ) ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a - b ≠ 0)
    (hA : (A : ℝ) = (N : ℝ) * a) (hB : (B : ℝ) = (N : ℝ) * b) :
    hEntropy (A : ℝ) (B : ℝ) = (N : ℝ) * hEntropy a b := by
  have h := h_entropy_scale (N : ℝ) a b hN ha hb hab
  rwa [← hA, ← hB] at h

theorem choose_ratio_le_entropy_bound
    (a b k : ℕ) (hk : 0 < k) (hka : k < a) (hkb : k < b) :
    (a.choose k : ℝ) / (b.choose k : ℝ) ≤
      ((b : ℝ) + 1) * Real.exp (hEntropy (a : ℝ) (k : ℝ) -
        hEntropy (b : ℝ) (k : ℝ)) := by
  have hnum := choose_le_exp_h_entropy a k hk hka
  have hden := choose_ge_exp_h_entropy_div b k hk hkb
  have hden_pos : 0 < (b.choose k : ℝ) := by
    exact_mod_cast Nat.choose_pos hkb.le
  have hlow_pos : 0 < Real.exp (hEntropy (b : ℝ) (k : ℝ)) / ((b : ℝ) + 1) := by
    positivity
  have hstep₁ :
      (a.choose k : ℝ) / (b.choose k : ℝ) ≤
        Real.exp (hEntropy (a : ℝ) (k : ℝ)) / (b.choose k : ℝ) := by
    exact div_le_div_of_nonneg_right hnum hden_pos.le
  have hstep₂ :
      Real.exp (hEntropy (a : ℝ) (k : ℝ)) / (b.choose k : ℝ) ≤
        Real.exp (hEntropy (a : ℝ) (k : ℝ)) /
          (Real.exp (hEntropy (b : ℝ) (k : ℝ)) / ((b : ℝ) + 1)) := by
    exact div_le_div_of_nonneg_left (by positivity) hlow_pos hden
  calc
    (a.choose k : ℝ) / (b.choose k : ℝ)
        ≤ Real.exp (hEntropy (a : ℝ) (k : ℝ)) / (b.choose k : ℝ) := hstep₁
    _ ≤ Real.exp (hEntropy (a : ℝ) (k : ℝ)) /
          (Real.exp (hEntropy (b : ℝ) (k : ℝ)) / ((b : ℝ) + 1)) := hstep₂
    _ = ((b : ℝ) + 1) * Real.exp (hEntropy (a : ℝ) (k : ℝ) -
          hEntropy (b : ℝ) (k : ℝ)) := by
      rw [Real.exp_sub]
      field_simp [Real.exp_ne_zero]

theorem choose_ratio_le_pow (a b k : ℕ) (hab : a ≤ b) (hk : k ≤ a) :
    (a.choose k : ℝ) / (b.choose k : ℝ) ≤ ((a : ℝ) / (b : ℝ)) ^ k := by
  have hdesc := desc_fact_ratio_le a b k hab hk
  have hfac_pos : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hchooseA : (a.choose k : ℝ) = (a.descFactorial k : ℝ) / (k.factorial : ℝ) := by
    have h := Nat.descFactorial_eq_factorial_mul_choose a k
    have h' : (a.descFactorial k : ℝ) = (k.factorial : ℝ) * (a.choose k : ℝ) := by
      exact_mod_cast h
    rw [h']
    field_simp [hfac_pos.ne']
  have hchooseB : (b.choose k : ℝ) = (b.descFactorial k : ℝ) / (k.factorial : ℝ) := by
    have h := Nat.descFactorial_eq_factorial_mul_choose b k
    have h' : (b.descFactorial k : ℝ) = (k.factorial : ℝ) * (b.choose k : ℝ) := by
      exact_mod_cast h
    rw [h']
    field_simp [hfac_pos.ne']
  rw [hchooseA, hchooseB]
  field_simp [hfac_pos.ne']
  exact hdesc

theorem pippenger_small_term_raw
    (N L r c m : ℕ) (hm : 0 < m) (hmN : m ≤ N) (hmL : m ≤ L)
    (hrc : r ≤ c) (hcmN : c * m ≤ r * N) :
    (N.choose m : ℝ) * (L.choose m : ℝ) *
        ((c * m).choose (r * m) : ℝ) / ((r * N).choose (r * m) : ℝ)
      ≤ ((Real.exp 1 * (N : ℝ) / (m : ℝ)) *
          (Real.exp 1 * (L : ℝ) / (m : ℝ)) *
          (((c * m : ℕ) : ℝ) / ((r * N : ℕ) : ℝ)) ^ r) ^ m := by
  have hN := choose_le_exp_pow N m hm hmN
  have hL := choose_le_exp_pow L m hm hmL
  have hratio := choose_ratio_le_pow (c * m) (r * N) (r * m) hcmN
    (Nat.mul_le_mul_right m hrc)
  have hratio' :
      ((c * m).choose (r * m) : ℝ) / ((r * N).choose (r * m) : ℝ)
        ≤ ((((c * m : ℕ) : ℝ) / ((r * N : ℕ) : ℝ)) ^ r) ^ m := by
    calc
      ((c * m).choose (r * m) : ℝ) / ((r * N).choose (r * m) : ℝ)
          ≤ (((c * m : ℕ) : ℝ) / ((r * N : ℕ) : ℝ)) ^ (r * m) := hratio
      _ = ((((c * m : ℕ) : ℝ) / ((r * N : ℕ) : ℝ)) ^ r) ^ m := by
        rw [← pow_mul]
  have h12 :
      (N.choose m : ℝ) * (L.choose m : ℝ) ≤
        (Real.exp 1 * (N : ℝ) / (m : ℝ)) ^ m *
          (Real.exp 1 * (L : ℝ) / (m : ℝ)) ^ m := by
    exact mul_le_mul hN hL (by positivity) (by positivity)
  calc
    (N.choose m : ℝ) * (L.choose m : ℝ) *
        ((c * m).choose (r * m) : ℝ) / ((r * N).choose (r * m) : ℝ)
      = ((N.choose m : ℝ) * (L.choose m : ℝ)) *
          (((c * m).choose (r * m) : ℝ) / ((r * N).choose (r * m) : ℝ)) := by ring
    _ ≤ ((Real.exp 1 * (N : ℝ) / (m : ℝ)) ^ m *
          (Real.exp 1 * (L : ℝ) / (m : ℝ)) ^ m) *
          ((((c * m : ℕ) : ℝ) / ((r * N : ℕ) : ℝ)) ^ r) ^ m := by
        exact mul_le_mul h12 hratio' (by positivity) (by positivity)
    _ = ((Real.exp 1 * (N : ℝ) / (m : ℝ)) *
          (Real.exp 1 * (L : ℝ) / (m : ℝ)) *
          (((c * m : ℕ) : ℝ) / ((r * N : ℕ) : ℝ)) ^ r) ^ m := by
        set A := Real.exp 1 * (N : ℝ) / (m : ℝ)
        set B := Real.exp 1 * (L : ℝ) / (m : ℝ)
        set C := (((c * m : ℕ) : ℝ) / ((r * N : ℕ) : ℝ)) ^ r
        rw [← mul_pow, ← mul_pow]

theorem pippenger_term_le_entropy_bound
    (N L r c m : ℕ) (hm : 0 < m) (hmN : m < N) (hmL : m < L)
    (hr : 0 < r) (hrc : r < c) :
    (N.choose m : ℝ) * (L.choose m : ℝ) *
        ((c * m).choose (r * m) : ℝ) / ((r * N).choose (r * m) : ℝ)
      ≤ (((r * N : ℕ) : ℝ) + 1) *
        Real.exp (hEntropy (N : ℝ) (m : ℝ) + hEntropy (L : ℝ) (m : ℝ) +
          hEntropy ((c * m : ℕ) : ℝ) ((r * m : ℕ) : ℝ) -
          hEntropy ((r * N : ℕ) : ℝ) ((r * m : ℕ) : ℝ)) := by
  have hN := choose_le_exp_h_entropy N m hm hmN
  have hL := choose_le_exp_h_entropy L m hm hmL
  have hratio := choose_ratio_le_entropy_bound (c * m) (r * N) (r * m)
    (by exact Nat.mul_pos hr hm)
    (by exact (Nat.mul_lt_mul_right hm).mpr hrc)
    (by exact Nat.mul_lt_mul_of_pos_left hmN hr)
  have h12 :
      (N.choose m : ℝ) * (L.choose m : ℝ) ≤
        Real.exp (hEntropy (N : ℝ) (m : ℝ)) *
          Real.exp (hEntropy (L : ℝ) (m : ℝ)) := by
    exact mul_le_mul hN hL (by positivity) (by positivity)
  calc
    (N.choose m : ℝ) * (L.choose m : ℝ) *
        ((c * m).choose (r * m) : ℝ) / ((r * N).choose (r * m) : ℝ)
        = ((N.choose m : ℝ) * (L.choose m : ℝ)) *
            (((c * m).choose (r * m) : ℝ) / ((r * N).choose (r * m) : ℝ)) := by
          ring
    _ ≤ (Real.exp (hEntropy (N : ℝ) (m : ℝ)) *
          Real.exp (hEntropy (L : ℝ) (m : ℝ))) *
          ((((r * N : ℕ) : ℝ) + 1) *
            Real.exp (hEntropy ((c * m : ℕ) : ℝ) ((r * m : ℕ) : ℝ) -
              hEntropy ((r * N : ℕ) : ℝ) ((r * m : ℕ) : ℝ))) := by
          exact mul_le_mul h12 hratio (by positivity) (by positivity)
    _ = (((r * N : ℕ) : ℝ) + 1) *
        Real.exp (hEntropy (N : ℝ) (m : ℝ) + hEntropy (L : ℝ) (m : ℝ) +
          hEntropy ((c * m : ℕ) : ℝ) ((r * m : ℕ) : ℝ) -
          hEntropy ((r * N : ℕ) : ℝ) ((r * m : ℕ) : ℝ)) := by
          set HN := hEntropy (N : ℝ) (m : ℝ)
          set HL := hEntropy (L : ℝ) (m : ℝ)
          set HC := hEntropy ((c * m : ℕ) : ℝ) ((r * m : ℕ) : ℝ)
          set HR := hEntropy ((r * N : ℕ) : ℝ) ((r * m : ℕ) : ℝ)
          set B := (((r * N : ℕ) : ℝ) + 1)
          rw [show HN + HL + HC - HR = (HN + HL) + (HC - HR) by ring]
          rw [Real.exp_add, Real.exp_add]
          ring

theorem pippenger_entropy_exponent_eq_phi
    (N L r c m : ℕ) (θ : ℝ)
    (hN : 0 < N) (hm : 0 < m) (hmN : m < N) (hmL : m < L)
    (hr : 0 < r) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hLθ : (L : ℝ) = θ * (N : ℝ))
    (hcθ : (c : ℝ) = (r : ℝ) / θ) :
    hEntropy (N : ℝ) (m : ℝ) + hEntropy (L : ℝ) (m : ℝ) +
        hEntropy ((c * m : ℕ) : ℝ) ((r * m : ℕ) : ℝ) -
        hEntropy ((r * N : ℕ) : ℝ) ((r * m : ℕ) : ℝ)
      = (N : ℝ) * Phi (r : ℝ) θ ((m : ℝ) / (N : ℝ)) := by
  set n : ℝ := (N : ℝ) with hn
  set x : ℝ := (m : ℝ) / n with hx
  have hn_pos : 0 < n := by rw [hn]; exact_mod_cast hN
  have hn_ne : n ≠ 0 := ne_of_gt hn_pos
  have hm_posR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hx_pos : 0 < x := by rw [hx]; exact div_pos hm_posR hn_pos
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have hx_lt_one : x < 1 := by
    rw [hx]
    exact (div_lt_one hn_pos).mpr (by rw [hn]; exact_mod_cast hmN)
  have hx_lt_θ : x < θ := by
    have hmLr : (m : ℝ) < (L : ℝ) := by exact_mod_cast hmL
    rw [hLθ] at hmLr
    rw [hx]
    rw [div_lt_iff₀ hn_pos]
    simpa [hn, mul_comm] using hmLr
  have hr_posR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hr_ne : (r : ℝ) ≠ 0 := ne_of_gt hr_posR
  have hθ_ne : θ ≠ 0 := ne_of_gt hθ0
  have hNent :
      hEntropy (N : ℝ) (m : ℝ) = n * hEntropy 1 x := by
    have h := h_entropy_scale_nat N N m 1 x hn_ne one_ne_zero hx_ne
      (by nlinarith [hx_lt_one])
      (by ring)
      (by rw [show (N : ℝ) = n by rw [hn], hx]; field_simp [hn_ne])
    simpa [hn, hx] using h
  have hLent :
      hEntropy (L : ℝ) (m : ℝ) = n * hEntropy θ x := by
    have h := h_entropy_scale_nat N L m θ x hn_ne hθ_ne hx_ne
      (by nlinarith [hx_lt_θ])
      (by rw [hLθ, show (N : ℝ) = n by rw [hn]]; ring)
      (by rw [show (N : ℝ) = n by rw [hn], hx]; field_simp [hn_ne])
    simpa [hn, hx] using h
  have hCent :
      hEntropy ((c * m : ℕ) : ℝ) ((r * m : ℕ) : ℝ) =
        n * hEntropy ((r : ℝ) * x / θ) ((r : ℝ) * x) := by
    have ha_ne : (r : ℝ) * x / θ ≠ 0 := by
      exact div_ne_zero (mul_ne_zero hr_ne hx_ne) hθ_ne
    have hb_ne : (r : ℝ) * x ≠ 0 := mul_ne_zero hr_ne hx_ne
    have hab_ne : (r : ℝ) * x / θ - (r : ℝ) * x ≠ 0 := by
      have hpos : 0 < (r : ℝ) * x / θ - (r : ℝ) * x := by
        have : 1 < 1 / θ := by
          rw [one_lt_div hθ0]
          exact hθ1
        have hcoef : 0 < 1 / θ - 1 := by linarith
        have hrx : 0 < (r : ℝ) * x := mul_pos hr_posR hx_pos
        have heq : (r : ℝ) * x / θ - (r : ℝ) * x =
            (r : ℝ) * x * (1 / θ - 1) := by ring
        rw [heq]
        exact mul_pos hrx hcoef
      exact ne_of_gt hpos
    have h := h_entropy_scale_nat N (c * m) (r * m)
      ((r : ℝ) * x / θ) ((r : ℝ) * x) hn_ne ha_ne hb_ne hab_ne
      (by
        rw [Nat.cast_mul, hcθ, hx]
        field_simp [hn_ne, hθ_ne]
        ring)
      (by
        rw [Nat.cast_mul, show (N : ℝ) = n by rw [hn], hx]
        field_simp [hn_ne])
    simpa [hn, hx] using h
  have hRent :
      hEntropy ((r * N : ℕ) : ℝ) ((r * m : ℕ) : ℝ) =
        n * hEntropy (r : ℝ) ((r : ℝ) * x) := by
    have hb_ne : (r : ℝ) * x ≠ 0 := mul_ne_zero hr_ne hx_ne
    have hab_ne : (r : ℝ) - (r : ℝ) * x ≠ 0 := by
      have hpos : 0 < (r : ℝ) - (r : ℝ) * x := by nlinarith [hr_posR, hx_lt_one]
      exact ne_of_gt hpos
    have h := h_entropy_scale_nat N (r * N) (r * m)
      (r : ℝ) ((r : ℝ) * x) hn_ne hr_ne hb_ne hab_ne
      (by rw [Nat.cast_mul]; ring)
      (by
        rw [Nat.cast_mul, show (N : ℝ) = n by rw [hn], hx]
        field_simp [hn_ne])
    simpa [hn, hx] using h
  rw [hNent, hLent, hCent, hRent]
  unfold Phi
  ring

theorem pippenger_mid_term_le
    (N L r c m : ℕ) (θ : ℝ)
    (hN : 0 < N) (hm : 0 < m) (hmN : m < N) (hmL : m < L)
    (hr : 0 < r) (hrc : r < c) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hLθ : (L : ℝ) = θ * (N : ℝ))
    (hcθ : (c : ℝ) = (r : ℝ) / θ)
    (hphi : Phi (r : ℝ) θ ((m : ℝ) / (N : ℝ)) ≤ -(1 : ℝ) / 1000) :
    (N.choose m : ℝ) * (L.choose m : ℝ) *
        ((c * m).choose (r * m) : ℝ) / ((r * N).choose (r * m) : ℝ)
      ≤ (((r * N : ℕ) : ℝ) + 1) * Real.exp (-(N : ℝ) / 1000) := by
  have hterm := pippenger_term_le_entropy_bound N L r c m hm hmN hmL hr hrc
  have hscale := pippenger_entropy_exponent_eq_phi N L r c m θ hN hm hmN hmL
    hr hθ0 hθ1 hLθ hcθ
  rw [hscale] at hterm
  refine le_trans hterm ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [Real.exp_le_exp]
  have hNnonneg : 0 ≤ (N : ℝ) := by positivity
  have := mul_le_mul_of_nonneg_left hphi hNnonneg
  nlinarith

/-! ## Subset extension -/

/-
Extend a subset to a given cardinality.
-/
theorem exists_superset_card_eq {α : Type*} [Fintype α]
    (B : Finset α) (m : ℕ)
    (hBm : B.card ≤ m) (hmA : m ≤ Fintype.card α) :
    ∃ T : Finset α, B ⊆ T ∧ T.card = m := by
  classical
  -- Since $m \leq \text{Fintype.card } \alpha$, we can choose $m - B.card$ elements from the
  -- complement of $B$ to form $T$.
  obtain ⟨S, hS⟩ : ∃ S : Finset α, S ⊆ Finset.univ \ B ∧ S.card = m - B.card := by
    exact Finset.exists_subset_card_eq ( by simpa [ Finset.card_sdiff ] using by omega );
  use B ∪ S
  rw [
    Finset.card_union_of_disjoint
      (Finset.disjoint_left.mpr fun x hx₁ hx₂ =>
        Finset.mem_sdiff.mp (hS.1 hx₂) |>.2 hx₁),
    hS.2,
    add_tsub_cancel_of_le hBm]
  simp +decide

/-! ## Counting constrained permutations with arbitrary subsets -/

/-
Multiplying by a fixed permutation on the right preserves subtype cardinality.
-/
theorem card_subtype_perm_mul_right {n : ℕ} (π : Equiv.Perm (Fin n))
    (P : Equiv.Perm (Fin n) → Prop) [DecidablePred P] :
    Fintype.card {σ // P σ} = Fintype.card {σ // P (σ * π)} := by
  rw [ Fintype.card_subtype, Fintype.card_subtype ];
  convert Finset.card_image_of_injective _ ( show Function.Injective ( fun x : Equiv.Perm ( Fin n )
    => x * π ) from fun x y hxy => by simpa using hxy ) using 1;
  exact congr_arg Finset.card ( by ext; aesop )

/-
Multiplying by a fixed permutation on the left preserves subtype cardinality.
-/
theorem card_subtype_perm_mul_left {n : ℕ} (π : Equiv.Perm (Fin n))
    (P : Equiv.Perm (Fin n) → Prop) [DecidablePred P] :
    Fintype.card {σ // P σ} = Fintype.card {σ // P (π * σ)} := by
  rw [ Fintype.card_subtype, Fintype.card_subtype ];
  rw [ Finset.card_filter, Finset.card_filter ];
  conv_lhs => rw [ ← Equiv.sum_comp ( Equiv.mulLeft π ) ];
  rfl

/-
There exists a permutation mapping a given finset to the initial segment.
-/
theorem exists_perm_set_to_initial {n : ℕ} (A : Finset (Fin n)) :
    ∃ π : Equiv.Perm (Fin n), ∀ x : Fin n, x ∈ A ↔ (π x).val < A.card := by
  -- Let's denote the set of elements in A as B and the set of elements not in A as Bᶜ.
  set B := A
  set Bc := Finset.univ \ B;
  -- We can define bijections between B and Fin B.card, and between Bc and Fin (n - B.card).
  obtain ⟨f, hf⟩ : ∃ f : B ≃ Fin B.card, True := by
    exact ⟨ Fintype.equivOfCardEq <| by simp +decide, trivial ⟩
  obtain ⟨g, hg⟩ : ∃ g : Bc ≃ Fin (n - B.card), True := by
    exact ⟨ Fintype.equivOfCardEq <| by aesop, trivial ⟩;
  -- Define the permutation π by combining the bijections f and g.
  use Equiv.ofBijective (fun x => if hx : x ∈ B then ⟨f ⟨x, hx⟩, by
    exact lt_of_lt_of_le ( Fin.is_lt _ ) ( by simpa using Finset.card_le_univ B )⟩ else ⟨g ⟨x, by
    exact Finset.mem_sdiff.mpr ⟨ Finset.mem_univ _, hx ⟩⟩ + B.card, by
    lia⟩) ⟨by
  all_goals generalize_proofs at *;
  intro x y hxy; by_cases hx : x ∈ B <;> by_cases hy : y ∈ B <;> simp_all +decide [ Fin.ext_iff ];
  · have := f.injective ( Fin.ext hxy ); aesop;
  · grind +revert;
  · grind;
  · have := g.injective ( Fin.ext hxy ); aesop;, by
    all_goals generalize_proofs at *;
    intro x;
    by_cases hx : x.val < B.card;
    · use f.symm ⟨x.val, hx⟩;
      simp +decide;
    · use g.symm ⟨x.val - B.card, by
        exact tsub_lt_tsub_iff_right ( le_of_not_gt hx ) |>.2 ( Fin.is_lt x )⟩
      generalize_proofs at *;
      have hy : (g.symm ⟨x.val - B.card, by
          exact tsub_lt_tsub_iff_right (le_of_not_gt hx) |>.2 (Fin.is_lt x)⟩ : Fin n) ∉ B := by
        exact (Finset.mem_sdiff.mp (g.symm ⟨x.val - B.card, by
          exact tsub_lt_tsub_iff_right (le_of_not_gt hx) |>.2 (Fin.is_lt x)⟩).property).2
      simp +decide [hy, Fin.ext_iff]
      omega⟩;
  grind

/-
The count of constrained permutations depends only on subset cardinalities.
Proved via conjugation reducing to card_perm_constrained.
-/
theorem card_constrained_perm_subsets {n : ℕ}
    (A B : Finset (Fin n)) (hs : A.card ≤ B.card) (ht : B.card ≤ n) :
    Fintype.card {σ : Equiv.Perm (Fin n) // ∀ a ∈ A, σ a ∈ B} =
    B.card.descFactorial A.card * (n - A.card).factorial := by
  obtain ⟨π₁, hπ₁⟩ := exists_perm_set_to_initial A
  obtain ⟨π₂, hπ₂⟩ := exists_perm_set_to_initial B;
  -- Using the bijection between the sets, we can rewrite the cardinality.
  have h_card_eq : Fintype.card {σ : Equiv.Perm (Fin n) | ∀ a ∈ A, σ a ∈ B} = Fintype.card {σ :
    Equiv.Perm (Fin n) | ∀ i : Fin n, i.val < A.card → (σ i).val < B.card} := by
    rw [ Fintype.card_subtype, Fintype.card_subtype ];
    fapply Finset.card_bij (fun σ _ => π₂ * σ * π₁⁻¹);
    · simp +contextual [ hπ₁, hπ₂ ];
    · aesop;
    · intro b hb; use π₂⁻¹ * b * π₁; simp_all +decide [ mul_assoc ];
  have h_left :
      Fintype.card {σ : Equiv.Perm (Fin n) // ∀ a ∈ A, σ a ∈ B} =
        Fintype.card ↑({σ : Equiv.Perm (Fin n) | ∀ a ∈ A, σ a ∈ B} :
          Set (Equiv.Perm (Fin n))) := by
    exact Fintype.card_congr
      (Equiv.subtypeEquivRight (fun σ : Equiv.Perm (Fin n) => by rfl))
  have h_right :
      Fintype.card
        {σ : Equiv.Perm (Fin n) // ∀ i : Fin n, i.val < A.card → (σ i).val < B.card} =
        Fintype.card ↑({σ : Equiv.Perm (Fin n) |
          ∀ i : Fin n, i.val < A.card → (σ i).val < B.card} :
          Set (Equiv.Perm (Fin n))) := by
    exact Fintype.card_congr
      (Equiv.subtypeEquivRight (fun σ : Equiv.Perm (Fin n) => by rfl))
  calc
    Fintype.card {σ : Equiv.Perm (Fin n) // ∀ a ∈ A, σ a ∈ B}
        = Fintype.card ↑({σ : Equiv.Perm (Fin n) | ∀ a ∈ A, σ a ∈ B} :
            Set (Equiv.Perm (Fin n))) := h_left
    _ = Fintype.card ↑({σ : Equiv.Perm (Fin n) |
          ∀ i : Fin n, i.val < A.card → (σ i).val < B.card} :
          Set (Equiv.Perm (Fin n))) := h_card_eq
    _ = Fintype.card
        {σ : Equiv.Perm (Fin n) // ∀ i : Fin n, i.val < A.card → (σ i).val < B.card} :=
      h_right.symm
    _ = B.card.descFactorial A.card * (n - A.card).factorial :=
      card_perm_constrained n A.card B.card hs ht

/-! ## Good matching existence -/

/-
Right coverage from any equivalence between product types.
-/
theorem right_coverage_of_equiv {N L r c : ℕ} (hc : 0 < c)
    (σ : (Fin N × Fin r) ≃ (Fin L × Fin c)) :
    ∀ w : Fin L, ∃ v : Fin N, ∃ e : Fin r, (σ ⟨v, e⟩).1 = w := by
  -- For any $w \in \text{Fin } L$, consider the element $(w, 0) \in \text{Fin } L \times
  -- \text{Fin } c$. Since $\sigma$ is a bijection, there exists $(v, e) \in \text{Fin } N \times
  -- \text{Fin } r$ such that $\sigma(v, e) = (w, 0)$.
  intro w
  obtain ⟨x, hx⟩ : ∃ x : Fin N × Fin r, σ x = (w, ⟨0, hc⟩) := by
    exact σ.surjective _;
  grind +splitImp

/-
First moment principle: if the weighted sum of subtype cardinalities
is less than the total, then the complement is nonempty.
-/
theorem first_moment_principle {n : ℕ} (hn : 0 < n.factorial)
    (weights : Finset (Finset (Fin n) × Finset (Fin n)))
    (hsum : (∑ p ∈ weights,
      (Fintype.card {σ : Equiv.Perm (Fin n) // ∀ a ∈ p.1, σ a ∈ p.2} : ℝ) / n.factorial) < 1) :
    ∃ σ : Equiv.Perm (Fin n), ∀ p ∈ weights, ¬ (∀ a ∈ p.1, σ a ∈ p.2) := by
  contrapose! hsum; simp_all +decide only [Prod.exists, Fintype.card_subtype]
  -- By definition of $weights$, every permutation $\sigma$ is in at least one of the subtypes
  -- ${σ | ∀ a ∈ p.1, σ a ∈ p.2}$ for $p ∈ weights$.
  have h_union : (Finset.univ : Finset (Equiv.Perm (Fin n))) ⊆ Finset.biUnion weights (fun p =>
    Finset.filter (fun σ => ∀ a ∈ p.1, σ a ∈ p.2) (Finset.univ : Finset (Equiv.Perm (Fin n)))) := by
    intro σ hσ; specialize hsum σ; aesop;
  have := Finset.card_mono h_union
  simp_all +decide only [
    subset_iff,
    mem_univ,
    mem_biUnion,
    mem_filter,
    true_and,
    Prod.exists,
    imp_self,
    implies_true,
    card_univ,
    ge_iff_le]
  rw [← Finset.sum_div _ _ _, le_div_iff₀] <;> norm_cast
  simp_all +decide only [Fintype.card_perm, Fintype.card_fin, one_mul]
  exact this.trans ( Finset.card_biUnion_le )

/-
If the sum of "bad fractions" over a given set of (A,B) pairs is < 1,
then there exists a permutation not satisfying any of them.
-/
theorem good_perm_of_sum_lt (M : ℕ) (_hM : 0 < M)
    (pairs : Finset (Finset (Fin M) × Finset (Fin M)))
    (hsum : (∑ p ∈ pairs,
      (p.2.card.descFactorial p.1.card * (M - p.1.card).factorial : ℝ) / M.factorial) < 1)
    (hpairs : ∀ p ∈ pairs, p.1.card ≤ p.2.card ∧ p.2.card ≤ M) :
    ∃ σ : Equiv.Perm (Fin M), ∀ p ∈ pairs, ¬ (∀ a ∈ p.1, σ a ∈ p.2) := by
  -- Apply the first_moment_principle with n = M and weights = pairs.
  apply first_moment_principle (Nat.factorial_pos M) pairs;
  convert hsum using 2;
  rw [ card_constrained_perm_subsets ];
  · norm_cast;
  · grind;
  · grind

/-
Indexed first moment principle.  This version deliberately keeps duplicate
events indexed separately, which is exactly what the Pippenger overcount needs.
-/
theorem first_moment_principle_indexed {n : ℕ} {ι : Type*}
    (I : Finset ι) (A B : ι → Finset (Fin n))
    (hsum : (∑ i ∈ I,
      (Fintype.card {σ : Equiv.Perm (Fin n) // ∀ a ∈ A i, σ a ∈ B i} : ℝ) /
        n.factorial) < 1) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i ∈ I, ¬ (∀ a ∈ A i, σ a ∈ B i) := by
  classical
  contrapose! hsum; simp_all +decide only [Fintype.card_subtype]
  have h_union : (Finset.univ : Finset (Equiv.Perm (Fin n))) ⊆
      I.biUnion (fun i =>
        Finset.filter (fun σ => ∀ a ∈ A i, σ a ∈ B i)
          (Finset.univ : Finset (Equiv.Perm (Fin n)))) := by
    intro σ hσ
    specialize hsum σ
    rcases hsum with ⟨i, hiI, hσi⟩
    exact Finset.mem_biUnion.mpr
      ⟨i, hiI, Finset.mem_filter.mpr ⟨Finset.mem_univ σ, hσi⟩⟩
  have := Finset.card_mono h_union
  simp_all +decide only [
    subset_iff,
    mem_univ,
    mem_biUnion,
    mem_filter,
    true_and,
    imp_self,
    implies_true,
    card_univ,
    ge_iff_le]
  rw [← Finset.sum_div _ _ _, le_div_iff₀] <;> norm_cast
  · simp_all +decide only [Fintype.card_perm, Fintype.card_fin, one_mul]
    exact this.trans (Finset.card_biUnion_le)
  · exact_mod_cast Nat.factorial_pos n

/-
Indexed version of `good_perm_of_sum_lt`.
-/
theorem good_perm_indexed_of_sum_lt {ι : Type*}
    (M : ℕ) (I : Finset ι) (A B : ι → Finset (Fin M))
    (hsum : (∑ i ∈ I,
      ((B i).card.descFactorial (A i).card * (M - (A i).card).factorial : ℝ) /
        M.factorial) < 1)
    (hpairs : ∀ i ∈ I, (A i).card ≤ (B i).card ∧ (B i).card ≤ M) :
    ∃ σ : Equiv.Perm (Fin M), ∀ i ∈ I, ¬ (∀ a ∈ A i, σ a ∈ B i) := by
  classical
  apply first_moment_principle_indexed I A B
  refine lt_of_eq_of_lt ?_ hsum
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [card_constrained_perm_subsets]
  · norm_cast
  · exact (hpairs i hi).1
  · exact (hpairs i hi).2

theorem desc_factorial_ratio_eq_choose_ratio
    (M a k : ℕ) (_hka : k ≤ a) (hkM : k ≤ M) :
    ((a.descFactorial k * (M - k).factorial : ℝ) / M.factorial) =
      (a.choose k : ℝ) / (M.choose k : ℝ) := by
  have hdescA : (a.descFactorial k : ℝ) = (k.factorial : ℝ) * (a.choose k : ℝ) := by
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose a k
  have hdescM : (M.descFactorial k : ℝ) = (k.factorial : ℝ) * (M.choose k : ℝ) := by
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose M k
  have hfacM : (M.factorial : ℝ) =
      ((M - k).factorial : ℝ) * ((k.factorial : ℝ) * (M.choose k : ℝ)) := by
    have h := Nat.factorial_mul_descFactorial hkM
    have h' : ((M - k).factorial : ℝ) * (M.descFactorial k : ℝ) = (M.factorial : ℝ) := by
      exact_mod_cast h
    rw [hdescM] at h'
    rw [← h']
  rw [hdescA, hfacM]
  have hfact_pos : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have htail_pos : (0 : ℝ) < ((M - k).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (M - k)
  have hchoose_pos : (0 : ℝ) < (M.choose k : ℝ) := by
    exact_mod_cast Nat.choose_pos hkM
  field_simp [hfact_pos.ne', htail_pos.ne', hchoose_pos.ne']

/-- If the expected number of bad sets is < 1, a good matching exists. -/
theorem good_matching_exists_of_ratio_sum_lt_one
    (N L r c A : ℕ) (_hN : 0 < N) (hL : 0 < L) (hr : 0 < r) (hc : r < c)
    (hNL : r * N = c * L) (hA : A ≤ L)
    (hsum : (∑ m ∈ Finset.Icc 1 A,
      (N.choose m : ℝ) * ↑(L.choose m) *
        ↑((c * m).choose (r * m)) / ↑((r * N).choose (r * m))) < 1) :
    ∃ (edge : Fin N → Fin r → Fin L),
      (∀ w : Fin L, ∃ v : Fin N, ∃ e : Fin r, edge v e = w) ∧
      (∀ S : Finset (Fin N), S.card ≤ A →
        (S.biUnion (fun v => Finset.univ.image (edge v))).card ≥ S.card) := by
  classical
  let M := r * N
  let eL : (Fin N × Fin r) ≃ Fin M :=
    Fintype.equivOfCardEq (by simp [M, Nat.mul_comm])
  let eR : (Fin L × Fin c) ≃ Fin M :=
    Fintype.equivOfCardEq (by simp [M, Nat.mul_comm, hNL])
  let leftSet : Finset (Fin N) → Finset (Fin M) :=
    fun S => (S.product (Finset.univ : Finset (Fin r))).image eL
  let rightSet : Finset (Fin L) → Finset (Fin M) :=
    fun T => (T.product (Finset.univ : Finset (Fin c))).image eR
  let triples : Finset (Σ m : ℕ, Finset (Fin N) × Finset (Fin L)) :=
    (Finset.Icc 1 A).sigma fun m =>
      ((Finset.univ : Finset (Fin N)).powersetCard m).product
        ((Finset.univ : Finset (Fin L)).powersetCard m)
  have hcpos : 0 < c := by omega
  have hleft_card : ∀ S : Finset (Fin N), (leftSet S).card = S.card * r := by
    intro S
    dsimp [leftSet]
    rw [Finset.card_image_of_injective]
    · simp
    · exact eL.injective
  have hright_card : ∀ T : Finset (Fin L), (rightSet T).card = T.card * c := by
    intro T
    dsimp [rightSet]
    rw [Finset.card_image_of_injective]
    · simp
    · exact eR.injective
  have hLN : L ≤ N := by
    have hmul : r * L < r * N := by
      have h1 : r * L < c * L := (Nat.mul_lt_mul_right hL).mpr hc
      simpa [hNL] using h1
    exact Nat.le_of_lt (Nat.lt_of_mul_lt_mul_left hmul)
  have hsum_index_eq_desc :
      (∑ i ∈ triples,
        ((rightSet i.2.2).card.descFactorial (leftSet i.2.1).card *
            (M - (leftSet i.2.1).card).factorial : ℝ) / M.factorial)
        =
      ∑ m ∈ Finset.Icc 1 A,
        (N.choose m : ℝ) * (L.choose m : ℝ) *
          (((c * m).descFactorial (r * m) * (r * N - r * m).factorial : ℝ) /
            (r * N).factorial) := by
    dsimp [triples]
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl ?_
    intro m hm
    rw [Finset.sum_product]
    calc
      (∑ x ∈ (Finset.univ : Finset (Fin N)).powersetCard m,
        ∑ y ∈ (Finset.univ : Finset (Fin L)).powersetCard m,
          ↑((rightSet y).card.descFactorial (leftSet x).card) *
              ↑(M - (leftSet x).card).factorial / ↑M.factorial)
          =
        ∑ _x ∈ (Finset.univ : Finset (Fin N)).powersetCard m,
          ∑ _y ∈ (Finset.univ : Finset (Fin L)).powersetCard m,
            (((c * m).descFactorial (r * m) * (r * N - r * m).factorial : ℝ) /
              (r * N).factorial) := by
          refine Finset.sum_congr rfl ?_
          intro S hS
          have hScard : S.card = m := (Finset.mem_powersetCard.mp hS).2
          refine Finset.sum_congr rfl ?_
          intro T hT
          have hTcard : T.card = m := (Finset.mem_powersetCard.mp hT).2
          simp [hleft_card, hright_card, hScard, hTcard, M, mul_comm]
      _ = (N.choose m : ℝ) * (L.choose m : ℝ) *
            (((c * m).descFactorial (r * m) * (r * N - r * m).factorial : ℝ) /
              (r * N).factorial) := by
          simp [Finset.card_powersetCard, mul_assoc, mul_comm]
  have hdesc_eq_choose :
      (∑ m ∈ Finset.Icc 1 A,
        (N.choose m : ℝ) * (L.choose m : ℝ) *
          (((c * m).descFactorial (r * m) * (r * N - r * m).factorial : ℝ) /
            (r * N).factorial))
        =
      ∑ m ∈ Finset.Icc 1 A,
        (N.choose m : ℝ) * (L.choose m : ℝ) *
          ((c * m).choose (r * m) : ℝ) / ((r * N).choose (r * m) : ℝ) := by
    refine Finset.sum_congr rfl ?_
    intro m hm
    have hmA : m ≤ A := (Finset.mem_Icc.mp hm).2
    have hmN : m ≤ N := le_trans (le_trans hmA hA) hLN
    rw [desc_factorial_ratio_eq_choose_ratio]
    · ring
    · exact Nat.mul_le_mul_right m hc.le
    · exact Nat.mul_le_mul_left r hmN
  have hsum_index :
      (∑ i ∈ triples,
        ((rightSet i.2.2).card.descFactorial (leftSet i.2.1).card *
            (M - (leftSet i.2.1).card).factorial : ℝ) / M.factorial) < 1 := by
    rw [hsum_index_eq_desc, hdesc_eq_choose]
    simpa [M, Nat.mul_comm, mul_assoc] using hsum
  have hpairs : ∀ i ∈ triples,
      (leftSet i.2.1).card ≤ (rightSet i.2.2).card ∧ (rightSet i.2.2).card ≤ M := by
    intro i hi
    rcases Finset.mem_sigma.mp hi with ⟨hmI, hp⟩
    rcases Finset.mem_product.mp hp with ⟨hS, hT⟩
    have hScard : i.2.1.card = i.1 := (Finset.mem_powersetCard.mp hS).2
    have hTcard : i.2.2.card = i.1 := (Finset.mem_powersetCard.mp hT).2
    have hmL : i.1 ≤ L := by
      have hsub := (Finset.mem_powersetCard.mp hT).1
      have hcard_le := Finset.card_le_card hsub
      simpa [hTcard] using hcard_le
    constructor
    · rw [hleft_card, hright_card, hScard, hTcard]
      simpa [Nat.mul_comm] using Nat.mul_le_mul_right i.1 hc.le
    · rw [hright_card, hTcard]
      have hmLc : c * i.1 ≤ c * L := Nat.mul_le_mul_left c hmL
      simpa [M, hNL, Nat.mul_comm] using hmLc
  obtain ⟨τ, hτ⟩ :=
    good_perm_indexed_of_sum_lt M triples
      (fun i => leftSet i.2.1) (fun i => rightSet i.2.2) hsum_index hpairs
  let σ : (Fin N × Fin r) ≃ (Fin L × Fin c) := (eL.trans τ).trans eR.symm
  refine ⟨fun v e => (σ (v, e)).1, right_coverage_of_equiv hcpos σ, ?_⟩
  intro S hS
  by_cases hS0 : S.card = 0
  · rw [hS0]
    exact Nat.zero_le _
  by_contra hnot
  have hlt : (S.biUnion (fun v => Finset.univ.image (fun e => (σ (v, e)).1))).card < S.card :=
    Nat.lt_of_not_ge hnot
  let neigh : Finset (Fin L) := S.biUnion (fun v => Finset.univ.image (fun e => (σ (v, e)).1))
  have hneigh_le : neigh.card ≤ S.card := le_of_lt hlt
  have hSL : S.card ≤ L := le_trans hS hA
  obtain ⟨T, hneigh_subset, hTcard⟩ :=
    exists_superset_card_eq (α := Fin L) neigh S.card hneigh_le (by simpa using hSL)
  have hmI : S.card ∈ Finset.Icc 1 A := by
    exact Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt (Nat.pos_of_ne_zero hS0), hS⟩
  have hS_pow : S ∈ (Finset.univ : Finset (Fin N)).powersetCard S.card := by
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S, rfl⟩
  have hT_pow : T ∈ (Finset.univ : Finset (Fin L)).powersetCard S.card := by
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ T, hTcard⟩
  have hi : (⟨S.card, (S, T)⟩ : Σ m : ℕ, Finset (Fin N) × Finset (Fin L)) ∈ triples := by
    dsimp [triples]
    exact Finset.mem_sigma.mpr ⟨hmI, Finset.mem_product.mpr ⟨hS_pow, hT_pow⟩⟩
  have hevent : ∀ a ∈ leftSet S, τ a ∈ rightSet T := by
    intro a ha
    dsimp [leftSet] at ha
    rcases Finset.mem_image.mp ha with ⟨x, hx, rfl⟩
    rcases Finset.mem_product.mp hx with ⟨hxS, _hxe⟩
    have hxT : (σ x).1 ∈ T := by
      apply hneigh_subset
      dsimp [neigh]
      exact Finset.mem_biUnion.mpr
        ⟨x.1, hxS, Finset.mem_image.mpr ⟨x.2, Finset.mem_univ x.2, rfl⟩⟩
    dsimp [rightSet]
    exact Finset.mem_image.mpr
      ⟨σ x, Finset.mem_product.mpr ⟨hxT, Finset.mem_univ (σ x).2⟩, by
        dsimp [σ]
        simp⟩
  exact (hτ ⟨S.card, (S, T)⟩ hi) hevent

/-! ## Constructing FiniteExpanderWitness from a good edge function -/

/-- Package a good edge function into a FiniteExpanderWitness. -/
noncomputable def finiteExpanderOfGoodEdge
    (N L r : ℕ) (A : ℕ) (hN : 0 < N)
    (edge : Fin N → Fin r → Fin L)
    (hcov : ∀ w : Fin L, ∃ v : Fin N, ∃ e : Fin r, edge v e = w)
    (hexp : ∀ S : Finset (Fin N), S.card ≤ A →
        (S.biUnion (fun v => Finset.univ.image (edge v))).card ≥ S.card) :
    FiniteExpanderWitness r where
  V := Fin N
  W := Fin L
  instFintypeV := inferInstance
  instDecEqV := inferInstance
  instFintypeW := inferInstance
  instDecEqW := inferInstance
  edge := edge
  hV_pos := by simp only [Fintype.card_fin]; exact hN
  right_coverage := hcov
  expansionThreshold := A
  expansion := fun S hS => by
    have := hexp S hS
    simp only [edgeNeighbors] at this ⊢
    exact this

end KaltonRoberts
