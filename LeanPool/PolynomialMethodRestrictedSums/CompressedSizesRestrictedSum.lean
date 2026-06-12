/-
Copyright (c) 2026 Nick Adfor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nick Adfor
-/

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set
import Mathlib.Tactic.Common
import Mathlib.Tactic.Tauto
import Aesop
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Choose.Basic
import LeanPool.PolynomialMethodRestrictedSums.RestrictedSumDistinctSizes


/-!
# Restricted sums with compressed sizes

Theorem 3.2 of Alon-Nathanson-Ruzsa: a lower bound on the restricted sum set
in terms of the "compressed sizes" of the summand sets.

The main theorem of this file was originally proved by Aristotle
(Lean v4.24.0, project request uuid 08cb15be-5c46-4619-9dbf-e523d453b544).
-/

open MvPolynomial

open Finset

open Matrix

open BigOperators

variable {R : Type*} [CommRing R]

variable {p : ℕ} [Fact (Nat.Prime p)] {k : ℕ}

/-
Theorem 3.2:
Let p be a prime, and let A₀, ..., Aₖ be nonempty subsets of Z_p, where |A_i| = b_i,
and suppose b₀ ≥ b₁ ≥ ... ≥ bₖ. Define b′₀, ..., b′ₖ by:
  b′₀ = b₀ and b′_i = min{b′_{i-1} - 1, b_i} for 1 ≤ i ≤ k.
If b′_k > 0 then
  |{a₀ + ... + aₖ : a_i ∈ A_i, a_i ≠ a_j}| ≥ min{p, ∑_{i=0}^k b′_i - (k + 2 choose 2) + 1}.
Moreover, this estimate is sharp for all p ≥ b₀ ≥ ... ≥ bₖ.

Proof from the paper (pages 6-7):

If b′_i ≤ 0 for some i then b′_k ≤ 0, thus b′_i > 0 for all i.
For each i, 1 ≤ i ≤ k, let A′_i be an arbitrary subset of cardinality b′_i of A_i.
Note that the cardinalities of the sets A′_i are pairwise distinct and that
⊕_{i=0}^k A′_i ⊂ ⊕_{i=0}^k A_i.

If ∑_{i=0}^k b′_i ≤ p + (k + 2 choose 2) - 1 then
  |⊕_{i=0}^k A_i| ≥ |⊕_{i=0}^k A′_i| ≥ ∑_{i=0}^k b′_i - (k + 2 choose 2) + 1,
by Proposition 1.2, as needed.

Otherwise, we claim that there are 1 ≤ b''_k < b''_{k-1} < ... < b''_0,
where b''_i ≤ b′_i for all i and ∑_{i=0}^k b''_i = p + (k + 2 choose 2) - 1.
To prove this claim, consider the operator T that maps sequences of integers
(d₀, ..., dₖ) with d₀ > d₁ > ... > dₖ ≥ 1 to sequences of the same kind defined as follows.
The sequence (k + 1, ..., 1) is mapped to itself.
For any other sequence (d₀, ..., dₖ), let j be the largest index for which
d_j > k + 1-j and define T(d₀, ..., dₖ) = (d₀, ..., d_{j-1}, d_j - 1, d_{j + 1}, ..., dₖ).
Clearly, the sum of the elements in T(D) is one less than the sum of the elements of D
for every D that differs from (k + 1, ..., 1), and thus, by repeatedly applying T to our
sequence (b′₀, ..., b′_k) we get the desired sequence (b''₀, ..., b''_k), proving the claim.

Returning to the proof of the theorem in case ∑_{i=0}^k b′_i > p + (k + 2 choose 2) - 1,
let b''_i be as in the claim, and apply Proposition 1.2 to arbitrary subsets A''_i
of cardinality b''_i of A′_i.

It remains to show that the estimate is best possible for all p ≥ b₀ ≥ ... ≥ bₖ ≥ 1.
This is shown by defining A_i = {1, 2, 3, ..., b_i} for all i.
It is easy to check that for these sets A_i, the set ⊕_{i=0}^k A_i is empty if b′_k ≤ 0
and in any case it is contained in the set of consecutive residues
  (k + 2 choose 2), (k + 2 choose 2) + 1, ..., ∑_{i=0}^k b′_i,
where the numbers b′_i are defined by (2). This completes the proof.
-/
noncomputable section AristotleLemmas

/-- A sequence `b` is valid if it is strictly decreasing and the last element is positive. -/
def ValidSeq (k : ℕ) (b : Fin (k + 1) → ℕ) : Prop :=
  (∀ i j, i < j → b j < b i) ∧ 0 < b (Fin.last k)

/-- The base sequence `b_i = k + 1 - i`. Its sum equals `(k + 2).choose 2`. -/
def baseSeq (k : ℕ) : Fin (k + 1) → ℕ := fun i => k + 1 - i

lemma sum_baseSeq (k : ℕ) : ∑ i, baseSeq k i = Nat.choose (k + 2) 2 := by
  unfold baseSeq;
  induction k <;> simp_all +decide [ Nat.choose_succ_succ, Fin.sum_univ_succ ];
  ring

/-
Any valid sequence is component-wise greater than or equal to the base sequence (k + 1, ..., 1).
This follows from the fact that the sequence is strictly decreasing and the last element is at least
1.
-/
lemma valid_seq_ge_base {k : ℕ} {b : Fin (k + 1) → ℕ} (h : ValidSeq k b) :
    ∀ i, b i ≥ baseSeq k i := by
      -- We proceed by induction on $i$.
      intro i
      induction i using Fin.reverseInduction with
      | last => unfold baseSeq; norm_num; linarith [ h.2 ]
      | cast i ih =>
        unfold baseSeq at *
        have := h.1 _ _ ( @Fin.castSucc_lt_succ k i ); norm_num at *; omega

/-
If a valid sequence is not equal to the base sequence, then there must be some index where it is
strictly greater than the base sequence. This is because valid sequences are always component-wise
greater than or equal to the base sequence.
-/
lemma exists_gt_base_of_ne_base {k : ℕ} {b : Fin (k + 1) → ℕ}
    (h_valid : ValidSeq k b) (h_ne : b ≠ baseSeq k) :
    ∃ j, baseSeq k j < b j := by
      -- Since $b$ is not equal to the base sequence, there must be some $i$ where $b i \neq
      -- baseSeq k i$.
      obtain ⟨i, hi⟩ : ∃ i, b i ≠ baseSeq k i := by
        exact Function.ne_iff.mp h_ne;
      -- Since $b$ is valid, we have $b i \geq baseSeq k i$ for all $i$.
      have h_ge : ∀ i, b i ≥ baseSeq k i := by
        exact fun i => valid_seq_ge_base h_valid i;
      exact ⟨ i, lt_of_le_of_ne ( h_ge i ) hi.symm ⟩

/-- The transformation T maps a sequence `b` to `b'` by finding the largest index
`j` such that `b_j > k + 1 - j` and setting `b'_j = b_j - 1`. If no such `j`
exists (i.e. `b` is the base sequence), it returns `b`. -/
noncomputable def transformSeq (k : ℕ) (b : Fin (k + 1) → ℕ) : Fin (k + 1) → ℕ :=
  let s := (Finset.univ : Finset (Fin (k + 1))).filter (fun j => baseSeq k j < b j)
  if h : s.Nonempty then
    let j := s.max' h
    Function.update b j (b j - 1)
  else
    b

/-
If b is a valid sequence different from the base sequence, then T(b) is also a valid sequence, its
sum is one less than the sum of b, and T(b) is component-wise less than or equal to b.
-/
lemma transformSeq_props {k : ℕ} {b : Fin (k + 1) → ℕ}
    (h_valid : ValidSeq k b) (h_not_base : b ≠ baseSeq k) :
    let b' := transformSeq k b
    ValidSeq k b' ∧ (∑ i, b' i = ∑ i, b i - 1) ∧ (∀ i, b' i ≤ b i) := by
      -- Let $j$ be the largest index such that $b_j > k + 1-j$.
      obtain ⟨j, hj⟩ : ∃ j, baseSeq k j < b j ∧ ∀ i > j, baseSeq k i ≥ b i := by
        obtain ⟨j, hj⟩ : ∃ j, baseSeq k j < b j := by
          apply exists_gt_base_of_ne_base h_valid h_not_base;
        exact ⟨ Finset.max' ( Finset.univ.filter fun i => baseSeq k i < b i ) ⟨ j,
            Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hj ⟩ ⟩,
            Finset.mem_filter.mp ( Finset.max'_mem
                ( Finset.univ.filter fun i => baseSeq k i < b i )
                ⟨ j, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hj ⟩ ⟩ ) |>.2,
            fun i hi => le_of_not_gt fun hi' =>
                not_lt_of_ge ( Finset.le_max' _ _ <| by aesop ) hi ⟩;
      -- Show that $b'$ is valid.
      have h_valid_b' : ValidSeq k (Function.update b j (b j - 1)) := by
        refine ⟨?_, ?_⟩
        · intro i j_1 a
          simp_all only [ne_eq, gt_iff_lt, ge_iff_le]
          obtain ⟨left, right⟩ := hj
          by_cases hi : i = j <;> by_cases hj :
            j_1 = j <;> simp_all? +decide [ Function.update_apply ];
          · refine lt_of_le_of_lt ( right _ a ) ?_;
            refine lt_of_lt_of_le ?_ ( Nat.le_sub_one_of_lt left );
            exact tsub_lt_tsub_left_of_le ( by linarith [ Fin.is_lt j, Fin.is_lt j_1 ] ) (
                by simpa using a );
          · exact lt_of_lt_of_le
              ( Nat.sub_lt ( Nat.pos_of_ne_zero ( by linarith [ h_valid.2 ] ) ) zero_lt_one )
              ( h_valid.1 _ _ a |> le_of_lt );
          · exact h_valid.1 _ _ a;
        · unfold Function.update
          simp_all only [ne_eq, gt_iff_lt, ge_iff_le, eq_rec_constant, dite_eq_ite]
          obtain ⟨left, right⟩ := hj
          split
          next h =>
            subst h
            simp_all only [tsub_pos_iff_lt]
            unfold baseSeq at *; aesop;
          next h => exact h_valid.2;
      unfold transformSeq
      obtain ⟨left, right⟩ := hj
      by_cases h : ((Finset.univ : Finset (Fin (k + 1))).filter
          (fun j => baseSeq k j < b j)).Nonempty
      · -- h.Nonempty branch: b' = update b (max') (b max' - 1)
        simp only [dif_pos h]
        refine ⟨?_, ?_, ?_⟩
        · -- ValidSeq of the update
          convert h_valid_b'
          refine le_antisymm ?_ ?_ <;> simp_all? +decide [Finset.max']
          · exact fun i hi => not_lt.1 fun contra => not_lt_of_ge (right i contra) hi
          · exact ⟨j, left, le_rfl⟩
        · -- ∑ x, update b max' (b max' - 1) x = ∑ i, b i - 1
          have h_mem :=
            Finset.max'_mem (Finset.filter (fun j => baseSeq k j < b j) Finset.univ) h
          simp_all only [mem_filter, mem_univ, true_and]
          rw [Finset.sum_update_of_mem]
          · rw [← Finset.sum_sdiff
                (Finset.singleton_subset_iff.mpr (Finset.mem_univ (Finset.max' _ h)))]
            rw [add_comm, Finset.sum_singleton]; omega
          · exact Finset.mem_univ _
        · -- ∀ i, update b max' (b max' - 1) i ≤ b i
          intro i
          by_cases hi : i = Finset.max' (Finset.filter (fun j => baseSeq k j < b j)
            Finset.univ) h <;> aesop
      · -- ¬h.Nonempty branch: b' = b — but this is impossible because we have `j` with
        -- `baseSeq k j < b j`, so the filter is non-empty
        exfalso
        apply h
        exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, left⟩⟩

/-
For any sequence b, the compressed sizes sequence is component-wise less than or equal to b. This
follows immediately from the definition involving min.
-/
lemma compressedSizes_le {k : ℕ} {b : Fin (k + 1) → ℕ} : ∀ i, compressedSizes b i ≤ b i := by
  intro i
  obtain ⟨i, ih⟩ := i
  unfold compressedSizes
  cases i <;> aesop

/-
The value of compressedSizes at index i + 1 is min(compressedSizes b i - 1, b (i + 1)) by
definition.
-/
lemma compressedSizes_succ {k : ℕ} {b : Fin (k + 1) → ℕ} (i : Fin k) :
    compressedSizes b (Fin.succ i) = min (compressedSizes b (Fin.castSucc i) - 1) (
        b (Fin.succ i)) := by
      cases i
      simp_all only [Fin.succ_mk, Fin.castSucc_mk];
      -- By definition of compressedSizes, we have compressedSizes b (i + 1) = min
      -- (compressedSizes
      -- b i - 1) (b (i + 1)).
      rw [compressedSizes]

/-
If the last element of the compressed sizes sequence is positive, then all elements are positive.
This can be proven by reverse induction or by observing that the sequence is non-increasing (or
strictly decreasing where positive). Actually, from the recurrence, b'_{i + 1} <= b'_i - 1, so b'_i
>= b'_{i + 1} + 1 > b'_{i + 1}. So if the last is positive, previous ones are larger.
-/
lemma compressedSizes_pos {k : ℕ} {b : Fin (k + 1) → ℕ}
    (h_last_pos : compressedSizes b (Fin.last k) > 0) :
    ∀ i, 0 < compressedSizes b i := by
      intro i
      have fwd : 0 ≤ compressedSizes b (Fin.last k) := le_of_lt h_last_pos
      induction i using Fin.reverseInduction with
      | last => assumption
      | cast i ih =>
        -- By definition of compressed sizes, we have `compressedSizes b i.succ = min
        -- (compressedSizes b i.castSucc - 1) (b i.succ)`.
        have h_compressed_succ :
            compressedSizes b i.succ = min (compressedSizes b i.castSucc - 1) (b i.succ) := by
          exact compressedSizes_succ i
        cases min_cases ( compressedSizes b i.castSucc - 1 ) ( b i.succ ) <;> omega

/-
If a valid sequence has a sum strictly greater than the target sum (which is at least the base sum),
then there exists a valid sequence with the target sum that is component-wise less than or equal to
the original sequence. This is proved by repeatedly applying the transformation T, which reduces the
sum by 1 at each step while maintaining validity and the component-wise inequality.
-/
lemma polynomialMethod_reduction_lemma {k : ℕ} {b : Fin (k + 1) → ℕ} (h_valid : ValidSeq k b)
    (h_sum : ∑ i, b i > p + Nat.choose (k + 2) 2 - 1) :
    ∃ b'' : Fin (k + 1) → ℕ, ValidSeq k b'' ∧
      (∑ i, b'' i = p + Nat.choose (k + 2) 2 - 1) ∧
      (∀ i, b'' i ≤ b i) := by
        -- Apply the induction hypothesis to find such a $b''$.
        induction h_sum : ∑ i, b i using Nat.strong_induction_on generalizing b with
        | _ m ih =>
        -- By repeatedly applying the transformation T, we can reduce the sum of the sequence by 1
        -- each time while maintaining validity and the component-wise inequality.
        have h_transform : ∃ b' : Fin (k + 1) → ℕ,
            ValidSeq k b' ∧ (∑ i, b' i = ∑ i, b i - 1) ∧ (∀ i, b' i ≤ b i) := by
          by_cases h_eq_base : b = baseSeq k;
          · subst h_eq_base
            exfalso
            have h_sum_1 : ∑ i, baseSeq k i > p + (k + 2).choose 2 - 1 := ‹_›
            rw [ sum_baseSeq ] at h_sum_1;
            have hp : p > 1 := Fact.out
            have hk : 0 < (k + 2).choose 2 := Nat.choose_pos ( by linarith : 2 ≤ k + 2 )
            omega
          · exact ⟨ transformSeq k b, transformSeq_props h_valid h_eq_base |>.1,
              transformSeq_props h_valid h_eq_base |>.2.1,
              transformSeq_props h_valid h_eq_base |>.2.2 ⟩;
        grind

/-
The compressed sizes sequence is strictly decreasing because each term is defined as the minimum of
the previous term minus 1 and the original sequence value. Thus, b'_{i + 1} <= b'_i - 1 < b'_i.
Since the last term is positive by hypothesis, the sequence is valid.
-/
lemma compressedSizes_is_valid {k : ℕ} {b : Fin (k + 1) → ℕ}
    (h_last_pos : compressedSizes b (Fin.last k) > 0) :
    ValidSeq k (compressedSizes b) := by
      refine ⟨ ?_, h_last_pos ⟩;
      -- We proceed by induction on $j - i$.
      intro i j hij
      induction j using Fin.induction generalizing i with
      | zero => tauto
      | succ j ih =>
        rcases lt_or_eq_of_le ( show i ≤ Fin.castSucc j from Nat.le_of_lt_succ hij ) with h | h
        · -- By definition of compressedSizes, we have compressedSizes b (j + 1) = min
          -- (compressedSizes b j - 1) (b (j + 1)).
          have h_compressed_succ :
              compressedSizes b (Fin.succ j) = min (compressedSizes b (Fin.castSucc j) - 1) (
              b (Fin.succ j)) := by
            exact compressedSizes_succ j
          exact h_compressed_succ.symm ▸ lt_of_le_of_lt ( min_le_left _ _ ) (
              Nat.lt_of_le_of_lt ( Nat.sub_le _ _ ) ( ih _ h ) );
        · subst h
          -- By definition of `compressedSizes`, we have `compressedSizes b (Fin.succ j) = min
          -- (compressedSizes b (Fin.castSucc j) - 1) (b (Fin.succ j))`.
          have h_compressed_succ :
              compressedSizes b (Fin.succ j) = min (compressedSizes b (Fin.castSucc j) - 1) (
              b (Fin.succ j)) := by
            exact compressedSizes_succ j
          rcases min_cases ( compressedSizes b ( Fin.castSucc j ) - 1 ) (
              b ( Fin.succ j ) ) with ⟨ left, right ⟩ | ⟨ left, right ⟩
          · -- By definition of `compressedSizes`, we know that `compressedSizes b (Fin.last k) >
            -- 0`.
            rw [h_compressed_succ, left]
            have h_compressed_last_pos : ∀ i, compressedSizes b i > 0 := by
              exact fun i => compressedSizes_pos h_last_pos i
            exact Nat.sub_lt (h_compressed_last_pos _) Nat.one_pos
          · rw [h_compressed_succ, left]
            exact right.trans_le ( Nat.sub_le _ _ )

end AristotleLemmas

theorem compressedSizes_restricted_sum (A : Fin (k + 1) → Finset (ZMod p))
    (_h_nonempty : ∀ i, (A i).Nonempty)
    (_h_sizes_noninc : ∀ i j, i ≤ j → (A j).card ≤ (A i).card)
    (h_last_pos : compressedSizes (fun i => (A i).card) (Fin.last k) > 0) :
    (restrictedSumSet k A).card ≥
    min p (∑ i : Fin (k + 1),
        compressedSizes (fun i => (A i).card) i - (Nat.choose (k + 2) 2) + 1) := by
  by_cases h_case : ∑ i, compressedSizes (fun i => #(A i)) i ≤ p + Nat.choose (k + 2) 2 - 1;
  · -- Let $b'$ be the compressed sizes sequence.
    set b' : Fin (k + 1) → ℕ := compressedSizes (fun i => #(A i));
    -- Since $b'$ is a valid sequence, we can choose subsets $A'_i \subseteq A_i$ such that $|A'_i|
    -- = b'_i$ for all $i$.
    obtain ⟨A', hA'⟩ : ∃ A' : Fin (k + 1) → Finset (ZMod p),
        (∀ i, A' i ⊆ A i) ∧ (∀ i, (A' i).card = b' i) ∧
            (∀ i j, i < j → (A' i).card ≠ (A' j).card) := by
      have h_valid_seq : ValidSeq k b' := by
        apply compressedSizes_is_valid; assumption;
      have h_subset : ∀ i, ∃ A'_i ⊆ A i, (A'_i).card = b' i := by
        intro i;
        exact Finset.exists_subset_card_eq ( by
          linarith [ h_valid_seq.2,
            show compressedSizes ( fun i => Finset.card ( A i ) ) i ≤ Finset.card ( A i )
              from compressedSizes_le i ] );
      choose A' hA' using h_subset;
      exact ⟨ A', fun i => hA' i |>.1, fun i => hA' i |>.2,
          fun i j hij =>
              by rw [ hA' i |>.2, hA' j |>.2 ]; exact ne_of_gt ( h_valid_seq.1 i j hij ) ⟩;
    -- By `restricted_sum_distinct_sizes`, we have |restrictedSumSet k A'| ≥ ∑ b' - (k + 2 choose
    -- 2)
    -- + 1.
    have h_restricted_sum_A' :
        (restrictedSumSet k A').card ≥ (∑ i, b' i) - (Nat.choose (k + 2) 2) + 1 := by
      obtain ⟨ left, left_1, right ⟩ := hA'
      apply le_trans ?_ (restricted_sum_distinct_sizes A' ?_ ?_ ?_)
      · simp_rw [left_1]; exact le_rfl
      · exact fun i => Finset.card_pos.mp ( by
          rw [ left_1 ];
          exact compressedSizes_pos h_last_pos i )
      · intro i j hij
        exact right i j hij
      · simp_rw [left_1]; exact h_case
    -- Since $A'_i \subseteq A_i$, we have $restrictedSumSet k A' \subseteq restrictedSumSet k
    -- A$.
    have h_restricted_sum_subset : restrictedSumSet k A' ⊆ restrictedSumSet k A := by
      intro x hx;
      unfold restrictedSumSet at *; aesop;
    exact le_trans ( min_le_right _ _ ) (
        h_restricted_sum_A'.trans ( Finset.card_mono h_restricted_sum_subset ) );
  · -- Apply the reduction lemma to find a sequence b'' with the desired properties.
    obtain ⟨b'', hb''⟩ : ∃ b'',
        ValidSeq k b'' ∧ (∑ i, b'' i = p + Nat.choose (k + 2) 2 - 1) ∧
            (∀ i, b'' i ≤ compressedSizes (fun i => #(A i)) i) := by
      have := polynomialMethod_reduction_lemma ( compressedSizes_is_valid h_last_pos )
        ( by linarith ); aesop;
    have h_subset : ∃ A'' : Fin (k + 1) → Finset (ZMod p),
        (∀ i, A'' i ⊆ A i) ∧ (∀ i, (A'' i).card = b'' i) ∧
            (∀ i j, i < j → (A'' i).card ≠ (A'' j).card) ∧
            (#(restrictedSumSet k A'') ≥ ∑ i, b'' i - Nat.choose (k + 2) 2 + 1) := by
      have h_subset : ∃ A'' : Fin (k + 1) → Finset (ZMod p),
          (∀ i, A'' i ⊆ A i) ∧ (∀ i, (A'' i).card = b'' i) ∧
              (∀ i j, i < j → (A'' i).card ≠ (A'' j).card) := by
        have h_subset : ∀ i, ∃ A''_i ⊆ A i, (A''_i).card = b'' i := by
          intros i
          have h_card : b'' i ≤ #(A i) := by
            exact le_trans ( hb''.2.2 i ) ( compressedSizes_le i );
          exact Finset.exists_subset_card_eq h_card;
        choose A'' hA''₁ hA''₂ using h_subset;
        exact ⟨ A'', hA''₁, hA''₂,
            fun i j hij => by rw [ hA''₂ i, hA''₂ j ]; exact ne_of_gt ( hb''.1.1 i j hij ) ⟩;
      obtain ⟨ A'', hA''₁, hA''₂, hA''₃ ⟩ := h_subset; use A''
      obtain ⟨ left, left_1, right ⟩ := hb''
      refine ⟨ hA''₁, hA''₂, hA''₃, ?_ ⟩
      refine le_trans ?_ ( restricted_sum_distinct_sizes A'' ?_ ?_ ?_ );
      · grind;
      · exact fun i =>
          Finset.card_pos.mp ( by
            rw [ hA''₂ ];
            exact left.2 |> fun h => by
              exact Nat.pos_of_ne_zero fun hi => by
                have := left.1 i ( Fin.last k ); aesop );
      · aesop;
      · grind;
    obtain ⟨ A'', hA''₁, hA''₂, hA''₃,
        hA''₄ ⟩ := h_subset
    have :=
        Finset.card_mono ( show restrictedSumSet k A'' ⊆ restrictedSumSet k A from ?_ )
    · simp_all only [gt_iff_lt, not_le, ne_eq, ge_iff_le, Order.add_one_le_iff, inf_le_iff]
      obtain ⟨left, right⟩ := hb''
      obtain ⟨left_1, right⟩ := right
      omega
    · intro x hx; unfold restrictedSumSet at *
      simp_all only [gt_iff_lt, not_le, ne_eq, ge_iff_le, Order.add_one_le_iff, mem_image,
          mem_filter, Fintype.mem_piFinset]
      obtain ⟨left, right⟩ := hb''
      obtain ⟨w, h⟩ := hx
      obtain ⟨left_1, right⟩ := right
      obtain ⟨left_2, right_1⟩ := h
      obtain ⟨left_2, right_2⟩ := left_2
      subst right_1
      apply Exists.intro
      · apply And.intro
        on_goal 2 => { rfl
        }
        · simp_all only [not_false_eq_true, implies_true, and_true]
          intro a
          apply hA''₁
          simp_all only
