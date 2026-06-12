/-
Copyright (c) 2026 Nick Adfor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nick Adfor
-/

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Set
import Mathlib.Tactic.Common
import Aesop
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Choose.Basic
import LeanPool.PolynomialMethodRestrictedSums.RestrictedSumDistinctSizes
import LeanPool.PolynomialMethodRestrictedSums.CompressedSizesRestrictedSum


/-!
# The Dias da Silva-Hamidoune theorem

Derives the Dias da Silva-Hamidoune lower bound `dias_da_silva_hamidoune` on
sums of `s` distinct elements of a subset of `ZMod p`.

The main theorem of this file was originally proved by Aristotle
(Lean v4.24.0, project request uuid 7257b62c-6371-4fa8-a5b5-ea19029f0f1f).
-/

open MvPolynomial

open Finset

open Matrix

open BigOperators

variable {R : Type*} [CommRing R]

variable {p : ℕ} [Fact (Nat.Prime p)] {k : ℕ}

/-- The set of all sums of s distinct elements of A -/
def distinctSumSet (A : Finset (ZMod p)) (s : ℕ) : Finset (ZMod p) :=
  (A.powerset.filter (fun B => B.card = s)).image (fun B => ∑ x ∈ B, x)

/--
Theorem 3.3 (Dias da Silva and Hamidoune):
Let p be a prime and let A be a nonempty subset of Z_p.
Let s∧A denote the set of all sums of s distinct elements of A.
Then |s∧A| ≥ min{p, s|A| - s² + 1}.

Proof from the paper:
If |A| < s there is nothing to prove.
Otherwise put s = k + 1 and apply Theorem 3.2 with A_i = A for all i.
Here b′_i = |A| - i for all 0 ≤ i ≤ k and hence
|(k + 1)∧A| = |⊕_{i=0}^k A_i| ≥ min{p, ∑_{i=0}^k (|A| - i) - (k + 2 choose 2) + 1}
= min{p, (k + 1)|A| - (k + 1 choose 2) - (k + 2 choose 2) + 1}
= min{p, (k + 1)|A| - (k + 1)² + 1}.

Detailed calculation:
Let k = s - 1, so s = k + 1.
For Theorem 3.2 with all A_i = A, we have b_i = |A| for all i.
The compressed sizes are:
  b′₀ = |A|
  b′₁ = min{b′₀ - 1, |A|} = |A| - 1
  b′₂ = min{b′₁ - 1, |A|} = |A| - 2
  ...
  b′_k = min{b′_{k-1} - 1, |A|} = |A| - k = |A| - (s - 1)

Then ∑_{i=0}^k b′_i = ∑_{i=0}^k (|A| - i) = (k + 1)|A| - ∑_{i=0}^k i
                    = (k + 1)|A| - (k(k + 1))/2
                    = (k + 1)|A| - (k + 1 choose 2)

Now (k + 2 choose 2) = (k + 1)(k + 2)/2 = (k + 1 choose 2) + (k + 1)

So ∑ b′_i - (k + 2 choose 2) + 1 = [(k + 1)|A| - (k + 1 choose 2)] - [(k + 1 choose 2) + (k + 1)] +
1
                              = (k + 1)|A| - 2*(k + 1 choose 2) - (k + 1) + 1
                              = (k + 1)|A| - [2*(k(k + 1))/2] - k
                              = (k + 1)|A| - k(k + 1) - k
                              = (k + 1)|A| - (k + 1)k - k
                              = (k + 1)|A| - (k + 1)² + 1
                              = s|A| - s² + 1

Thus by Theorem 3.2, we get the desired bound.
-/
theorem dias_da_silva_hamidoune (A : Finset (ZMod p)) (s : ℕ)
    (_h_nonempty : A.Nonempty) (h_s_le_card : s ≤ A.card) :
    (distinctSumSet A s).card ≥ min p (s * A.card - s ^ 2 + 1) := by
  by_cases hs : s = 0
  · subst hs
    suffices h : (distinctSumSet A 0).Nonempty by
      rw [ge_iff_le]
      calc min p (0 * #A - 0 ^ 2 + 1)
          ≤ 1 := by omega
        _ ≤ _ := Finset.one_le_card.mpr h
    exact ⟨ 0, Finset.mem_image.mpr ⟨ ∅, by aesop ⟩ ⟩
  · -- Apply Theorem 3.2 with k = s - 1 and A_i = A for all i.
    have h_theorem : ∀ (A : Finset (ZMod p)) (k : ℕ) (hk : k + 1 ≤ A.card),
        (restrictedSumSet k (fun _ => A)).card ≥ min p ((k + 1) * A.card - (k + 1) ^ 2 + 1) := by
      intros A k hk
      have h_compressed : ∀ i : Fin (k + 1),
          compressedSizes (fun _ => A.card) i = A.card - i.val := by
        intro i
        induction i using Fin.induction with
        | zero => unfold compressedSizes; aesop
        | succ i ih =>
          unfold compressedSizes
          simp_all only [Order.add_one_le_iff, Fin.val_castSucc, Fin.val_succ]
          split
          next i_1 heq => simp_all only [Fin.zero_eta, Fin.succ_ne_zero]
          next i_1 i_2 hi heq =>
            simp_all only [Nat.succ_eq_add_one]
            rcases i with ⟨ _ | i, hi ⟩ <;> simp_all +decide [ Nat.sub_sub ]
      -- Apply Theorem 3.2 with the given parameters.
      have h_apply_theorem :
          (restrictedSumSet k (fun _ => A)).card ≥ min p ((∑ i : Fin (k + 1),
              (A.card - i.val)) - (Nat.choose (k + 2) 2) + 1) := by
        convert compressedSizes_restricted_sum ( fun _ => A ) _ _ _ using 1;
        · aesop;
        · exact fun i => Finset.card_pos.mp ( by linarith );
        · aesop;
        · aesop;
      -- Simplify the sum $\sum_{i=0}^{k} (A.card - i)$.
      have h_sum_simplified : ∑ i : Fin (k + 1),
          (A.card - i.val) = (k + 1) * A.card - (k + 1) * k / 2 := by
        have h_sum_simplified : ∑ i ∈ Finset.range (k + 1),
            (A.card - i) = (k + 1) * A.card - (k + 1) * k / 2 := by
          have h_sum_simplified : ∑ i ∈ Finset.range (k + 1),
              (A.card - i) = ∑ i ∈ Finset.range (k + 1), A.card - ∑ i ∈ Finset.range (k + 1),
              i := by
            exact eq_tsub_of_add_eq <|
                by rw [ ← Finset.sum_add_distrib ]; exact Finset.sum_congr rfl fun i hi =>
                    tsub_add_cancel_of_le <| by linarith [ Finset.mem_range.mp hi ];
          simp_all +decide [ Finset.sum_range_id ];
        rw [ ← h_sum_simplified, Finset.sum_range ];
      simp_all +decide [ Nat.choose_two_right ];
      grind;
    specialize h_theorem A ( s - 1 )
    rcases s with _ | n
    · simp_all only [zero_le, not_true_eq_false]
    simp_all only [Order.add_one_le_iff, Nat.add_eq_zero_iff, one_ne_zero, and_false,
        not_false_eq_true, add_tsub_cancel_right, Nat.add_one_sub_one, ge_iff_le, inf_le_iff,
        forall_const]
    cases h_theorem with
    | inl h => ?_
    | inr h_1 => ?_
    · -- By definition of $restricted\_sum\_set$, we have $restricted\_sum\_set n (fun _ => A)
      -- \subseteq distinct\_sum\_set A (n + 1)$.
      have h_subset : restrictedSumSet n (fun _ => A) ⊆ distinctSumSet A (n + 1) := by
        intro x hx; unfold restrictedSumSet at hx; unfold distinctSumSet
        simp_all only [ne_eq, mem_image, mem_filter, Fintype.mem_piFinset, mem_powerset]
        obtain ⟨w, h_1⟩ := hx
        obtain ⟨left, right⟩ := h_1
        obtain ⟨left, right_1⟩ := left
        subst right
        use Finset.image w Finset.univ;
        exact ⟨ ⟨ Finset.image_subset_iff.mpr fun i _ => left i,
            by
              rw [ Finset.card_image_of_injective _ fun i j hij =>
                    le_antisymm
                      ( le_of_not_gt fun hi => right_1 _ _ hi hij.symm )
                      ( le_of_not_gt fun hj => right_1 _ _ hj hij ),
                  Finset.card_fin ] ⟩,
          by
            rw [ Finset.sum_image <| fun i _ j _ hij =>
                  le_antisymm
                    ( le_of_not_gt fun hi => right_1 _ _ hi hij.symm )
                    ( le_of_not_gt fun hj => right_1 _ _ hj hij ) ] ⟩;
      exact Or.inl ( le_trans h ( Finset.card_le_card h_subset ) );
    · refine Or.inr (lt_of_lt_of_le h_1 ?_);
      refine Finset.card_le_card ?_;
      intro x hx;
      unfold restrictedSumSet at hx; unfold distinctSumSet
      simp_all only [ne_eq, mem_image, mem_filter, Fintype.mem_piFinset, mem_powerset]
      obtain ⟨w, h_1⟩ := hx
      obtain ⟨left, right⟩ := h_1
      obtain ⟨left, right_1⟩ := left
      subst right
      exact ⟨ Finset.image w Finset.univ, ⟨ Finset.image_subset_iff.mpr fun i _ => left i,
          by
            rw [ Finset.card_image_of_injective _ fun i j hij =>
                  le_antisymm
                    ( le_of_not_gt fun hi => right_1 _ _ hi hij.symm )
                    ( le_of_not_gt fun hj => right_1 _ _ hj hij ),
                Finset.card_fin ] ⟩,
        by
          rw [ Finset.sum_image <| fun i _ j _ hij =>
                le_antisymm
                  ( le_of_not_gt fun hi => right_1 _ _ hi hij.symm )
                  ( le_of_not_gt fun hj => right_1 _ _ hj hij ) ] ⟩
