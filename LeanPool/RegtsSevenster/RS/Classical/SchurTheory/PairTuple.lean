/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.PairInner

/-!
# Pair-content to tuple equivalence

The set of pair-contents with prescribed row and column margins bijects
with the set of row-wise multisets with matching column margins.
-/

namespace RS

open Finset

section Helpers

variable {k : ℕ}

/-- Sum of counts over a full Fintype equals card. -/
private theorem sum_count_univ_gen {γ : Type*} [Fintype γ] [DecidableEq γ]
    (m : Multiset γ) : ∑ j : γ, m.count j = Multiset.card m := by
  rw [← Multiset.toFinset_sum_count_eq m]
  exact (Finset.sum_subset (Finset.subset_univ _)
    (fun a _ ha => Multiset.count_eq_zero.mpr
      (fun hmem => ha (Multiset.mem_toFinset.mpr hmem)))).symm

/-- Filtering by first component and mapping to second preserves count. -/
private theorem filter_fst_map_snd_count
    (m : Multiset (Fin k × Fin k)) (a b : Fin k) :
    ((m.filter (fun c => c.1 = a)).map Prod.snd).count b = m.count (a, b) := by
  rw [Multiset.count_map, Multiset.filter_filter]
  rw [show Multiset.filter (fun c => b = Prod.snd c ∧ Prod.fst c = a) m =
    Multiset.filter (fun c => (a, b) = c) m from
    Multiset.filter_congr fun c _ =>
      ⟨fun ⟨hb, ha⟩ => Prod.ext ha.symm hb,
       fun h => ⟨congr_arg Prod.snd h, (congr_arg Prod.fst h).symm⟩⟩]
  exact (Multiset.count_eq_card_filter_eq m (a, b)).symm

/-- Card of filter by first component equals row-margin sum. -/
private theorem filter_fst_card
    (m : Multiset (Fin k × Fin k)) (a : Fin k) :
    (m.filter (fun c => c.1 = a)).card = ∑ b : Fin k, m.count (a, b) := by
  rw [← Multiset.card_map Prod.snd (m.filter (fun c => c.1 = a))]
  rw [← sum_count_univ_gen]
  exact Finset.sum_congr rfl fun b _ => filter_fst_map_snd_count m a b

/-- `Prod.mk a` is injective in the second argument. -/
private theorem prod_mk_injective (a : Fin k) :
    Function.Injective (Prod.mk a : Fin k → Fin k × Fin k) :=
  fun _ _ h => (Prod.mk.inj h).2

/-- Count of `(a₀, b₀)` in the fintype-sum of mapped multisets. -/
private theorem count_sum_map_mk [DecidableEq (Fin k × Fin k)]
    (f : Fin k → Multiset (Fin k)) (a₀ b₀ : Fin k) :
    Multiset.count (a₀, b₀)
      (∑ a : Fin k, (f a).map (Prod.mk a)) = (f a₀).count b₀ := by
  rw [Multiset.count_sum']
  rw [Fintype.sum_eq_single a₀]
  · exact Multiset.count_map_eq_count' (Prod.mk a₀) (f a₀)
      (prod_mk_injective a₀) b₀
  · intro a ha
    rw [Multiset.count_eq_zero.mpr]
    intro hmem
    rw [Multiset.mem_map] at hmem
    obtain ⟨b, _, hab⟩ := hmem
    exact ha (congr_arg Prod.fst hab)

end Helpers

open scoped Classical in
/-- Pair-contents with prescribed margins biject with row-wise
multisets matching the column margins. -/
theorem pair_tuple_card {n k : ℕ} (α β : Fin k → ℕ)
    (hα : ∑ a : Fin k, α a = n) :
    Fintype.card {s : Sym (Fin k × Fin k) n //
      (∀ a, (∑ b : Fin k, s.1.count (a, b)) = α a) ∧
      (∀ b, (∑ a : Fin k, s.1.count (a, b)) = β b)} =
    Fintype.card {W : ∀ a : Fin k, Sym (Fin k) (α a) //
      ∀ b : Fin k, (∑ a : Fin k, (W a).1.count b) = β b} := by
  apply Fintype.card_congr
  -- Forward map: s ↦ (W, proof)
  -- W a = ⟨(s.1.filter (·.1 = a)).map Prod.snd, card_proof⟩
  -- Backward map: W ↦ (s, proof)
  -- s = ⟨∑ a, (W a).1.map (Prod.mk a), card_proof⟩
  refine {
    toFun := fun ⟨s, hs₁, hs₂⟩ => ?_
    invFun := fun ⟨W, hW⟩ => ?_
    left_inv := fun ⟨s, hs₁, hs₂⟩ => ?_
    right_inv := fun ⟨W, hW⟩ => ?_
  }
  · -- Forward map
    refine ⟨fun a => ⟨(s.1.filter (fun c => c.1 = a)).map Prod.snd, ?_⟩, fun b
      => ?_⟩
    · -- card proof: card = α a
      rw [Multiset.card_map, filter_fst_card]
      exact hs₁ a
    · -- column margin
      rw [Finset.sum_congr rfl (fun a _ => filter_fst_map_snd_count s.1 a b)]
      exact hs₂ b
  · -- Backward map
    refine ⟨⟨∑ a : Fin k, (W a).1.map (Prod.mk a), ?_⟩, fun a₀ => ?_, fun b₀
      => ?_⟩
    · -- card proof: card = n
      rw [Multiset.card_sum]
      rw [Finset.sum_congr rfl (fun a _ => Multiset.card_map (Prod.mk a) (W
        a).1)]
      conv_rhs => rw [← hα]
      exact Finset.sum_congr rfl fun a _ => (W a).2
    · -- row margin
      rw [Finset.sum_congr rfl (fun b _ => count_sum_map_mk (fun a => (W a).1)
        a₀ b)]
      exact sum_count_univ_gen (W a₀).1 |>.trans (W a₀).2
    · -- column margin
      rw [Finset.sum_congr rfl (fun a _ => count_sum_map_mk (fun a => (W a).1) a
        b₀)]
      exact hW b₀
  · -- Left inverse: backward (forward s) = s
    apply Subtype.ext
    apply Subtype.ext
    apply Multiset.ext'
    intro ⟨a₀, b₀⟩
    -- count (a₀, b₀) in backward (forward s) = count (a₀, b₀) in s
    simp only
    rw [count_sum_map_mk]
    exact filter_fst_map_snd_count s.1 a₀ b₀
  · -- Right inverse: forward (backward W) = W
    apply Subtype.ext
    funext a₀
    apply Subtype.ext
    apply Multiset.ext'
    intro b₀
    -- count b₀ in forward (backward W) a₀ = count b₀ in W a₀
    simp only
    rw [filter_fst_map_snd_count]
    exact count_sum_map_mk (fun a => (W a).1) a₀ b₀

end RS
