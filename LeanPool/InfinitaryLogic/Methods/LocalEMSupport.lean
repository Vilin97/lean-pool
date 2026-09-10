/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.ModelTheory.Semantics
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin

/-!
# Shared generic support for the EM term-model constructions

Language-independent lemmas consumed by BOTH the original `skolemColim`-based EM term model
(`EMTermModel.lean`) and the countable local stack (`LocalEMFamily.lean` /
`LocalEMContext.lean`) — extracted here (2026-07-02) so the local stack does not have to import
`EMTermModel.lean`:

* two Mathlib-gap `Term` lemmas: `Term.varFinset_relabel` and
  `Term.realize_eq_of_eq_on_varFinset`;
* the **ordered-support rank** machinery `deepRank` (the 0-indexed position of an element in a
  finite `J`-support, in increasing order) with its inverse/monotonicity lemmas against
  `Finset.orderEmbOfFin`.
-/

namespace FirstOrder.Language

/-- The variables of a relabeled term are the image of the original variables (a Mathlib gap). -/
theorem Term.varFinset_relabel {L' : Language} {α β : Type} [DecidableEq α] [DecidableEq β]
    (g : α → β) (t : L'.Term α) : (t.relabel g).varFinset = t.varFinset.image g := by
  induction t with
  | var i => simp [Term.relabel, Term.varFinset]
  | func f ts ih =>
    ext x
    simp only [Term.relabel, Term.varFinset, ih, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_image]
    tauto

/-- A term's realization depends only on the assignment of the variables that actually appear (a
Mathlib gap). -/
theorem Term.realize_eq_of_eq_on_varFinset {L' : Language} {M' : Type} [L'.Structure M']
    {α : Type} [DecidableEq α] {v w : α → M'} :
    ∀ t : L'.Term α, (∀ x ∈ t.varFinset, v x = w x) → t.realize v = t.realize w := by
  intro t
  induction t with
  | var i => intro h; exact h i (by simp [Term.varFinset])
  | func f ts ih =>
    intro h
    simp only [Term.realize]
    congr 1
    funext i
    exact ih i (fun x hx => h x (by
      simp only [Term.varFinset, Finset.mem_biUnion]
      exact ⟨i, Finset.mem_univ i, hx⟩))

/-! ### Ordered support (ranks) -/

variable (J : Type) [LinearOrder J]

/-- The **rank** of `j` in a finite support `S`: the number of support elements below it, i.e. its
0-indexed position in the increasing `J`-order. So a support `{j₀ < j₁ < …}` has ranks `0, 1, …`
and the deep interpretation sends it to `a_d, a_{d+1}, …` (a strictly-increasing deep tuple). -/
def deepRank (S : Finset J) (j : J) : ℕ := (S.filter (· < j)).card

/-- On the support, ranks strictly increase with `J`-order: the deep tuple is strictly increasing,
hence injective on the support. -/
theorem deepRank_lt_of_lt {S : Finset J} {j j' : J} (hj : j ∈ S) (hjj' : j < j') :
    deepRank J S j < deepRank J S j' := by
  apply Finset.card_lt_card
  refine ⟨fun x hx => ?_, fun hsub => ?_⟩
  · rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, lt_trans hx.2 hjj'⟩
  · exact absurd (Finset.mem_filter.mp (hsub (Finset.mem_filter.mpr ⟨hj, hjj'⟩))).2 (lt_irrefl j)

/-- The rank of the `i`-th support element (in increasing order) is `i`: the enumeration
`orderEmbOfFin` and the rank are mutually inverse. The elements of `S` strictly below the `i`-th
are exactly the first `i`. -/
theorem deepRank_orderEmbOfFin (S : Finset J) {k : ℕ} (h : S.card = k) (i : Fin k) :
    deepRank J S (S.orderEmbOfFin h i) = (i : ℕ) := by
  have step : S.filter (· < S.orderEmbOfFin h i)
      = (Finset.univ.filter (fun j : Fin k => j < i)).image (S.orderEmbOfFin h) := by
    conv_lhs => arg 2; rw [← Finset.image_orderEmbOfFin_univ S h]
    rw [Finset.filter_image]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, OrderEmbedding.lt_iff_lt]
  unfold deepRank
  rw [step, Finset.card_image_of_injective _ (S.orderEmbOfFin h).injective,
    Finset.filter_gt_eq_Iio, Fin.card_Iio]

/-- The rank of a support element is below the cardinality: a valid `Fin S.card` position. -/
theorem deepRank_lt_card {S : Finset J} {j : J} (hj : j ∈ S) : deepRank J S j < S.card := by
  have hmem : (j : J) ∈ Set.range (S.orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin S rfl]; exact hj
  obtain ⟨i, rfl⟩ := hmem
  rw [deepRank_orderEmbOfFin]; exact i.2

/-- The enumeration recovers a support element from its rank: `orderEmbOfFin` at position
`deepRank S j` is `j`, for `j ∈ S`. -/
theorem orderEmbOfFin_deepRank (S : Finset J) {k : ℕ} (h : S.card = k) {j : J} (hj : j ∈ S)
    (hlt : deepRank J S j < k) : S.orderEmbOfFin h ⟨deepRank J S j, hlt⟩ = j := by
  have hmem : (j : J) ∈ Set.range (S.orderEmbOfFin h) := by
    rw [Finset.range_orderEmbOfFin S h]; exact hj
  obtain ⟨i, rfl⟩ := hmem
  congr 1
  exact Fin.ext (deepRank_orderEmbOfFin J S h i)

end FirstOrder.Language
