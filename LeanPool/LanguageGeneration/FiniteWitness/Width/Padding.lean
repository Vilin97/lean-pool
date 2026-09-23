/-
Copyright (c) 2026 Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao
-/
module

public import LeanPool.LanguageGeneration.FiniteWitness.Width.Barriers
public import Mathlib.Algebra.Order.Monoid.WithTop
public import Mathlib.Tactic.Choose

/-!
# Padding witnesses collapses the bad-sample dimension
-/

@[expose] public section

namespace GenLimit.FiniteWitness

variable {α : Type*}

/-- A sample with a nonempty active subfamily whose common core is finite. -/
def BadSample (H : Set (Set α)) (T : Set α → Finset α) (S : Finset α) : Prop :=
  (active H T S).Nonempty ∧ (activeCore H T S).Finite

/-- The supremum of one plus the size of every bad sample for an assignment. -/
noncomputable def badCost (H : Set (Set α)) (T : Set α → Finset α) : WithTop ℕ :=
  ⨆ S : {S : Finset α // BadSample H T S}, ((S.val.card + 1 : ℕ) : WithTop ℕ)

/-- The infimum of bad-sample costs over positive witness assignments. -/
noncomputable def paddedDimension (H : Set (Set α)) : WithTop ℕ :=
  ⨅ T : {T : Set α → Finset α // Positive H T}, badCost H T.val

theorem badCost_le_iff (H : Set (Set α)) (T : Set α → Finset α) (d : ℕ) :
    badCost H T ≤ (d : WithTop ℕ) ↔ ∀ S, BadSample H T S → S.card + 1 ≤ d := by
  rw [badCost, iSup_le_iff]
  constructor
  · intro h S hS
    exact WithTop.coe_le_coe.mp (h ⟨S, hS⟩)
  · intro h S
    exact WithTop.coe_le_coe.mpr (h S.val S.property)

theorem badCost_zero_iff {H : Set (Set α)} {T : Set α → Finset α} (hp : Positive H T) :
    badCost H T = 0 ↔ Valid H T := by
  have hz : badCost H T ≤ ((0 : ℕ) : WithTop ℕ) ↔ badCost H T = 0 := le_bot_iff
  rw [← hz, badCost_le_iff]
  constructor
  · intro h
    refine ⟨hp, ?_⟩
    intro S hs hf
    have := h S ⟨hs, hf⟩
    omega
  · intro h S hs
    exact (h.2 S hs.1 hs.2).elim

/-- A finite bound on bad sample sizes can be removed by retaining and padding witnesses. -/
theorem padding_removes_finite_defects {H : Set (Set α)} (hUUS : Generic.UUS H)
    {T : Set α → Finset α} (hp : Positive H T) (d : ℕ)
    (hb : ∀ S, BadSample H T S → S.card + 1 ≤ d) :
    ∃ T' : Set α → Finset α, Valid H T' ∧ ∀ L ∈ H, T L ⊆ T' L := by
  classical
  have he : ∀ L ∈ H, ∃ F : Finset α, (↑F : Set α) ⊆ L ∧ F.card = d :=
    fun L hL => (hUUS L hL).exists_subset_card_eq d
  choose extra hpos hcard using he
  let T' : Set α → Finset α := fun L => if h : L ∈ H then T L ∪ extra L h else T L
  have ht (L) (hL : L ∈ H) : T L ⊆ T' L := by
    simp only [T', dite_eq_left hL]
    exact Finset.subset_union_left
  have hc (L) (hL : L ∈ H) : d ≤ (T' L).card := by
    rw [← hcard L hL]
    apply Finset.card_le_card
    simp only [T', dite_eq_left hL]
    exact Finset.subset_union_right
  refine ⟨T', ⟨?_, ?_⟩, ht⟩
  · intro L hL x hx
    change x ∈ (if h : L ∈ H then T L ∪ extra L h else T L) at hx
    rw [dite_eq_left hL] at hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hp L hL hx
    · exact hpos L hL hx
  · intro S hS
    have ha {L} (hL : L ∈ active H T' S) : L ∈ active H T S :=
      ⟨hL.1, (ht L hL.1).trans hL.2.1, hL.2.2⟩
    obtain ⟨L, hL⟩ := hS
    have hsize : d ≤ S.card := (hc L hL.1).trans (Finset.card_le_card hL.2.1)
    have hinf : (activeCore H T S).Infinite := by
      intro hf
      have := hb S ⟨⟨L, ha hL⟩, hf⟩
      omega
    exact hinf.mono (show activeCore H T S ⊆ activeCore H T' S from
      fun x hx K hK => hx K (ha hK))

theorem finite_badCost_implies_finiteWitnesses {H : Set (Set α)}
    (hUUS : Generic.UUS H) {T : Set α → Finset α} (hp : Positive H T) {d : ℕ}
    (hb : badCost H T ≤ (d : WithTop ℕ)) : HasFiniteWitnesses H := by
  obtain ⟨T', hT', _⟩ := padding_removes_finite_defects hUUS hp d
    ((badCost_le_iff H T d).mp hb)
  exact hT'.hasFiniteWitnesses

theorem paddedDimension_zero_of_finiteWitnesses {H : Set (Set α)} (h : HasFiniteWitnesses H) :
    paddedDimension H = 0 := by
  obtain ⟨T, hT⟩ := h
  apply le_antisymm _ bot_le
  calc paddedDimension H ≤ badCost H T := iInf_le
        (fun A : {T : Set α → Finset α // Positive H T} => badCost H A.val) ⟨T, hT.1⟩
    _ = 0 := (badCost_zero_iff hT.1).mpr hT

theorem paddedDimension_top_of_not_finiteWitnesses {H : Set (Set α)}
    (hUUS : Generic.UUS H) (h : ¬ HasFiniteWitnesses H) : paddedDimension H = ⊤ := by
  rw [paddedDimension, iInf_eq_top]
  intro T
  generalize hc : badCost H T.val = c
  induction c using WithTop.recTopCoe with
  | top => rfl
  | coe d =>
    exact (h (finite_badCost_implies_finiteWitnesses hUUS T.property (le_of_eq hc))).elim

theorem padding_collapse [Countable α] [Infinite α] (H : Set (Set α))
    (hUUS : Generic.UUS H) :
    (Generic.GeneratableInLimit H → paddedDimension H = 0) ∧
    (¬ Generic.GeneratableInLimit H → paddedDimension H = ⊤) := by
  constructor
  · intro hg
    exact paddedDimension_zero_of_finiteWitnesses
      ((ordinary_iff_finiteWitnesses H hUUS).mp hg)
  · intro hg
    apply paddedDimension_top_of_not_finiteWitnesses hUUS
    intro hf
    exact hg ((ordinary_iff_finiteWitnesses H hUUS).mpr hf)

end GenLimit.FiniteWitness
