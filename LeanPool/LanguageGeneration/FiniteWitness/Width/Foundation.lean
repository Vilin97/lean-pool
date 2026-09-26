/-
Copyright (c) 2026 Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao
-/
module

public import LeanPool.LanguageGeneration.FiniteWitness.Separation
public import Mathlib.Data.Set.Countable
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Push

/-! Fixed-assignment interfaces and arbitrary positive separating sets. -/

public section

namespace GenLimit.FiniteWitness

variable {α : Type*}

/-- Every assigned witness consists of positive examples from its target language. -/
@[expose] def Positive (H : Set (Set α)) (T : Set α → Finset α) : Prop :=
  ∀ L ∈ H, (↑(T L) : Set α) ⊆ L

/-- A positive witness assignment whose nonempty active subfamilies have infinite common cores. -/
@[expose]
def Valid (H : Set (Set α)) (T : Set α → Finset α) : Prop :=
  Positive H T ∧ ∀ S, (active H T S).Nonempty → (activeCore H T S).Infinite

/-- Existence of a valid witness assignment with a uniform finite cardinality bound. -/
@[expose]
def HasBoundedWitnesses (H : Set (Set α)) (d : ℕ) : Prop :=
  ∃ T, Valid H T ∧ ∀ L ∈ H, (T L).card ≤ d

theorem valid_iff_positive_separates (H : Set (Set α)) (T : Set α → Finset α) :
    Valid H T ↔ Positive H T ∧ Separates H T := by
  classical
  constructor
  · rintro ⟨hp, hc⟩
    refine ⟨hp, ?_⟩
    intro F hFH hF hC
    by_contra hn
    push Not at hn
    let S := hC.toFinset
    have ha : ∀ L ∈ F, L ∈ active H T S := by
      intro L hL
      refine ⟨hFH hL, ?_, ?_⟩
      · intro x hx
        exact hC.mem_toFinset.mpr (fun K hK => hn L hL K hK x hx)
      · intro x hx
        exact (hC.mem_toFinset.mp hx) L hL
    obtain ⟨L, hL⟩ := hF
    exact (hc S ⟨L, ha L hL⟩) (hC.subset (fun x hx K hK => hx K (ha K hK)))
  · rintro ⟨hp, hs⟩
    refine ⟨hp, ?_⟩
    intro S hS hfin
    have heq : ⋂₀ active H T S = activeCore H T S := by ext; simp [activeCore]
    have hf : (⋂₀ active H T S).Finite := heq.symm ▸ hfin
    obtain ⟨L, hL, K, hK, x, hx, hn⟩ := hs _ (fun _ h => h.1) hS hf
    exact hn (hK.2.2 (hL.2.1 hx))

theorem Valid.hasFiniteWitnesses {H : Set (Set α)} {T : Set α → Finset α}
    (h : Valid H T) : HasFiniteWitnesses H := ⟨T, h⟩

theorem Valid.mono {H K : Set (Set α)} {T : Set α → Finset α}
    (h : Valid H T) (hKH : K ⊆ H) : Valid K T := by
  refine ⟨fun L hL => h.1 L (hKH hL), ?_⟩
  intro S hS
  have hsub : active K T S ⊆ active H T S := fun _ h => ⟨hKH h.1, h.2⟩
  apply (h.2 S (hS.mono hsub)).mono
  intro x hx L hL
  exact hx L (hsub hL)

theorem HasBoundedWitnesses.mono {H K : Set (Set α)} {d : ℕ}
    (h : HasBoundedWitnesses H d) (hKH : K ⊆ H) : HasBoundedWitnesses K d := by
  obtain ⟨T, hT, hd⟩ := h
  exact ⟨T, hT.mono hKH, fun L hL => hd L (hKH hL)⟩

theorem HasBoundedWitnesses.mono_bound {H : Set (Set α)} {d e : ℕ}
    (h : HasBoundedWitnesses H d) (hde : d ≤ e) : HasBoundedWitnesses H e := by
  obtain ⟨T, hT, hd⟩ := h
  exact ⟨T, hT, fun L hL => (hd L hL).trans hde⟩

/-- Every nonempty subfamily with finite intersection contains targets separated by an assigned
set. -/
@[expose] def SetSeparates (H : Set (Set α)) (P : Set α → Set α) : Prop :=
  ∀ F : Set (Set α), F ⊆ H → F.Nonempty → (⋂₀ F).Finite →
    ∃ L ∈ F, ∃ K ∈ F, ¬ P L ⊆ K

theorem setSeparates_finset (H : Set (Set α)) (T : Set α → Finset α) :
    SetSeparates H (fun L => (↑(T L) : Set α)) ↔ Separates H T := by
  classical
  constructor
  · intro h F hFH hF hfin
    obtain ⟨L, hL, K, hK, hn⟩ := h F hFH hF hfin
    by_contra hno
    push Not at hno
    exact hn (fun x hx => hno L hL K hK x hx)
  · intro h F hFH hF hfin
    obtain ⟨L, hL, K, hK, x, hx, hn⟩ := h F hFH hF hfin
    exact ⟨L, hL, K, hK, fun hs => hn (hs hx)⟩

theorem exists_countable_same_core [Countable α] {F : Set (Set α)} (hF : F.Nonempty) :
    ∃ C ⊆ F, C.Nonempty ∧ C.Countable ∧ ⋂₀ C = ⋂₀ F := by
  classical
  obtain ⟨L, hL⟩ := hF
  have hw : ∀ x : α, ∃ K ∈ F, x ∉ ⋂₀ F → x ∉ K := by
    intro x
    by_cases hx : x ∈ ⋂₀ F
    · exact ⟨L, hL, fun hn => (hn hx).elim⟩
    · simp only [Set.mem_sInter, not_forall] at hx
      obtain ⟨K, hK, hxK⟩ := hx
      exact ⟨K, hK, fun _ => hxK⟩
  choose f hf hfx using hw
  refine ⟨insert L (Set.range f), ?_, ⟨L, by simp⟩, (Set.countable_range f).insert L, ?_⟩
  · intro K hK
    rcases hK with rfl | ⟨x, rfl⟩
    · exact hL
    · exact hf x
  · ext x
    constructor
    · intro hx
      by_contra hn
      exact hfx x hn (hx (f x) (by simp))
    · intro hx K hK
      apply hx K
      rcases hK with rfl | ⟨y, rfl⟩
      · exact hL
      · exact hf y

theorem setSeparates_iff_countable [Countable α] (H : Set (Set α))
    (P : Set α → Set α) :
    SetSeparates H P ↔
      ∀ F : Set (Set α), F ⊆ H → F.Nonempty → F.Countable → (⋂₀ F).Finite →
        ∃ L ∈ F, ∃ K ∈ F, ¬ P L ⊆ K := by
  constructor
  · exact fun h F hFH hF _ hfin => h F hFH hF hfin
  · intro h F hFH hF hfin
    obtain ⟨C, hCF, hC, hc, heq⟩ := exists_countable_same_core hF
    obtain ⟨L, hL, K, hK, hn⟩ := h C (hCF.trans hFH) hC hc (heq.symm ▸ hfin)
    exact ⟨L, hCF hL, K, hCF hK, hn⟩

end GenLimit.FiniteWitness
