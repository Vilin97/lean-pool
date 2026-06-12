/-
Copyright (c) 2026 Math_XMUM. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Math_XMUM
-/
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.MinMax
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Common
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Push
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Bound

/-!
# Scarf's combinatorial lemma

This file develops the combinatorial core behind Scarf's lemma. It introduces the
`IndexedLOrder` class of families of linear orders indexed by a finite set, the
notions of dominant sets, cells, rooms and doors, and the colorful/nearly-colorful
machinery used in the parity (door-counting) argument that culminates in
`IndexedLOrder.Scarf`: every coloring of a finite indexed linear order admits a
colorful room.
-/

section fiberlemma

open Finset


variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

lemma injOn_sdiff (s : Finset α) (f : α → β) (h : s.card = (Finset.image f s).card + 1) : ∃ a b,
    a ∈ s ∧ b ∈ s ∧ f a = f b ∧ a ≠ b ∧ Set.InjOn f (s \ ({a, b} : Finset α)) := by
  have of_card_domain_eq_card_image_succ  (s : Finset α) (f : α → β)
      (h : s.card = (Finset.image f s).card + 1) :
  ∃ a b, a ∈ s ∧ b ∈ s ∧ f a = f b ∧ a ≠ b := by
    suffices ¬ Set.InjOn f s by
      contrapose! this
      tauto
    by_contra h1
    linarith [Finset.card_image_of_injOn h1]
  obtain ⟨a, b, as, bs, h1, h2⟩ := of_card_domain_eq_card_image_succ s f h
  have absub : {a, b} ⊆ s :=  Finset.insert_subset as (Finset.singleton_subset_iff.mpr bs)
  use a, b
  repeat apply And.intro;assumption
  rw [←Finset.coe_sdiff]
  apply Finset.injOn_of_card_image_eq
  rw [Finset.card_sdiff_of_subset absub]
  · have : (Finset.image f (s \ {a, b})).card = (Finset.image f s).card - 1 := by
      have aux1 : ∀ c, c ∈ s → c ≠ a → c ≠ b → f c ≠ f a := by
        intro c cs ca cb fcfa
        have cardabc : ({a, b, c} : Finset α).card = 3 := by
          rw [Finset.card_eq_three]
          use a, b, c
          tauto
        have abcss : {a, b, c} ⊆ s := by
          apply Finset.insert_subset as
          apply Finset.insert_subset bs (by simp [cs])
        have : (image f s).card < s.card - 1 :=
          calc
            _ = (image f ((s \ {a, b, c}) ∪ {a, b, c})).card :=
              congrArg _ (congrArg _ (Eq.symm (sdiff_union_of_subset abcss)))
            _ = (image f (s \ {a, b, c}) ∪ image f {a, b, c}).card :=
              congrArg _ (Finset.image_union _ _)
            _ ≤ (image f (s \ {a, b, c})).card + (image f {a, b, c}).card :=
              Finset.card_union_le _ _
            _ = (image f (s \ {a, b, c})).card + 1 := by
              simp only [image_insert, image_singleton, Nat.add_left_cancel_iff, card_eq_one]
              exact ⟨f a, by simp [←h1, fcfa]⟩
            _ ≤ (s \ {a, b, c}).card + 1 := by
              simp [Finset.card_image_le]
            _ = s.card - 3 + 1 := by
              rw [Finset.card_sdiff_of_subset abcss, cardabc]
            _ < _ := by
              have : 2 < s.card := by
                have := Finset.card_le_card abcss
                omega
              omega
        omega
      have aux2 : Finset.image f (s \ {a, b}) = Finset.image f s \ {f a} := by
        ext x
        constructor <;> intro h1'
        · obtain ⟨c, csdiff, fcx⟩ := Finset.mem_image.1 h1'
          obtain ⟨cs, cneab⟩ := Finset.mem_sdiff.1 csdiff
          simp only [mem_insert, mem_singleton, not_or] at cneab
          simp only [mem_sdiff, mem_image, mem_singleton]
          exact ⟨⟨c, cs, fcx⟩, by simp only [← fcx]; exact aux1 c cs cneab.1 cneab.2⟩
        · simp only [mem_sdiff, mem_image, mem_singleton] at h1'
          obtain ⟨c, cs, fcx⟩ := h1'.1
          simp only [← fcx, mem_image, mem_sdiff, mem_insert, mem_singleton, not_or]
          use c
          simp only [cs, true_and, and_true]
          by_contra! hf
          by_cases ceqa : c = a
          · rw [ceqa] at fcx; rw [fcx] at h1'; tauto
          · rw [hf ceqa, ←h1] at fcx; rw [fcx] at h1; tauto
      rw [aux2, Finset.card_sdiff_of_subset (by
        simpa using Finset.singleton_subset_iff.mpr (Finset.mem_image.mpr ⟨a, as, rfl⟩)),
        card_singleton]
    rw [this,Finset.card_pair h2, h]
    simp

end fiberlemma


attribute [local instance] Classical.propDecidable
open Finset

variable {T : Type*} [Inhabited T]
variable {I : Type*}

/-- A family of linear orders on `T` indexed by `I`. -/
class IndexedLOrder (I T : Type*) where
  /-- The linear order on `T` at index `i`. -/
  IST : I → LinearOrder T

instance : FunLike (IndexedLOrder I T) I (LinearOrder T) where
  coe := fun a => a.IST
  coe_injective' := fun f g h => by cases f; cases g; congr


variable [IST : IndexedLOrder I T]

namespace IndexedLOrder

/-- Strict order at index `i` for an `IndexedLOrder`: `lt a b` for the linear
order `IST i`. -/
abbrev ltAt (i : I) (a b : T) : Prop :=
  (IST i).lt a b

/-- Non-strict order at index `i` for an `IndexedLOrder`: `le a b` for the linear
order `IST i`. -/
abbrev leAt (i : I) (a b : T) : Prop :=
  (IST i).le a b

end IndexedLOrder

local notation  lhs "<[" i "]" rhs => IndexedLOrder.ltAt i lhs rhs
local notation  lhs "≤[" i "]" rhs => IndexedLOrder.leAt i lhs rhs

namespace IndexedLOrder
variable (σ : Finset T) (C : Finset I)

/- Definition of Dominant -/
/-- `σ` is dominant for `C`: every point is dominated at some index of `C`. -/
def isDominant :=
  ∀ y, ∃ i ∈ C, ∀ x ∈ σ,  y ≤[i] x

variable {σ C} in
lemma Nonempty_of_Dominant (h : IST.isDominant σ C) : C.Nonempty := by
  obtain ⟨j,hj⟩ := h default
  exact ⟨j, hj.1⟩

/- Lemma 1 -/
omit [Inhabited T] in
lemma Dominant_of_subset (σ τ : Finset T) (C : Finset I) :
  τ ⊆ σ → isDominant σ C  → isDominant τ C := by
    intro h1 h2 y
    obtain ⟨j,hj⟩:= h2 y
    use j,hj.1
    intro x hx
    exact hj.2 x (h1 hx)

omit [Inhabited T] in
lemma Dominant_of_supset (σ : Finset T) (C D : Finset I) :
  C ⊆ D → isDominant σ C  → isDominant σ D := by
    intro h1 h2 y
    obtain ⟨j,hj⟩:= h2 y
    use j,(h1 hj.1)
    intro x hx
    exact hj.2 x hx

/-- The minimum of `σ` in the linear order at index `i`. -/
abbrev mini {σ : Finset T} (h2 : σ.Nonempty) (i : I) : T := @Finset.min' _ (IST i) _ h2

omit [Inhabited T] in
lemma keylemma_of_dominant {σ : Finset T} {C : Finset I} (h1 : IST.isDominant σ C)
    (h2 : σ.Nonempty) : σ  = C.image (mini h2)  :=
  by
    ext a
    constructor
    · intro ha
      rw [mem_image]
      by_contra  hm
      push Not at hm
      obtain ⟨i,hi1,hi2⟩ := h1 a
      replace hm := hm i hi1
      rw [mini] at hm
      have ha1 := @Finset.le_min' _ (IST i) _ h2 a hi2
      have ha2 := @Finset.min'_le _ (IST i) _ _ ha
      apply hm
      refine @eq_of_le_of_ge _ (IST i).toPartialOrder _ _ ha2 ha1
    · suffices h: ∀ x ∈ C, mini h2 x = a → a ∈ σ from
      by simp only [mem_image, forall_exists_index, and_imp];exact h
      intro _ _ ha
      simp [mini,<-ha,Finset.min'_mem]

omit [Inhabited T] in
lemma card_le_of_domiant {σ : Finset T} {C : Finset I} (h1 : IST.isDominant σ C)
    : σ.card  ≤  C.card  := by
  by_cases h2 : σ.Nonempty
  · rw [keylemma_of_dominant h1 h2]
    apply Finset.card_image_le
  · rw [not_nonempty_iff_eq_empty] at h2
    simp only [h2, card_empty, zero_le]

omit [Inhabited T] in
lemma empty_Dominant (h : D.Nonempty) : IST.isDominant Finset.empty D := by
  intro y
  obtain ⟨j,hj⟩ := h
  use j
  constructor
  · exact hj
  · intro x hx
    contradiction

/-- A cell: `σ` is dominant for `C`. -/
abbrev isCell := isDominant σ C

/-- A room: a cell whose color and goods sets have equal size. -/
abbrev isRoom :=  isCell σ C ∧ C.card = σ.card

lemma sigma_nonempty_of_room {σ : Finset T} {C : Finset I} (h : isRoom σ C) : σ.Nonempty  := by
  have hC : C.Nonempty := Nonempty_of_Dominant h.1
  have hCpos : 0 < C.card := Finset.card_pos.2 hC
  have h_card : σ.card = C.card := h.2.symm
  have hpos : 0 < σ.card := by rwa [h_card]
  exact Finset.card_pos.1 hpos

/-- A door: a cell whose color set is one larger than its goods set. -/
abbrev isDoor :=  isCell σ C ∧ C.card = σ.card + 1


variable [DecidableEq T] [DecidableEq I]

/-- The relation that one cell is a door of another room. -/
inductive isDoorof (τ : Finset T) (D : Finset I) (σ : Finset T) (C : Finset I) : Prop
  | idoor (h0 : isCell σ C) (h1 : isDoor τ D) (x :T) (h1 : x ∉ τ) (h2 : insert x τ = σ) (h3 : D = C)
  | odoor (h0 : isCell σ C) (h1 : isDoor τ D) (j :I) (h1 : j ∉ C) (h2 : τ = σ) (h3 : D = insert j C)

omit [Inhabited T] in
lemma isCell_of_door (h1 : isDoorof τ D σ C) : IST.isCell τ D := by
  cases h1
  · rename_i h0 _ j h1 h3 h4
    rw [h4]
    exact IST.Dominant_of_subset _ _ C (by simp [<-h3]) h0
  · rename_i h0 _ j h1 h2' h3
    rw [h2', h3]
    exact IST.Dominant_of_supset _ _ _ (Finset.subset_insert j C) h0

variable {σ C} in
omit [Inhabited T] in
lemma isRoom_of_Door (h1 : isDoorof τ D σ C) : IST.isRoom σ C := by
  cases h1
  · rename_i h0 h2 x h3 h4 h5
    constructor
    · exact h0
    · simp only [<-h5, h2.2, <-h4, h3, not_false_eq_true, Finset.card_insert_of_notMem]
  · rename_i h0 h2 x h3 h4 h5
    constructor
    · exact h0
    · have h6 := Finset.card_insert_of_notMem h3
      subst h4
      replace h5 : D.card = (insert x C).card := by rw [h5]
      rw [h6] at h5
      rw [h2.2] at h5
      exact Eq.symm <| (add_left_inj _).1 h5

/- TODO formula that every room has |I| doors -/
/- This can be skipped first-/

/-def door_para : Sum σ C.toSet.compl ≃ {(τ,D): (Finset T)× (Finset I) | IST.isDoorof τ D σ C} where
  toFun := fun x => match x with
    | .inl y => ⟨(Finset.erase σ y.1, C), by sorry⟩
    | .inr y => ⟨(σ, insert y.1 C), by sorry⟩
  invFun := sorry
  left_inv := sorry
  right_inv := sorry-/

omit [Inhabited T] in
lemma room_is_not_door (h1 : IST.isRoom σ C) : ∀ τ D,  ¬ (isDoorof σ C τ D) := by
  intro τ D hd
  unfold isRoom at h1
  cases hd with
  | idoor h0 hd  x h2 h3 h4 =>
    unfold isDoor at hd
    obtain ⟨_,hd⟩ := hd
    have cond : #σ = #σ +1 := by rw [h1.2] at hd; assumption
    simp at cond
  | odoor h0 hd j h2 h3 h4 =>
    unfold isDoor at hd
    obtain ⟨_,hd⟩ := hd
    have cond : #σ = #σ +1 := by rw [h1.2] at hd; assumption
    simp at cond

variable (τ D) in
/-- An outside door: a door whose goods part is empty. -/
abbrev isOutsideDoor := IST.isDoor τ D ∧ τ = Finset.empty

variable (τ D) in
/-- An internal door: a door that is not an outside door. -/
abbrev isInternalDoor := IST.isDoor τ D ∧ τ.Nonempty

/- Lemma 2-/
omit [Inhabited T] [DecidableEq T] [DecidableEq I] in
lemma outsidedoor_singleton (i : I) : IST.isOutsideDoor Finset.empty {i} := by
  constructor
  · rw [isDoor,isCell,isDominant]
    constructor
    · intro y; use i
      constructor
      · exact Finset.mem_singleton.2 (rfl)
      · intro x hx
        contradiction
    · simp only [Finset.card_singleton]
      rfl
  · rfl


--variable (τ D) in
omit [Inhabited T] [DecidableEq T] [DecidableEq I] in
lemma outsidedoor_is_singleton (h : IST.isOutsideDoor τ D) :  τ = Finset.empty ∧  ∃ i, D = {i} := by
  obtain ⟨h1, h2⟩ := h
  subst h2
  obtain ⟨_,h3⟩ := h1
  replace h4 : D.card = 1 := by
    simp_all
    rfl
  exact ⟨rfl, Finset.card_eq_one.1 h4⟩



section KeyLemma

-- Definition of the sets M_i used in the proof
/-- The set of points maximizing the dominance condition at a missing index. -/
def mSet (τ : Finset T) (D : Finset I) (i : I) (h_nonempty : τ.Nonempty) : Set T :=
  {y : T | ∀ k ∈ D, k ≠ i → mini h_nonempty k <[k] y}

-- Predicate for being the maximal element of M_i with respect to <_i
/-- `m` is maximal in the `mSet` of the given data. -/
def isMaximalInMSet (τ : Finset T) (D : Finset I) (i : I) (h_nonempty : τ.Nonempty) (x : T)
    : Prop :=
  x ∈ mSet τ D i h_nonempty ∧ ∀ y ∈ mSet τ D i h_nonempty, y ≤[i] x

-- The maximal element m_i when M_i is nonempty
/-- A chosen maximal element of the `mSet`. -/
noncomputable def mElement [Fintype T] (τ : Finset T) (D : Finset I) (i : I)
    (h_nonempty : τ.Nonempty)
    (h : (mSet τ D i h_nonempty).Nonempty) : T :=
  @Finset.max' _ (IST i) (mSet τ D i h_nonempty).toFinset (Set.toFinset_nonempty.mpr h)

-- Theorem: mElement is indeed the maximal element
omit [Inhabited T] [DecidableEq T] [DecidableEq I] in
theorem m_element_is_maximal [Fintype T] (τ : Finset T) (D : Finset I) (i : I)
    (h_nonempty : τ.Nonempty)
    (h : (mSet τ D i h_nonempty).Nonempty) :
    isMaximalInMSet τ D i h_nonempty (mElement τ D i h_nonempty h) := by
  unfold isMaximalInMSet mElement
  let s_finset := (mSet τ D i h_nonempty).toFinset
  have h_nonempty_finset: s_finset.Nonempty := Set.toFinset_nonempty.mpr h
  constructor
  · rw [←Set.mem_toFinset]
    exact @Finset.max'_mem _ (IST i) s_finset h_nonempty_finset
  · intros y hy
    rw [←Set.mem_toFinset] at hy
    apply @Finset.le_max' _ (IST i)
    exact hy

-- Sublemma 3.1: τ is dominant with respect to D - i iff i ∈ {a,b} and M_i = ∅
omit [Inhabited T] [DecidableEq T] in
lemma sublemma_3_1 (τ : Finset T) (D : Finset I)
    (h_door : IST.isDoor τ D) (h_nonempty : τ.Nonempty) :
    ∀ i ∈ D, (IST.isDominant τ (D.erase i) ↔
      (∃ a b, a ∈ D ∧ b ∈ D ∧ a ≠ b ∧
       mini h_nonempty a = mini h_nonempty b ∧
       (i = a ∨ i = b) ∧
       mSet τ D i h_nonempty = ∅)) := by
  classical
  intro i hi
  constructor
  · intro h_dom
    have h_card : D.card = τ.card + 1 := h_door.2
    have h_image_card : D.card = (D.image (mini h_nonempty)).card + 1 := by
      have h_dominant : IST.isDominant τ D := h_door.1
      have h_image_sub : D.image (mini h_nonempty) ⊆ τ := by
        intro x hx
        simp only [mem_image] at hx
        obtain ⟨j, _, hj_eq⟩ := hx
        rw [←hj_eq, mini]
        exact @Finset.min'_mem _ (IST j) τ h_nonempty
      have h_image_eq : D.image (mini h_nonempty) = τ := by
        convert (keylemma_of_dominant h_dominant h_nonempty).symm
      rw [h_card, h_image_eq]
    obtain ⟨a, b, ha_mem, hb_mem, h_eq_mini, h_ne, _⟩ := injOn_sdiff D (mini h_nonempty)
        h_image_card
    use a, b, ha_mem, hb_mem, h_ne, h_eq_mini
    by_cases h_case : i = a ∨ i = b
    · constructor
      · exact h_case
      · ext y
        simp only [mSet, ne_eq, gt_iff_lt, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
          not_forall, not_lt, le_min'_iff]
        obtain ⟨k, hk_in_erase, hk_dom⟩ := h_dom y
        have hk_in_D : k ∈ D := (Finset.mem_erase.mp hk_in_erase).2
        have hk_ne_i : k ≠ i := (Finset.mem_erase.mp hk_in_erase).1
        use k, hk_in_D, hk_ne_i
    · push Not at h_case
      obtain ⟨h_i_ne_a, h_i_ne_b⟩ := h_case
      have h_a_in_erase : a ∈ D.erase i := Finset.mem_erase.mpr ⟨h_i_ne_a.symm, ha_mem⟩
      have h_b_in_erase : b ∈ D.erase i := Finset.mem_erase.mpr ⟨h_i_ne_b.symm, hb_mem⟩
      have h_not_inj : ¬Set.InjOn (mini h_nonempty) (D.erase i : Set I) := by
        intro h_inj
        exact h_ne (h_inj h_a_in_erase h_b_in_erase h_eq_mini)
      have h_image_lt : ((D.erase i).image (mini h_nonempty)).card < (D.erase i).card := by
        by_contra h_not_lt
        push Not at h_not_lt
        have h_eq : ((D.erase i).image (mini h_nonempty)).card = (D.erase i).card :=
          le_antisymm Finset.card_image_le h_not_lt
        have h_inj : Set.InjOn (mini h_nonempty) (D.erase i : Set I) :=
          Finset.injOn_of_card_image_eq h_eq
        exact h_not_inj h_inj
      exfalso
      have h_dom_image := keylemma_of_dominant h_dom h_nonempty
      have h_tau_eq_image : τ.card = ((D.erase i).image (mini h_nonempty)).card :=
        congrArg Finset.card h_dom_image
      have h_tau_eq_erase : τ.card = (D.erase i).card := by
        rw [Finset.card_erase_of_mem hi, h_door.2]; simp
      rw [h_tau_eq_erase] at h_tau_eq_image
      rw [h_tau_eq_image] at h_image_lt
      exact not_lt.mpr (le_refl _) h_image_lt
  · rintro ⟨a, b, ha_mem, hb_mem, h_ne, h_eq_mini, h_i_case, h_Mi_empty⟩
    intro y
    unfold mSet at h_Mi_empty
    simp only [Set.mem_setOf_eq, Set.eq_empty_iff_forall_notMem] at h_Mi_empty
    specialize h_Mi_empty y
    push Not at h_Mi_empty
    obtain ⟨k, hk_mem, hk_ne_i, hk_not_lt⟩ := h_Mi_empty
    use k
    constructor
    · exact Finset.mem_erase.mpr ⟨hk_ne_i, hk_mem⟩
    · intro x hx
      letI : LinearOrder T := IST k
      have h_y_le_mini : y ≤[k] mini h_nonempty k := hk_not_lt
      have h_mini_le_x : mini h_nonempty k ≤[k] x := Finset.min'_le τ x hx
      exact @le_trans _ (IST k).toPreorder _ _ _ h_y_le_mini h_mini_le_x

/-Sublemma 3.2-/
omit [Inhabited T] in
lemma sublemma_3_2 (τ : Finset T) (D : Finset I) (x : T)
    (h_door : IST.isDoor τ D) (h_nonempty : τ.Nonempty) (h_not_mem : x ∉ τ)
    (a b : I) (ha : a ∈ D) (hb : b ∈ D) (hab : a ≠ b)
    (h_eq : mini h_nonempty a = mini h_nonempty b) :
    IST.isDominant (insert x τ) D ↔
    (∃ i ∈ ({a, b} : Finset I), (mSet τ D i h_nonempty).Nonempty ∧
     isMaximalInMSet τ D i h_nonempty x) := by
  constructor
  · intro h_dominant
    have h_insert_nonempty : (insert x τ).Nonempty := Finset.insert_nonempty x τ
    have h_min_eq_image : D.image (mini h_insert_nonempty) = insert x τ := by
      convert (keylemma_of_dominant h_dominant h_insert_nonempty).symm
    have h_x_is_min : ∃ i ∈ D, mini h_insert_nonempty i = x := by
      have h_x_in_image : x ∈ D.image (mini h_insert_nonempty) := by
        rw [h_min_eq_image]
        exact Finset.mem_insert_self x τ
      exact Finset.mem_image.mp h_x_in_image
    obtain ⟨i, hi_mem, hi_eq⟩ := h_x_is_min
    have h_is_room : isRoom (insert x τ) D := by
      unfold isRoom
      constructor
      · exact h_dominant
      · rw [Finset.card_insert_of_notMem h_not_mem, h_door.2]
    have h_inj_insert : Set.InjOn (mini h_insert_nonempty) (D : Set I) := by
      apply Finset.injOn_of_card_image_eq
      rw [h_min_eq_image, h_is_room.2]
    have h_mini_lt_x : ∀ k ∈ D, k ≠ i → mini h_nonempty k <[k] x := by
      intros k hk_mem hk_ne_i
      have h_mini_cases : mini h_insert_nonempty k = mini h_nonempty k ∨ mini h_insert_nonempty k =
          x := by
        letI := IST k
        unfold mini
        by_cases h : τ.min' h_nonempty ≤[k] x
        · left
          apply le_antisymm
          · apply Finset.min'_le
            exact Finset.mem_insert_of_mem (Finset.min'_mem _ h_nonempty)
          · apply Finset.le_min'
            intro y hy
            cases Finset.mem_insert.mp hy with
            | inl h_eq => rw [h_eq]; exact h
            | inr h_mem => exact Finset.min'_le _ _ h_mem
        · right
          apply le_antisymm
          · apply Finset.min'_le
            exact Finset.mem_insert_self _ _
          · apply Finset.le_min'
            intro y hy
            cases Finset.mem_insert.mp hy with
            | inl h_eq => rw [h_eq]
            | inr h_mem => exact le_of_not_ge (fun h_le => h (le_trans (Finset.min'_le _ _ h_mem)
                h_le))
      have h_mini_neq_x : mini h_insert_nonempty k ≠ x := by
        intro h_eq
        have h_inj : Set.InjOn (mini h_insert_nonempty) (D : Set I) := h_inj_insert
        have hi_mem_D : i ∈ D := hi_mem
        have hk_mem_D : k ∈ D := hk_mem
        have h_mini_i_eq_x : mini h_insert_nonempty i = x := hi_eq
        exact hk_ne_i (h_inj hi_mem_D hk_mem_D (h_mini_i_eq_x.trans h_eq.symm)).symm
      letI := IST k
      have h_mini_eq_k : mini h_insert_nonempty k = mini h_nonempty k := by
        cases h_mini_cases with
        | inl h => exact h
        | inr h => exact absurd h h_mini_neq_x
      apply lt_of_le_of_ne
      · have h_le : mini h_insert_nonempty k ≤[k] x := by
          apply @Finset.min'_le _ (IST k)
          exact Finset.mem_insert_self x τ
        rw [h_mini_eq_k] at h_le
        exact h_le
      · exact fun h_eq_x => h_not_mem (h_eq_x ▸ Finset.min'_mem τ h_nonempty)
    have h_x_le_mini_i : x ≤[i] mini h_nonempty i := by
      letI := IST i
      rw [← hi_eq]
      unfold mini
      apply Finset.min'_le
      · exact Finset.mem_insert_of_mem (Finset.min'_mem _ h_nonempty)
    have h_i_in_ab : i ∈ ({a, b} : Finset I) := by
      by_cases hik : i = a ∨ i = b
      · simp [hik]
      · push Not at hik
        obtain ⟨hia, hib⟩ := hik
        have h_mini_eq_for_ne_i : ∀ k ∈ D,
            k ≠ i → mini h_insert_nonempty k = mini h_nonempty k := by
          intros k hk_mem hk_ne_i
          have h_cases : mini h_insert_nonempty k = mini h_nonempty k ∨ mini h_insert_nonempty k =
              x := by
            letI := IST k
            by_cases h : τ.min' h_nonempty ≤[k] x
            · left
              apply le_antisymm
              · apply Finset.min'_le
                exact Finset.mem_insert_of_mem (Finset.min'_mem _ h_nonempty)
              · apply Finset.le_min'
                intro y hy
                cases Finset.mem_insert.mp hy with
                | inl h_eq_x => rw [h_eq_x]; exact h
                | inr h_mem => exact Finset.min'_le _ _ h_mem
            · right
              apply le_antisymm
              · apply Finset.min'_le
                exact Finset.mem_insert_self _ _
              · apply Finset.le_min'
                intro y hy
                cases Finset.mem_insert.mp hy with
                | inl h_eq_x => rw [h_eq_x]
                | inr h_mem => exact le_of_not_ge (fun h_le => h (le_trans (Finset.min'_le _ _
                    h_mem) h_le))
          have h_mini_neq_x : mini h_insert_nonempty k ≠ x := by
            intro h_eq_k_x
            exact hk_ne_i (h_inj_insert hk_mem hi_mem (h_eq_k_x.trans hi_eq.symm))
          cases h_cases with
          | inl h => exact h
          | inr h => exact absurd h h_mini_neq_x
        have h_mini_a_eq : mini h_insert_nonempty a = mini h_nonempty a := h_mini_eq_for_ne_i a ha
            (Ne.symm hia)
        have h_mini_b_eq : mini h_insert_nonempty b = mini h_nonempty b := h_mini_eq_for_ne_i b hb
            (Ne.symm hib)
        have h_contr : mini h_insert_nonempty a = mini h_insert_nonempty b := by
          rw [h_mini_a_eq, h_mini_b_eq, h_eq]
        exact (hab (h_inj_insert ha hb h_contr)).elim
    use i, h_i_in_ab
    constructor
    · have h_nonempty_M : (mSet τ D i h_nonempty).Nonempty := by
        use x
        unfold mSet
        apply Set.mem_setOf.mpr
        intro k hk_mem hk_ne_i
        exact h_mini_lt_x k hk_mem hk_ne_i
      exact h_nonempty_M
    · unfold isMaximalInMSet
      constructor
      · unfold mSet
        apply Set.mem_setOf.mpr
        intro k hk_mem hk_ne_i
        exact h_mini_lt_x k hk_mem hk_ne_i
      · intros y hy
        letI := IST i
        unfold mSet at hy
        simp only [ne_eq, gt_iff_lt, Set.mem_setOf_eq] at hy
        obtain ⟨k, hk_in_D, h_y_le_all⟩ := h_dominant y
        by_cases hik : k = i
        · subst hik
          exact h_y_le_all x (Finset.mem_insert_self x τ)
        · have h_lt_y : mini h_nonempty k <[k] y := hy k hk_in_D hik
          have h_mini_mem : mini h_nonempty k ∈ τ := by
            unfold mini
            exact @Finset.min'_mem _ (IST k) _ h_nonempty
          have h_mini_mem_insert : mini h_nonempty k ∈ insert x τ := Finset.mem_insert_of_mem
              h_mini_mem
          have h_le_m : y ≤[k] mini h_nonempty k := h_y_le_all (mini h_nonempty k) h_mini_mem_insert
          letI := IST k
          exact absurd (lt_of_lt_of_le h_lt_y h_le_m) (lt_irrefl _)
  · rintro ⟨i, hi_mem_ab, h_M_nonempty, h_x_is_max⟩
    have h_x_in_M : x ∈ mSet τ D i h_nonempty := h_x_is_max.1
    unfold isDominant
    intro y
    have h_dom_tau := h_door.1
    obtain ⟨k, hk_in_D, hk_dom⟩ := h_dom_tau y
    by_cases h_k_eq_i : k = i
    · subst h_k_eq_i
      have hk_in_D : k ∈ D := by
        cases Finset.mem_insert.mp hi_mem_ab with
        | inl hk_eq_a => rwa [hk_eq_a]
        | inr hk_eq_b => have : k = b := Finset.mem_singleton.mp hk_eq_b; rw [this]; exact hb
      letI := IST k
      by_cases h_y_le_x : y ≤[k] x
      · use k, hk_in_D
        intro z hz
        cases Finset.mem_insert.mp hz with
        | inl h_z_eq_x => rw [h_z_eq_x]; exact h_y_le_x
        | inr h_z_in_tau => exact hk_dom z h_z_in_tau
      · have h_x_lt_y : x <[k] y := lt_of_not_ge h_y_le_x
        have h_y_not_in_M : y ∉ mSet τ D k h_nonempty := by
          intro h_y_in_M
          have h_y_le_x : y ≤[k] x := h_x_is_max.2 y h_y_in_M
          exact not_le.mpr h_x_lt_y h_y_le_x
        simp only [mSet, ne_eq, gt_iff_lt, Set.mem_setOf_eq, not_forall] at h_y_not_in_M
        obtain ⟨j, hj_in_D, hj_ne_k, hj_not_lt⟩ := h_y_not_in_M
        use j, hj_in_D
        intro z hz
        cases Finset.mem_insert.mp hz with
        | inl h_z_eq_x =>
          rw [h_z_eq_x]
          letI := IST j
          have h_mini_lt_x : mini h_nonempty j <[j] x := h_x_in_M j hj_in_D hj_ne_k
          have h_y_le_mini : y ≤[j] mini h_nonempty j := le_of_not_gt hj_not_lt
          exact le_of_lt (lt_of_le_of_lt h_y_le_mini h_mini_lt_x)
        | inr h_z_in_tau =>
          letI := IST j
          have h_y_le_mini : y ≤[j] mini h_nonempty j := le_of_not_gt hj_not_lt
          have h_mini_le_z : mini h_nonempty j ≤[j] z := Finset.min'_le τ z h_z_in_tau
          exact le_trans h_y_le_mini h_mini_le_z
    · use k, hk_in_D
      intro z hz
      cases Finset.mem_insert.mp hz with
      | inl h_z_eq_x =>
        rw [h_z_eq_x]
        letI := IST k
        have h_y_le_mini : y ≤[k] mini h_nonempty k := hk_dom (mini h_nonempty k)
            (Finset.min'_mem τ h_nonempty)
        have h_mini_lt_x : mini h_nonempty k <[k] x := h_x_in_M k hk_in_D h_k_eq_i
        exact le_of_lt (lt_of_le_of_lt h_y_le_mini h_mini_lt_x)
      | inr h_z_in_tau =>
        exact hk_dom z h_z_in_tau


-- Key lemma: M_a and M_b are disjoint
omit [Inhabited T] [DecidableEq T] [DecidableEq I] in
lemma M_sets_disjoint (τ : Finset T) (D : Finset I) (a b : I)
    (h_nonempty : τ.Nonempty) (h_door : IST.isDoor τ D)
    (ha : a ∈ D) (hb : b ∈ D) (hab : a ≠ b)
    (h_eq : mini h_nonempty a = mini h_nonempty b) :
    mSet τ D a h_nonempty ∩ mSet τ D b h_nonempty = ∅ := by
  ext y
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false]
  constructor
  · intro ⟨h_in_a, h_in_b⟩
    unfold mSet at h_in_a h_in_b
    have h_b_ne_a : b ≠ a := hab.symm
    have h_mini_b_lt_y : mini h_nonempty b <[b] y := h_in_a b hb h_b_ne_a
    have h_mini_a_lt_y : mini h_nonempty a <[a] y := h_in_b a ha hab
    rw [h_eq] at h_mini_a_lt_y
    obtain ⟨k, hk_in_D, hk_dom⟩ := h_door.1 y
    have h_mini_b_mem : mini h_nonempty b ∈ τ := by
      unfold mini
      exact @Finset.min'_mem _ (IST b) _ h_nonempty
    have h_y_le_mini_b : y ≤[k] mini h_nonempty b := hk_dom (mini h_nonempty b) h_mini_b_mem
    by_cases hk_eq_a : k = a
    · subst hk_eq_a
      letI := IST k
      exact not_le.mpr h_mini_a_lt_y h_y_le_mini_b
    · by_cases hk_eq_b : k = b
      · subst hk_eq_b
        letI := IST k
        exact not_le.mpr h_mini_b_lt_y h_y_le_mini_b
      · have h_mini_k_lt_y : mini h_nonempty k <[k] y := h_in_a k hk_in_D hk_eq_a
        have h_mini_k_mem : mini h_nonempty k ∈ τ := by
          unfold mini
          exact @Finset.min'_mem _ (IST k) _ h_nonempty
        have h_y_le_mini_k : y ≤[k] mini h_nonempty k := hk_dom (mini h_nonempty k) h_mini_k_mem
        letI := IST k
        exact not_le.mpr h_mini_k_lt_y h_y_le_mini_k
  · intro h
    exact False.elim h

omit [Inhabited T] [DecidableEq T] [DecidableEq I] in
lemma m_element_not_in_tau [Fintype T] (τ : Finset T) (D : Finset I) (i a b : I)
    (h_door : IST.isDoor τ D) (h_nonempty : τ.Nonempty)
    (ha_mem : a ∈ D) (hb_mem : b ∈ D) (hab : a ≠ b)
    (h_eq_mini : mini h_nonempty a = mini h_nonempty b)
    (h_M_nonempty : (mSet τ D i h_nonempty).Nonempty)
    (h_i_is : i = a ∨ i = b) :
    mElement τ D i h_nonempty h_M_nonempty ∉ τ := by
  let m_i := mElement τ D i h_nonempty h_M_nonempty
  have h_max : isMaximalInMSet τ D i h_nonempty m_i :=
    m_element_is_maximal τ D i h_nonempty h_M_nonempty
  intro h_m_in_tau
  obtain ⟨k, hk_mem, hk_dom⟩ := h_door.1 m_i
  by_cases hk_eq_i : k = i
  · subst hk_eq_i
    have h_m_le_mini : m_i ≤[k] mini h_nonempty k := hk_dom (mini h_nonempty k) (by
      unfold mini
      exact @Finset.min'_mem _ (IST k) _ h_nonempty)
    have h_m_eq_mini : m_i = mini h_nonempty k := by
      letI := IST k
      have h_mini_le_m : mini h_nonempty k ≤[k] m_i := Finset.min'_le τ m_i h_m_in_tau
      exact le_antisymm h_m_le_mini h_mini_le_m
    have h_m_in_M : m_i ∈ mSet τ D k h_nonempty := h_max.1
    unfold mSet at h_m_in_M
    cases h_i_is with
    | inl hi_eq_a =>
      subst hi_eq_a
      have h_mini_b_lt_m : mini h_nonempty b <[b] m_i := h_m_in_M b hb_mem hab.symm
      rw [h_m_eq_mini, h_eq_mini] at h_mini_b_lt_m
      letI := IST b
      exact lt_irrefl (mini h_nonempty b) h_mini_b_lt_m
    | inr hi_eq_b =>
      subst hi_eq_b
      have h_mini_a_lt_m : mini h_nonempty a <[a] m_i := h_m_in_M a ha_mem hab
      rw [h_m_eq_mini, ← h_eq_mini] at h_mini_a_lt_m
      letI := IST a
      exact lt_irrefl (mini h_nonempty a) h_mini_a_lt_m
  · have h_m_in_M : m_i ∈ mSet τ D i h_nonempty := h_max.1
    unfold mSet at h_m_in_M
    have h_mini_k_lt_m : mini h_nonempty k <[k] m_i := h_m_in_M k hk_mem hk_eq_i
    have h_m_le_mini_k : m_i ≤[k] mini h_nonempty k := hk_dom (mini h_nonempty k) (by
      unfold mini
      exact @Finset.min'_mem _ (IST k) _ h_nonempty)
    letI := IST k
    exact not_le.mpr h_mini_k_lt_m h_m_le_mini_k

omit [Inhabited T] [DecidableEq T] in
lemma odoor_index_in_pair (τ : Finset T) (D : Finset I) (C : Finset I)
    (a b j : I) (_h_door : IST.isDoor τ D) (h_nonempty : τ.Nonempty)
    (ha_mem : a ∈ D) (hb_mem : b ∈ D) (hab : a ≠ b)
    (h_eq_mini : mini h_nonempty a = mini h_nonempty b)
    (h_dom : IST.isDominant τ C) (h_room_card : C.card = τ.card)
    (_hj_not_mem : j ∉ C) (hc_eq : D = insert j C) :
    j ∈ ({a, b} : Finset I) := by
  by_contra h_not_in
  simp only [Finset.mem_insert, Finset.mem_singleton] at h_not_in
  push Not at h_not_in
  obtain ⟨hj_ne_a, hj_ne_b⟩ := h_not_in
  have ha_in_C : a ∈ C := by
    have ha_in_D : a ∈ D := ha_mem
    rw [hc_eq] at ha_in_D
    cases Finset.mem_insert.mp ha_in_D with
    | inl h_eq => exact absurd h_eq (Ne.symm hj_ne_a)
    | inr h_mem => exact h_mem
  have hb_in_C : b ∈ C := by
    have hb_in_D : b ∈ D := hb_mem
    rw [hc_eq] at hb_in_D
    cases Finset.mem_insert.mp hb_in_D with
    | inl h_eq => exact absurd h_eq (Ne.symm hj_ne_b)
    | inr h_mem => exact h_mem
  have h_inj_C : Set.InjOn (mini h_nonempty) (C : Set I) := by
    apply Finset.injOn_of_card_image_eq
    have h_tau_eq_C_image : τ = C.image (mini h_nonempty) := by
      convert keylemma_of_dominant h_dom h_nonempty
    rw [←h_tau_eq_C_image]
    exact h_room_card.symm
  exact hab (h_inj_C ha_in_C hb_in_C h_eq_mini)

omit [Inhabited T] [DecidableEq T] [DecidableEq I] in
lemma maximal_element_unique [Fintype T] (τ : Finset T) (D : Finset I) (i : I)
    (h_nonempty : τ.Nonempty) (h_M_nonempty : (mSet τ D i h_nonempty).Nonempty)
    (x : T) (h_x_max : isMaximalInMSet τ D i h_nonempty x) :
    x = mElement τ D i h_nonempty h_M_nonempty := by
  let m_i := mElement τ D i h_nonempty h_M_nonempty
  have h_mi_max : isMaximalInMSet τ D i h_nonempty m_i :=
    m_element_is_maximal τ D i h_nonempty h_M_nonempty
  letI := IST i
  have h_x_in_M : x ∈ mSet τ D i h_nonempty := h_x_max.1
  have h_mi_in_M : m_i ∈ mSet τ D i h_nonempty := h_mi_max.1
  have h_x_le_mi : x ≤[i] m_i := h_mi_max.2 x h_x_in_M
  have h_mi_le_x : m_i ≤[i] x := h_x_max.2 m_i h_mi_in_M
  exact le_antisymm h_x_le_mi h_mi_le_x

omit [Inhabited T] [DecidableEq I] in
lemma idoor_determines_element [Fintype T] (τ : Finset T) (D : Finset I)
    (a b : I) (h_door : IST.isDoor τ D) (h_nonempty : τ.Nonempty)
    (ha_mem : a ∈ D) (hb_mem : b ∈ D) (hab : a ≠ b)
    (h_eq_mini : mini h_nonempty a = mini h_nonempty b)
    (h_Ma_nonempty : (mSet τ D a h_nonempty).Nonempty)
    (h_Mb_nonempty : (mSet τ D b h_nonempty).Nonempty)
    (x : T) (h_room : IST.isRoom (insert x τ) D)
    (hx_not_mem : x ∉ τ) :
    x = mElement τ D a h_nonempty h_Ma_nonempty ∨
    x = mElement τ D b h_nonempty h_Mb_nonempty := by
  have h_dom : IST.isDominant (insert x τ) D := h_room.1
  have h_exists_max : ∃ i ∈ ({a, b} : Finset I), (mSet τ D i h_nonempty).Nonempty ∧
      isMaximalInMSet τ D i h_nonempty x := by
    apply (sublemma_3_2 τ D x h_door h_nonempty hx_not_mem a b ha_mem hb_mem hab h_eq_mini).mp
    exact h_dom
  obtain ⟨i, hi_mem, hi_nonempty, hi_max⟩ := h_exists_max
  have h_x_eq_mi : x = mElement τ D i h_nonempty hi_nonempty :=
    maximal_element_unique τ D i h_nonempty hi_nonempty x hi_max
  cases Finset.mem_insert.mp hi_mem with
  | inl hi_eq_a =>
    left
    subst hi_eq_a
    exact h_x_eq_mi
  | inr hi_eq_b =>
    right
    have heq : i = b := Finset.mem_singleton.mp hi_eq_b
    subst heq
    exact h_x_eq_mi

omit [Inhabited T] in
/-- Two-rooms conclusion when both `mSet`s are nonempty. -/
theorem internalDoorTwoRoomsBothNonempty [Finite T] (τ : Finset T) (D : Finset I)
    (h_door : IST.isDoor τ D) (h_nonempty : τ.Nonempty) (a b : I)
    (ha_mem : a ∈ D) (hb_mem : b ∈ D) (h_eq_mini : mini h_nonempty a = mini h_nonempty b)
    (hab : a ≠ b) (h_card : D.card = τ.card + 1)
    (h_disjoint : mSet τ D a h_nonempty ∩ mSet τ D b h_nonempty = ∅)
    (h_Ma_nonempty : (mSet τ D a h_nonempty).Nonempty)
    (h_Mb_nonempty : (mSet τ D b h_nonempty).Nonempty) :
    ∃ (σ₁ σ₂ : Finset T) (C₁ C₂ : Finset I),
      (σ₁, C₁) ≠ (σ₂, C₂) ∧
      IST.isRoom σ₁ C₁ ∧
      IST.isRoom σ₂ C₂ ∧
      isDoorof τ D σ₁ C₁ ∧
      isDoorof τ D σ₂ C₂ ∧
      (∀ σ C, IST.isRoom σ C → isDoorof τ D σ C →
       (σ = σ₁ ∧ C = C₁) ∨ (σ = σ₂ ∧ C = C₂)) := by
  have : Fintype T := Fintype.ofFinite T
  let m_a := mElement τ D a h_nonempty h_Ma_nonempty
  let m_b := mElement τ D b h_nonempty h_Mb_nonempty
  have h_ma_max : isMaximalInMSet τ D a h_nonempty m_a :=
    m_element_is_maximal τ D a h_nonempty h_Ma_nonempty
  have h_mb_max : isMaximalInMSet τ D b h_nonempty m_b :=
    m_element_is_maximal τ D b h_nonempty h_Mb_nonempty
  have h_ma_ne_mb : m_a ≠ m_b := by
    intro h_eq
    have h_ma_in_Ma : m_a ∈ mSet τ D a h_nonempty := h_ma_max.1
    have h_mb_in_Mb : m_b ∈ mSet τ D b h_nonempty := h_mb_max.1
    rw [h_eq] at h_ma_in_Ma
    have h_in_inter : m_b ∈ mSet τ D a h_nonempty ∩ mSet τ D b h_nonempty :=
      ⟨h_ma_in_Ma, h_mb_in_Mb⟩
    rw [h_disjoint] at h_in_inter
    exact Set.notMem_empty m_b h_in_inter
  have h_ma_not_mem : m_a ∉ τ :=
    m_element_not_in_tau τ D a a b h_door h_nonempty ha_mem hb_mem hab h_eq_mini h_Ma_nonempty
        (Or.inl rfl)
  have h_mb_not_mem : m_b ∉ τ :=
    m_element_not_in_tau τ D b a b h_door h_nonempty ha_mem hb_mem hab h_eq_mini h_Mb_nonempty
        (Or.inr rfl)
  use insert m_a τ, insert m_b τ, D, D
  constructor
  · intro h_pair_eq
    have h_eq : insert m_a τ = insert m_b τ := congr_arg Prod.fst h_pair_eq
    have : m_a = m_b := by
      have h_ma_in : m_a ∈ insert m_a τ := Finset.mem_insert_self m_a τ
      rw [h_eq] at h_ma_in
      cases Finset.mem_insert.mp h_ma_in with
      | inl h => exact h
      | inr h => exact absurd h h_ma_not_mem
    exact h_ma_ne_mb this
  constructor
  · constructor
    · apply (sublemma_3_2 τ D m_a h_door h_nonempty h_ma_not_mem a b ha_mem hb_mem hab
        h_eq_mini).mpr
      use a, by simp
    · rw [Finset.card_insert_of_notMem h_ma_not_mem, h_card]
  constructor
  · constructor
    · apply (sublemma_3_2 τ D m_b h_door h_nonempty h_mb_not_mem a b ha_mem hb_mem hab
        h_eq_mini).mpr
      use b, by simp
    · rw [Finset.card_insert_of_notMem h_mb_not_mem, h_card]
  constructor
  · apply isDoorof.idoor
    · apply (sublemma_3_2 τ D m_a h_door h_nonempty h_ma_not_mem a b ha_mem hb_mem hab
        h_eq_mini).mpr
      use a, by simp
    · exact h_door
    · exact h_ma_not_mem
    · rfl
    · rfl
  constructor
  · apply isDoorof.idoor
    · apply (sublemma_3_2 τ D m_b h_door h_nonempty h_mb_not_mem a b ha_mem hb_mem hab
        h_eq_mini).mpr
      use b, by simp
    · exact h_door
    · exact h_mb_not_mem
    · rfl
    · rfl
  · intros σ C h_room h_door_rel
    cases h_door_rel with
    | idoor h0 _ x hx_not_mem hx_eq hc_eq =>
      subst hx_eq hc_eq
      have h_insert_room : IST.isRoom (insert x τ) D := by
        constructor
        · exact h0
        · rw [Finset.card_insert_of_notMem hx_not_mem, h_card]
      cases idoor_determines_element τ D a b h_door h_nonempty ha_mem hb_mem hab h_eq_mini
          h_Ma_nonempty h_Mb_nonempty x h_insert_room hx_not_mem with
      | inl h_x_eq_ma => left; exact ⟨h_x_eq_ma ▸ rfl, rfl⟩
      | inr h_x_eq_mb => right; exact ⟨h_x_eq_mb ▸ rfl, rfl⟩
    | odoor h0 _ j hj_not_mem hj_eq hc_eq =>
      subst hj_eq
      have h_card_eq : C.card = τ.card := h_room.2
      have h_card_D : D.card = τ.card + 1 := h_door.2
      have h_card_insert : (insert j C).card = C.card + 1 := Finset.card_insert_of_notMem
          hj_not_mem
      rw [hc_eq] at h_card_D
      rw [h_card_insert] at h_card_D
      rw [h_card_eq] at h_card_D
      have hj_in_ab : j = a ∨ j = b := by
        by_contra h_not_in
        push Not at h_not_in
        obtain ⟨hj_ne_a, hj_ne_b⟩ := h_not_in
        have ha_in_C : a ∈ C := by
          have ha_in_D : a ∈ D := ha_mem
          rw [hc_eq] at ha_in_D
          cases Finset.mem_insert.mp ha_in_D with
          | inl h_eq => exact False.elim (hj_ne_a h_eq.symm)
          | inr h_mem => exact h_mem
        have hb_in_C : b ∈ C := by
          have hb_in_D : b ∈ D := hb_mem
          rw [hc_eq] at hb_in_D
          cases Finset.mem_insert.mp hb_in_D with
          | inl h_eq => exact False.elim (hj_ne_b h_eq.symm)
          | inr h_mem => exact h_mem
        have h_inj_C : Set.InjOn (mini h_nonempty) (C : Set I) := by
          apply Finset.injOn_of_card_image_eq
          have h_tau_eq_C_image : τ = C.image (mini h_nonempty) := by
            convert keylemma_of_dominant h0 h_nonempty
          rw [←h_tau_eq_C_image]
          exact h_card_eq.symm
        have h_a_ne_b : a ≠ b := hab
        have h_mini_eq : mini h_nonempty a = mini h_nonempty b := h_eq_mini
        exact h_a_ne_b (h_inj_C ha_in_C hb_in_C h_mini_eq)
      cases hj_in_ab with
      | inl hj_eq_a =>
        have h_dom_C : IST.isDominant τ C := h0
        rw [show C = D.erase j by rw [hc_eq]; exact (Finset.erase_insert hj_not_mem).symm]
            at h_dom_C
        have hj_eq_a_mem : j ∈ D := by rw [hj_eq_a]; exact ha_mem
        have h_contra := (sublemma_3_1 τ D h_door h_nonempty j hj_eq_a_mem).mp h_dom_C
        obtain ⟨a', b', ha'_mem, hb'_mem, ha'b'_ne, h_eq_mini', h_j_in_pair,
            h_M_empty⟩ := h_contra
        have h_Mj_nonempty : (mSet τ D j h_nonempty).Nonempty := by
          rw [hj_eq_a]; exact h_Ma_nonempty
        rw [h_M_empty] at h_Mj_nonempty
        exact False.elim (Set.not_nonempty_empty h_Mj_nonempty)
      | inr hj_eq_b =>
        have h_dom_C : IST.isDominant τ C := h0
        rw [show C = D.erase j by rw [hc_eq]; exact (Finset.erase_insert hj_not_mem).symm]
            at h_dom_C
        have hj_eq_b_mem : j ∈ D := by rw [hj_eq_b]; exact hb_mem
        have h_contra := (sublemma_3_1 τ D h_door h_nonempty j hj_eq_b_mem).mp h_dom_C
        obtain ⟨a', b', ha'_mem, hb'_mem, ha'b'_ne, h_eq_mini', h_j_in_pair,
            h_M_empty⟩ := h_contra
        have h_Mj_nonempty : (mSet τ D j h_nonempty).Nonempty := by
          rw [hj_eq_b]; exact h_Mb_nonempty
        rw [h_M_empty] at h_Mj_nonempty
        exact False.elim (Set.not_nonempty_empty h_Mj_nonempty)

omit [Inhabited T] in
/-- Two-rooms conclusion when the first `mSet` is empty but the second is nonempty. -/
theorem internalDoorTwoRoomsLeftEmpty [Finite T] (τ : Finset T) (D : Finset I)
    (h_door : IST.isDoor τ D) (h_nonempty : τ.Nonempty) (a b : I)
    (ha_mem : a ∈ D) (hb_mem : b ∈ D) (h_eq_mini : mini h_nonempty a = mini h_nonempty b)
    (hab : a ≠ b) (h_card : D.card = τ.card + 1)
    (h_disjoint : mSet τ D a h_nonempty ∩ mSet τ D b h_nonempty = ∅)
    (h_Ma_empty : mSet τ D a h_nonempty = ∅)
    (h_Mb_nonempty : (mSet τ D b h_nonempty).Nonempty) :
    ∃ (σ₁ σ₂ : Finset T) (C₁ C₂ : Finset I),
      (σ₁, C₁) ≠ (σ₂, C₂) ∧
      IST.isRoom σ₁ C₁ ∧
      IST.isRoom σ₂ C₂ ∧
      isDoorof τ D σ₁ C₁ ∧
      isDoorof τ D σ₂ C₂ ∧
      (∀ σ C, IST.isRoom σ C → isDoorof τ D σ C →
       (σ = σ₁ ∧ C = C₁) ∨ (σ = σ₂ ∧ C = C₂)) := by
  have : Fintype T := Fintype.ofFinite T
  let m_b := mElement τ D b h_nonempty h_Mb_nonempty
  have h_mb_max : isMaximalInMSet τ D b h_nonempty m_b :=
    m_element_is_maximal τ D b h_nonempty h_Mb_nonempty
  have h_mb_not_mem : m_b ∉ τ :=
    m_element_not_in_tau τ D b a b h_door h_nonempty ha_mem hb_mem hab h_eq_mini h_Mb_nonempty
        (Or.inr rfl)
  use insert m_b τ, τ, D, D.erase a
  constructor
  · intro h_pair_eq
    have h_eq : insert m_b τ = τ := congr_arg Prod.fst h_pair_eq
    have h_mb_in : m_b ∈ insert m_b τ := Finset.mem_insert_self m_b τ
    rw [h_eq] at h_mb_in
    exact h_mb_not_mem h_mb_in
  constructor
  · constructor
    · apply (sublemma_3_2 τ D m_b h_door h_nonempty h_mb_not_mem a b ha_mem hb_mem hab
        h_eq_mini).mpr
      use b, by simp
    · rw [Finset.card_insert_of_notMem h_mb_not_mem, h_card]
  constructor
  · constructor
    · apply (sublemma_3_1 τ D h_door h_nonempty a ha_mem).mpr
      use a, b, ha_mem, hb_mem, hab, h_eq_mini, (Or.inl rfl), h_Ma_empty
    · rw [Finset.card_erase_of_mem ha_mem, h_card]
      simp
  constructor
  · apply isDoorof.idoor
    · apply (sublemma_3_2 τ D m_b h_door h_nonempty h_mb_not_mem a b ha_mem hb_mem hab
        h_eq_mini).mpr
      use b, by simp
    · exact h_door
    · exact h_mb_not_mem
    · rfl
    · rfl
  constructor
  · apply isDoorof.odoor
    · apply (sublemma_3_1 τ D h_door h_nonempty a ha_mem).mpr
      use a, b, ha_mem, hb_mem, hab, h_eq_mini, (Or.inl rfl), h_Ma_empty
    · exact h_door
    · exact Finset.notMem_erase a D
    · rfl
    · exact (Finset.insert_erase ha_mem).symm
  · intros σ C h_room h_door_rel
    cases h_door_rel with
    | idoor h0 _ x hx_not_mem hx_eq hc_eq =>
      subst hx_eq hc_eq
      have h_dom : IST.isDominant (insert x τ) D := h0
      have h_exists_max : ∃ i ∈ ({a, b} : Finset I),
          (mSet τ D i h_nonempty).Nonempty ∧ isMaximalInMSet τ D i h_nonempty x := by
        apply (sublemma_3_2 τ D x h_door h_nonempty hx_not_mem a b ha_mem hb_mem hab
            h_eq_mini).mp h_dom
      obtain ⟨i, hi_mem, hi_nonempty, hi_max⟩ := h_exists_max
      cases Finset.mem_insert.mp hi_mem with
      | inl hi_eq_a =>
        subst hi_eq_a
        rw [h_Ma_empty] at hi_nonempty
        exact False.elim (Set.not_nonempty_empty hi_nonempty)
      | inr hi_eq_b =>
        have : i = b := Finset.mem_singleton.mp hi_eq_b; subst this
        have h_x_eq_mb : x = m_b := maximal_element_unique τ D i h_nonempty hi_nonempty x hi_max
        left; exact ⟨h_x_eq_mb ▸ rfl, rfl⟩
     | odoor h0 _ j hj_not_mem hj_eq hc_eq =>
       subst hj_eq
       have h_card_eq : C.card = τ.card := h_room.2
       have h_card_D : D.card = τ.card + 1 := h_door.2
       have h_card_insert : (insert j C).card = C.card + 1 := Finset.card_insert_of_notMem
           hj_not_mem
       rw [hc_eq] at h_card_D
       rw [h_card_insert] at h_card_D
       rw [h_card_eq] at h_card_D
       have hj_in_ab : j ∈ ({a, b} : Finset I) :=
         odoor_index_in_pair τ D C a b j h_door h_nonempty ha_mem hb_mem hab h_eq_mini h0
             h_card_eq hj_not_mem hc_eq
       cases Finset.mem_insert.mp hj_in_ab with
       | inl hj_eq_a =>
         have hj_eq_a : j = a := hj_eq_a
         subst hj_eq_a
         right
         exact ⟨rfl, (hc_eq ▸ (Finset.erase_insert hj_not_mem).symm)⟩
       | inr hj_eq_b =>
         exfalso
         have h_dom_C : IST.isDominant τ C := h_room.1
         rw [show C = D.erase j by rw[hc_eq]; exact (Finset.erase_insert hj_not_mem).symm]
             at h_dom_C
         have hj_eq_b : j = b := Finset.mem_singleton.mp hj_eq_b
         subst hj_eq_b
         have h_contra := (sublemma_3_1 τ D h_door h_nonempty j hb_mem).mp h_dom_C
         obtain ⟨_, _, _, _, _, _, _, h_M_empty⟩ := h_contra
         exact (Set.not_nonempty_iff_eq_empty.mpr h_M_empty) h_Mb_nonempty

omit [Inhabited T] in
/-- Two-rooms conclusion when the first `mSet` is nonempty but the second is empty. -/
theorem internalDoorTwoRoomsRightEmpty [Finite T] (τ : Finset T) (D : Finset I)
    (h_door : IST.isDoor τ D) (h_nonempty : τ.Nonempty) (a b : I)
    (ha_mem : a ∈ D) (hb_mem : b ∈ D) (h_eq_mini : mini h_nonempty a = mini h_nonempty b)
    (hab : a ≠ b) (h_card : D.card = τ.card + 1)
    (h_Ma_nonempty : (mSet τ D a h_nonempty).Nonempty)
    (h_Mb_nonempty : ¬ (mSet τ D b h_nonempty).Nonempty) :
    ∃ (σ₁ σ₂ : Finset T) (C₁ C₂ : Finset I),
      (σ₁, C₁) ≠ (σ₂, C₂) ∧
      IST.isRoom σ₁ C₁ ∧
      IST.isRoom σ₂ C₂ ∧
      isDoorof τ D σ₁ C₁ ∧
      isDoorof τ D σ₂ C₂ ∧
      (∀ σ C, IST.isRoom σ C → isDoorof τ D σ C →
       (σ = σ₁ ∧ C = C₁) ∨ (σ = σ₂ ∧ C = C₂)) := by
  have : Fintype T := Fintype.ofFinite T
  let m_a := mElement τ D a h_nonempty h_Ma_nonempty
  have h_ma_max : isMaximalInMSet τ D a h_nonempty m_a :=
    m_element_is_maximal τ D a h_nonempty h_Ma_nonempty
  have h_ma_not_mem : m_a ∉ τ :=
    m_element_not_in_tau τ D a a b h_door h_nonempty ha_mem hb_mem hab h_eq_mini h_Ma_nonempty
        (Or.inl rfl)
  have h_Mb_empty : mSet τ D b h_nonempty = ∅ := Set.not_nonempty_iff_eq_empty.mp h_Mb_nonempty
  use insert m_a τ, τ, D, D.erase b
  constructor
  · intro h_pair_eq
    have h_eq : insert m_a τ = τ := congr_arg Prod.fst h_pair_eq
    have h_ma_in : m_a ∈ insert m_a τ := Finset.mem_insert_self m_a τ
    rw [h_eq] at h_ma_in
    exact h_ma_not_mem h_ma_in
  constructor
  · constructor
    · apply (sublemma_3_2 τ D m_a h_door h_nonempty h_ma_not_mem a b ha_mem hb_mem hab
        h_eq_mini).mpr
      use a, by simp
    · rw [Finset.card_insert_of_notMem h_ma_not_mem, h_card]
  constructor
  · constructor
    · apply (sublemma_3_1 τ D h_door h_nonempty b hb_mem).mpr
      use a, b, ha_mem, hb_mem, hab, h_eq_mini, (Or.inr rfl), h_Mb_empty
    · rw [Finset.card_erase_of_mem hb_mem, h_card]
      simp
  constructor
  · apply isDoorof.idoor
    · apply (sublemma_3_2 τ D m_a h_door h_nonempty h_ma_not_mem a b ha_mem hb_mem hab
        h_eq_mini).mpr
      use a, by simp
    · exact h_door
    · exact h_ma_not_mem
    · rfl
    · rfl
  constructor
  · apply isDoorof.odoor
    · apply (sublemma_3_1 τ D h_door h_nonempty b hb_mem).mpr
      use a, b, ha_mem, hb_mem, hab, h_eq_mini, (Or.inr rfl), h_Mb_empty
    · exact h_door
    · exact Finset.notMem_erase b D
    · rfl
    · exact (Finset.insert_erase hb_mem).symm
  · intros σ C h_room h_door_rel
    cases h_door_rel with
    | idoor h0 _ x hx_not_mem hx_eq hc_eq =>
      subst hx_eq hc_eq
      have h_dom : IST.isDominant (insert x τ) D := h0
      have h_exists_max : ∃ i ∈ ({a, b} : Finset I),
          (mSet τ D i h_nonempty).Nonempty ∧ isMaximalInMSet τ D i h_nonempty x := by
        apply (sublemma_3_2 τ D x h_door h_nonempty hx_not_mem a b ha_mem hb_mem hab
            h_eq_mini).mp h_dom
      obtain ⟨i, hi_mem, hi_nonempty, hi_max⟩ := h_exists_max
      cases Finset.mem_insert.mp hi_mem with
      | inl hi_eq_a =>
        subst hi_eq_a
        have h_x_eq_ma : x = m_a := maximal_element_unique τ D i h_nonempty hi_nonempty x hi_max
        left; exact ⟨h_x_eq_ma ▸ rfl, rfl⟩
      | inr hi_eq_b =>
        have : i = b := Finset.mem_singleton.mp hi_eq_b; subst this
        rw [h_Mb_empty] at hi_nonempty
        exact False.elim (Set.not_nonempty_empty hi_nonempty)
     | odoor h0 _ j hj_not_mem hj_eq hc_eq =>
       subst hj_eq
       have h_card_eq : C.card = τ.card := h_room.2
       have h_card_D : D.card = τ.card + 1 := h_door.2
       have h_card_insert : (insert j C).card = C.card + 1 := Finset.card_insert_of_notMem
           hj_not_mem
       rw [hc_eq, h_card_insert, h_card_eq] at h_card_D
       have hj_in_ab : j ∈ ({a, b} : Finset I) :=
         odoor_index_in_pair τ D C a b j h_door h_nonempty ha_mem hb_mem hab h_eq_mini h0
             h_card_eq hj_not_mem hc_eq
       cases Finset.mem_insert.mp hj_in_ab with
       | inl hj_eq_a =>
         subst hj_eq_a
         exfalso
         have h_dom_C : IST.isDominant τ C := h_room.1
         rw [show C = D.erase j by rw [hc_eq]; exact (Finset.erase_insert hj_not_mem).symm]
             at h_dom_C
         have h_contra := (sublemma_3_1 τ D h_door h_nonempty j ha_mem).mp h_dom_C
         obtain ⟨_, _, _, _, _, _, _, h_M_empty⟩ := h_contra
         exact (Set.not_nonempty_iff_eq_empty.mpr h_M_empty) h_Ma_nonempty
       | inr hj_eq_b =>
         have hj_eq_b : j = b := Finset.mem_singleton.mp hj_eq_b
         subst hj_eq_b
         right
         exact ⟨rfl, (hc_eq ▸ (Finset.erase_insert hj_not_mem).symm)⟩

/- Lemma 3-/
omit [Inhabited T] in
theorem internal_door_two_rooms [Finite T] (τ : Finset T) (D : Finset I)
    (h_int_door : IST.isInternalDoor τ D) :
    ∃ (σ₁ σ₂ : Finset T) (C₁ C₂ : Finset I),
      (σ₁, C₁) ≠ (σ₂, C₂) ∧
      IST.isRoom σ₁ C₁ ∧
      IST.isRoom σ₂ C₂ ∧
      isDoorof τ D σ₁ C₁ ∧
      isDoorof τ D σ₂ C₂ ∧
      (∀ σ C, IST.isRoom σ C → isDoorof τ D σ C →
       (σ = σ₁ ∧ C = C₁) ∨ (σ = σ₂ ∧ C = C₂)) := by
  have : Fintype T := Fintype.ofFinite T
  obtain ⟨h_door, h_nonempty⟩ := h_int_door
  have h_card : D.card = τ.card + 1 := h_door.2
  have h_image_card : D.card = (D.image (mini h_nonempty)).card + 1 := by
    have h_dominant : IST.isDominant τ D := h_door.1
    have h_image_eq : D.image (mini h_nonempty) = τ := by
      convert (keylemma_of_dominant h_dominant h_nonempty).symm
    rw [h_card, h_image_eq]
  obtain ⟨a, b, ha_mem, hb_mem, h_eq_mini, hab, _⟩ := injOn_sdiff D (mini h_nonempty) h_image_card
  have h_disjoint : mSet τ D a h_nonempty ∩ mSet τ D b h_nonempty = ∅ :=
    M_sets_disjoint τ D a b h_nonempty h_door ha_mem hb_mem hab h_eq_mini
  by_cases h_Ma_nonempty : (mSet τ D a h_nonempty).Nonempty
  · by_cases h_Mb_nonempty : (mSet τ D b h_nonempty).Nonempty
    · exact internalDoorTwoRoomsBothNonempty τ D h_door h_nonempty a b ha_mem hb_mem
        h_eq_mini hab h_card h_disjoint h_Ma_nonempty h_Mb_nonempty
    · exact internalDoorTwoRoomsRightEmpty τ D h_door h_nonempty a b ha_mem hb_mem
        h_eq_mini hab h_card h_Ma_nonempty h_Mb_nonempty
  · have h_Ma_empty : mSet τ D a h_nonempty = ∅ := Set.not_nonempty_iff_eq_empty.mp h_Ma_nonempty
    by_cases h_Mb_nonempty : (mSet τ D b h_nonempty).Nonempty
    · exact internalDoorTwoRoomsLeftEmpty τ D h_door h_nonempty a b ha_mem hb_mem
        h_eq_mini hab h_card h_disjoint h_Ma_empty h_Mb_nonempty
    · have h_Mb_empty : mSet τ D b h_nonempty = ∅ := Set.not_nonempty_iff_eq_empty.mp h_Mb_nonempty
      use τ, τ, D.erase b, D.erase a
      constructor
      · intro h_pair_eq
        have h_erasure_eq : D.erase b = D.erase a := congr_arg Prod.snd h_pair_eq
        have h_a_in_erase_b : a ∈ D.erase b := Finset.mem_erase.mpr ⟨hab, ha_mem⟩
        rw [h_erasure_eq] at h_a_in_erase_b
        exact (Finset.notMem_erase a D) h_a_in_erase_b
      constructor
      · constructor
        · apply (sublemma_3_1 τ D h_door h_nonempty b hb_mem).mpr
          use a, b, ha_mem, hb_mem, hab, h_eq_mini, (Or.inr rfl), h_Mb_empty
        · rw [Finset.card_erase_of_mem hb_mem, h_door.2]
          simp
      constructor
      · constructor
        · apply (sublemma_3_1 τ D h_door h_nonempty a ha_mem).mpr
          use a, b, ha_mem, hb_mem, hab, h_eq_mini, (Or.inl rfl), h_Ma_empty
        · rw [Finset.card_erase_of_mem ha_mem, h_door.2]
          simp
      constructor
      · apply isDoorof.odoor
        · apply (sublemma_3_1 τ D h_door h_nonempty b hb_mem).mpr
          use a, b, ha_mem, hb_mem, hab, h_eq_mini, (Or.inr rfl), h_Mb_empty
        · exact h_door
        · exact Finset.notMem_erase b D
        · rfl
        · exact (Finset.insert_erase hb_mem).symm
      constructor
      · apply isDoorof.odoor
        · apply (sublemma_3_1 τ D h_door h_nonempty a ha_mem).mpr
          use a, b, ha_mem, hb_mem, hab, h_eq_mini, (Or.inl rfl), h_Ma_empty
        · exact h_door
        · exact Finset.notMem_erase a D
        · rfl
        · exact (Finset.insert_erase ha_mem).symm
      · intros σ C h_room h_door_rel
        cases h_door_rel with
        | idoor h0 _ x hx_not_mem hx_eq hc_eq =>
          subst hx_eq hc_eq
          have h_dom : IST.isDominant (insert x τ) D := h0
          have h_exists_max : ∃ i ∈ ({a, b} : Finset I),
              (mSet τ D i h_nonempty).Nonempty ∧ isMaximalInMSet τ D i h_nonempty x := by
            apply (sublemma_3_2 τ D x h_door h_nonempty hx_not_mem a b ha_mem hb_mem hab
                h_eq_mini).mp h_dom
          obtain ⟨i, hi_mem, hi_nonempty, _⟩ := h_exists_max
          cases Finset.mem_insert.mp hi_mem with
          | inl hi_eq_a =>
            subst hi_eq_a; rw [h_Ma_empty] at hi_nonempty
            exact absurd hi_nonempty Set.not_nonempty_empty
          | inr hi_eq_b =>
            have : i = b := Finset.mem_singleton.mp hi_eq_b; subst this
            rw [h_Mb_empty] at hi_nonempty
            exact absurd hi_nonempty Set.not_nonempty_empty
        | odoor h0 _ j hj_not_mem hj_eq hc_eq =>
          subst hj_eq
          have h_dom_C : IST.isDominant τ C := h0
          have h_card_eq : C.card = τ.card := h_room.2
          have h_card_D : D.card = τ.card + 1 := h_door.2
          have h_card_insert : (insert j C).card = C.card + 1 := Finset.card_insert_of_notMem
              hj_not_mem
          rw [hc_eq] at h_card_D
          rw [h_card_insert] at h_card_D
          rw [h_card_eq] at h_card_D
          have hj_in_ab : j ∈ ({a, b} : Finset I) :=
            odoor_index_in_pair τ D C a b j h_door h_nonempty ha_mem hb_mem hab h_eq_mini h_dom_C
                h_card_eq hj_not_mem hc_eq
          cases Finset.mem_insert.mp hj_in_ab with
          | inl hj_eq_a =>
            have hj_eq_a : j = a := hj_eq_a
            subst hj_eq_a
            have h_C_eq_erase : C = D.erase j := by
              rw [hc_eq]
              exact (Finset.erase_insert hj_not_mem).symm
            right
            exact ⟨rfl, h_C_eq_erase⟩
          | inr hj_eq_b =>
            have hj_eq_b : j = b := Finset.mem_singleton.mp hj_eq_b
            subst hj_eq_b
            have h_C_eq_erase : C = D.erase j := by
              rw [hc_eq]
              exact (Finset.erase_insert hj_not_mem).symm
            left
            exact ⟨rfl, h_C_eq_erase⟩

end KeyLemma


noncomputable section Scarf

attribute [local instance] Classical.propDecidable


--variable [IST : IndexedLOrder I T]

variable (c : T → I) (σ : Finset T) (C : Finset I)

/-- A colorful cell: the image of the coloring on `σ` equals `C`. -/
def isColorful : Prop := IST.isCell σ C ∧ σ.image c   = C

/-- A nearly colorful cell: exactly one color of `C` is missing. -/
def isNearlyColorful : Prop := IST.isCell σ C ∧ (C \ σ.image c).card = 1

/-- A nearly colorful cell whose missing color is exactly `i`. -/
def isTypedNC (i : I) (σ : Finset T) (C : Finset I) : Prop := IST.isCell σ C ∧ (C \ (σ.image c))
    = {i}


variable {c σ C}


omit [Inhabited T] [DecidableEq T] in
lemma not_colorful_of_TypedNC (h1 : isTypedNC c i σ C) : ¬ IST.isColorful c σ C := by
  intro h
  unfold isTypedNC at h1
  unfold isColorful at h
  have h_diff := h1.2
  have h_ne : σ.image c ≠ C := by
    intro h_eq
    rw [←h_eq, Finset.sdiff_self] at h_diff
    have h_singleton_nonempty : ({i} : Finset I).Nonempty := Finset.singleton_nonempty i
    rw [←h_diff] at h_singleton_nonempty
    exact Finset.not_nonempty_empty h_singleton_nonempty
  exact h_ne h.2

omit [Inhabited T] [DecidableEq T] in
lemma NC_of_TNC (h1 : isTypedNC c i σ C) : isNearlyColorful c σ C := by
  have hcell := h1.1
  have heq := h1.2
  constructor
  · exact hcell
  · rw [heq]
    have h_eq : C \ image c σ = {i} := by
      rw [heq]
    rw [←heq, h_eq]
    exact Finset.card_singleton i


--Useless lemma, remain sorry first.
/-section useless_lemma
lemma door_of_Croom (h1 : isColorful c σ C) (h2 : isDoorof τ D σ C)
    : isNearlyColorful c τ D := by sorry

lemma unique_type_door_of_Croom (h1 : isColorful c σ C) (i :I) :
∃! x : Finset T × Finset I , isDoorof x.1 x.2 σ C ∧ isTypedNC c i σ C:= by sorry

lemma type_aux (h : isNearlyColorful c σ C) : ∃! i : I, i ∉ σ.image c ∧ C = insert i (σ.image c)
    := by
  sorry

def NCtype (h : isNearlyColorful c σ C) : I :=
  Classical.choose (type_aux h).exists

structure TypedNC (i : I) (σ : Finset T) (C : Finset I): Prop where
  nc : isNearlyColorful c σ C
  t : NCtype nc = i
end useless_lemma-/

lemma Finset.eq_of_mem_of_card_one {α : Type*} {s : Finset α} {a : α}
    (h_mem : a ∈ s) (h_card : s.card = 1) : s = {a} :=
  Finset.eq_singleton_iff_unique_mem.mpr ⟨h_mem, fun y hy =>
    let ⟨b, hb⟩ := Finset.card_eq_one.mp h_card
    have h_a_eq_b : a = b := Finset.eq_of_mem_singleton (hb ▸ h_mem)
    have h_y_eq_b : y = b := Finset.eq_of_mem_singleton (hb ▸ hy)
    h_y_eq_b.trans h_a_eq_b.symm⟩

omit [Inhabited T] [DecidableEq T] in
lemma room_of_colorful (h : IST.isColorful c σ C) : IST.isRoom σ C := by
  unfold isRoom
  unfold isColorful at h
  constructor
  · exact h.1
  · have h1 : C.card = (σ.image c).card := by rw [h.2]
    have h2 : (σ.image c).card ≤ σ.card := Finset.card_image_le
    have h3 : σ.card ≤ C.card := card_le_of_domiant h.1
    linarith



/-- A chosen point of the goods set of a colorful room. -/
def pickColorfulPoint (h : IST.isColorful c σ C)
    : σ := Classical.choice (sigma_nonempty_of_room (room_of_colorful h)).to_subtype


-- Easy
/- Lemma 4 -/
omit [Inhabited T] [DecidableEq T] in
lemma NC_of_outsidedoor (h : isOutsideDoor σ C) : isNearlyColorful c σ C  := by
  cases h with
  | intro hd he =>
    unfold isNearlyColorful
    unfold isCell
    constructor
    · exact hd.1
    · rw [he]
      have h_img : Finset.image c Finset.empty = Finset.empty := Finset.image_empty c
      rw [h_img]
      have h_disj : Disjoint C Finset.empty := Finset.disjoint_empty_right C
      have h_sdiff : C \ Finset.empty = C := Finset.sdiff_eq_self_of_disjoint h_disj
      rw [h_sdiff]
      unfold isDoor at hd
      have h1 := hd.2
      rw [he] at h1
      exact h1

/-variable {c σ C} in
lemma type_unique_of_outsidedoor (h : isOutsideDoor σ C) : ∃! i,
    i = isNCtype (NC_of_outsidedoor (c:=c) h)  := sorry-/
/-Lemma 5-/
omit [Inhabited T] in
lemma NC_or_C_of_door (h1 : isTypedNC c i τ D) (h2 : isDoorof τ D σ C)
    : isTypedNC c i σ C ∨ isColorful c σ C := by
  unfold isTypedNC at h1 ⊢
  unfold isColorful
  have h1_cell := h1.left
  have h1_eq := h1.right
  have h_sigma_cell : isCell σ C := by
    cases h2 with
    | idoor h0 _ _ _ _ _ => exact h0
    | odoor h0 _ _ _ _ _ => exact h0
  have step1_subset : C \ (σ.image c) ⊆ D \ (τ.image c) := by
    intro y hy
    simp only [Finset.mem_sdiff] at hy ⊢
    obtain ⟨y_in_C, y_notin_img_sigma⟩ := hy
    constructor
    · cases h2
      · rename_i h_D_eq; rw [h_D_eq]; exact y_in_C
      · rename_i h_D_eq; rw [h_D_eq]; exact Finset.mem_insert_of_mem y_in_C
    · cases h2 with
      | idoor h0 hdoor x h_x_notin h_sigma_eq h_D_eq =>
        rw [← h_sigma_eq, Finset.image_insert] at y_notin_img_sigma
        simp only [Finset.mem_insert, not_or] at y_notin_img_sigma
        exact y_notin_img_sigma.2
      | odoor h0 hdoor j h_j_notin h_sigma_eq h_D_eq =>
        rw [← h_sigma_eq] at y_notin_img_sigma
        exact y_notin_img_sigma
  have step2_D_card : (D \ (τ.image c)).card = 1 := by
    have D_sdiff_eq_i : D \ (τ.image c) = {i} := by
      rw [h1_eq]
    rw [D_sdiff_eq_i, Finset.card_singleton]
  have step3_C_card_le : (C \ σ.image c).card ≤ 1 := by
    rw [← step2_D_card]
    exact Finset.card_le_card step1_subset
  by_cases h : (C \ σ.image c).card = 0
  · right
    constructor
    · exact h_sigma_cell
    · have h_C_subset_img : C ⊆ σ.image c := by
        rw [Finset.subset_iff]
        intro x hx
        by_contra hxn
        have : x ∈ C \ σ.image c := by simp [hx, hxn]
        have : (C \ σ.image c).Nonempty := ⟨x, this⟩
        have : 0 < (C \ σ.image c).card := Finset.card_pos.2 this
        linarith [h]
      have h_room: isRoom σ C := isRoom_of_Door h2
      have h_card_eq : C.card = σ.card := h_room.2
      have h_img_le_C_card : (σ.image c).card ≤ C.card := by
        calc (σ.image c).card
          ≤ σ.card := Finset.card_image_le
          _ = C.card := h_card_eq.symm
      exact (Finset.eq_of_subset_of_card_le h_C_subset_img h_img_le_C_card).symm
  · left
    constructor
    · exact h_sigma_cell
    · have h_card_one : (C \ σ.image c).card = 1 := by omega
      have h_subset_singleton : C \ σ.image c ⊆ {i} := by
        have D_sdiff_eq_i : D \ (τ.image c) = {i} := by
          rw [h1_eq]
        rw [← D_sdiff_eq_i]
        exact step1_subset
      have C_sdiff_eq_i : C \ σ.image c = {i} :=
        Finset.eq_of_subset_of_card_le h_subset_singleton (by rw [h_card_one,
            Finset.card_singleton])
      have h_i_notin_img : i ∉ σ.image c := by
        have h_i_in_sdiff : i ∈ C \ σ.image c := by rw [C_sdiff_eq_i]; simp
        exact (Finset.mem_sdiff.mp h_i_in_sdiff).2
      exact C_sdiff_eq_i

omit [Inhabited T] in
lemma NCtype_of_door (h1 : isTypedNC c i τ D) (_ : isDoorof τ D σ C) (_ : isTypedNC c i σ C)
    : isTypedNC c i τ D := h1

omit [Inhabited T] in
lemma isTypedNC_of_isNearlyColorful_of_isDoorof_isTypedNC (h_nc : isNearlyColorful c τ D)
    (h_door : isDoorof τ D σ C) (h_room_typed : isTypedNC c i σ C) : isTypedNC c i τ D := by
  constructor
  · exact h_nc.1
  · have h_subset : C \ image c σ ⊆ D \ image c τ := by
      intro y hy
      simp only [Finset.mem_sdiff] at hy ⊢
      obtain ⟨y_in_C, y_notin_img_sigma⟩ := hy
      constructor
      · cases h_door with
        | idoor h0 _ _ _ _ h_D_eq => rw [h_D_eq]; exact y_in_C
        | odoor h0 _ _ _ _ h_D_eq => rw [h_D_eq]; exact Finset.mem_insert_of_mem y_in_C
      · cases h_door with
        | idoor h0 _ x _ h_sigma_eq _ =>
          rw [← h_sigma_eq, Finset.image_insert] at y_notin_img_sigma
          simp only [Finset.mem_insert, not_or] at y_notin_img_sigma
          exact y_notin_img_sigma.2
        | odoor h0 _ _ _ h_sigma_eq _ =>
          rw [← h_sigma_eq] at y_notin_img_sigma
          exact y_notin_img_sigma
    have h_i_in_diff : i ∈ D \ image c τ := h_subset (h_room_typed.2 ▸ Finset.mem_singleton_self i)
    have h_card_one : (D \ image c τ).card = 1 := h_nc.2
    exact Finset.eq_of_mem_of_card_one h_i_in_diff h_card_one

/- Lemma 6 -/
omit [Inhabited T] [DecidableEq T] in
lemma card_of_NCcell (h : isNearlyColorful c σ D) : #σ = #(image c σ)  ∨  #σ = #(image c σ)
    + 1 := by
  unfold isNearlyColorful at h
  rcases h with ⟨h_cell, h_nc_card⟩
  let img := image c σ
  have h_card_le_D : σ.card ≤ D.card := card_le_of_domiant h_cell
  have h_D_card_eq := (Finset.card_sdiff_add_card_inter D img).symm
  rw [h_nc_card] at h_D_card_eq
  have h_inter_le_img : (D ∩ img).card ≤ img.card := card_le_card (Finset.inter_subset_right)
  have h_D_le : D.card ≤ 1 + img.card := by
    linarith [h_D_card_eq, h_inter_le_img]
  have h_img_le_sigma : img.card ≤ σ.card := card_image_le
  have h_sigma_le_plus_one : σ.card ≤ img.card + 1 := by
    linarith [h_card_le_D, h_D_le]
  have h_or : σ.card ≤ img.card ∨ σ.card = img.card + 1 := by
    apply Nat.le_or_eq_of_le_succ
    exact h_sigma_le_plus_one
  cases h_or with
  | inl h_le =>
    left
    exact le_antisymm h_le h_img_le_sigma
  | inr h_eq =>
    right
    exact h_eq

omit [Inhabited T] [DecidableEq T] in
lemma image_subset_of_NCdoor (h1 : isNearlyColorful c σ C) (h2 : isDoor σ C) : image c σ ⊆ C := by
  unfold isNearlyColorful at h1
  unfold isDoor at h2
  rcases h1 with ⟨h_cell, h_nc_card⟩
  rcases h2 with ⟨_, h_door_card⟩
  let img := image c σ
  have h_img_le_sigma : img.card ≤ σ.card := card_image_le
  have h_sigma_le_C : σ.card ≤ C.card := card_le_of_domiant h_cell
  have h_inter_card : (C ∩ img).card = σ.card := by
    have h_C_card_eq := (Finset.card_sdiff_add_card_inter C img).symm
    rw [h_nc_card] at h_C_card_eq
    have h_C_eq : C.card = 1 + (C ∩ img).card := by linarith [h_C_card_eq]
    rw [h_door_card] at h_C_eq
    linarith [h_C_eq]
  have h_img_eq_inter : img.card = (C ∩ img).card := by
    have h_le1 : (C ∩ img).card ≤ img.card := card_le_card (Finset.inter_subset_right)
    have h_le2 : img.card ≤ (C ∩ img).card := by
      calc img.card
        ≤ σ.card := h_img_le_sigma
        _ = (C ∩ img).card := h_inter_card.symm
    exact le_antisymm h_le2 h_le1
  have h_inter_eq_img : C ∩ img = img :=
    Finset.eq_of_subset_of_card_le (Finset.inter_subset_right) (by rw [h_img_eq_inter])
  rwa [Finset.inter_eq_right] at h_inter_eq_img

section ImageErase

variable {T I : Type*} [DecidableEq T] [DecidableEq I]

lemma image_erase_eq_erase_image_of_unique
  (σ : Finset T) (c : T → I) {z : T}
  (_ : z ∈ σ)
  (uniq : ∀ ⦃w⦄, w ∈ σ → c w = c z → w = z) :
  (σ.erase z).image c = (σ.image c).erase (c z) := by
  ext i
  constructor
  · intro hi
    rcases Finset.mem_image.mp hi with ⟨w, hw_in_erase, rfl⟩
    rcases Finset.mem_erase.mp hw_in_erase with ⟨hw_ne_z, hw_in_σ⟩
    have h_ne_color : c w ≠ c z := by
      intro h_eq
      have := uniq hw_in_σ h_eq
      exact hw_ne_z this
    exact Finset.mem_erase.mpr ⟨h_ne_color, Finset.mem_image.mpr ⟨w, hw_in_σ, rfl⟩⟩
  · intro hi
    rcases Finset.mem_erase.mp hi with ⟨h_i_ne, hi_img⟩
    rcases Finset.mem_image.mp hi_img with ⟨w, hw_in_σ, rfl⟩
    have hw_ne_z : w ≠ z := by
      intro h_eq
      apply h_i_ne
      simp [h_eq]
    exact Finset.mem_image.mpr ⟨w, Finset.mem_erase.mpr ⟨hw_ne_z, hw_in_σ⟩, rfl⟩

end ImageErase
variable (c σ C) in
/-- The set of nearly colorful doors of a given room. -/
abbrev NCdoors := {(τ,D) | isNearlyColorful c τ D ∧ isDoorof τ D σ C }


omit [DecidableEq T] [Inhabited T] IST in
lemma three_collision_card_bound (σ : Finset T) (c : T → I)
    (a b z : T) (ha_in_σ : a ∈ σ) (hb_in_σ : b ∈ σ) (hz_in_σ : z ∈ σ)
    (hab_ne : a ≠ b) (haz_ne : a ≠ z) (hbz_ne : b ≠ z)
    (hc_eq : c a = c b) (hcz_eq : c b = c z) :
    σ.card ≥ (σ.image c).card + 2 := by
  classical
  let σ_rest := σ \ {a, b, z}
  have h_three_subset_sigma : {a, b, z} ⊆ σ := by
    intro w hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with (rfl | rfl | rfl);
    · exact ha_in_σ
    · exact hb_in_σ
    · exact hz_in_σ
  have h_partition : σ = {a, b, z} ∪ σ_rest :=
    (Finset.union_sdiff_of_subset h_three_subset_sigma).symm
  have h_disjoint : Disjoint ({a, b, z} : Finset T) σ_rest :=
    Finset.disjoint_sdiff
  have h_card_partition : σ.card = ({a, b, z} : Finset T).card + σ_rest.card := by
    rw [h_partition, Finset.card_union_of_disjoint h_disjoint]
  have h_triple_card : ({a, b, z} : Finset T).card = 3 := by
    rw [Finset.card_eq_three]
    exact ⟨a, b, z, hab_ne, haz_ne, hbz_ne, rfl⟩
  have h_image_bound : (σ.image c).card ≤ σ_rest.card + 1 := by
    have h_image_union : σ.image c = insert (c a) (σ_rest.image c) := by
      ext i; simp only [Finset.mem_image, Finset.mem_insert]
      constructor
      · rintro ⟨t, ht_in_σ, rfl⟩
        by_cases h_t_abz : t ∈ ({a, b, z} : Finset T)
        · simp only [mem_insert, mem_singleton] at h_t_abz; rcases h_t_abz with (rfl | rfl | rfl)
          · left; rfl
          · left; exact hc_eq.symm
          · left; exact (hc_eq.trans hcz_eq).symm
        · right; use t; simp [σ_rest, ht_in_σ, h_t_abz]
      · rintro (rfl | ⟨t, ht_in_rest, rfl⟩)
        · use a
        · use t; exact ⟨(Finset.mem_sdiff.mp ht_in_rest).1, rfl⟩
    rw [h_image_union]
    linarith [Finset.card_insert_le (c a) (σ_rest.image c), Finset.card_image_le (f := c)
        (s := σ_rest)]
  calc σ.card
      = 3 + σ_rest.card           := by rw [h_card_partition, h_triple_card]
    _ = σ_rest.card + 3           := by ring
    _ = (σ_rest.card + 1) + 2     := by ring
    _ ≥ (σ.image c).card + 2      := by omega


omit [DecidableEq T] [Inhabited T] IST in
lemma image_erase_collision_preserves [DecidableEq T] (σ : Finset T) (c : T → I)
    (x y : T) (hx_in_σ : x ∈ σ) (hy_in_σ : y ∈ σ) (hxy_ne : x ≠ y) (hcxy_eq : c x = c y) :
    (σ.erase x).image c = σ.image c ∧ (σ.erase y).image c = σ.image c := by
  constructor
  · ext z
    simp only [Finset.mem_image]
    constructor
    · intro ⟨w, hw_in_erased, hw_eq⟩
      have hw_in_σ : w ∈ σ := by
        rw [Finset.mem_erase] at hw_in_erased
        exact hw_in_erased.2
      exact ⟨w, hw_in_σ, hw_eq⟩
    · intro ⟨w, hw_in_σ, hw_eq⟩
      by_cases h : w = x
      · subst h
        use y
        constructor
        · rw [Finset.mem_erase]
          exact ⟨hxy_ne.symm, hy_in_σ⟩
        · rw [←hcxy_eq, hw_eq]
      · use w
        exact ⟨Finset.mem_erase.mpr ⟨h, hw_in_σ⟩, hw_eq⟩
  · ext z
    simp only [Finset.mem_image]
    constructor
    · intro ⟨w, hw_in_erased, hw_eq⟩
      have hw_in_σ : w ∈ σ := by
        rw [Finset.mem_erase] at hw_in_erased
        exact hw_in_erased.2
      exact ⟨w, hw_in_σ, hw_eq⟩
    · intro ⟨w, hw_in_σ, hw_eq⟩
      by_cases h : w = y
      · subst h
        use x
        constructor
        · rw [Finset.mem_erase]
          exact ⟨hxy_ne, hx_in_σ⟩
        · rw [hcxy_eq, hw_eq]
      · use w
        exact ⟨Finset.mem_erase.mpr ⟨h, hw_in_σ⟩, hw_eq⟩


omit [DecidableEq T] [Inhabited T] in
lemma collision_door_valid [DecidableEq T] (σ : Finset T) (C : Finset I) (_ : T → I)
    (x : T) (h_cell : isCell σ C) (hx_in_σ : x ∈ σ) (h_card_eq : C.card = σ.card) :
    isDoorof (σ.erase x) C σ C := by
  apply isDoorof.idoor h_cell
  · constructor
    · exact Dominant_of_subset σ (σ.erase x) C (Finset.erase_subset x σ) h_cell
    · rw [h_card_eq]
      rw [Finset.card_erase_of_mem hx_in_σ]
      exact (Nat.sub_add_cancel (Finset.card_pos.mpr ⟨x, hx_in_σ⟩)).symm
  · exact Finset.notMem_erase x σ
  · exact Finset.insert_erase hx_in_σ
  · rfl

-- Lemma 7
omit [DecidableEq T] [Inhabited T] in
/-- The two doors of a nearly colorful room, when the coloring is injective on `σ`. -/
lemma doorsOfNCroomInjective [DecidableEq T] (h_room : isRoom σ C)
    (h_nc : isNearlyColorful c σ C) (h_eq : #σ = #(image c σ)) :
    ∃ door1 door2, door1 ≠ door2 ∧ NCdoors c σ C = {door1, door2} := by
  have h_card_eq : C.card = σ.card := h_room.2
  have h_cell : isCell σ C := h_room.1
  let img := image c σ
  have h_inj_on_σ : Set.InjOn c ↑σ := (Finset.card_image_iff).mp h_eq.symm
  have h_img_C_card_1 : (img \ C).card = 1 := by
    have h_card_eq' : C.card = img.card := by linarith [h_card_eq, h_eq]
    have h_C_sdiff := Finset.card_sdiff_add_card_inter C img
    rw [h_nc.2, h_card_eq'] at h_C_sdiff
    have h_img_sdiff := Finset.card_sdiff_add_card_inter img C
    rw [Finset.inter_comm] at h_C_sdiff
    linarith [h_C_sdiff, h_img_sdiff]
  obtain ⟨c_y, h_img_C_eq⟩ := Finset.card_eq_one.mp h_img_C_card_1
  have h_c_y_in_img : c_y ∈ img := by
    have : c_y ∈ img \ C := by rw [h_img_C_eq]; simp
    exact (Finset.mem_sdiff.mp this).1
  have h_c_y_notin_C : c_y ∉ C := by
    have : c_y ∈ img \ C := by rw [h_img_C_eq]; simp
    exact (Finset.mem_sdiff.mp this).2
  obtain ⟨y, h_y_in_σ, h_c_y_eq⟩ := Finset.mem_image.mp h_c_y_in_img
  subst h_c_y_eq
  have h_y_unique : ∀ ⦃z⦄, z ∈ σ → c z = c y → z = y :=
    fun z hz hcz => h_inj_on_σ hz h_y_in_σ hcz
  let door1 := (σ.erase y, C)
  let door2 := (σ, insert (c y) C)
  use door1, door2
  constructor
  · intro h_eq_doors; simp only [Prod.ext_iff] at h_eq_doors;
    have this := h_eq_doors.1
    have : y ∉ σ := Finset.erase_eq_self.mp this
    exact this h_y_in_σ
  · ext ⟨τ, D⟩; constructor
    · intro h
      rcases h with ⟨h_nc_door, h_is_door⟩
      cases h_is_door with
      | idoor h0 h_door x hx_notin_τ h_insert_x h_D_eq_C =>
        subst h_D_eq_C
        have h_nc_card := h_nc_door.2
        have h_x_in_σ : x ∈ σ := by rw [←h_insert_x]; exact Finset.mem_insert_self x τ
        have h_τ_eq_erase : τ = σ.erase x := by rw [←Finset.erase_insert hx_notin_τ, h_insert_x]
        have h_x_unique : ∀ ⦃w⦄, w ∈ σ → c w = c x → w = x := by
          intro w hw hcw
          exact h_inj_on_σ hw h_x_in_σ hcw
        have h_img_erase : (τ.image c) = img.erase (c x) := by
          rw [h_τ_eq_erase]
          exact image_erase_eq_erase_image_of_unique σ c h_x_in_σ h_x_unique
        rw [h_img_erase] at h_nc_card
        by_cases h_x_eq_y : x = y
        · subst h_x_eq_y
          simp [h_τ_eq_erase, door1]
        · have h_cx_in_D : c x ∈ D := by
            by_contra h_cx_notin_C
            have h_cx_in_img_diff_D : c x ∈ img \ D := Finset.mem_sdiff.mpr
                ⟨Finset.mem_image_of_mem c h_x_in_σ, h_cx_notin_C⟩
            rw [h_img_C_eq, Finset.mem_singleton] at h_cx_in_img_diff_D
            have h_c_eq : c x = c y := by rw [h_cx_in_img_diff_D]
            have x_in_sigma : x ∈ σ := by
              have : x ∈ insert x τ := Finset.mem_insert_self x τ
              have : x ∈ σ := by
                rw [←h_insert_x]
                exact Finset.mem_insert_self x τ
              exact this
            have := h_y_unique x_in_sigma h_c_eq
            exact h_x_eq_y this
          exfalso
          have h_card_2 : (D \ (img.erase (c x))).card = 2 := by
            have h_eq : D \ (img.erase (c x)) = insert (c x) (D \ img) := by
              ext y
              simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
              constructor
              · intro ⟨hy_D, hy_not_erase⟩
                simp only [ne_eq, not_and] at hy_not_erase
                by_cases h : y = c x
                · left; exact h
                · right
                  exact ⟨hy_D, hy_not_erase h⟩
              · intro h
                cases h with
                | inl h_eq => exact ⟨h_eq ▸ h_cx_in_D, by simp [h_eq]⟩
                | inr h_in =>
                  exact ⟨h_in.1, by simp only [ne_eq, not_and]; intro h_neq; exact h_in.2⟩
            rw [h_eq, Finset.card_insert_of_notMem]
            · rw [h_nc.2]
            · intro h_mem
              have := (Finset.mem_sdiff.mp h_mem).2
              have h_img_mem : c x ∈ img := Finset.mem_image_of_mem c h_x_in_σ
              exact this h_img_mem
          rw [h_card_2] at h_nc_card; linarith
         | odoor h0 h_door j hj_notin_C h_τ_eq_σ h_D_eq_insert =>
          subst h_τ_eq_σ; subst h_D_eq_insert
          have h_nc_card := h_nc_door.2
          by_cases h_j_eq_cy : j = c y
          · subst h_j_eq_cy; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; right; rfl
          · exfalso
            have h_j_notin_img : j ∉ img := by
              intro h_j_in_img
              have h_j_in_img_diff_C : j ∈ img \ C := Finset.mem_sdiff.mpr ⟨h_j_in_img,
                  hj_notin_C⟩
              rw [h_img_C_eq, Finset.mem_singleton] at h_j_in_img_diff_C
              exact h_j_eq_cy h_j_in_img_diff_C
            have h_card_2 : ((insert j C) \ img).card = 2 := by
              have h_eq : (insert j C) \ img = (C \ img) ∪ {j} := by
                ext x
                simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_union,
                    Finset.mem_singleton]
                constructor
                · intro ⟨hx_in, hx_notin⟩
                  cases hx_in with
                  | inl hx_eq_j => right; exact hx_eq_j
                  | inr hx_in_C => left; exact ⟨hx_in_C, hx_notin⟩
                · intro h
                  cases h with
                  | inl h => exact ⟨Or.inr h.1, h.2⟩
                  | inr h => exact ⟨Or.inl h, by rw [h]; exact h_j_notin_img⟩
              rw [h_eq, Finset.card_union_of_disjoint]
              · rw [h_nc.2, Finset.card_singleton]
              · exact Finset.disjoint_singleton_right.mpr (fun h => hj_notin_C
                  (Finset.mem_sdiff.mp h).1)
            rw [h_card_2] at h_nc_card; linarith
    · intro h
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      rcases h with (h_eq1 | h_eq2)
      · have ⟨h_τ_eq, h_D_eq⟩ : τ = σ.erase y ∧ D = C := Prod.mk.inj h_eq1
        subst h_τ_eq h_D_eq
        constructor
        · unfold isNearlyColorful
          constructor
          · unfold isCell
            exact Dominant_of_subset _ _ D (Finset.erase_subset y σ) h_cell
          · rw [image_erase_eq_erase_image_of_unique σ c h_y_in_σ h_y_unique]
            have h_eq_diff : D \ (image c σ).erase (c y) = D \ image c σ := by
              ext z
              constructor
              · intro h
                simp only [Finset.mem_sdiff, Finset.mem_erase] at h ⊢
                exact ⟨h.1, fun h_in => h.2 ⟨fun h_eq => h_c_y_notin_C (h_eq ▸ h.1), h_in⟩⟩
              · intro h
                simp only [Finset.mem_sdiff, Finset.mem_erase] at h ⊢
                exact ⟨h.1, fun ⟨_, h_in⟩ => h.2 h_in⟩
            rw [h_eq_diff, h_nc.2]
        · apply isDoorof.idoor
          · exact h_cell
          · constructor
            · unfold isCell
              exact Dominant_of_subset _ _ D (Finset.erase_subset y σ) h_cell
            · rw [Finset.card_erase_of_mem h_y_in_σ, h_card_eq]
              exact (Nat.sub_add_cancel (Finset.card_pos.mpr ⟨y, h_y_in_σ⟩)).symm
          · exact Finset.notMem_erase y σ
          · exact Finset.insert_erase h_y_in_σ
          · rfl
      · have ⟨h_τ_eq, h_D_eq⟩ : τ = σ ∧ D = insert (c y) C := Prod.mk.inj h_eq2
        subst h_τ_eq h_D_eq
        constructor
        · unfold isNearlyColorful
          constructor
          · unfold isCell
            unfold isDominant
            intro z
            obtain ⟨i, hi_in_C, hi_dom⟩ := h_cell z
            use i, Finset.mem_insert_of_mem hi_in_C
          · have h_j_in_img : c y ∈ img := Finset.mem_image_of_mem c h_y_in_σ
            have h_sdiff_insert : (insert (c y) C) \ img = C \ img := by
              rw [Finset.insert_sdiff_of_mem _ h_j_in_img]
            rw [h_sdiff_insert, h_nc.2]
        · apply isDoorof.odoor
          · exact h_cell
          · constructor
            · apply Dominant_of_supset τ C (insert (c y) C)
              · exact Finset.subset_insert (c y) C
              · exact h_cell
            · rw [Finset.card_insert_of_notMem h_c_y_notin_C, h_card_eq]
          · exact h_c_y_notin_C
          · rfl
          · rfl

omit [DecidableEq T] [Inhabited T] IST in
/-- The unordered colliding pair equals `{x, y}` for a repeated coloring. -/
lemma pairEqOfCollision [DecidableEq T] {x y a b : T}
    (h_x_in_σ : x ∈ σ) (h_y_in_σ : y ∈ σ) (h_xy_ne : x ≠ y) (h_cxy_eq : c x = c y)
    (ha_in_σ : a ∈ σ) (hb_in_σ : b ∈ σ) (hc_eq : c a = c b) (hab_ne : a ≠ b)
    (h_inj_outside : Set.InjOn c ((σ : Set T) \ {a, b}))
    (h_inj : #σ = #(image c σ) + 1) :
    ({x, y} : Finset T) = {a, b} := by
  classical
  by_contra h_ne_pair
  by_cases h_disjoint : Disjoint ({x, y} : Finset T) {a, b}
  · have h_x_notin_ab : x ∉ {a, b} := Finset.disjoint_left.mp h_disjoint (by simp)
    have h_y_notin_ab : y ∉ {a, b} := Finset.disjoint_left.mp h_disjoint (by simp)
    have h_x_in_sdiff : x ∈ σ \ {a, b} := Finset.mem_sdiff.mpr ⟨h_x_in_σ, h_x_notin_ab⟩
    have h_y_in_sdiff : y ∈ σ \ {a, b} := Finset.mem_sdiff.mpr ⟨h_y_in_σ, h_y_notin_ab⟩
    have h_x_in_set : x ∈ (↑σ : Set T) \ {a, b} := by
      simp only [Set.mem_diff, SetLike.mem_coe, h_x_in_σ, Set.mem_insert_iff,
        Set.mem_singleton_iff, not_or, true_and]
      simp only [mem_insert, mem_singleton, not_or] at h_x_notin_ab
      exact h_x_notin_ab
    have h_y_in_set : y ∈ (↑σ : Set T) \ {a, b} := by
      simp only [Set.mem_diff, SetLike.mem_coe, h_y_in_σ, Set.mem_insert_iff,
        Set.mem_singleton_iff, not_or, true_and]
      simp only [mem_insert, mem_singleton, not_or] at h_y_notin_ab
      exact h_y_notin_ab
    have h_inj_xy := h_inj_outside h_x_in_set h_y_in_set h_cxy_eq
    exact h_xy_ne h_inj_xy
  · rw [Finset.not_disjoint_iff] at h_disjoint
    obtain ⟨u, hu_in_xy, hu_in_ab⟩ := h_disjoint
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu_in_xy hu_in_ab
    cases hu_in_xy with
    | inl h_u_eq_x =>
      rw [h_u_eq_x] at hu_in_ab
      cases hu_in_ab with
      | inl h_x_eq_a =>
        by_cases h_y_eq_b : y = b
        · rw [h_x_eq_a, h_y_eq_b] at h_ne_pair
          exact h_ne_pair rfl
        · have h_y_ne_a : y ≠ a := by
            rw [h_x_eq_a] at h_xy_ne
            exact h_xy_ne.symm
          have h_c_chain : c a = c y := by
            rw [←h_x_eq_a, h_cxy_eq]
          have h_y_in_complement : y ∈ σ \ {a, b} := by
            rw [Finset.mem_sdiff]
            exact ⟨h_y_in_σ, by simp [h_y_ne_a, h_y_eq_b]⟩
          have h_y_in_set : y ∈ (↑σ : Set T) \ {a, b} := by
            simp [Set.mem_diff, h_y_in_σ, h_y_ne_a, h_y_eq_b]
          have h_pairs_different : ({a, y} : Finset T) ≠ {a, b} := by
            intro h_eq
            have h_y_in : y ∈ ({a, b} : Finset T) := by
              rw [←h_eq]
              simp
            simp only [mem_insert, mem_singleton] at h_y_in
            cases h_y_in with
            | inl h_y_eq_a => exact h_y_ne_a h_y_eq_a
            | inr h_y_eq_b_case => exact h_y_eq_b h_y_eq_b_case
          exfalso
          have h_all_distinct : a ≠ b ∧ a ≠ y ∧ b ≠ y := by
            exact ⟨hab_ne, h_y_ne_a.symm, Ne.symm h_y_eq_b⟩
          have h_same_color : c a = c b ∧ c b = c y := by
            exact ⟨hc_eq, by rw [←hc_eq, ←h_c_chain]⟩
          have h_three_in_sigma : a ∈ σ ∧ b ∈ σ ∧ y ∈ σ := by
            exact ⟨ha_in_σ, hb_in_σ, h_y_in_σ⟩
          have h_card_bound : σ.card ≥ (σ.image c).card + 2 :=
            three_collision_card_bound σ c a b y ha_in_σ hb_in_σ h_y_in_σ
              hab_ne h_all_distinct.2.1 h_all_distinct.2.2 hc_eq h_same_color.2
          linarith [h_inj, h_card_bound]
      | inr h_x_eq_b =>
        by_cases h_y_eq_a : y = a
        · rw [h_x_eq_b, h_y_eq_a] at h_ne_pair
          have : ({b, a} : Finset T) = {a, b} := by simp [Finset.pair_comm]
          rw [this] at h_ne_pair
          exact h_ne_pair rfl
        · have h_y_ne_b : y ≠ b := by
            rw [h_x_eq_b] at h_xy_ne
            exact h_xy_ne.symm
          have h_c_chain : c b = c y := by
            rw [←h_x_eq_b, h_cxy_eq]
          have h_y_in_complement : y ∈ σ \ {a, b} := by
            rw [Finset.mem_sdiff]
            exact ⟨h_y_in_σ, by simp [h_y_eq_a, h_y_ne_b]⟩
          have h_y_in_set : y ∈ (↑σ : Set T) \ {a, b} := by
            simp [Set.mem_diff, h_y_in_σ, h_y_eq_a, h_y_ne_b]
          have h_pairs_different : ({b, y} : Finset T) ≠ {a, b} := by
            intro h_eq
            have h_y_in : y ∈ ({a, b} : Finset T) := by
              rw [←h_eq]
              simp
            simp only [mem_insert, mem_singleton] at h_y_in
            cases h_y_in with
            | inl h_y_eq_a_case => exact h_y_eq_a h_y_eq_a_case
            | inr h_y_eq_b_case => exact h_y_ne_b h_y_eq_b_case
          exfalso
          have h_all_distinct : a ≠ b ∧ b ≠ y ∧ a ≠ y := by
            exact ⟨hab_ne, h_y_ne_b.symm, Ne.symm h_y_eq_a⟩
          have h_same_color : c a = c b ∧ c b = c y := by
            exact ⟨hc_eq, h_c_chain⟩
          have h_three_in_sigma : a ∈ σ ∧ b ∈ σ ∧ y ∈ σ := by
            exact ⟨ha_in_σ, hb_in_σ, h_y_in_σ⟩
          have h_card_bound : σ.card ≥ (σ.image c).card + 2 :=
            three_collision_card_bound σ c a b y ha_in_σ hb_in_σ h_y_in_σ
              hab_ne h_all_distinct.2.2 h_all_distinct.2.1 hc_eq h_same_color.2
          linarith [h_inj, h_card_bound]
    | inr h_u_eq_y =>
      rw [h_u_eq_y] at hu_in_ab
      cases hu_in_ab with
      | inl h_y_eq_a =>
        by_cases h_x_eq_b : x = b
        · rw [h_y_eq_a, h_x_eq_b] at h_ne_pair
          have : ({a, b} : Finset T) = {b, a} := by simp [Finset.pair_comm]
          rw [←this] at h_ne_pair
          exact h_ne_pair rfl
        · have h_x_ne_a : x ≠ a := by
            rw [h_y_eq_a] at h_xy_ne
            exact h_xy_ne
          have h_c_chain : c a = c x := by
            rw [←h_y_eq_a, h_cxy_eq.symm]
          have h_x_in_complement : x ∈ σ \ {a, b} := by
            rw [Finset.mem_sdiff]
            exact ⟨h_x_in_σ, by simp [h_x_ne_a, h_x_eq_b]⟩
          have h_x_in_set : x ∈ (↑σ : Set T) \ {a, b} := by
            simp [Set.mem_diff, h_x_in_σ, h_x_ne_a, h_x_eq_b]
          have h_pairs_different : ({a, x} : Finset T) ≠ {a, b} := by
            intro h_eq
            have h_x_in : x ∈ ({a, b} : Finset T) := by
              rw [←h_eq]
              simp
            simp only [mem_insert, mem_singleton] at h_x_in
            cases h_x_in with
            | inl h_x_eq_a_case => exact h_x_ne_a h_x_eq_a_case
            | inr h_x_eq_b_case => exact h_x_eq_b h_x_eq_b_case
          exfalso
          have h_all_distinct : a ≠ b ∧ a ≠ x ∧ b ≠ x := by
            exact ⟨hab_ne, h_x_ne_a.symm, Ne.symm h_x_eq_b⟩
          have h_same_color : c a = c b ∧ c b = c x := by
            exact ⟨hc_eq, by rw [←hc_eq, ←h_c_chain]⟩
          have h_three_in_sigma : a ∈ σ ∧ b ∈ σ ∧ x ∈ σ := by
            exact ⟨ha_in_σ, hb_in_σ, h_x_in_σ⟩
          have h_card_bound : σ.card ≥ (σ.image c).card + 2 :=
            three_collision_card_bound σ c a b x ha_in_σ hb_in_σ h_x_in_σ
              hab_ne h_all_distinct.2.1 h_all_distinct.2.2 hc_eq h_same_color.2
          linarith [h_inj, h_card_bound]
      | inr h_y_eq_b =>
        by_cases h_x_eq_a : x = a
        · rw [h_y_eq_b, h_x_eq_a] at h_ne_pair
          exact h_ne_pair rfl
        · have h_x_ne_b : x ≠ b := by
            rw [h_y_eq_b] at h_xy_ne
            exact h_xy_ne
          have h_c_chain : c b = c x := by
            rw [←h_y_eq_b, h_cxy_eq.symm]
          have h_x_in_complement : x ∈ σ \ {a, b} := by
            rw [Finset.mem_sdiff]
            exact ⟨h_x_in_σ, by simp [h_x_eq_a, h_x_ne_b]⟩
          have h_x_in_set : x ∈ (↑σ : Set T) \ {a, b} := by
            simp [Set.mem_diff, h_x_in_σ, h_x_eq_a, h_x_ne_b]
          have h_pairs_different : ({b, x} : Finset T) ≠ {a, b} := by
            intro h_eq
            have h_x_in : x ∈ ({a, b} : Finset T) := by
              rw [←h_eq]
              simp
            simp only [mem_insert, mem_singleton] at h_x_in
            cases h_x_in with
            | inl h_x_eq_a_case => exact h_x_eq_a h_x_eq_a_case
            | inr h_x_eq_b_case => exact h_x_ne_b h_x_eq_b_case
          exfalso
          have h_all_distinct : a ≠ b ∧ b ≠ x ∧ a ≠ x := by
            exact ⟨hab_ne, h_x_ne_b.symm, Ne.symm h_x_eq_a⟩
          have h_same_color : c a = c b ∧ c b = c x := by
            exact ⟨hc_eq, h_c_chain⟩
          have h_three_in_sigma : a ∈ σ ∧ b ∈ σ ∧ x ∈ σ := by
            exact ⟨ha_in_σ, hb_in_σ, h_x_in_σ⟩
          have h_card_bound : σ.card ≥ (σ.image c).card + 2 :=
            three_collision_card_bound σ c a b x ha_in_σ hb_in_σ h_x_in_σ
              hab_ne h_all_distinct.2.2 h_all_distinct.2.1 hc_eq h_same_color.2
          linarith [h_inj, h_card_bound]

omit [DecidableEq T] [Inhabited T] IST in
/-- The colliding pair `{a, b}` of a repeated coloring coincides with `{x, y}`. -/
lemma collisionPairEq {x y a b : T}
    (h_x_in_σ : x ∈ σ) (h_y_in_σ : y ∈ σ) (h_xy_ne : x ≠ y) (h_cxy_eq : c x = c y)
    (ha_in_σ : a ∈ σ) (hb_in_σ : b ∈ σ) (hc_eq : c a = c b) (hab_ne : a ≠ b)
    (h_inj_outside : Set.InjOn c ((σ : Set T) \ {a, b}))
    (h_inj : #σ = #(image c σ) + 1) :
    (a = x ∧ b = y) ∨ (a = y ∧ b = x) := by
  have h_pair_eq : ({x, y} : Finset T) = {a, b} :=
    pairEqOfCollision h_x_in_σ h_y_in_σ h_xy_ne h_cxy_eq ha_in_σ hb_in_σ hc_eq hab_ne
      h_inj_outside h_inj
  have h_eq_or_swap : ({x, y} : Finset T) = {a, b} ∨ ({x, y} : Finset T) = {b, a} := by
    left; exact h_pair_eq
  cases h_eq_or_swap with
  | inl h_eq =>
    have : {a, b} = {x, y} := h_eq.symm
    by_cases h : a = x
    · left
      constructor
      · exact h
      · have h_b_in : b ∈ ({x, y} : Finset T) := by rw [← this]; simp
        simp only [mem_insert, mem_singleton] at h_b_in
        cases h_b_in with
        | inl h_b_eq_x => rw [h, h_b_eq_x] at hab_ne; contradiction
        | inr h_b_eq_y => exact h_b_eq_y
    · right
      have h_a_in : a ∈ ({x, y} : Finset T) := by rw [← this]; simp
      simp only [mem_insert, mem_singleton] at h_a_in
      cases h_a_in with
      | inl h_a_eq_x => contradiction
      | inr h_a_eq_y =>
        constructor
        · exact h_a_eq_y
        · have h_b_in : b ∈ ({x, y} : Finset T) := by rw [← this]; simp
          simp only [mem_insert, mem_singleton] at h_b_in
          cases h_b_in with
          | inl h_b_eq_x => exact h_b_eq_x
          | inr h_b_eq_y => rw [h_a_eq_y, h_b_eq_y] at hab_ne; contradiction
  | inr h_eq =>
    have : {b, a} = {x, y} := h_eq.symm
    by_cases h : b = x
    · have h_a_in : a ∈ ({x, y} : Finset T) := by rw [← this]; simp
      simp only [mem_insert, mem_singleton] at h_a_in
      cases h_a_in with
      | inl h_a_eq_x =>
        exfalso
        rw [h_a_eq_x] at hab_ne
        rw [h] at hab_ne
        exact hab_ne rfl
      | inr h_a_eq_y => exact Or.inr ⟨h_a_eq_y, h⟩
    · have h_b_in : b ∈ ({x, y} : Finset T) := by rw [← this]; simp
      simp only [mem_insert, mem_singleton] at h_b_in
      cases h_b_in with
      | inl h_b_eq_x => contradiction
      | inr h_b_eq_y =>
        have h_a_in : a ∈ ({x, y} : Finset T) := by rw [← this]; simp
        simp only [mem_insert, mem_singleton] at h_a_in
        cases h_a_in with
        | inl h_a_eq_x => exact Or.inl ⟨h_a_eq_x, h_b_eq_y⟩
        | inr h_a_eq_y => rw [h_a_eq_y, h_b_eq_y] at hab_ne; contradiction

omit [DecidableEq T] [Inhabited T] IST in
/-- A nearly colorful room has a unique missing color in `C`. -/
lemma uniqueMissingColor (h_missing_card : (C \ σ.image c).card = 1) :
    ∃! i₀, i₀ ∈ C ∧ i₀ ∉ σ.image c := by
  have h_nonempty : (C \ σ.image c).Nonempty := by
    rw [←Finset.card_pos]
    rw [h_missing_card]
    norm_num
  have h_singleton : ∃ i₀, C \ σ.image c = {i₀} := by
    exact Finset.card_eq_one.mp h_missing_card
  obtain ⟨i₀, h_eq⟩ := h_singleton
  use i₀
  constructor
  · constructor
    · have h_i₀_in_diff : i₀ ∈ C \ image c σ := by rw [h_eq]; simp
      exact (Finset.mem_sdiff.mp h_i₀_in_diff).1
    · have h_i₀_in_diff : i₀ ∈ C \ image c σ := by rw [h_eq]; simp
      exact (Finset.mem_sdiff.mp h_i₀_in_diff).2
  · intro j ⟨h_j_in_C, h_j_notin_img⟩
    have h_j_in_diff : j ∈ C \ σ.image c := by
      exact Finset.mem_sdiff.mpr ⟨h_j_in_C, h_j_notin_img⟩
    rw [h_eq] at h_j_in_diff
    exact Finset.mem_singleton.mp h_j_in_diff

omit [DecidableEq T] [Inhabited T] in
/-- The two doors of a nearly colorful room, when one color of `σ` is repeated. -/
lemma doorsOfNCroomRepeated [DecidableEq T] (h_room : isRoom σ C)
    (h_nc : isNearlyColorful c σ C) (h_inj : #σ = #(image c σ) + 1) :
    ∃ door1 door2, door1 ≠ door2 ∧ NCdoors c σ C = {door1, door2} := by
  have h_card_eq : C.card = σ.card := h_room.2
  let img := image c σ
  unfold isNearlyColorful at h_nc
  obtain ⟨h_cell, h_missing_card⟩ := h_nc
  have h_missing_exists : ∃! i₀, i₀ ∈ C ∧ i₀ ∉ σ.image c :=
    uniqueMissingColor h_missing_card
  obtain ⟨i₀, ⟨h_i₀_in_C, h_i₀_notin_img⟩, h_i₀_unique⟩ := h_missing_exists
  have h_collision_exists : ∃ x y, x ∈ σ ∧ y ∈ σ ∧ x ≠ y ∧ c x = c y := by
    by_contra h_no_collision
    push Not at h_no_collision
    have h_inj_on_σ : Set.InjOn c σ := by
      intro x h_x y h_y h_eq
      by_contra h_ne
      exact h_no_collision x y h_x h_y h_ne h_eq
    have h_card_eq : σ.card = (σ.image c).card := by
      exact (Finset.card_image_of_injOn h_inj_on_σ).symm
    rw [h_card_eq] at h_inj
    linarith
  obtain ⟨x, y, h_x_in_σ, h_y_in_σ, h_xy_ne, h_cxy_eq⟩ := h_collision_exists
  have h_collision_structure : ∃ a b, a ∈ σ ∧ b ∈ σ ∧ c a = c b ∧ a ≠ b ∧ Set.InjOn c (σ \ {a,
      b}) := by
    obtain ⟨a, b, ha, hb, heq, hne, hinj⟩ := injOn_sdiff σ c h_inj
    exact ⟨a, b, ha, hb, heq, hne, by convert hinj; simp⟩
  obtain ⟨a, b, ha_in_σ, hb_in_σ, hc_eq, hab_ne, h_inj_outside⟩ := h_collision_structure
  have h_collision_pair : (a = x ∧ b = y) ∨ (a = y ∧ b = x) :=
    collisionPairEq h_x_in_σ h_y_in_σ h_xy_ne h_cxy_eq ha_in_σ hb_in_σ hc_eq hab_ne h_inj_outside
      h_inj
  let τ₁ := σ.erase x
  let τ₂ := σ.erase y
  let door1 := (τ₁, C)
  let door2 := (τ₂, C)
  have h_door1_valid : isDoorof τ₁ C σ C :=
    collision_door_valid σ C c x h_cell h_x_in_σ h_card_eq
  have h_door2_valid : isDoorof τ₂ C σ C :=
    collision_door_valid σ C c y h_cell h_y_in_σ h_card_eq
  have h_imgs_preserved := image_erase_collision_preserves σ c x y h_x_in_σ h_y_in_σ h_xy_ne
      h_cxy_eq
  have h_door1_nc : isNearlyColorful c τ₁ C := by
    unfold isNearlyColorful
    constructor
    · exact Dominant_of_subset σ τ₁ C (Finset.erase_subset x σ) h_cell
    · rw [h_imgs_preserved.1, h_missing_card]
  have h_door2_nc : isNearlyColorful c τ₂ C := by
    unfold isNearlyColorful
    constructor
    · exact Dominant_of_subset σ τ₂ C (Finset.erase_subset y σ) h_cell
    · rw [h_imgs_preserved.2, h_missing_card]
  have h_doors_distinct : door1 ≠ door2 := by
    simp only [ne_eq, Prod.mk.injEq, and_true, door1, τ₁, door2, τ₂]
    intro h_eq
    have h_y_mem : y ∈ σ.erase x := by
      rw [Finset.mem_erase]
      exact ⟨h_xy_ne.symm, h_y_in_σ⟩
    rw [h_eq] at h_y_mem
    have h_y_not_mem : y ∉ σ.erase y := by
      rw [Finset.mem_erase]
      simp
    exact h_y_not_mem h_y_mem
  have h_exactly_two : NCdoors c σ C = {door1, door2} := by
    ext ⟨τ, D⟩
    simp only [NCdoors, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro ⟨h_nc_τD, h_door_τD⟩
      cases h_door_τD with
      | idoor h_cell_σC h_door_τD z h_z_notin_τ h_insert_eq h_D_eq_C =>
        rw [h_D_eq_C]
        have h_τ_eq : τ = σ.erase z := by
          rw [←Finset.erase_insert h_z_notin_τ, h_insert_eq]
        rw [h_τ_eq]
        have h_z_in_σ : z ∈ σ := by
          rw [←h_insert_eq]
          exact Finset.mem_insert_self z τ
        by_cases h_z_cases : z = x ∨ z = y
        · rcases h_z_cases with h_z_eq_x | h_z_eq_y
          · left; simp [door1, τ₁, h_z_eq_x]
          · right; simp [door2, τ₂, h_z_eq_y]
        · exfalso
          push Not at h_z_cases
          have h_card_is_one : (C \ (σ.erase z).image c).card = 1 := by
            rw [←h_D_eq_C, ←h_τ_eq]
            exact h_nc_τD.2
          have h_card_is_two : (C \ (σ.erase z).image c).card = 2 := by
            have h_uniq_z : ∀ w ∈ σ, c w = c z → w = z := by
              intro w hw h_c_eq
              rcases h_collision_pair with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
              · have h_z_ne_ab : z ≠ a ∧ z ≠ b := h_z_cases
                by_cases hw_ab : w ∈ ({a, b} : Finset T)
                · exfalso
                  have h_c_z_eq_ca : c z = c a := by
                    simp only [mem_insert, mem_singleton] at hw_ab; rcases hw_ab with rfl | rfl
                    · exact h_c_eq.symm
                    · exact h_c_eq.symm.trans hc_eq.symm
                  have h_card_ge_img_add_2 : σ.card ≥ (σ.image c).card + 2 :=
                    three_collision_card_bound σ c a b z ha_in_σ hb_in_σ h_z_in_σ
                      hab_ne (Ne.symm h_z_ne_ab.1) (Ne.symm h_z_ne_ab.2)
                          hc_eq (h_c_z_eq_ca ▸ hc_eq.symm)
                  linarith [h_inj, h_card_ge_img_add_2]
                · have h_w_sdiff : w ∈ σ \ {a, b} := by simp [hw, hw_ab]
                  have h_z_sdiff : z ∈ σ \ {a, b} := by simp [h_z_in_σ, h_z_ne_ab]
                  exact h_inj_outside (by simpa using h_w_sdiff) (by simpa using h_z_sdiff) h_c_eq
              · have h_z_ne_ab : z ≠ a ∧ z ≠ b := h_z_cases.symm
                by_cases hw_ab : w ∈ ({a, b} : Finset T)
                · exfalso
                  have h_c_z_eq_ca : c z = c a := by
                    simp only [mem_insert, mem_singleton] at hw_ab; rcases hw_ab with rfl | rfl
                    · exact h_c_eq.symm
                    · exact h_c_eq.symm.trans hc_eq.symm
                  have h_card_ge_img_add_2 : σ.card ≥ (σ.image c).card + 2 :=
                    three_collision_card_bound σ c a b z ha_in_σ hb_in_σ h_z_in_σ
                      hab_ne (Ne.symm h_z_ne_ab.1) (Ne.symm h_z_ne_ab.2)
                          hc_eq (h_c_z_eq_ca ▸ hc_eq.symm)
                  linarith [h_inj, h_card_ge_img_add_2]
                · have h_w_sdiff : w ∈ σ \ {a, b} := by simp [hw, hw_ab]
                  have h_z_sdiff : z ∈ σ \ {a, b} := by simp [h_z_in_σ, h_z_ne_ab]
                  exact h_inj_outside (by simpa using h_w_sdiff) (by simpa using h_z_sdiff) h_c_eq
            have h_img_erase : (σ.erase z).image c = (σ.image c).erase (c z) :=
              image_erase_eq_erase_image_of_unique σ c h_z_in_σ h_uniq_z
            rw [h_img_erase]
            have h_img_subset_C : image c σ ⊆ C := by
              have h_C_card_img : C.card = (image c σ).card + 1 := by rw [h_card_eq, h_inj]
              have h_C_card_form : C.card = (C \ image c σ).card + (C ∩ image c σ).card :=
                  (card_sdiff_add_card_inter C (image c σ)).symm
              rw [h_missing_card] at h_C_card_form
              have h_img_eq_inter_card : (image c σ).card = (C ∩ image c σ).card := by linarith
              have h_inter_eq_img : C ∩ image c σ = image c σ :=
                Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw
                    [h_img_eq_inter_card])
              rwa [Finset.inter_eq_right] at h_inter_eq_img
            have h_cz_in_C : c z ∈ C := h_img_subset_C (mem_image_of_mem c h_z_in_σ)
            have h_cz_not_in_diff : c z ∉ C \ image c σ := by simp [mem_image_of_mem c h_z_in_σ]
            have h_eq : C \ (image c σ).erase (c z) = (C \ image c σ) ∪ {c z} := by
              ext y
              simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_union,
                  Finset.mem_singleton]
              constructor
              · intro ⟨hy_in_C, hy_cond⟩
                by_cases h : y ∈ image c σ
                · right; by_contra h'; exact hy_cond ⟨h', h⟩
                · left; exact ⟨hy_in_C, h⟩
              · intro h
                cases h with
                | inl h => exact ⟨h.1, fun h' => h.2 h'.2⟩
                | inr h => rw [h]; exact ⟨h_cz_in_C, fun hp => hp.1 rfl⟩
            rw [h_eq, Finset.card_union_of_disjoint]
            · rw [h_missing_card, Finset.card_singleton]
            · exact Finset.disjoint_singleton_right.mpr h_cz_not_in_diff
          rw [h_card_is_two] at h_card_is_one
          norm_num at h_card_is_one
      | odoor h_cell_σC h_door_τD j h_j_notin_C h_τ_eq_σ h_D_eq =>
        exfalso
        have h_card_is_one : ((C ∪ {j}) \ (σ.image c)).card = 1 := by
         have : D \ (τ.image c) = (C ∪ {j}) \ (σ.image c) := by
           rw [h_D_eq, ← h_τ_eq_σ]
           rw [Finset.insert_eq, Finset.union_comm]
         rw [← this]
         exact h_nc_τD.2
        have h_img_subset_C : image c σ ⊆ C := by
          have h_C_card_img : C.card = (image c σ).card + 1 := by rw [h_card_eq, h_inj]
          have h_C_card_form : C.card = (C \ image c σ).card + (C ∩ image c σ).card :=
              (card_sdiff_add_card_inter C (image c σ)).symm
          rw [h_missing_card] at h_C_card_form
          have h_img_eq_inter_card : (image c σ).card = (C ∩ image c σ).card := by linarith
          have h_inter_eq_img : C ∩ image c σ = image c σ :=
            Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [h_img_eq_inter_card])
          rwa [Finset.inter_eq_right] at h_inter_eq_img
        have h_j_notin_img : j ∉ image c σ := fun h => h_j_notin_C (h_img_subset_C h)
        have h_card_is_two : ((C ∪ {j}) \ (σ.image c)).card = 2 := by
          rw [Finset.union_sdiff_distrib, Finset.card_union_of_disjoint]
          · have h_sdiff_eq : {j} \ image c σ = {j} :=
              Finset.sdiff_eq_self_of_disjoint (Finset.disjoint_singleton_left.mpr h_j_notin_img)
            rw [h_sdiff_eq, Finset.card_singleton]
            linarith [h_missing_card]
          · rw [Finset.sdiff_eq_self_of_disjoint (Finset.disjoint_singleton_left.mpr
              h_j_notin_img)]
            rw [Finset.disjoint_singleton_right]
            intro h
            have : j ∈ C := (Finset.mem_sdiff.mp h).1
            exact h_j_notin_C this
        rw [h_card_is_two] at h_card_is_one
        norm_num at h_card_is_one
    · intro h_or
      cases h_or with
      | inl h_eq =>
        have : τ = τ₁ ∧ D = C := Prod.mk.inj h_eq
        rw [this.1, this.2]
        exact ⟨h_door1_nc, h_door1_valid⟩
      | inr h_eq =>
        have : τ = τ₂ ∧ D = C := Prod.mk.inj h_eq
        rw [this.1, this.2]
        exact ⟨h_door2_nc, h_door2_valid⟩
  use door1, door2

omit [DecidableEq T] [Inhabited T] in
lemma doors_of_NCroom [DecidableEq T] (h_room : isRoom σ C) (h_nc : isNearlyColorful c σ C) :
  ∃ door1 door2, door1 ≠ door2 ∧ NCdoors c σ C = {door1, door2} := by
  rcases card_of_NCcell h_nc with h_eq | h_inj
  · exact doorsOfNCroomInjective h_room h_nc h_eq
  · exact doorsOfNCroomRepeated h_room h_nc h_inj


variable [Fintype T] [Fintype I]

variable (c) in
/-- The finset of colorful rooms of a coloring. -/
abbrev colorful := Finset.filter (fun (x : Finset T× Finset I) =>  IST.isColorful c x.1 x.2) univ

variable (c) in
/-- The set used for the double-counting parity argument of typed doors. -/
abbrev dbcountingset (i : I) := Finset.filter (fun x : (Finset T× Finset I) × (Finset T× Finset I)
    => isTypedNC c i x.1.1 x.1.2 ∧ isDoorof x.1.1 x.1.2 x.2.1 x.2.2) univ


variable (c) in
lemma dbcount_outside_door' (i : I) : ∃ x,  filter (fun x => isOutsideDoor x.1.1 x.1.2)
    (dbcountingset c i) = {x}  :=  by
  classical
  have h_T_nonempty : Nonempty T := ⟨(default : T)⟩
  have h_T_univ_nonempty : (Finset.univ : Finset T).Nonempty := Finset.univ_nonempty_iff.mpr
      h_T_nonempty
  let x_max_i : T := @Finset.max' T (IST i) Finset.univ h_T_univ_nonempty
  let σ_u : Finset T := {x_max_i}
  let C_u : Finset I := {i}
  let τ_u : Finset T := Finset.empty
  let D_u : Finset I := {i}
  let x_unique : (Finset T × Finset I) × (Finset T × Finset I) := ((τ_u, D_u), (σ_u, C_u))
  have h_outside_door_τu_Du : isOutsideDoor τ_u D_u := outsidedoor_singleton i
  have h_typed_nc : isTypedNC c i τ_u D_u := by
    constructor
    · exact (NC_of_outsidedoor (c := c) h_outside_door_τu_Du).1
    · simp only [τ_u]
      constructor
  have h_door_relation : isDoorof τ_u D_u σ_u C_u := by
    apply isDoorof.idoor
    · intro y
      use i
      constructor
      · simp only [C_u, Finset.mem_singleton]
      · intro x hx
        simp only [σ_u] at hx
        simp only [Finset.mem_singleton] at hx
        rw [hx]
        exact @Finset.le_max' T (IST i) Finset.univ y (Finset.mem_univ y)
    · exact h_outside_door_τu_Du.1
    · simp only [τ_u]
      exact Finset.notMem_empty x_max_i
    · simp only [τ_u, σ_u]
      rfl
    · rfl
  use x_unique
  ext x_gen
  simp only [mem_filter, mem_univ, mem_singleton]
  constructor
  · intro h_in_filter
    simp only [true_and] at h_in_filter
    obtain ⟨h_in_db, h_outside⟩ := h_in_filter
    obtain ⟨h_typed, h_door⟩ := h_in_db
    obtain ⟨h_is_door, h_empty⟩ := h_outside
    have h_empty_image : (x_gen.1.1).image c = ∅ := by
      rw [h_empty]
      exact Finset.image_empty c
    have h_x_gen_1_2_eq : x_gen.1.2 = {i} := by
      have h_eq := h_typed.2
      rw [h_empty_image] at h_eq
      simp only [sdiff_empty] at h_eq
      exact h_eq
    obtain ⟨_, h_D_singleton⟩ := outsidedoor_is_singleton ⟨h_is_door, h_empty⟩
    obtain ⟨j, h_D_eq⟩ := h_D_singleton
    have h_j_eq_i : j = i := by
      have h_eq_j : x_gen.1.2 = {j} := h_D_eq
      rw [h_x_gen_1_2_eq] at h_eq_j
      have : j ∈ {j} := Finset.mem_singleton_self j
      rw [←h_eq_j] at this
      exact Finset.eq_of_mem_singleton this
    cases h_door with
    | idoor h_cell_σC h_door_τD x h_x_notin h_insert_eq h_D_eq_C =>
      have h_σ_eq : x_gen.2.1 = {x} := by
        rw [←h_insert_eq, h_empty]
        rfl
      have h_x_eq_max : x = x_max_i := by
        have h_dom : ∀ y, y ≤[i] x := by
          intro y
          obtain ⟨j_dom, hj_in, hj_dom⟩ := h_cell_σC y
          rw [←h_D_eq_C, h_x_gen_1_2_eq] at hj_in
          simp only [mem_singleton] at hj_in
          subst hj_in
          apply hj_dom
          rw [h_σ_eq]
          simp
        have h1 : x ≤[i] x_max_i := @Finset.le_max' T (IST i) Finset.univ x (Finset.mem_univ x)
        have h2 : x_max_i ≤[i] x := h_dom x_max_i
        exact @le_antisymm T (IST i).toPartialOrder x x_max_i h1 h2
      apply Prod.ext
      · apply Prod.ext
        · exact h_empty
        · rw [h_x_gen_1_2_eq]
      · apply Prod.ext
        · rw [h_σ_eq, h_x_eq_max]
        · rw [←h_D_eq_C, h_x_gen_1_2_eq]
    | odoor h_cell_σC h_door_τD j h_j_notin h_τ_eq h_D_insert =>
      exfalso
      have h_σ_empty : x_gen.2.1 = ∅ := by
        rw [←h_τ_eq, h_empty]
        rfl
      let h_door_constructed : isDoorof x_gen.1.1 x_gen.1.2 x_gen.2.1 x_gen.2.2 :=
        isDoorof.odoor h_cell_σC ⟨h_is_door.1, h_is_door.2⟩ j h_j_notin h_τ_eq h_D_insert
      have h_room : IST.isRoom x_gen.2.1 x_gen.2.2 := isRoom_of_Door h_door_constructed
      have h_σ_nonempty : x_gen.2.1.Nonempty := sigma_nonempty_of_room h_room
      rw [h_σ_empty] at h_σ_nonempty
      exact Finset.not_nonempty_empty h_σ_nonempty
  · intro h_eq
    rw [h_eq]
    simp only [true_and]
    constructor
    · constructor
      · exact h_typed_nc
      · exact h_door_relation
    · exact h_outside_door_τu_Du

variable (c)

-- Use Lemme 2
lemma dbcount_outside_door_odd (i : I) : Odd (filter (fun x => isOutsideDoor x.1.1 x.1.2)
    (dbcountingset c i)).card  := by
  have cardone: (filter (fun x => isOutsideDoor x.1.1 x.1.2) (dbcountingset c i)).card = 1 := by
    obtain ⟨x,hx⟩ := dbcount_outside_door' c i
    simp [hx]
  convert odd_one

omit [Inhabited T] in
lemma fiber_size_internal_door (c : T → I) (i : I) (y : Finset T × Finset I)
    (hy_internal : IST.isInternalDoor y.1 y.2) (hy_typed : isTypedNC c i y.1 y.2) :
    let s := filter (fun x => ¬ isOutsideDoor x.1.1 x.1.2) (dbcountingset c i)
    let f := fun (x : (Finset T × Finset I) × Finset T × Finset I) => x.1
    (filter (fun a => f a = y) s).card = 2 := by
  obtain ⟨σ₁, σ₂, C₁, C₂, h_ne, h_room₁, h_room₂, h_door₁, h_door₂, h_unique⟩ :=
    internal_door_two_rooms y.1 y.2 hy_internal
  let s := filter (fun x => ¬ isOutsideDoor x.1.1 x.1.2) (dbcountingset c i)
  let f := fun (x : (Finset T × Finset I) × Finset T × Finset I) => x.1
  let elem1 : (Finset T × Finset I) × Finset T × Finset I := (y, (σ₁, C₁))
  let elem2 : (Finset T × Finset I) × Finset T × Finset I := (y, (σ₂, C₂))
  have elem1_in_s : elem1 ∈ s := by
    simp only [elem1, s, mem_filter]
    constructor
    · simp only [mem_univ, true_and]
      exact ⟨hy_typed, h_door₁⟩
    · intro h_outside
      exact (Finset.nonempty_iff_ne_empty.mp hy_internal.2) h_outside.2
  have elem2_in_s : elem2 ∈ s := by
    simp only [elem2, s, mem_filter]
    constructor
    · simp only [mem_univ, true_and]
      exact ⟨hy_typed, h_door₂⟩
    · intro h_outside
      exact (Finset.nonempty_iff_ne_empty.mp hy_internal.2) h_outside.2
  have elems_distinct : elem1 ≠ elem2 := by
    intro h_eq
    injection h_eq with _ h_pair_eq
    exact h_ne h_pair_eq
  have fiber_eq : filter (fun a => f a = y) s = {elem1, elem2} := by
    ext x
    constructor
    · intro hx
      rw [mem_filter] at hx
      obtain ⟨hx_s, hx_eq⟩ := hx
      rw [mem_filter] at hx_s
      obtain ⟨hx_db, _⟩ := hx_s
      rw [mem_filter] at hx_db
      obtain ⟨_, hx_typed_x, hx_door_x⟩ := hx_db
      have h_x_form : x = (y, x.2) := Prod.ext_iff.mpr ⟨hx_eq, rfl⟩
      have h_room_x2 : IST.isRoom x.2.1 x.2.2 := isRoom_of_Door hx_door_x
      have hx_door_y : isDoorof y.1 y.2 x.2.1 x.2.2 :=
        hx_eq ▸ hx_door_x
      obtain h_case1 | h_case2 := h_unique x.2.1 x.2.2 h_room_x2 hx_door_y
      · simp only [mem_insert, mem_singleton]
        left
        rw [h_x_form]
        apply Prod.ext
        · rfl
        · apply Prod.ext
          · exact h_case1.1
          · exact h_case1.2
      · simp only [mem_insert, mem_singleton]
        right
        rw [h_x_form]
        apply Prod.ext
        · rfl
        · apply Prod.ext
          · exact h_case2.1
          · exact h_case2.2
    · intro hx
      simp only [mem_insert, mem_singleton] at hx
      cases hx with
      | inl h =>
        rw [h, mem_filter]
        exact ⟨elem1_in_s, by simp [f, elem1]⟩
      | inr h =>
        rw [h, mem_filter]
        exact ⟨elem2_in_s, by simp [f, elem2]⟩
  apply Eq.trans (congrArg Finset.card fiber_eq)
  exact Finset.card_pair elems_distinct

omit [Inhabited T] in
lemma dbcount_internal_door_even (i : I) : Even (filter (fun x => ¬ isOutsideDoor x.1.1 x.1.2)
    (dbcountingset c i)).card := by
  let s := filter (fun x => ¬ isOutsideDoor x.1.1 x.1.2) (dbcountingset c i)
  let t := filter (fun (x : Finset T × Finset I)
      => IST.isInternalDoor x.1 x.2 ∧ isTypedNC c i x.1 x.2) univ
  let f := fun (x : (Finset T × Finset I) × Finset T × Finset I) => x.1
  have fs_in_t : ∀ x ∈ s, f x ∈ t := by
    intro x hx
    rw [mem_filter] at hx
    obtain ⟨hx_db, hx_not_outside⟩ := hx
    rw [mem_filter] at hx_db
    obtain ⟨_, hx_typed, hx_door⟩ := hx_db
    rw [mem_filter]
    simp only [mem_univ, true_and]
    constructor
    · unfold isInternalDoor
      constructor
      · cases hx_door with
        | idoor h0 h1 y h_notin h_eq h_D_eq_C => exact h1
        | odoor h0 h1 j h_notin h_eq h_D_eq => exact h1
      · by_contra h_empty
        have h_outside : isOutsideDoor x.1.1 x.1.2 := by
          constructor
          · cases hx_door with
            | idoor h0 h1 y h_notin h_eq h_D_eq_C => exact h1
            | odoor h0 h1 j h_notin h_eq h_D_eq => exact h1
          · exact Finset.not_nonempty_iff_eq_empty.mp h_empty
        exact hx_not_outside h_outside
    · exact hx_typed
  have fiber_size_two : ∀ y ∈ t, (filter (fun a=> f a = y) s).card = 2 := by
    intro y hy
    rw [mem_filter] at hy
    obtain ⟨_, hy_internal, hy_typed⟩ := hy
    exact fiber_size_internal_door c i y hy_internal hy_typed
  have counteq := Finset.card_eq_sum_card_fiberwise fs_in_t
  have sumeq := Finset.sum_const_nat fiber_size_two
  rw [sumeq] at counteq
  rw [counteq]
  simp only [even_two, Even.mul_left]

/- Easy -/
omit [Fintype T] [Fintype I] [Inhabited T] in
variable {c} in
lemma NC_of_NCdoor (h1 : isTypedNC c i τ D)
(h2 : isDoorof τ D σ C) :
  ¬ isColorful c σ C → isTypedNC c i σ C := by
  intro h_not_colorful
  obtain h_typed | h_colorful := NC_or_C_of_door h1 h2
  · exact h_typed
  · contradiction

omit [Inhabited T] in
variable {c} in
lemma firber2_doors_NCroom (h0 : isRoom σ C) (h1 : isTypedNC c i σ C) :
  (filter (fun (x : (Finset T× Finset I)× Finset T × Finset I) => x.2 = (σ,C))
      (dbcountingset c i)).card = 2 := by
    obtain ⟨door1, door2, h_ne, h_doors_eq⟩ := doors_of_NCroom h0 (NC_of_TNC h1)
    have h_filter_eq : filter (fun (x : (Finset T× Finset I)× Finset T × Finset I) => x.2 = (σ,C))
        (dbcountingset c i) =
                       {(door1, (σ,C)), (door2, (σ,C))} := by
      ext x
      constructor
      · intro hx
        rw [mem_filter] at hx
        obtain ⟨h_db, h_eq⟩ := hx
        rw [mem_filter] at h_db
        obtain ⟨_, h_typed, h_door⟩ := h_db
        have h_x_form : x = (x.1, (σ,C)) := by
          rw [Prod.ext_iff]
          exact ⟨rfl, h_eq⟩
        rw [h_x_form]
        simp only [mem_insert, Prod.mk.injEq, and_true, mem_singleton]
        have h_x1_in_doors : x.1 ∈ NCdoors c σ C := by
          simp only [NCdoors, Set.mem_setOf_eq]
          have h_sigma : x.2.1 = σ := by rw [h_eq]
          have h_C : x.2.2 = C := by rw [h_eq]
          rw [h_sigma, h_C] at h_door
          exact ⟨NC_of_TNC h_typed, h_door⟩
        rw [h_doors_eq] at h_x1_in_doors
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h_x1_in_doors
        exact h_x1_in_doors
      · intro hx
        simp only [mem_insert, mem_singleton] at hx
        cases hx with
        | inl h =>
          rw [h, mem_filter]
          constructor
          · rw [mem_filter]
            have h_door1_in_doors : door1 ∈ NCdoors c σ C := by
              rw [h_doors_eq]
              exact Set.mem_insert door1 {door2}
            simp only [NCdoors, Set.mem_setOf_eq] at h_door1_in_doors
            exact ⟨by simp,
                isTypedNC_of_isNearlyColorful_of_isDoorof_isTypedNC h_door1_in_doors.1
                h_door1_in_doors.2 h1, h_door1_in_doors.2⟩
          · rfl
        | inr h =>
          rw [h, mem_filter]
          constructor
          · rw [mem_filter]
            have h_door2_in_doors : door2 ∈ NCdoors c σ C := by
              rw [h_doors_eq]
              exact Set.mem_insert_of_mem door1 (Set.mem_singleton door2)
            simp only [NCdoors, Set.mem_setOf_eq] at h_door2_in_doors
            exact ⟨by simp,
                isTypedNC_of_isNearlyColorful_of_isDoorof_isTypedNC h_door2_in_doors.1
                h_door2_in_doors.2 h1, h_door2_in_doors.2⟩
          · rfl
    rw [h_filter_eq]
    simp [h_ne]

omit [Inhabited T] in
lemma dbcount_NCroom (i : I) : Even (filter (fun x => ¬isColorful c x.2.1 x.2.2)
    (dbcountingset c i)).card := by
  let s := filter (fun x => ¬isColorful c x.2.1 x.2.2) (dbcountingset c i)
  let t := filter (fun (x : Finset T × Finset I) => IST.isRoom x.1 x.2 ∧ isTypedNC c i x.1 x.2 )
      univ
  let f := fun (x : (Finset T × Finset I)× Finset T × Finset I) => x.2
  have fs_in_t : ∀ x ∈ s, f x ∈ t := by
    intro x hx
    change x.2 ∈ t
    rw [mem_filter] at hx
    obtain ⟨hx1,hx2⟩ := hx
    rw [mem_filter] at hx1
    rw [mem_filter]
    refine ⟨by simp, isRoom_of_Door hx1.2.2,?_⟩
    apply NC_of_NCdoor hx1.2.1 hx1.2.2 hx2
  have counteq := Finset.card_eq_sum_card_fiberwise fs_in_t
  have fiber_sizetwo :∀ y ∈ t, #(filter (fun a=> f a = y) s) = 2  :=
    by
      intro y hy
      rw [Finset.mem_filter] at hy
      obtain ⟨_,hy1,hy2⟩ := hy
      unfold s
      rw [filter_filter]
      have f2 := firber2_doors_NCroom hy1 hy2
      rw [<-f2]
      congr 1
      apply filter_congr
      intro x hx
      rw [mem_filter] at hx
      obtain ⟨hx1,hx2,hx3⟩ := hx
      unfold f
      constructor
      · simp
      · intro h
        simp_rw [h,and_true]
        exact not_colorful_of_TypedNC hy2
  have sumeq := Finset.sum_const_nat fiber_sizetwo
  rw [sumeq] at counteq
  rw [counteq]
  simp only [even_two, Even.mul_left]

lemma parity_lemma {a b c d : ℕ} (h1 : Odd a) (h2 : Even b) (h3 : Even d) (h4 : a + b = c + d)
    : Odd c := by
  by_contra h0
  replace h0 := Nat.not_odd_iff_even.1 h0
  have oddab := Even.odd_add h2 h1
  rw [h4] at oddab
  have evencd := Even.add h0 h3
  exact Nat.not_odd_iff_even.2 evencd oddab


theorem _root_.Finset.card_filter_filter_neg {α : Type*} (s : Finset α) (p : α → Prop)
    [DecidablePred p]
 : s.card  = (Finset.filter p s).card + (Finset.filter (fun (a : α) => ¬p a) s).card :=
  by
    nth_rw 1 [<-Finset.filter_union_filter_not_eq p s]
    apply Finset.card_union_eq_card_add_card.2 (Finset.disjoint_filter_filter_not _ _ _)

lemma typed_colorful_room_odd (i : I) : Odd (Finset.filter (fun (x: (Finset T× Finset I)
    × Finset T × Finset I) =>  isColorful c x.2.1 x.2.2) (dbcountingset c i)).card
:= by
  let s:= dbcountingset c i
  have cardeq' := Finset.card_filter_filter_neg s (fun x => isOutsideDoor x.1.1 x.1.2)
  have cardeq := Finset.card_filter_filter_neg s (fun x => isColorful c x.2.1 x.2.2)
  apply parity_lemma (dbcount_outside_door_odd c i) (dbcount_internal_door_even c i)
      (dbcount_NCroom c i)
  rw [<-cardeq',<-cardeq]

variable [Inhabited I]

omit [DecidableEq T] in
theorem Scarf : (IST.colorful c).Nonempty := by
  have cardpos := Odd.pos <| typed_colorful_room_odd c default
  replace nonempty:= Finset.card_pos.1 cardpos
  obtain ⟨x,hx⟩ := nonempty
  replace hx := (Finset.mem_filter.1 hx).2
  use x.2
  simp only [mem_filter, mem_univ, hx, and_self]


end Scarf

end IndexedLOrder
