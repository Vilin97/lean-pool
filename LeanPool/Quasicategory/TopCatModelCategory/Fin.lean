/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Fin.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.FinCases

namespace Fin

/-
@[simps]
def orderIsoSingleton {α : Type*} [Preorder α] (a : α) :
    Fin 1 ≃o ({a} : Finset α) where
  toFun _ := ⟨a, by simp⟩
  invFun _ := 0
  left_inv _ := by aesop
  right_inv _ := by aesop
  map_rel_iff' := by aesop

@[simps! apply]
noncomputable def orderIsoPair {α : Type*} [Preorder α] [DecidableEq α] (a b : α) (hab : a < b) :
    Fin 2 ≃o ({a, b} : Finset α) where
  toEquiv := Equiv.ofBijective (fun i ↦ match i with
    | 0 => ⟨a, by simp⟩
    | 1 => ⟨b, by simp⟩) (by
    constructor
    · intro i j h
      fin_cases i <;> fin_cases j <;> aesop
    · rintro ⟨x, hx⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      obtain rfl | rfl := hx
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩)
  map_rel_iff' := by
    intro i j
    fin_cases i <;> fin_cases j
    · simp
    · simpa using hab.le
    · dsimp
      simp only [Subtype.mk_le_mk, isValue, le_zero_iff, Nat.reduceAdd, one_eq_zero_iff, zero_add,
        Nat.succ_ne_self, iff_false]
      intro h
      have := lt_of_le_of_lt h hab
      simp at this
    · simp

@[simps! apply]
noncomputable def orderIsoTriple {α : Type*} [Preorder α] [DecidableEq α] (a b c : α)
    (hab : a < b) (hbc : b < c ):
    Fin 3 ≃o ({a, b, c} : Finset α) where
  toEquiv := Equiv.ofBijective (fun i ↦ match i with
    | 0 => ⟨a, by simp⟩
    | 1 => ⟨b, by simp⟩
    | 2 => ⟨c, by simp⟩) (by
    have hac := hab.trans hbc
    constructor
    · intro i j h
      fin_cases i <;> fin_cases j <;> aesop
    · rintro ⟨x, hx⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      obtain rfl | rfl | rfl := hx
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩)
  map_rel_iff' := by
    intro i j
    have := hab.le
    have := hbc.le
    have := hab.le.trans hbc.le
    have := hab.trans hbc
    have h : ∀ ⦃i j : α⦄ (h₁ : i < j), ¬ (j ≤ i) := fun i j hij h ↦ by
      have := lt_of_le_of_lt h hij
      simp at this
    fin_cases i <;> fin_cases j <;> try simp <;> try assumption
    all_goals apply h; assumption-/

lemma eq_last_or_eq_castSucc {n : ℕ} (i : Fin (n + 1)) :
    i = Fin.last _ ∨ ∃ (j : Fin n), i = j.castSucc := by
  by_cases hi : i = Fin.last _
  · tauto
  · have := Fin.exists_castSucc_eq.2 hi
    tauto

lemma monotone_iff {α : Type u} [Preorder α] {n : ℕ} (f : Fin (n + 1) → α) :
    Monotone f ↔ ∀ (i : Fin n), f i.castSucc ≤ f i.succ := by
  refine ⟨fun hf i ↦ hf i.castSucc_le_succ, fun hf ↦ ?_⟩
  let P (k : ℕ) := ∀ (i : ℕ) (hi : i + k ≤ n), f ⟨i, by omega⟩ ≤ f ⟨i + k, by omega⟩
  suffices ∀ k, P k by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ (h : i ≤ j)
    obtain ⟨k, rfl⟩ := Nat.le.dest h
    exact this k i (by omega)
  intro k
  induction k with
  | zero => simp [P]
  | succ k hk =>
      intro i hi
      simp only [← add_assoc]
      exact (hk i (by omega)).trans (hf ⟨i + k, by omega⟩)

/-lemma orderHom_injective_iff {α : Type*} [PartialOrder α] {n : ℕ} (f : Fin (n + 1) →o α) :
    Function.Injective f ↔ ∀ (i : Fin n), f i.castSucc ≠ f i.succ := by
  constructor
  · intro hf i h
    simpa [Fin.ext_iff] using hf h
  · intro hf i j h
    wlog hij : i ≤ j generalizing i j h
    · exact (this h.symm (by omega)).symm
    obtain ⟨k, hk⟩ := Nat.le.dest hij
    cases k with
    | zero => ext; omega
    | succ k =>
        let l : Fin n := ⟨i.1, by omega⟩
        have h₁ : f i < f l.succ := by
          rw [lt_iff_le_and_ne]
          exact ⟨f.monotone l.castSucc_le_succ, hf l⟩
        have h₂ : f i < f j := lt_of_lt_of_le h₁ (f.monotone (by
          simp only [Fin.le_def, val_succ, l]
          omega))
        exact (h₂.ne h).elim-/

lemma strictMono_iff {α : Type*} [PartialOrder α] {n : ℕ} (f : Fin (n + 1) → α) :
    StrictMono f ↔ ∀ (i : Fin n), f i.castSucc < f i.succ := by
  constructor
  · intro hf i
    exact hf (castSucc_lt_succ i)
  · intro h
    let φ : Fin (n + 1) →o α :=
      { toFun := f
        monotone' := by
          rw [monotone_iff]
          intro i
          exact (h i).le }
    refine (Monotone.strictMono_iff_injective (f := f) φ.monotone).2
      ((orderHom_injective_iff φ).2 (fun i hi ↦ ?_))
    dsimp [φ] at hi
    replace h := h i
    simp [hi] at h

@[simps]
def oneOrderHomEquiv {α : Type*} [Preorder α] :
    (Fin 1 →o α) ≃ α where
  toFun f := f 0
  invFun a :=
    { toFun _ := a
      monotone' _ _ _ := by aesop }
  left_inv _ := by
    ext i
    obtain rfl := Subsingleton.elim 0 i
    rfl
  right_inv _ := rfl

lemma orderHom_ext_of_injective_aux {α : Type*} [PartialOrder α] [DecidableEq α]
    {n : ℕ} {f g : Fin n →o α}
    (hg : Function.Injective g)
    (h : Finset.image f ⊤ = Finset.image g ⊤) (i : Fin n)
    (h' : ∀ (j : Fin n), j < i → f j = g j) :
    f i ≤ g i := by
  have : g i ∈ Finset.image f ⊤ := by rw [h]; simp
  simp only [Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ, true_and] at this
  obtain ⟨j, hj⟩ := this
  rw [← hj]
  apply f.monotone
  by_contra!
  rw [h' j this] at hj
  obtain rfl := hg hj
  simp at this

lemma orderHom_ext_of_injective {α : Type*} [PartialOrder α] [DecidableEq α]
    {n : ℕ} {f g : Fin n →o α}
    (hf : Function.Injective f) (hg : Function.Injective g)
    (h : Finset.image f ⊤ = Finset.image g ⊤) :
    f = g := by
  let P (i : ℕ) := ∀ (j : ℕ) (hij : j < i) (hj : j < n), f ⟨j, by omega⟩ = g ⟨j, by omega⟩
  suffices ∀ i, P i by ext i; exact this (i.1 + 1) i.1 (by omega) (by omega)
  suffices ∀ i, P i → P (i + 1) by
    intro i
    induction i with
    | zero =>
        intro _ _
        omega
    | succ i hi => exact fun j hij hj ↦ this _ hi j hij hj
  intro i hi j hij hj
  obtain hij | rfl := (Nat.le_of_lt_succ hij).lt_or_eq
  · exact hi j hij hj
  · apply le_antisymm
    · exact orderHom_ext_of_injective_aux hg h _
        (fun k hk ↦ hi k hk (by omega))
    · exact orderHom_ext_of_injective_aux hf h.symm _
        (fun k hk ↦ (hi k hk (by omega)).symm)

@[simp]
lemma range_succAboveOrderEmb {n : ℕ} (i : Fin (n + 1)) :
    Set.range (Fin.succAboveOrderEmb i).toOrderHom = {i}ᶜ := by aesop

lemma eq_id_of_strictMono {n : ℕ} (f : Fin (n + 1) →o Fin (n + 1)) (hf : StrictMono f) :
    f = .id := by
  apply orderHom_ext_of_injective
  · exact hf.injective
  · exact fun _ _ h ↦ h
  · simp only [Finset.top_eq_univ, OrderHom.id_coe, Finset.image_id]
    apply Finset.image_univ_of_surjective
    apply Finite.surjective_of_injective
    exact hf.injective

section

variable {α : Type*}

section

variable {n : ℕ} (f : Fin n → α)

def insert (i₀ : Fin (n + 1)) (x : α) (i : Fin (n + 1)) : α :=
  if h₀ : i = i₀ then x
    else
      if hi : i < i₀ then
          f ⟨i.1, by omega⟩
        else
          f (i.pred (by
            rintro rfl
            simp only [not_lt, le_zero_iff] at hi
            tauto))

@[simp]
lemma insert_self (i₀ : Fin (n + 1)) (x : α) :
    insert f i₀ x i₀ = x :=
  dif_pos rfl

@[simp] lemma insert_zero_succ (x : α) (i : Fin n) :
    insert f 0 x i.succ = f i := rfl

@[simp]
lemma insert_last_castSucc (x : α) (i : Fin n) :
    insert f (Fin.last _) x i.castSucc = f i := by
  dsimp [insert]
  have : i.castSucc ≠ last n := fun h ↦ by
    rw [Fin.ext_iff] at h
    simp only [coe_castSucc, val_last] at h
    omega
  rw [dif_neg this, dif_pos (castSucc_lt_last i)]

lemma insert_apply (i : Fin n) (x : α) (j : Fin (n + 1)) (hj : j ≠ i.succ) :
    insert f i.succ x j = f (i.predAbove j) := by
  dsimp [insert]
  rw [dif_neg hj]
  split_ifs with h <;> congr 1
  · rw [predAbove_of_lt_succ _ _ h]
    rfl
  · rw [predAbove_of_succ_le _ _ (by simpa using h)]

@[simp]
lemma insert_apply_succAbove (i : Fin (n + 1)) (x : α) (j : Fin n) :
    insert f i x (i.succAbove j) = f j := by
  dsimp [insert]
  rw [dif_neg (succAbove_ne i j)]
  by_cases h : j.castSucc < i
  · simp only [Fin.succAbove_of_castSucc_lt i j h, dif_pos h,
      coe_castSucc, Fin.eta]
  · simp only [not_lt] at h
    simp only [Fin.succAbove_of_le_castSucc i j h,
      dif_neg (not_lt.2 (h.trans j.castSucc_le_succ)), pred_succ]

end

section

variable [Preorder α] {n : ℕ}

lemma monotone_insert_zero (f : Fin (n + 1) →o α) (x : α) (hx : x ≤ f 0) :
    Monotone (insert f 0 x) := by
  rw [monotone_iff]
  intro i
  obtain rfl | ⟨j, rfl⟩ := i.eq_zero_or_eq_succ
  · simpa [insert_zero_succ f x 0] using hx
  · simpa only [← succ_castSucc, insert_zero_succ]
      using f.monotone (castSucc_le_succ j)

lemma monotone_insert_last (f : Fin (n + 1) →o α) (x : α)
    (hx : f (Fin.last _) ≤ x) :
    Monotone (insert f (Fin.last _) x) := by
  rw [monotone_iff]
  intro i
  obtain rfl | ⟨j, rfl⟩ := i.eq_last_or_eq_castSucc
  · simpa
  · simpa only [insert_last_castSucc, succ_castSucc]
      using f.monotone (castSucc_le_succ j)

lemma monotone_insert (f : Fin (n + 1) →o α) (i : Fin n) (x : α)
    (hx₁ : f i.castSucc ≤ x) (hx₂ : x ≤ f i.succ):
    Monotone (insert f i.succ.castSucc x) := by
  rw [monotone_iff]
  intro j
  by_cases hj : j.castSucc ≠ i.castSucc.succ ∧
    j.succ ≠ i.castSucc.succ
  · rw [← succ_castSucc, insert_apply _ _ _ _ hj.1, insert_apply _ _ _ _ hj.2]
    apply f.monotone
    apply predAbove_right_monotone
    exact castSucc_le_succ j
  · simp only [Classical.not_and_iff_or_not_not,
      Decidable.not_not, succ_inj] at hj
    conv_lhs at hj => rw [succ_castSucc, castSucc_inj]
    obtain rfl | rfl := hj
    · rw [insert_self, ← succ_castSucc,
        insert_apply _ _ _ _ (by simp [Fin.ext_iff]),
        Fin.predAbove_of_succ_le _ _ (by simpa using castSucc_le_succ i),
        pred_succ]
      exact hx₂
    · simpa [← succ_castSucc, insert_apply f i.castSucc x i.castSucc.castSucc
        (by simp [Fin.ext_iff])] using hx₁

end

section

variable [PartialOrder α] {n : ℕ}

lemma strictMono_insert_zero(f : Fin (n + 1) → α) (hf : StrictMono f)
    (x : α) (hx : x < f 0) :
    StrictMono (insert f 0 x) := by
  rw [strictMono_iff]
  intro i
  obtain rfl | ⟨j, rfl⟩ := i.eq_zero_or_eq_succ
  · simpa [insert_zero_succ f x 0] using hx
  · simpa only [← succ_castSucc, insert_zero_succ]
      using hf (castSucc_lt_succ j)

lemma strictMono_insert_last (f : Fin (n + 1) → α) (hf : StrictMono f)
    (x : α) (hx : f (Fin.last _) < x) :
    StrictMono (insert f (Fin.last _) x) := by
  rw [strictMono_iff]
  intro i
  obtain rfl | ⟨j, rfl⟩ := i.eq_last_or_eq_castSucc
  · simpa
  · simpa only [insert_last_castSucc, succ_castSucc]
      using hf (castSucc_lt_succ j)

lemma predAbove_eq_predAdove_iff_of_lt (i : Fin n) (j k : Fin (n + 1))
    (hjk : j < k) :
    i.predAbove j = i.predAbove k ↔ j = i.castSucc ∧ k = i.succ := by
  constructor
  · intro h₁
    by_cases h₂ : i.castSucc < j
    · rw [predAbove_of_castSucc_lt _ _ h₂,
        predAbove_of_castSucc_lt _ _ (by omega), pred_inj] at h₁
      omega
    · simp only [not_lt] at h₂
      rw [predAbove_of_le_castSucc _ _ h₂] at h₁
      by_cases h₃ : i.castSucc < k
      · obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_eq_succ
        · simp at h₃
        · rw [predAbove_of_castSucc_lt _ _ h₃, ← castSucc_inj,
            castSucc_castPred, pred_succ] at h₁
          subst h₁
          obtain rfl : i = k :=
            le_antisymm (by simpa using h₃) (by simpa using h₂)
          tauto
      · simp only [not_lt] at h₃
        rw [predAbove_of_le_castSucc _ _ h₃, ← castSucc_inj,
          castSucc_castPred, castSucc_castPred] at h₁
        omega
  · rintro ⟨rfl, rfl⟩
    simp

lemma strictMono_insert (f : Fin (n + 1) → α) (hf : StrictMono f)
    (i : Fin n) (x : α)
    (hx₁ : f i.castSucc < x) (hx₂ : x < f i.succ):
    StrictMono (insert f i.succ.castSucc x) := by
  rw [strictMono_iff]
  intro j
  by_cases hj : j.castSucc ≠ i.castSucc.succ ∧
    j.succ ≠ i.castSucc.succ
  · rw [← succ_castSucc, insert_apply _ _ _ _ hj.1, insert_apply _ _ _ _ hj.2]
    apply hf
    obtain h | h := (i.castSucc.predAbove_right_monotone (castSucc_le_succ j)).lt_or_eq
    · exact h
    · rw [predAbove_eq_predAdove_iff_of_lt _ _ _ (castSucc_lt_succ j)] at h
      simp only [castSucc_inj, succ_inj, and_self, ne_eq] at h hj
      tauto
  · simp only [Classical.not_and_iff_or_not_not,
      Decidable.not_not, succ_inj] at hj
    conv_lhs at hj => rw [succ_castSucc, castSucc_inj]
    obtain rfl | rfl := hj
    · rw [insert_self, ← succ_castSucc,
        insert_apply _ _ _ _ (by simp [Fin.ext_iff]),
        Fin.predAbove_of_succ_le _ _ (by simpa using castSucc_le_succ i),
        pred_succ]
      exact hx₂
    · simpa [← succ_castSucc, insert_apply f i.castSucc x i.castSucc.castSucc
        (by simp [Fin.ext_iff])] using hx₁

end

end

section

variable {ι : Type*} [Preorder ι] {x₀ x₁ : ι} (h : x₀ ≤ x₁)

@[simps]
def orderHomMk₂ : Fin 2 →o ι where
  toFun i := match i with
    | 0 => x₀
    | 1 => x₁
  monotone' := by
    rw [monotone_iff]
    intro i
    fin_cases i
    exact h

end

end Fin
