/-
Copyright (c) 2026 Vincent Trélat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Trélat
-/

import LeanPool.ZFLean.Basic

/-!
# Boolean algebra on `ZFSet`

This file defines the boolean algebra on `ZFSet` and the type of booleans `ZFBool`.
It defines the following operations:
- `not` : negation
- `and` : conjunction
- `or` : disjunction
- `true` : ZF true value
- `false` : ZF false value
- `𝔹` : set of ZF booleans
- `toBool` : conversion from `ZFBool` to `Bool`
- `ofBool` : conversion from `Bool` to `ZFBool`

-/

noncomputable section

/-! ## Preliminary definitions -/

namespace ZFSet

/-- Symmetric difference of two sets, denoted by `Δ`. -/
def symmDiff (p q : ZFSet) : ZFSet := (p \ q) ∪ (q \ p)
/-- Imported ZFLean declaration. -/
infix:70 " Δ " => symmDiff

@[simp]
theorem mem_symmDiff (x p q : ZFSet) : x ∈ p Δ q ↔ (x ∈ p ∧ x ∉ q) ∨ (x ∈ q ∧ x ∉ p) := by
  simp only [symmDiff, mem_union, mem_sdiff]

@[simp]
theorem symmDiff_empty (p : ZFSet) : p Δ ∅ = p := by
  ext x
  simp only [mem_symmDiff, notMem_empty, not_false_eq_true, and_true, false_and, or_false]

theorem symmDiff_comm (p q : ZFSet) : p Δ q = q Δ p := by
  ext x
  simp only [mem_symmDiff]
  exact Or.comm

@[simp]
theorem symmDiff_self (p : ZFSet) : p Δ p = ∅ := by
  ext x
  simp only [mem_symmDiff, and_not_self, or_self, notMem_empty]


/-! ## ZF Boolean Algebra -/

/-- False value defined as the empty set. -/
abbrev zffalse : ZFSet := ∅
/-- True value defined as the singleton containing the empty set. -/
abbrev zftrue : ZFSet := {zffalse}
/-- Set of ZF booleans, defined as the set containing `zffalse` and `zftrue`. -/
abbrev 𝔹 : ZFSet := {zffalse,zftrue}
/-- Type of ZF booleans. -/
abbrev ZFBool := { x // x ∈ 𝔹 }

theorem zftrue_ne_zffalse : zftrue ≠ zffalse := by
  intro h
  rw [ZFSet.ext_iff, zffalse, zftrue] at h
  specialize h ∅
  rw [mem_singleton] at h
  nomatch h.mp rfl

namespace ZFBool

theorem zftrue_mem_𝔹 : zftrue ∈ 𝔹 := by
  rw [mem_insert_iff, mem_singleton]
  exact Or.inr rfl

theorem zffalse_mem_𝔹 : zffalse ∈ 𝔹 := by
  rw [mem_insert_iff, mem_singleton]
  exact Or.inl rfl

lemma _root_.ZFSet.ZFBool.𝔹.nonempty : ZFSet.𝔹 ≠ ∅ := by
  intro h
  rw [ZFSet.ext_iff] at h
  simp only [ZFSet.notMem_empty, iff_false] at h
  nomatch h ZFSet.zffalse (ZFSet.ZFBool.zffalse_mem_𝔹)

/-- False value, lifted on `ZFBool`. -/
abbrev false : ZFBool := ⟨zffalse, zffalse_mem_𝔹⟩
/-- True value, lifted on `ZFBool`. -/
abbrev true : ZFBool := ⟨zftrue, zftrue_mem_𝔹⟩
instance Bool_top : Top ZFBool := ⟨true⟩
instance Bool_bot : Bot ZFBool := ⟨false⟩
theorem top_eq_true : ⊤ = true := rfl
@[simp] theorem bot_eq_false : ⊥ = false := rfl
theorem true_ne_false : (⊤ : ZFBool) ≠ ⊥ := by
  intro h
  rw [top_eq_true, bot_eq_false] at h
  injection h with h
  nomatch zftrue_ne_zffalse h

theorem mem_𝔹_iff (p : ZFSet) : p ∈ 𝔹 ↔ p = zffalse ∨ p = zftrue := by
  rw [mem_insert_iff, mem_singleton]

@[simp]
theorem powerset_false : zffalse.powerset = zftrue := by
  unfold zftrue zffalse
  ext x
  simp only [mem_powerset, mem_singleton]
  apply Iff.intro
  · exact subset_of_empty
  · exact (subset_of_subset_of_eq (fun _ a => a) ·)

/--
The enumeration of the powerset of `𝔹`.
-/
theorem powerset_𝔹_def :
  ZFSet.𝔹.powerset = {∅, {ZFSet.zffalse}, {ZFSet.zftrue}, {ZFSet.zffalse, ZFSet.zftrue}} := by
  ext1 x
  constructor
  · intro h
    rw [ZFSet.mem_powerset, ZFSet.𝔹] at h
    simp_rw [ZFSet.mem_insert_iff, ZFSet.mem_singleton]
    by_cases hx : x = ∅
    · left; exact hx
    · right
      by_cases hx' : ZFSet.zffalse ∈ x
      · rw [← or_assoc, or_comm, ← or_assoc]
        left
        by_cases hx'' : ZFSet.zftrue ∈ x
        · left
          ext1 s
          constructor
          · intro hs; exact h hs
          · intro hs; rcases (ZFSet.ZFBool.mem_𝔹_iff s).mp hs with rfl | rfl <;> assumption
        · right
          ext1 s
          constructor
          · intro hs
            rw [ZFSet.mem_singleton]
            rcases ZFSet.ZFBool.mem_𝔹_iff s |>.mp (h hs) with rfl | rfl <;> trivial
          · intro hs
            rcases ZFSet.mem_singleton.mp hs
            exact hx'
      · by_cases hx'' : ZFSet.zftrue ∈ x
        · right
          left
          ext1 s
          constructor
          · intro hs
            rw [ZFSet.mem_singleton]
            rcases (ZFSet.ZFBool.mem_𝔹_iff s).mp (h hs) with rfl | rfl <;> trivial
          · intro hs
            rcases ZFSet.mem_singleton.mp hs
            exact hx''
        · simp_rw [ZFSet.subset_def, ZFSet.ZFBool.mem_𝔹_iff] at h
          obtain ⟨w, hw⟩ := nonempty_exists_iff.mp hx
          rcases h hw with rfl | rfl <;> contradiction
  · intro hx
    simp_rw [ZFSet.mem_insert_iff, ZFSet.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> rw [ZFSet.mem_powerset]
    · exact ZFSet.empty_subset ZFSet.𝔹
    · intro _ hx
      rw [ZFSet.ZFBool.mem_𝔹_iff]
      rcases ZFSet.mem_singleton.mp hx
      left; rfl
    · intro _ hx
      rw [ZFSet.ZFBool.mem_𝔹_iff]
      rcases ZFSet.mem_singleton.mp hx
      right; rfl

/-- Boolean negation, defined as the symmetric difference with `true`. -/
protected abbrev not (p : ZFBool) : ZFBool := ⟨true Δ p.1, by
  let ⟨p, hp⟩ := p
  rw [mem_𝔹_iff] at hp ⊢
  rcases hp with rfl | rfl
  · right
    exact symmDiff_empty _
  · left
    exact symmDiff_self _⟩

/-- Cases elimination for `ZFBool`. -/
@[cases_eliminator]
def casesOn {motive : ZFBool → Sort _}
  (p : ZFBool)
  (false : motive ⊥)
  (true : motive ⊤) : motive p := by
  obtain ⟨P, hP⟩ := p
  have := mem_𝔹_iff P |>.mp hP
  by_cases h : P = zffalse
  · subst h
    exact false
  · have := Or.resolve_left this h
    subst this
    exact true

/-- Boolean conjunction, defined as set intersection. -/
protected abbrev and (p q : ZFBool) : ZFBool :=
  let ⟨P, hP⟩ := p
  let ⟨Q, hQ⟩ := q
  ⟨P ∩ Q, by
    rw [mem_𝔹_iff]
    rw [mem_𝔹_iff] at hP hQ
    cases hP <;> cases hQ <;> subst_eqs
    · apply Or.inl
      ext1
      rw [mem_inter, and_self]
    · apply Or.inl
      ext1
      simp only [mem_inter, notMem_empty, false_and]
    · apply Or.inl
      ext1
      simp only [mem_inter,  notMem_empty, and_false]
    · apply Or.inr
      ext1
      simp only [mem_inter, and_self]⟩
/-- Imported ZFLean declaration. -/
infixl:55 " ⋀ " => ZFBool.and
/-- Imported ZFLean declaration. -/
protected abbrev or (p q : ZFBool) : ZFBool :=
  let ⟨P, hP⟩ := p
  let ⟨Q, hQ⟩ := q
  ⟨P ∪ Q,
    by
    rw [mem_𝔹_iff]
    rw [mem_𝔹_iff] at hP hQ
    cases hP <;> cases hQ <;> subst_eqs
    · apply Or.inl
      ext1
      rw [mem_union, or_self]
    · apply Or.inr
      ext1
      simp only [mem_union, notMem_empty, mem_singleton, false_or]
    · apply Or.inr
      ext1
      simp only [mem_union, notMem_empty, or_false]
    · apply Or.inr
      ext1
      simp only [mem_union, or_self]⟩
/-- Imported ZFLean declaration. -/
infixl:55 " ⋁ " => ZFBool.or

/-! ### Boolean algebra -/

theorem not_true_eq_false : ZFBool.not ⊤ = ⊥ := by
  rw [Subtype.mk.injEq]
  ext1
  rw [mem_symmDiff]
  constructor
  · rintro (⟨l, r⟩ | ⟨l, r⟩) <;> nomatch r l
  · intro h
    nomatch notMem_empty _ h

theorem not_false_eq_true : ZFBool.not ⊥ = ⊤ := by
  rw [Subtype.mk.injEq]
  ext1
  rw [mem_symmDiff]
  constructor
  · rintro (⟨l, r⟩ | ⟨l, r⟩)
    · exact l
    · nomatch notMem_empty _ l
  · intro h
    left
    exact ⟨h, notMem_empty _⟩

theorem and_comm (p q : ZFBool) : p ⋀ q = q ⋀ p := by
  obtain ⟨P, hP⟩ := p
  obtain ⟨Q, hQ⟩ := q
  rw [Subtype.mk.injEq]
  ext1
  repeat rw [mem_inter]
  exact And.comm

theorem and_assoc (p q r : ZFBool) : p ⋀ q ⋀ r = p ⋀ (q ⋀ r) := by
  obtain ⟨P, hP⟩ := p
  obtain ⟨Q, hQ⟩ := q
  obtain ⟨R, hR⟩ := r
  rw [Subtype.mk.injEq]
  ext1
  repeat rw [mem_inter]
  exact _root_.and_assoc

theorem and_true (p : ZFBool) : p ⋀ ⊤ = p := by
  obtain ⟨P, hP⟩ := p
  rw [Subtype.mk.injEq]
  ext1
  rw [mem_inter]
  rw [mem_𝔹_iff] at hP
  rw [and_iff_left_iff_imp]
  intro h
  cases hP
  · subst_eqs
    simp only [notMem_empty] at h
  · subst_eqs
    assumption

@[simp]
theorem and_false (p : ZFBool) : p ⋀ ⊥ = ⊥ := by
  obtain ⟨P, hP⟩ := p
  ext
  rw [mem_inter]
  rw [mem_𝔹_iff] at hP
  rcases hP with rfl | rfl
  · exact and_iff_left_of_imp id
  · constructor
    · rintro ⟨_, h⟩
      exact h
    · intro h
      nomatch notMem_empty _ h

theorem and_iff (p q : ZFBool) : p ⋀ q = ⊤ ↔ p = ⊤ ∧ q = ⊤ := by
  constructor
  · intro h
    cases q using casesOn with
    | false =>
      rw [and_false] at h
      nomatch true_ne_false h.symm
    | true => exact ⟨and_true p ▸ h, rfl⟩
  · rintro (⟨rfl,rfl⟩)
    rw [and_true]

theorem and_intro (p q : ZFBool) : p = ⊤ ∧ q = ⊤ → p ⋀ q = ⊤ :=
  and_iff p q |>.mpr

theorem or_comm (p q : ZFBool) : p ⋁ q = q ⋁ p := by
  obtain ⟨P, hP⟩ := p
  obtain ⟨Q, hQ⟩ := q
  rw [Subtype.mk.injEq]
  ext1
  repeat rw [mem_union]
  exact Or.comm

theorem or_assoc (p q r : ZFBool) : p ⋁ q ⋁ r = p ⋁ (q ⋁ r) := by
  obtain ⟨P, hP⟩ := p
  obtain ⟨Q, hQ⟩ := q
  obtain ⟨R, hR⟩ := r
  rw [Subtype.mk.injEq]
  ext1
  repeat rw [mem_union]
  exact _root_.or_assoc

theorem or_true (p : ZFBool) : p ⋁ ⊤ = ⊤ := by
  obtain ⟨P, hP⟩ := p
  rw [Subtype.mk.injEq]
  ext1
  rw [mem_union]
  rw [mem_𝔹_iff] at hP
  cases hP <;> subst_eqs
  · simp only [notMem_empty, mem_singleton, false_or, top_eq_true]
  · exact or_iff_left_of_imp id

theorem or_false (p : ZFBool) : p ⋁ ⊥ = p := by
  obtain ⟨P, hP⟩ := p
  rw [Subtype.mk.injEq]
  ext1
  rw [mem_union]
  rw [mem_𝔹_iff] at hP
  cases hP <;> subst_eqs
  · rw [or_self]
  · simp only [notMem_empty, _root_.or_false]

theorem or_iff (p q : ZFBool) : p ⋁ q = ⊤ ↔ p = ⊤ ∨ q = ⊤ := by
  constructor
  · intro h
    cases p using casesOn with
    | false =>
      rw [or_comm, or_false] at h
      exact Or.inr h
    | true => exact Or.inl rfl
  · intro h
    rcases h with rfl | rfl
    · rw [or_comm, or_true]
    · rw [or_true]

theorem or_intro (p q : ZFBool) : p = ⊤ ∨ q = ⊤ → p ⋁ q = ⊤ :=
  or_iff p q |>.mpr

open Classical in
/-- Conversion of `ZFBool` to `Lean.Bool`. -/
def toBool : ZFBool → Bool
  | ⟨b, hb⟩ =>
    if h : b = zftrue then Bool.true
    else if h' : b = zffalse then Bool.false
    else False.elim (by rcases (ZFBool.mem_𝔹_iff b |>.mp hb) <;> contradiction)

theorem toBool_false : toBool ⊥ = Bool.false := by
  rw [toBool]
  split_ifs with h h'
  · nomatch zftrue_ne_zffalse h.symm
  · rfl
  · nomatch h'

theorem toBool_true : toBool ⊤ = Bool.true := by
  rw [toBool]
  split_ifs with h h'
  · rfl
  · nomatch h rfl
  · nomatch h'

theorem toBool_and (p q : ZFBool) : (p ⋀ q).toBool = (p.toBool && q.toBool) := by
  cases p <;> cases q
  · rw [and_false, toBool_false, Bool.false_and]
  · rw [and_true, toBool_true, toBool_false, Bool.false_and]
  · rw [and_false, toBool_true, toBool_false, Bool.and_false]
  · rw [and_true, toBool_true, Bool.true_and]

theorem toBool_or (p q : ZFBool) : (p ⋁ q).toBool = (p.toBool || q.toBool) := by
  cases p <;> cases q
  · rw [or_false, toBool_false, Bool.false_or]
  · rw [or_true, toBool_true, toBool_false, Bool.or_true]
  · rw [or_false, toBool_true, toBool_false, Bool.true_or]
  · rw [or_true, toBool_true, Bool.true_or]

theorem toBool_not (p : ZFBool) : toBool p.not = ¬ p.toBool := by
  cases p
  · rw [not_false_eq_true, toBool_true, toBool_false, Bool.false_eq_true, Bool.coe_sort_true]
    exact _root_.not_false_eq_true.symm
  · rw [not_true_eq_false, toBool_false, toBool_true, Bool.coe_false]
    exact eq_false (fun h => h rfl) |>.symm

theorem not_top_iff_bot {P : ZFBool} : P ≠ ⊤ ↔ P = ⊥ := by
  constructor
  · intro
    cases P <;> trivial
  · intro _ h
    subst P
    injections h
    nomatch zftrue_ne_zffalse h.symm

theorem not_bot_iff_top {P : ZFBool} : P ≠ ⊥ ↔ P = ⊤ := by
  constructor
  · intro
    cases P <;> trivial
  · intro _ h
    subst P
    injections h
    nomatch zftrue_ne_zffalse h

/-- Conversion of `Lean.Bool` to `ZFBool` -/
def ofBool : Bool → ZFBool
  | .true  => ⟨zftrue, ZFBool.zftrue_mem_𝔹⟩
  | .false => ⟨zffalse, ZFBool.zffalse_mem_𝔹⟩

theorem mem_ofBool_𝔹 (b : Bool) : (ofBool b).val ∈ 𝔹 := by
  unfold 𝔹
  rcases b <;> simp [ofBool]

theorem sub_ofBool_singleton_𝔹 (b : Bool) : {(ofBool b).val} ⊆ 𝔹 := by
  intro
  rw [mem_singleton]
  rintro rfl
  exact mem_ofBool_𝔹 b

theorem to_Bool_ofBool (b : Bool) : ZFBool.toBool (ofBool b) = b := by
  cases b <;> rw [ofBool, ZFBool.toBool]
  · split_ifs with h
    · nomatch zftrue_ne_zffalse.symm h
    · rfl
    · generalize_proofs
      contradiction
  · split_ifs with h
    · rfl
    · contradiction
    · generalize_proofs
      contradiction

theorem of_Bool_toBool (b : ZFBool) : ofBool b.toBool = b := by
  obtain ⟨b, hb⟩ := b
  rw [ZFBool.toBool, ofBool.eq_def]
  split_ifs with h <;> (first | subst b | contradiction) <;> trivial

theorem ofBool_decide_eq_true_iff {P : Prop} [Decidable P] : ofBool (decide P) = ⊤ ↔ P := by
  constructor
  · intro h
    cases hP : decide P with
    | false =>
      rw [hP] at h
      unfold ofBool at h
      injection h with h
      nomatch zftrue_ne_zffalse h.symm
    | true => exact decide_eq_true_eq.mp hP
  · intro h
    cases hP : decide P with
    | false =>
      rw [Bool.decide_false_iff] at hP
      contradiction
    | true => rfl

theorem ofBool_decide_eq_false_iff {P : Prop} [Decidable P] : ofBool (decide P) = ⊥ ↔ ¬P := by
  constructor
  · intro h
    cases hP : decide P with
    | false => exact decide_eq_false_iff_not.mp hP
    | true =>
      rw [hP] at h
      unfold ofBool at h
      injection h with h
      nomatch zftrue_ne_zffalse h
  · intro h
    cases hP : decide P with
    | false => rfl
    | true =>
      rw [Bool.decide_iff] at hP
      contradiction

/-- The equivalence between ZF booleans and Lean booleans. -/
def instEquivBool : ZFBool ≃ Bool where
  toFun := toBool
  invFun := ofBool
  left_inv := of_Bool_toBool
  right_inv := to_Bool_ofBool

instance : Coe Bool ZFBool := ⟨ofBool⟩
instance : Coe ZFBool Bool := ⟨toBool⟩

end ZFBool



namespace ZFBool

theorem and_coe (p q : ZFBool) : p ⋀ q = ((p : Bool) && (q : Bool)) := by
  rw [← toBool_and, of_Bool_toBool]
theorem or_coe (p q : ZFBool) : p ⋁ q = ((p : Bool) || (q : Bool)) := by
  rw [← toBool_or, of_Bool_toBool]
theorem not_coe (p : ZFBool) : ZFBool.not p = ¬(p : Bool) := by
  rw [← toBool_not]

theorem and_or_distrib_left (p q r : ZFBool) : p ⋀ (q ⋁ r) = (p ⋀ q) ⋁ (p ⋀ r) := by
  rw [and_coe, or_coe, and_coe, and_coe, or_coe]
  iterate 3 rw [to_Bool_ofBool]
  rw [Bool.and_or_distrib_left]

end ZFBool

end ZFSet

end
