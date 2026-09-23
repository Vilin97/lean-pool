/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

module

public import Mathlib.Data.Vector.Basic
public import Mathlib.Logic.Relation

/-!
# Helper Lemmas about the Kleene Star

Nothing here is specific about PDL, but we prove some useful results about the reflexive-transitive
closure `ReflTransGen` and the transitive closure `TransGen`.
-/

@[expose] public section

namespace PDL

/-- A version of `Relation.ReflTransGen.cases_tail` also giving (in)equalities. -/
theorem ReflTransGen.cases_tail_eq_neq {r : α → α → Prop} (h : Relation.ReflTransGen r x z) :
    x = z ∨ (x ≠ z ∧ ∃ y, x ≠ y ∧ r x y ∧ Relation.ReflTransGen r y z) := by
  induction h using Relation.ReflTransGen.head_induction_on
  · left
    rfl
  case head a b a_r_b b_r_z IH_b_z =>
    cases Classical.em (a = b)
    case inl a_is_b =>
      subst a_is_b
      cases IH_b_z
      case inl a_is_z =>
        left
        assumption
      case inr IH =>
        right
        assumption
    case inr a_neq_b =>
      cases IH_b_z
      case inl a_is_z =>
        subst a_is_z
        right
        constructor
        · assumption
        · use b
      case inr IH =>
        cases Classical.em (a = z)
        · left
          assumption
        · right
          constructor
          · assumption
          · use b

/-- `ReflTransGen r a b` implies `∃ x₀ ... xₙ, a = x₀ ∧ r x₀ x₁ ∧ ... ∧ xₙ = b`.
Similar to `List.exists_chain_of_relationReflTransGen`. -/
theorem ReflTransGen.to_finitelyManySteps {r : α → α → Prop} (h : Relation.ReflTransGen r x z) :
    ∃ (n : ℕ) (ys : List.Vector α n.succ),
      x = ys.head ∧ z = ys.last ∧ ∀ i : Fin n, r (ys.get i.castSucc) (ys.get (i.succ)) := by
  induction h using Relation.ReflTransGen.head_induction_on
  case refl =>
    use 0, List.Vector.cons z List.Vector.nil
    aesop
  case head a b a_r_b b_rS_z IH_b_z =>
    rcases IH_b_z with ⟨m, zs, b_is_head_zs, z_is_last_zs, zs_steps⟩
    use m + 1
    use a ::ᵥ zs
    simp only [List.Vector.head_cons, List.Vector.get_cons_succ, true_and]
    constructor
    · aesop
    · intro i
      induction i using Fin.induction
      all_goals aesop

/-- `a = x₀ ∧ r x₀ x₁ ∧ ... ∧ xₙ = b` implies `ReflTransGen r a b`.
Similar to `List.relationReflTransGen_of_exists_chain` in mathlib. -/
theorem ReflTransGen.from_finitelyManySteps (r : α → α → Prop) {n : ℕ} :
    ∀ (x z : α) (ys : List.Vector α (Nat.succ n)),
      (x = ys.head ∧ z = ys.last ∧ ∀ i : Fin n, r (ys.get i.castSucc) (ys.get (i.succ)))
        → Relation.ReflTransGen r x z := by
  induction n
  case zero =>
    rintro x z ys ⟨x_is_head, z_is_last, _⟩
    have : x = z := by
      subst_eqs
      simp_all [List.Vector.head, List.Vector.last, Fin.last]
    rw [this]
  case succ n IH =>
    rintro x z ys ⟨x_is_head, z_is_last, steprel⟩
    let y := ys.tail.head
    rw [Relation.ReflTransGen.cases_head_iff]
    right
    use y
    constructor
    · specialize steprel 0
      simp only [Fin.castSucc_zero, List.Vector.get_zero, Fin.succ_zero_eq_one] at steprel
      rw [← x_is_head] at steprel
      convert steprel
      cases ys using List.Vector.inductionOn
      case cons y ys hyp =>
        cases ys using List.Vector.inductionOn
        rfl
    · apply IH y z ys.tail
      unfold y
      simp only [List.Vector.get_tail_succ, true_and]
      constructor
      · have sameLast : ys.tail.last = ys.last := by
          cases ys using List.Vector.inductionOn
          case cons y ys hyp =>
            cases ys using List.Vector.inductionOn
            rfl
        rw [sameLast]
        exact z_is_last
      · intro i
        specialize steprel i.succ
        induction i
        all_goals aesop

/-- `ReflTransGen r a b` is equivalent to `∃ x₀ ... xₙ, a = x₀ ∧ r x₀ x₁ ∧ ... ∧ r xₙ = b` -/
theorem ReflTransGen.iff_finitelyManySteps (r : α → α → Prop) (x z : α) :
    Relation.ReflTransGen r x z ↔
      ∃ (n : ℕ) (ys : List.Vector α n.succ),
        x = ys.head ∧ z = ys.last ∧ ∀ i : Fin n, r (ys.get i.castSucc) (ys.get (i.succ)) :=
  ⟨ReflTransGen.to_finitelyManySteps,
  fun ⟨_, ys, x_is_head, z_is_last, rhs⟩ =>
    ReflTransGen.from_finitelyManySteps r x z ys ⟨x_is_head, z_is_last, rhs⟩⟩

theorem Relation.ReflTransGen_or_left {r r' : α → α → Prop} {a b : α} :
    Relation.ReflTransGen r a b
    → Relation.ReflTransGen (fun x y => r x y ∨ r' x y) a b := by
  intro a_b
  induction a_b
  case refl => exact _root_.Relation.ReflTransGen.refl
  case tail _ b_c IH => exact _root_.Relation.ReflTransGen.tail IH (Or.inl b_c)

theorem Relation.ReflTransGen_or_right {r r' : α → α → Prop} {a b : α} :
    Relation.ReflTransGen r a b
    → Relation.ReflTransGen (fun x y => r' x y ∨ r x y) a b := by
  intro a_b
  induction a_b
  case refl => exact _root_.Relation.ReflTransGen.refl
  case tail _ b_c IH => exact _root_.Relation.ReflTransGen.tail IH (Or.inr b_c)

theorem Relation.ReflTransGen_imp {r r' : α → α → Prop} {a b : α} :
    (∀ x y, r x y → r' x y)
    → Relation.ReflTransGen r a b
    → Relation.ReflTransGen r' a b := by
  intro hyp a_b
  induction a_b
  case refl => exact _root_.Relation.ReflTransGen.refl
  case tail _ b_c IH => exact _root_.Relation.ReflTransGen.tail IH (hyp _ _ b_c)

theorem Relation.TransGen_or_left {r r' : α → α → Prop} {a b : α} :
    Relation.TransGen r a b
    → Relation.TransGen (fun x y => r x y ∨ r' x y) a b := by
  intro a_b
  induction a_b
  case single => apply _root_.Relation.TransGen.single; left; assumption
  case tail _ b_c IH => exact _root_.Relation.TransGen.tail IH (Or.inl b_c)

theorem Relation.TransGen_or_right {r r' : α → α → Prop} {a b : α} :
    Relation.TransGen r a b
    → Relation.TransGen (fun x y => r' x y ∨ r x y) a b := by
  intro a_b
  induction a_b
  case single => apply _root_.Relation.TransGen.single; right; assumption
  case tail _ b_c IH => exact _root_.Relation.TransGen.tail IH (Or.inr b_c)

theorem Relation.TransGen_imp {r r' : α → α → Prop} {a b : α} :
    (∀ x y, r x y → r' x y)
    → Relation.TransGen r a b
    → Relation.TransGen r' a b := by
  intro hyp a_b
  induction a_b
  case single => apply _root_.Relation.TransGen.single; apply hyp; assumption
  case tail _ b_c IH => exact _root_.Relation.TransGen.tail IH (hyp _ _ b_c)

theorem Relation.TransGen_of_ReflTransGen {α : Type} {r : α → α → Prop}
  {a b : α} (h : Relation.ReflTransGen r a b) (hne : a ≠ b) : Relation.TransGen r a b :=
  by induction h
     case refl => contradiction
     case tail c b a_c c_b ih => cases eq_or_ne a c with
      | inl a_eq_c => apply Relation.TransGen.single
                      simp_all
      | inr a_ne_c => apply Relation.TransGen.tail (ih a_ne_c) c_b

lemma Relation.TransGen.flip_iff (α : Type) {r : α → α → Prop} {a b : α} :
    (Relation.TransGen (flip r)) a b ↔ (Relation.TransGen r) b a := by
  exact @Relation.transGen_swap α r a b

end PDL
