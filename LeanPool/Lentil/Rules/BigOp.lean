/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
import LeanPool.Lentil.Rules.Basic

/-! Theorems about big operators (e.g., `⋀`, `⋁`). -/

open Classical LentilLib

namespace TLA

section bigop

variable {α : Type u} {β : Type v} (f g : β → pred α) (l : List β)

-- FIXME: currently we only have the definition of `fold`, but we do not specify
-- its result, so for each `Foldable` instance, we need to repeat the following proofs!
-- maybe we should revise the definitions of `bigwedge` and `bigvee` (see `Lentil/Basic.lean`)
-- also, can we get rid of the repetition?

section bigwedge

@[tlasimp]
theorem bigwedge_list_nil : (⋀ x ∈ [], (f x)) =tla= (⊤) := rfl

@[tlasimp]
theorem bigwedge_list_cons (b : β) : (⋀ x ∈ (b :: l), (f x)) =tla= ((f b) ∧ ⋀ x ∈ l, (f x)) := rfl

@[tlasimp]
theorem bigwedge_list_append (l1 l2 : List β) : (⋀ x ∈ (l1 ++ l2), (f x)) =tla= ((⋀ x ∈ l1, (f x)) ∧ ⋀ x ∈ l2, (f x)) := by
  simp only [tlaBigwedge, Foldable.fold, List.foldr_append]
  simp only [← List.foldr_map]
  generalize (l1.map f) = l1'; clear l1
  generalize (List.foldr tlaAnd [tlafml|⊤] (List.map f l2)) = p; clear l2
  -- CHECK Why so hard? No existing lemma?
  induction l1' with
  | nil => simp [true_and]
  | cons b l1' ih => simp [and_assoc, ih]

theorem bigwedge_forall_list : (⋀ x ∈ l, (f x)) =tla= (∀ x, (⌞ x ∈ l ⌟ → (f x))) := by
  induction l with
  | nil => funext e; tlaUnfoldSimp
  | cons b l ih =>
    simp [tlasimp, ih]
    funext e; tlaUnfoldSimp

theorem bigwedge_forall_fintype_list : (⋀ x ∈ l, (f x)) =tla= (∀ x : Fin l.length, (f l[x])) := by
  rw [bigwedge_forall_list]
  funext e; tlaUnfoldSimp; apply List.mem_forall_iff_fin_index

omit f in
theorem bigwedge_forall_swap {γ : Type w} (f : β → γ → pred α) : (∀ c : γ, (⋀ x ∈ l, (f x c))) =tla= (⋀ x ∈ l, ∀ c : γ, ((f x c))) := by
  simp only [bigwedge_forall_fintype_list]; apply TLA.forall_comm

theorem bigwedge_inner_and_split : (⋀ x ∈ l, (f x) ∧ (g x)) =tla= ((⋀ x ∈ l, (f x)) ∧ (⋀ x ∈ l, (g x))) := by
  (repeat rw [bigwedge_forall_list]); funext e; tlaUnfoldSimp; aesop

theorem always_bigwedge : (□ ⋀ x ∈ l, (f x)) =tla= (⋀ x ∈ l, □ (f x)) := by
  (repeat rw [bigwedge_forall_list]); funext e; tlaUnfoldSimp; aesop

theorem eventually_always_bigwedge_distrib : (◇ □ ⋀ x ∈ l, (f x)) =tla= (⋀ x ∈ l, ◇ □ (f x)) := by
  induction l with
  | nil => funext e; tlaUnfoldSimp
  | cons x l ih => simp [tlasimp, eventually_always_and_distrib, ih]

end bigwedge

section bigvee

@[tlasimp]
theorem bigvee_list_nil : (⋁ x ∈ [], (f x)) =tla= (⊥) := rfl

@[tlasimp]
theorem bigvee_list_cons (b : β) : (⋁ x ∈ (b :: l), (f x)) =tla= ((f b) ∨ ⋁ x ∈ l, (f x)) := rfl

theorem bigvee_exists_list : (⋁ x ∈ l, (f x)) =tla= (∃ x, (⌞ x ∈ l ⌟ ∧ (f x))) := by
  induction l with
  | nil => funext e; tlaUnfoldSimp
  | cons b l ih =>
    simp [tlasimp, ih]
    funext e; tlaUnfoldSimp

theorem bigvee_exists_fintype_list : (⋁ x ∈ l, (f x)) =tla= (∃ x : Fin l.length, (f l[x])) := by
  rw [bigvee_exists_list]
  funext e; tlaUnfoldSimp; apply List.mem_exists_iff_fin_index

theorem bigvee_and_distrib (p : pred α) : (p ∧ ⋁ x ∈ l, (f x)) =tla= (⋁ x ∈ l, p ∧ (f x)) := by
  repeat rw [bigvee_exists_list]
  funext e; tlaUnfoldSimp; aesop

end bigvee

theorem bigwedge_bigvee_match : ((⋀ x ∈ l, (f x)) ∧ (⋁ x ∈ l, (g x))) |-tla- (⋁ x ∈ l, (f x) ∧ (g x)) := by
  rw [bigwedge_forall_list, bigvee_exists_list, bigvee_exists_list]; tlaUnfoldSimp; aesop

end bigop

end TLA
