/-
Copyright (c) 2026 Jineon Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jineon Baek
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Tactic.Cases
import LeanPool.ErdosTuzaValtr.Lib.Core.Rel3

variable {α : Type _}

/-- Local notion for a list whose elements all lie in a finset. -/
protected def List.In (l : List α) (S : Finset α) : Prop :=
  ∀ a : α, a ∈ l → a ∈ S

/-- The image of a finset under the order-dual embedding. -/
protected def Finset.Mirror [LinearOrder α] (S : Finset α) : Finset αᵒᵈ :=
  Finset.image OrderDual.toDual S

/-- The image of a finset of order-dual elements back under `ofDual`. -/
protected def Finset.ofMirror [LinearOrder α] (S : Finset αᵒᵈ) : Finset α :=
  Finset.image OrderDual.ofDual S

namespace List

/-- Flip a list of elements together with its order, landing in the order dual. -/
protected def Mirror (l : List α) : List αᵒᵈ :=
  (List.map OrderDual.toDual l).reverse

/-- Recover a list from its mirror in the order dual. -/
protected def ofMirror (l : List αᵒᵈ) : List α :=
  (List.map OrderDual.ofDual l).reverse

variable (R : α → α → α → Prop)

/-- `Chain3 R a b l` means `R` holds for every three consecutive entries of `a :: b :: l`. -/
inductive Chain3 : α → α → List α → Prop
  | nil {a b : α} : Chain3 a b []
  | cons : ∀ {a b c : α} {l : List α}, R a b c → Chain3 b c l → Chain3 a b (c :: l)

/-- `Chain3' R l` means `R` holds for every three consecutive entries of `l`. -/
def Chain3' : List α → Prop
  | nil => True
  | [_] => True
  | a :: b :: l => Chain3 R a b l

variable {R}

@[simp]
theorem chain3_cons {a b c : α} {l : List α} : Chain3 R a b (c :: l) ↔ R a b c ∧ Chain3 R b c l :=
  ⟨fun p => by cases p with | cons n p => exact ⟨n, p⟩, fun ⟨n, p⟩ => p.cons n⟩

@[simp]
theorem chain3_nil {a b : α} : Chain3 R a b [] := Chain3.nil

instance decidableChain3 [DecidableRel3 R] (a b : α) (l : List α) : Decidable (Chain3 R a b l) := by
  induction l generalizing a b <;> simp only [Chain3.nil, chain3_cons] <;> infer_instance

instance decidableChain3' [DecidableRel3 R] (l : List α) : Decidable (Chain3' R l) := by
  rcases l with _ | ⟨a, _ | ⟨b, l⟩⟩
  · exact instDecidableTrue
  · exact instDecidableTrue
  · exact decidableChain3 a b l

end List
