/-
Copyright (c) 2026 Scott Harper, Peiran Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Harper, Peiran Wu
-/
import LeanPool.OrderPQ.IsCyclic

lemma ne_iff_eq_of_or_and_ne {α : Type*} {a b c : α} (h1 : a = b ∨ a = c) (h2 : b ≠ c) :
    a ≠ b ↔ a = c :=
  ⟨h1.resolve_left, fun h3 => ne_of_eq_of_ne h3 h2.symm⟩

namespace IsSimpleGroup

variable {G : Type*} [Group G] [IsSimpleGroup G]

@[to_additive]
lemma ne_bot_iff_eq_top_of_normal {H : Subgroup G} (h : H.Normal) : H ≠ ⊤ ↔ H = ⊥ := by
  exact ne_iff_eq_of_or_and_ne (eq_bot_or_eq_top_of_normal H h).symm bot_ne_top.symm

@[to_additive]
lemma monoidHom_injective_or_eq_one {H : Type*} [Group H] (φ : G →* H) :
    Function.Injective φ ∨ φ = 1 := by
  rw [← MonoidHom.ker_eq_bot_iff φ, ← MonoidHom.ker_eq_top_iff (f := φ)]
  exact eq_bot_or_eq_top_of_normal φ.ker φ.normal_ker

@[to_additive]
lemma monoidHom_ne_one_iff_injective {H : Type*} [Group H] (φ : G →* H) :
    φ ≠ 1 ↔ Function.Injective φ := by
  rw [← MonoidHom.ker_eq_bot_iff φ, ne_eq, ← MonoidHom.ker_eq_top_iff (f := φ)]
  exact ne_bot_iff_eq_top_of_normal φ.normal_ker

end IsSimpleGroup

section GroupsOfPrimeOrder

variable {p : ℕ} [hp : Fact p.Prime]
variable {G : Type*} [Group G] (h : Nat.card G = p) {H : Subgroup G}
include h

@[to_additive]
theorem Subgroup.eq_bot_or_eq_top_of_prime_card' :
    H = ⊥ ∨ H = ⊤ := by
  have := Finite.of_card_eq_neZero h
  rw [eq_bot_iff_card, ← card_eq_iff_eq_top, ← Nat.dvd_prime (h ▸ hp.elim)]
  exact card_subgroup_dvd_card H

@[to_additive]
theorem IsSimpleGroup.of_prime_card :
    IsSimpleGroup G := by
  have := Nontrivial.of_card_eq_prime h
  exact ⟨fun H _ => H.eq_bot_or_eq_top_of_prime_card' h⟩

@[to_additive]
lemma Subgroup.ne_top_iff_eq_bot_of_prime_card : H ≠ ⊤ ↔ H = ⊥ := by
  have := Nontrivial.of_card_eq_prime h
  refine ne_iff_eq_of_or_and_ne (eq_bot_or_eq_top_of_prime_card' h).symm bot_ne_top.symm

variable {x : G} (hx : x ≠ 1)
include hx

@[to_additive]
lemma Subgroup.zpowers_eq_top_of_ne_one : Subgroup.zpowers x = ⊤ :=
  eq_bot_or_eq_top_of_prime_card' h |>.resolve_left <| hx ∘ zpowers_eq_bot.mp

@[to_additive]
lemma MonoidHom.end_eq_of_apply_eq (f₁ f₂ : G →* G) (h2 : f₁ x = f₂ x) : f₁ = f₂ :=
  MonoidHom.eq_of_apply_eq (Subgroup.zpowers_eq_top_of_ne_one h hx ▸ Subgroup.mem_top) _ _ h2

@[to_additive]
lemma MulAut.eq_of_apply_eq (f₁ f₂ : G ≃* G) (h2 : f₁ x = f₂ x) : f₁ = f₂ :=
  MulEquiv.eq_of_apply_eq (Subgroup.zpowers_eq_top_of_ne_one h hx ▸ Subgroup.mem_top) _ _ h2

end GroupsOfPrimeOrder
