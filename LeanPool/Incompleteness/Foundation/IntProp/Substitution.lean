/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.IntProp.Formula

/-! # Substitution -/


namespace LO
namespace IntProp

/-- Imported declaration from the Incompleteness formalization. -/
abbrev Substitution (α) := α → (Formula α)

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.IntProp.Substitution.id {α} : Substitution α := fun a => .atom a

namespace Formula

variable {φ ψ : Formula α} {s : Substitution α}

/-- Imported declaration from the Incompleteness formalization. -/
def subst (s : Substitution α) : Formula α → Formula α
  | atom a  => (s a)
  | ⊥       => ⊥
  | φ ⋏ ψ   => φ.subst s ⋏ ψ.subst s
  | φ ⋎ ψ   => φ.subst s ⋎ ψ.subst s
  | φ ==> ψ   => φ.subst s ==> ψ.subst s

/-- Imported declaration from the Incompleteness formalization. -/
notation:80 φ "⟦" s "⟧" => Formula.subst s φ

@[simp] lemma subst_atom {a} : (.atom a)⟦s⟧ = s a := rfl

@[simp] lemma subst_bot : ⊥⟦s⟧ = ⊥ := rfl

@[simp] lemma subst_top : ⊤⟦s⟧ = ⊤ := rfl

@[simp] lemma subst_imp : (φ ==> ψ)⟦s⟧ = φ⟦s⟧ ==> ψ⟦s⟧ := rfl

@[simp] lemma subst_neg : (∼φ)⟦s⟧ = ∼(φ⟦s⟧) := rfl

@[simp] lemma subst_and : (φ ⋏ ψ)⟦s⟧ = φ⟦s⟧ ⋏ ψ⟦s⟧ := rfl

@[simp] lemma subst_or : (φ ⋎ ψ)⟦s⟧ = φ⟦s⟧ ⋎ ψ⟦s⟧ := rfl

@[simp] lemma subst_iff : (φ <=> ψ)⟦s⟧ = (φ⟦s⟧ <=> ψ⟦s⟧) := rfl

end Formula


@[simp] lemma subst_id {φ : Formula α} :
    φ⟦.id⟧ = φ := by induction φ using Formula.rec' <;> simp_all;

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.IntProp.Substitution.comp (s₁ s₂ : Substitution α) : Substitution α :=
  fun a => (s₁ a)⟦s₂⟧
/-- Imported declaration from the Incompleteness formalization. -/
infixr:80 " ∘ " => Substitution.comp

@[simp]
lemma subst_comp {s₁ s₂ : Substitution α} {φ : Formula α} : φ⟦s₁ ∘ s₂⟧ = φ⟦s₁⟧⟦s₂⟧ := by
  induction φ using Formula.rec' <;> simp_all [Substitution.comp];

/-- Imported declaration from the Incompleteness formalization. -/
class SubstitutionClosed (S : Set (Formula α)) where
  closed : ∀ φ ∈ S, (∀ s : Substitution α, φ⟦s⟧ ∈ S)


end IntProp
end LO
