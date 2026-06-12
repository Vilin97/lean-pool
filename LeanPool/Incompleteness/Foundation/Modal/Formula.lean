/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Logic.HilbertStyle.Lukasiewicz
import LeanPool.Incompleteness.Foundation.Vorspiel.Collection
import LeanPool.Incompleteness.Foundation.Modal.LogicSymbol

/-! # Formula -/


namespace LO
namespace Modal

/-- Imported declaration from the Incompleteness formalization. -/
inductive Formula (α : Type u) : Type u where
  | atom   : α → Formula α
  | falsum : Formula α
  | imp    : Formula α → Formula α → Formula α
  | box    : Formula α → Formula α
  deriving DecidableEq

namespace Formula

/-- Imported declaration from the Incompleteness formalization. -/
abbrev neg (φ : Formula α) : Formula α := imp φ falsum

/-- Imported declaration from the Incompleteness formalization. -/
abbrev verum : Formula α := imp falsum falsum

/-- Imported declaration from the Incompleteness formalization. -/
abbrev top : Formula α := imp falsum falsum

/-- Imported declaration from the Incompleteness formalization. -/
abbrev or (φ ψ : Formula α) : Formula α := imp (neg φ) ψ

/-- Imported declaration from the Incompleteness formalization. -/
abbrev and (φ ψ : Formula α) : Formula α := neg (imp φ (neg ψ))

/-- Imported declaration from the Incompleteness formalization. -/
abbrev dia (φ : Formula α) : Formula α := neg (box (neg φ))

variable {α : Type u}

instance : BasicModalLogicalConnective (Formula α) where
  tilde := neg
  arrow := imp
  wedge := and
  vee := or
  top := verum
  bot := falsum
  box := box
  dia := dia

instance : LukasiewiczAbbrev (Formula α) where
  top := rfl
  neg := rfl
  or := rfl
  and := rfl
instance : DiaAbbrev (Formula α) := ⟨rfl⟩

section «lp_section_1»

variable [ToString α]

/-- Imported declaration from the Incompleteness formalization. -/
def toStr : Formula α → String
  -- | ⊤       => "\\top"
  | ⊥       => "\\bot"
  | atom a  => "{" ++ toString a ++ "}"
  | □φ      => "\\Box " ++ toStr φ
  -- | ◇φ      => "\\Diamond " ++ toStr φ
  | φ ==> ψ   => "\\left(" ++ toStr φ ++ " \\to " ++ toStr ψ ++ "\\right)"
  -- | φ ⋏ ψ   => "\\left(" ++ toStr φ ++ " \\land " ++ toStr ψ ++ "\\right)"
  -- | φ ⋎ ψ   => "\\left(" ++ toStr φ ++ " \\lor "   ++ toStr ψ ++ "\\right)"

instance : Repr (Formula α) := ⟨fun t _ => toStr t⟩

instance : ToString (Formula α) := ⟨toStr⟩

instance : Coe α (Formula α) := ⟨atom⟩

end «lp_section_1»

-- @[simp] lemma neg_top : ∼(⊤ : Formula α) = ⊥ := rfl

@[simp] lemma neg_bot : ∼(⊥ : Formula α) = ⊤ := rfl

-- @[simp] lemma neg_atom (a : α) : ∼(atom a) = natom a := rfl

-- @[simp] lemma neg_natom (a : α) : ∼(natom a) = atom a := rfl

-- @[simp] lemma neg_and (φ ψ : Formula α) : ∼(φ ⋏ ψ) = ∼φ ⋎ ∼ψ := rfl

-- @[simp] lemma neg_or (φ ψ : Formula α) : ∼(φ ⋎ ψ) = ∼φ ⋏ ∼ψ := rfl

-- @[simp] lemma neg_neg' (φ : Formula α) : ∼∼φ = φ := neg_neg φ

-- @[simp] lemma neg_box (φ : Formula α) : ∼(□φ) = ◇(∼φ) := rfl

-- @[simp] lemma neg_dia (φ : Formula α) : ∼(◇φ) = □(∼φ) := rfl

/-
@[simp] lemma neg_inj (φ ψ : Formula α) : ∼φ = ∼ψ ↔ φ = ψ := by
  constructor
  · intro h; simpa using congr_arg (∼·) h
  · exact congr_arg _
-/

lemma or_eq (φ ψ : Formula α) : or φ ψ = φ ⋎ ψ := rfl

lemma and_eq (φ ψ : Formula α) : and φ ψ = φ ⋏ ψ := rfl

lemma imp_eq (φ ψ : Formula α) : imp φ ψ = φ ==> ψ := rfl

lemma neg_eq (φ : Formula α) : neg φ = ∼φ := rfl

lemma box_eq (φ : Formula α) : box φ = □φ := rfl

lemma dia_eq (φ : Formula α) : dia φ = ◇φ := rfl

lemma iff_eq (φ ψ : Formula α) : φ <=> ψ = (φ ==> ψ) ⋏ (ψ ==> φ) := rfl

lemma falsum_eq : (falsum : Formula α) = ⊥ := rfl

@[simp] lemma and_inj (φ₁ ψ₁ φ₂ ψ₂ : Formula α) :
    φ₁ ⋏ φ₂ = ψ₁ ⋏ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by
  simp[Wedge.wedge]

@[simp] lemma or_inj (φ₁ ψ₁ φ₂ ψ₂ : Formula α) :
    φ₁ ⋎ φ₂ = ψ₁ ⋎ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by
  simp[Vee.vee]

@[simp] lemma imp_inj (φ₁ ψ₁ φ₂ ψ₂ : Formula α) :
    φ₁ ==> φ₂ = ψ₁ ==> ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by
  simp[Arrow.arrow]

@[simp] lemma neg_inj (φ ψ : Formula α) : ∼φ = ∼ψ ↔ φ = ψ := by simp [NegAbbrev.neg];

/-
instance : ModalDeMorgan (Formula α) where
  verum := rfl
  falsum := rfl
  and := by simp
  or := by simp
  imply := by simp[imp_eq]
  neg := by simp
  dia := by simp
  box := by simp
-/

/-- Formula complexity -/
def complexity : Formula α → ℕ
| atom _  => 0
| ⊥       => 0
| φ ==> ψ   => max φ.complexity ψ.complexity + 1
| □φ   => φ.complexity + 1

/-- Max numbers of `□` -/
def degree : Formula α → Nat
  | atom _ => 0
  | ⊥ => 0
  | φ ==> ψ => max φ.degree ψ.degree
  | □φ => φ.degree + 1

@[simp] lemma degree_neg (φ : Formula α) :
    degree (∼φ) = degree φ := by
  induction φ <;> simp_all [degree]
@[simp] lemma degree_imp (φ ψ : Formula α) :
    degree (φ ==> ψ) = max (degree φ) (degree ψ) := by
  simp [degree]

/-- Imported declaration from the Incompleteness formalization. -/
@[elab_as_elim]
def cases' {C : Formula α → Sort w}
    (hfalsum : C ⊥)
    (hatom : ∀ a : α, C (atom a))
    (himp     : ∀ (φ ψ : Formula α), C (φ ==> ψ))
    (hbox    : ∀ (φ : Formula α), C (□φ))
    : (φ : Formula α) → C φ
  | ⊥       => hfalsum
  | atom a  => hatom a
  | □φ      => hbox φ
  | φ ==> ψ   => himp φ ψ

/-- Imported declaration from the Incompleteness formalization. -/
@[elab_as_elim]
def rec' {C : Formula α → Sort w}
  (hfalsum : C ⊥)
  (hatom : ∀ a : α, C (atom a))
  (himp    : ∀ (φ ψ : Formula α), C φ → C ψ → C (φ ==> ψ))
  (hbox    : ∀ (φ : Formula α), C φ → C (□φ))
  : (φ : Formula α) → C φ
  | ⊥      => hfalsum
  | atom a => hatom a
  | φ ==> ψ  => himp φ ψ (rec' hfalsum hatom himp hbox φ) (rec' hfalsum hatom himp hbox ψ)
  | □φ     => hbox φ (rec' hfalsum hatom himp hbox φ)

-- @[simp] lemma complexity_neg (φ : Formula α) : complexity (∼φ) = φ.complexity + 1 :=
--   by induction φ using rec' <;> try { simp[neg_eq, neg, *]; rfl;}

section «lp_section_2»

variable [DecidableEq α]

/-- Imported declaration from the Incompleteness formalization. -/
def hasDecEq : (φ ψ : Formula α) → Decidable (φ = ψ) := fun _ _ => inferInstance
instance : DecidableEq (Formula α) := hasDecEq

end «lp_section_2»


/-- Imported declaration from the Incompleteness formalization. -/
def isBox : Formula α → Bool
  | box _ => true
  | _  => false

end Formula


/-- Imported declaration from the Incompleteness formalization. -/
abbrev FormulaSet (α) := Set (Formula α)

/-- Imported declaration from the Incompleteness formalization. -/
abbrev FormulaFinset (α) := Finset (Formula α)


/-


lemma sub_of_top (h : φ ∈ 𝒮 ⊤) : φ = ⊤ := by simp_all [subformulae];
lemma sub_of_bot (h : φ ∈ 𝒮 ⊥) : φ = ⊥ := by simp_all [subformulae];

-/

/-
class FormulaFinset.SubformulaClosed (X : FormulaFinset α) where
  imp_closed : ∀ {φ ψ}, φ ==> ψ ∈ X → φ ∈ X ∧ ψ ∈ X
  box_closed : ∀ {φ}, □φ ∈ X → φ ∈ X

namespace SubformulaClosed

instance [DecidableEq α] {φ : Formula α} : FormulaFinset.SubformulaClosed (φ.subformulae) where
  imp_closed hpq := ⟨Formula.subformulae.mem_imp₁ hpq, Formula.subformulae.mem_imp₂ hpq⟩
  box_closed hp := Formula.subformulae.mem_box hp


variable {φ : Formula α} {X : FormulaFinset α} [closed : X.SubformulaClosed]

lemma mem_box (h : □φ ∈ X) : φ ∈ X := closed.box_closed h
macro_rules | `(tactic| trivial) => `(tactic| apply mem_box <| by assumption)

lemma mem_imp (h : φ ==> ψ ∈ X) : φ ∈ X ∧ ψ ∈ X := closed.imp_closed h

lemma mem_imp₁ (h : φ ==> ψ ∈ X) : φ ∈ X := mem_imp h |>.1
macro_rules | `(tactic| trivial) => `(tactic| apply mem_imp₁ <| by assumption)

lemma mem_imp₂ (h : φ ==> ψ ∈ X) : ψ ∈ X := mem_imp h |>.2
macro_rules | `(tactic| trivial) => `(tactic| apply mem_imp₁ <| by assumption)

attribute [aesop safe 5 forward]
  mem_box
  mem_imp₁
  mem_imp₂

end SubformulaClosed


class FormulaSet.SubformulaClosed (T : FormulaSet α) where
  imp_closed : ∀ {φ ψ}, φ ==> ψ ∈ T → φ ∈ T ∧ ψ ∈ T
  box_closed : ∀ {φ}, □φ ∈ T → φ ∈ T

namespace FormulaSet
namespace SubformulaClosed

instance {φ : Formula α} [DecidableEq α] : FormulaSet.SubformulaClosed (φ.subformulae).toSet where
  box_closed := FormulaFinset.SubformulaClosed.box_closed;
  imp_closed := FormulaFinset.SubformulaClosed.imp_closed;

variable {φ : Formula α} {T : FormulaSet α} [T_closed : T.SubformulaClosed]

lemma mem_box (h : □φ ∈ T) : φ ∈ T := T_closed.box_closed h
macro_rules | `(tactic| trivial) => `(tactic| apply mem_box <| by assumption)

lemma mem_imp (h : φ ==> ψ ∈ T) : φ ∈ T ∧ ψ ∈ T := T_closed.imp_closed h

lemma mem_imp₁ (h : φ ==> ψ ∈ T) : φ ∈ T := mem_imp h |>.1
macro_rules | `(tactic| trivial) => `(tactic| apply mem_imp₁ <| by assumption)

lemma mem_imp₂ (h : φ ==> ψ ∈ T) : ψ ∈ T := mem_imp h |>.2
macro_rules | `(tactic| trivial) => `(tactic| apply mem_imp₂ <| by assumption)

end SubformulaClosed
end FormulaSet

end Subformula
-/

/-
section Atoms

variable [DecidableEq α]

namespace Formula

def atoms : Formula α → Finset (α)
  | .atom a => {a}
  | ⊤      => ∅
  | ⊥      => ∅
  | ∼φ     => φ.atoms
  | □φ  => φ.atoms
  | φ ==> ψ => φ.atoms ∪ ψ.atoms
  | φ ⋏ ψ  => φ.atoms ∪ ψ.atoms
  | φ ⋎ ψ  => φ.atoms ∪ ψ.atoms
prefix:70 "𝒜 " => Formula.atoms

@[simp]
lemma mem_atoms_iff_mem_subformulae {a : α} {φ : Formula α} :
    a ∈ 𝒜 φ ↔ (atom a) ∈ φ.subformulae := by
  induction φ using Formula.rec' <;> simp_all [subformulae, atoms];

end Formula

end Atoms
-/


namespace Formula

variable {φ ψ χ : Formula α}

/-- Imported declaration from the Incompleteness formalization. -/
@[elab_as_elim]
def casesNeg [DecidableEq α] {C : Formula α → Sort w}
    (hfalsum : C ⊥)
    (hatom : ∀ a : α, C (atom a))
    (hneg    : ∀ φ : Formula α, C (∼φ))
    (himp    : ∀ (φ ψ : Formula α), ψ ≠ ⊥ → C (φ ==> ψ))
    (hbox    : ∀ (φ : Formula α), C (□φ))
    : (φ : Formula α) → C φ
  | ⊥       => hfalsum
  | atom a  => hatom a
  | □φ      => hbox φ
  | ∼φ      => hneg φ
  | φ ==> ψ  => if e : ψ = ⊥ then e ▸ hneg φ else himp φ ψ e

/-- Imported declaration from the Incompleteness formalization. -/
@[elab_as_elim]
def recNeg [DecidableEq α] {C : Formula α → Sort w}
    (hfalsum : C ⊥)
    (hatom : ∀ a : α, C (atom a))
    (hneg    : ∀ φ : Formula α, C (φ) → C (∼φ))
    (himp    : ∀ (φ ψ : Formula α), ψ ≠ ⊥ → C φ → C ψ → C (φ ==> ψ))
    (hbox    : ∀ (φ : Formula α), C (φ) → C (□φ))
    : (φ : Formula α) → C φ
  | ⊥       => hfalsum
  | atom a  => hatom a
  | □φ      => hbox φ (recNeg hfalsum hatom hneg himp hbox φ)
  | ∼φ      => hneg φ (recNeg hfalsum hatom hneg himp hbox φ)
  | φ ==> ψ  =>
    if e : ψ = ⊥
    then e ▸ hneg φ (recNeg hfalsum hatom hneg himp hbox φ)
    else himp φ ψ e (recNeg hfalsum hatom hneg himp hbox φ) (recNeg hfalsum hatom hneg himp hbox
      ψ)


section «lp_section_3»

/-- Imported declaration from the Incompleteness formalization. -/
def negated : Formula α → Bool
  | ∼_ => True
  | _  => False

@[simp] lemma negated_def : (∼φ).negated := by simp [negated]

@[simp]
lemma negated_imp : (φ ==> ψ).negated ↔ (ψ = ⊥) := by
  simp [negated];
  split;
  · simp_all [Formula.imp_eq]; rfl;
  · simp_all [Formula.imp_eq]; simpa;

lemma negated_iff : φ.negated ↔ ∃ ψ, φ = ∼ψ := by
  classical
  induction φ using Formula.casesNeg with
  | himp => simp [negated_imp, NegAbbrev.neg];
  | _ => simp [negated]

lemma not_negated_iff : ¬φ.negated ↔ ∀ ψ, φ ≠ ∼ψ := by
  classical
  induction φ using Formula.casesNeg with
  | himp => simp [negated_imp, NegAbbrev.neg];
  | _ => simp [negated]

/-- Imported declaration from the Incompleteness formalization. -/
@[elab_as_elim]
def recNegated [DecidableEq α] {C : Formula α → Sort w}
    (hfalsum : C ⊥)
    (hatom : ∀ a : α, C (atom a))
    (hneg    : ∀ φ : Formula α, C (φ) → C (∼φ))
    (himp    : ∀ (φ ψ : Formula α), ¬(φ ==> ψ).negated → C φ → C ψ → C (φ ==> ψ))
    (hbox    : ∀ (φ : Formula α), C (φ) → C (□φ))
    : (φ : Formula α) → C φ
  | ⊥       => hfalsum
  | atom a  => hatom a
  | □φ      => hbox φ (recNegated hfalsum hatom hneg himp hbox φ)
  | ∼φ      => hneg φ (recNegated hfalsum hatom hneg himp hbox φ)
  | φ ==> ψ  => by
    by_cases e : ψ = ⊥
    · exact e ▸ hneg φ (recNegated hfalsum hatom hneg himp hbox φ)
    · refine himp φ ψ ?_ (recNegated hfalsum hatom hneg himp hbox φ) (recNegated hfalsum hatom
      hneg himp hbox ψ)
      · simpa [negated_imp]

end «lp_section_3»

section «lp_section_4»

variable [Encodable α]
open Encodable

/-- Imported declaration from the Incompleteness formalization. -/
def toNat : Formula α → ℕ
  | atom a  => (Nat.pair 0 <| encode a) + 1
  | ⊥       => (Nat.pair 1 0) + 1
  | □φ      => (Nat.pair 2 <| φ.toNat) + 1
  | φ ==> ψ   => (Nat.pair 3 <| φ.toNat.pair ψ.toNat) + 1

def ofNat : ℕ → Option (Formula α)
  | 0 => none
  | e + 1 =>
    let idx := e.unpair.1
    let c := e.unpair.2
    match idx with
    | 0 => (decode c).map Formula.atom
    | 1 => some ⊥
    | 2 =>
      have : c < e + 1 := Nat.lt_succ_iff.mpr <| Nat.unpair_right_le _
      do
        let φ <- ofNat c
        return □φ
    | 3 =>
      have : c.unpair.1 < e + 1 :=
        Nat.lt_succ_iff.mpr <| le_trans (Nat.unpair_left_le _) <| Nat.unpair_right_le _
      have : c.unpair.2 < e + 1 :=
        Nat.lt_succ_iff.mpr <| le_trans (Nat.unpair_right_le _) <| Nat.unpair_right_le _
      do
        let φ <- ofNat c.unpair.1
        let ψ <- ofNat c.unpair.2
        return φ ==> ψ
    | _ => none

lemma ofNat_toNat : ∀ (φ : Formula α), ofNat (toNat φ) = some φ
  | atom a  => by simp [toNat, ofNat, Nat.unpair_pair, encodek, Option.map_some];
  | ⊥       => by simp [toNat, ofNat]
  | □φ      => by simp [toNat, ofNat, ofNat_toNat φ]
  | φ ==> ψ   => by simp [toNat, ofNat, ofNat_toNat φ, ofNat_toNat ψ]

instance : Encodable (Formula α) where
  encode := toNat
  decode := ofNat
  encodek := ofNat_toNat

end «lp_section_4»

end Formula


/-
end Formula

namespace FormulaSet

open Formula
variable {T : FormulaSet α}

class SubstClosed (T : FormulaSet α) : Prop where
  closed : ∀ {φ}, φ ∈ T → ∀ {σ}, φ.subst σ ∈ T

def instSubstClosed
  (hAtom : ∀ a : α, (atom a) ∈ T → ∀ {σ}, (atom a).subst σ ∈ T)
  (hImp : ∀ {φ ψ}, φ ==> ψ ∈ T → ∀ {σ}, (φ ==> ψ).subst σ ∈ T)
  (hBox : ∀ {φ}, □φ ∈ T → ∀ {σ}, (□φ).subst σ ∈ T)
  : T.SubstClosed := ⟨
  by
    intro φ hφ σ;
    induction φ using Formula.cases' with
    | hatom a => apply hAtom; assumption;
    | hfalsum => apply hφ;
    | himp φ ψ => apply hImp; assumption;
    | hbox φ => apply hBox; assumption;
⟩

namespace SubstClosed

variable [T.SubstClosed]

lemma mem_atom (h : atom a ∈ T) : (atom a).subst σ ∈ T := SubstClosed.closed h

lemma mem_bot (h : ⊥ ∈ T) : (⊥ : Formula α).subst σ ∈ T := SubstClosed.closed h

lemma mem_imp (h : φ ==> ψ ∈ T) : (φ ==> ψ).subst σ ∈ T := SubstClosed.closed h

lemma mem_neg (h : ∼φ ∈ T) : (∼φ).subst σ ∈ T := SubstClosed.closed h

lemma mem_and (h : φ ⋏ ψ ∈ T) : (φ ⋏ ψ).subst σ ∈ T := SubstClosed.closed h

lemma mem_or (h : φ ⋎ ψ ∈ T) : (φ ⋎ ψ).subst σ ∈ T := SubstClosed.closed h

lemma mem_box (h : □φ ∈ T) : (□φ).subst σ ∈ T := SubstClosed.closed h

instance union {T₁ T₂ : FormulaSet α} [T₁_closed : T₁.SubstClosed] [T₂_closed : T₂.SubstClosed] :
    (T₁ ∪ T₂).SubstClosed := by
  refine instSubstClosed ?_ ?_ ?_;
  · rintro a (ha₁ | ha₂) σ;
    · left; apply mem_atom ha₁;
    · right; apply mem_atom ha₂;
  · rintro φ ψ (h₁ | h₂) σ;
    · left; apply mem_imp h₁;
    · right; apply mem_imp h₂;
  · rintro φ (h₁ | h₂) σ;
    · left; apply mem_box h₁;
    · right; apply mem_box h₂;

end SubstClosed

end FormulaSet

end subst
-/

end Modal
end LO
