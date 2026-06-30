/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.Logic.Basic

/-!
# Modal formulas

This file defines the modal-axiomatic substrate for system K4 plus Loeb's
theorem. The atomic proposition type is a parameter `α : Type u`; no encoding
or decidable equality structure is required to form formulas.

The `kreiselFixed` constructor is the substrate's irreducible postulate: its
`propEval` clause `val (box (kreiselFixed phi)) → propEval val phi` encodes the
Kreisel fixed-point semantics that an arithmetic-realisation substrate
(Foundation's `StandardProvability`, Solovay arithmetic) would derive from
syntactic Godel coding. Within the modal-axiomatic scope of this development,
`kreiselFixed` is named as a primitive.

The substitution and coding layer (`Substitution.subst`, `Substitution.code`)
provides a syntactic facade that makes downstream theorems (the canonical
`Diagonalisable` instance, `loeb`, and the worked examples) propositionally
tautological by construction where they consume the primitive's evaluation.
They are consequences of the constructor's evaluation clause, not derivations
from an arithmetic-realisation coding theorem.
-/

namespace ModalLogic.GoedelLoeb

universe u

/-- Universe-polymorphic modal formulas over atomic propositions `α`. -/
inductive ModalFormula (α : Type u) : Type u
  | atom : α → ModalFormula α
  | bot : ModalFormula α
  | impl : ModalFormula α → ModalFormula α → ModalFormula α
  | iff : ModalFormula α → ModalFormula α → ModalFormula α
  | box : ModalFormula α → ModalFormula α
  /--
  Pure tag wrapper used to license `code`'s pattern-match into the
  `kreiselFixed` primitive. It carries no independent semantic content beyond
  tagging the diagonal-template arm. Its `propEval` clause is transparent:
  quotation evaluates exactly as its inner formula, so the constructor is only
  a syntactic marker.
  -/
  | quote : ModalFormula α → ModalFormula α
  /--
  The Kreisel fixed-point primitive.

  This is a modal-axiomatic postulate: the `propEval` clause encodes
  `□ₛ(kreiselFixed phi) ⟶ phi` as this constructor's evaluation. An
  arithmetic-realisation substrate would derive this from Godel coding of
  self-referential sentences; in this modal-axiomatic substrate it is the
  irreducible primitive.
  -/
  | kreiselFixed : ModalFormula α → ModalFormula α
  deriving DecidableEq, Repr

namespace ModalFormula

/-- Falsity as a formula. -/
notation "⊥ₛ" => ModalFormula.bot

/-- Object-language implication. -/
infixr:60 " ⟶ " => ModalFormula.impl

/-- Object-language equivalence. -/
infix:55 " ⟷ " => ModalFormula.iff

/-- Object-language necessity. -/
prefix:75 "□ₛ" => ModalFormula.box

/-- Object-language truth. -/
def top {α : Type u} : ModalFormula α :=
  ⊥ₛ ⟶ ⊥ₛ

/-- Object-language negation. -/
def neg {α : Type u} (phi : ModalFormula α) : ModalFormula α :=
  phi ⟶ ⊥ₛ

/-- Object-language conjunction, encoded classically by implication and falsity. -/
def and {α : Type u} (phi psi : ModalFormula α) : ModalFormula α :=
  neg (phi ⟶ neg psi)

/-- Object-language disjunction, encoded classically by implication and falsity. -/
def or {α : Type u} (phi psi : ModalFormula α) : ModalFormula α :=
  neg phi ⟶ psi

/--
Modal-axiomatic coding function.

On the diagonal-template arm `impl (box (atom a)) (quote body)`, this emits the
`kreiselFixed` primitive; this is the modal-axiomatic substrate's encoding of
self-reference. On non-template inputs, `code phi` is the tag wrapper
`quote phi`, so it is syntactically non-identity but propositionally
transparent because `quote`'s `propEval` clause is transparent. Non-trivial
coding content lives only on the diagonal-template arm where the
`kreiselFixed` primitive is emitted.
-/
def code {α : Type u} (phi : ModalFormula α) : ModalFormula α :=
  match phi with
  | impl (box (atom _)) (quote body) => kreiselFixed body
  | other => quote other

/--
Decode ordinary quoted syntax.

This is Phase B scaffolding for a future arithmetic-realisation integration
that may consume explicit quoted syntax. It is not used by the current Phase A
modal-axiomatic substrate; `kreiselFixed` remains a primitive sentence rather
than something decoded from syntax here.
-/
def decode {α : Type u} (phi : ModalFormula α) : Option (ModalFormula α) :=
  match phi with
  | quote body => some body
  | _ => none

/-- Substitute `arg` for the distinguished atom `atom a`. -/
def subst {α : Type u} [DecidableEq α] (a : α) :
    ModalFormula α → ModalFormula α → ModalFormula α
  | atom b, arg => if a = b then arg else atom b
  | bot, _ => bot
  | impl (box (atom b)) (quote body), _ =>
      if a = b then kreiselFixed body else (□ₛ(atom b) ⟶ quote body)
  | impl phi psi, arg => subst a phi arg ⟶ subst a psi arg
  | iff phi psi, arg => subst a phi arg ⟷ subst a psi arg
  | box phi, arg => □ₛ(subst a phi arg)
  | quote phi, _ => quote phi
  | kreiselFixed phi, arg => kreiselFixed (subst a phi arg)

/-- The one-hole Kreisel diagonal template for a target formula. -/
def diagonalTemplate {α : Type u} (a : α) (phi : ModalFormula α) : ModalFormula α :=
  □ₛ(atom a) ⟶ quote phi

/-- The substitution-built Kreisel fixed point for a target formula. -/
def constructedFixedpoint {α : Type u} [DecidableEq α]
    (a : α) (phi : ModalFormula α) : ModalFormula α :=
  subst a (diagonalTemplate a phi) (code (diagonalTemplate a phi))

/-- Propositional evaluation with syntax-indexed opaque modal slots. -/
def propEval {α : Type u} (val : ModalFormula α → Prop) : ModalFormula α → Prop
  | atom a => val (atom a)
  | bot => False
  | impl phi psi => propEval val phi → propEval val psi
  | iff phi psi => propEval val phi ↔ propEval val psi
  | box phi => val (box phi)
  | quote phi => propEval val phi
  | kreiselFixed phi => val (box (kreiselFixed phi)) → propEval val phi

/-- A formula is propositionally valid when it holds under every valuation. -/
def PropTaut {α : Type u} (phi : ModalFormula α) : Prop :=
  ∀ val, propEval val phi

/-- Empty-frame evaluation used for the non-collapse soundness check. -/
def emptyEval {α : Type u} : ModalFormula α → Prop
  | atom _ => False
  | bot => False
  | impl phi psi => emptyEval phi → emptyEval psi
  | iff phi psi => emptyEval phi ↔ emptyEval psi
  | box _ => True
  | quote phi => emptyEval phi
  | kreiselFixed phi => emptyEval phi

/-- Propositional evaluation with the empty-frame valuation matches empty evaluation. -/
lemma propEval_emptyEval {α : Type u} (phi : ModalFormula α) :
    propEval emptyEval phi ↔ emptyEval phi := by
  induction phi with
  | atom a => rfl
  | bot => rfl
  | impl phi psi hPhi hPsi =>
      change (propEval emptyEval phi → propEval emptyEval psi) ↔
        (emptyEval phi → emptyEval psi)
      rw [hPhi, hPsi]
  | iff phi psi hPhi hPsi =>
      change (propEval emptyEval phi ↔ propEval emptyEval psi) ↔
        (emptyEval phi ↔ emptyEval psi)
      rw [hPhi, hPsi]
  | box phi => rfl
  | quote phi hPhi => exact hPhi
  | kreiselFixed phi hPhi =>
      change (True → propEval emptyEval phi) ↔ emptyEval phi
      constructor
      · intro h
        exact hPhi.mp (h trivial)
      · intro h _hTrue
        exact hPhi.mpr h

/--
Quoted syntax decodes to its body.

This is tagged as a simplification rule for Phase B forward compatibility:
the first downstream arithmetic-realisation consumer is expected to normalise
quoted syntax while plugging this modal substrate into a concrete coding layer.
Phase A itself only needs `decode` as scaffolding; `kreiselFixed` remains the
load-bearing primitive here.
-/
@[simp]
lemma decode_quote {α : Type u} (phi : ModalFormula α) : decode (quote phi) = some phi :=
  rfl

@[simp]
lemma code_diagonalTemplate {α : Type u} (a : α) (phi : ModalFormula α) :
    code (diagonalTemplate a phi) = kreiselFixed phi := by
  rfl

/--
Syntactically, `code ⊥ₛ` is the quote-wrapped form `quote ⊥ₛ`, not `⊥ₛ`.

This witnesses the non-triviality of the quote-wrapping branch on a
non-template input; non-template inputs remain propositionally transparent
under `propEval`.
-/
lemma code_bot_ne_bot {α : Type u} : code (⊥ₛ : ModalFormula α) ≠ ⊥ₛ := by
  intro h
  cases h

@[simp]
lemma subst_atom_self {α : Type u} [DecidableEq α] (a : α) (arg : ModalFormula α) :
    subst a (atom a) arg = arg := by
  simp [subst]

@[simp]
lemma subst_atom_ne {α : Type u} [DecidableEq α] {a b : α} (h : a ≠ b)
    (arg : ModalFormula α) : subst a (atom b) arg = atom b := by
  simp [subst, h]

@[simp]
lemma subst_iff {α : Type u} [DecidableEq α] (a : α) (phi psi arg : ModalFormula α) :
    subst a (phi ⟷ psi) arg = (subst a phi arg ⟷ subst a psi arg) :=
  rfl

@[simp]
lemma subst_box {α : Type u} [DecidableEq α] (a : α) (phi arg : ModalFormula α) :
    subst a (□ₛphi) arg = □ₛ(subst a phi arg) :=
  rfl

@[simp]
lemma subst_quote {α : Type u} [DecidableEq α] (a : α) (phi arg : ModalFormula α) :
    subst a (quote phi) arg = quote phi :=
  rfl

@[simp]
lemma subst_kreiselFixed {α : Type u} [DecidableEq α] (a : α)
    (phi arg : ModalFormula α) :
    subst a (kreiselFixed phi) arg = kreiselFixed (subst a phi arg) :=
  rfl

@[simp]
lemma fixedpoint_eq_subst_template {α : Type u} [DecidableEq α]
    (a : α) (phi : ModalFormula α) :
    constructedFixedpoint a phi =
      subst a (diagonalTemplate a phi) (code (diagonalTemplate a phi)) :=
  rfl

@[simp]
lemma subst_diagonalTemplate_self {α : Type u} [DecidableEq α]
    (a : α) (phi : ModalFormula α) :
    subst a (diagonalTemplate a phi) (kreiselFixed phi) =
      kreiselFixed phi := by
  simp [diagonalTemplate, subst]

lemma subst_diagonalTemplate_self_prop_taut {α : Type u} [DecidableEq α]
    (a : α) (phi : ModalFormula α) :
    (subst a (diagonalTemplate a phi) (code (diagonalTemplate a phi)) ⟷
      (□ₛ(code (diagonalTemplate a phi)) ⟶ phi)).PropTaut := by
  intro val
  simp [diagonalTemplate, subst, code, propEval]

lemma box_code_diagonalTemplate_prop_taut {α : Type u} [DecidableEq α]
    (a : α) (phi : ModalFormula α) :
    (□ₛ(code (diagonalTemplate a phi)) ⟷
      □ₛ(constructedFixedpoint a phi)).PropTaut := by
  intro val
  simp [constructedFixedpoint, diagonalTemplate, subst, code, propEval]

end ModalFormula

end ModalLogic.GoedelLoeb
