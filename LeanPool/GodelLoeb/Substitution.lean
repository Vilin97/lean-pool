/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import LeanPool.GodelLoeb.ModalFormula

/-!
# Substitution and coding aliases

This file keeps the qualified `Substitution.*` names used by the
diagonal layer. The operations themselves live in `ModalFormula.lean`
so that the explicit Kreisel fixed-point primitive, coding, and
distinguished-slot substitution stay definitionally aligned.

These aliases are part of the modal-axiomatic substrate. In particular,
`Substitution.code` is not an arithmetic-realisation Godel coding theorem:
on the diagonal-template arm it emits the `ModalFormula.kreiselFixed`
postulate, and on all other inputs it delegates to the transparent `quote`
wrapper. Downstream structural facts are therefore consequences of the
`kreiselFixed` evaluation clause plus this syntactic template recogniser.
-/

namespace ModalLogic.GoedelLoeb

universe u

/- Qualified aliases and witnesses for the substitution/coding layer. -/
namespace Substitution

/--
Qualified name for modal-axiomatic coding.

This aliases the template recogniser that emits `ModalFormula.kreiselFixed`
on the diagonal-template arm and transparent `quote` wrappers elsewhere.
-/
abbrev code {α : Type u} : ModalFormula α → ModalFormula α :=
  ModalFormula.code

/--
Qualified name for decoding quoted syntax.

This is Phase B scaffolding and is not consumed by the current Phase A
modal-axiomatic substrate.
-/
abbrev decode {α : Type u} : ModalFormula α → Option (ModalFormula α) :=
  ModalFormula.decode

/-- Qualified name for distinguished-slot substitution. -/
abbrev subst {α : Type u} [DecidableEq α] (a : α) :
    ModalFormula α → ModalFormula α → ModalFormula α :=
  ModalFormula.subst a

/-- Qualified name for the one-hole Kreisel template. -/
abbrev diagonalTemplate {α : Type u} (a : α) : ModalFormula α → ModalFormula α :=
  ModalFormula.diagonalTemplate a

/-- Qualified name for the constructed fixed point. -/
abbrev fixedpoint {α : Type u} [DecidableEq α] (a : α) :
    ModalFormula α → ModalFormula α :=
  ModalFormula.constructedFixedpoint a

/-- Qualified structural self-substitution identity. -/
lemma subst_diagonalTemplate_self {α : Type u} [DecidableEq α]
    (a : α) (phi : ModalFormula α) :
    subst a (diagonalTemplate a phi) (code (diagonalTemplate a phi)) =
      ModalFormula.kreiselFixed phi :=
  ModalFormula.subst_diagonalTemplate_self a phi

end Substitution

end ModalLogic.GoedelLoeb
