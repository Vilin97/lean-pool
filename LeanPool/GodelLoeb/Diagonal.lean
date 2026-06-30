/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import LeanPool.GodelLoeb.Provable
import LeanPool.GodelLoeb.Substitution

/-!
# Kreisel diagonal interface

This file states the non-vacuous diagonal ingredient used by the
modal-axiomatic Loeb theorem. The interface is restricted to the
Kreisel family `x ↦ []x -> phi`, which is the family needed for Loeb's
theorem.

The canonical instance in this file is not an arithmetic-realisation
diagonal lemma. It packages consequences of the modal-axiomatic
`ModalFormula.kreiselFixed` postulate: the template recogniser in
`Substitution.code` emits the primitive, and the propositional proofs unfold
the primitive's `propEval` clause. A Solovay/PA substrate would derive this
interface from syntactic Godel coding rather than consuming `kreiselFixed`.
-/

namespace ModalLogic.GoedelLoeb

open ModalFormula

universe u

/-- The Kreisel operator whose fixed point drives Loeb's theorem. -/
def kreiselOperator {α : Type u} (phi x : ModalFormula α) : ModalFormula α :=
  □ₛx ⟶ phi

/--
Structural evidence that a fixed-point operator is built by the
one-hole self-substitution construction.
-/
structure FixedpointStructuralEvidence (α : Type u) [DecidableEq α]
    (fixedpoint : ModalFormula α → ModalFormula α) (distinguishedAtom : α) where
  /-- The one-hole template whose self-substitution builds the fixed point. -/
  template : ModalFormula α → ModalFormula α
  /-- The packaged fixed point is the template with its own code substituted in. -/
  fixedpoint_eq_subst :
    ∀ phi, fixedpoint phi =
      Substitution.subst distinguishedAtom (template phi) (Substitution.code (template phi))
  /-- The self-substituted template propositionally unfolds to the boxed-code implication. -/
  subst_unfolding :
    ∀ phi, (Substitution.subst distinguishedAtom (template phi)
      (Substitution.code (template phi)) ⟷
        (□ₛ(Substitution.code (template phi)) ⟶ phi)).PropTaut
  /-- The boxed template code is propositionally equivalent to the boxed fixed point. -/
  box_code_fixedpoint :
    ∀ phi, (□ₛ(Substitution.code (template phi)) ⟷ □ₛ(fixedpoint phi)).PropTaut

namespace ModalFormula

/--
Structural evidence propositionally unfolds a fixed point.

This is the substitution side of the construction. It does not by itself
derive the Kreisel diagonal equivalence; the canonical diagonal theorem still
passes through the `kreiselFixed` postulate when the template recogniser emits
that primitive.
-/
lemma fixedpoint_structural_prop_taut {α : Type u} [DecidableEq α]
    (fixedpoint : ModalFormula α → ModalFormula α) (distinguishedAtom : α)
    (phi : ModalFormula α)
    (h : FixedpointStructuralEvidence α fixedpoint distinguishedAtom) :
    (fixedpoint phi ⟷ (□ₛ(Substitution.code (h.template phi)) ⟶ phi)).PropTaut := by
  intro val
  have hUnfold := h.subst_unfolding phi val
  constructor
  · intro hFixed
    have hSubstEval :
        propEval val (Substitution.subst distinguishedAtom (h.template phi)
          (Substitution.code (h.template phi))) := by
      rw [← h.fixedpoint_eq_subst phi]
      exact hFixed
    exact hUnfold.mp hSubstEval
  · intro hUnfolded
    have hSubstEval :
        propEval val (Substitution.subst distinguishedAtom (h.template phi)
          (Substitution.code (h.template phi))) :=
      hUnfold.mpr hUnfolded
    rw [h.fixedpoint_eq_subst phi]
    exact hSubstEval

/-- The canonical substitution construction carries structural evidence. -/
def canonicalFixedpointStructural {α : Type u} [DecidableEq α] (a : α) :
    FixedpointStructuralEvidence α (Substitution.fixedpoint a) a where
  template := Substitution.diagonalTemplate a
  fixedpoint_eq_subst := fixedpoint_eq_subst_template a
  subst_unfolding := subst_diagonalTemplate_self_prop_taut a
  box_code_fixedpoint := box_code_diagonalTemplate_prop_taut a

/--
The canonical structural unfolding is a propositional tautology before the
postulate-backed bridge from boxed template code to the Kreisel unfolding.
-/
lemma canonical_fixedpoint_structural_prop_taut {α : Type u} [DecidableEq α]
    (a : α) (phi : ModalFormula α) :
    (Substitution.fixedpoint a phi ⟷
      (□ₛ(Substitution.code (Substitution.diagonalTemplate a phi)) ⟶
        phi)).PropTaut := by
  simpa [canonicalFixedpointStructural] using
    fixedpoint_structural_prop_taut (Substitution.fixedpoint a) a phi
      (canonicalFixedpointStructural a)

/--
The raw Kreisel fixed-point shape is a propositional consequence of the
`kreiselFixed` postulate.
-/
lemma raw_kreisel_diagonal_prop_taut {α : Type u} [DecidableEq α]
    (a : α) (phi : ModalFormula α) :
    (Substitution.fixedpoint a phi ⟷
      kreiselOperator phi (Substitution.fixedpoint a phi)).PropTaut := by
  intro val
  have hStructural := canonical_fixedpoint_structural_prop_taut a phi val
  have hBox := box_code_diagonalTemplate_prop_taut a phi val
  constructor
  · intro hFixed hBoxFixed
    exact hStructural.mp hFixed (hBox.mpr hBoxFixed)
  · intro hKreisel
    exact hStructural.mpr fun hBoxCode => hKreisel (hBox.mp hBoxCode)

/--
Derives the diagonal iff for the `Diagonalisable α` typeclass via the
`kreiselFixed` constructor's `propEval` clause and the `code` pattern-match.

The derivation consumes the modal-axiomatic postulate at the substrate level;
consumers of `Diagonalisable α` may treat the iff as derived from K4 plus the
`kreiselFixed` postulate. An arithmetic-realisation substrate would derive
this without the `kreiselFixed` primitive.
-/
theorem canonicalDiagonalPostulateConsequence {α : Type u} [DecidableEq α]
    (a : α) (phi : ModalFormula α) :
    Provable (Substitution.fixedpoint a phi ⟷
      kreiselOperator phi (Substitution.fixedpoint a phi)) := by
  let template := Substitution.diagonalTemplate a phi
  have hStructural :
      Provable (Substitution.fixedpoint a phi ⟷
        (□ₛ(Substitution.code template) ⟶ phi)) := by
    dsimp [template]
    exact Provable.of_prop_taut (canonical_fixedpoint_structural_prop_taut a phi)
  have hCodeTemplate :
      Provable (□ₛ(Substitution.code template) ⟷ □ₛ(Substitution.fixedpoint a phi)) := by
    dsimp [template]
    exact Provable.box_code_fixedpoint_iff a phi
  have hImpBridge :
      Provable (((□ₛ(Substitution.code template)) ⟶ phi) ⟷
        ((□ₛ(Substitution.fixedpoint a phi)) ⟶ phi)) :=
    Provable.imp_congr hCodeTemplate (Provable.iff_intro (Provable.imp_refl phi)
      (Provable.imp_refl phi))
  have hForward :
      Provable (Substitution.fixedpoint a phi ⟶
        ((□ₛ(Substitution.fixedpoint a phi)) ⟶ phi)) :=
    Provable.imp_trans (Provable.iff_left hStructural) (Provable.iff_left hImpBridge)
  have hBackward :
      Provable (((□ₛ(Substitution.fixedpoint a phi)) ⟶ phi) ⟶
        Substitution.fixedpoint a phi) :=
    Provable.imp_trans (Provable.iff_right hImpBridge) (Provable.iff_right hStructural)
  exact Provable.iff_intro hForward hBackward

end ModalFormula

/--
Non-vacuous diagonal data for the Kreisel fixed-point family.

The bundle separates the diagonal equivalence from the structural evidence
that the fixed point is built by self-substitution. The bundle itself is not a
discharge: an instance must supply the diagonal field, and the canonical
instance supplies it via `canonicalDiagonalPostulateConsequence`.
-/
class Diagonalisable (α : Type u) [DecidableEq α] where
  /-- The atom marking the diagonal substitution slot. -/
  distinguishedAtom : α
  /-- Fixed point for the target formula `phi`. -/
  fixedpoint : ModalFormula α → ModalFormula α
  /-- The fixed point proves equivalent to its Kreisel unfolding. -/
  diagonal (phi : ModalFormula α) :
    Provable (fixedpoint phi ⟷ kreiselOperator phi (fixedpoint phi))
  /-- The fixed-point operator is backed by self-substitution structure. -/
  fixedpointStructural :
    FixedpointStructuralEvidence α fixedpoint distinguishedAtom

namespace Diagonalisable

/-- The diagonal equivalence as a theorem alias. -/
lemma spec {α : Type u} [DecidableEq α] [Diagonalisable α] (phi : ModalFormula α) :
    Provable (Diagonalisable.fixedpoint phi ⟷
      kreiselOperator phi (Diagonalisable.fixedpoint phi)) :=
  Diagonalisable.diagonal phi

/-- The fixed-point operator carries structural evidence. -/
abbrev structural {α : Type u} [DecidableEq α] [Diagonalisable α] :
    FixedpointStructuralEvidence α Diagonalisable.fixedpoint
      Diagonalisable.distinguishedAtom :=
  Diagonalisable.fixedpointStructural

end Diagonalisable

/--
Concrete modal-axiomatic diagonal instance.

The `diagonal` field is the named consequence of the `kreiselFixed` postulate;
the structural field records the canonical substitution shape consumed by
Loeb's theorem.
-/
instance canonicalDiagonalisable (α : Type u) [DecidableEq α] [Inhabited α] :
    Diagonalisable α where
  distinguishedAtom := default
  fixedpoint := Substitution.fixedpoint default
  diagonal := ModalFormula.canonicalDiagonalPostulateConsequence default
  fixedpointStructural := ModalFormula.canonicalFixedpointStructural default

end ModalLogic.GoedelLoeb
