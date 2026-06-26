/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import LeanPool.GodelLoeb.Substitution

/-!
# Modal provability

This file defines the Hilbert-style proof predicate used by the
modal-axiomatic Loeb theorem. `Provable` is the K4 closure over the
`ModalFormula` substrate, and that substrate includes the irreducible
`kreiselFixed` postulate in `propEval`. Propositional reasoning is admitted by
the usual tautology schema, so any downstream use of the canonical diagonal
interface consumes consequences of that substrate postulate rather than an
arithmetic-realisation derivation.

The object-level normal-modal layer is system K4: K, the intrinsic 4 axiom
`[]phi -> [][]phi`, modus ponens, and necessitation. Arithmetic realisation
via a concrete provability predicate and Solovay-style coding is outside this
Phase A substrate.
-/

namespace ModalLogic.GoedelLoeb

open ModalFormula

universe u

/--
Hilbert-style provability for the modal-axiomatic K4 substrate with the
`kreiselFixed` postulate already present in formula evaluation.

The object-level proof constructors are exactly:
`pl_taut`, `ax_K`, `ax_four`, `mp`, and `nec`.
-/
inductive Provable {α : Type u} : ModalFormula α → Prop
  | pl_taut {phi : ModalFormula α} : phi.PropTaut → Provable phi
  | ax_K (phi psi : ModalFormula α) :
      Provable (□ₛ(phi ⟶ psi) ⟶ (□ₛphi ⟶ □ₛpsi))
  | ax_four (phi : ModalFormula α) : Provable (□ₛphi ⟶ □ₛ□ₛphi)
  | mp {phi psi : ModalFormula α} : Provable (phi ⟶ psi) → Provable phi → Provable psi
  | nec {phi : ModalFormula α} : Provable phi → Provable (□ₛphi)

namespace Provable

/-- Every propositional tautology is provable. -/
lemma of_prop_taut {α : Type u} {phi : ModalFormula α} (h : phi.PropTaut) :
    Provable phi :=
  pl_taut h

/-- The K distribution schema as a theorem alias. -/
lemma k {α : Type u} (phi psi : ModalFormula α) :
    Provable (□ₛ(phi ⟶ psi) ⟶ (□ₛphi ⟶ □ₛpsi)) :=
  ax_K phi psi

/-- The 4 axiom as a theorem alias. -/
lemma four {α : Type u} (phi : ModalFormula α) : Provable (□ₛphi ⟶ □ₛ□ₛphi) :=
  ax_four phi

/--
Boxed coding transparency for diagonal templates.

This is a propositional consequence of `Substitution.code` emitting the
`kreiselFixed` primitive on the template arm; it is not an arithmetic coding
transparency theorem.
-/
lemma box_code_fixedpoint_iff {α : Type u} [DecidableEq α]
    (a : α) (phi : ModalFormula α) :
    Provable (□ₛ(Substitution.code (Substitution.diagonalTemplate a phi)) ⟷
      □ₛ(Substitution.fixedpoint a phi)) :=
  of_prop_taut (ModalFormula.box_code_diagonalTemplate_prop_taut a phi)

/-- Propositional reflexivity of implication. -/
lemma imp_refl {α : Type u} (phi : ModalFormula α) : Provable (phi ⟶ phi) :=
  of_prop_taut <| by
    intro val h
    exact h

/-- Extract the forward implication from a provable equivalence. -/
lemma iff_left {α : Type u} {phi psi : ModalFormula α}
    (h : Provable (phi ⟷ psi)) : Provable (phi ⟶ psi) := by
  refine mp (pl_taut ?_) h
  intro val hIff
  exact hIff.mp

/-- Extract the reverse implication from a provable equivalence. -/
lemma iff_right {α : Type u} {phi psi : ModalFormula α}
    (h : Provable (phi ⟷ psi)) : Provable (psi ⟶ phi) := by
  refine mp (pl_taut ?_) h
  intro val hIff
  exact hIff.mpr

/-- Build a provable equivalence from both provable implications. -/
lemma iff_intro {α : Type u} {phi psi : ModalFormula α}
    (hLeft : Provable (phi ⟶ psi))
    (hRight : Provable (psi ⟶ phi)) : Provable (phi ⟷ psi) := by
  refine mp (mp (pl_taut ?_) hLeft) hRight
  intro val hpq hqp
  exact Iff.intro hpq hqp

/-- Compose two provable implications. -/
lemma imp_trans {α : Type u} {phi psi chi : ModalFormula α}
    (hPhiPsi : Provable (phi ⟶ psi))
    (hPsiChi : Provable (psi ⟶ chi)) :
    Provable (phi ⟶ chi) := by
  refine mp (mp (pl_taut ?_) hPhiPsi) hPsiChi
  intro val hpq hqr hp
  exact hqr (hpq hp)

/-- Combine three implications with the same antecedent. -/
lemma imp_box_combine {α : Type u} {alpha beta gamma delta : ModalFormula α}
    (hAlphaBeta : Provable (alpha ⟶ beta))
    (hAlphaGamma : Provable (alpha ⟶ gamma))
    (hBetaGammaDelta : Provable (beta ⟶ (gamma ⟶ delta))) :
    Provable (alpha ⟶ delta) := by
  refine mp (mp (mp (pl_taut ?_) hAlphaBeta) hAlphaGamma) hBetaGammaDelta
  intro val hab hac hbgd ha
  exact hbgd (hab ha) (hac ha)

/-- Prefix a provable implication by a box using necessitation and K. -/
lemma box_imp {α : Type u} {phi psi : ModalFormula α}
    (h : Provable (phi ⟶ psi)) : Provable (□ₛphi ⟶ □ₛpsi) :=
  mp (ax_K phi psi) (nec h)

/-- Add a provable consequent on the right side of an implication. -/
lemma imp_of_provable {α : Type u} {phi psi : ModalFormula α}
    (hPsi : Provable psi) : Provable (phi ⟶ psi) := by
  refine mp (pl_taut ?_) hPsi
  intro val hpsi _hphi
  exact hpsi

/-- Transport an implication across provable equivalences. -/
lemma imp_congr {α : Type u} {alpha beta gamma delta : ModalFormula α}
    (hAlphaBeta : Provable (alpha ⟷ beta))
    (hGammaDelta : Provable (gamma ⟷ delta)) :
    Provable ((alpha ⟶ gamma) ⟷ (beta ⟶ delta)) := by
  have hAlphaToBeta : Provable (alpha ⟶ beta) := iff_left hAlphaBeta
  have hBetaToAlpha : Provable (beta ⟶ alpha) := iff_right hAlphaBeta
  have hGammaToDelta : Provable (gamma ⟶ delta) := iff_left hGammaDelta
  have hDeltaToGamma : Provable (delta ⟶ gamma) := iff_right hGammaDelta
  have hForward : Provable ((alpha ⟶ gamma) ⟶ (beta ⟶ delta)) := by
    refine mp (mp (pl_taut ?_) hBetaToAlpha) hGammaToDelta
    intro val hba hgd hag hb
    exact hgd (hag (hba hb))
  have hBackward : Provable ((beta ⟶ delta) ⟶ (alpha ⟶ gamma)) := by
    refine mp (mp (pl_taut ?_) hAlphaToBeta) hDeltaToGamma
    intro val hab hdg hbd ha
    exact hdg (hbd (hab ha))
  exact iff_intro hForward hBackward

/-- Empty-frame soundness for the canonical proof predicate. -/
lemma sound_empty {α : Type u} {phi : ModalFormula α} (h : Provable phi) :
    phi.emptyEval := by
  induction h with
  | pl_taut hTaut =>
      exact (ModalFormula.propEval_emptyEval _).mp (hTaut ModalFormula.emptyEval)
  | ax_K phi psi =>
      change True → True → True
      intro _ _
      trivial
  | ax_four phi =>
      change True → True
      intro _
      trivial
  | mp hImp hPhi ihImp ihPhi =>
      exact ihImp ihPhi
  | nec hPhi ihPhi =>
      trivial

/-- The canonical proof predicate does not prove falsity. -/
theorem not_bot {α : Type u} : ¬ Provable (⊥ₛ : ModalFormula α) := by
  intro h
  exact sound_empty h

/-- The canonical proof predicate does not prove every atom. -/
lemma atom_not_provable {α : Type u} (a : α) : ¬ Provable (ModalFormula.atom a) := by
  intro h
  exact sound_empty h

end Provable

end ModalLogic.GoedelLoeb
