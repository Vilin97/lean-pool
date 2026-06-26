/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import LeanPool.GodelLoeb.Incompleteness

/-!
# Worked modal-axiomatic example

This file keeps concrete formula-level checks over `α := Bool`. The
canonical diagonal instance uses `default = false` as the distinguished
atom. The worked target uses an unprovable atomic consequent, so the file
also records the formal obstruction to a closed Loeb hypothesis in the
canonical consistent substrate.
-/

namespace ModalLogic.GoedelLoeb

open ModalFormula

/-- The canonical Bool diagonal instance is available. -/
example : Diagonalisable Bool :=
  inferInstance

/-- The unprovable atomic consequent used by the worked target. -/
def workedConsequent : ModalFormula Bool :=
  ModalFormula.atom false

/-- A concrete non-tautological target for the worked Loeb example. -/
def workedPhi : ModalFormula Bool :=
  Substitution.fixedpoint false workedConsequent

/-- The worked target is not a propositional tautology. -/
lemma workedPhi_not_prop_taut : ¬ workedPhi.PropTaut := by
  intro h
  let val : ModalFormula Bool → Prop
    | box phi => phi = workedPhi
    | _ => False
  have hFalse : ModalFormula.propEval val workedPhi := h val
  dsimp [workedPhi, workedConsequent, Substitution.fixedpoint,
    ModalFormula.constructedFixedpoint, ModalFormula.diagonalTemplate,
    ModalFormula.propEval, ModalFormula.code, ModalFormula.subst] at hFalse
  exact hFalse rfl

/-- The worked consequent is not provable in the canonical proof predicate. -/
lemma workedConsequent_not_provable : ¬ Provable workedConsequent :=
  Provable.atom_not_provable false

/-- The worked target is not provable without an inconsistent Loeb hypothesis. -/
lemma workedPhi_not_provable : ¬ Provable workedPhi := by
  intro h
  have hEmpty : workedPhi.emptyEval := Provable.sound_empty h
  dsimp [workedPhi, workedConsequent, Substitution.fixedpoint,
    ModalFormula.constructedFixedpoint, ModalFormula.diagonalTemplate,
    ModalFormula.emptyEval, ModalFormula.code, ModalFormula.subst] at hEmpty

/--
Conditional Loeb firing on the concrete worked target.

The theorem is intentionally not closed: `workedLoebHypothesis_not_provable`
shows that a closed hypothesis for this atomic consequent would contradict
the canonical non-collapse witness.
-/
theorem workedLoeb (h : Provable (□ₛworkedPhi ⟶ workedPhi)) : Provable workedPhi :=
  loeb h

/-- No closed Loeb hypothesis exists for the unprovable worked target. -/
lemma workedLoebHypothesis_not_provable : ¬ Provable (□ₛworkedPhi ⟶ workedPhi) := by
  intro h
  exact workedPhi_not_provable (workedLoeb h)

/-- The modal second-incompleteness corollary fired for the Bool instance. -/
theorem workedSecondIncompleteness :
    ¬ Provable (modalConsistencySentence : ModalFormula Bool) :=
  secondIncompleteness

end ModalLogic.GoedelLoeb
