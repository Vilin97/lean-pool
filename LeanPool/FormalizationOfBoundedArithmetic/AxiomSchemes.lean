/-
Copyright (c) 2026 ruplet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ruplet
-/

import Lean

import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics

import LeanPool.FormalizationOfBoundedArithmetic.IsEnum
import LeanPool.FormalizationOfBoundedArithmetic.DisplayedVariables
import LeanPool.FormalizationOfBoundedArithmetic.LanguagePeano
import LeanPool.FormalizationOfBoundedArithmetic.LanguageZambella
import LeanPool.FormalizationOfBoundedArithmetic.Syntax
import LeanPool.FormalizationOfBoundedArithmetic.Semantics
import LeanPool.FormalizationOfBoundedArithmetic.Order

/-!
# LeanPool.FormalizationOfBoundedArithmetic.AxiomSchemes
-/

open FirstOrder Language BoundedFormula Formula


-- i think that type level is set to 0 because of
-- Vars1x type is just Type
-- variable {α disp : Type}

-- Definition 3.4 (Induction Scheme), p. 35 od draft (46 of PDF)
-- Note that `phi(x)` is permitted to have free variables other than `x`
-- This means that ultimately we need to take universal closure of the
-- resulting Bounded Formula, to get a Sentence (no free vars)
-- expect 1 displayed free variable (`x`), thus DisplayedFV1
-- but we can have more free vars - we `forall` over them!
/-- Build the universal closure of an induction axiom for a displayed variable. -/
def mkInductionSentence
  {a} [IsEnum a] {name}
  {L : Language}
    [Zero <| L.Term Empty]
    [One <| L.Term (Vars1 name)]
    [Add <| L.Term (Vars1 name)]
  (phi : L.Formula ((Vars1 name) ⊕ a))
  : L.Sentence :=
  let univ := phi.iAlls'
  let base := univ.subst (fun _ => 0)
  let step_assumption := univ
  let step_target := univ.subst (fun _ => (var Vars1.fv1) + 1)
  let step' : L.Formula (Vars1 name) := step_assumption ⟹ step_target
  let step := step'.display1.flip.iAlls'
  let forall_x_holds := univ.display1.flip.iAlls'
  base ⟹ step ⟹ forall_x_holds

/-- Normalize a realized induction sentence in a hypothesis. -/
syntax (name := simpInduction) "simpInduction" " at " (ppSpace ident)? : tactic

macro_rules
| `(tactic| simpInduction at $h:ident) =>
  `(tactic|
  conv at $h =>
    unfold Sentence.Realize mkInductionSentence
    rw [Formula.realize_imp];
    rw [Formula.realize_imp];
    conv =>
      lhs
      unfold Formula.Realize
      rw [BoundedFormula.realize_subst]
      change Formula.Realize _ _
    conv =>
      rhs; lhs
      rw [realize_iAlls'.Vars1]; ext
      rw [Formula.realize_flip]
      rw [realize_display1]
      rw [Formula.realize_imp];
      conv => lhs -- this is just `univ` already
      conv =>
        rhs
        unfold Formula.Realize
        rw [BoundedFormula.realize_subst]
        change Formula.Realize _ _
    simp only [delta0_simps]
    unfold Formula.Realize
    simp only [delta0_simps]
  )

/-- Coerce a bounded formula with no bound variables to a formula. -/
def _root_.FirstOrder.Language.BoundedFormula.toFormula' {L : Language} {a}
    (phi : L.BoundedFormula a 0) : L.Formula a := phi

-- This is induction sentence creator which instead of ∀x, φ(x),
-- gives you ∀x : int, φ(x)
/-- Build a typed induction sentence that guards the induction variable as numeric. -/
def mkInductionSentenceTyped
  {a} [IsEnum a] {name}
  {n}
  (phi : zambella.BoundedFormula ((Vars1 name) ⊕ a) n)
  : zambella.Sentence :=
  let univ := phi.alls.iAlls'
  let base := univ.subst (fun _ => 0)
  let step_assumption := univ
  let step_target : zambella.Formula (Vars1 name) := univ.subst (fun _ => (var .fv1) + 1)
  let step' : zambella.Formula (Vars1 name) := step_assumption ⟹ step_target
  let step := step'.IsNum.toFormula'.display1.flip.iAlls'
  let forall_x_holds := univ.IsNum.toFormula'.display1.flip.iAlls'
  base ⟹ step ⟹ forall_x_holds


-- Definition V.I.2 (Comprehension Axiom); p. 96 PDF; release of Logical Foundations
-- `X` cannot occur free in `phi(z)`, but `y` can
/-- Build the bounded-comprehension sentence associated to a displayed formula. -/
def mkComprehensionSentence {a} [IsEnum a] {name}
  (phi : zambella.Formula (((Vars1 name) ⊕ (Vars1 .y)) ⊕ a))
  : zambella.Sentence :=
    -- now `y` is accessible and nothing else!
    let univ : zambella.Formula (Vars1 name ⊕ Vars1 FvName.y)
      := phi.iAlls'
    -- X(z) ↔ φ(z)
    let iff : zambella.Formula (Vars3 .y .z .X) :=
      z ∈' X ⇔
      univ.subst (Sum.elim (fun _ => .var z.name) (fun _ => .var y.name))
    let iff : zambella.Formula (Vars1 .z ⊕ Vars2 .y .X) :=
      (display3 .z iff.rotate213)
    let all_z : zambella.Formula (Vars2 .y .X) :=
      iBdAllNumLt' y iff.flip
    let X_def : zambella.Formula (Vars1 .X ⊕ Vars1 .y) :=
      (display2 .X (X.IsStr ⊓ all_z).rotate21)
    let ex_X : zambella.Formula (Vars1 .y) := iExs' X_def.flip
    let ex_X_typed : zambella.Formula (Vars1 .y) :=
      ex_X.IsNum
    -- quantify over `y`, the length of str created
    ex_X_typed.mkInl.flip.iAlls'

/-- Normalize a realized comprehension sentence in a hypothesis. -/
syntax (name := simpComp) "simpComp" " at " (ppSpace ident)? : tactic

macro_rules
| `(tactic| simpComp at $h:ident) =>
  `(tactic|
  conv at $h =>
    unfold Sentence.Realize mkComprehensionSentence
    rw [realize_iAlls'.Vars1]; ext
    rw [realize_flip]
    rw [realize_mkInl]
    unfold Formula.IsNum
    rw [Formula.realize_imp]
    conv =>
      lhs
      rw [Term.realize_isnum]
      lhs; arg 1
      simp only [delta0_simps]
    rhs
    rw [realize_iExs'.Vars1]; right; ext
    rw [realize_flip]
    rw [realize_display2]
    rw [realize_rotate_21]
    rw [Formula.realize_inf]
    conv =>
      lhs
      rw [Term.realize_isstr]
      simp only [delta0_simps]
    conv =>
      rhs
      rw [realize_iBdAllNumLt'.Vars1]; ext
      conv =>
        lhs
        simp only [delta0_simps]
      ext
      ext
      rw [realize_flip]
      rw [realize_display3]
      rw [realize_rotate_213]
      rw [Formula.realize_iff]
      conv =>
        lhs
        unfold Formula.Realize
        simp only [delta0_simps]
      rhs
      unfold Formula.Realize
      rw [realize_subst]
      rw [Formula.boundedFormula_realize_eq_realize]
      rw [realize_iAlls'.Vars1]; ext
      simp only [delta0_simps]
  )
