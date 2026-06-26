/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import LeanPool.GodelLoeb.Provable

/-!
# Kripke frames and the basic modal axioms

This file develops elementary Kripke-frame semantics for normal modal
logic and the project-level forcing bridge for polymorphic modal
formulas.

The `kreiselFixed` clause in `Forces` is intentionally an identity on the
inner formula, just like `quote`. The diagonal content of the modal-axiomatic
postulate is not derived by that clause; for formulas using `kreiselFixed`, the
semantic load is carried by the explicit `PropTautSound` assumption used by
`provable_forces`. An arithmetic-realisation substrate would replace that
assumption with a concrete frame or arithmetic soundness theorem.
-/

namespace ModalLogic.GoedelLoeb

universe u w

/-- A Kripke frame is a type of worlds equipped with accessibility. -/
structure KripkeFrame where
  /-- The type of possible worlds. -/
  World : Type w
  /-- The accessibility relation between worlds. -/
  accessible : World → World → Prop

namespace KripkeFrame

variable (F : KripkeFrame)

/-- Necessity at a world. -/
def necessarily (P : F.World → Prop) (w : F.World) : Prop :=
  ∀ v, F.accessible w v → P v

/-- Possibility at a world. -/
def possibly (P : F.World → Prop) (w : F.World) : Prop :=
  ∃ v, F.accessible w v ∧ P v

variable {F}

/-- The distribution axiom of normal modal logic. -/
lemma distrib_K {P Q : F.World → Prop} {w : F.World}
    (hImp : F.necessarily (fun v => P v → Q v) w)
    (hP : F.necessarily P w) :
    F.necessarily Q w := by
  intro v hwv
  exact hImp v hwv (hP v hwv)

/-- The reflexivity axiom of normal modal logic. -/
lemma refl_T (hRefl : ∀ w, F.accessible w w)
    {P : F.World → Prop} {w : F.World}
    (h : F.necessarily P w) : P w :=
  h w (hRefl w)

/-- The transitivity axiom of normal modal logic. -/
lemma four
    (hTrans : ∀ w₁ w₂ w₃, F.accessible w₁ w₂ → F.accessible w₂ w₃ →
      F.accessible w₁ w₃)
    {P : F.World → Prop} {w : F.World}
    (h : F.necessarily P w) :
    F.necessarily (fun u => F.necessarily P u) w := by
  intro v hwv u hvu
  exact h u (hTrans w v u hwv hvu)

/-- The Euclidean axiom of normal modal logic. -/
lemma five
    (hEucl : ∀ w₁ w₂ w₃, F.accessible w₁ w₂ → F.accessible w₁ w₃ →
      F.accessible w₂ w₃)
    {P : F.World → Prop} {w : F.World}
    (h : F.possibly P w) :
    F.necessarily (fun u => F.possibly P u) w := by
  obtain ⟨u, hwu, hPu⟩ := h
  intro v hwv
  exact ⟨u, hEucl w v u hwv hwu, hPu⟩

open ModalFormula

/--
Project-level forcing relation for `ModalFormula α`.

The `quote` and `kreiselFixed` cases are both transparent at this Kripke layer.
That is deliberately weaker than the `propEval` postulate for `kreiselFixed`;
the bridge from propositional tautologies to forcing is the separate
`PropTautSound` hypothesis.
-/
def Forces {α : Type u} (val : α → F.World → Prop) (w : F.World) :
    ModalFormula α → Prop
  | atom a => val a w
  | bot => False
  | impl phi psi => Forces val w phi → Forces val w psi
  | iff phi psi => Forces val w phi ↔ Forces val w psi
  | box phi => ∀ v, F.accessible w v → Forces val v phi
  | quote phi => Forces val w phi
  | kreiselFixed phi => Forces val w phi

/--
Semantic soundness assumption for the project-level tautology schema.

For `kreiselFixed`-bearing formulas this is the Kripke-side counterpart of the
modal-axiomatic postulate in `propEval`; `Forces` alone does not derive that
diagonal content.
-/
def PropTautSound {α : Type u} (val : α → F.World → Prop) : Prop :=
  ∀ {w : F.World} {phi : ModalFormula α}, phi.PropTaut → Forces (F := F) val w phi

/-- Apply an explicit propositional-tautology soundness assumption. -/
lemma propTaut_forces {α : Type u} {val : α → F.World → Prop} {w : F.World}
    {phi : ModalFormula α} (hSound : PropTautSound (F := F) val) (h : phi.PropTaut) :
    Forces (F := F) val w phi :=
  hSound h

/--
Soundness of the canonical K4 proof predicate for every transitive frame,
conditional on the explicit `PropTautSound` bridge for propositional
tautologies.
-/
theorem provable_forces {α : Type u} {F : KripkeFrame}
    (hTrans : ∀ w₁ w₂ w₃, F.accessible w₁ w₂ → F.accessible w₂ w₃ →
      F.accessible w₁ w₃)
    {val : α → F.World → Prop}
    (hProp : PropTautSound (F := F) val)
    {phi : ModalFormula α} (h : Provable phi) :
    ∀ w : F.World, Forces (F := F) val w phi := by
  induction h with
  | pl_taut hTaut =>
      intro w
      exact propTaut_forces (F := F) hProp hTaut
  | ax_K phi psi =>
      intro w hBoxImp hBoxPhi v hwv
      exact hBoxImp v hwv (hBoxPhi v hwv)
  | ax_four phi =>
      intro w hBoxPhi v hwv u hvu
      exact hBoxPhi u (hTrans w v u hwv hvu)
  | mp hImp hPhi ihImp ihPhi =>
      intro w
      exact ihImp w (ihPhi w)
  | nec hPhi ihPhi =>
      intro w v _hAcc
      exact ihPhi v

end KripkeFrame

end ModalLogic.GoedelLoeb
