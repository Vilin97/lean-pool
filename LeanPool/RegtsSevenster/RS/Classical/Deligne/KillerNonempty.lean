/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.PieriPos
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.SchurVanishing

/-!
# Upgrading a killing diagram to a nonempty one

Schur vanishing is upward closed, and the empty diagram is below
every diagram, so a killed object is killed at some diagram with
at least one cell.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory

universe v u

variable {A : Type u}

/-- A diagram with no cells is the empty diagram. -/
theorem YoungDiagram.eq_bot_of_card_eq_zero {lam : YoungDiagram}
    (h : lam.card = 0) : lam = ⊥ := by
  ext c
  constructor
  · intro hc
    exact absurd (Finset.card_eq_zero.mp h ▸ hc)
      (Finset.notMem_empty c)
  · intro hc
    exact absurd hc (Finset.notMem_empty c)

/-- **A killed object is killed at a nonempty diagram.** -/
theorem exists_killer_card_ne_zero
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] [MonoidalPreadditive A]
    [MonoidalLinear ℂ A]
    (P : SchurPackage.{v}) {X : A}
    {lam : YoungDiagram} (h : SchurKilled P X lam) :
    ∃ mu : YoungDiagram, mu.card ≠ 0 ∧ SchurKilled P X mu := by
  by_cases hc : lam.card = 0
  · refine ⟨(rowShape 1).val, ?_, ?_⟩
    · rw [(rowShape 1).prop]
      exact one_ne_zero
    · refine SchurKilled.mono P ?_ h
      rw [YoungDiagram.eq_bot_of_card_eq_zero hc]
      exact bot_le
  · exact ⟨lam, hc, h⟩

end RS
