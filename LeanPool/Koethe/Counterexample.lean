/-
Copyright (c) 2026 Tom Adamczewski and Epoch AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GPT-6 Astra, Tom Adamczewski
-/
module

public import Mathlib.Algebra.AlgebraicCard
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Tactic.Ring
public import LeanPool.Koethe.Mortality.MaskMortality
public import LeanPool.Koethe.MaskSequence.Universal
public import LeanPool.Koethe.Linearization.Nil
public import LeanPool.Koethe.ShiftWitness.Witness

/-!
# The counterexample: a nil ideal with a non-nilpotent `2 × 2` matrix

This file assembles the whole development. The scalar-linearization theorem
`KoetheCounterexample.nil_of_all_pencils_nil` discharges the explicit hypothesis of
`KoetheCounterexample.ShiftWitness.exists_nilideal_nonnil_matrix`, and the ground field
`GroundField = AlgebraicClosure (ULift (ZMod 2))` is countable and algebraically closed, so
`exists_universalMortalSequence` and `maskMortality` apply to it. The result is a ring `R`
in an arbitrary universe, a nil two-sided ideal `I ⊆ R`, and a matrix in `M_2(I)` that is
not nilpotent.
-/

@[expose] public section

noncomputable section

universe u

namespace KoetheCounterexample

/-- A universal mortal sequence over any field produces a nil two-sided ideal
in a unital ring, with a nonnilpotent two-by-two matrix over that ideal. -/
theorem exists_nilideal_nonnil_matrix_of_universal_mortal
    {k : Type u} [Field k] (v : ℕ → Triple k) (hv : UniversalMortalSequence k v) :
    ∃ (R : Type u) (_ : Ring R) (I : TwoSidedIdeal R),
      (∀ x ∈ I, IsNilpotent x) ∧
        ∃ W : Matrix (Fin 2) (Fin 2) R,
          W ∈ TwoSidedIdeal.matrix (Fin 2) I ∧ ¬ IsNilpotent W :=
  ShiftWitness.exists_nilideal_nonnil_matrix v hv nil_of_all_pencils_nil

/-- The countable algebraically closed ground field `\overline{𝔽₂}`, lifted to an arbitrary
universe so that the counterexample exists in every universe. -/
abbrev GroundField : Type u := AlgebraicClosure (ULift.{u} (ZMod 2))

instance countable_groundField : Countable (GroundField.{u}) :=
  Set.countable_univ_iff.mp <|
    (Algebraic.countable (ULift.{u} (ZMod 2)) (GroundField.{u})).mono
      fun x _ => Algebra.IsAlgebraic.isAlgebraic x

/-- **A counterexample to nilness of finite matrix ideals.** In every universe there is a
ring `R` with a nil two-sided ideal `I` such that the matrix ideal `M_2(I)` of `M_2(R)`
contains a non-nilpotent matrix. -/
theorem counterexample :
    ∃ (R : Type u) (_ : Ring R) (I : TwoSidedIdeal R),
      (∀ x ∈ I, IsNilpotent x) ∧
        ∃ W : Matrix (Fin 2) (Fin 2) R,
          W ∈ TwoSidedIdeal.matrix (Fin 2) I ∧ ¬ IsNilpotent W := by
  obtain ⟨v, hv⟩ := exists_universalMortalSequence (GroundField.{u})
    (maskMortality (GroundField.{u}))
  exact exists_nilideal_nonnil_matrix_of_universal_mortal v hv

end KoetheCounterexample

end
