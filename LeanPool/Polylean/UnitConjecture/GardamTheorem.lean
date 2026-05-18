/-
Copyright (c) 2026 Siddhartha Gadgil, Anand Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Anand Rao
-/

import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Defs
import LeanPool.Polylean.UnitConjecture.TorsionFree
import LeanPool.Polylean.UnitConjecture.GroupRing

namespace LeanPool.Polylean


/-!

## Giles Gardam's result

The proof of the theorem `𝔽₂[P]` has non-trivial units. Together with the main result of `TorsionFree` -- that `P` is torsion-free,
this completes the formal proof of Gardam's theorem that Kaplansky's Unit Conjecture is false.
-/


section Preliminaries

/-! ### Preliminaries -/

/-- The definition of an element of a free module being trivial but not zero, i.e., of the form `k•x` for `x : X` and `k ≠ 0`. -/
def trivialNonZeroElem {R X : Type _} [Ring R] [DecidableEq X][DecidableEq R] (a : FreeModule R X) : Prop :=
  ∃! x : X, FreeModule.coordinates x a ≠ 0

/-- The statement of Kaplansky's Unit Conjecture:
The only units in a group ring, when the group is torsion-free and the ring is a field, are the trivial units. -/
def UnitConjecture : Prop :=
  ∀ {F : Type _} [Field F] [DecidableEq F]
  {G : Type _} [Group G] [DecidableEq G] [TorsionFree G],
    ∀ u : (F[G])ˣ, trivialNonZeroElem (u : F[G])

/-- The finite field on two elements. -/
abbrev 𝔽₂ := Fin 2

instance : Field 𝔽₂ where
  inv := id
  exists_pair_ne := ⟨0, 1, by decide⟩
  mul_inv_cancel := fun
    | 0 => by intro; contradiction
    | 1 => by intro; rfl
  inv_zero := rfl
  div_eq_mul_inv := by decide
  qsmul := _
  nnqsmul := _

instance ringElem : Coe P (𝔽₂[P]) where
    coe g := ⟦[(1, g)]⟧

end Preliminaries

section Constants

namespace P

/-!
The main constants of the group `P`.
-/

abbrev x : P := (K.x, Q.e)
abbrev y : P := (K.y, Q.e)
abbrev z : P := (K.z, Q.e)
abbrev a : P := ((0, 0, 0), Q.a)
abbrev b : P := ((0, 0, 0), Q.b)

end P

namespace Gardam

open P

/-! The components of the non-trivial unit `α`. -/
def p : 𝔽₂[P] := (1 : 𝔽₂[P]) +  x +  y +  x*y +  z⁻¹ + x*z⁻¹ + y*z⁻¹ + x*y*z⁻¹
def q : 𝔽₂[P] := (x⁻¹*y⁻¹ : 𝔽₂[P]) + x + y⁻¹*z + z
def r : 𝔽₂[P] := (1 : 𝔽₂[P]) + x + y⁻¹*z + x*y*z
def s : 𝔽₂[P] := (1 : 𝔽₂[P]) + x*z⁻¹ + x⁻¹*z⁻¹ + y*z⁻¹ + y⁻¹*z⁻¹

/-- The non-trivial unit `α`. -/
def α : 𝔽₂[P] := p  +  q * a  +  r * b  +  s * a * b

/-! The components of the inverse `α'` of the non-trivial unit `α`. -/
def p' : 𝔽₂[P] := x⁻¹ * (a⁻¹  * p * a)
def q' : 𝔽₂[P] := -(x⁻¹ * q)
def r' : 𝔽₂[P] := -(y⁻¹ * r)
def s' : 𝔽₂[P] := z⁻¹ * (a⁻¹ * s * a)

/-- The inverse `α'` of the non-trivial unit `α`. -/
def α' : 𝔽₂[P] := p'  +  q' * a  +  r' * b  +  s' * a * b

end Gardam

end Constants


section Verification

/-!
### Verification

The main verification of Giles Gardam's result.
-/

namespace Gardam

open P

/-- A proof that the unit is non-trivial. -/
theorem α_nonTrivial : ¬ (trivialNonZeroElem α) := by
    intro ⟨g, _, (eqg : ∀ y, α.coordinates y ≠ 0 → y = g)⟩
    have l₁ : z⁻¹ = g := by
      apply eqg; decide
    have l₂ : x * y = g := by
      apply eqg; decide
    have l₃ : z⁻¹ = x * y := by
      refine' Eq.trans _ (Eq.symm _) <;> assumption
    simp  at l₃
    have l₄ : z⁻¹ ≠ x * y := by
      decide
    simp [l₃] at l₄

/-! The fact that the counter-example `α` is in fact a unit of the group ring `𝔽₂[P]` is verified by
  computing the product of `α` with its inverse `α'` and checking that the result is `(1 : 𝔽₂[P])`.

  The computational aspects of the group ring implementation and the Metabelian construction are used here. -/

/-- A proof of the existence of a non-trivial unit in `𝔽₂[P]`. -/
def Counterexample : {u : (𝔽₂[P])ˣ // ¬(trivialNonZeroElem u.val)} :=
  ⟨⟨α, α', by native_decide, by native_decide⟩, α_nonTrivial⟩

/-- Giles Gardam's result - Kaplansky's Unit Conjecture is false. -/
theorem GardamTheorem : ¬ UnitConjecture :=
   fun conjecture => Counterexample.prop <|
    conjecture (F := 𝔽₂) (G := P) Counterexample.val

end Gardam

end Verification

/-!
We check that our definition of "trivial but not zero" is correct by showing it equivalent to a more direct definition.
-/

theorem trivialNonZeroElem_trivial_nonzeroAux {R G : Type _} [Ring R] [Group G] [DecidableEq G] [DecidableEq R] (p : FormalSum R G) :
    trivialNonZeroElem  ⟦p⟧  ↔  ∃ a: R, ∃ g : G, p ≈ [(a, g)] ∧ (a ≠ 0) := by
  apply Iff.intro
  · rw [trivialNonZeroElem]
    intro ⟨x, hyp⟩
    let ⟨hyp₁, hyp₂⟩ := hyp
    use FreeModule.coordinates x ⟦p⟧
    use x
    apply And.intro
    · funext x₁
      simp only [FormalSum.coords, monomCoeff, FreeModule.coordinates, Quotient.lift_mk, add_zero]
      by_cases h:x = x₁
      · simp [h]
      · let hyp₃ := hyp₂ x₁
        simp only [h, FreeModule.coordinates, Quot.lift_mk, ne_eq] at hyp₃
        let neqLem : ((x == x₁) = false) :=
          by apply beq_false_of_ne; assumption
        simp only [neqLem]
        by_cases h:FormalSum.coords p x₁ = 0
        · assumption
        · simp only [Quotient.lift_mk, h, not_false_iff, forall_true_left] at hyp₃
          have := Eq.symm hyp₃
          contradiction
    · assumption
  · intro ⟨a, g, hyp⟩
    simp only [trivialNonZeroElem, ne_eq]
    use g
    apply And.intro
    · intro h
      simp only [FreeModule.coordinates, Quotient.lift_mk] at h
      have : p.coords = FormalSum.coords [(a, g)] := hyp.left
      rw [this] at h
      simp only [FormalSum.coords, monomCoeff, beq_self_eq_true, add_zero] at h
      have := hyp.right
      contradiction
    · intro x h
      simp only [FreeModule.coordinates, Quotient.lift_mk] at h
      have : p.coords = FormalSum.coords [(a, g)] := hyp.left
      rw [this] at h
      simp only [FormalSum.coords, monomCoeff, add_zero] at h
      by_cases c:x = g
      · assumption
      · have neq : (g == x) = false := by aesop
        simp only [neq, not_true] at h

/-- Our definition of tiviality of `p : R[G]` coincides with the direct definition `p = a ⬝ g` with `a ≠ 0` -/
theorem trivialNonZeroElem_trivial_nonzero {R G : Type _} [Ring R] [Group G] [DecidableEq G] [DecidableEq R]: ∀  (p : FreeModule R G),
    trivialNonZeroElem  p  ↔  ∃ a: R, ∃ g : G, p = (a * g) ∧ (a ≠ 0) := by
  rw [groupRingMul]
  apply Quotient.ind
  simp only [trivialNonZeroElem_trivial_nonzeroAux]
  conv =>
    enter [a, 2, 1, a, 1, g, 1]
    rw [Quotient.eq]
  intro a
  rfl

end LeanPool.Polylean
