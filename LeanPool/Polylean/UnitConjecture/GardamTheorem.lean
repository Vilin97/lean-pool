/-
Copyright (c) 2026 Siddhartha Gadgil, Anand Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Anand Rao
-/

import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Defs
import LeanPool.Polylean.UnitConjecture.TorsionFree
import LeanPool.Polylean.UnitConjecture.GroupRing

/-!

## Giles Gardam's result

The proof of the theorem `𝔽₂[P]` has non-trivial units. Together with the main
result of `TorsionFree` -- that `P` is torsion-free, this completes the formal
proof of Gardam's theorem that Kaplansky's Unit Conjecture is false.
-/

namespace LeanPool.Polylean




/-! ### Preliminaries -/

/-- An element of a free module is trivial but not zero if it is supported on one basis vector. -/
def trivialNonZeroElem {R X : Type _} [Ring R] [DecidableEq X] [DecidableEq R]
    (a : FreeModule R X) : Prop :=
  ∃! x : X, FreeModule.coordinates x a ≠ 0

/-- The statement of Kaplansky's Unit Conjecture:
The only units in a group ring, when the group is torsion-free and the ring is a field,
are the trivial units. -/
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

namespace P

/-!
The main constants of the group `P`.
-/

/-- The first kernel generator of the Promislow group. -/
abbrev x : P := (K.x, Q.e)
/-- The second kernel generator of the Promislow group. -/
abbrev y : P := (K.y, Q.e)
/-- The third kernel generator of the Promislow group. -/
abbrev z : P := (K.z, Q.e)
/-- The first nontrivial quotient generator of the Promislow group. -/
abbrev a : P := ((0, 0, 0), Q.a)
/-- The second nontrivial quotient generator of the Promislow group. -/
abbrev b : P := ((0, 0, 0), Q.b)

end P

namespace Gardam

open P

/-- Embed a group element as the corresponding basis element of `𝔽₂[P]`. -/
private abbrev groupRingOf (g : P) : 𝔽₂[P] :=
  ⟦[(1, g)]⟧

/-- The group-ring multiplication, made explicit to avoid the monomial `HMul R G` notation. -/
private abbrev ringMul (u v : 𝔽₂[P]) : 𝔽₂[P] :=
  GroupRing.mul u v

/-- The `p` component of Gardam's non-trivial unit `α`. -/
def p : 𝔽₂[P] :=
  (1 : 𝔽₂[P]) + groupRingOf x + groupRingOf y + groupRingOf (x * y) +
    groupRingOf (z⁻¹) + groupRingOf (x * z⁻¹) + groupRingOf (y * z⁻¹) +
    groupRingOf (x * y * z⁻¹)
/-- The `q` component of Gardam's non-trivial unit `α`. -/
def q : 𝔽₂[P] := groupRingOf (x⁻¹ * y⁻¹) + groupRingOf x + groupRingOf (y⁻¹ * z) +
  groupRingOf z
/-- The `r` component of Gardam's non-trivial unit `α`. -/
def r : 𝔽₂[P] := (1 : 𝔽₂[P]) + groupRingOf x + groupRingOf (y⁻¹ * z) +
  groupRingOf (x * y * z)
/-- The `s` component of Gardam's non-trivial unit `α`. -/
def s : 𝔽₂[P] := (1 : 𝔽₂[P]) + groupRingOf (x * z⁻¹) + groupRingOf (x⁻¹ * z⁻¹) +
  groupRingOf (y * z⁻¹) + groupRingOf (y⁻¹ * z⁻¹)

/-- The non-trivial unit `α`. -/
def α : 𝔽₂[P] :=
  p + ringMul q (groupRingOf a) + ringMul r (groupRingOf b) +
    ringMul (ringMul s (groupRingOf a)) (groupRingOf b)

/-- The `p'` component of the inverse `α'`. -/
def p' : 𝔽₂[P] :=
  ringMul (groupRingOf (x⁻¹))
    (ringMul (ringMul (groupRingOf (a⁻¹)) p) (groupRingOf a))
/-- The `q'` component of the inverse `α'`. -/
def q' : 𝔽₂[P] := -ringMul (groupRingOf (x⁻¹)) q
/-- The `r'` component of the inverse `α'`. -/
def r' : 𝔽₂[P] := -ringMul (groupRingOf (y⁻¹)) r
/-- The `s'` component of the inverse `α'`. -/
def s' : 𝔽₂[P] :=
  ringMul (groupRingOf (z⁻¹))
    (ringMul (ringMul (groupRingOf (a⁻¹)) s) (groupRingOf a))

/-- The inverse `α'` of the non-trivial unit `α`. -/
def α' : 𝔽₂[P] :=
  p' + ringMul q' (groupRingOf a) + ringMul r' (groupRingOf b) +
    ringMul (ringMul s' (groupRingOf a)) (groupRingOf b)

end Gardam

/-!
### Verification

The main verification of Giles Gardam's result.
-/

namespace Gardam

open P

/-- A proof that the unit is non-trivial. -/
theorem α_nonTrivial : ¬ (trivialNonZeroElem α) := by
  intro ⟨g, _, eqg⟩
  exact (by decide : z⁻¹ ≠ x * y) ((eqg z⁻¹ (by decide)).trans (eqg (x * y) (by decide)).symm)

/-! The fact that the counter-example `α` is in fact a unit of the group ring `𝔽₂[P]`
  is verified by computing the product of `α` with its inverse `α'` and checking that the
  result is `(1 : 𝔽₂[P])`.

  The computational aspects of the group ring implementation and the Metabelian construction
  are used here. -/

/-- The product of Gardam's unit and its inverse is one. -/
theorem α_mul_α' : ringMul α α' = (1 : 𝔽₂[P]) := by
  decide +kernel

/-- The product of Gardam's inverse and its unit is one. -/
theorem α'_mul_α : ringMul α' α = (1 : 𝔽₂[P]) := by
  decide +kernel

/-- A proof of the existence of a non-trivial unit in `𝔽₂[P]`. -/
def Counterexample : {u : (𝔽₂[P])ˣ // ¬(trivialNonZeroElem u.val)} :=
  ⟨⟨α, α', α_mul_α', α'_mul_α⟩, α_nonTrivial⟩

/-- Giles Gardam's result - Kaplansky's Unit Conjecture is false. -/
theorem GardamTheorem : ¬ UnitConjecture :=
   fun conjecture => Counterexample.prop <|
    conjecture (F := 𝔽₂) (G := P) Counterexample.val

end Gardam

/-!
We check that our definition of "trivial but not zero" is correct by showing it equivalent
to a more direct definition.
-/

theorem trivialNonZeroElem_trivial_nonzeroAux {R G : Type _} [Ring R] [Group G]
    [DecidableEq G] [DecidableEq R] (p : FormalSum R G) :
    trivialNonZeroElem  ⟦p⟧  ↔  ∃ a: R, ∃ g : G, p ≈ [(a, g)] ∧ (a ≠ 0) := by
  apply Iff.intro
  · rw [trivialNonZeroElem]
    intro ⟨x, hyp₁, hyp₂⟩
    refine ⟨FreeModule.coordinates x ⟦p⟧, x, ?_, hyp₁⟩
    funext x₁
    simp only [FormalSum.coords, monomCoeff, FreeModule.coordinates, Quotient.lift_mk, add_zero]
    by_cases h : x = x₁
    · simp [h]
    · simp only [beq_false_of_ne h]
      by_cases hc : FormalSum.coords p x₁ = 0
      · exact hc
      · exact absurd (hyp₂ x₁ (by simp [FreeModule.coordinates, hc])) (Ne.symm h)
  · intro ⟨a, g, hyp⟩
    simp only [trivialNonZeroElem, ne_eq]
    use g
    refine ⟨?_, ?_⟩
    · intro h
      simp only [FreeModule.coordinates, Quotient.lift_mk] at h
      have : p.coords = FormalSum.coords [(a, g)] := hyp.left
      rw [this] at h
      simp only [FormalSum.coords, monomCoeff, beq_self_eq_true, add_zero] at h
      exact absurd h hyp.right
    · intro x h
      simp only [FreeModule.coordinates, Quotient.lift_mk] at h
      have : p.coords = FormalSum.coords [(a, g)] := hyp.left
      rw [this] at h
      simp only [FormalSum.coords, monomCoeff, add_zero] at h
      by_cases c : x = g
      · exact c
      · simp only [beq_false_of_ne (Ne.symm c), not_true] at h

/-- Triviality of `p : R[G]` coincides with the direct definition `p = a ⬝ g`, `a ≠ 0`. -/
theorem trivialNonZeroElem_trivial_nonzero {R G : Type _} [Ring R] [Group G]
    [DecidableEq G] [DecidableEq R] :
    ∀ (p : FreeModule R G),
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
