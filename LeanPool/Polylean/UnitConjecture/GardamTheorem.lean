/-
Copyright (c) 2026 Siddhartha Gadgil, Anand Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Anand Rao
-/

import LeanPool.Polylean.UnitConjecture.GardamDefs
import LeanPool.Polylean.UnitConjecture.GardamMulAlpha
import LeanPool.Polylean.UnitConjecture.GardamMulAlphaPrime

namespace LeanPool.Polylean


/-!

## Giles Gardam's result

The proof of the theorem `𝔽₂[P]` has non-trivial units. Together with the main
result of `TorsionFree` -- that `P` is torsion-free, this completes the formal
proof of Gardam's theorem that Kaplansky's Unit Conjecture is false.

The definitions of `α`, `α'`, and the proof of `α_nonTrivial` live in
`GardamDefs`. The two heavy `decide +kernel` checks `α · α' = 1` and
`α' · α = 1` live in `GardamMulAlpha` and `GardamMulAlphaPrime` so they
build in parallel.
-/

namespace Gardam

open P

/-! The fact that the counter-example `α` is in fact a unit of the group ring `𝔽₂[P]`
  is verified by computing the product of `α` with its inverse `α'` and checking that the
  result is `(1 : 𝔽₂[P])`.

  The computational aspects of the group ring implementation and the Metabelian construction
  are used here. -/

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
        simp only [FreeModule.coordinates, ne_eq] at hyp₃
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
