/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.PowerSurj

/-!
# The same-cycle quotient of a permutation

The orbit space of a permutation of `Fin n` under the same-cycle
relation, its fintype structure, orbit sizes, and the
identification of functions fixed by the permutation with
functions on the orbit space.  This is the indexing object for the
cycle-sum identity: a permutation's completed cycle-type product
expands as a sum over colourings of its orbits.
-/

namespace RS

open Finset Equiv Equiv.Perm

variable {n : ℕ} (π : Equiv.Perm (Fin n))

/-- The same-cycle setoid of a permutation. -/
def sameCycleSetoid : Setoid (Fin n) where
  r a b := π.SameCycle a b
  iseqv := ⟨Equiv.Perm.SameCycle.refl π,
    Equiv.Perm.SameCycle.symm, Equiv.Perm.SameCycle.trans⟩

/-- The orbit space of a permutation. -/
def OrbitSpace : Type :=
  Quotient (sameCycleSetoid π)

/-- The class of a point. -/
def orbitOf (i : Fin n) : OrbitSpace π :=
  Quotient.mk (sameCycleSetoid π) i

/-- Two points have the same class exactly when they are on the same
cycle. -/
theorem orbitOf_eq_iff {i j : Fin n} :
    orbitOf π i = orbitOf π j ↔ π.SameCycle i j :=
  ⟨Quotient.exact, fun h => Quotient.sound h⟩

/-- Every orbit is the class of a point. -/
theorem orbitOf_surjective : Function.Surjective (orbitOf π) :=
  Quotient.mk_surjective

/-- The orbit space is finite, being a quotient of a finite type. -/
noncomputable instance : Fintype (OrbitSpace π) := by
  classical
  exact @Quotient.fintype (Fin n) _ (sameCycleSetoid π)
    (Classical.decRel _)

/-- The fibre of an orbit: the points lying in it. -/
noncomputable def orbFibre (O : OrbitSpace π) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => orbitOf π i = O)

/-- The size of an orbit. -/
noncomputable def orbCard (O : OrbitSpace π) : ℕ :=
  (orbFibre π O).card

/-- Membership in an orbit's fibre. -/
theorem mem_orbFibre {O : OrbitSpace π} {i : Fin n} :
    i ∈ orbFibre π O ↔ orbitOf π i = O := by
  classical
  rw [orbFibre]
  simp

/-- Every fibre is nonempty. -/
theorem orbFibre_nonempty (O : OrbitSpace π) :
    (orbFibre π O).Nonempty := by
  obtain ⟨i, rfl⟩ := orbitOf_surjective π O
  exact ⟨i, (mem_orbFibre π).mpr rfl⟩

/-- Hence every orbit has positive size. -/
theorem orbCard_pos (O : OrbitSpace π) : 0 < orbCard π O :=
  Finset.card_pos.mpr (orbFibre_nonempty π O)

/-- A function fixed by `π` is constant along powers. -/
theorem fixed_comp_zpow {C : Type*} {f : Fin n → C}
    (hf : f ∘ π = f) : ∀ k : ℤ, f ∘ (π ^ k : Equiv.Perm (Fin n)) = f := by
  have hinv : f ∘ ⇑π⁻¹ = f := by
    funext a
    have := congrFun hf (π⁻¹ a)
    simpa using this.symm
  intro k
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih =>
      funext a
      have h1 : (π ^ ((k : ℤ) + 1) : Equiv.Perm (Fin n)) a =
          (π ^ (k : ℤ) : Equiv.Perm (Fin n)) (π a) := by
        rw [show (π ^ ((k : ℤ) + 1) : Equiv.Perm (Fin n)) =
          (π ^ (k : ℤ)) * π from by rw [zpow_add, zpow_one]]
        rfl
      show f ((π ^ ((k : ℤ) + 1) : Equiv.Perm (Fin n)) a) = f a
      rw [h1]
      have h2 := congrFun ih (π a)
      simp only [Function.comp_apply] at h2
      rw [h2]
      exact congrFun hf a
  | pred k ih =>
      funext a
      have h1 : (π ^ ((-k : ℤ) - 1) : Equiv.Perm (Fin n)) a =
          (π ^ (-k : ℤ) : Equiv.Perm (Fin n)) (π⁻¹ a) := by
        rw [show (π ^ ((-k : ℤ) - 1) : Equiv.Perm (Fin n)) =
          (π ^ (-k : ℤ)) * π⁻¹ from by
            rw [zpow_sub, zpow_one]]
        rfl
      show f ((π ^ ((-k : ℤ) - 1) : Equiv.Perm (Fin n)) a) = f a
      rw [h1]
      have h2 := congrFun ih (π⁻¹ a)
      simp only [Function.comp_apply] at h2
      rw [h2]
      exact congrFun hinv a

/-- Functions fixed by the permutation are exactly the functions
on the orbit space. -/
noncomputable def fixedFunEquiv (C : Type*) :
    {f : Fin n → C // f ∘ π = f} ≃ (OrbitSpace π → C) where
  toFun f := Quotient.lift f.1 (by
    intro a b hab
    obtain ⟨k, hk⟩ := hab
    have := congrFun (fixed_comp_zpow π f.2 k) a
    simp only [Function.comp_apply] at this
    rw [← hk]
    exact this.symm ▸ this.symm ▸ this)
  invFun g := ⟨fun i => g (orbitOf π i), by
    funext i
    show g (orbitOf π (π i)) = g (orbitOf π i)
    refine congrArg g ((orbitOf_eq_iff π).mpr ?_)
    exact ⟨-1, by simp⟩⟩
  left_inv f := Subtype.ext (funext fun i => rfl)
  right_inv g := funext fun O => by
    obtain ⟨i, rfl⟩ := orbitOf_surjective π O
    rfl

/-- The identification reads a fixed function's value at any point
of the orbit. -/
@[simp] theorem fixedFunEquiv_apply_orbitOf {C : Type*}
    (f : {f : Fin n → C // f ∘ π = f}) (i : Fin n) :
    fixedFunEquiv π C f (orbitOf π i) = f.1 i := rfl

end RS
