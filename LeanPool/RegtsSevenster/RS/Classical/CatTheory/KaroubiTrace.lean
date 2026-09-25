/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.CatTheory.KaroubiLinear
import LeanPool.RegtsSevenster.RS.Classical.Algebra.TraceCriterion
import LeanPool.RegtsSevenster.RS.Common.NilpotentMap

/-!
# The trace criterion on a Karoubi corner

Nilpotence transports along the underlying-morphism map. Cyclicity
sandwiches arbitrary ambient tests into the corner, so a
nondegenerate trace that kills nilpotents proves semisimplicity
of every corner endomorphism algebra.
-/

namespace RS

open CategoryTheory CategoryTheory.Idempotents

/-- Nilpotent corner endomorphisms are nilpotent in the base category. -/
theorem karoubiEnd_isNilpotent {C : Type*} [Category C]
    [Preadditive C] {P : Karoubi C} {x : End P}
    (hx : IsNilpotent x) : IsNilpotent (show End P.X from x.f) :=
  isNilpotent_map_of_mul_zero (fun y : End P => (show End P.X from y.f))
    rfl (fun _ _ => rfl) hx

/-- A finite-dimensional ambient trace criterion restricts to a
Karoubi corner. -/
theorem karoubiEnd_isSemisimpleRing_of_trace {C : Type*} [Category C]
    [Preadditive C] [Linear ℂ C] (P : Karoubi C)
    [FiniteDimensional ℂ (End P.X)] (τ : End P.X →ₗ[ℂ] ℂ)
    (hnil : ∀ x : End P.X, IsNilpotent x → τ x = 0)
    (hcyc : ∀ a b : End P.X, τ (a ≫ b) = τ (b ≫ a))
    (hnd : ∀ a : End P.X, (∀ b : End P.X, τ (a ≫ b) = 0) → a = 0) :
    IsSemisimpleRing (End P) := by
  have : FiniteDimensional ℂ (End P) :=
    FiniteDimensional.of_injective
      (show End P →ₗ[ℂ] End P.X from karoubiHomLinearMap P P)
      (fun _ _ h => Karoubi.Hom.ext h)
  refine isSemisimpleRing_of_trace (τ.comp (karoubiHomLinearMap P P))
    (fun x hx => hnil x.f (karoubiEnd_isNilpotent hx)) (fun a ha => ?_)
  apply Karoubi.hom_ext
  apply hnd a.f
  intro b
  have hb : P.p ≫ (P.p ≫ b ≫ P.p) ≫ P.p = P.p ≫ b ≫ P.p := by
    simp only [Category.assoc]
    rw [show P.p ≫ P.p ≫ b ≫ P.p ≫ P.p =
      (P.p ≫ P.p) ≫ b ≫ (P.p ≫ P.p) from by
        simp only [Category.assoc]]
    rw [P.idem]
  have key := ha (⟨P.p ≫ b ≫ P.p, hb⟩ : End P)
  have hred : a.f ≫ (P.p ≫ b ≫ P.p) = (a.f ≫ b) ≫ P.p := by
    rw [show a.f ≫ (P.p ≫ b ≫ P.p) =
      (a.f ≫ P.p) ≫ b ≫ P.p from by simp only [Category.assoc]]
    rw [Karoubi.comp_p]
    simp only [Category.assoc]
  calc τ (a.f ≫ b) = τ (P.p ≫ (a.f ≫ b)) := by
        rw [show P.p ≫ (a.f ≫ b) = (P.p ≫ a.f) ≫ b from by
          simp only [Category.assoc], Karoubi.p_comp]
    _ = τ ((a.f ≫ b) ≫ P.p) := hcyc _ _
    _ = τ (a.f ≫ (P.p ≫ b ≫ P.p)) := by rw [hred]
    _ = 0 := key

end RS
