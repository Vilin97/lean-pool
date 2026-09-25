/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.HomTraceNondegenerate

/-!
# Trace cyclicity on Hom classes

The accompanying paper's Lemma 3.5(a) on the category: the
descended trace of a composition is independent of the
order.  Bilinear induction
with `fragTrace_comm` at the singles.
-/

namespace RS

variable {R : ℕ} (f : EdgeRankParameter R)

/-- The descended trace is cyclic. -/
theorem HomSpace.traceMap_comp_comm {t u : ℕ}
    (p : HomSpace f.val (t + u)) (q : HomSpace f.val (u + t)) :
    HomSpace.traceMap f.val t
        (HomSpace.comp f t u t p q) =
      HomSpace.traceMap f.val u
        (HomSpace.comp f u t u q p) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ p
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  change traceFunctional f.val t (composeFinsupp t u t x y) =
    traceFunctional f.val u (composeFinsupp u t u y x)
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add x₁ x₂ h₁ h₂ =>
    simp only [map_add, LinearMap.add_apply]
    rw [h₁, h₂]
  | single F c =>
    induction y using Finsupp.induction_linear with
    | zero => simp only [map_zero, LinearMap.zero_apply]
    | add y₁ y₂ h₁ h₂ =>
      simp only [map_add, LinearMap.add_apply]
      rw [h₁, h₂]
    | single G c' =>
      rw [composeFinsupp_single, composeFinsupp_single]
      have h1 : ∀ (a b : ℕ) (H : Fragment (Fin (a + a)))
          (d : ℂ), traceFunctional f.val a
            (Finsupp.single H d) = d * fragTrace f.val H := by
        intro a b H d
        rw [show (Finsupp.single H d :
            Fragment (Fin (a + a)) →₀ ℂ) =
            d • Finsupp.single H 1 by
          rw [Finsupp.smul_single, smul_eq_mul, mul_one],
          map_smul, traceFunctional_single, smul_eq_mul]
      rw [h1 t u _ (c * c'), h1 u t _ (c' * c),
        fragTrace_comm f.val f.iso_invariant F G]
      ring

end RS
