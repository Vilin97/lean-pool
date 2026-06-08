/-
Copyright (c) 2026 Barinder S. Banwait. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Barinder S. Banwait
-/

/-
Attribution: This file is adapted from
  ~/Documents/QuadraticIntegers/QuadraticIntegers/RingOfIntegers.lean
by Brasca et al. The theorem `ring_of_integers_neg7` is the specialisation of
`QuadraticInteger.d_1` at d = -7, e = (d-1)/4 = -2, giving
`IsIntegralClosure (QuadraticAlgebra ℤ (-2) 1) ℤ K'`.
-/

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring
import LeanPool.RamanujanNagell.QuadraticIntegers.QuadraticIntegerROI

/-! ## The field ℚ(√-7) presented as QuadraticAlgebra ℚ (-7) 0

In this presentation ω' satisfies (ω')² = -7 + 0·ω' = -7, so ω' = √(-7).
-/

open QuadraticAlgebra

noncomputable section

/-- The number field `ℚ(√-7)`, presented as `QuadraticAlgebra ℚ (-7) 0`. -/
notation "K'" => QuadraticAlgebra ℚ (-7 : ℤ) 0

/-! ## Algebra instance: QuadraticAlgebra ℤ (-2) 1 → K'

The ring map sends the ℤ-generator ω_int (satisfying ω_int² = -2 + ω_int) to
(1 + ω')/2 in K', where ω' satisfies (ω')² = -7. Indeed:
  ((1 + ω')/2)² = (1 + 2ω' + (ω')²)/4 = (1 + 2ω' - 7)/4 = (-6 + 2ω')/4
                = -3/2 + ω'/2
  -2 + 1·((1 + ω')/2) = -2 + 1/2 + ω'/2 = -3/2 + ω'/2  ✓
This is `QuadraticInteger.d_1`'s algebra instance at d = -7, e = -2.
-/

/-- The proof that (1/2)·(ω'+1) satisfies the relation for QuadraticAlgebra ℤ (-2) 1. -/
private def algK'Proof : (1 / 2 : ℚ) • ((ω : K') + 1) * ((1 / 2 : ℚ) • ((ω : K') + 1)) =
    (-2 : ℤ) • (1 : K') + (1 : ℤ) • ((1 / 2 : ℚ) • ((ω : K') + 1)) := by
  ext
  · simp only [re_mul, re_smul, im_smul, omega_re, omega_im, re_add, im_add, re_one, im_one,
               add_zero, zero_add]
    simp only [smul_eq_mul]; ring
  · simp only [im_mul, re_smul, im_smul, omega_re, omega_im, re_add, im_add, re_one, im_one,
               add_zero, zero_add]
    simp only [smul_eq_mul]; ring

noncomputable instance algebraIntZK' : Algebra (QuadraticAlgebra ℤ (-2 : ℤ) 1) K' :=
  (QuadraticAlgebra.lift (R := ℤ) ⟨(1 / 2 : ℚ) • ((ω : K') + 1), algK'Proof⟩).toRingHom.toAlgebra

/-- The algebra map sends ω to (1+ω')/2. -/
lemma algebraMap_omega_K' :
    algebraMap (QuadraticAlgebra ℤ (-2 : ℤ) 1) K' (ω : QuadraticAlgebra ℤ (-2 : ℤ) 1) =
    (1 / 2 : ℚ) • ((ω : K') + 1) := by
  have h := QuadraticAlgebra.lift_symm_apply_coe
    (QuadraticAlgebra.lift (R := ℤ) ⟨(1 / 2 : ℚ) • ((ω : K') + 1), algK'Proof⟩)
  rw [Equiv.symm_apply_apply] at h
  exact h.symm

/-! ## The ring of integers of K'

Specialisation of `QuadraticInteger.d_1` at d = -7, e = -2:
- d = -7 ≡ 1 [ZMOD 4]  (since -7 = 4·(-2) + 1)
- e = (d - 1)/4 = (-7 - 1)/4 = -2
- S = QuadraticAlgebra ℤ e 1 = QuadraticAlgebra ℤ (-2) 1

This is exactly the ring ℤ[θ] in our main file (where θ satisfies θ² = θ - 2),
which is the ring of integers of ℚ(√-7) since disc(θ² - θ + 2) = 1 - 8 = -7.
-/
theorem ring_of_integers_neg7 : IsIntegralClosure (QuadraticAlgebra ℤ (-2 : ℤ) 1) ℤ K' := by
  haveI hsq : Fact (Squarefree (-7 : ℤ)) :=
    ⟨by have h7 : Squarefree (7 : ℤ) := (show Prime (7 : ℤ) from by norm_num).squarefree
        exact fun x hx ↦ h7 x (dvd_neg.mpr hx)⟩
  haveI halt : (-7 : ℤ).natAbs.AtLeastTwo := ⟨by norm_num⟩
  haveI hmod : Fact ((-7 : ℤ) ≡ 1 [ZMOD 4]) := ⟨by decide⟩
  haveI : Algebra (QuadraticAlgebra ℤ (-2 : ℤ) 1) K' :=
    (QuadraticAlgebra.lift (R := ℤ)
      ⟨(1 + (ω : K')) / 2, QuadraticInteger.algebra_S_K (d := -7)⟩).toRingHom.toAlgebra
  -- Inline the lemma application directly into convert
  convert @QuadraticInteger.d_1 (-7 : ℤ) hsq halt hmod using 1
  refine Algebra.algebra_ext_iff.mpr (RingHom.ext_iff.mp ?_)
  unfold algebraIntZK'
    -- The `change` here is optional documentation, but good for readability
  change (QuadraticAlgebra.lift (R := ℤ) ⟨(1 / 2 : ℚ) • ((ω : K') + 1), algK'Proof⟩).toRingHom =
    (QuadraticAlgebra.lift (R := ℤ)
        ⟨(1 + (ω : K')) / 2, QuadraticInteger.algebra_S_K (d := -7)⟩).toRingHom
  congr 1; congr 1; apply Subtype.ext
  change (1 / 2 : ℚ) • ((ω : K') + 1) = (1 + (ω : K')) / 2
  -- Inline the two_ne_zero proof directly into the rewrite
  rw [eq_div_iff two_ne_zero, show (2 : K') = 1 + 1 by norm_num]
  -- Use <;> to apply the exact same simp and ring sequence to both .re and .im subgoals
  ext <;>
    simp only [re_mul, im_mul, re_smul, im_smul, omega_re, omega_im, re_add, im_add,
               re_one, im_one, add_zero, zero_add, smul_eq_mul] <;>
    ring
end
