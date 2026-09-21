/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.ResidueMathlib
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.NumberTheory.Padics.PadicNumbers

import Mathlib.Algebra.Ring.Prod

/-!
# API checks for the residue map

The first-projection valuation on `ℚ × ℚ` has a nonzero support ideal. Its residue map kills a
nonzero support element but not an element of value zero, which distinguishes the strictly
negative kernel from the zero ideal.

The first cancellation fixture uses two representatives of value zero whose sum has bottom value.
A second fixture uses the separated `2`-adic valuation: `2` has the nonbottom value `-1`, and two
copies of the value-zero representative `1` add to it. This distinguishes the strictly negative
ideal from the support ideal and checks additivity across a genuine finite value drop. The root
`LM24` module does not import this client.
-/

public noncomputable section

open scoped DirectSum

namespace Tests

def residueFirstProjectionValuation : MaxAddDegree (ℚ × ℚ) ℕ :=
  MaxAddDegree.ofValuation
    ((1 : Valuation ℚ (WithZero (Multiplicative ℕ))).comap (RingHom.fst ℚ ℚ))

instance : residueFirstProjectionValuation.IsMultiplicative :=
  inferInstanceAs (MaxAddDegree.ofValuation _).IsMultiplicative

def residueSupportElement : residueFirstProjectionValuation.nonpositiveSubring :=
  ⟨(0, 1), by
    rw [MaxAddDegree.mem_nonpositiveSubring_iff]
    simp [MaxAddDegree.ofValuation_apply, residueFirstProjectionValuation,
      Valuation.one_apply_def]⟩

def residueValueZeroElement : residueFirstProjectionValuation.nonpositiveSubring :=
  ⟨(1, 1), by
    rw [MaxAddDegree.mem_nonpositiveSubring_iff]
    simp [MaxAddDegree.ofValuation_apply, residueFirstProjectionValuation,
      Valuation.one_apply_def]⟩

def residuePositiveUnit : residueFirstProjectionValuation.nonpositiveSubring :=
  ⟨(1, 0), by
    rw [MaxAddDegree.mem_nonpositiveSubring_iff]
    simp [MaxAddDegree.ofValuation_apply, residueFirstProjectionValuation,
      Valuation.one_apply_def]⟩

def residueNegativeUnit : residueFirstProjectionValuation.nonpositiveSubring :=
  ⟨(-1, 0), by
    rw [MaxAddDegree.mem_nonpositiveSubring_iff]
    simp [MaxAddDegree.ofValuation_apply, residueFirstProjectionValuation,
      Valuation.one_apply_def]⟩

/-- The residue kernel contains a nonzero element of the original ring. -/
theorem residueMap_supportElement_eq_zero :
    residueFirstProjectionValuation.residueMap residueSupportElement = 0 := by
  rw [MaxAddDegree.residueMap_eq_zero_iff]
  simp [MaxAddDegree.ofValuation_apply, residueFirstProjectionValuation,
    residueSupportElement, Valuation.one_apply_def]

/-- An element of value zero does not lie in the residue kernel. -/
theorem residueMap_valueZeroElement_ne_zero :
    residueFirstProjectionValuation.residueMap residueValueZeroElement ≠ 0 := by
  rw [ne_eq, MaxAddDegree.residueMap_eq_zero_iff]
  simp [MaxAddDegree.ofValuation_apply, residueFirstProjectionValuation,
    residueValueZeroElement, Valuation.one_apply_def]

/-- Two value-zero representatives can cancel to an element of strictly lower value. -/
theorem residueMap_cancellation_fixture :
    residueFirstProjectionValuation.residueMap residuePositiveUnit ≠ 0 ∧
      residueFirstProjectionValuation.residueMap residueNegativeUnit ≠ 0 ∧
      residueFirstProjectionValuation.residueMap
        (residuePositiveUnit + residueNegativeUnit) = 0 := by
  constructor
  · rw [ne_eq, MaxAddDegree.residueMap_eq_zero_iff]
    simp [MaxAddDegree.ofValuation_apply, residueFirstProjectionValuation,
      residuePositiveUnit, Valuation.one_apply_def]
  constructor
  · rw [ne_eq, MaxAddDegree.residueMap_eq_zero_iff]
    simp [MaxAddDegree.ofValuation_apply, residueFirstProjectionValuation,
      residueNegativeUnit, Valuation.one_apply_def]
  · have hsum : residuePositiveUnit + residueNegativeUnit = 0 := by
      apply Subtype.ext
      simp [residuePositiveUnit, residueNegativeUnit]
    rw [hsum, map_zero]

/-- The two nonzero residue classes in the cancellation fixture add to zero. -/
theorem residueMap_cancellation_sum_eq_zero :
    residueFirstProjectionValuation.residueMap residuePositiveUnit +
      residueFirstProjectionValuation.residueMap residueNegativeUnit = 0 := by
  rw [← map_add]
  exact residueMap_cancellation_fixture.2.2

example (m : ℕ) : Module residueFirstProjectionValuation.ResidueRing
    (residueFirstProjectionValuation.Component m) :=
  inferInstance

/-- The grade-zero scalar action is the homogeneous product used by LM24. -/
theorem residueModule_smul_embeds_as_mul (m : ℕ)
    (a : residueFirstProjectionValuation.ResidueRing)
    (b : residueFirstProjectionValuation.Component m) :
    DirectSum.of residueFirstProjectionValuation.Component m (a • b) =
      DirectSum.of residueFirstProjectionValuation.Component 0 a *
        DirectSum.of residueFirstProjectionValuation.Component m b :=
  DirectSum.of_zero_smul _ a b

section Padic

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev residueTwoAdicValuation : MaxAddDegree ℚ ℤ :=
  MaxAddDegree.ofValuation (Rat.padicValuation 2)

def residueTwoAdicOne : residueTwoAdicValuation.nonpositiveSubring :=
  ⟨1, by simp⟩

/-- The element `2` has the nonbottom max-additive value `-1`. -/
theorem residueTwoAdic_value_two :
    residueTwoAdicValuation 2 = ((-1 : ℤ) : WithBot ℤ) := by
  rw [MaxAddDegree.ofValuation_apply]
  have h := congrArg
    (fun z : WithZero (Multiplicative ℤ) ↦
      Multiplicative.toAdd (WithZero.toMulBot z))
    (Rat.padicValuation_self 2)
  exact h.trans (by rfl)

def residueTwoAdicTwo : residueTwoAdicValuation.nonpositiveSubring :=
  ⟨2, by
    rw [MaxAddDegree.mem_nonpositiveSubring_iff, residueTwoAdic_value_two]
    simp⟩

/-- The strictly negative residue kernel is larger than the support ideal. -/
theorem residueTwoAdic_two_eq_zero :
    residueTwoAdicValuation.residueMap residueTwoAdicTwo = 0 := by
  rw [MaxAddDegree.residueMap_eq_zero_iff]
  rw [show (residueTwoAdicTwo : ℚ) = 2 from rfl, residueTwoAdic_value_two]
  simp

theorem residueTwoAdic_one_ne_zero :
    residueTwoAdicValuation.residueMap residueTwoAdicOne ≠ 0 := by
  rw [ne_eq, MaxAddDegree.residueMap_eq_zero_iff]
  simp [residueTwoAdicOne]

/--
Two value-zero representatives add in the valuation subring to `2`, whose value is strictly
negative and nonbottom; their residue classes therefore sum to zero.
-/
theorem residueTwoAdic_one_add_one_eq_zero :
    residueTwoAdicValuation.residueMap residueTwoAdicOne +
      residueTwoAdicValuation.residueMap residueTwoAdicOne = 0 := by
  rw [← map_add]
  have hsum : residueTwoAdicOne + residueTwoAdicOne = residueTwoAdicTwo := by
    apply Subtype.ext
    norm_num [residueTwoAdicOne, residueTwoAdicTwo]
  rw [hsum, residueTwoAdic_two_eq_zero]

theorem residueTwoAdic_negativeIdeal_mathlib_bridge :
    residueTwoAdicValuation.negativeIdeal =
      ((Rat.padicValuation 2).ltIdeal 1).comap
        (MaxAddDegree.nonpositiveEquivInteger (Rat.padicValuation 2)).toRingHom :=
  MaxAddDegree.negativeIdeal_ofValuation_eq_comap_ltIdeal (Rat.padicValuation 2)

end Padic

end Tests
