/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import Mathlib.FieldTheory.RatFunc.IntermediateField

/-!
# Linear-fractional automorphisms of a rational function field

An invertible matrix `((a, b), (c, d))` acts on `K(X)` by sending
`X` to `(aX+b)/(cX+d)`.  This file constructs that action as a `K`-algebra
equivalence and records its action on `X` and on embedded polynomials.
-/

namespace BGS.Algebra

open IntermediateField Polynomial

noncomputable section

variable {K : Type*} [Field K]

/-- The value of the linear-fractional substitution associated to
`((a, b), (c, d))` at the rational-function variable. -/
def ratFuncLinearFractionalValue (a b c d : K) : RatFunc K :=
  (RatFunc.C a * RatFunc.X + RatFunc.C b) /
    (RatFunc.C c * RatFunc.X + RatFunc.C d)

private lemma linearPolynomial_ne_zero_of_determinant_ne_zero
    {a b c d : K} (hdet : a * d - b * c ≠ 0) :
    (C c * X + C d : K[X]) ≠ 0 := by
  intro h
  have hc : c = 0 := by
    have hcoeff := congrArg (fun f : K[X] => f.coeff 1) h
    simpa using hcoeff
  have hd : d = 0 := by
    have hcoeff := congrArg (fun f : K[X] => f.coeff 0) h
    simpa using hcoeff
  apply hdet
  simp [hc, hd]

lemma ratFuncLinearFractional_denominator_ne_zero
    {a b c d : K} (hdet : a * d - b * c ≠ 0) :
    RatFunc.C c * RatFunc.X + RatFunc.C d ≠ 0 := by
  simpa only [map_add, map_mul, RatFunc.algebraMap_X, RatFunc.algebraMap_C] using
    RatFunc.algebraMap_ne_zero
      (linearPolynomial_ne_zero_of_determinant_ne_zero hdet)

lemma ratFuncLinearFractionalValue_not_constant
    {a b c d : K} (hdet : a * d - b * c ≠ 0) :
    ¬ ∃ k : K, ratFuncLinearFractionalValue a b c d = RatFunc.C k := by
  rintro ⟨k, hk⟩
  have hden := ratFuncLinearFractional_denominator_ne_zero hdet
  have hcross :
      RatFunc.C a * RatFunc.X + RatFunc.C b =
        RatFunc.C k * (RatFunc.C c * RatFunc.X + RatFunc.C d) :=
    (div_eq_iff hden).mp hk
  have hpoly :
      (C a * X + C b : K[X]) = C k * (C c * X + C d) := by
    apply RatFunc.algebraMap_injective K
    simpa only [map_add, map_mul, RatFunc.algebraMap_X, RatFunc.algebraMap_C] using hcross
  have ha : a = k * c := by
    have hcoeff := congrArg (fun f : K[X] => f.coeff 1) hpoly
    simpa using hcoeff
  have hb : b = k * d := by
    have hcoeff := congrArg (fun f : K[X] => f.coeff 0) hpoly
    simpa using hcoeff
  apply hdet
  rw [ha, hb]
  ring

lemma ratFuncLinearFractionalValue_transcendental
    {a b c d : K} (hdet : a * d - b * c ≠ 0) :
    Transcendental K (ratFuncLinearFractionalValue a b c d) :=
  RatFunc.transcendental_of_ne_C _
    (ratFuncLinearFractionalValue_not_constant hdet)

lemma ratFuncLinearFractionalValue_inverse_formula
    {a b c d : K} (hdet : a * d - b * c ≠ 0) :
    RatFunc.X =
      (RatFunc.C d * ratFuncLinearFractionalValue a b c d - RatFunc.C b) /
        (RatFunc.C a - RatFunc.C c * ratFuncLinearFractionalValue a b c d) := by
  have hden := ratFuncLinearFractional_denominator_ne_zero hdet
  have hdetRat : RatFunc.C (a * d - b * c) ≠ (0 : RatFunc K) := by
    simpa using RatFunc.C_injective.ne hdet
  have hvalue_mul_denominator :
      ratFuncLinearFractionalValue a b c d *
          (RatFunc.C c * RatFunc.X + RatFunc.C d) =
        RatFunc.C a * RatFunc.X + RatFunc.C b := by
    rw [ratFuncLinearFractionalValue]
    exact div_mul_cancel₀ _ hden
  have hinverseNumerator :
      RatFunc.C d * ratFuncLinearFractionalValue a b c d - RatFunc.C b =
        RatFunc.C (a * d - b * c) * RatFunc.X /
          (RatFunc.C c * RatFunc.X + RatFunc.C d) := by
    apply (eq_div_iff hden).2
    calc
      (RatFunc.C d * ratFuncLinearFractionalValue a b c d - RatFunc.C b) *
          (RatFunc.C c * RatFunc.X + RatFunc.C d) =
          RatFunc.C d *
              (ratFuncLinearFractionalValue a b c d *
                (RatFunc.C c * RatFunc.X + RatFunc.C d)) -
            RatFunc.C b * (RatFunc.C c * RatFunc.X + RatFunc.C d) := by ring
      _ = RatFunc.C (a * d - b * c) * RatFunc.X := by
        rw [hvalue_mul_denominator]
        simp only [map_sub, map_mul]
        ring
  have hinverseDenominator :
      RatFunc.C a - RatFunc.C c * ratFuncLinearFractionalValue a b c d =
        RatFunc.C (a * d - b * c) /
          (RatFunc.C c * RatFunc.X + RatFunc.C d) := by
    apply (eq_div_iff hden).2
    calc
      (RatFunc.C a - RatFunc.C c * ratFuncLinearFractionalValue a b c d) *
          (RatFunc.C c * RatFunc.X + RatFunc.C d) =
          RatFunc.C a * (RatFunc.C c * RatFunc.X + RatFunc.C d) -
            RatFunc.C c *
              (ratFuncLinearFractionalValue a b c d *
                (RatFunc.C c * RatFunc.X + RatFunc.C d)) := by ring
      _ = RatFunc.C (a * d - b * c) := by
        rw [hvalue_mul_denominator]
        simp only [map_sub, map_mul]
        ring
  rw [hinverseNumerator, hinverseDenominator]
  rw [div_div_div_cancel_right₀ hden]
  field_simp [hdetRat]

lemma adjoin_ratFuncLinearFractionalValue_eq_top
    {a b c d : K} (hdet : a * d - b * c ≠ 0) :
    K⟮ratFuncLinearFractionalValue a b c d⟯ =
      (⊤ : IntermediateField K (RatFunc K)) := by
  apply top_unique
  rw [← RatFunc.adjoin_X]
  apply IntermediateField.adjoin_simple_le_iff.mpr
  rw [ratFuncLinearFractionalValue_inverse_formula hdet]
  exact div_mem
    (sub_mem
      (mul_mem (IntermediateField.algebraMap_mem _ d)
        (IntermediateField.mem_adjoin_simple_self K
          (ratFuncLinearFractionalValue a b c d)))
      (IntermediateField.algebraMap_mem _ b))
    (sub_mem
      (IntermediateField.algebraMap_mem _ a)
      (mul_mem (IntermediateField.algebraMap_mem _ c)
        (IntermediateField.mem_adjoin_simple_self K
          (ratFuncLinearFractionalValue a b c d))))

/-- The `K`-algebra automorphism of `K(X)` induced by the invertible matrix
`((a, b), (c, d))`. -/
def ratFuncLinearFractionalEquiv
    (a b c d : K) (hdet : a * d - b * c ≠ 0) :
    RatFunc K ≃ₐ[K] RatFunc K :=
  (RatFunc.algEquivOfTranscendental
      (ratFuncLinearFractionalValue a b c d)
      (ratFuncLinearFractionalValue_transcendental hdet)).trans
    ((IntermediateField.equivOfEq
      (adjoin_ratFuncLinearFractionalValue_eq_top hdet)).trans
      IntermediateField.topEquiv)

@[simp]
theorem ratFuncLinearFractionalEquiv_apply_X
    (a b c d : K) (hdet : a * d - b * c ≠ 0) :
    ratFuncLinearFractionalEquiv a b c d hdet RatFunc.X =
      ratFuncLinearFractionalValue a b c d := by
  simp [ratFuncLinearFractionalEquiv]

@[simp]
theorem ratFuncLinearFractionalEquiv_apply_algebraMap
    (a b c d : K) (hdet : a * d - b * c ≠ 0) (f : K[X]) :
    ratFuncLinearFractionalEquiv a b c d hdet
        (algebraMap K[X] (RatFunc K) f) =
      Polynomial.aeval (ratFuncLinearFractionalValue a b c d) f := by
  simp [ratFuncLinearFractionalEquiv]

end

end BGS.Algebra
