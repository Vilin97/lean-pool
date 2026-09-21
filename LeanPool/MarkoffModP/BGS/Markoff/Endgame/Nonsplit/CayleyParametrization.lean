/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Core.ConicParametrization
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Cayley coordinates on the nonsplit norm-one torus

This file gives the rational coordinate needed to descend the nonsplit end-game cover from the
quadratic finite field to `ZMod p`.  A point `delta` outside the base field identifies the affine
line with the norm-one torus minus its identity by

`z |-> (z - delta ^ p) / (z - delta)`.

The inverse is `(w * delta - delta ^ p) / (w - 1)`.  The proof records the Frobenius identities
explicitly; these are the identities used when the pulled-back trace equation is cleared of
denominators over the base field.
-/

namespace BGS.Markoff

section

variable (p : ℕ) [Fact p.Prime]

private abbrev F := ZMod p
private abbrev E := quadraticFiniteField p

noncomputable local instance : Fintype (E p) := Fintype.ofFinite (E p)
noncomputable local instance : Fintype {w : quadraticNormOneTorus p // w ≠ 1} :=
  Fintype.ofFinite _

private theorem quadraticExtension_finrank : Module.finrank (F p) (E p) = 2 := by
  simpa [F, E] using GaloisField.finrank p (n := 2)

private theorem exists_quadraticNonbaseElement :
    ∃ delta : E p, delta ∉ Set.range (algebraMap (F p) (E p)) := by
  classical
  have hnotSurjective : ¬ Function.Surjective (algebraMap (F p) (E p)) := by
    intro hsurjective
    have hbijective : Function.Bijective (algebraMap (F p) (E p)) :=
      ⟨(algebraMap (F p) (E p)).injective, hsurjective⟩
    have hone : Module.finrank (F p) (E p) = 1 :=
      Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr hbijective
    rw [quadraticExtension_finrank p] at hone
    omega
  change ¬ ∀ y, ∃ x, algebraMap (F p) (E p) x = y at hnotSurjective
  exact Classical.not_forall.mp hnotSurjective

/-- A chosen element of the quadratic finite field which is not defined over the base field. -/
noncomputable def quadraticNonbaseElement : E p :=
  Classical.choose (exists_quadraticNonbaseElement p)

theorem quadraticNonbaseElement_not_mem_range :
    quadraticNonbaseElement p ∉ Set.range (algebraMap (F p) (E p)) := by
  classical
  exact Classical.choose_spec (exists_quadraticNonbaseElement p)

private theorem quadraticExtension_card : Fintype.card (E p) = p ^ 2 := by
  rw [Module.card_eq_pow_finrank (K := F p), quadraticExtension_finrank p, ZMod.card]

theorem quadraticNonbaseElement_frobenius_ne_self :
    quadraticNonbaseElement p ^ p ≠ quadraticNonbaseElement p := by
  intro hfixed
  apply quadraticNonbaseElement_not_mem_range p
  have hmem : quadraticNonbaseElement p ∈ (⊥ : Subfield (E p)) :=
    (Subfield.mem_bot_iff_pow_eq_self (F := E p) (p := p)).mpr hfixed
  rw [mem_bot_iff_intCast p (E p)] at hmem
  rcases hmem with ⟨n, hn⟩
  refine ⟨(n : F p), ?_⟩
  simpa using hn

theorem quadraticNonbaseElement_frobenius_not_mem_range :
    quadraticNonbaseElement p ^ p ∉ Set.range (algebraMap (F p) (E p)) := by
  intro hmem
  rcases hmem with ⟨z, hz⟩
  apply quadraticNonbaseElement_frobenius_ne_self p
  calc
    quadraticNonbaseElement p ^ p
        = algebraMap (F p) (E p) z := hz.symm
    _ = (algebraMap (F p) (E p) z) ^ p := by
      symm
      calc
        (algebraMap (F p) (E p) z) ^ p =
            algebraMap (F p) (E p) (z ^ p) := (map_pow _ z p).symm
        _ = algebraMap (F p) (E p) z := by rw [ZMod.pow_card]
    _ = (quadraticNonbaseElement p ^ p) ^ p := by rw [← hz]
    _ = quadraticNonbaseElement p := by
      rw [← pow_mul, ← pow_two, ← quadraticExtension_card p]
      exact FiniteField.pow_card _

private theorem algebraMap_sub_nonzero (z : F p) :
    algebraMap (F p) (E p) z - quadraticNonbaseElement p ≠ 0 := by
  rw [sub_ne_zero]
  exact fun h => quadraticNonbaseElement_not_mem_range p ⟨z, h⟩

private theorem algebraMap_sub_frobenius_nonzero (z : F p) :
    algebraMap (F p) (E p) z - quadraticNonbaseElement p ^ p ≠ 0 := by
  rw [sub_ne_zero]
  exact fun h => quadraticNonbaseElement_frobenius_not_mem_range p ⟨z, h⟩

/-- The Cayley fraction before it is packaged as a norm-one unit. -/
noncomputable def quadraticCayleyValue (z : F p) : E p :=
  (algebraMap (F p) (E p) z - quadraticNonbaseElement p ^ p) /
    (algebraMap (F p) (E p) z - quadraticNonbaseElement p)

theorem quadraticCayleyValue_ne_zero (z : F p) : quadraticCayleyValue p z ≠ 0 := by
  exact div_ne_zero (algebraMap_sub_frobenius_nonzero p z) (algebraMap_sub_nonzero p z)

theorem quadraticNonbaseElement_frobenius_frobenius :
    (quadraticNonbaseElement p ^ p) ^ p = quadraticNonbaseElement p := by
  rw [← pow_mul, ← pow_two, ← quadraticExtension_card p]
  exact FiniteField.pow_card _

theorem quadraticCayleyValue_frobenius (z : F p) :
    quadraticCayleyValue p z ^ p = (quadraticCayleyValue p z)⁻¹ := by
  rw [quadraticCayleyValue, div_pow, sub_pow_char (R := E p), sub_pow_char (R := E p),
    ← map_pow, ZMod.pow_card, quadraticNonbaseElement_frobenius_frobenius p]
  rw [inv_div]

/-- Frobenius exchanges the two linear factors occurring in the Cayley coordinate. -/
theorem quadraticCayleyBaseFactor_frobenius (z : F p) :
    (algebraMap (F p) (E p) z - quadraticNonbaseElement p) ^ p =
      algebraMap (F p) (E p) z - quadraticNonbaseElement p ^ p := by
  rw [sub_pow_char (R := E p)]
  calc
    algebraMap (F p) (E p) z ^ p - quadraticNonbaseElement p ^ p =
        algebraMap (F p) (E p) (z ^ p) - quadraticNonbaseElement p ^ p := by
      rw [map_pow]
    _ = algebraMap (F p) (E p) z - quadraticNonbaseElement p ^ p := by
      rw [ZMod.pow_card]

/-- Applying Frobenius again returns the other Cayley linear factor. -/
theorem quadraticCayleyConjugateFactor_frobenius (z : F p) :
    (algebraMap (F p) (E p) z - quadraticNonbaseElement p ^ p) ^ p =
      algebraMap (F p) (E p) z - quadraticNonbaseElement p := by
  rw [sub_pow_char (R := E p)]
  calc
    algebraMap (F p) (E p) z ^ p - (quadraticNonbaseElement p ^ p) ^ p =
        algebraMap (F p) (E p) (z ^ p) - quadraticNonbaseElement p := by
      rw [map_pow, quadraticNonbaseElement_frobenius_frobenius p]
    _ = algebraMap (F p) (E p) z - quadraticNonbaseElement p := by
      rw [ZMod.pow_card]

/-- The product of the conjugate Cayley factors is Frobenius-fixed, hence is a base-field
coefficient in the descended equation. -/
theorem quadraticCayleyFactorProduct_frobenius (z : F p) :
    ((algebraMap (F p) (E p) z - quadraticNonbaseElement p ^ p) *
        (algebraMap (F p) (E p) z - quadraticNonbaseElement p)) ^ p =
      (algebraMap (F p) (E p) z - quadraticNonbaseElement p ^ p) *
        (algebraMap (F p) (E p) z - quadraticNonbaseElement p) := by
  rw [mul_pow, quadraticCayleyConjugateFactor_frobenius p,
    quadraticCayleyBaseFactor_frobenius p, mul_comm]

private theorem div_pow_add_inv_pow (A B : E p) (hA : A ≠ 0) (hB : B ≠ 0) (d : ℕ) :
    (A / B) ^ d + ((A / B) ^ d)⁻¹ =
      (A ^ (2 * d) + B ^ (2 * d)) / ((A * B) ^ d) := by
  rw [Nat.mul_comm 2 d, pow_mul, pow_mul, div_pow, inv_div, mul_pow]
  field_simp [pow_ne_zero d hA, pow_ne_zero d hB]

/-- Clearing the Cayley denominator gives the symmetric numerator used for powers of a
norm-one parameter. -/
theorem quadraticCayleyValue_pow_add_inv_pow (z : F p) (d : ℕ) :
    quadraticCayleyValue p z ^ d + (quadraticCayleyValue p z ^ d)⁻¹ =
      ((algebraMap (F p) (E p) z - quadraticNonbaseElement p ^ p) ^ (2 * d) +
        (algebraMap (F p) (E p) z - quadraticNonbaseElement p) ^ (2 * d)) /
      (((algebraMap (F p) (E p) z - quadraticNonbaseElement p ^ p) *
        (algebraMap (F p) (E p) z - quadraticNonbaseElement p)) ^ d) := by
  exact div_pow_add_inv_pow p _ _ (algebraMap_sub_frobenius_nonzero p z)
    (algebraMap_sub_nonzero p z) d

theorem quadraticCayleyValue_ne_one (z : F p) : quadraticCayleyValue p z ≠ 1 := by
  intro hone
  have hnumerator :
      algebraMap (F p) (E p) z - quadraticNonbaseElement p ^ p =
        algebraMap (F p) (E p) z - quadraticNonbaseElement p := by
    exact (div_eq_one_iff_eq (algebraMap_sub_nonzero p z)).mp hone
  exact quadraticNonbaseElement_frobenius_ne_self p (sub_right_inj.mp hnumerator)

/-- The Cayley coordinate as a unit of the quadratic finite field. -/
noncomputable def quadraticCayleyUnit (z : F p) : (E p)ˣ :=
  Units.mk0 (quadraticCayleyValue p z) (quadraticCayleyValue_ne_zero p z)

theorem quadraticCayleyUnit_norm (z : F p) :
    Algebra.norm (F p) (quadraticCayleyUnit p z : E p) = 1 := by
  apply (algebraMap (F p) (E p)).injective
  rw [map_one, algebraMap_quadraticNorm p]
  change quadraticCayleyValue p z * quadraticCayleyValue p z ^ p = 1
  rw [quadraticCayleyValue_frobenius p]
  exact mul_inv_cancel₀ (quadraticCayleyValue_ne_zero p z)

/-- The Cayley coordinate, regarded as a point of the norm-one torus. -/
noncomputable def quadraticCayleyPoint (z : F p) : quadraticNormOneTorus p :=
  ⟨quadraticCayleyUnit p z, by
    change Units.map (Algebra.norm (F p) (S := E p)) (quadraticCayleyUnit p z) = 1
    apply Units.ext
    exact quadraticCayleyUnit_norm p z⟩

theorem quadraticCayleyPoint_ne_one (z : F p) : quadraticCayleyPoint p z ≠ 1 := by
  intro h
  have hval := congrArg (fun w : quadraticNormOneTorus p =>
    (((w : (E p)ˣ) : E p))) h
  exact quadraticCayleyValue_ne_one p z (by simpa [quadraticCayleyPoint, quadraticCayleyUnit] using hval)

/-- The base-field trace of a powered Cayley point is the cleared symmetric Cayley fraction. -/
theorem algebraMap_quadraticNormOneTrace_quadraticCayleyPoint_pow
    (z : F p) (d : ℕ) :
    algebraMap (F p) (E p) (quadraticNormOneTrace p (quadraticCayleyPoint p z ^ d)) =
      ((algebraMap (F p) (E p) z - quadraticNonbaseElement p ^ p) ^ (2 * d) +
        (algebraMap (F p) (E p) z - quadraticNonbaseElement p) ^ (2 * d)) /
      (((algebraMap (F p) (E p) z - quadraticNonbaseElement p ^ p) *
        (algebraMap (F p) (E p) z - quadraticNonbaseElement p)) ^ d) := by
  rw [algebraMap_quadraticNormOneTrace]
  simpa [splitTorusTrace, quadraticCayleyPoint, quadraticCayleyUnit] using
    quadraticCayleyValue_pow_add_inv_pow p z d

/-- Solving the Cayley fraction for its base-field coordinate gives the expected inverse
fraction. -/
theorem quadraticCayleyInverseFormula_point (z : F p) :
    ((quadraticCayleyValue p z * quadraticNonbaseElement p -
        quadraticNonbaseElement p ^ p) /
      (quadraticCayleyValue p z - 1)) = algebraMap (F p) (E p) z := by
  have hdelta : quadraticNonbaseElement p - quadraticNonbaseElement p ^ p ≠ 0 :=
    sub_ne_zero.mpr (quadraticNonbaseElement_frobenius_ne_self p).symm
  rw [quadraticCayleyValue]
  field_simp [algebraMap_sub_nonzero p z, algebraMap_sub_frobenius_nonzero p z,
    quadraticNonbaseElement_frobenius_ne_self p, hdelta]
  ring

private theorem quadraticCayleyPoint_injective :
    Function.Injective (fun z : F p =>
      (⟨quadraticCayleyPoint p z, quadraticCayleyPoint_ne_one p z⟩ :
        {w : quadraticNormOneTorus p // w ≠ 1})) := by
  intro z r h
  have hvalue : quadraticCayleyValue p z = quadraticCayleyValue p r := by
    have htorus := congrArg Subtype.val h
    have hunit := congrArg (fun w : quadraticNormOneTorus p => (w : (E p)ˣ)) htorus
    exact congrArg Units.val hunit
  apply (algebraMap (F p) (E p)).injective
  rw [← quadraticCayleyInverseFormula_point p z,
    ← quadraticCayleyInverseFormula_point p r, hvalue]

private theorem quadraticCayleyTarget_card :
    Fintype.card {w : quadraticNormOneTorus p // w ≠ 1} = p := by
  classical
  rw [Fintype.card_subtype_compl (fun w : quadraticNormOneTorus p => w = 1)]
  rw [Fintype.card_subtype_eq]
  rw [Fintype.card_eq_nat_card, quadraticNormOneTorus_natCard p]
  omega

private theorem quadraticCayleyPoint_bijective :
    Function.Bijective (fun z : F p =>
      (⟨quadraticCayleyPoint p z, quadraticCayleyPoint_ne_one p z⟩ :
        {w : quadraticNormOneTorus p // w ≠ 1})) := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨quadraticCayleyPoint_injective p, by
    rw [ZMod.card, quadraticCayleyTarget_card p]⟩

/-- Cayley coordinates identify the affine line with the norm-one torus minus its identity. -/
noncomputable def quadraticCayleyParameterEquiv :
    F p ≃ {w : quadraticNormOneTorus p // w ≠ 1} :=
  Equiv.ofBijective (fun z =>
    (⟨quadraticCayleyPoint p z, quadraticCayleyPoint_ne_one p z⟩ :
      {w : quadraticNormOneTorus p // w ≠ 1}))
    (quadraticCayleyPoint_bijective p)

@[simp]
theorem quadraticCayleyParameterEquiv_apply (z : F p) :
    quadraticCayleyParameterEquiv p z =
      ⟨quadraticCayleyPoint p z, quadraticCayleyPoint_ne_one p z⟩ := rfl

/-- The inverse coordinate has the explicit fraction used in the descent calculation. -/
theorem algebraMap_quadraticCayleyParameterEquiv_symm
    (w : {w : quadraticNormOneTorus p // w ≠ 1}) :
    algebraMap (F p) (E p) ((quadraticCayleyParameterEquiv p).symm w) =
      (((w.1 : (E p)ˣ) : E p) * quadraticNonbaseElement p -
          quadraticNonbaseElement p ^ p) /
        (((w.1 : (E p)ˣ) : E p) - 1) := by
  have happly := (quadraticCayleyParameterEquiv p).apply_symm_apply w
  have hvalue :
      quadraticCayleyValue p ((quadraticCayleyParameterEquiv p).symm w) =
        ((w.1 : (E p)ˣ) : E p) := by
    have htorus := congrArg Subtype.val happly
    change quadraticCayleyPoint p ((quadraticCayleyParameterEquiv p).symm w) = w.1 at htorus
    have hunit := congrArg Subtype.val htorus
    change quadraticCayleyUnit p ((quadraticCayleyParameterEquiv p).symm w) =
      (w.1 : (E p)ˣ) at hunit
    have h := congrArg Units.val hunit
    exact h
  rw [← quadraticCayleyInverseFormula_point p]
  rw [hvalue]

end

end BGS.Markoff
