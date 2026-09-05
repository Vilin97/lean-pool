/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/

import LeanPool.KasamiCyclicAdditive.Prelude
import LeanPool.KasamiCyclicAdditive.Preliminaries.FiniteFieldSums

/-!
# Character-sum lemmas over a finite field

Elementary orthogonality relations for multiplicative characters and shared
additive-character/Gauss-sum facts over a finite field `K` with values in `ℂ`.
These are used by the phase-to-root-count identity and the MCM Fourier/phase
development.

The multiplicative-character orthogonality section is characteristic
independent. The shared additive-character section supplies the principal Gauss
sum, characteristic-two self-inverse and Gauss-product identities, and related
nonvanishing facts. Primitive-character nontriviality is supplied by
`Phase/AdditiveCharacter.lean`.
-/

open Finset

namespace KasamiCyclicAdditive.Phase

/-- The `ℂ`-valued multiplicative characters of a finite field form a finite
type. -/
noncomputable instance instFintypeMulCharComplex (K : Type*) [Field K] [Fintype K] :
    Fintype (MulChar K ℂ) := Fintype.ofFinite _

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- The number of `ℂ`-valued multiplicative characters of `K` is `#Kˣ`. -/
lemma card_mulChar : Fintype.card (MulChar K ℂ) = Fintype.card Kˣ := by
  have := MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity K ℂ
  simpa [Nat.card_eq_fintype_card] using this

/-- First orthogonality relation: summing the value at a fixed unit over all characters. -/
lemma sum_char_apply (a : Kˣ) :
    ∑ χ : MulChar K ℂ, χ (a : K) = if a = 1 then (Fintype.card Kˣ : ℂ) else 0 := by
  split_ifs with ha
  · simp [ha, card_mulChar]
  · obtain ⟨χ₀, hχ₀⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity K ℂ
      (a := (a : K)) (by simpa using ha)
    refine eq_zero_of_mul_eq_self_left hχ₀ ?_
    simp only [Finset.mul_sum, ← MulChar.mul_apply]
    exact Fintype.sum_bijective _ (Group.mulLeft_bijective χ₀) _ _ fun χ' ↦ rfl

/-- Second orthogonality relation: summing a fixed character over all units. -/
lemma sum_units_char (θ : MulChar K ℂ) :
    ∑ b : Kˣ, θ ((b : K)) = if θ = 1 then (Fintype.card Kˣ : ℂ) else 0 := by
  split_ifs with h
  · simp [h, MulChar.one_apply_coe]
  · rw [sum_units_eq_sum (fun a : K => θ a) (MulChar.map_nonunit θ (by simp))]
    exact MulChar.sum_eq_zero_of_ne_one h

/-- The sum of `χ a` over the cubic characters `χ` (those with `χ ^ 3 = 1`) equals the
number of cube roots of `a` in `Kˣ`.  This packages both the vanishing at non-cubes and
the count at cubes into a single identity, and needs only the two orthogonality
relations. -/
lemma sum_cubic_char_apply (a : Kˣ) :
    ∑ χ ∈ Finset.univ.filter (fun χ : MulChar K ℂ => χ ^ 3 = 1), χ (a : K) =
      (#{b : Kˣ | b ^ 3 = a} : ℂ) := by
  have hN : (Fintype.card Kˣ : ℂ) ≠ 0 := by
    simp [Fintype.card_ne_zero]
  have key : (Fintype.card Kˣ : ℂ) * (#{b : Kˣ | b ^ 3 = a} : ℂ)
      = (Fintype.card Kˣ : ℂ) * ∑ χ ∈ Finset.univ.filter (fun χ : MulChar K ℂ => χ ^ 3 = 1),
          χ ((a⁻¹ : Kˣ) : K) := by
    calc (Fintype.card Kˣ : ℂ) * (#{b : Kˣ | b ^ 3 = a} : ℂ)
        = ∑ b : Kˣ, (if b ^ 3 * a⁻¹ = 1 then (Fintype.card Kˣ : ℂ) else 0) := by
          simp only [mul_inv_eq_one, Finset.sum_ite, Finset.sum_const, nsmul_eq_mul]
          ring
      _ = ∑ b : Kˣ, ∑ χ : MulChar K ℂ, χ (((b ^ 3 * a⁻¹ : Kˣ)) : K) :=
          Finset.sum_congr rfl fun b _ => (sum_char_apply _).symm
      _ = ∑ χ : MulChar K ℂ, (∑ b : Kˣ, (χ ^ 3) ((b : K))) * χ ((a⁻¹ : Kˣ) : K) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun χ _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun b _ => ?_
          push_cast
          rw [map_mul, MulChar.pow_apply_coe, map_pow]
      _ = ∑ χ : MulChar K ℂ, (if χ ^ 3 = 1 then (Fintype.card Kˣ : ℂ) else 0)
            * χ ((a⁻¹ : Kˣ) : K) :=
          Finset.sum_congr rfl fun χ _ => by rw [sum_units_char]
      _ = (Fintype.card Kˣ : ℂ) * ∑ χ ∈ Finset.univ.filter (fun χ : MulChar K ℂ => χ ^ 3 = 1),
            χ ((a⁻¹ : Kˣ) : K) := by
          rw [Finset.mul_sum, Finset.sum_filter]
          exact Finset.sum_congr rfl fun χ _ => by split_ifs <;> ring
  have hinv : ∑ χ ∈ Finset.univ.filter (fun χ : MulChar K ℂ => χ ^ 3 = 1), χ ((a⁻¹ : Kˣ) : K)
      = ∑ χ ∈ Finset.univ.filter (fun χ : MulChar K ℂ => χ ^ 3 = 1), χ ((a : Kˣ) : K) := by
    refine Finset.sum_nbij' (fun χ => χ⁻¹) (fun χ => χ⁻¹) ?_ ?_ ?_ ?_ ?_ <;>
      intro χ hχ <;> simp_all [MulChar.inv_apply']
  rw [hinv] at key
  exact (mul_left_cancel₀ hN key).symm

end KasamiCyclicAdditive.Phase

namespace KasamiCyclicAdditive

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

omit [Fintype K] [DecidableEq K] in
/-- In characteristic two an additive character is its own inverse. -/
lemma addChar_inv_self [CharP K 2] (psi : AddChar K ℂ) : psi⁻¹ = psi := by
  ext x
  rw [AddChar.inv_apply, CharTwo.neg_eq]

omit [DecidableEq K] in
/-- A primitive additive character sums to zero over `K` after any nonzero
rescaling. -/
lemma sum_addChar_eq_zero {psi : AddChar K ℂ} (hpsi : psi.IsPrimitive) (a : Kˣ) :
    ∑ x : K, psi ((a : K) * x) = 0 := by
  classical
  have h := AddChar.sum_mulShift (R := K) (R' := ℂ) (a : K) hpsi
  have ha : (a : K) ≠ 0 := a.ne_zero
  simp only [ha, ite_false] at h
  simpa [mul_comm] using h

/-- Removing the term at `0`, the same sum over `Kˣ` is `-1`. -/
lemma sum_units_addChar {psi : AddChar K ℂ} (hpsi : psi.IsPrimitive) (a : Kˣ) :
    ∑ x : Kˣ, psi ((a : K) * (x : K)) = -1 := by
  have h := KasamiCyclicAdditive.sum_units_add (fun x : K => psi ((a : K) * x))
  rw [sum_addChar_eq_zero hpsi a] at h
  simp only [mul_zero, AddChar.map_zero_eq_one] at h
  linear_combination h

omit [DecidableEq K] in
/-- The Gauss sum of the principal character is `-1`. -/
lemma gaussSum_principal {psi : AddChar K ℂ} (hpsi : psi.IsPrimitive) :
    gaussSum (1 : MulChar K ℂ) psi = -1 := by
  classical
  have h := sum_units_addChar hpsi (1 : Kˣ)
  simp only [Units.val_one, one_mul] at h
  have h2 := KasamiCyclicAdditive.sum_units_add (fun x : K => (1 : MulChar K ℂ) x * psi x)
  have h3 : ∑ x : Kˣ, (1 : MulChar K ℂ) (x : K) * psi (x : K) = ∑ x : Kˣ, psi (x : K) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [MulChar.one_apply_coe, one_mul]
  rw [h3, h] at h2
  simp only [MulChar.map_nonunit _ (by simp : ¬ IsUnit (0 : K)), zero_mul, zero_add] at h2
  rw [gaussSum, ← h2]

omit [DecidableEq K] in
/-- In characteristic two, `G(θ) G(θ⁻¹) = |K|` for nonprincipal `θ`. -/
lemma gaussSum_mul_inv [CharP K 2] {psi : AddChar K ℂ} (hpsi : psi.IsPrimitive)
    {theta : MulChar K ℂ} (h : theta ≠ 1) :
    gaussSum theta psi * gaussSum theta⁻¹ psi = (Fintype.card K : ℂ) := by
  have h2 := gaussSum_mul_gaussSum_eq_card h hpsi
  rwa [addChar_inv_self] at h2

omit [DecidableEq K] in
/-- Against a primitive additive character no Gauss sum vanishes, principal
character included. -/
lemma gaussSum_ne_zero_of_primitive {psi : AddChar K ℂ} (hpsi : psi.IsPrimitive)
    (chi : MulChar K ℂ) : gaussSum chi psi ≠ 0 := by
  classical
  by_cases h : chi = 1
  · rw [h, gaussSum_principal hpsi]
    norm_num
  · refine gaussSum_ne_zero_of_nontrivial ?_ h hpsi
    have : 0 < Fintype.card K := Fintype.card_pos
    exact_mod_cast this.ne'

end KasamiCyclicAdditive
