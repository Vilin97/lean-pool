/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.FiniteField.QuadraticCharacter
import LeanPool.MarkoffModP.BGS.Markoff.Diophantine.PrimewiseCRT
import LeanPool.MarkoffModP.BGS.Markoff.Core.PuncturedNormalization

/-!
# Elementary local counts on the Markoff surface

This file proves the two exact finite-field counts used in Section 7 of the published
Bourgain--Gamburd--Sarnak paper.  The full surface count is reduced to an explicit quadratic-
character sum, including the exceptional fibers at normalized traces `0`, `2`, and `-2`.
Coordinatewise normalization then transports the results back to the original Markoff surface.
-/

namespace BGS.Markoff

open Finset
open BGS.FiniteField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private lemma quadraticChar_neg_four_eq_one
    (hF : ringChar F ≠ 2) (hneg : quadraticChar F (-1) = 1) :
    quadraticChar F (-4) = 1 := by
  have htwo : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  rw [show (-4 : F) = (-1) * 2 ^ 2 by norm_num, map_mul,
    hneg, quadraticChar_sq_one' htwo, one_mul]

private lemma sum_quadraticChar_neg_four_mul_sq
    (hF : ringChar F ≠ 2) (hneg : quadraticChar F (-1) = 1) :
    ∑ x : F, quadraticChar F ((-4) * x ^ 2) = (Fintype.card F : ℤ) - 1 := by
  have hnegFour := quadraticChar_neg_four_eq_one hF hneg
  calc
    ∑ x : F, quadraticChar F ((-4) * x ^ 2) =
        ∑ x : F, if x = 0 then 0 else 1 := by
      apply sum_congr rfl
      intro x _
      by_cases hx : x = 0
      · simp [hx]
      · rw [map_mul, hnegFour, one_mul, quadraticChar_sq_one' hx]
        simp [hx]
    _ = (Fintype.card F : ℤ) - 1 := by
      rw [sum_ite]
      simp only [sum_const_zero, sum_const, nsmul_eq_mul, mul_one]
      have hfilter : (univ.filter fun x : F ↦ ¬x = 0) = univ.erase 0 := by
        ext x
        simp
      rw [hfilter, card_erase_of_mem (mem_univ 0)]
      rw [card_univ]
      have hcard : 0 < Fintype.card F := Fintype.card_pos
      omega

private lemma quadraticChar_neg_sixteen_eq_one
    (hF : ringChar F ≠ 2) (hneg : quadraticChar F (-1) = 1) :
    quadraticChar F (-16) = 1 := by
  have hfour : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 ^ 2 by norm_num]
    exact pow_ne_zero 2 (Ring.two_ne_zero hF)
  rw [show (-16 : F) = (-1) * 4 ^ 2 by norm_num, map_mul,
    hneg, quadraticChar_sq_one' hfour, one_mul]

private lemma markoffDiscriminant_inner_sum
    (hF : ringChar F ≠ 2) (hneg : quadraticChar F (-1) = 1) (y : F) :
    ∑ x : F, quadraticChar F ((y ^ 2 - 4) * x ^ 2 - 4 * y ^ 2) =
      -quadraticChar F (y ^ 2 - 4) +
        (if y = 0 then (Fintype.card F : ℤ) else 0) +
        (if y ^ 2 = 4 then (Fintype.card F : ℤ) else 0) := by
  have htwo : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hfour : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 ^ 2 by norm_num]
    exact pow_ne_zero 2 htwo
  by_cases hy : y = 0
  · subst y
    have hrewrite (x : F) :
        ((0 : F) ^ 2 - 4) * x ^ 2 - 4 * (0 : F) ^ 2 = (-4) * x ^ 2 := by ring
    simp_rw [hrewrite]
    rw [sum_quadraticChar_neg_four_mul_sq hF hneg]
    have hzeroFour : (0 : F) ^ 2 ≠ 4 := by
      simpa using hfour.symm
    simp only [if_true, if_neg hzeroFour]
    rw [show quadraticChar F ((0 : F) ^ 2 - 4) = 1 by
      simpa using quadraticChar_neg_four_eq_one hF hneg]
    ring
  · by_cases hspecial : y ^ 2 = 4
    · have hconstant (x : F) : (y ^ 2 - 4) * x ^ 2 - 4 * y ^ 2 = (-16 : F) := by
        rw [hspecial]
        ring
      simp_rw [hconstant, quadraticChar_neg_sixteen_eq_one hF hneg]
      rw [if_neg hy, if_pos hspecial]
      simp [hspecial]
    · have hA : y ^ 2 - 4 ≠ 0 := sub_ne_zero.mpr hspecial
      have hC : (4 : F) * y ^ 2 ≠ 0 := mul_ne_zero hfour (pow_ne_zero 2 hy)
      rw [BGS.FiniteField.sum_quadraticChar_mul_sq_sub hF hA hC]
      rw [if_neg hy, if_neg hspecial]
      ring

private lemma markoffDiscriminant_double_sum
    (hF : ringChar F ≠ 2) (hneg : quadraticChar F (-1) = 1) :
    ∑ y : F, ∑ x : F, quadraticChar F ((y ^ 2 - 4) * x ^ 2 - 4 * y ^ 2) =
      3 * (Fintype.card F : ℤ) + 1 := by
  have htwo : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hfour : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 ^ 2 by norm_num]
    exact pow_ne_zero 2 htwo
  have hchiFour : quadraticChar F (4 : F) = 1 := by
    rw [show (4 : F) = 2 ^ 2 by norm_num, quadraticChar_sq_one' htwo]
  have hquadratic :
      ∑ y : F, quadraticChar F (y ^ 2 - 4) = -1 := by
    simpa using
      (BGS.FiniteField.sum_quadraticChar_mul_sq_sub hF (A := (1 : F))
        (C := (4 : F)) one_ne_zero hfour)
  have hzeroIndicator :
      ∑ y : F, (if y = 0 then (Fintype.card F : ℤ) else 0) =
        Fintype.card F := by
    simp
  have hrootCard : (univ.filter fun y : F ↦ y ^ 2 = 4).card = 2 := by
    have hroots := quadraticChar_card_sqrts hF (4 : F)
    rw [hchiFour] at hroots
    norm_num [Set.toFinset_setOf] at hroots
    exact_mod_cast hroots
  have hspecialIndicator :
      ∑ y : F, (if y ^ 2 = 4 then (Fintype.card F : ℤ) else 0) =
        2 * Fintype.card F := by
    rw [sum_ite]
    simp only [sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
    rw [hrootCard]
    ring
  simp_rw [markoffDiscriminant_inner_sum hF hneg]
  rw [sum_add_distrib, sum_add_distrib]
  rw [sum_neg_distrib, hquadratic, hzeroIndicator, hspecialIndicator]
  ring

private def normalizedMarkoffThirdCoordinateEquivDiscriminantRoots
    (hF : ringChar F ≠ 2) (x y : F) :
    {z : F // IsNormalizedMarkoff (⟨x, y, z⟩ : NormalizedPoint F)} ≃
      {d : F // d ^ 2 = (y ^ 2 - 4) * x ^ 2 - 4 * y ^ 2} where
  toFun z := ⟨2 * z.1 - x * y, by
    have hz := z.2
    change x ^ 2 + y ^ 2 + z.1 ^ 2 - x * y * z.1 = 0 at hz
    linear_combination 4 * hz⟩
  invFun d := ⟨(d.1 + x * y) / 2, by
    change x ^ 2 + y ^ 2 + ((d.1 + x * y) / 2) ^ 2 -
      x * y * ((d.1 + x * y) / 2) = 0
    have htwo : (2 : F) ≠ 0 := Ring.two_ne_zero hF
    field_simp [htwo]
    linear_combination d.2⟩
  left_inv z := by
    apply Subtype.ext
    dsimp
    have htwo : (2 : F) ≠ 0 := Ring.two_ne_zero hF
    field_simp [htwo]
    ring
  right_inv d := by
    apply Subtype.ext
    dsimp
    have htwo : (2 : F) ≠ 0 := Ring.two_ne_zero hF
    field_simp [htwo]
    ring

private def normalizedSurfaceEquivDiscriminantRoots
    (hF : ringChar F ≠ 2) :
    ↑(normalizedSurface F) ≃
      Σ x : F, Σ y : F,
        {d : F // d ^ 2 = (y ^ 2 - 4) * x ^ 2 - 4 * y ^ 2} where
  toFun u :=
    ⟨u.1.u1, u.1.u2,
      normalizedMarkoffThirdCoordinateEquivDiscriminantRoots hF u.1.u1 u.1.u2
        ⟨u.1.u3, u.2⟩⟩
  invFun u :=
    ⟨⟨u.1, u.2.1,
        (normalizedMarkoffThirdCoordinateEquivDiscriminantRoots hF u.1 u.2.1).symm
          u.2.2⟩,
      ((normalizedMarkoffThirdCoordinateEquivDiscriminantRoots hF u.1 u.2.1).symm
          u.2.2).2⟩
  left_inv u := by
    apply Subtype.ext
    ext <;> simp
  right_inv u := by
    rcases u with ⟨x, y, d⟩
    simp

private lemma squareRootSubtypeCard_eq_quadraticChar_add_one
    (hF : ringChar F ≠ 2) (t : F) :
    (Fintype.card {d : F // d ^ 2 = t} : ℤ) = quadraticChar F t + 1 := by
  calc
    (Fintype.card {d : F // d ^ 2 = t} : ℤ) =
        ((({d : F | d ^ 2 = t} : Set F).toFinset.card : ℕ) : ℤ) := by
      rw [Set.toFinset_card]
      exact_mod_cast Fintype.card_congr (Equiv.refl _)
    _ = quadraticChar F t + 1 := quadraticChar_card_sqrts hF t

/-- If the field has odd characteristic and `-1` has quadratic character `1`, the normalized
Markoff surface has `q² + 3q + 1` points, including the origin. -/
theorem normalizedSurface_card_eq_of_quadraticChar_neg_one_eq_one
    (hF : ringChar F ≠ 2) (hneg : quadraticChar F (-1) = 1) :
    Nat.card ↑(normalizedSurface F) =
      Fintype.card F ^ 2 + 3 * Fintype.card F + 1 := by
  classical
  letI := Fintype.ofFinite ↑(normalizedSurface F)
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_congr (normalizedSurfaceEquivDiscriminantRoots hF)]
  rw [Fintype.card_sigma]
  simp_rw [Fintype.card_sigma]
  have hroots (x y : F) :
      (Fintype.card {d : F //
        d ^ 2 = (y ^ 2 - 4) * x ^ 2 - 4 * y ^ 2} : ℤ) =
        quadraticChar F ((y ^ 2 - 4) * x ^ 2 - 4 * y ^ 2) + 1 := by
    exact squareRootSubtypeCard_eq_quadraticChar_add_one hF _
  apply Nat.cast_injective (R := ℤ)
  push_cast
  simp_rw [hroots]
  simp_rw [sum_add_distrib]
  rw [sum_comm]
  rw [markoffDiscriminant_double_sum hF hneg]
  simp
  ring

/-- Removing the origin from the normalized surface leaves `q² + 3q` points. -/
theorem normalizedPuncturedSurface_card_eq_of_quadraticChar_neg_one_eq_one
    (hF : ringChar F ≠ 2) (hneg : quadraticChar F (-1) = 1) :
    Nat.card ↑(normalizedPuncturedSurface F) =
      Fintype.card F ^ 2 + 3 * Fintype.card F := by
  change (normalizedPuncturedSurface F).ncard = _
  rw [normalizedPuncturedSurface, Set.ncard_sdiff_singleton_of_mem]
  · rw [← Nat.card_coe_set_eq,
      normalizedSurface_card_eq_of_quadraticChar_neg_one_eq_one hF hneg]
    omega
  · exact isNormalizedMarkoff_origin

/-- Published equation (95) in normalized coordinates: for prime `p ≡ 1 (mod 4)`, the
punctured surface has exactly `p² + 3p` points. -/
theorem normalizedPuncturedSurface_zmod_card_eq_of_mod_four_eq_one
    (p : ℕ) [Fact p.Prime] (hpModFour : p % 4 = 1) :
    Nat.card ↑(normalizedPuncturedSurface (ZMod p)) = p ^ 2 + 3 * p := by
  have hpTwo : p ≠ 2 := by
    intro hp
    subst p
    norm_num at hpModFour
  have hchar : ringChar (ZMod p) ≠ 2 := (ZMod.ringChar_zmod_n p).substr hpTwo
  have hneg : quadraticChar (ZMod p) (-1) = 1 := by
    rw [quadraticChar_neg_one hchar, ZMod.χ₄_nat_eq_if_mod_four, ZMod.card p, hpModFour]
    simp only [if_true]
    have hpOdd : p % 2 = 1 := by omega
    rw [hpOdd]
    norm_num
  simpa [ZMod.card p] using
    normalizedPuncturedSurface_card_eq_of_quadraticChar_neg_one_eq_one hchar hneg

private def normalizedFiber1ZeroEquivSquareRoots :
    ↑(normalizedFiber1 (0 : F)) ≃ Σ y : F, {z : F // z ^ 2 = -y ^ 2} where
  toFun u := ⟨u.1.u2, u.1.u3, by
    have hu := u.2.1
    change u.1.u1 ^ 2 + u.1.u2 ^ 2 + u.1.u3 ^ 2 -
      u.1.u1 * u.1.u2 * u.1.u3 = 0 at hu
    rw [u.2.2] at hu
    linear_combination hu⟩
  invFun u := ⟨⟨0, u.1, u.2.1⟩, by
    constructor
    · change (0 : F) ^ 2 + u.1 ^ 2 + u.2.1 ^ 2 - 0 * u.1 * u.2.1 = 0
      rw [u.2.2]
      ring
    · rfl⟩
  left_inv u := by
    apply Subtype.ext
    ext
    · exact u.2.2.symm
    · rfl
    · rfl
  right_inv u := by
    rcases u with ⟨y, z⟩
    rfl

/-- The full first-coordinate-zero fiber has `2q - 1` points; the extra point is the origin. -/
theorem normalizedFiber1_zero_card_eq_of_quadraticChar_neg_one_eq_one
    (hF : ringChar F ≠ 2) (hneg : quadraticChar F (-1) = 1) :
    Nat.card ↑(normalizedFiber1 (0 : F)) = 2 * Fintype.card F - 1 := by
  classical
  letI := Fintype.ofFinite ↑(normalizedFiber1 (0 : F))
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_congr normalizedFiber1ZeroEquivSquareRoots]
  rw [Fintype.card_sigma]
  apply Nat.cast_injective (R := ℤ)
  push_cast
  simp_rw [squareRootSubtypeCard_eq_quadraticChar_add_one hF]
  have hchar (y : F) :
      quadraticChar F (-y ^ 2) = if y = 0 then 0 else 1 := by
    by_cases hy : y = 0
    · simp [hy]
    · rw [show -y ^ 2 = (-1) * y ^ 2 by ring, map_mul, hneg,
          quadraticChar_sq_one' hy, one_mul]
      simp [hy]
  simp_rw [hchar, sum_add_distrib]
  have hfilter : (univ.filter fun y : F ↦ ¬y = 0) = univ.erase 0 := by
    ext y
    simp
  rw [sum_ite]
  simp only [sum_const_zero, sum_const, nsmul_eq_mul]
  rw [hfilter, card_erase_of_mem (mem_univ 0), card_univ]
  have hcard : 0 < Fintype.card F := Fintype.card_pos
  omega

/-- After removing the origin, a normalized coordinate-zero fiber has `2q - 2` points. -/
theorem normalizedPuncturedFiber1_zero_card_eq_of_quadraticChar_neg_one_eq_one
    (hF : ringChar F ≠ 2) (hneg : quadraticChar F (-1) = 1) :
    Nat.card ↑(normalizedFiber1 (0 : F) \ {normalizedOrigin}) =
      2 * Fintype.card F - 2 := by
  change (normalizedFiber1 (0 : F) \ {normalizedOrigin}).ncard = _
  rw [Set.ncard_sdiff_singleton_of_mem]
  · rw [← Nat.card_coe_set_eq,
      normalizedFiber1_zero_card_eq_of_quadraticChar_neg_one_eq_one hF hneg]
    have hcard : 0 < Fintype.card F := Fintype.card_pos
    omega
  · exact ⟨isNormalizedMarkoff_origin, rfl⟩

/-- Published equation (96) for the first normalized coordinate. -/
theorem normalizedPuncturedFiber1_zero_zmod_card_eq_of_mod_four_eq_one
    (p : ℕ) [Fact p.Prime] (hpModFour : p % 4 = 1) :
    Nat.card ↑(normalizedFiber1 (0 : ZMod p) \ {normalizedOrigin}) = 2 * p - 2 := by
  have hpTwo : p ≠ 2 := by
    intro hp
    subst p
    norm_num at hpModFour
  have hchar : ringChar (ZMod p) ≠ 2 := (ZMod.ringChar_zmod_n p).substr hpTwo
  have hneg : quadraticChar (ZMod p) (-1) = 1 := by
    rw [quadraticChar_neg_one hchar, ZMod.χ₄_nat_eq_if_mod_four, ZMod.card p, hpModFour]
    simp only [if_true]
    have hpOdd : p % 2 = 1 := by omega
    rw [hpOdd]
    norm_num
  simpa [ZMod.card p] using
    normalizedPuncturedFiber1_zero_card_eq_of_quadraticChar_neg_one_eq_one hchar hneg

/-- Original-coordinate punctured Markoff points whose first coordinate vanishes. -/
def puncturedMarkoffFirstCoordinateZero (R : Type*) [CommRing R] :
    Set (PuncturedMarkoffSurface R) :=
  {x | x.1.1.x1 = 0}

/-- Original-coordinate punctured Markoff points whose second coordinate vanishes. -/
def puncturedMarkoffSecondCoordinateZero (R : Type*) [CommRing R] :
    Set (PuncturedMarkoffSurface R) :=
  {x | x.1.1.x2 = 0}

/-- Original-coordinate punctured Markoff points whose third coordinate vanishes. -/
def puncturedMarkoffThirdCoordinateZero (R : Type*) [CommRing R] :
    Set (PuncturedMarkoffSurface R) :=
  {x | x.1.1.x3 = 0}

/-- Swapping the first two coordinates identifies their zero-coordinate loci. -/
def puncturedMarkoffSecondCoordinateZeroEquivFirst (R : Type*) [CommRing R] :
    ↑(puncturedMarkoffSecondCoordinateZero R) ≃
      ↑(puncturedMarkoffFirstCoordinateZero R) :=
  (swap12PuncturedPerm R).subtypeEquiv fun _ ↦ Iff.rfl

/-- Swapping the last two coordinates and then the first two identifies the third and first
zero-coordinate loci. -/
def puncturedMarkoffThirdCoordinateZeroEquivFirst (R : Type*) [CommRing R] :
    ↑(puncturedMarkoffThirdCoordinateZero R) ≃
      ↑(puncturedMarkoffFirstCoordinateZero R) :=
  ((swap23PuncturedPerm R).trans (swap12PuncturedPerm R)).subtypeEquiv fun _ ↦ Iff.rfl

private def puncturedMarkoffFirstCoordinateZeroEquivNormalized
    [Invertible (3 : F)] :
    ↑(puncturedMarkoffFirstCoordinateZero F) ≃
      ↑(normalizedFiber1 (0 : F) \ {normalizedOrigin}) where
  toFun x := by
    let u := puncturedNormalizationEquiv F x.1
    refine ⟨u.1, ⟨⟨u.2.1, ?_⟩, u.2.2⟩⟩
    rw [show (u.1 : NormalizedPoint F) = toNormalized x.1.1.1 by rfl]
    change (3 : F) * x.1.1.1.x1 = 0
    rw [x.2, mul_zero]
  invFun u := by
    let v : ↑(normalizedPuncturedSurface F) := ⟨u.1, ⟨u.2.1.1, u.2.2⟩⟩
    let x := (puncturedNormalizationEquiv F).symm v
    refine ⟨x, ?_⟩
    have hnormalize : puncturedNormalizationEquiv F x = v :=
      (puncturedNormalizationEquiv F).apply_symm_apply v
    have hcoordinate : (3 : F) * x.1.1.x1 = 0 := by
      have := congrArg (fun w : ↑(normalizedPuncturedSurface F) ↦ w.1.u1) hnormalize
      simpa [v, puncturedNormalizationEquiv_coe, toNormalized] using this.trans u.2.1.2
    exact (mul_eq_zero.mp hcoordinate).resolve_left (isUnit_of_invertible (3 : F)).ne_zero
  left_inv x := by
    apply Subtype.ext
    change (puncturedNormalizationEquiv F).symm (puncturedNormalizationEquiv F x.1) = x.1
    exact (puncturedNormalizationEquiv F).symm_apply_apply x.1
  right_inv u := by
    apply Subtype.ext
    change ((puncturedNormalizationEquiv F)
      ((puncturedNormalizationEquiv F).symm
        ⟨u.1, ⟨u.2.1.1, u.2.2⟩⟩)).1 = u.1
    rw [(puncturedNormalizationEquiv F).apply_symm_apply]

/-- Normalization transports the coordinate-zero count to original Markoff coordinates. -/
theorem puncturedMarkoffFirstCoordinateZero_card_eq_of_quadraticChar_neg_one_eq_one
    [Invertible (3 : F)] (hF : ringChar F ≠ 2)
    (hneg : quadraticChar F (-1) = 1) :
    Nat.card ↑(puncturedMarkoffFirstCoordinateZero F) =
      2 * Fintype.card F - 2 := by
  rw [Nat.card_congr puncturedMarkoffFirstCoordinateZeroEquivNormalized]
  exact normalizedPuncturedFiber1_zero_card_eq_of_quadraticChar_neg_one_eq_one hF hneg

/-- The second-coordinate-zero locus has the same exact local count. -/
theorem puncturedMarkoffSecondCoordinateZero_card_eq_of_quadraticChar_neg_one_eq_one
    [Invertible (3 : F)] (hF : ringChar F ≠ 2)
    (hneg : quadraticChar F (-1) = 1) :
    Nat.card ↑(puncturedMarkoffSecondCoordinateZero F) =
      2 * Fintype.card F - 2 := by
  rw [Nat.card_congr (puncturedMarkoffSecondCoordinateZeroEquivFirst F)]
  exact puncturedMarkoffFirstCoordinateZero_card_eq_of_quadraticChar_neg_one_eq_one hF hneg

/-- The third-coordinate-zero locus has the same exact local count. -/
theorem puncturedMarkoffThirdCoordinateZero_card_eq_of_quadraticChar_neg_one_eq_one
    [Invertible (3 : F)] (hF : ringChar F ≠ 2)
    (hneg : quadraticChar F (-1) = 1) :
    Nat.card ↑(puncturedMarkoffThirdCoordinateZero F) =
      2 * Fintype.card F - 2 := by
  rw [Nat.card_congr (puncturedMarkoffThirdCoordinateZeroEquivFirst F)]
  exact puncturedMarkoffFirstCoordinateZero_card_eq_of_quadraticChar_neg_one_eq_one hF hneg

/-- Published equation (95) for the original-coordinate punctured Markoff surface. -/
theorem puncturedMarkoffSurface_zmod_card_eq_of_mod_four_eq_one
    (p : ℕ) [Fact p.Prime] (hpModFour : p % 4 = 1) :
    Nat.card (PuncturedMarkoffSurface (ZMod p)) = p ^ 2 + 3 * p := by
  have hp := (Fact.out : p.Prime)
  have hpThree : 3 < p := by
    by_contra h
    have hpLe : p ≤ 3 := by omega
    have hpTwo : 2 ≤ p := hp.two_le
    have hpCases : p = 2 ∨ p = 3 := by omega
    rcases hpCases with rfl | rfl <;> norm_num at hpModFour
  letI : Invertible (3 : ZMod p) :=
    invertibleOfNonzero (by
      intro hzero
      have hdvd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp hzero
      exact (Nat.not_le_of_gt hpThree) (Nat.le_of_dvd (by norm_num) hdvd))
  rw [Nat.card_congr (puncturedNormalizationEquiv (ZMod p))]
  exact normalizedPuncturedSurface_zmod_card_eq_of_mod_four_eq_one p hpModFour

/-- The primewise-punctured carrier has the product cardinality asserted after published
equation (95). -/
theorem primewisePuncturedMarkoffSurface_card_eq_of_mod_four_eq_one
    {ι : Type*} [Fintype ι] (a : ι → ℕ) [∀ i, Fact (a i).Prime]
    (hmod : ∀ i, a i % 4 = 1) :
    Nat.card (PrimewisePuncturedMarkoffSurface a) =
      ∏ i, (a i ^ 2 + 3 * a i) := by
  rw [Nat.card_pi]
  apply Finset.prod_congr rfl
  intro i _
  exact puncturedMarkoffSurface_zmod_card_eq_of_mod_four_eq_one (a i) (hmod i)

/-- The single-residue-ring CRT presentation has the same exact product cardinality. -/
theorem crtPrimewisePuncturedMarkoffSurface_card_eq_of_mod_four_eq_one
    {ι : Type*} [Fintype ι] (a : ι → ℕ) [∀ i, Fact (a i).Prime]
    (coprime : Pairwise (Function.onFun Nat.Coprime a)) (hmod : ∀ i, a i % 4 = 1) :
    Nat.card (CRTPrimewisePuncturedMarkoffSurface a coprime) =
      ∏ i, (a i ^ 2 + 3 * a i) := by
  rw [Nat.card_congr (primewisePuncturedCRTEquiv a coprime)]
  exact primewisePuncturedMarkoffSurface_card_eq_of_mod_four_eq_one a hmod

/-- Published equation (96) in original Markoff coordinates, for the first coordinate. -/
theorem puncturedMarkoffFirstCoordinateZero_zmod_card_eq_of_mod_four_eq_one
    (p : ℕ) [Fact p.Prime] (hpModFour : p % 4 = 1) :
    Nat.card ↑(puncturedMarkoffFirstCoordinateZero (ZMod p)) = 2 * p - 2 := by
  have hp := (Fact.out : p.Prime)
  have hpThree : 3 < p := by
    by_contra h
    have hpLe : p ≤ 3 := by omega
    have hpTwo : 2 ≤ p := hp.two_le
    have hpCases : p = 2 ∨ p = 3 := by omega
    rcases hpCases with rfl | rfl <;> norm_num at hpModFour
  letI : Invertible (3 : ZMod p) :=
    invertibleOfNonzero (by
      intro hzero
      have hdvd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp hzero
      exact (Nat.not_le_of_gt hpThree) (Nat.le_of_dvd (by norm_num) hdvd))
  have hpTwo : p ≠ 2 := by omega
  have hchar : ringChar (ZMod p) ≠ 2 := (ZMod.ringChar_zmod_n p).substr hpTwo
  have hneg : quadraticChar (ZMod p) (-1) = 1 := by
    rw [quadraticChar_neg_one hchar, ZMod.χ₄_nat_eq_if_mod_four, ZMod.card p, hpModFour]
    simp only [if_true]
    have hpOdd : p % 2 = 1 := by omega
    rw [hpOdd]
    norm_num
  simpa [ZMod.card p] using
    puncturedMarkoffFirstCoordinateZero_card_eq_of_quadraticChar_neg_one_eq_one hchar hneg

/-- Published equation (96) for the second original Markoff coordinate. -/
theorem puncturedMarkoffSecondCoordinateZero_zmod_card_eq_of_mod_four_eq_one
    (p : ℕ) [Fact p.Prime] (hpModFour : p % 4 = 1) :
    Nat.card ↑(puncturedMarkoffSecondCoordinateZero (ZMod p)) = 2 * p - 2 := by
  rw [Nat.card_congr (puncturedMarkoffSecondCoordinateZeroEquivFirst (ZMod p))]
  exact puncturedMarkoffFirstCoordinateZero_zmod_card_eq_of_mod_four_eq_one p hpModFour

/-- Published equation (96) for the third original Markoff coordinate. -/
theorem puncturedMarkoffThirdCoordinateZero_zmod_card_eq_of_mod_four_eq_one
    (p : ℕ) [Fact p.Prime] (hpModFour : p % 4 = 1) :
    Nat.card ↑(puncturedMarkoffThirdCoordinateZero (ZMod p)) = 2 * p - 2 := by
  rw [Nat.card_congr (puncturedMarkoffThirdCoordinateZeroEquivFirst (ZMod p))]
  exact puncturedMarkoffFirstCoordinateZero_zmod_card_eq_of_mod_four_eq_one p hpModFour

end BGS.Markoff
