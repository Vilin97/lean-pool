/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Core.Basic
import LeanPool.MarkoffModP.BGS.FiniteField.EllipticCharacterSum
import LeanPool.MarkoffModP.BGS.FiniteField.QuadraticCharacter

/-!
# Point-count algebra for the incidence auxiliary curve

This file reduces the off-diagonal auxiliary-curve count to the exact Hasse character sum exposed
in `BGS.FiniteField.EllipticCharacterSum`.
-/

namespace BGS.Markoff

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The number of square roots of `t`, regarded as an integer. -/
def squareRootCount (t : F) : ℤ :=
  ((univ.filter fun x : F ↦ x ^ 2 = t).card : ℕ)

theorem squareRootCount_eq_quadraticChar_add_one
    (hF : ringChar F ≠ 2) (t : F) :
    squareRootCount t = quadraticChar F t + 1 := by
  simpa [squareRootCount, Set.toFinset_ofPred] using quadraticChar_card_sqrts hF t

/-- The generic quadratic branch value occurring in each auxiliary equation. -/
def branchValue (A C y : F) : F :=
  A * y ^ 2 - C

/-- The weighted number of affine triples `(y, lambda, mu)` on two quadratic branches. -/
def auxiliaryTripleCount (A B C D : F) : ℤ :=
  ∑ y : F, squareRootCount (branchValue A C y) * squareRootCount (branchValue B D y)

/-- Exact character expansion of the number of affine auxiliary triples. -/
theorem auxiliaryTripleCount_eq
    (hF : ringChar F ≠ 2) {A B C D : F}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0) :
    auxiliaryTripleCount A B C D =
      (Fintype.card F : ℤ) - quadraticChar F A - quadraticChar F B +
        ∑ y : F, quadraticChar F (branchValue A C y * branchValue B D y) := by
  let chi := quadraticChar F
  calc
    auxiliaryTripleCount A B C D =
        ∑ y : F, (chi (branchValue A C y) + 1) * (chi (branchValue B D y) + 1) := by
      apply sum_congr rfl
      intro y _
      rw [squareRootCount_eq_quadraticChar_add_one hF,
        squareRootCount_eq_quadraticChar_add_one hF]
    _ = ∑ y : F,
        (chi (branchValue A C y * branchValue B D y) +
          chi (branchValue A C y) + chi (branchValue B D y) + 1) := by
      apply sum_congr rfl
      intro y _
      rw [map_mul]
      ring
    _ = (∑ y : F, chi (branchValue A C y * branchValue B D y)) +
          (∑ y : F, chi (branchValue A C y)) +
          (∑ y : F, chi (branchValue B D y)) + ∑ _y : F, 1 := by
      simp_rw [sum_add_distrib]
    _ = (∑ y : F, chi (branchValue A C y * branchValue B D y)) -
          chi A - chi B + (Fintype.card F : ℤ) := by
      rw [show (∑ y : F, chi (branchValue A C y)) = -chi A by
        simpa [chi, branchValue] using
          BGS.FiniteField.sum_quadraticChar_mul_sq_sub hF hA hC]
      rw [show (∑ y : F, chi (branchValue B D y)) = -chi B by
        simpa [chi, branchValue] using
          BGS.FiniteField.sum_quadraticChar_mul_sq_sub hF hB hD]
      simp
      ring
    _ = (Fintype.card F : ℤ) - chi A - chi B +
          ∑ y : F, chi (branchValue A C y * branchValue B D y) := by ring

/-- A quadratic with two distinct roots has character sum minus the character of its leading
coefficient. -/
theorem sum_quadraticChar_two_linear_factors
    (hF : ringChar F ≠ 2) {A B C D : F}
    (hA : A ≠ 0) (hB : B ≠ 0) (hcross : A * D ≠ B * C) :
    ∑ x : F, quadraticChar F ((A * x - C) * (B * x - D)) =
      -quadraticChar F (A * B) := by
  let L : F := A * B
  let center : F := (A * D + B * C) / (2 * L)
  let constantTerm : F := (A * D - B * C) ^ 2 / (4 * L)
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 ^ 2 by norm_num]
    exact pow_ne_zero 2 h2
  have hL : L ≠ 0 := mul_ne_zero hA hB
  have hconstant : constantTerm ≠ 0 := by
    exact div_ne_zero (pow_ne_zero 2 (sub_ne_zero.mpr hcross)) (mul_ne_zero h4 hL)
  let e : F ≃ F := Equiv.addRight center
  calc
    ∑ x : F, quadraticChar F ((A * x - C) * (B * x - D)) =
        ∑ x : F, quadraticChar F ((A * (e x) - C) * (B * (e x) - D)) := by
      exact (e.sum_comp fun x ↦ quadraticChar F ((A * x - C) * (B * x - D))).symm
    _ = ∑ x : F, quadraticChar F (L * x ^ 2 - constantTerm) := by
      apply sum_congr rfl
      intro x _
      congr 1
      dsimp [e, center, constantTerm, L]
      field_simp [h2, hA, hB]
      ring
    _ = -quadraticChar F L :=
      BGS.FiniteField.sum_quadraticChar_mul_sq_sub hF hL hconstant
    _ = -quadraticChar F (A * B) := rfl

/-- Replacing the square variable in the quartic trace sum by a free variable produces the cubic
trace sum, including the correction at infinity. -/
theorem quarticTrace_add_leadingChar_eq_cubicTrace
    (hF : ringChar F ≠ 2) {A B C D : F}
    (hA : A ≠ 0) (hB : B ≠ 0) (hcross : A * D ≠ B * C) :
    (∑ y : F, quadraticChar F (branchValue A C y * branchValue B D y)) +
        quadraticChar F (A * B) =
      ∑ x : F, quadraticChar F (x * (A * x - C) * (B * x - D)) := by
  let chi := quadraticChar F
  have hsquareMap :=
    BGS.FiniteField.sum_comp_sq_eq_sum_quadraticChar_add_one hF
      (fun x : F ↦ chi ((A * x - C) * (B * x - D)))
  have hquadratic := sum_quadraticChar_two_linear_factors hF hA hB hcross
  calc
    (∑ y : F, chi (branchValue A C y * branchValue B D y)) + chi (A * B) =
        (∑ y : F, chi ((A * y ^ 2 - C) * (B * y ^ 2 - D))) + chi (A * B) := by
      simp only [branchValue]
    _ = (∑ x : F, (chi x + 1) * chi ((A * x - C) * (B * x - D))) +
          chi (A * B) := by rw [hsquareMap]
    _ = (∑ x : F,
          (chi (x * (A * x - C) * (B * x - D)) +
            chi ((A * x - C) * (B * x - D)))) + chi (A * B) := by
      congr 1
      apply sum_congr rfl
      intro x _
      rw [add_mul, one_mul, ← map_mul, mul_assoc]
    _ = (∑ x : F, chi (x * (A * x - C) * (B * x - D))) +
          (∑ x : F, chi ((A * x - C) * (B * x - D))) + chi (A * B) := by
      rw [sum_add_distrib]
    _ = ∑ x : F, chi (x * (A * x - C) * (B * x - D)) := by
      rw [hquadratic]
      ring

/-- Scaling `X = A * B * x` turns the cubic trace polynomial into the monic cubic with roots
`0`, `B * C`, and `A * D`. -/
theorem cubicTrace_eq_monicCubicTrace
    {A B C D : F} (hA : A ≠ 0) (hB : B ≠ 0) :
    (∑ x : F, quadraticChar F (x * (A * x - C) * (B * x - D))) =
      ∑ X : F, quadraticChar F (X * (X - B * C) * (X - A * D)) := by
  let chi := quadraticChar F
  have hAB : A * B ≠ 0 := mul_ne_zero hA hB
  let e : F ≃ F := Equiv.mulLeft₀ (A * B) hAB
  calc
    (∑ x : F, chi (x * (A * x - C) * (B * x - D))) =
        ∑ x : F, chi ((e x) * ((e x) - B * C) * ((e x) - A * D)) := by
      apply sum_congr rfl
      intro x _
      have hpoly :
          (e x) * ((e x) - B * C) * ((e x) - A * D) =
            (A * B) ^ 2 * (x * (A * x - C) * (B * x - D)) := by
        change
          (A * B * x) * (A * B * x - B * C) * (A * B * x - A * D) =
            (A * B) ^ 2 * (x * (A * x - C) * (B * x - D))
        ring
      rw [hpoly]
      conv_rhs => rw [map_mul, quadraticChar_sq_one' hAB, one_mul]
    _ = ∑ X : F, chi (X * (X - B * C) * (X - A * D)) :=
      e.sum_comp (fun X ↦ chi (X * (X - B * C) * (X - A * D)))

/-- The quartic trace, including its leading-coefficient correction, is exactly the character
trace of the monic cubic model. -/
theorem quarticTrace_add_leadingChar_eq_monicCubicTrace
    (hF : ringChar F ≠ 2) {A B C D : F}
    (hA : A ≠ 0) (hB : B ≠ 0) (hcross : A * D ≠ B * C) :
    (∑ y : F, quadraticChar F (branchValue A C y * branchValue B D y)) +
        quadraticChar F (A * B) =
      ∑ X : F, quadraticChar F (X * (X - B * C) * (X - A * D)) := by
  rw [quarticTrace_add_leadingChar_eq_cubicTrace hF hA hB hcross,
    cubicTrace_eq_monicCubicTrace hA hB]

/-- The monic Weierstrass model obtained from the cubic trace sum.  Its equation is
`Y^2 = X * (X - u) * (X - v)`. -/
def auxiliaryEllipticCurve (u v : F) : WeierstrassCurve F :=
  ⟨0, -(u + v), 0, u * v, 0⟩

omit [Fintype F] [DecidableEq F] in
theorem auxiliaryEllipticCurve_equation_iff (u v x y : F) :
    (auxiliaryEllipticCurve u v).toAffine.Equation x y ↔
      y ^ 2 = x * (x - u) * (x - v) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [auxiliaryEllipticCurve, zero_mul, add_zero]
  ring_nf

omit [Fintype F] [DecidableEq F] in
theorem auxiliaryEllipticCurve_delta (u v : F) :
    (auxiliaryEllipticCurve u v).Δ = 16 * u ^ 2 * v ^ 2 * (u - v) ^ 2 := by
  simp only [auxiliaryEllipticCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

omit [Fintype F] [DecidableEq F] in
theorem auxiliaryEllipticCurve_delta_ne_zero
    (hF : ringChar F ≠ 2) {u v : F} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    (auxiliaryEllipticCurve u v).Δ ≠ 0 := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have h16 : (16 : F) ≠ 0 := by
    rw [show (16 : F) = 2 ^ 4 by norm_num]
    exact pow_ne_zero 4 h2
  rw [auxiliaryEllipticCurve_delta]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero h16 (pow_ne_zero 2 hu)) (pow_ne_zero 2 hv))
    (pow_ne_zero 2 (sub_ne_zero.mpr huv))

omit [Fintype F] [DecidableEq F] in
theorem auxiliaryEllipticCurve_isElliptic
    (hF : ringChar F ≠ 2) {u v : F} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    (auxiliaryEllipticCurve u v).IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (auxiliaryEllipticCurve_delta_ne_zero hF hu hv huv)⟩

omit [Fintype F] [DecidableEq F] in
/-- The cubic model associated to two distinct quadratic branches is elliptic. -/
theorem auxiliaryEllipticCurve_branches_delta_ne_zero
    (hF : ringChar F ≠ 2) {A B C D : F}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0)
    (hcross : A * D ≠ B * C) :
    (auxiliaryEllipticCurve (B * C) (A * D)).Δ ≠ 0 :=
  auxiliaryEllipticCurve_delta_ne_zero hF (mul_ne_zero hB hC) (mul_ne_zero hA hD)
    (Ne.symm hcross)

omit [Fintype F] [DecidableEq F] in
theorem auxiliaryEllipticCurve_branches_isElliptic
    (hF : ringChar F ≠ 2) {A B C D : F}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0)
    (hcross : A * D ≠ B * C) :
    (auxiliaryEllipticCurve (B * C) (A * D)).IsElliptic :=
  auxiliaryEllipticCurve_isElliptic hF (mul_ne_zero hB hC) (mul_ne_zero hA hD)
    (Ne.symm hcross)

/-- The Weierstrass curve attached to the two Markoff auxiliary branches. -/
def markoffAuxiliaryEllipticCurve (a b : F) : WeierstrassCurve F :=
  auxiliaryEllipticCurve
    ((9 * b ^ 2 - 4) * (4 * a ^ 2))
    ((9 * a ^ 2 - 4) * (4 * b ^ 2))

omit [Fintype F] [DecidableEq F] in
/-- Admissibility and the off-diagonal condition make the Markoff cubic model elliptic. -/
theorem markoffAuxiliaryEllipticCurve_delta_ne_zero
    (hF : ringChar F ≠ 2) {a b : F}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hA : 9 * a ^ 2 - 4 ≠ 0) (hB : 9 * b ^ 2 - 4 ≠ 0)
    (hab : a ^ 2 ≠ b ^ 2) :
    (markoffAuxiliaryEllipticCurve a b).Δ ≠ 0 := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 ^ 2 by norm_num]
    exact pow_ne_zero 2 h2
  have hC : (4 * a ^ 2 : F) ≠ 0 := mul_ne_zero h4 (pow_ne_zero 2 ha)
  have hD : (4 * b ^ 2 : F) ≠ 0 := mul_ne_zero h4 (pow_ne_zero 2 hb)
  have h16 : (16 : F) ≠ 0 := by
    rw [show (16 : F) = 2 ^ 4 by norm_num]
    exact pow_ne_zero 4 h2
  have hcross :
      (9 * a ^ 2 - 4) * (4 * b ^ 2) ≠ (9 * b ^ 2 - 4) * (4 * a ^ 2) := by
    intro h
    have hzero : (16 : F) * (a ^ 2 - b ^ 2) = 0 := by
      calc
        (16 : F) * (a ^ 2 - b ^ 2) =
            (9 * a ^ 2 - 4) * (4 * b ^ 2) -
              (9 * b ^ 2 - 4) * (4 * a ^ 2) := by ring
        _ = 0 := sub_eq_zero.mpr h
    exact (mul_ne_zero h16 (sub_ne_zero.mpr hab)) hzero
  simpa only [markoffAuxiliaryEllipticCurve] using
    auxiliaryEllipticCurve_branches_delta_ne_zero hF hA hB hC hD hcross

theorem squareRootCount_nonnegative (t : F) : 0 ≤ squareRootCount t := by
  simp [squareRootCount]

theorem squareRootCount_le_two (hF : ringChar F ≠ 2) (t : F) :
    squareRootCount t ≤ 2 := by
  rw [squareRootCount_eq_quadraticChar_add_one hF]
  by_cases ht : t = 0
  · simp [ht]
  · rcases quadraticChar_dichotomy ht with h | h <;> rw [h] <;> norm_num

theorem squareRootCount_eq_zero_of_no_root {t : F} (h : ¬ ∃ x : F, x ^ 2 = t) :
    squareRootCount t = 0 := by
  change (((univ.filter fun x : F ↦ x ^ 2 = t).card : ℕ) : ℤ) = 0
  norm_cast
  rw [card_eq_zero, filter_eq_empty_iff]
  intro x _ hx
  exact h ⟨x, hx⟩

/-- The exact Hasse input makes the total number of affine auxiliary triples exceed the twelve
triples that can lie above three forbidden first coordinates. -/
theorem twelve_lt_auxiliaryTripleCount
    (hHasse : BGS.FiniteField.LegendrePointCardHasseBound F)
    (hF : ringChar F ≠ 2) (hcard : 26 ≤ Fintype.card F)
    {A B C D : F} (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0)
    (hcross : A * D ≠ B * C) :
    12 < auxiliaryTripleCount A B C D := by
  have hu : B * C ≠ 0 := mul_ne_zero hB hC
  have hv : A * D ≠ 0 := mul_ne_zero hA hD
  have huv : B * C ≠ A * D := Ne.symm hcross
  have htrace := BGS.FiniteField.fifteen_sub_card_lt_ellipticCubicCharacterSum
    hHasse hF hcard hu hv huv
  have hquartic := quarticTrace_add_leadingChar_eq_monicCubicTrace
    hF hA hB hcross
  have hcount := auxiliaryTripleCount_eq hF hA hB hC hD
  have hchiA : quadraticChar F A ≤ 1 := by
    rcases quadraticChar_dichotomy hA with h | h <;> omega
  have hchiB : quadraticChar F B ≤ 1 := by
    rcases quadraticChar_dichotomy hB with h | h <;> omega
  have hchiAB : quadraticChar F (A * B) ≤ 1 := by
    rcases quadraticChar_dichotomy (mul_ne_zero hA hB) with h | h <;> omega
  dsimp [BGS.FiniteField.ellipticCubicCharacterSum] at htrace
  omega

/-- Hasse's bound for the explicit elliptic model yields an auxiliary point away from any three
forbidden first coordinates. -/
theorem exists_auxiliary_triple_away_from_three
    (hHasse : BGS.FiniteField.LegendrePointCardHasseBound F)
    (hF : ringChar F ≠ 2) (hcard : 26 ≤ Fintype.card F)
    {A B C D : F} (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0)
    (hcross : A * D ≠ B * C) (bad : Finset F) (hbad : bad.card ≤ 3) :
    ∃ y, y ∉ bad ∧ ∃ lambda mu,
      lambda ^ 2 = branchValue A C y ∧ mu ^ 2 = branchValue B D y := by
  classical
  let term (y : F) : ℤ :=
    squareRootCount (branchValue A C y) * squareRootCount (branchValue B D y)
  have htermNonnegative (y : F) : 0 ≤ term y :=
    mul_nonneg (squareRootCount_nonnegative _) (squareRootCount_nonnegative _)
  have htermLeFour (y : F) : term y ≤ 4 := by
    dsimp [term]
    nlinarith [squareRootCount_nonnegative (branchValue A C y),
      squareRootCount_nonnegative (branchValue B D y),
      squareRootCount_le_two hF (branchValue A C y),
      squareRootCount_le_two hF (branchValue B D y)]
  by_contra hExists
  have hzeroOutside (y : F) (hy : y ∉ bad) : term y = 0 := by
    by_cases hfirst : ∃ lambda : F, lambda ^ 2 = branchValue A C y
    · have hsecond : ¬ ∃ mu : F, mu ^ 2 = branchValue B D y := by
        rintro ⟨mu, hmu⟩
        obtain ⟨lambda, hlambda⟩ := hfirst
        exact hExists ⟨y, hy, lambda, mu, hlambda, hmu⟩
      simp [term, squareRootCount_eq_zero_of_no_root hsecond]
    · simp [term, squareRootCount_eq_zero_of_no_root hfirst]
  have hrestrict : ∑ y ∈ bad, term y = ∑ y : F, term y := by
    apply sum_subset (subset_univ bad)
    intro y _ hy
    exact hzeroOutside y hy
  have hupper : ∑ y : F, term y ≤ 12 := by
    rw [← hrestrict]
    calc
      ∑ y ∈ bad, term y ≤ ∑ _y ∈ bad, (4 : ℤ) :=
        sum_le_sum fun y _ ↦ htermLeFour y
      _ = (bad.card : ℤ) * 4 := by simp
      _ ≤ 12 := by exact_mod_cast Nat.mul_le_mul_right 4 hbad
  have hlower : 12 < ∑ y : F, term y := by
    simpa [auxiliaryTripleCount, term] using
      twelve_lt_auxiliaryTripleCount hHasse hF hcard hA hB hC hD hcross
  omega

end BGS.Markoff
