/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# The explicit elliptic character sum needed by the incidence argument

This file reduces the needed Legendre character-sum estimate to a narrow
point-cardinality target.  The target is an explicit proposition parameter,
not a `sorry` or axiom; the selected Theorem 1 route does not use it.
-/

@[expose] public section

namespace BGS.FiniteField

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The quadratic-character trace sum of `Y² = X (X - u) (X - v)`. -/
def ellipticCubicCharacterSum (u v : F) : ℤ :=
  ∑ x : F, quadraticChar F (x * (x - u) * (x - v))

/-- The Weierstrass model `Y² = X (X - u) (X - v)`. -/
def legendreWeierstrassCurve (u v : F) : WeierstrassCurve F :=
  ⟨0, -(u + v), 0, u * v, 0⟩

omit [Fintype F] [DecidableEq F] in
lemma legendreWeierstrassCurve_equation_iff (u v x y : F) :
    (legendreWeierstrassCurve u v).toAffine.Equation x y ↔
      y ^ 2 = x * (x - u) * (x - v) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [legendreWeierstrassCurve, zero_mul, neg_mul, add_mul]
  constructor <;> intro h
  · linear_combination h
  · linear_combination h

omit [Fintype F] [DecidableEq F] in
lemma legendreWeierstrassCurve_discriminant (u v : F) :
    (legendreWeierstrassCurve u v).Δ = 16 * u ^ 2 * v ^ 2 * (u - v) ^ 2 := by
  simp only [legendreWeierstrassCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

omit [Fintype F] [DecidableEq F] in
lemma legendreWeierstrassCurve_discriminant_ne_zero {u v : F}
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) (hF : ringChar F ≠ 2) :
    (legendreWeierstrassCurve u v).Δ ≠ 0 := by
  rw [legendreWeierstrassCurve_discriminant]
  have htwo : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hsixteen : (16 : F) ≠ 0 := by
    rw [show (16 : F) = 2 ^ 4 by norm_num]
    exact pow_ne_zero 4 htwo
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hsixteen (pow_ne_zero 2 hu))
    (pow_ne_zero 2 hv)) (pow_ne_zero 2 (sub_ne_zero.mpr huv))

/-- Affine solutions, rearranged into fibers of the `X`-coordinate. -/
def affineCubicSolutionEquivSigma (u v : F) :
    {xy : F × F // xy.2 ^ 2 = xy.1 * (xy.1 - u) * (xy.1 - v)} ≃
      Σ x : F, {y : F // y ^ 2 = x * (x - u) * (x - v)} where
  toFun xy := ⟨xy.1.1, xy.1.2, xy.2⟩
  invFun xy := ⟨(xy.1, xy.2.1), xy.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The affine Weierstrass equation is exactly the displayed cubic equation. -/
def legendreAffineEquationEquiv (u v : F) :
    {xy : F × F // (legendreWeierstrassCurve u v).toAffine.Equation xy.1 xy.2} ≃
      {xy : F × F // xy.2 ^ 2 = xy.1 * (xy.1 - u) * (xy.1 - v)} where
  toFun xy := ⟨xy.1, (legendreWeierstrassCurve_equation_iff u v xy.1.1 xy.1.2).mp xy.2⟩
  invFun xy := ⟨xy.1, (legendreWeierstrassCurve_equation_iff u v xy.1.1 xy.1.2).mpr xy.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma affineCubicSolution_card_eq_card_add_characterSum
    (hF : ringChar F ≠ 2) (u v : F) :
    (Fintype.card {xy : F × F // xy.2 ^ 2 = xy.1 * (xy.1 - u) * (xy.1 - v)} : ℤ) =
      Fintype.card F + ellipticCubicCharacterSum u v := by
  rw [Fintype.card_congr (affineCubicSolutionEquivSigma u v), Fintype.card_sigma]
  push_cast
  calc
    ∑ x : F, (Fintype.card {y : F // y ^ 2 = x * (x - u) * (x - v)} : ℤ) =
        ∑ x : F, (quadraticChar F (x * (x - u) * (x - v)) + 1) := by
      apply sum_congr rfl
      intro x _
      calc
        (Fintype.card {y : F // y ^ 2 = x * (x - u) * (x - v)} : ℤ) =
            ((({y : F | y ^ 2 = x * (x - u) * (x - v)} : Set F).toFinset.card : ℕ) : ℤ) := by
              rw [Set.toFinset_card]
              exact_mod_cast Fintype.card_congr
                (Equiv.refl {y : F // y ^ 2 = x * (x - u) * (x - v)})
        _ = quadraticChar F (x * (x - u) * (x - v)) + 1 :=
          quadraticChar_card_sqrts hF (x * (x - u) * (x - v))
    _ = Fintype.card F + ellipticCubicCharacterSum u v := by
      simp [ellipticCubicCharacterSum, sum_add_distrib, add_comm]

omit [Fintype F] [DecidableEq F] in
/-- The nonsingularity hypotheses give an honest elliptic-curve instance for the Legendre model. -/
theorem legendreWeierstrassCurveIsElliptic {u v : F}
    (hF : ringChar F ≠ 2) (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    (legendreWeierstrassCurve u v).IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (legendreWeierstrassCurve_discriminant_ne_zero hu hv huv hF)⟩

/-- The exact rational-point identity behind the cubic character sum. -/
theorem legendreWeierstrassCurve_point_card_eq_card_add_one_add_characterSum
    (hF : ringChar F ≠ 2) {u v : F} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    (Nat.card (legendreWeierstrassCurve u v).toAffine.Point : ℤ) =
      Fintype.card F + 1 + ellipticCubicCharacterSum u v := by
  let W := legendreWeierstrassCurve u v
  let : W.IsElliptic := legendreWeierstrassCurveIsElliptic hF hu hv huv
  calc
    (Nat.card W.toAffine.Point : ℤ) =
        Nat.card (WithZero {xy : F × F // W.toAffine.Equation xy.1 xy.2}) := by
      exact_mod_cast Nat.card_congr W.toAffine.pointEquiv
    _ = Nat.card {xy : F × F // W.toAffine.Equation xy.1 xy.2} + 1 := by
      change (Nat.card (Option {xy : F × F // W.toAffine.Equation xy.1 xy.2}) : ℤ) = _
      rw [Finite.card_option]
      norm_num
    _ = Nat.card {xy : F × F // xy.2 ^ 2 = xy.1 * (xy.1 - u) * (xy.1 - v)} + 1 := by
      exact_mod_cast congrArg (fun n : ℕ => n + 1)
        (Nat.card_congr (legendreAffineEquationEquiv u v))
    _ = Fintype.card {xy : F × F // xy.2 ^ 2 = xy.1 * (xy.1 - u) * (xy.1 - v)} + 1 := by
      rw [Nat.card_eq_fintype_card]
    _ = Fintype.card F + ellipticCubicCharacterSum u v + 1 := by
      rw [affineCubicSolution_card_eq_card_add_characterSum hF u v]
    _ = Fintype.card F + 1 + ellipticCubicCharacterSum u v := by ring

/-- The cubic sum is the negative of the usual Frobenius trace `q + 1 - #E(F)`. -/
theorem ellipticCubicCharacterSum_eq_point_card_sub_card_sub_one
    (hF : ringChar F ≠ 2) {u v : F} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    ellipticCubicCharacterSum u v =
      (Nat.card (legendreWeierstrassCurve u v).toAffine.Point : ℤ) - Fintype.card F - 1 := by
  have hcount := legendreWeierstrassCurve_point_card_eq_card_add_one_add_characterSum
    hF hu hv huv
  linarith

/-- The desired character-sum estimate is exactly the Hasse rational-point bound for this model. -/
theorem ellipticCubicCharacterSum_sq_le_four_mul_card_iff_point_card_hasse
    (hF : ringChar F ≠ 2) {u v : F} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    ellipticCubicCharacterSum u v ^ 2 ≤ 4 * (Fintype.card F : ℤ) ↔
      ((Nat.card (legendreWeierstrassCurve u v).toAffine.Point : ℤ) -
        Fintype.card F - 1) ^ 2 ≤ 4 * (Fintype.card F : ℤ) := by
  rw [ellipticCubicCharacterSum_eq_point_card_sub_card_sub_one hF hu hv huv]

/-- The exact Legendre-family Hasse target.  It is retained only as an
explicit premise for the optional incidence-diameter route. -/
def LegendrePointCardHasseBound (F : Type*)
    [Field F] [Fintype F] [DecidableEq F] : Prop :=
  ∀ {u v : F}, u ≠ 0 → v ≠ 0 → u ≠ v →
    ((Nat.card (legendreWeierstrassCurve u v).toAffine.Point : ℤ) -
      Fintype.card F - 1) ^ 2 ≤ 4 * (Fintype.card F : ℤ)

/--
The exact Hasse character-sum input needed in Proposition 6.  Unlike the point-cardinality bound
above, this is now a proved reduction rather than a second gap.
-/
theorem ellipticCubicCharacterSum_sq_le_four_mul_card
    (hHasse : LegendrePointCardHasseBound F)
    (hF : ringChar F ≠ 2) {u v : F} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    ellipticCubicCharacterSum u v ^ 2 ≤ 4 * (Fintype.card F : ℤ) := by
  exact (ellipticCubicCharacterSum_sq_le_four_mul_card_iff_point_card_hasse
    hF hu hv huv).2 (hHasse hu hv huv)

/-- For fields of cardinality at least `26`, Hasse's square bound is strong enough to leave more
than twelve points after the three forbidden fibers are removed. -/
theorem fifteen_sub_card_lt_ellipticCubicCharacterSum
    (hHasse : LegendrePointCardHasseBound F)
    (hF : ringChar F ≠ 2) (hcard : 26 ≤ Fintype.card F)
    {u v : F} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    (15 : ℤ) - Fintype.card F < ellipticCubicCharacterSum u v := by
  let q : ℤ := Fintype.card F
  let trace : ℤ := ellipticCubicCharacterSum u v
  have hq : (26 : ℤ) ≤ q := by
    dsimp [q]
    exact_mod_cast hcard
  have hHasse : trace ^ 2 ≤ 4 * q := by
    simpa [q, trace] using
      ellipticCubicCharacterSum_sq_le_four_mul_card hHasse hF hu hv huv
  by_contra hbound
  have htrace : trace ≤ 15 - q := by omega
  have hleftNonnegative : 0 ≤ -trace - (q - 15) := by omega
  have hrightNonnegative : 0 ≤ -trace + (q - 15) := by omega
  have hsquareLower : (q - 15) ^ 2 ≤ trace ^ 2 := by
    nlinarith [mul_nonneg hleftNonnegative hrightNonnegative]
  have hfactorPositive : 0 < (q - 9) * (q - 25) :=
    mul_pos (by omega) (by omega)
  nlinarith

end BGS.FiniteField
