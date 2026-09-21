/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.FiniteField.QuadraticCharacter
import LeanPool.MarkoffModP.BGS.Markoff.Core.Basic
import LeanPool.MarkoffModP.BGS.Markoff.Incidence.Geometry
import LeanPool.MarkoffModP.BGS.Markoff.Incidence.PointCount

/-!
# Incidence of Markoff conic fibers

This file formalizes the algebra behind Proposition 6 of Bourgain--Gamburd--Sarnak.  Geometric
integrality is proved in `BGS.Markoff.IncidenceCoordinateRing`; the independent Hasse point-count
gap is isolated in `BGS.FiniteField.EllipticCharacterSum`.
-/

namespace BGS.Markoff

universe u

variable {F : Type u} [Field F]

/-- The Markoff fiber obtained by fixing the first coordinate. -/
def fiber1 (a : F) : Set (Point F) :=
  {x | IsMarkoff x ∧ x.x1 = a}

/-- The Markoff fiber obtained by fixing the second coordinate. -/
def fiber2 (a : F) : Set (Point F) :=
  {x | IsMarkoff x ∧ x.x2 = a}

/-- The Markoff fiber obtained by fixing the third coordinate. -/
def fiber3 (a : F) : Set (Point F) :=
  {x | IsMarkoff x ∧ x.x3 = a}

/-- Two fibers meet when their set-theoretic intersection is nonempty. -/
def FibersMeet (s t : Set (Point F)) : Prop :=
  (s ∩ t).Nonempty

/--
The affine auxiliary equations used in the paper to find one third-coordinate fiber meeting
the fibers with first-coordinate value `a` and second-coordinate value `b`.
-/
def IncidenceAux (a b y lambda mu : F) : Prop :=
  (9 * a ^ 2 - 4) * y ^ 2 - lambda ^ 2 = 4 * a ^ 2 ∧
    (9 * b ^ 2 - 4) * y ^ 2 - mu ^ 2 = 4 * b ^ 2

open MvPolynomial
open scoped TensorProduct

noncomputable section

/-- The first equation of the auxiliary curve, with variables `(y, lambda, mu)`. -/
def incidenceAuxPolynomial1 {K : Type u} [Field K] (a : K) :
    MvPolynomial (Fin 3) K :=
  C (9 * a ^ 2 - 4) * X 0 ^ 2 - X 1 ^ 2 - C (4 * a ^ 2)

/-- The second equation of the auxiliary curve, with variables `(y, lambda, mu)`. -/
def incidenceAuxPolynomial2 {K : Type u} [Field K] (b : K) :
    MvPolynomial (Fin 3) K :=
  C (9 * b ^ 2 - 4) * X 0 ^ 2 - X 2 ^ 2 - C (4 * b ^ 2)

/-- The ideal cutting out the affine auxiliary curve from Proposition 6. -/
def incidenceAuxIdeal {K : Type u} [Field K] (a b : K) :
    Ideal (MvPolynomial (Fin 3) K) :=
  Ideal.span {incidenceAuxPolynomial1 a, incidenceAuxPolynomial2 b}

/-- The affine coordinate ring of the auxiliary curve. -/
abbrev IncidenceAuxCoordinateRing (K : Type u) [Field K] (a b : K) :=
  MvPolynomial (Fin 3) K ⧸ incidenceAuxIdeal a b

/-- The actual geometric-integrality condition required before applying a Weil bound. -/
def IncidenceAuxGeometricallyIntegral {K : Type u} [Field K] (a b : K) : Prop :=
  IsDomain (AlgebraicClosure K ⊗[K] IncidenceAuxCoordinateRing K a b)

end

@[simp]
theorem eval_incidenceAuxPolynomial1_vec
    {K : Type u} [Field K] (a y lambda mu : K) :
    aeval ![y, lambda, mu] (incidenceAuxPolynomial1 a) =
      (9 * a ^ 2 - 4) * y ^ 2 - lambda ^ 2 - 4 * a ^ 2 := by
  simp [incidenceAuxPolynomial1]

@[simp]
theorem eval_incidenceAuxPolynomial2_vec
    {K : Type u} [Field K] (b y lambda mu : K) :
    aeval ![y, lambda, mu] (incidenceAuxPolynomial2 b) =
      (9 * b ^ 2 - 4) * y ^ 2 - mu ^ 2 - 4 * b ^ 2 := by
  simp [incidenceAuxPolynomial2]

/-- The coordinate-ring equations are exactly the two scalar equations used in the incidence
argument. -/
theorem incidenceAux_iff_aeval_eq_zero
    {K : Type u} [Field K] (a b y lambda mu : K) :
    IncidenceAux a b y lambda mu ↔
      aeval ![y, lambda, mu] (incidenceAuxPolynomial1 a) = 0 ∧
        aeval ![y, lambda, mu] (incidenceAuxPolynomial2 b) = 0 := by
  simp [IncidenceAux, sub_eq_zero]

/-- A chosen root of the quadratic defining the intersection of two coordinate fibers. -/
def conicRoot (a y discriminantRoot : F) : F :=
  (3 * a * y + discriminantRoot) / 2

lemma markoffPolynomial_conicRoot
    (h2 : (2 : F) ≠ 0) {a y discriminantRoot : F}
    (h : (9 * a ^ 2 - 4) * y ^ 2 - discriminantRoot ^ 2 = 4 * a ^ 2) :
    markoffPolynomial ⟨a, conicRoot a y discriminantRoot, y⟩ = 0 := by
  have h4 : (4 : F) ≠ 0 := by
    intro h4
    apply (mul_ne_zero h2 h2)
    calc
      (2 : F) * 2 = 4 := by norm_num
      _ = 0 := h4
  calc
    markoffPolynomial ⟨a, conicRoot a y discriminantRoot, y⟩ =
        -(((9 * a ^ 2 - 4) * y ^ 2 - discriminantRoot ^ 2) - 4 * a ^ 2) / 4 := by
      simp only [markoffPolynomial, conicRoot]
      field_simp [h2, h4]
      ring
    _ = 0 := by rw [h]; simp

lemma point_mem_fiber1_inter_fiber3
    (h2 : (2 : F) ≠ 0) {a y discriminantRoot : F}
    (h : (9 * a ^ 2 - 4) * y ^ 2 - discriminantRoot ^ 2 = 4 * a ^ 2) :
    ⟨a, conicRoot a y discriminantRoot, y⟩ ∈ fiber1 a ∩ fiber3 y := by
  constructor
  · exact ⟨markoffPolynomial_conicRoot h2 h, rfl⟩
  · exact ⟨markoffPolynomial_conicRoot h2 h, rfl⟩

lemma point_mem_fiber2_inter_fiber3
    (h2 : (2 : F) ≠ 0) {b y discriminantRoot : F}
    (h : (9 * b ^ 2 - 4) * y ^ 2 - discriminantRoot ^ 2 = 4 * b ^ 2) :
    ⟨conicRoot b y discriminantRoot, b, y⟩ ∈ fiber2 b ∩ fiber3 y := by
  have hmarkoff : IsMarkoff ⟨conicRoot b y discriminantRoot, b, y⟩ := by
    change markoffPolynomial (swap12 ⟨b, conicRoot b y discriminantRoot, y⟩) = 0
    rw [markoffPolynomial_swap12]
    exact markoffPolynomial_conicRoot h2 h
  constructor
  · exact ⟨hmarkoff, rfl⟩
  · exact ⟨hmarkoff, rfl⟩

theorem incidenceAux_implies_common_fiber
    (h2 : (2 : F) ≠ 0) {a b y lambda mu : F}
    (h : IncidenceAux a b y lambda mu) :
    FibersMeet (fiber1 a) (fiber3 y) ∧ FibersMeet (fiber2 b) (fiber3 y) := by
  refine ⟨?_, ?_⟩
  · exact ⟨_, point_mem_fiber1_inter_fiber3 h2 h.1⟩
  · exact ⟨_, point_mem_fiber2_inter_fiber3 h2 h.2⟩

/-- A point on the auxiliary curve gives a common fiber, while retaining any extra predicate
required of its `y`-coordinate. -/
theorem incidenceAux_exists_implies_common_fiber_with
    (h2 : (2 : F) ≠ 0) {P : F → Prop} {a b : F}
    (h : ∃ y lambda mu, P y ∧ IncidenceAux a b y lambda mu) :
    ∃ y, P y ∧ FibersMeet (fiber1 a) (fiber3 y) ∧
      FibersMeet (fiber2 b) (fiber3 y) := by
  obtain ⟨y, lambda, mu, hy, haux⟩ := h
  exact ⟨y, hy, incidenceAux_implies_common_fiber h2 haux⟩

/-- On the diagonal `a² = b²`, one equation supplies both auxiliary square roots. -/
theorem diagonal_incidenceAux_of_firstEquation
    {a b y lambda : F} (hab : a ^ 2 = b ^ 2)
    (h : (9 * a ^ 2 - 4) * y ^ 2 - lambda ^ 2 = 4 * a ^ 2) :
    IncidenceAux a b y lambda lambda := by
  refine ⟨h, ?_⟩
  simpa only [← hab] using h

/-- Combine the diagonal and off-diagonal point-existence problems. -/
theorem auxPointExists_of_diagonal_offDiagonal {P : F → Prop}
    (hdiag : ∀ a : F, P a →
      ∃ y lambda, P y ∧
        (9 * a ^ 2 - 4) * y ^ 2 - lambda ^ 2 = 4 * a ^ 2)
    (hoff : ∀ a b : F, P a → P b → a ^ 2 ≠ b ^ 2 →
      ∃ y lambda mu, P y ∧ IncidenceAux a b y lambda mu) :
    ∀ a b : F, P a → P b →
      ∃ y lambda mu, P y ∧ IncidenceAux a b y lambda mu := by
  intro a b ha hb
  by_cases hab : a ^ 2 = b ^ 2
  · obtain ⟨y, lambda, hy, heq⟩ := hdiag a ha
    exact ⟨y, lambda, lambda, hy, diagonal_incidenceAux_of_firstEquation hab heq⟩
  · exact hoff a b ha hb hab

/-- Coordinates retained as vertices of the paper's incidence graph. -/
def IsAdmissibleCoordinate {p : ℕ} (a : ZMod p) : Prop :=
  a ≠ 0 ∧ (3 * a) ^ 2 ≠ 4

/-- The three first-coordinate values excluded from the incidence graph. -/
def forbiddenIntermediateCoordinates (p : ℕ) [Fact p.Prime] : Finset (ZMod p) :=
  {0, 2 / 3, -(2 / 3)}

theorem forbiddenIntermediateCoordinates_card_le_three
    (p : ℕ) [Fact p.Prime] : (forbiddenIntermediateCoordinates p).card ≤ 3 := by
  exact Finset.card_le_three

/-- A natural number smaller than the modulus remains nonzero in `ZMod p`. -/
theorem natCast_ne_zero_zmod_of_pos_of_lt
    {n p : ℕ} (hn : 0 < n) (hnp : n < p) : (n : ZMod p) ≠ 0 := by
  intro hzero
  have hdvd : p ∣ n := (ZMod.natCast_eq_zero_iff n p).mp hzero
  exact (Nat.not_le_of_gt hnp) (Nat.le_of_dvd hn hdvd)

/-- Outside the three forbidden values, a coordinate is admissible. -/
theorem admissible_of_not_mem_forbiddenIntermediateCoordinates
    {p : ℕ} [Fact p.Prime] (h3 : (3 : ZMod p) ≠ 0) {y : ZMod p}
    (hy : y ∉ forbiddenIntermediateCoordinates p) : IsAdmissibleCoordinate y := by
  constructor
  · intro hzero
    exact hy (by simp [forbiddenIntermediateCoordinates, hzero])
  · intro hsquare
    have hsquare' : (3 * y) ^ 2 = (2 : ZMod p) ^ 2 := by
      calc
        (3 * y) ^ 2 = 4 := hsquare
        _ = (2 : ZMod p) ^ 2 := by norm_num
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquare' with hpositive | hnegative
    · have hyvalue : y = 2 / 3 :=
        (eq_div_iff h3).2 (by simpa [mul_comm] using hpositive)
      exact hy (by simp [forbiddenIntermediateCoordinates, hyvalue])
    · have hyvalue : y = -(2 / 3) := by
        rw [← neg_div]
        exact (eq_div_iff h3).2 (by simpa [mul_comm] using hnegative)
      exact hy (by simp [forbiddenIntermediateCoordinates, hyvalue])

/-- The exact auxiliary-point conclusion, including the condition that the new fiber remains a
vertex of the incidence graph. -/
def IncidenceAuxPointAt (p : ℕ) (hp : p.Prime) : Prop :=
  letI : Fact p.Prime := ⟨hp⟩
  ∀ a b : ZMod p,
    IsAdmissibleCoordinate a →
      IsAdmissibleCoordinate b →
        ∃ y lambda mu : ZMod p,
          IsAdmissibleCoordinate y ∧ IncidenceAux a b y lambda mu

/-- The common-fiber conclusion actually needed for the diameter-two incidence argument. -/
def IncidenceBridgeAt (p : ℕ) (hp : p.Prime) : Prop :=
  letI : Fact p.Prime := ⟨hp⟩
  ∀ a b : ZMod p,
    IsAdmissibleCoordinate a →
      IsAdmissibleCoordinate b →
        ∃ y : ZMod p,
          IsAdmissibleCoordinate y ∧
            FibersMeet (fiber1 a) (fiber3 y) ∧ FibersMeet (fiber2 b) (fiber3 y)

/--
The diagonal finite-field point problem suppressed in line 661 of the paper.

Besides finding an affine conic point, the proof must avoid the three possible forbidden
coordinates `y = 0, ±2/3`.
-/
theorem incidenceAux_diagonal_point :
    ∃ p0 : ℕ, ∀ (p : ℕ) (_hp : p.Prime), p0 ≤ p →
      ∀ a : ZMod p, IsAdmissibleCoordinate a →
        ∃ y lambda : ZMod p,
          IsAdmissibleCoordinate y ∧
            (9 * a ^ 2 - 4) * y ^ 2 - lambda ^ 2 = 4 * a ^ 2 := by
  refine ⟨11, ?_⟩
  intro p hp hpLarge a ha
  letI : Fact p.Prime := ⟨hp⟩
  have h3lt : 3 < p := by omega
  have h4lt : 4 < p := by omega
  have h3 : (3 : ZMod p) ≠ 0 :=
    natCast_ne_zero_zmod_of_pos_of_lt (by norm_num) h3lt
  have h4 : (4 : ZMod p) ≠ 0 :=
    natCast_ne_zero_zmod_of_pos_of_lt (by norm_num) h4lt
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    omega
  have hcard : 8 ≤ Fintype.card (ZMod p) := by
    rw [ZMod.card]
    omega
  have hA : (9 * a ^ 2 - 4 : ZMod p) ≠ 0 := by
    intro hzero
    apply ha.2
    calc
      (3 * a) ^ 2 = 9 * a ^ 2 := by ring
      _ = 4 := sub_eq_zero.mp hzero
  have hC : (4 * a ^ 2 : ZMod p) ≠ 0 := by
    exact mul_ne_zero h4 (pow_ne_zero 2 ha.1)
  obtain ⟨y, hy, lambda, hlambda⟩ :=
    BGS.FiniteField.exists_quadratic_conic_point_away_from_three
      hchar hcard hA hC (forbiddenIntermediateCoordinates p)
      (forbiddenIntermediateCoordinates_card_le_three p)
  refine ⟨y, lambda, admissible_of_not_mem_forbiddenIntermediateCoordinates h3 hy, ?_⟩
  linear_combination -hlambda

/--
The geometric-integrality assertion needed in the off-diagonal case.

The paper merely calls the affine curve irreducible. A Weil argument needs geometric
integrality of an appropriate model, and the assertion still requires a proof.
-/
def IncidenceAuxOffDiagonalGeometryAt (p : ℕ) (hp : p.Prime) : Prop :=
  letI : Fact p.Prime := ⟨hp⟩
  ∀ a b : ZMod p,
    IsAdmissibleCoordinate a → IsAdmissibleCoordinate b → a ^ 2 ≠ b ^ 2 →
      IncidenceAuxGeometricallyIntegral a b

/-- The off-diagonal auxiliary-point statement reduced to the explicit elliptic character sum. -/
def IncidenceAuxOffDiagonalPointAt (p : ℕ) (hp : p.Prime) : Prop :=
  letI : Fact p.Prime := ⟨hp⟩
  ∀ a b : ZMod p,
    IsAdmissibleCoordinate a → IsAdmissibleCoordinate b → a ^ 2 ≠ b ^ 2 →
      ∃ y lambda mu : ZMod p,
        IsAdmissibleCoordinate y ∧ IncidenceAux a b y lambda mu

/-- Optional Legendre Hasse premise for the incidence-diameter route.  The
selected Theorem 1 proof does not use this route. -/
def ZModLegendrePointCardHasseBound : Prop :=
  ∀ (p : ℕ) [Fact p.Prime],
    BGS.FiniteField.LegendrePointCardHasseBound (ZMod p)

/--
The off-diagonal auxiliary point follows from the narrow Hasse bound for
`Y² = X (X - u) (X - v)`.  This direct route does not pretend that geometric integrality alone
contains the missing genus and point-count estimates.
-/
theorem incidenceAux_offDiagonal_point
    (hHasse : ZModLegendrePointCardHasseBound) :
    ∃ p0 : ℕ, ∀ (p : ℕ) (_hp : p.Prime), p0 ≤ p →
      IncidenceAuxOffDiagonalPointAt p _hp := by
  refine ⟨29, ?_⟩
  intro p hp hpLarge a b ha hb hab
  letI : Fact p.Prime := ⟨hp⟩
  have h3lt : 3 < p := by omega
  have h4lt : 4 < p := by omega
  have h16lt : 16 < p := by omega
  have h3 : (3 : ZMod p) ≠ 0 :=
    natCast_ne_zero_zmod_of_pos_of_lt (by norm_num) h3lt
  have h4 : (4 : ZMod p) ≠ 0 :=
    natCast_ne_zero_zmod_of_pos_of_lt (by norm_num) h4lt
  have h16 : (16 : ZMod p) ≠ 0 :=
    natCast_ne_zero_zmod_of_pos_of_lt (by norm_num) h16lt
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    omega
  have hcard : 26 ≤ Fintype.card (ZMod p) := by
    rw [ZMod.card]
    omega
  have hA : (9 * a ^ 2 - 4 : ZMod p) ≠ 0 := by
    intro hzero
    apply ha.2
    calc
      (3 * a) ^ 2 = 9 * a ^ 2 := by ring
      _ = 4 := sub_eq_zero.mp hzero
  have hB : (9 * b ^ 2 - 4 : ZMod p) ≠ 0 := by
    intro hzero
    apply hb.2
    calc
      (3 * b) ^ 2 = 9 * b ^ 2 := by ring
      _ = 4 := sub_eq_zero.mp hzero
  have hC : (4 * a ^ 2 : ZMod p) ≠ 0 :=
    mul_ne_zero h4 (pow_ne_zero 2 ha.1)
  have hD : (4 * b ^ 2 : ZMod p) ≠ 0 :=
    mul_ne_zero h4 (pow_ne_zero 2 hb.1)
  have hcross :
      (9 * a ^ 2 - 4) * (4 * b ^ 2) ≠ (9 * b ^ 2 - 4) * (4 * a ^ 2) := by
    intro h
    have hzero : (16 : ZMod p) * (a ^ 2 - b ^ 2) = 0 := by
      calc
        (16 : ZMod p) * (a ^ 2 - b ^ 2) =
            (9 * a ^ 2 - 4) * (4 * b ^ 2) -
              (9 * b ^ 2 - 4) * (4 * a ^ 2) := by ring
        _ = 0 := sub_eq_zero.mpr h
    exact (mul_ne_zero h16 (sub_ne_zero.mpr hab)) hzero
  obtain ⟨y, hy, lambda, mu, hlambda, hmu⟩ :=
    exists_auxiliary_triple_away_from_three (hHasse p) hchar hcard hA hB hC hD hcross
      (forbiddenIntermediateCoordinates p) (forbiddenIntermediateCoordinates_card_le_three p)
  refine ⟨y, lambda, mu,
    admissible_of_not_mem_forbiddenIntermediateCoordinates h3 hy, ?_, ?_⟩
  · dsimp [branchValue] at hlambda
    linear_combination -hlambda
  · dsimp [branchValue] at hmu
    linear_combination -hmu

/-- For all sufficiently large primes, the explicit auxiliary equations have an admissible
solution for every pair of admissible coordinates. -/
theorem incidenceAuxPoint_eventually
    (hHasse : ZModLegendrePointCardHasseBound) :
    ∃ p0 : ℕ, ∀ (p : ℕ) (hp : p.Prime), p0 ≤ p → IncidenceAuxPointAt p hp := by
  obtain ⟨pDiag, hDiag⟩ := incidenceAux_diagonal_point
  obtain ⟨pOff, hOff⟩ := incidenceAux_offDiagonal_point hHasse
  refine ⟨pDiag + pOff, ?_⟩
  intro p hp hpLarge
  letI : Fact p.Prime := ⟨hp⟩
  exact auxPointExists_of_diagonal_offDiagonal
    (hDiag p hp (by omega)) (hOff p hp (by omega))

/-- A prime larger than two has `2 ≠ 0` in its prime field. -/
theorem two_ne_zero_zmod {p : ℕ} (hp : 2 < p) : (2 : ZMod p) ≠ 0 := by
  exact natCast_ne_zero_zmod_of_pos_of_lt (by norm_num) hp

/-- An admissible solution of the auxiliary equations gives the required graph bridge. -/
theorem incidenceBridgeAt_of_auxPoint
    (p : ℕ) (hp : p.Prime) (h2 : (2 : ZMod p) ≠ 0)
    (haux : IncidenceAuxPointAt p hp) : IncidenceBridgeAt p hp := by
  letI : Fact p.Prime := ⟨hp⟩
  intro a b ha hb
  exact incidenceAux_exists_implies_common_fiber_with h2 (haux a b ha hb)

/-- The bridge is a consequence of the exposed point-existence problems, not an assumption. -/
theorem incidenceBridge_eventually
    (hHasse : ZModLegendrePointCardHasseBound) :
    ∃ p0 : ℕ, ∀ (p : ℕ) (hp : p.Prime), p0 ≤ p → IncidenceBridgeAt p hp := by
  obtain ⟨pAux, hAux⟩ := incidenceAuxPoint_eventually hHasse
  refine ⟨3 + pAux, ?_⟩
  intro p hp hpLarge
  exact incidenceBridgeAt_of_auxPoint p hp (two_ne_zero_zmod (by omega))
    (hAux p hp (by omega))

/-- The bridge specialized to primes congruent to three modulo four. -/
theorem incidenceBridge_mod_three
    (hHasse : ZModLegendrePointCardHasseBound) :
    ∃ p0 : ℕ, ∀ (p : ℕ) (hp : p.Prime), p0 ≤ p → p % 4 = 3 → IncidenceBridgeAt p hp := by
  obtain ⟨p0, h⟩ := incidenceBridge_eventually hHasse
  exact ⟨p0, fun p hp hpLarge _ => h p hp hpLarge⟩

/-- The admissible-fiber bridge specialized to primes congruent to one modulo four. -/
theorem incidenceBridge_mod_one_admissible
    (hHasse : ZModLegendrePointCardHasseBound) :
    ∃ p0 : ℕ, ∀ (p : ℕ) (hp : p.Prime), p0 ≤ p → p % 4 = 1 → IncidenceBridgeAt p hp := by
  obtain ⟨p0, h⟩ := incidenceBridge_eventually hHasse
  exact ⟨p0, fun p hp hpLarge _ => h p hp hpLarge⟩

end BGS.Markoff
