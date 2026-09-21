/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.FiniteField.EllipticCharacterSum
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Finite.Basic

/-!
# Frobenius setup for the explicit Hasse bound

This work file develops the Frobenius--norm route to Hasse's bound for the explicit curve
`Y² = X (X - u) (X - v)`.  It contains no replacement assumption for Hasse's theorem: the aim is
to isolate, in Mathlib's actual elliptic-point API, the first geometric degree calculation that is
still missing.
-/

noncomputable section

namespace BGS.FiniteField

open Polynomial

variable {F : Type*} [Field F]

local instance algebraicClosureDecidableEq :
    DecidableEq (AlgebraicClosure F) := Classical.decEq _

/-- The Legendre affine model after base change to an extension field. -/
abbrev legendreAffineOver (u v : F) (K : Type*) [Field K] [Algebra F K] :
    WeierstrassCurve.Affine K :=
  WeierstrassCurve.Affine.baseChange (legendreWeierstrassCurve u v).toAffine
    K

/-- Coordinatewise transport of a Legendre point along a field-extension homomorphism.

Mathlib's bundled point map requires elliptic-curve group instances.  This underlying map does not:
nonsingular points transport along every injective field homomorphism, including before we have
installed the nonsingularity hypotheses on the Legendre model. -/
def mapLegendrePointCoordinates {K L : Type*} [Field K] [Field L]
    [Algebra F K] [Algebra F L] (u v : F) (f : K →ₐ[F] L) :
    (legendreAffineOver u v K).Point → (legendreAffineOver u v L).Point
  | .zero => .zero
  | .some x y h => .some (f x) (f y)
      (((legendreWeierstrassCurve u v).toAffine.baseChange_nonsingular f.injective x y).mpr h)

/-- The Legendre affine model over a fixed algebraic closure. -/
abbrev legendreAffineOverClosure (u v : F) : WeierstrassCurve.Affine (AlgebraicClosure F) :=
  legendreAffineOver u v (AlgebraicClosure F)

/-- Base change of an `F`-rational Legendre point to the algebraic closure. -/
def legendrePointBaseChange (u v : F) :
    (legendreWeierstrassCurve u v).toAffine.Point →
      (legendreAffineOverClosure u v).Point
  | .zero => .zero
  | .some x y h => .some (algebraMap F (AlgebraicClosure F) x)
      (algebraMap F (AlgebraicClosure F) y)
      (((legendreWeierstrassCurve u v).toAffine.baseChange_nonsingular
        (Algebra.ofId F (AlgebraicClosure F)).injective x y).mpr h)

/-- Base change into the algebraic closure is injective on Legendre points. -/
theorem legendrePointBaseChange_injective (u v : F) :
    Function.Injective (legendrePointBaseChange u v) := by
  rintro (_ | _) (_ | _) h
  any_goals contradiction
  · rfl
  · simpa only [WeierstrassCurve.Affine.Point.some.injEq] using
      And.intro
        ((algebraMap F (AlgebraicClosure F)).injective
          (WeierstrassCurve.Affine.Point.some.inj h).1)
        ((algebraMap F (AlgebraicClosure F)).injective
          (WeierstrassCurve.Affine.Point.some.inj h).2)

section FiniteBaseField

variable [Fintype F]

/-- The `#F`-power Frobenius acting on points of the Legendre curve over an algebraic closure. -/
def legendrePointFrobenius (u v : F) :
    (legendreAffineOverClosure u v).Point →
      (legendreAffineOverClosure u v).Point :=
  mapLegendrePointCoordinates u v (FiniteField.frobeniusAlgHom F (AlgebraicClosure F))

/-- The endomorphism `Frob - 1`; its kernel is the group of `F`-rational points. -/
def legendreFrobeniusMinusIdentity (u v : F) :
    (legendreAffineOverClosure u v).Point →
      (legendreAffineOverClosure u v).Point := by
  classical
  exact fun P ↦ (legendrePointFrobenius u v P).add (-P)

@[simp]
theorem legendrePointFrobenius_zero (u v : F) :
    legendrePointFrobenius u v 0 = 0 := rfl

/-- An algebraic-closure element fixed by the `#F`-power Frobenius comes from `F`.

This is the coordinate descent input for identifying the kernel of `Frob - 1`: it is proved from
the complete root multiset of `X ^ #F - X`, rather than assumed as a fixed-field theorem. -/
theorem exists_eq_algebraMap_of_frobenius_eq (z : AlgebraicClosure F)
    (hz : FiniteField.frobeniusAlgHom F (AlgebraicClosure F) z = z) :
    ∃ x : F, algebraMap F (AlgebraicClosure F) x = z := by
  let P : F[X] := X ^ Fintype.card F - X
  have hP0 : P ≠ 0 := by
    exact FiniteField.X_pow_card_sub_X_ne_zero F Fintype.one_lt_card
  have hsplit : P.Splits := by
    rw [Polynomial.splits_iff_card_roots]
    dsimp [P]
    rw [FiniteField.roots_X_pow_card_sub_X, ← Finset.card_def, Finset.card_univ,
      FiniteField.X_pow_card_sub_X_natDegree_eq F Fintype.one_lt_card]
  have hzroot : (P.map (algebraMap F (AlgebraicClosure F))).IsRoot z := by
    rw [Polynomial.IsRoot.def]
    rw [Polynomial.eval_map]
    dsimp [P]
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X]
    exact sub_eq_zero.mpr hz
  exact hsplit.mem_range_of_isRoot hP0 hzroot

@[simp]
theorem legendrePointFrobenius_baseChange (u v : F)
    (P : (legendreWeierstrassCurve u v).toAffine.Point) :
    legendrePointFrobenius u v (legendrePointBaseChange u v P) =
      legendrePointBaseChange u v P := by
  cases P with
  | zero => rfl
  | some x y h =>
      simp only [legendrePointFrobenius, legendrePointBaseChange,
        mapLegendrePointCoordinates, AlgHom.commutes]

/-- Every Frobenius-fixed algebraic-closure point descends to an `F`-rational point. -/
theorem exists_baseChange_eq_of_legendrePointFrobenius_eq (u v : F)
    (P : (legendreAffineOverClosure u v).Point)
    (hP : legendrePointFrobenius u v P = P) :
    ∃ P₀ : (legendreWeierstrassCurve u v).toAffine.Point,
      legendrePointBaseChange u v P₀ = P := by
  cases P with
  | zero => exact ⟨.zero, rfl⟩
  | some x y h =>
      have hxy :
          FiniteField.frobeniusAlgHom F (AlgebraicClosure F) x = x ∧
            FiniteField.frobeniusAlgHom F (AlgebraicClosure F) y = y := by
        simpa only [legendrePointFrobenius, mapLegendrePointCoordinates,
          WeierstrassCurve.Affine.Point.some.injEq] using hP
      obtain ⟨x₀, hx₀⟩ := exists_eq_algebraMap_of_frobenius_eq x hxy.1
      obtain ⟨y₀, hy₀⟩ := exists_eq_algebraMap_of_frobenius_eq y hxy.2
      have hmapped :
          (legendreAffineOverClosure u v).Nonsingular
            (algebraMap F (AlgebraicClosure F) x₀)
            (algebraMap F (AlgebraicClosure F) y₀) := by
        simpa only [hx₀, hy₀] using h
      have hbase : (legendreWeierstrassCurve u v).toAffine.Nonsingular x₀ y₀ :=
        ((legendreWeierstrassCurve u v).toAffine.baseChange_nonsingular
          (Algebra.ofId F (AlgebraicClosure F)).injective x₀ y₀).mp hmapped
      refine ⟨.some x₀ y₀ hbase, ?_⟩
      simp only [legendrePointBaseChange, hx₀, hy₀]

/-- `F`-rational Legendre points are exactly the Frobenius-fixed algebraic-closure points. -/
def legendreRationalPointEquivFrobeniusFixed (u v : F) :
    (legendreWeierstrassCurve u v).toAffine.Point ≃
      {P : (legendreAffineOverClosure u v).Point // legendrePointFrobenius u v P = P} :=
  Equiv.ofBijective
    (fun P ↦ ⟨legendrePointBaseChange u v P, legendrePointFrobenius_baseChange u v P⟩)
    ⟨fun P Q h ↦ legendrePointBaseChange_injective u v (congrArg Subtype.val h),
      fun P ↦ by
        obtain ⟨P₀, hP₀⟩ :=
          exists_baseChange_eq_of_legendrePointFrobenius_eq u v P.1 P.2
        exact ⟨P₀, Subtype.ext hP₀⟩⟩

/-- Point cardinality is the cardinality of the Frobenius fixed-point subtype. -/
theorem legendre_point_card_eq_frobeniusFixed_card (u v : F) :
    Nat.card (legendreWeierstrassCurve u v).toAffine.Point =
      Nat.card {P : (legendreAffineOverClosure u v).Point //
        legendrePointFrobenius u v P = P} :=
  Nat.card_congr (legendreRationalPointEquivFrobeniusFixed u v)

section FrobeniusEndomorphism

variable {u v : F} [(legendreWeierstrassCurve u v).IsElliptic]

/-- The coordinate Frobenius as an endomorphism of the algebraic-closure point group. -/
def legendrePointFrobeniusHom (u v : F)
    [(legendreWeierstrassCurve u v).IsElliptic] :
    (legendreAffineOverClosure u v).Point →+
      (legendreAffineOverClosure u v).Point :=
  WeierstrassCurve.Affine.Point.map
    (W' := (legendreWeierstrassCurve u v).toAffine)
    (FiniteField.frobeniusAlgHom F (AlgebraicClosure F))

@[simp]
theorem legendrePointFrobeniusHom_apply (u v : F)
    [(legendreWeierstrassCurve u v).IsElliptic]
    (P : (legendreAffineOverClosure u v).Point) :
    legendrePointFrobeniusHom u v P = legendrePointFrobenius u v P := by
  cases P <;> rfl

/-- The group endomorphism `Frob - 1`. -/
def legendreFrobeniusMinusIdentityHom (u v : F)
    [(legendreWeierstrassCurve u v).IsElliptic] :
    (legendreAffineOverClosure u v).Point →+
      (legendreAffineOverClosure u v).Point :=
  legendrePointFrobeniusHom u v - AddMonoidHom.id _

/-- The usual Frobenius trace `q + 1 - #E(F)`.  This is the negative of the cubic character sum
used elsewhere in the incidence count. -/
def legendreFrobeniusTrace (u v : F) : ℤ :=
  (Fintype.card F : ℤ) + 1 - Nat.card (legendreWeierstrassCurve u v).toAffine.Point

/-- The single endomorphism used by the integral discriminant proof of Hasse's inequality:
`[t] - [2]Frob`, where `t = q + 1 - #E(F)` is the usual Frobenius trace.

The remaining geometric wall is to construct an isogeny-degree theory strong enough to compute
the degree of this endomorphism as `frobeniusNormForm q t t 2 = 4q - t²`. -/
def legendreHasseWitnessEndomorphism (u v : F)
    [(legendreWeierstrassCurve u v).IsElliptic] :
    (legendreAffineOverClosure u v).Point →+
      (legendreAffineOverClosure u v).Point :=
  legendreFrobeniusTrace u v • AddMonoidHom.id _ -
    (2 : ℤ) • legendrePointFrobeniusHom u v

/-- The rational-point fixed subtype is literally the kernel of `Frob - 1`. -/
def legendreFrobeniusFixedEquivKernel (u v : F)
    [(legendreWeierstrassCurve u v).IsElliptic] :
    {P : (legendreAffineOverClosure u v).Point // legendrePointFrobenius u v P = P} ≃
      (legendreFrobeniusMinusIdentityHom u v).ker where
  toFun P := ⟨P.1, by
    change legendrePointFrobeniusHom u v P.1 - P.1 = 0
    rw [legendrePointFrobeniusHom_apply, P.2, sub_self]⟩
  invFun P := ⟨P.1, by
    have hP := P.2
    change legendrePointFrobeniusHom u v P.1 - P.1 = 0 at hP
    exact legendrePointFrobeniusHom_apply u v P.1 ▸ sub_eq_zero.mp hP⟩
  left_inv P := Subtype.ext rfl
  right_inv P := Subtype.ext rfl

/-- Rational points are equivalent to the kernel of `Frob - 1`. -/
def legendreRationalPointEquivFrobeniusKernel (u v : F)
    [(legendreWeierstrassCurve u v).IsElliptic] :
    (legendreWeierstrassCurve u v).toAffine.Point ≃
      (legendreFrobeniusMinusIdentityHom u v).ker :=
  (legendreRationalPointEquivFrobeniusFixed u v).trans
    (legendreFrobeniusFixedEquivKernel u v)

/-- The point cardinality is the kernel cardinality of `Frob - 1`. -/
theorem legendre_point_card_eq_frobeniusMinusIdentity_ker_card (u v : F)
    [(legendreWeierstrassCurve u v).IsElliptic] :
    Nat.card (legendreWeierstrassCurve u v).toAffine.Point =
      Nat.card (legendreFrobeniusMinusIdentityHom u v).ker :=
  Nat.card_congr (legendreRationalPointEquivFrobeniusKernel u v)

end FrobeniusEndomorphism

@[simp]
theorem legendreFrobeniusMinusIdentity_baseChange (u v : F)
    (P : (legendreWeierstrassCurve u v).toAffine.Point) :
    legendreFrobeniusMinusIdentity u v
        (legendrePointBaseChange u v P) = 0 := by
  classical
  change (legendrePointFrobenius u v (legendrePointBaseChange u v P)).add
    (-(legendrePointBaseChange u v P)) = 0
  rw [legendrePointFrobenius_baseChange]
  cases P with
  | zero => rfl
  | some x y h =>
      simp only [legendrePointBaseChange, WeierstrassCurve.Affine.Point.neg_some]
      exact WeierstrassCurve.Affine.Point.add_of_Y_eq rfl
        (WeierstrassCurve.Affine.negY_negY _ _).symm

/-- The integer quadratic form which Hasse identifies with the degree of `m - n·Frob`. -/
def frobeniusNormForm (q t m n : ℤ) : ℤ :=
  m ^ 2 - t * m * n + q * n ^ 2

/-- The norm-form value of Hasse's witness endomorphism is exactly the discriminant gap. -/
theorem frobeniusNormForm_hasseWitness (q t : ℤ) :
    frobeniusNormForm q t t 2 = 4 * q - t ^ 2 := by
  simp only [frobeniusNormForm]
  ring

/-- A single nonnegative value of Hasse's norm form, at `(m,n) = (t,2)`, forces the
discriminant inequality. -/
theorem sq_le_four_mul_of_frobeniusNormForm_nonnegative {q t : ℤ}
    (hnorm : 0 ≤ frobeniusNormForm q t t 2) : t ^ 2 ≤ 4 * q := by
  rw [frobeniusNormForm_hasseWitness] at hnorm
  omega

/-- The norm-form value which must be identified with the degree of
`legendreHasseWitnessEndomorphism`.  This definition does not assume that identification. -/
def legendreHasseNormWitness (u v : F) : ℤ :=
  let q : ℤ := Fintype.card F
  let t : ℤ := legendreFrobeniusTrace u v
  frobeniusNormForm q t t 2

/-!
### Exact remaining geometric statement

The next theorem must construct a natural-valued algebraic degree for
`legendreHasseWitnessEndomorphism u v` and prove that its integer cast is
`legendreHasseNormWitness u v`.  Nonnegativity would then be automatic and the theorem below would
close Hasse's bound.

This cannot honestly be replaced by the cardinality of the kernel of the underlying abstract group
homomorphism: identifying kernel cardinality with algebraic degree already requires separability,
and the quadratic degree law is geometry, not abstract group theory.  In the current Mathlib API,
the division polynomials are not connected to scalar multiplication on `Affine.Point`, the
`ωₙ` polynomial needed for the `Y`-coordinate is still absent, and no rational-map/isogeny degree or
parallelogram law is available.  Thus even the minimal witness degree requires constructing those
interfaces in-repository.
-/

/-- Once the missing geometric degree calculation proves the norm witness nonnegative, the
arithmetic reduction gives exactly the desired point-cardinality bound. -/
theorem legendreWeierstrassCurve_point_card_hasse_of_normWitness_nonnegative
    {u v : F} (hnorm : 0 ≤ legendreHasseNormWitness u v) :
    ((Nat.card (legendreWeierstrassCurve u v).toAffine.Point : ℤ) -
      Fintype.card F - 1) ^ 2 ≤ 4 * (Fintype.card F : ℤ) := by
  have htrace : legendreFrobeniusTrace u v ^ 2 ≤ 4 * (Fintype.card F : ℤ) :=
    sq_le_four_mul_of_frobeniusNormForm_nonnegative hnorm
  convert htrace using 1
  simp only [legendreFrobeniusTrace]
  ring

/-- Nonnegativity of the explicit Frobenius norm witness is exactly the Hasse point-cardinality
inequality.  Thus the missing algebraic-degree calculation is not merely sufficient: it is the
whole remaining Hasse wall. -/
theorem legendreHasseNormWitness_nonnegative_iff_point_card_hasse (u v : F) :
    0 ≤ legendreHasseNormWitness u v ↔
      ((Nat.card (legendreWeierstrassCurve u v).toAffine.Point : ℤ) -
        Fintype.card F - 1) ^ 2 ≤ 4 * (Fintype.card F : ℤ) := by
  constructor
  · exact legendreWeierstrassCurve_point_card_hasse_of_normWitness_nonnegative
  · intro hhasse
    simp only [legendreHasseNormWitness, frobeniusNormForm_hasseWitness,
      legendreFrobeniusTrace]
    nlinarith [sq_nonneg
      ((Nat.card (legendreWeierstrassCurve u v).toAffine.Point : ℤ) -
        Fintype.card F - 1)]

end FiniteBaseField

end BGS.FiniteField
