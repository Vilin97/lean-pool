/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.TraceCurve.Kummer
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The Laurent split trace cover inside its Kummer function field

This file constructs the comparison map that was missing between the denominator-cleared affine
trace-cover coordinate ring, localized away from the two coordinate axes, and the explicit
odd-coprime Kummer tower.  Injectivity is kept as the visible remaining wall; it is not encoded as
an axiom or typeclass field.
-/

@[expose] public section

namespace BGS.Markoff

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

/-- The affine coordinate ring of the normalized split trace cover. -/
abbrev SplitTraceAffineCoordinateRing (K : Type*) [Field K]
    (sigma : K) (d e : ℕ) :=
  MvPolynomial (Fin 2) K ⧸
    Ideal.span {splitTraceCoverPolynomial (1 : K) sigma d e}

/-- The product of the two coordinate functions in the affine trace-cover ring. -/
def splitTraceAffineCoordinateProduct (sigma : K) (d e : ℕ) :
    SplitTraceAffineCoordinateRing K sigma d e :=
  Ideal.Quotient.mk _ (MvPolynomial.X 0 * MvPolynomial.X 1)

/-- The coordinate ring of the open trace cover in the two-dimensional torus. -/
abbrev SplitTraceLaurentCoordinateRing (K : Type*) [Field K]
    (sigma : K) (d e : ℕ) :=
  Localization.Away (splitTraceAffineCoordinateProduct sigma d e)

section OddCoprimeTower

variable (sigma : K) (hsigma : sigma ≠ 0) (e d : ℕ)
  (heOdd : Odd e) (hdOdd : Odd d) (hde : d.Coprime e)

/-- Evaluation of the two affine coordinates at the canonical roots of the Kummer tower. -/
def splitTracePolynomialToKummerTop :
    MvPolynomial (Fin 2) K →ₐ[K] SplitTraceXiFunctionField K sigma e d := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  let hEtaIrred := splitTraceEtaKummerPolynomial_irreducible' sigma hsigma e heOdd
  letI : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) := ⟨hEtaIrred⟩
  let hXiIrred :=
    splitTraceXiKummerPolynomial_irreducible sigma hsigma e d heOdd hdOdd hde
  letI : Fact (Irreducible (splitTraceXiKummerPolynomial sigma e d)) := ⟨hXiIrred⟩
  exact MvPolynomial.aeval ![splitTraceXiRoot sigma e d,
    splitTraceEtaRootInXiField sigma e d]

/-- The defining affine trace-cover relation vanishes under evaluation in the Kummer tower. -/
lemma splitTracePolynomialToKummerTop_relation :
    splitTracePolynomialToKummerTop sigma hsigma e d heOdd hdOdd hde
      (splitTraceCoverPolynomial 1 sigma d e) = 0 := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  let : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  let hEtaIrred := splitTraceEtaKummerPolynomial_irreducible' sigma hsigma e heOdd
  let : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) := ⟨hEtaIrred⟩
  let hXiIrred :=
    splitTraceXiKummerPolynomial_irreducible sigma hsigma e d heOdd hdOdd hde
  let : Fact (Irreducible (splitTraceXiKummerPolynomial sigma e d)) := ⟨hXiIrred⟩
  have hCover := splitTraceKummerTower_roots_on_cover
    sigma hsigma e d heOdd hdOdd hde
  have hsigmaMap :
      splitTraceBaseElementInXiField sigma e d
          (algebraMap (RatFunc K) (SplitTraceBaseFunctionField K sigma) (RatFunc.C sigma)) =
        algebraMap K (SplitTraceXiFunctionField K sigma e d) sigma := by
    rw [show RatFunc.C sigma = algebraMap K (RatFunc K) sigma by
      rw [RatFunc.algebraMap_eq_C]]
    change algebraMap (RatFunc K) (SplitTraceXiFunctionField K sigma e d)
        (algebraMap K (RatFunc K) sigma) =
      algebraMap K (SplitTraceXiFunctionField K sigma e d) sigma
    exact (IsScalarTower.algebraMap_apply K (RatFunc K)
      (SplitTraceXiFunctionField K sigma e d) sigma).symm
  rw [hsigmaMap] at hCover
  simpa [splitTracePolynomialToKummerTop, MvPolynomial.aeval_def,
    splitTraceCoverPolynomial] using hCover

/-- The affine trace-cover coordinate ring maps canonically to the Kummer top field. -/
def splitTraceAffineToKummerTop :
    SplitTraceAffineCoordinateRing K sigma d e →ₐ[K]
      SplitTraceXiFunctionField K sigma e d := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  let hEtaIrred := splitTraceEtaKummerPolynomial_irreducible' sigma hsigma e heOdd
  letI : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) := ⟨hEtaIrred⟩
  let hXiIrred :=
    splitTraceXiKummerPolynomial_irreducible sigma hsigma e d heOdd hdOdd hde
  letI : Fact (Irreducible (splitTraceXiKummerPolynomial sigma e d)) := ⟨hXiIrred⟩
  refine Ideal.Quotient.liftₐ
    (Ideal.span {splitTraceCoverPolynomial (1 : K) sigma d e})
    (splitTracePolynomialToKummerTop sigma hsigma e d heOdd hdOdd hde) ?_
  intro p hp
  have hle : Ideal.span {splitTraceCoverPolynomial (1 : K) sigma d e} ≤
      RingHom.ker
        (splitTracePolynomialToKummerTop sigma hsigma e d heOdd hdOdd hde).toRingHom := by
    rw [Ideal.span_le]
    intro q hq
    simp only [Set.mem_singleton_iff] at hq
    subst q
    exact splitTracePolynomialToKummerTop_relation sigma hsigma e d heOdd hdOdd hde
  exact hle hp

@[simp]
lemma splitTraceAffineToKummerTop_coordinate (i : Fin 2) :
    splitTraceAffineToKummerTop sigma hsigma e d heOdd hdOdd hde
        (Ideal.Quotient.mk _ (MvPolynomial.X i)) =
      ![splitTraceXiRoot sigma e d, splitTraceEtaRootInXiField sigma e d] i := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  let : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  let hEtaIrred := splitTraceEtaKummerPolynomial_irreducible' sigma hsigma e heOdd
  let : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) := ⟨hEtaIrred⟩
  let hXiIrred :=
    splitTraceXiKummerPolynomial_irreducible sigma hsigma e d heOdd hdOdd hde
  let : Fact (Irreducible (splitTraceXiKummerPolynomial sigma e d)) := ⟨hXiIrred⟩
  change MvPolynomial.aeval
    ![splitTraceXiRoot sigma e d, splitTraceEtaRootInXiField sigma e d] (MvPolynomial.X i) = _
  simp

lemma splitTraceBaseV_sq :
    splitTraceBaseV sigma ^ 2 =
      algebraMap (RatFunc K) (SplitTraceBaseFunctionField K sigma)
        (splitTraceRadicand sigma) := by
  apply sub_eq_zero.mp
  have h := AdjoinRoot.eval₂_root (splitTraceBaseKummerPolynomial sigma)
  rw [splitTraceBaseKummerPolynomial] at h
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C] at h
  rw [← AdjoinRoot.algebraMap_eq] at h
  exact h

lemma splitTraceEtaRoot_pow :
    (AdjoinRoot.root (splitTraceEtaKummerPolynomial sigma e)) ^ e =
      algebraMap (SplitTraceBaseFunctionField K sigma)
        (SplitTraceEtaFunctionField K sigma e) (splitTraceBaseV sigma) := by
  apply sub_eq_zero.mp
  have h := AdjoinRoot.eval₂_root (splitTraceEtaKummerPolynomial sigma e)
  rw [splitTraceEtaKummerPolynomial] at h
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C] at h
  rw [← AdjoinRoot.algebraMap_eq] at h
  exact h

lemma splitTraceXiRoot_pow :
    splitTraceXiRoot sigma e d ^ d =
      algebraMap (SplitTraceEtaFunctionField K sigma e)
        (SplitTraceXiFunctionField K sigma e d) (splitTraceXiRadicand sigma e) := by
  apply sub_eq_zero.mp
  have h := AdjoinRoot.eval₂_root (splitTraceXiKummerPolynomial sigma e d)
  rw [splitTraceXiKummerPolynomial] at h
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C] at h
  rw [← AdjoinRoot.algebraMap_eq] at h
  exact h

lemma splitTraceBaseV_ne_zero (hsigma : sigma ≠ 0) : splitTraceBaseV sigma ≠ 0 := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  let : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  change AdjoinRoot.root (splitTraceBaseKummerPolynomial sigma) ≠ 0
  exact (root_X_pow_sub_C_ne_zero_iff hBaseIrred).mpr
    (splitTraceRadicand_ne_zero sigma hsigma)

lemma splitTraceBaseU_ne_zero (hsigma : sigma ≠ 0) : splitTraceBaseU sigma ≠ 0 := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  let : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  exact (map_ne_zero_iff _
    (algebraMap (RatFunc K) (SplitTraceBaseFunctionField K sigma)).injective).mpr
      RatFunc.X_ne_zero

lemma splitTraceEtaRootInXiField_ne_zero
    (hsigma : sigma ≠ 0) (heOdd : Odd e) (hdOdd : Odd d) (hde : d.Coprime e) :
    splitTraceEtaRootInXiField sigma e d ≠ 0 := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  let : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  let hEtaIrred := splitTraceEtaKummerPolynomial_irreducible' sigma hsigma e heOdd
  let : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) := ⟨hEtaIrred⟩
  let hXiIrred :=
    splitTraceXiKummerPolynomial_irreducible sigma hsigma e d heOdd hdOdd hde
  let : Fact (Irreducible (splitTraceXiKummerPolynomial sigma e d)) := ⟨hXiIrred⟩
  apply (map_ne_zero_iff _
    (algebraMap (SplitTraceEtaFunctionField K sigma e)
      (SplitTraceXiFunctionField K sigma e d)).injective).mpr
  change AdjoinRoot.root (splitTraceEtaKummerPolynomial sigma e) ≠ 0
  change AdjoinRoot.root (X ^ e - C (splitTraceBaseV sigma)) ≠ 0
  exact (root_X_pow_sub_C_ne_zero_iff hEtaIrred).mpr
    (splitTraceBaseV_ne_zero (sigma := sigma) hsigma)

lemma splitTraceXiRoot_ne_zero
    (hsigma : sigma ≠ 0) (heOdd : Odd e) (hdOdd : Odd d) (hde : d.Coprime e) :
    splitTraceXiRoot sigma e d ≠ 0 := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  let : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  let hEtaIrred := splitTraceEtaKummerPolynomial_irreducible' sigma hsigma e heOdd
  let : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) := ⟨hEtaIrred⟩
  let hXiIrred :=
    splitTraceXiKummerPolynomial_irreducible sigma hsigma e d heOdd hdOdd hde
  let : Fact (Irreducible (splitTraceXiKummerPolynomial sigma e d)) := ⟨hXiIrred⟩
  have hRadicand : splitTraceXiRadicand sigma e ≠ 0 := by
    apply (map_ne_zero_iff _
      (algebraMap (SplitTraceBaseFunctionField K sigma)
        (SplitTraceEtaFunctionField K sigma e)).injective).mpr
    exact mul_ne_zero
      (splitTraceBaseU_ne_zero (sigma := sigma) hsigma)
      (splitTraceBaseV_ne_zero (sigma := sigma) hsigma)
  change AdjoinRoot.root (X ^ d - C (splitTraceXiRadicand sigma e)) ≠ 0
  exact (root_X_pow_sub_C_ne_zero_iff hXiIrred).mpr hRadicand

lemma splitTraceAffineCoordinateProduct_maps_to_nonzero :
    letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) :=
      ⟨splitTraceBaseKummerPolynomial_irreducible sigma hsigma⟩
    letI : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) :=
      ⟨splitTraceEtaKummerPolynomial_irreducible' sigma hsigma e heOdd⟩
    letI : Fact (Irreducible (splitTraceXiKummerPolynomial sigma e d)) :=
      ⟨splitTraceXiKummerPolynomial_irreducible sigma hsigma e d heOdd hdOdd hde⟩
    splitTraceAffineToKummerTop sigma hsigma e d heOdd hdOdd hde
      (splitTraceAffineCoordinateProduct sigma d e) ≠ 0 := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  let : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  let hEtaIrred := splitTraceEtaKummerPolynomial_irreducible' sigma hsigma e heOdd
  let : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) := ⟨hEtaIrred⟩
  let hXiIrred :=
    splitTraceXiKummerPolynomial_irreducible sigma hsigma e d heOdd hdOdd hde
  let : Fact (Irreducible (splitTraceXiKummerPolynomial sigma e d)) := ⟨hXiIrred⟩
  change splitTraceAffineToKummerTop sigma hsigma e d heOdd hdOdd hde
      (Ideal.Quotient.mk _ (MvPolynomial.X 0 * MvPolynomial.X 1)) ≠ 0
  simp only [map_mul]
  rw [splitTraceAffineToKummerTop_coordinate, splitTraceAffineToKummerTop_coordinate]
  exact mul_ne_zero
    (splitTraceXiRoot_ne_zero (sigma := sigma) (e := e) (d := d)
      hsigma heOdd hdOdd hde)
    (splitTraceEtaRootInXiField_ne_zero (sigma := sigma) (e := e) (d := d)
      hsigma heOdd hdOdd hde)

/-- The image of the coordinate product is a unit for algebraic reasons internal to the Kummer
tower.  This proof uses the three root-power equations, rather than treating the top quotient as a
field through a late typeclass instance. -/
lemma splitTraceAffineCoordinateProduct_maps_to_isUnit :
    IsUnit (splitTraceAffineToKummerTop sigma hsigma e d heOdd hdOdd hde
      (splitTraceAffineCoordinateProduct sigma d e)) := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  let : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  let hEtaIrred := splitTraceEtaKummerPolynomial_irreducible' sigma hsigma e heOdd
  let : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) := ⟨hEtaIrred⟩
  let hXiIrred :=
    splitTraceXiKummerPolynomial_irreducible sigma hsigma e d heOdd hdOdd hde
  let : Fact (Irreducible (splitTraceXiKummerPolynomial sigma e d)) := ⟨hXiIrred⟩
  have hBaseUUnit : IsUnit (splitTraceBaseU sigma) :=
    (isUnit_iff_ne_zero.mpr RatFunc.X_ne_zero).map
      (algebraMap (RatFunc K) (SplitTraceBaseFunctionField K sigma))
  have hBaseVUnit : IsUnit (splitTraceBaseV sigma) := by
    apply (isUnit_pow_iff (by norm_num : (2 : ℕ) ≠ 0)).mp
    rw [splitTraceBaseV_sq]
    exact (isUnit_iff_ne_zero.mpr (splitTraceRadicand_ne_zero sigma hsigma)).map
      (algebraMap (RatFunc K) (SplitTraceBaseFunctionField K sigma))
  have hEtaUnit :
      IsUnit (AdjoinRoot.root (splitTraceEtaKummerPolynomial sigma e)) := by
    have he : e ≠ 0 := by
      rintro rfl
      simp at heOdd
    apply (isUnit_pow_iff he).mp
    rw [splitTraceEtaRoot_pow]
    exact hBaseVUnit.map
      (algebraMap (SplitTraceBaseFunctionField K sigma)
        (SplitTraceEtaFunctionField K sigma e))
  have hEtaTopUnit : IsUnit (splitTraceEtaRootInXiField sigma e d) :=
    hEtaUnit.map (algebraMap (SplitTraceEtaFunctionField K sigma e)
      (SplitTraceXiFunctionField K sigma e d))
  have hXiRadicandUnit : IsUnit (splitTraceXiRadicand sigma e) :=
    (hBaseUUnit.mul hBaseVUnit).map
      (algebraMap (SplitTraceBaseFunctionField K sigma)
        (SplitTraceEtaFunctionField K sigma e))
  have hXiUnit : IsUnit (splitTraceXiRoot sigma e d) := by
    have hd : d ≠ 0 := by
      rintro rfl
      simp at hdOdd
    apply (isUnit_pow_iff hd).mp
    rw [splitTraceXiRoot_pow]
    exact hXiRadicandUnit.map
      (algebraMap (SplitTraceEtaFunctionField K sigma e)
        (SplitTraceXiFunctionField K sigma e d))
  have himage :
      splitTraceAffineToKummerTop sigma hsigma e d heOdd hdOdd hde
          (splitTraceAffineCoordinateProduct sigma d e) =
        splitTraceXiRoot sigma e d * splitTraceEtaRootInXiField sigma e d := by
    change splitTraceAffineToKummerTop sigma hsigma e d heOdd hdOdd hde
      (Ideal.Quotient.mk _ (MvPolynomial.X 0 * MvPolynomial.X 1)) = _
    simp only [map_mul]
    rw [splitTraceAffineToKummerTop_coordinate, splitTraceAffineToKummerTop_coordinate]
    simp
  rw [himage]
  exact hXiUnit.mul hEtaTopUnit

/-- The affine comparison map extends uniquely across the localization inverting both trace-cover
coordinates. -/
def splitTraceLaurentToKummerTop :
    letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) :=
      ⟨splitTraceBaseKummerPolynomial_irreducible sigma hsigma⟩
    letI : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) :=
      ⟨splitTraceEtaKummerPolynomial_irreducible' sigma hsigma e heOdd⟩
    letI : Fact (Irreducible (splitTraceXiKummerPolynomial sigma e d)) :=
      ⟨splitTraceXiKummerPolynomial_irreducible sigma hsigma e d heOdd hdOdd hde⟩
    SplitTraceLaurentCoordinateRing K sigma d e →ₐ[K]
      SplitTraceXiFunctionField K sigma e d := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  let hEtaIrred := splitTraceEtaKummerPolynomial_irreducible' sigma hsigma e heOdd
  letI : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) := ⟨hEtaIrred⟩
  let hXiIrred :=
    splitTraceXiKummerPolynomial_irreducible sigma hsigma e d heOdd hdOdd hde
  letI : Fact (Irreducible (splitTraceXiKummerPolynomial sigma e d)) := ⟨hXiIrred⟩
  apply IsLocalization.Away.liftAlgHom (splitTraceAffineCoordinateProduct sigma d e)
  exact splitTraceAffineCoordinateProduct_maps_to_isUnit
    sigma hsigma e d heOdd hdOdd hde

theorem splitTraceLaurentToKummerTop_algebraMap_apply
    (a : SplitTraceAffineCoordinateRing K sigma d e) :
    letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) :=
      ⟨splitTraceBaseKummerPolynomial_irreducible sigma hsigma⟩
    letI : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) :=
      ⟨splitTraceEtaKummerPolynomial_irreducible' sigma hsigma e heOdd⟩
    letI : Fact (Irreducible (splitTraceXiKummerPolynomial sigma e d)) :=
      ⟨splitTraceXiKummerPolynomial_irreducible sigma hsigma e d heOdd hdOdd hde⟩
    splitTraceLaurentToKummerTop sigma hsigma e d heOdd hdOdd hde
        (algebraMap (SplitTraceAffineCoordinateRing K sigma d e)
          (SplitTraceLaurentCoordinateRing K sigma d e) a) =
      splitTraceAffineToKummerTop sigma hsigma e d heOdd hdOdd hde a := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  let : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  let hEtaIrred := splitTraceEtaKummerPolynomial_irreducible' sigma hsigma e heOdd
  let : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) := ⟨hEtaIrred⟩
  let hXiIrred :=
    splitTraceXiKummerPolynomial_irreducible sigma hsigma e d heOdd hdOdd hde
  let : Fact (Irreducible (splitTraceXiKummerPolynomial sigma e d)) := ⟨hXiIrred⟩
  simp only [splitTraceLaurentToKummerTop, IsLocalization.Away.liftAlgHom_apply]
  apply IsLocalization.Away.lift_eq

/-- Injectivity of the Laurent comparison map is reduced exactly to injectivity of the affine
quotient map.  No domain hypothesis is manufactured here: proving the affine map injective is the
remaining kernel-equality/irreducibility wall. -/
theorem splitTraceLaurentToKummerTop_injective_of_affine_injective
    (hAffine : Function.Injective
      (splitTraceAffineToKummerTop sigma hsigma e d heOdd hdOdd hde)) :
    letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) :=
      ⟨splitTraceBaseKummerPolynomial_irreducible sigma hsigma⟩
    letI : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) :=
      ⟨splitTraceEtaKummerPolynomial_irreducible' sigma hsigma e heOdd⟩
    letI : Fact (Irreducible (splitTraceXiKummerPolynomial sigma e d)) :=
      ⟨splitTraceXiKummerPolynomial_irreducible sigma hsigma e d heOdd hdOdd hde⟩
    Function.Injective
      (splitTraceLaurentToKummerTop sigma hsigma e d heOdd hdOdd hde) := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  let : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  let hEtaIrred := splitTraceEtaKummerPolynomial_irreducible' sigma hsigma e heOdd
  let : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) := ⟨hEtaIrred⟩
  let hXiIrred :=
    splitTraceXiKummerPolynomial_irreducible sigma hsigma e d heOdd hdOdd hde
  let : Fact (Irreducible (splitTraceXiKummerPolynomial sigma e d)) := ⟨hXiIrred⟩
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (splitTraceAffineCoordinateProduct sigma d e))
    (splitTraceLaurentToKummerTop sigma hsigma e d heOdd hdOdd hde).toRingHom).2
  intro x y
  change algebraMap (SplitTraceAffineCoordinateRing K sigma d e)
        (SplitTraceLaurentCoordinateRing K sigma d e) x =
      algebraMap (SplitTraceAffineCoordinateRing K sigma d e)
        (SplitTraceLaurentCoordinateRing K sigma d e) y ↔
    splitTraceLaurentToKummerTop sigma hsigma e d heOdd hdOdd hde
        (algebraMap (SplitTraceAffineCoordinateRing K sigma d e)
          (SplitTraceLaurentCoordinateRing K sigma d e) x) =
      splitTraceLaurentToKummerTop sigma hsigma e d heOdd hdOdd hde
        (algebraMap (SplitTraceAffineCoordinateRing K sigma d e)
          (SplitTraceLaurentCoordinateRing K sigma d e) y)
  rw [splitTraceLaurentToKummerTop_algebraMap_apply,
    splitTraceLaurentToKummerTop_algebraMap_apply]
  constructor
  · intro hxy
    have hMapped := congrArg
      (splitTraceLaurentToKummerTop sigma hsigma e d heOdd hdOdd hde) hxy
    simpa only [splitTraceLaurentToKummerTop_algebraMap_apply] using hMapped
  · intro hxy
    exact congrArg
      (algebraMap (SplitTraceAffineCoordinateRing K sigma d e)
        (SplitTraceLaurentCoordinateRing K sigma d e)) (hAffine hxy)

end OddCoprimeTower

end

end BGS.Markoff
