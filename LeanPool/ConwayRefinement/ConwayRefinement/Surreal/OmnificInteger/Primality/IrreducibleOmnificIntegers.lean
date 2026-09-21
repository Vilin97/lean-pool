/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.OmnificInteger.Primality.OmnificIntegers
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.CardinalFiniteClassReduction
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.Reduction
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.ReducedCharacterization
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.ReducedDivisibility
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Monomial
public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.ArchimedeanAssumptions

/-!
# Every irreducible omnific integer is prime

Let `b` be an omnific integer, read as a bounded integer-part element of the signed Hahn series
`ℝ⟦Surreal⟧` with nonpositive exponents. If `b` is not an ordinary integer, its lowest exponent is
nonzero, and at the Archimedean class `σ` of that exponent LM24's reduction `ρ_σ(b)` divides `b`
with cofactor the open truncation `τ_σ(b)` (LM24, Definition 8.2.4): `b = ρ_σ(b) · τ_σ(b)`. Both
factors lie in the integer part, the units of the integer part are `±1`, and `ρ_σ(b)` is not a
unit. So an irreducible `b` has `τ_σ(b) ∈ {0, 1, -1}`: `b` or `-b` is reduced (LM24,
Proposition 8.2.5), hence primal (`Surreal.OmnificInteger.isPrimal_of_isReduced`, resting on the
primality of every series), hence prime. An irreducible ordinary integer is a prime number, and
a prime number `p` is prime in the omnific integers: `p` divides an omnific integer exactly when
it divides its integer constant coefficient, since a series without constant term is divisible
by every nonzero integer.

Hence every irreducible omnific integer is prime, and factorisations into irreducibles are unique
up to order and units (`Surreal.OmnificInteger.factorization_unique`).
-/

universe u

public noncomputable section

open Cardinal FiniteArchimedeanClass
open scoped HahnSeries

namespace HahnSeries.Nonpositive

variable {K G R : Type*} {κ : Cardinal}
variable [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
variable [Module K G] [IsOrderedModule K G]
variable [Field R] [Fact (ℵ₀ < κ)]

/-! ### Units of the integer part over the integers -/

variable (Z : Subring R) (hZ : ∀ r : R, r ∈ Z ↔ ∃ z : ℤ, (z : R) = r)
include hZ

/-- When `Z` is the image of `ℤ`, the units of the integer part are `1` and `-1`. -/
theorem eq_one_or_eq_neg_one_of_isUnit [CharZero R]
    {x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z} (hx : IsUnit x) :
    x = 1 ∨ x = -1 := by
  obtain ⟨v, rfl⟩ := hx
  set x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z := ↑v with hxdef
  let y : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z := ↑v⁻¹
  have hxy : x * y = 1 := by rw [hxdef]; exact v.mul_inv
  have hxN := eq_C_constantCoeff_of_isUnit
    ((CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z).isUnit_map v.isUnit)
  have hyN := eq_C_constantCoeff_of_isUnit
    ((CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z).isUnit_map (v⁻¹).isUnit)
  obtain ⟨m, hm⟩ := (hZ _).mp ((mem_cardSuppLTTruncationIntegerPart (Z := Z)).mp x.2).2
  obtain ⟨n, hn⟩ := (hZ _).mp ((mem_cardSuppLTTruncationIntegerPart (Z := Z)).mp y.2).2
  have hxC : CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z x = C (m : R) := by
    rw [hxN, constantCoeff_apply, CardSuppLTTruncationIntegerPart.coe_toNonpositiveRingHom, hm]
  have hyC : CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z y = C (n : R) := by
    rw [hyN, constantCoeff_apply, CardSuppLTTruncationIntegerPart.coe_toNonpositiveRingHom, hn]
  have hmn : ((m * n : ℤ) : R) = 1 := by
    have h := congrArg (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z) hxy
    rw [map_mul, map_one, hxC, hyC, ← map_mul] at h
    have h' := congrArg (fun q : Nonpositive G R ↦ (q : R⟦G⟧)) h
    simp only [coe_C, Subring.coe_one] at h'
    rw [← HahnSeries.C_one] at h'
    rw [Int.cast_mul]
    exact HahnSeries.C_injective h'
  have hm1 : m * n = 1 := by exact_mod_cast hmn
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hm1 with h1 | h1
  · left
    apply CardSuppLTTruncationIntegerPart.toNonpositiveRingHom_injective Z
    rw [hxC, h1, map_one, Int.cast_one, map_one]
  · right
    apply CardSuppLTTruncationIntegerPart.toNonpositiveRingHom_injective Z
    rw [hxC, h1, map_neg, map_one, Int.cast_neg, Int.cast_one, map_neg, map_one]

/-! ### Irreducible elements of the integer part are reduced up to sign -/

/-- An irreducible bounded integer-part element with nonzero lowest exponent is reduced up to
sign: at the class of its lowest exponent, `x = ρ_σ(x) τ_σ(x)` with `ρ_σ(x)` not a unit, so
`τ_σ(x) ∈ {0, 1, -1}` (LM24, Proposition 8.2.5). -/
theorem isReduced_or_isReduced_neg_of_irreducible [CharZero R]
    (u : HahnEmbedding.ArchimedeanStrata K G)
    {x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z} (hirr : Irreducible x)
    (horder : ((CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z x :
      Nonpositive G R) : R⟦G⟧).order ≠ 0) :
    IsReduced (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z x) ∨
      IsReduced (-CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z x) := by
  set xN := CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z x with hxN
  have hx0 : xN ≠ 0 := by
    intro h
    apply horder
    rw [h, Subring.coe_zero, HahnSeries.order_zero]
  set c := leadingClass xN horder with hc
  have hT : T (K := K) c xN = xN := T_leadingClass xN horder
  by_cases htau : tau (K := K) c xN = 0
  · left
    exact (isReduced_iff_tau_leadingClass_eq_zero_or_one xN hx0 horder).mpr (Or.inl htau)
  have hfac := rhoIntegerPart_mul_tauIntegerPart u c Z x hT htau
  rcases hirr.isUnit_or_isUnit hfac.symm with hρ | hτ
  · -- the reduction is not a unit: it would be `1`, forcing `x = τ_σ(x)`
    exfalso
    have hρN : CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z
        (rhoIntegerPart u c Z x hT htau) = 1 := by
      rcases eq_one_or_eq_neg_one_of_isUnit Z hZ hρ with h1 | h1
      · rw [h1, map_one]
      · exfalso
        have hcoeff := coeff_zero_rho_of_tau_ne_zero u c xN htau
        rw [← toNonpositive_rhoIntegerPart u c Z x hT htau, h1, map_neg, map_one] at hcoeff
        have : ((-1 : Nonpositive G R) : R⟦G⟧).coeff 0 = -1 := by
          rw [Subring.coe_neg, Subring.coe_one, HahnSeries.coeff_neg, HahnSeries.coeff_one,
            if_pos rfl]
        rw [this] at hcoeff
        have h2 : (1 : R) + 1 = 0 := by
          calc (1 : R) + 1 = -1 + 1 := by rw [hcoeff]
            _ = 0 := neg_add_cancel 1
        exact two_ne_zero (one_add_one_eq_two.symm.trans h2)
    have hxτ : xN = tau (K := K) c xN := by
      have h := congrArg (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z) hfac
      rw [map_mul, hρN, one_mul, toNonpositive_tauIntegerPart] at h
      exact h.symm
    have hcmk : c = FiniteArchimedeanClass.mk (xN : R⟦G⟧).order horder := by
      apply Subtype.ext
      rw [hc, leadingClass_val, FiniteArchimedeanClass.val_mk]
    have hnot : (xN : R⟦G⟧).order ∉ ball K c := by
      intro hmem
      have hlt := (FiniteArchimedeanClass.mem_ball_iff (K := K)).mp hmem horder
      rw [← hcmk] at hlt
      exact lt_irrefl _ hlt
    have h0 : ((tau (K := K) c xN : Nonpositive G R) : R⟦G⟧).coeff (xN : R⟦G⟧).order = 0 :=
      coeff_tau_of_not_mem c xN hnot
    rw [← hxτ] at h0
    exact hx0 (Subtype.ext (HahnSeries.coeff_order_eq_zero.mp h0))
  · rcases eq_one_or_eq_neg_one_of_isUnit Z hZ hτ with h1 | h1
    · left
      refine (isReduced_iff_tau_leadingClass_eq_zero_or_one (K := K) xN hx0 horder).mpr (Or.inr ?_)
      have h := congrArg (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z) h1
      rw [toNonpositive_tauIntegerPart, map_one] at h
      exact h
    · right
      have hx0' : -xN ≠ 0 := neg_ne_zero.mpr hx0
      have horder' : ((-xN : Nonpositive G R) : R⟦G⟧).order ≠ 0 := by
        rw [Subring.coe_neg, HahnSeries.order_neg]; exact horder
      refine (isReduced_iff_tau_leadingClass_eq_zero_or_one (K := K) (-xN) hx0' horder').mpr
        (Or.inr ?_)
      have hclass : leadingClass (-xN) horder' = c := by
        apply Subtype.ext
        rw [leadingClass_val, leadingClass_val, Subring.coe_neg, HahnSeries.order_neg]
      rw [hclass, map_neg]
      have h := congrArg (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z) h1
      rw [toNonpositive_tauIntegerPart, map_neg, map_one] at h
      rw [h, neg_neg]

/-! ### Prime numbers are prime in the integer part over the integers -/

/-- The integer constant coefficient of a bounded integer-part element over the integers. -/
def intCoeff (x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) : ℤ :=
  Classical.choose ((hZ _).mp ((mem_cardSuppLTTruncationIntegerPart (Z := Z)).mp x.2).2)

theorem intCoeff_spec (x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) :
    ((intCoeff Z hZ x : ℤ) : R) =
      ((x : CardSuppLTField (G := G) (R := R) (κ := κ)) : R⟦G⟧).coeff 0 :=
  Classical.choose_spec ((hZ _).mp ((mem_cardSuppLTTruncationIntegerPart (Z := Z)).mp x.2).2)

/-- The integer constant coefficient is a ring homomorphism to `ℤ`. -/
@[expose] def intCoeffRingHom [CharZero R] :
    cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z →+* ℤ where
  toFun := intCoeff Z hZ
  map_one' := by
    apply Int.cast_injective (α := R)
    rw [intCoeff_spec, Int.cast_one, Subring.coe_one, Subfield.coe_one, HahnSeries.coeff_one,
      if_pos rfl]
  map_mul' x y := by
    apply Int.cast_injective (α := R)
    rw [Int.cast_mul, intCoeff_spec, intCoeff_spec, intCoeff_spec]
    have h := coeff_zero_mul (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z x)
      (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z y)
    rw [Subring.coe_mul, Subfield.coe_mul]
    simpa only [CardSuppLTTruncationIntegerPart.coe_toNonpositiveRingHom] using h
  map_zero' := by
    apply Int.cast_injective (α := R)
    rw [intCoeff_spec, Int.cast_zero, Subring.coe_zero, Subfield.coe_zero, HahnSeries.coeff_zero]
  map_add' x y := by
    apply Int.cast_injective (α := R)
    rw [Int.cast_add, intCoeff_spec, intCoeff_spec, intCoeff_spec, Subring.coe_add,
      Subfield.coe_add, HahnSeries.coeff_add]

theorem intCoeffRingHom_apply [CharZero R]
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) :
    intCoeffRingHom Z hZ x = intCoeff Z hZ x :=
  rfl

omit hZ in
/-- A constant series, in the `κ`-bounded field. -/
@[expose] def constField (r : R) : CardSuppLTField (G := G) (R := R) (κ := κ) :=
  ⟨HahnSeries.C r, by
    rw [mem_cardSuppLTSubfield, HahnSeries.C_apply]
    exact (HahnSeries.cardSupp_single_le _ _).trans_lt (one_lt_aleph0.trans Fact.out)⟩

omit hZ in
theorem coe_constField (r : R) :
    ((constField (G := G) (κ := κ) r : CardSuppLTField (G := G) (R := R) (κ := κ)) : R⟦G⟧) =
      HahnSeries.C r :=
  rfl

/-- An integer `z ≠ 0` divides a bounded integer-part element exactly when it divides its integer
constant coefficient: a series without constant term is divisible by every nonzero integer. -/
theorem intCast_dvd_iff [CharZero R] {z : ℤ} (hz : z ≠ 0)
    (a : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) :
    (z : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) ∣ a ↔
      z ∣ intCoeffRingHom Z hZ a := by
  constructor
  · intro h
    have := map_dvd (intCoeffRingHom Z hZ) h
    rwa [map_intCast, Int.cast_id] at this
  · rintro ⟨k, hk⟩
    have hzR : (z : R) ≠ 0 := Int.cast_ne_zero.mpr hz
    have ha0 : ((a : CardSuppLTField (G := G) (R := R) (κ := κ)) : R⟦G⟧).coeff 0 =
        ((z * k : ℤ) : R) := by
      rw [← hk, intCoeffRingHom_apply, intCoeff_spec]
    -- the quotient `(a - a₀) / z + k`
    let w : CardSuppLTField (G := G) (R := R) (κ := κ) :=
      constField ((z : R)⁻¹) * ((a : CardSuppLTField (G := G) (R := R) (κ := κ)) -
        constField ((z * k : ℤ) : R)) + constField (k : R)
    have hw : (w : R⟦G⟧) = HahnSeries.C ((z : R)⁻¹) *
        (((a : CardSuppLTField (G := G) (R := R) (κ := κ)) : R⟦G⟧) -
          HahnSeries.C ((z * k : ℤ) : R)) +
          HahnSeries.C (k : R) := by
      simp only [w, Subfield.coe_add, Subfield.coe_mul, Subfield.coe_sub, coe_constField]
    have hwmem : w ∈ cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z := by
      rw [mem_cardSuppLTTruncationIntegerPart, hw]
      constructor
      · intro g hg
        rcases HahnSeries.support_add_subset _ _ hg with hg | hg
        · obtain ⟨i, hi, j, hj, rfl⟩ := HahnSeries.support_mul_subset hg
          rw [HahnSeries.C_apply] at hi
          have hi0 : i = 0 := HahnSeries.support_single_subset hi
          change i + j ∈ Set.Iic 0
          rw [hi0, zero_add]
          rw [sub_eq_add_neg] at hj
          rcases HahnSeries.support_add_subset _ _ hj with hj | hj
          · exact ((mem_cardSuppLTTruncationIntegerPart (Z := Z)).mp a.2).1 hj
          · have hj' := HahnSeries.support_neg_subset _ hj
            rw [HahnSeries.C_apply] at hj'
            exact (HahnSeries.support_single_subset hj').le
        · rw [HahnSeries.C_apply] at hg
          exact (HahnSeries.support_single_subset hg).le
      · rw [HahnSeries.coeff_add, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul,
          HahnSeries.coeff_sub, ha0, HahnSeries.C_apply, HahnSeries.coeff_single_same, sub_self,
          smul_zero, zero_add, HahnSeries.C_apply, HahnSeries.coeff_single_same]
        exact (hZ _).mpr ⟨k, rfl⟩
    refine ⟨⟨w, hwmem⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rw [Subring.coe_mul, Subfield.coe_mul, SubringClass.coe_intCast, SubringClass.coe_intCast]
    change ((a : CardSuppLTField (G := G) (R := R) (κ := κ)) : R⟦G⟧) = (z : R⟦G⟧) * (w : R⟦G⟧)
    rw [hw, ← map_intCast (HahnSeries.C : R →+* R⟦G⟧), mul_add, ← mul_assoc, ← map_mul,
      mul_inv_cancel₀ hzR, map_one, one_mul, ← map_mul, ← Int.cast_mul, sub_add_cancel]

/-- A prime number is prime in the integer part over the integers. -/
theorem prime_intCast [CharZero R] {z : ℤ} (hz : Prime z) :
    Prime (z : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) := by
  refine ⟨?_, ?_, fun a b hab ↦ ?_⟩
  · intro h
    apply hz.ne_zero
    have := congrArg (intCoeffRingHom Z hZ) h
    rwa [map_intCast, Int.cast_id, map_zero] at this
  · intro h
    apply hz.not_unit
    rcases eq_one_or_eq_neg_one_of_isUnit Z hZ h with h1 | h1
    · have := congrArg (intCoeffRingHom Z hZ) h1
      rw [map_intCast, Int.cast_id, map_one] at this
      rw [this]; exact isUnit_one
    · have := congrArg (intCoeffRingHom Z hZ) h1
      rw [map_intCast, Int.cast_id, map_neg, map_one] at this
      rw [this]; exact isUnit_one.neg
  · rw [intCast_dvd_iff Z hZ hz.ne_zero, map_mul] at hab
    rcases hz.dvd_or_dvd hab with h | h
    · exact Or.inl ((intCast_dvd_iff Z hZ hz.ne_zero a).mpr h)
    · exact Or.inr ((intCast_dvd_iff Z hZ hz.ne_zero b).mpr h)

/-- An integer irreducible in the integer part over the integers is irreducible in `ℤ`. -/
theorem irreducible_int_of_irreducible_intCast [CharZero R] {z : ℤ}
    (hz : Irreducible (z : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)) :
    Irreducible z := by
  refine ⟨fun h ↦ hz.not_isUnit (h.map (Int.castRingHom _)), fun a b hab ↦ ?_⟩
  have hab' : (z : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) = a * b := by
    rw [hab, Int.cast_mul]
  rcases hz.isUnit_or_isUnit hab' with h | h
  · left
    rcases eq_one_or_eq_neg_one_of_isUnit Z hZ h with h1 | h1
    · have := congrArg (intCoeffRingHom Z hZ) h1
      rw [map_intCast, Int.cast_id, map_one] at this
      rw [this]; exact isUnit_one
    · have := congrArg (intCoeffRingHom Z hZ) h1
      rw [map_intCast, Int.cast_id, map_neg, map_one] at this
      rw [this]; exact isUnit_one.neg
  · right
    rcases eq_one_or_eq_neg_one_of_isUnit Z hZ h with h1 | h1
    · have := congrArg (intCoeffRingHom Z hZ) h1
      rw [map_intCast, Int.cast_id, map_one] at this
      rw [this]; exact isUnit_one
    · have := congrArg (intCoeffRingHom Z hZ) h1
      rw [map_intCast, Int.cast_id, map_neg, map_one] at this
      rw [this]; exact isUnit_one.neg

end HahnSeries.Nonpositive

namespace Surreal.OmnificInteger

open HahnSeries.Nonpositive

theorem not_isOrdinaryInteger_neg {x : Surreal.OmnificInteger.{u}} (hx : ¬ IsOrdinaryInteger x) :
    ¬ IsOrdinaryInteger (-x) := by
  intro h
  obtain ⟨z, hz⟩ := (isOrdinaryInteger_iff _).mp h
  apply hx
  rw [isOrdinaryInteger_iff]
  refine ⟨-z, ?_⟩
  rw [Int.cast_neg, ← hz, Subring.coe_neg, neg_neg]

theorem toSignedNonpositiveHahn_neg (x : Surreal.OmnificInteger.{u}) :
    (-x).toSignedNonpositiveHahn = -x.toSignedNonpositiveHahn := by
  apply Subtype.ext
  rw [coe_toSignedNonpositiveHahn, Subring.coe_neg, Surreal.toSignedFullHahnSeries_neg,
    ← coe_toSignedNonpositiveHahn]
  exact (Subring.coe_neg _ _).symm

theorem realIntegerSubring_mem_iff (r : ℝ) :
    r ∈ Surreal.realIntegerSubring ↔ ∃ z : ℤ, (z : ℝ) = r := by
  rw [Surreal.mem_realIntegerSubring]
  exact Iff.rfl

/-- An irreducible omnific integer that is not an ordinary integer is primal: it or its negative
is reduced (LM24, Proposition 8.2.5), and reduced nonordinary omnific integers are primal. -/
theorem isPrimal_of_irreducible_of_not_isOrdinaryInteger (x : Surreal.OmnificInteger.{u})
    (hirr : Irreducible x) (hx : ¬ IsOrdinaryInteger x) : IsPrimal x := by
  have hb : Irreducible (toSignedSmallSupportIntegerPart x) := by
    rw [← signedSmallSupportIntegerPartRingEquiv_apply]
    exact (MulEquiv.irreducible_iff (f := signedSmallSupportIntegerPartRingEquiv.{u})).mpr hirr
  have horder := boundedSignedHahn_order_ne_zero_of_not_isOrdinaryInteger x hx
  have himage : HahnSeries.CardSuppLTTruncationIntegerPart.toNonpositiveRingHom
      Surreal.realIntegerSubring (toSignedSmallSupportIntegerPart x) =
        x.toSignedNonpositiveHahn := by
    apply Subtype.ext
    rw [HahnSeries.CardSuppLTTruncationIntegerPart.coe_toNonpositiveRingHom,
      coe_toSignedNonpositiveHahn]
    exact coe_toSignedSmallSupportIntegerPart x
  rcases isReduced_or_isReduced_neg_of_irreducible Surreal.realIntegerSubring
    realIntegerSubring_mem_iff Surreal.archimedeanStrata hb horder with hred | hred
  · rw [himage] at hred
    exact isPrimal_of_isReduced x hx hred
  · rw [himage, ← toSignedNonpositiveHahn_neg] at hred
    have hneg := isPrimal_of_isReduced (-x) (not_isOrdinaryInteger_neg hx) hred
    have hx' : x = (-1) * (-x) := by rw [neg_one_mul, neg_neg]
    rw [hx']
    exact isUnit_neg_one.isPrimal.mul hneg

/-- An irreducible omnific integer that is not an ordinary integer is prime. -/
theorem prime_of_irreducible_of_not_isOrdinaryInteger (x : Surreal.OmnificInteger.{u})
    (hirr : Irreducible x) (hx : ¬ IsOrdinaryInteger x) : Prime x :=
  hirr.prime_of_isPrimal (isPrimal_of_irreducible_of_not_isOrdinaryInteger x hirr hx)

/-- An irreducible ordinary integer is prime in the omnific integers. -/
theorem prime_of_irreducible_of_isOrdinaryInteger (x : Surreal.OmnificInteger.{u})
    (hirr : Irreducible x) (hx : IsOrdinaryInteger x) : Prime x := by
  obtain ⟨z, hz⟩ := (isOrdinaryInteger_iff x).mp hx
  have hxz : x = (z : Surreal.OmnificInteger.{u}) := Subtype.ext (by rw [hz]; simp)
  rw [hxz] at hirr ⊢
  rw [← MulEquiv.prime_iff signedSmallSupportIntegerPartRingEquiv.{u}, map_intCast]
  have hirr' : Irreducible (z : SignedSmallSupportIntegerPart.{u}) := by
    rw [← map_intCast signedSmallSupportIntegerPartRingEquiv.{u}]
    exact (MulEquiv.irreducible_iff (f := signedSmallSupportIntegerPartRingEquiv.{u})).mpr hirr
  exact prime_intCast Surreal.realIntegerSubring realIntegerSubring_mem_iff
    (irreducible_iff_prime.mp
      (irreducible_int_of_irreducible_intCast Surreal.realIntegerSubring
        realIntegerSubring_mem_iff hirr'))

/-- **Every irreducible omnific integer is prime.** -/
@[blueprint "thm:omnific-factorisation"
  (phase := "Surreal numbers and omnific integers")
  (title := "Irreducible omnific integers are prime")
  (statement := /--
    Every irreducible element of $\mathbf{Oz}$ is prime in $\mathbf{Oz}$.
  -/)
  (proof := /--
  Let $x\in\mathbf{Oz}$ be irreducible.  If $x$ is not an ordinary integer, the
  factorisation at its leading Archimedean class shows that either $x$ or $-x$
  is reduced.  The reduced element is primal by
  \ref{thm:reduced-omnific-primal}; multiplication by $-1$ preserves primality,
  so $x$ is primal and hence prime.  If $x$ is an ordinary integer, its
  irreducibility in $\mathbf{Oz}$ makes the corresponding integer irreducible in
  $\mathbb Z$, hence a prime integer.  Divisibility of integer constants in
  $\mathbf{Oz}$ is detected by the ordinary integer constant coefficient, so
  $x$ is prime in $\mathbf{Oz}$ in this case as well.
  -/)]
theorem prime_of_irreducible (x : Surreal.OmnificInteger.{u}) (hirr : Irreducible x) : Prime x := by
  by_cases hx : IsOrdinaryInteger x
  · exact prime_of_irreducible_of_isOrdinaryInteger x hirr hx
  · exact prime_of_irreducible_of_not_isOrdinaryInteger x hirr hx

/-- Unique factorisation in the omnific integers: two factorisations of an omnific integer into
irreducibles agree up to order and units. -/
theorem factorization_unique {f g : Multiset Surreal.OmnificInteger.{u}}
    (hf : ∀ x ∈ f, Irreducible x) (hg : ∀ x ∈ g, Irreducible x)
    (hfg : Associated f.prod g.prod) :
    Multiset.Rel Associated f g :=
  prime_factors_unique (fun x hx ↦ prime_of_irreducible x (hf x hx))
    (fun x hx ↦ prime_of_irreducible x (hg x hx)) hfg

end Surreal.OmnificInteger
