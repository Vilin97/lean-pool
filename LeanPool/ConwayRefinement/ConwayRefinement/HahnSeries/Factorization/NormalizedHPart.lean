/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupportConstantTermOne
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.RealSupportSupremum

import Mathlib.Algebra.GroupWithZero.Divisibility
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Monomial

/-!
# Normalized finite-support part over an exponent subgroup

LM24, Lemma 6.5.2 associates to a nonzero finite-support real-exponent series `p` a unique
series `p_H` in `1 + K(H^{< 0})`. The defining property is intrinsic: every normalized
finite-support `H`-series divides `p` after exponent-domain extension exactly when it divides
`p_H` over `H`.

This file freezes that property and its uniqueness proposition without choosing a factorisation
of `p`. The full existence theorem depends on the Ritt factorisation and greatest-common-divisor
prerequisites used in the paper; no such prerequisite is hidden in the definition. The identity
case is proved completely as a semantic boundary check.
-/

open scoped HahnSeries

universe v

public noncomputable section

namespace HahnSeries.Nonpositive

variable (H : AddSubgroup ℝ) {K : Type v} [Field K]

/-- The finite-support exponent-domain embedding induced by `H ⊆ ℝ`. -/
def finiteSupportToReal :
    FiniteSupportRing (G := H) (K := K) →+*
      FiniteSupportRing (G := ℝ) (K := K) :=
  mapDomainFiniteSupport H.subtype Subtype.val_injective fun _ _ ↦ Iff.rfl

/-- The underlying nonpositive series of `finiteSupportToReal` is `mapDomainToReal`. -/
@[simp]
theorem coe_finiteSupportToReal
    (p : FiniteSupportRing (G := H) (K := K)) :
    ((finiteSupportToReal H p : FiniteSupportRing (G := ℝ) (K := K)) :
        Nonpositive ℝ K) = mapDomainToReal H (p : Nonpositive H K) :=
  by
    apply Subtype.ext
    rw [finiteSupportToReal, coe_mapDomainFiniteSupport,
      coe_mapDomainToReal, coe_mapDomain]

/-- A normalized finite-support `H`-series is the normalized `H`-part of `p` when it has exactly
the same normalized `H`-divisors as `p` has after exponent-domain extension. -/
def IsNormalizedHPart
    (p : FiniteSupportRing (G := ℝ) (K := K))
    (q : ConstantTermOneFiniteSupport (G := H) (K := K)) : Prop :=
  ∀ r : ConstantTermOneFiniteSupport (G := H) (K := K),
    finiteSupportToReal H
        (r : FiniteSupportRing (G := H) (K := K)) ∣ p ↔
      (r : FiniteSupportRing (G := H) (K := K)) ∣
        (q : FiniteSupportRing (G := H) (K := K))

/-- Characterization of the normalized `H`-part property by divisibility. -/
theorem isNormalizedHPart_iff
    (p : FiniteSupportRing (G := ℝ) (K := K))
    (q : ConstantTermOneFiniteSupport (G := H) (K := K)) :
    IsNormalizedHPart H p q ↔
      ∀ r : ConstantTermOneFiniteSupport (G := H) (K := K),
        finiteSupportToReal H
            (r : FiniteSupportRing (G := H) (K := K)) ∣ p ↔
          (r : FiniteSupportRing (G := H) (K := K)) ∣
            (q : FiniteSupportRing (G := H) (K := K)) :=
  Iff.rfl

/-- Existence and uniqueness of a normalized `H`-part for a finite-support real series. -/
def HasUniqueNormalizedHPart
    (p : FiniteSupportRing (G := ℝ) (K := K)) : Prop :=
  ∃! q : ConstantTermOneFiniteSupport (G := H) (K := K),
    IsNormalizedHPart H p q

/-- Two normalized `H`-parts of the same finite-support real series are equal. Thus the
uniqueness clause in LM24, Lemma 6.5.2 follows from the intrinsic divisibility property alone. -/
theorem IsNormalizedHPart.eq
    {p : FiniteSupportRing (G := ℝ) (K := K)}
    {q q' : ConstantTermOneFiniteSupport (G := H) (K := K)}
    (hq : IsNormalizedHPart H p q) (hq' : IsNormalizedHPart H p q') : q = q' := by
  have hqDvdQ' :
      (q : FiniteSupportRing (G := H) (K := K)) ∣
        (q' : FiniteSupportRing (G := H) (K := K)) :=
    (hq' q).mp ((hq q).mpr dvd_rfl)
  have hq'DvdQ :
      (q' : FiniteSupportRing (G := H) (K := K)) ∣
        (q : FiniteSupportRing (G := H) (K := K)) :=
    (hq q').mp ((hq' q').mpr dvd_rfl)
  obtain ⟨u, hu⟩ := associated_of_dvd_dvd hqDvdQ' hq'DvdQ
  have huUnit : IsUnit
      (((u : FiniteSupportRing (G := H) (K := K)) : Nonpositive H K)) :=
    u.isUnit.map (finiteSupportSubring (G := H) (K := K)).subtype
  have huConstant : constantCoeff
      (((u : FiniteSupportRing (G := H) (K := K)) : Nonpositive H K)) = 1 := by
    have hconstant := congrArg
      (fun r : FiniteSupportRing (G := H) (K := K) ↦
        constantCoeff (r : Nonpositive H K)) hu
    simpa only [Subring.coe_mul, map_mul, q.constantCoeff_eq_one,
      q'.constantCoeff_eq_one, one_mul] using hconstant
  have huOne : (u : FiniteSupportRing (G := H) (K := K)) = 1 := by
    apply Subtype.ext
    exact eq_one_of_isUnit_of_constantCoeff_eq_one huUnit huConstant
  apply Subtype.ext
  simpa only [huOne, mul_one] using hu

/-- For the normalized `H`-part property, existence already implies unique existence. -/
theorem hasUniqueNormalizedHPart_iff_exists
    (p : FiniteSupportRing (G := ℝ) (K := K)) :
    HasUniqueNormalizedHPart H p ↔
      ∃ q : ConstantTermOneFiniteSupport (G := H) (K := K),
        IsNormalizedHPart H p q := by
  constructor
  · rintro ⟨q, hq, _⟩
    exact ⟨q, hq⟩
  · rintro ⟨q, hq⟩
    exact ⟨q, hq, fun _ hq' ↦ hq'.eq H hq⟩

/-- A normalized series whose real-domain image divides one is itself one. -/
theorem ConstantTermOneFiniteSupport.eq_one_of_finiteSupportToReal_dvd_one
    (r : ConstantTermOneFiniteSupport (G := H) (K := K))
    (hr : finiteSupportToReal H
      (r : FiniteSupportRing (G := H) (K := K)) ∣ 1) : r = 1 := by
  have hrUnitFinite : IsUnit (finiteSupportToReal H
      (r : FiniteSupportRing (G := H) (K := K))) :=
    isUnit_iff_dvd_one.mpr hr
  have hrUnit : IsUnit (mapDomainToReal H
      ((r : FiniteSupportRing (G := H) (K := K)) : Nonpositive H K)) := by
    rw [← coe_finiteSupportToReal]
    exact hrUnitFinite.map
      (finiteSupportSubring (G := ℝ) (K := K)).subtype
  have hrConstant : constantCoeff (mapDomainToReal H
      ((r : FiniteSupportRing (G := H) (K := K)) : Nonpositive H K)) = 1 := by
    rw [constantCoeff_mapDomainToReal]
    exact r.constantCoeff_eq_one
  have hrImageEq : mapDomainToReal H
      ((r : FiniteSupportRing (G := H) (K := K)) : Nonpositive H K) = 1 :=
    eq_one_of_isUnit_of_constantCoeff_eq_one hrUnit hrConstant
  apply Subtype.ext
  apply Subtype.ext
  exact mapDomainToReal_injective H (by simpa using hrImageEq)

/-- The multiplicative identity is its own normalized `H`-part. -/
theorem one_isNormalizedHPart :
    IsNormalizedHPart H
      (1 : FiniteSupportRing (G := ℝ) (K := K))
      (1 : ConstantTermOneFiniteSupport (G := H) (K := K)) := by
  intro r
  constructor
  · intro hr
    rw [r.eq_one_of_finiteSupportToReal_dvd_one H hr]
  · intro hr
    simpa using (finiteSupportToReal H).map_dvd hr

/-- The identity has a unique normalized `H`-part, namely itself. -/
theorem existsUnique_normalizedHPart_one :
    ∃! q : ConstantTermOneFiniteSupport (G := H) (K := K),
      IsNormalizedHPart H
        (1 : FiniteSupportRing (G := ℝ) (K := K)) q := by
  refine ⟨1, one_isNormalizedHPart H, ?_⟩
  intro q hq
  apply q.eq_one_of_finiteSupportToReal_dvd_one H
  exact (hq q).mpr (dvd_refl _)

end HahnSeries.Nonpositive
