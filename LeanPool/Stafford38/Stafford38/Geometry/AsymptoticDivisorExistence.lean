/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Geometry.ProjectiveDivisorOrderGap
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# A scheme-free boundary valuation for a nonconstant affine coordinate

The global asymptotic-conormal argument needs a boundary place at which the
distinguished affine coordinate tends to zero.  This file constructs that
place without projective schemes or normalization.

If `x` is transcendental over `k` in a field `K`, evaluation embeds the DVR
`k[X]_(X)` in `K`; its parameter maps to `x`.  This already produces the
strict order gap for the rational projective pair `[x:x²]`.  Independently,
Zorn's theorem extends the local map to a valuation subring of all of `K`,
which contains `x` in its maximal ideal and excludes `x⁻¹`.

The exact remaining commutative-algebra input is a *discrete extension* of
this place to the finitely generated function field: a discrete valuation
subring of `K` centred at `x=0`.  Mathlib has the unrestricted valuation-ring
extension and the source DVR, but no theorem preserving rank one/discreteness
under the extension (nor the equivalent normalization/height-one-prime
construction).
-/

namespace Stafford38.Geometry.AsymptoticDivisorExistence

open IsLocalRing
open Polynomial

noncomputable section

universe u v

variable (k : Type u) [Field k]

/-- Over an algebraically closed ground field, "nonconstant" is exactly the
input needed below: an element outside the scalar image is transcendental. -/
theorem transcendental_of_not_mem_range_algebraMap
    {K : Type v} [Field K] [Algebra k K] [IsAlgClosed k]
    {x : K} (hx : x ∉ Set.range (algebraMap k K)) :
    Transcendental k x := by
  change ¬IsAlgebraic k x
  intro halg
  let L : IntermediateField k K := IntermediateField.adjoin k {x}
  let : Algebra.IsAlgebraic k L :=
    IntermediateField.isAlgebraic_adjoin (K := k) (L := K) (S := {x}) (by
      intro y hy
      simpa only [Set.mem_singleton_iff] using hy ▸ halg.isIntegral)
  have hL : L = ⊥ :=
    IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic L
  apply hx
  rw [← IntermediateField.mem_bot, ← hL]
  exact IntermediateField.subset_adjoin k {x} (Set.mem_singleton x)

/-- The prime ideal `(X)` in the one-variable polynomial ring. -/
def coordinateZeroPrime : Ideal (Polynomial k) := Ideal.span {Polynomial.X}

instance coordinateZeroPrime_isPrime : (coordinateZeroPrime k).IsPrime := by
  exact (Ideal.span_singleton_prime Polynomial.X_ne_zero).2 Polynomial.prime_X

/-- The local ring of the affine line at the origin. -/
abbrev CoordinateZeroLocalRing := Localization.AtPrime (coordinateZeroPrime k)

instance coordinateZeroLocalRing_isDomain : IsDomain (CoordinateZeroLocalRing k) :=
  inferInstance

instance coordinateZeroLocalRingSMul : SMul k (CoordinateZeroLocalRing k) :=
  Algebra.toSMul

instance coordinateZeroLocalRing_isDiscreteValuationRing :
    IsDiscreteValuationRing (CoordinateZeroLocalRing k) := by
  apply IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
    (Polynomial k) (P := coordinateZeroPrime k)
  · rw [coordinateZeroPrime, ne_eq, Ideal.span_singleton_eq_bot]
    exact Polynomial.X_ne_zero

/-- Evaluation at a transcendental element extends from `k[X]` to the local
ring at `(X)`, because every polynomial outside `(X)` is nonzero and hence a
unit in the ambient field. -/
def coordinateZeroLocalMap
    {K : Type v} [Field K] [Algebra k K]
    (x : K) (hx : Transcendental k x) :
    CoordinateZeroLocalRing k →+* K :=
  IsLocalization.lift (S := CoordinateZeroLocalRing k)
    (M := (coordinateZeroPrime k).primeCompl)
    (g := (Polynomial.aeval x).toRingHom) fun y ↦ by
      rw [isUnit_iff_ne_zero]
      intro hy
      have hy0 : (y : Polynomial k) = 0 := by
        apply transcendental_iff_injective.mp hx
        simpa using hy
      exact y.2 (hy0 ▸ (coordinateZeroPrime k).zero_mem)

@[simp]
theorem coordinateZeroLocalMap_algebraMap_X
    {K : Type v} [Field K] [Algebra k K]
    (x : K) (hx : Transcendental k x) :
    coordinateZeroLocalMap k x hx
        (algebraMap k[X] (CoordinateZeroLocalRing k) Polynomial.X) = x := by
  rw [coordinateZeroLocalMap, IsLocalization.lift_eq]
  exact Polynomial.aeval_X x

/-- The coordinate-zero DVR map is an embedding, not merely a place with a
kernel.  Thus the remaining problem is extension of this discrete valuation,
not repair of the source local model. -/
theorem coordinateZeroLocalMap_injective
    {K : Type v} [Field K] [Algebra k K]
    (x : K) (hx : Transcendental k x) :
    Function.Injective (coordinateZeroLocalMap k x hx) := by
  rw [coordinateZeroLocalMap, IsLocalization.lift_injective_iff]
  intro a b
  have hloc := IsLocalization.injective (CoordinateZeroLocalRing k)
    (coordinateZeroPrime k).primeCompl_le_nonZeroDivisors
  have heval := transcendental_iff_injective.mp hx
  constructor
  · intro hab
    exact congrArg (Polynomial.aeval x) (hloc hab)
  · intro hab
    exact congrArg (algebraMap (Polynomial k) (CoordinateZeroLocalRing k))
      (heval hab)

/-- The local line at `x = 0` is already a DVR and maps to the ambient
function field.  Consequently the rational projective pair `[x:x²]` has the
strict order gap required by `ProjectiveDivisorOrderGap`, unconditionally.

This is a genuine rank-one discrete producer, stronger than the Zorn
valuation below.  It does not yet contain the remaining affine coordinates;
extending this DVR place to the whole finitely generated function field while
retaining discreteness is the named residual theorem. -/
theorem exists_coordinateZeroDVR_projectiveOrderGap
    {K : Type v} [Field K] [Algebra k K]
    (x : K) (hx : Transcendental k x) :
    let R := CoordinateZeroLocalRing k
    let q : R := algebraMap (Polynomial k) R Polynomial.X
    ∃ (uniformizer : R) (a r b : ℕ) (u₀ ur u₁ : Rˣ),
      coordinateZeroLocalMap k x hx q = x ∧
      Irreducible uniformizer ∧
      0 < a ∧ 0 < r ∧ b = a + r ∧ a < b ∧
      q = (u₀ : R) * uniformizer ^ a ∧
      q = (ur : R) * uniformizer ^ r ∧
      u₁ = u₀ * ur ∧
      q * q = (u₁ : R) * uniformizer ^ b := by
  let R := CoordinateZeroLocalRing k
  let q : R := algebraMap (Polynomial k) R Polynomial.X
  have hq_ne : q ≠ 0 := by
    intro hq
    apply Polynomial.X_ne_zero (R := k)
    apply IsLocalization.injective R
      (coordinateZeroPrime k).primeCompl_le_nonZeroDivisors
    simpa only [q, map_zero] using hq
  have hq_vanish : q ∈ maximalIdeal R := by
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff
      R (coordinateZeroPrime k) Polynomial.X).2
        (Ideal.mem_span_singleton_self Polynomial.X)
  obtain ⟨uniformizer, huniformizer⟩ :=
    IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨a, r, b, u₀, ur, u₁, ha, hr, hb, hab,
      hq₀, hratio, hu₁, hq₁⟩ :=
    ProjectiveDivisorOrderGap.exists_uniformizer_strict_orderGap
      uniformizer huniformizer q q (q * q)
      hq_ne hq_ne hq_vanish hq_vanish rfl
  exact ⟨uniformizer, a, r, b, u₀, ur, u₁,
    coordinateZeroLocalMap_algebraMap_X k x hx, huniformizer,
    ha, hr, hb, hab, hq₀, hratio, hu₁, hq₁⟩

/-- The complete scheme-free boundary-place package: a valuation subring of
the ambient function field together with a *local* factorization of
`k[X]_(X) → K`.  Locality records that the centre really lies over `(X)`;
`factor_commutes` records that no abstract replacement of the coordinate map
has been made. -/
structure BoundaryValuationData
    {K : Type v} [Field K] [Algebra k K]
    (x : K) (hx : Transcendental k x) where
  /-- The valuation subring supporting the local factorization at coordinate zero. -/
  valuation : ValuationSubring K
  /-- The local map from the coordinate-zero local ring into the selected valuation ring. -/
  factor : CoordinateZeroLocalRing k →+* valuation.toSubring
  factor_isLocal : IsLocalHom factor
  factor_commutes :
    valuation.toSubring.subtype.comp factor = coordinateZeroLocalMap k x hx

/-- The exact divisorial refinement missing from the library.  Unlike
`BoundaryValuationData`, this package asks that the valuation ring be a DVR.
It is deliberately only a data structure: this file does not postulate that
such a refinement exists.

The classical missing theorem is:

*Divisorial valuation extension.*  If `K/k` is a finitely generated function
field and `x ∈ K` is nonconstant, then there is a discrete valuation subring
of `K` in whose maximal ideal `x` lies.

For the Stafford application `x` is also a unit of the affine coordinate
domain, so this centre is necessarily on the boundary. -/
structure DiscreteBoundaryRefinement
    {K : Type v} [Field K] [Algebra k K]
    (x : K) where
  /-- The discrete valuation subring realizing the boundary refinement. -/
  valuation : ValuationSubring K
  isDiscrete : IsDiscreteValuationRing valuation.toSubring
  /-- The specified nonzero coordinate as a nonunit of the discrete valuation ring. -/
  coordinate : valuation.toSubring
  coordinate_eq : (coordinate : K) = x
  coordinate_ne : coordinate ≠ 0
  coordinate_nonunit : ¬IsUnit coordinate

/-- Zorn's valuation-ring theorem produces the complete local factorization
of the coordinate-zero local ring inside the function field. -/
theorem exists_boundaryValuationData
    {K : Type v} [Field K] [Algebra k K]
    (x : K) (hx : Transcendental k x) :
    Nonempty (BoundaryValuationData k x hx) := by
  let f := coordinateZeroLocalMap k x hx
  obtain ⟨V, hV, hlocal⟩ := IsLocalRing.exists_factor_valuationRing f
  exact ⟨{
    valuation := V
    factor := f.codRestrict V.toSubring hV
    factor_isLocal := hlocal
    factor_commutes := rfl
  }⟩

/-- A genuine discrete boundary refinement feeds the already formalized DVR
order-gap theorem with no further geometry hidden in the implication.

The rational projective pair is `[q₀:q₁]=[x:x²]`; its affine ratio is `x`.
At the discrete boundary both `q₀` and the ratio vanish, so their orders are
  strictly separated.  This is the exact handoff from a full-function-field
discrete refinement; existence of that refinement is the missing theorem. -/
theorem exists_projectiveOrderGap_of_discreteBoundaryRefinement
    {K : Type v} [Field K] [Algebra k K]
    (x : K) (D : DiscreteBoundaryRefinement k x) :
    let R := D.valuation.toSubring
    ∃ (uniformizer : R) (a r b : ℕ) (u₀ ur u₁ : Rˣ),
      Irreducible uniformizer ∧
      0 < a ∧ 0 < r ∧ b = a + r ∧ a < b ∧
      D.coordinate = (u₀ : R) * uniformizer ^ a ∧
      D.coordinate = (ur : R) * uniformizer ^ r ∧
      u₁ = u₀ * ur ∧
      D.coordinate * D.coordinate = (u₁ : R) * uniformizer ^ b := by
  let R := D.valuation.toSubring
  let : IsDiscreteValuationRing R := D.isDiscrete
  obtain ⟨uniformizer, huniformizer⟩ :=
    IsDiscreteValuationRing.exists_irreducible R
  have hvanish : D.coordinate ∈ maximalIdeal R := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact D.coordinate_nonunit
  obtain ⟨a, r, b, u₀, ur, u₁, ha, hr, hb, hab,
      hq₀, hratio, hu₁, hq₁⟩ :=
    ProjectiveDivisorOrderGap.exists_uniformizer_strict_orderGap
      uniformizer huniformizer
      D.coordinate D.coordinate (D.coordinate * D.coordinate)
      D.coordinate_ne D.coordinate_ne hvanish hvanish rfl
  exact ⟨uniformizer, a, r, b, u₀, ur, u₁, huniformizer,
    ha, hr, hb, hab, hq₀, hratio, hu₁, hq₁⟩

/-- A nonconstant coordinate has a scheme-free boundary valuation.

The valuation subring is obtained by dominating `k[X]_(X)` inside `K`.
The first conclusion says that the chosen coordinate lies at the centre;
the second says its inverse has a pole there. -/
theorem exists_boundaryValuationSubring
    {K : Type v} [Field K] [Algebra k K]
    (x : K) (hx : Transcendental k x) :
    ∃ V : ValuationSubring K,
      ∃ xV : V.toSubring,
        (xV : K) = x ∧
        x⁻¹ ∉ V ∧
        ¬IsUnit xV := by
  let R := CoordinateZeroLocalRing k
  let f : R →+* K := coordinateZeroLocalMap k x hx
  obtain ⟨D⟩ := exists_boundaryValuationData k x hx
  let V := D.valuation
  let fV : R →+* V.toSubring := D.factor
  let hlocalV : IsLocalHom fV := D.factor_isLocal
  let xR : R := algebraMap k[X] R Polynomial.X
  have hxR : xR ∈ maximalIdeal R := by
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff
      R (coordinateZeroPrime k) Polynomial.X).2
        (Ideal.mem_span_singleton_self Polynomial.X)
  have hfx : f xR = x := by
    exact coordinateZeroLocalMap_algebraMap_X k x hx
  let xV : V.toSubring := fV xR
  have hxV : (xV : K) = x := by
    have hcomm := D.factor_commutes
    have := DFunLike.congr_fun hcomm xR
    exact this.trans hfx
  have hxR_nonunit : ¬IsUnit xR := mem_nonunits_iff.mp hxR
  have hxnonunit : ¬IsUnit xV := by
    intro hu
    apply hxR_nonunit
    exact @IsLocalHom.map_nonunit _ _ _ _ _ _ fV hlocalV xR hu
  have hxinv : x⁻¹ ∉ V := by
    intro hxinvV
    have hxunit : IsUnit xV := by
      apply isUnit_iff_exists_inv.mpr
      refine ⟨⟨x⁻¹, hxinvV⟩, ?_⟩
      apply Subtype.ext
      change (xV : K) * x⁻¹ = (1 : K)
      rw [hxV]
      exact mul_inv_cancel₀ (by
        intro hx0
        apply hx
        simpa [hx0] using (isAlgebraic_zero : IsAlgebraic k (0 : K)))
    exact hxnonunit hxunit
  exact ⟨V, xV, hxV, hxinv, hxnonunit⟩

/-- Algebraically closed form: a nonconstant coordinate directly produces
the boundary valuation, with no separately supplied transcendence proof. -/
theorem exists_boundaryValuationSubring_of_nonconstant
    {K : Type v} [Field K] [Algebra k K] [IsAlgClosed k]
    (x : K) (hx : x ∉ Set.range (algebraMap k K)) :
    ∃ V : ValuationSubring K,
      ∃ xV : V.toSubring,
        (xV : K) = x ∧
        x⁻¹ ∉ V ∧
        ¬IsUnit xV :=
  exists_boundaryValuationSubring k x
    (transcendental_of_not_mem_range_algebraMap k hx)

/-- Coordinate-ring form of the construction.  If an affine coordinate is
a unit (the algebraic meaning of avoiding its zero hyperplane) and remains
nonconstant in a function field, then there is a boundary valuation which
contains the coordinate but excludes the image of its *regular inverse*.

For a prime affine ideal one applies this to its quotient domain and its
fraction field; the unit is supplied by `I + (x) = ⊤`. -/
theorem exists_boundaryValuationSubring_of_affineUnit
    [IsAlgClosed k]
    {A : Type*} [CommRing A] [Algebra k A]
    {K : Type v} [Field K] [Algebra k K]
    (ι : A →ₐ[k] K) (u : Aˣ)
    (hu : ι (u : A) ∉ Set.range (algebraMap k K)) :
    ∃ V : ValuationSubring K,
      ∃ xV : V.toSubring,
        (xV : K) = ι (u : A) ∧
        ι (u⁻¹ : Aˣ) ∉ V ∧
        ¬IsUnit xV := by
  obtain ⟨V, xV, hxV, hxinv, hxnonunit⟩ :=
    exists_boundaryValuationSubring_of_nonconstant k (ι (u : A)) hu
  refine ⟨V, xV, hxV, ?_, hxnonunit⟩
  have hprod : ι (u : A) * ι (u⁻¹ : Aˣ) = 1 := by
    rw [← map_mul]
    simp
  have hinv : ι (u⁻¹ : Aˣ) = (ι (u : A))⁻¹ :=
    eq_inv_of_mul_eq_one_right hprod
  rw [hinv]
  exact hxinv


end

end Stafford38.Geometry.AsymptoticDivisorExistence
