/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.PolynomialAlgebra.InitialForms
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrderType
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.Statements.SeriesPrimality
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.Prime.Defs

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.DegreeValuation
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Statements.ProductValue
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Polynomial presentations of the series ring and primality

Let `K((ℝ^{≤0}))` be the series ring, `K_fin = K(ℝ^{≤0})` its series with finite support, and
`L = Frac(K_fin)`. The argument of this file is stated for a *polynomial presentation*
(`IsPolynomialPresentation`) of a `K_fin`-subalgebra `K_fin[b_i : i ∈ ι]` of `K((ℝ^{≤0}))`:
evaluation `K_fin[X_i] → K((ℝ^{≤0})))`, `X_i ↦ b_i`, is injective, a polynomial whose value has
degree at most zero is a constant, and the subalgebra is saturated under the nonzero scalars of
`K_fin`. An irreducible `a = F(b) ∈ K((ℝ^{≤0}))` with `0 < deg a` then generates a prime ideal of
`K_fin[X_i]`:

* a finite-support divisor of `a` is a unit, since its cofactor would otherwise be a unit and
  force `deg a = 0`;
* `F` is irreducible in `L[X_i]`: a factorisation is cleared of denominators, the finite-support
  denominator is primal in `K((ℝ^{≤0}))` with finite-support factors, and the degree formula
  forces one factor to be a constant;
* `D = K_fin[X_i]/(F)` embeds in `L[X_i]/(F)`, by the same clearing of denominators together with
  the saturation of the presented subalgebra;
* `L[X_i]` is a unique factorisation domain, so `L[X_i]/(F)` and hence `D` are domains.

The presentation used is that of the whole series ring by the lifts of a minimal system of
homogeneous generators of `P̂` (`Berarducci.PolynomialRing`), which rests on the polynomiality
of `P̂`; the primality of every series follows (`Berarducci.Primality`).
-/

open HahnSeries HahnSeries.Nonpositive Berarducci
open scoped TensorProduct MaxAddDegree

universe v w

public noncomputable section

namespace Berarducci

variable {K : Type v} [Field K] [CharZero K]

/-! ### Degrees of divisors and units -/

/-- The degree of a divisor of a nonzero series is at most the degree of the series. -/
theorem seriesDegree_le_of_dvd {a c : Nonpositive ℝ K} (hdvd : c ∣ a) (ha : a ≠ 0) :
    degreeValuation K c ≤ degreeValuation K a := by
  obtain ⟨d, rfl⟩ := hdvd
  have hd : d ≠ 0 := fun h ↦ ha (by rw [h, mul_zero])
  rw [(degreeValuation K).map_mul]
  calc degreeValuation K c = degreeValuation K c + 0 := (add_zero _).symm
    _ ≤ degreeValuation K c + degreeValuation K d :=
        add_le_add le_rfl ((degreeValuation K).zero_le_degree (degreeValuation_isSeparated K)
          (fun _ ↦ bot_le) hd)

/-- A unit of the series ring has degree zero. -/
theorem seriesDegree_eq_zero_of_isUnit {b : Nonpositive ℝ K} (hb : IsUnit b) :
    degreeValuation K b = 0 := by
  rw [degreeValuation_apply, degree_eq_zero_of_isUnit degree_mul hb]

/-- A divisor of degree at most zero of an irreducible series of positive degree is a unit. -/
theorem isUnit_of_dvd_of_seriesDegree_le_zero {a u : Nonpositive ℝ K} (ha : Irreducible a)
    (haDegree : 0 < degreeValuation K a) (hu : degreeValuation K u ≤ 0) (hdvd : u ∣ a) :
    IsUnit u := by
  obtain ⟨w, rfl⟩ := hdvd
  rcases ha.isUnit_or_isUnit rfl with h | h
  · exact h
  · exfalso
    rw [(degreeValuation K).map_mul,
      seriesDegree_eq_zero_of_isUnit h, add_zero] at haDegree
    exact absurd (lt_of_lt_of_le haDegree hu) (lt_irrefl _)

/-! ### Clearing denominators -/

/-- The fraction field `L = Frac(K_fin)` of the finite-support series. -/
abbrev FiniteSupportFractionField : Type v :=
  FractionRing (Berarducci.FiniteSupportRing (K := K))

variable {ι : Type w}

variable (K ι) in
/-- Extension of coefficients `K_fin[X_i] → L[X_i]`. -/
abbrev coordinatePolynomialMap :
    MvPolynomial ι (Berarducci.FiniteSupportRing (K := K)) →+*
      MvPolynomial ι (FiniteSupportFractionField (K := K)) :=
  MvPolynomial.map (algebraMap (Berarducci.FiniteSupportRing (K := K))
    (FiniteSupportFractionField (K := K)))

omit [CharZero K] in
variable (K ι) in
/-- Extension of coefficients to the fraction field is injective. -/
theorem coordinatePolynomialMap_injective :
    Function.Injective (coordinatePolynomialMap K ι) :=
  MvPolynomial.map_injective _ (IsFractionRing.injective _ _)

omit [CharZero K] in
/-- Every polynomial over `L` becomes a polynomial over `K_fin` after multiplication by a nonzero
finite-support denominator. -/
theorem exists_C_mul_eq_coordinatePolynomialMap
    (q : MvPolynomial ι (FiniteSupportFractionField (K := K))) :
    ∃ (u : Berarducci.FiniteSupportRing (K := K))
      (h : MvPolynomial ι (Berarducci.FiniteSupportRing (K := K))),
      u ≠ 0 ∧ MvPolynomial.C (algebraMap (Berarducci.FiniteSupportRing (K := K))
        (FiniteSupportFractionField (K := K)) u) * q = coordinatePolynomialMap K ι h := by
  let := MvPolynomial.algebraMvPolynomial (σ := ι)
    (R := Berarducci.FiniteSupportRing (K := K)) (S := FiniteSupportFractionField (K := K))
  obtain ⟨⟨h, m⟩, hm⟩ := IsLocalization.surj
    ((nonZeroDivisors (Berarducci.FiniteSupportRing (K := K))).map
      (MvPolynomial.C (σ := ι))) q
  obtain ⟨u, hu, hum⟩ := Submonoid.mem_map.mp m.2
  refine ⟨u, h, nonZeroDivisors.ne_zero hu, ?_⟩
  simp only at hm
  rw [MvPolynomial.algebraMap_def, ← hum, MvPolynomial.map_C, mul_comm] at hm
  exact hm

/-! ### Polynomial presentations -/

omit [CharZero K] in
/-- A constant `c ∈ K_fin` evaluates to itself under `K_fin[X_i] → K((ℝ^{≤0}))`. -/
theorem aeval_C_finiteSupport (b : ι → Nonpositive ℝ K)
    (c : Berarducci.FiniteSupportRing (K := K)) :
    MvPolynomial.aeval b (MvPolynomial.C c) = (c : Nonpositive ℝ K) :=
  MvPolynomial.aeval_C _ _

/-- A family `b : ι → K((ℝ^{≤0}))` is a *polynomial presentation* of the `K_fin`-subalgebra
`K_fin[b_i : i ∈ ι]` it generates: evaluation `K_fin[X_i] → K((ℝ^{≤0}))`, `X_i ↦ b_i`, is
injective, a polynomial whose value has degree at most zero is a constant, and the subalgebra is
saturated under the nonzero scalars of `K_fin`: if `u t ∈ K_fin[b_i]` with `0 ≠ u ∈ K_fin`, then
`t ∈ K_fin[b_i]`. The paper's presentation `S = K_fin[b_B : B ∈ 𝓑]` of the ring of series of
finite degree is one, and so is any presentation of the whole series ring. -/
structure IsPolynomialPresentation (b : ι → Nonpositive ℝ K) : Prop where
  /-- Evaluation `F ↦ F(b)` is injective. -/
  injective : Function.Injective (MvPolynomial.aeval b : MvPolynomial ι
    (Berarducci.FiniteSupportRing (K := K)) →ₐ[Berarducci.FiniteSupportRing (K := K)]
      Nonpositive ℝ K)
  /-- A polynomial whose value has degree at most zero is a constant. -/
  eq_C_of_degree_le_zero : ∀ G : MvPolynomial ι (Berarducci.FiniteSupportRing (K := K)),
    degreeValuation K (MvPolynomial.aeval b G) ≤ 0 → G = MvPolynomial.C (G.coeff 0)
  /-- `K_fin[b_i]` is saturated under the nonzero scalars of `K_fin`. -/
  mem_range_of_mul_mem_range : ∀ (u : Berarducci.FiniteSupportRing (K := K)) (t : Nonpositive ℝ K),
    u ≠ 0 → (u : Nonpositive ℝ K) * t ∈ (MvPolynomial.aeval b : MvPolynomial ι
      (Berarducci.FiniteSupportRing (K := K)) →ₐ[Berarducci.FiniteSupportRing (K := K)]
        Nonpositive ℝ K).range →
      t ∈ (MvPolynomial.aeval b : MvPolynomial ι
        (Berarducci.FiniteSupportRing (K := K)) →ₐ[Berarducci.FiniteSupportRing (K := K)]
          Nonpositive ℝ K).range

namespace IsPolynomialPresentation

variable {b : ι → Nonpositive ℝ K} (hb : IsPolynomialPresentation b)
include hb

/-! ### Constant polynomials -/

omit [CharZero K] in
/-- If a nonzero finite-support multiple of `G ∈ L[X_i]` comes from a polynomial over `K_fin`
whose value has degree at most zero, and `G ≠ 0`, then `G` is a unit of `L[X_i]`. -/
theorem isUnit_of_C_mul_eq_coordinatePolynomialMap
    {u : Berarducci.FiniteSupportRing (K := K)} (hu : u ≠ 0)
    {G : MvPolynomial ι (FiniteSupportFractionField (K := K))} (hG : G ≠ 0)
    {G' : MvPolynomial ι (Berarducci.FiniteSupportRing (K := K))}
    (hGG' : MvPolynomial.C (algebraMap (Berarducci.FiniteSupportRing (K := K))
      (FiniteSupportFractionField (K := K)) u) * G = coordinatePolynomialMap K ι G')
    (hdeg : degreeValuation K (MvPolynomial.aeval b G') ≤ 0) : IsUnit G := by
  rw [hb.eq_C_of_degree_le_zero G' hdeg, coordinatePolynomialMap, MvPolynomial.map_C] at hGG'
  have hc : G'.coeff 0 ≠ 0 := by
    intro hc
    rw [hc, map_zero, MvPolynomial.C_0, mul_eq_zero, MvPolynomial.C_eq_zero,
      map_eq_zero_iff _ (IsFractionRing.injective _ _)] at hGG'
    exact hGG'.elim hu hG
  have hunit : IsUnit (MvPolynomial.C (algebraMap (Berarducci.FiniteSupportRing (K := K))
      (FiniteSupportFractionField (K := K)) (G'.coeff 0)) :
        MvPolynomial ι (FiniteSupportFractionField (K := K))) :=
    (isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hc)).map
      MvPolynomial.C
  rw [← hGG'] at hunit
  exact isUnit_of_mul_isUnit_right hunit

omit hb in
/-- The image of a degree-zero finite-support factor times a unit has degree at most zero. -/
private theorem seriesDegree_le_zero_of_eq_mul {w u₁ g₁ : Nonpositive ℝ K}
    (hw : w = u₁ * g₁) {d : Nonpositive ℝ K} (hd : d ≠ 0) (hd0 : degreeValuation K d = 0)
    (hu₁ : u₁ ∣ d) (hg₁ : IsUnit g₁) : degreeValuation K w ≤ 0 := by
  rw [hw, (degreeValuation K).map_mul,
    seriesDegree_eq_zero_of_isUnit hg₁, add_zero, ← hd0]
  exact seriesDegree_le_of_dvd hu₁ hd

/-! ### Irreducibility over the fraction field -/

/-- If `F(b)` is irreducible of positive degree, then `F` is irreducible in `L[X_i]`. -/
theorem irreducible_coordinatePolynomialMap_of_irreducible_aeval
    {F : MvPolynomial ι (Berarducci.FiniteSupportRing (K := K))}
    (ha : Irreducible (MvPolynomial.aeval b F))
    (haDegree : 0 < degreeValuation K (MvPolynomial.aeval b F)) :
    Irreducible (coordinatePolynomialMap K ι F) := by
  have hinj := coordinatePolynomialMap_injective K ι
  have hF0 : F ≠ 0 := fun h ↦ ha.ne_zero (by rw [h, map_zero])
  refine ⟨fun hunit ↦ ?_, fun G H hGH ↦ ?_⟩
  · -- a unit would make `a` divide a finite-support series
    obtain ⟨G, hG⟩ := hunit.exists_right_inv
    obtain ⟨v, h, hv, hvh⟩ := exists_C_mul_eq_coordinatePolynomialMap G
    have hmap : coordinatePolynomialMap K ι (MvPolynomial.C v) =
        coordinatePolynomialMap K ι (F * h) := by
      rw [coordinatePolynomialMap, MvPolynomial.map_C, map_mul, ← hvh, ← mul_assoc,
        mul_right_comm, hG, one_mul]
    have heq := hinj hmap
    have heval : (v : Nonpositive ℝ K) =
        MvPolynomial.aeval b F * MvPolynomial.aeval b h := by
      rw [← aeval_C_finiteSupport b v, heq, map_mul]
    have hdvd : MvPolynomial.aeval b F ∣ (v : Nonpositive ℝ K) := ⟨MvPolynomial.aeval b h, heval⟩
    have hv' : (v : Nonpositive ℝ K) ≠ 0 := fun h0 ↦ hv (Subtype.ext h0)
    have hle := seriesDegree_le_of_dvd hdvd hv'
    rw [degreeValuation_finiteSupport_eq_zero v hv] at hle
    exact absurd (lt_of_lt_of_le haDegree hle) (lt_irrefl _)
  · -- clear denominators in a factorisation and use primality of the denominator
    obtain ⟨u, G', hu, huG⟩ := exists_C_mul_eq_coordinatePolynomialMap G
    obtain ⟨v, H', hv, hvH⟩ := exists_C_mul_eq_coordinatePolynomialMap H
    have hmap : coordinatePolynomialMap K ι (MvPolynomial.C (u * v) * F) =
        coordinatePolynomialMap K ι (G' * H') := by
      rw [map_mul (coordinatePolynomialMap K ι), map_mul (coordinatePolynomialMap K ι), ← huG,
        ← hvH, hGH, coordinatePolynomialMap, MvPolynomial.map_C, map_mul, MvPolynomial.C_mul]
      ring
    have heq := hinj hmap
    have heval : ((u * v : Berarducci.FiniteSupportRing (K := K)) : Nonpositive ℝ K) *
        MvPolynomial.aeval b F = MvPolynomial.aeval b G' * MvPolynomial.aeval b H' := by
      rw [← aeval_C_finiteSupport b (u * v), ← map_mul, heq, map_mul]
    have huv : u * v ≠ 0 := mul_ne_zero hu hv
    have huv' : ((u * v : Berarducci.FiniteSupportRing (K := K)) : Nonpositive ℝ K) ≠ 0 :=
      fun h0 ↦ huv (Subtype.ext h0)
    have huvdeg : degreeValuation K ((u * v : Berarducci.FiniteSupportRing (K := K)) :
        Nonpositive ℝ K) = 0 := degreeValuation_finiteSupport_eq_zero _ huv
    obtain ⟨u₁, u₂, hu₁, hu₂, huv₁₂⟩ :=
      isPrimal_of_mem_finiteSupportSubring (u * v).2 ⟨MvPolynomial.aeval b F, heval.symm⟩
    obtain ⟨g₁, hg₁⟩ := hu₁
    obtain ⟨h₁, hh₁⟩ := hu₂
    have hprod : MvPolynomial.aeval b F = g₁ * h₁ := by
      refine mul_left_cancel₀ huv' ?_
      rw [heval, hg₁, hh₁, huv₁₂]
      ring
    have hu₁dvd : u₁ ∣ ((u * v : Berarducci.FiniteSupportRing (K := K)) :
        Nonpositive ℝ K) := ⟨u₂, huv₁₂⟩
    have hu₂dvd : u₂ ∣ ((u * v : Berarducci.FiniteSupportRing (K := K)) :
        Nonpositive ℝ K) := ⟨u₁, by rw [huv₁₂, mul_comm]⟩
    have hG0 : G ≠ 0 := fun h0 ↦ hF0 (hinj (by rw [hGH, h0, zero_mul, map_zero]))
    have hH0 : H ≠ 0 := fun h0 ↦ hF0 (hinj (by rw [hGH, h0, mul_zero, map_zero]))
    rcases ha.isUnit_or_isUnit hprod with h | h
    · exact Or.inl (hb.isUnit_of_C_mul_eq_coordinatePolynomialMap hu hG0 huG
        (seriesDegree_le_zero_of_eq_mul hg₁ huv' huvdeg hu₁dvd h))
    · exact Or.inr (hb.isUnit_of_C_mul_eq_coordinatePolynomialMap hv hH0 hvH
        (seriesDegree_le_zero_of_eq_mul hh₁ huv' huvdeg hu₂dvd h))

/-! ### The embedding `K_fin[X_i]/(F) → L[X_i]/(F)` -/

/-- If `F(b)` is irreducible of positive degree and a polynomial over `K_fin` becomes a multiple
of `F` over `L`, then it is already a multiple of `F` over `K_fin`. -/
theorem mem_span_of_coordinatePolynomialMap_mem_span
    {F : MvPolynomial ι (Berarducci.FiniteSupportRing (K := K))}
    (ha : Irreducible (MvPolynomial.aeval b F))
    (haDegree : 0 < degreeValuation K (MvPolynomial.aeval b F))
    {g : MvPolynomial ι (Berarducci.FiniteSupportRing (K := K))}
    (hg : coordinatePolynomialMap K ι g ∈ Ideal.span {coordinatePolynomialMap K ι F}) :
    g ∈ Ideal.span {F} := by
  have hinj := coordinatePolynomialMap_injective K ι
  rw [Ideal.mem_span_singleton] at hg ⊢
  obtain ⟨q, hq⟩ := hg
  obtain ⟨u, h, hu, huh⟩ := exists_C_mul_eq_coordinatePolynomialMap q
  have hmap : coordinatePolynomialMap K ι (MvPolynomial.C u * g) =
      coordinatePolynomialMap K ι (F * h) := by
    rw [map_mul, map_mul, coordinatePolynomialMap, MvPolynomial.map_C, ← huh, hq]
    ring
  have heq := hinj hmap
  have heval : (u : Nonpositive ℝ K) * MvPolynomial.aeval b g =
      MvPolynomial.aeval b F * MvPolynomial.aeval b h := by
    rw [← aeval_C_finiteSupport b u, ← map_mul, heq, map_mul]
  have hu' : (u : Nonpositive ℝ K) ≠ 0 := fun h0 ↦ hu (Subtype.ext h0)
  -- primality of `u` and the unit property of finite-support divisors of `a`
  obtain ⟨u₁, u₂, hu₁, hu₂, hu₁₂⟩ :=
    isPrimal_of_mem_finiteSupportSubring u.2 ⟨MvPolynomial.aeval b g, heval.symm⟩
  have hu₁unit : IsUnit u₁ := by
    refine isUnit_of_dvd_of_seriesDegree_le_zero ha haDegree ?_ hu₁
    rw [← degreeValuation_finiteSupport_eq_zero u hu]
    exact seriesDegree_le_of_dvd ⟨u₂, hu₁₂⟩ hu'
  obtain ⟨t', ht'⟩ := hu₂
  -- `h(b) = u * t` with `t ∈ K_fin[b_i]`, by saturation
  set t : Nonpositive ℝ K := (hu₁unit.unit⁻¹ : Units (Nonpositive ℝ K)) * t' with ht
  have hht : MvPolynomial.aeval b h = (u : Nonpositive ℝ K) * t := by
    have hinv : u₁ * (hu₁unit.unit⁻¹ : Units (Nonpositive ℝ K)) = 1 :=
      hu₁unit.mul_val_inv
    rw [ht, ht', hu₁₂]
    calc u₂ * t' = (u₁ * (hu₁unit.unit⁻¹ : Units (Nonpositive ℝ K))) * (u₂ * t') := by
          rw [hinv, one_mul]
      _ = u₁ * u₂ * ((hu₁unit.unit⁻¹ : Units (Nonpositive ℝ K)) * t') := by ring
  obtain ⟨t'', ht''⟩ := (AlgHom.mem_range _).mp
    (hb.mem_range_of_mul_mem_range u t hu (hht ▸ (MvPolynomial.aeval b).mem_range_self h))
  have hh' : h = MvPolynomial.C u * t'' := by
    apply hb.injective
    rw [map_mul, aeval_C_finiteSupport, ht'', hht]
  refine ⟨t'', mul_left_cancel₀ (MvPolynomial.C_ne_zero.mpr hu) ?_⟩
  rw [heq, hh']
  ring

/-- The ideal `(F) ⊆ K_fin[X_i]` is the contraction of the ideal `(F) ⊆ L[X_i]`. -/
theorem span_singleton_eq_comap
    {F : MvPolynomial ι (Berarducci.FiniteSupportRing (K := K))}
    (ha : Irreducible (MvPolynomial.aeval b F))
    (haDegree : 0 < degreeValuation K (MvPolynomial.aeval b F)) :
    Ideal.span {F} =
      (Ideal.span {coordinatePolynomialMap K ι F}).comap (coordinatePolynomialMap K ι) := by
  refine le_antisymm ?_ fun g hg ↦ ?_
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap]
    exact Ideal.subset_span rfl
  · exact hb.mem_span_of_coordinatePolynomialMap_mem_span ha haDegree (Ideal.mem_comap.mp hg)

/-- `D = K_fin[X_i]/(F)` is a domain when `F(b)` is irreducible of positive degree: it embeds in
`L[X_i]/(F)`, and `L[X_i]` is a unique factorisation domain. -/
theorem quotient_span_singleton_isDomain
    {F : MvPolynomial ι (Berarducci.FiniteSupportRing (K := K))}
    (ha : Irreducible (MvPolynomial.aeval b F))
    (haDegree : 0 < degreeValuation K (MvPolynomial.aeval b F)) :
    IsDomain (MvPolynomial ι (Berarducci.FiniteSupportRing (K := K)) ⧸ Ideal.span {F}) := by
  have hirr := hb.irreducible_coordinatePolynomialMap_of_irreducible_aeval ha haDegree
  have : (Ideal.span {coordinatePolynomialMap K ι F}).IsPrime :=
    (Ideal.span_singleton_prime hirr.ne_zero).mpr hirr.prime
  rw [hb.span_singleton_eq_comap ha haDegree]
  exact Ideal.Quotient.isDomain _

/-- `F` is prime in `K_fin[X_i]` when `F(b)` is irreducible of positive degree. -/
theorem prime_of_irreducible_aeval
    {F : MvPolynomial ι (Berarducci.FiniteSupportRing (K := K))}
    (ha : Irreducible (MvPolynomial.aeval b F))
    (haDegree : 0 < degreeValuation K (MvPolynomial.aeval b F)) : Prime F := by
  have hF0 : F ≠ 0 := fun h ↦ ha.ne_zero (by rw [h, map_zero])
  have := hb.quotient_span_singleton_isDomain ha haDegree
  exact (Ideal.span_singleton_prime hF0).mp
    ((Ideal.Quotient.isDomain_iff_prime (Ideal.span {F})).mp inferInstance)

end IsPolynomialPresentation

end Berarducci
