/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.CantorBendixsonValueMultiplicativity
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.NaturalOrder
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# Germs at zero and the Cantor–Bendixson valuation

The Cantor–Bendixson value on nonpositive Hahn series is a Mathlib valuation with natural ordinal
values. Its support ideal consists exactly of series bounded strictly below exponent zero;
quotienting by that ideal therefore gives the ring of germs at zero. The valuation's prime
support makes this quotient a domain.

The ordered exponent group is assumed Cauchy complete. The characteristic-zero domain hypotheses
are those of the multiplicativity theorem. A domain conclusion alone does not assert factor
primality or polynomiality of the germ ring.
-/

public noncomputable section
open Set
universe u v
namespace HahnSeries.Nonpositive
variable {G : Type u} {R : Type v} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G] [CompleteSpace G]
  [CommRing R] [NoZeroDivisors R] [CharZero R]

/-- The natural-ordinal valuation given by the Cantor–Bendixson rank at zero. -/
def cantorBendixsonValuation : Valuation (Nonpositive G R) NatOrdinal.{u} where
  toFun b := NatOrdinal.of (b : HahnSeries G R).cantorBendixsonValue
  map_zero' := congrArg NatOrdinal.of cantorBendixsonValue_zero
  map_one' := by
    apply congrArg NatOrdinal.of
    exact cantorBendixsonValue_of_finite_of_coeff_ne_zero (1 : HahnSeries G R)
      (by rw [support_one]; exact finite_singleton _) (by simp)
  map_mul' b c := cantorBendixsonValue_mul _ _ b.property c.property
  map_add_le_max' b c := by
    rcases le_max_iff.mp ((b : HahnSeries G R).cantorBendixsonValue_add_le c) with h | h
    · exact le_max_of_le_left (NatOrdinal.of.monotone h)
    · exact le_max_of_le_right (NatOrdinal.of.monotone h)

/-- Evaluation agrees with the Cantor–Bendixson value of the Hahn series. -/
@[simp]
theorem cantorBendixsonValuation_apply (b : Nonpositive G R) :
    cantorBendixsonValuation b = NatOrdinal.of (b : HahnSeries G R).cantorBendixsonValue := (rfl)

/-- Vanishing in the valuation support means being bounded strictly below zero. -/
theorem mem_cantorBendixsonValuation_supp (b : Nonpositive G R) :
    b ∈ (cantorBendixsonValuation (G := G) (R := R)).supp ↔
      ∃ c < (0 : G), (b : HahnSeries G R).support ⊆ Iic c := by
  rw [Valuation.mem_supp_iff, cantorBendixsonValuation_apply]
  exact cantorBendixsonValue_eq_zero_iff_support_bounded_lt _ b.property

/-- Two germs agree exactly when their representatives agree above some negative bound. -/
theorem cantorBendixson_germ_eq_iff (b c : Nonpositive G R) :
    Ideal.Quotient.mk (cantorBendixsonValuation (G := G) (R := R)).supp b =
      Ideal.Quotient.mk (cantorBendixsonValuation (G := G) (R := R)).supp c ↔
        ∃ e < (0 : G), ∀ g > e, (b : HahnSeries G R).coeff g = (c : HahnSeries G R).coeff g := by
  rw [Ideal.Quotient.eq, mem_cantorBendixsonValuation_supp]
  constructor
  · rintro ⟨e, he, hbc⟩
    refine ⟨e, he, fun g hg ↦ ?_⟩
    have hz : ((b - c : Nonpositive G R) : HahnSeries G R).coeff g = 0 := by
      by_contra hn
      exact (not_le_of_gt hg) (hbc hn)
    change ((b : HahnSeries G R) - (c : HahnSeries G R)).coeff g = 0 at hz
    simpa only [coeff_sub, sub_eq_zero] using hz
  · rintro ⟨e, he, hbc⟩
    refine ⟨e, he, fun g hg ↦ ?_⟩
    apply le_of_not_gt
    intro hge
    have hz := hbc g hge
    apply hg
    change ((b : HahnSeries G R) - (c : HahnSeries G R)).coeff g = 0
    simpa only [coeff_sub, sub_eq_zero] using hz

/-- A series representing a unit germ has nonzero coefficient at exponent zero. -/
theorem constantCoeff_ne_zero_of_isUnit_cantorBendixson_germ
    {b : Nonpositive G R}
    (hb : IsUnit
      (Ideal.Quotient.mk (cantorBendixsonValuation (G := G) (R := R)).supp b)) :
    constantCoeff b ≠ 0 := by
  let J := (cantorBendixsonValuation (G := G) (R := R)).supp
  obtain ⟨q, hbq, _⟩ := isUnit_iff_exists.mp hb
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective q
  have heq : Ideal.Quotient.mk J (b * c) = Ideal.Quotient.mk J 1 := by
    simpa only [map_mul, map_one] using hbq
  obtain ⟨e, he, hcoeff⟩ := (cantorBendixson_germ_eq_iff (b * c) 1).mp heq
  have hbc : constantCoeff b * constantCoeff c = 1 := by
    have hbc' := hcoeff 0 he
    rw [show ((b * c : Nonpositive G R) : HahnSeries G R).coeff 0 =
      (b : HahnSeries G R).coeff 0 * (c : HahnSeries G R).coeff 0 from
        coeff_zero_mul b c] at hbc'
    simpa only [constantCoeff_apply, Subring.coe_one, HahnSeries.coeff_one, ite_eq_left] using hbc'
  intro hb0
  rw [hb0, zero_mul] at hbc
  exact zero_ne_one hbc

/-- The germ quotient by series bounded strictly below zero is a domain. -/
theorem cantorBendixson_germ_isDomain :
    IsDomain (Nonpositive G R ⧸ (cantorBendixsonValuation (G := G) (R := R)).supp) :=
  inferInstance

end HahnSeries.Nonpositive
