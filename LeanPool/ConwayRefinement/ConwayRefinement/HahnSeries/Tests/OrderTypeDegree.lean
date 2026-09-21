/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrderType
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.HahnSeries.Degree
public import Mathlib.Data.Prod.Lex
public import Mathlib.Data.Sum.Order

import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Single

/-!
# API checks for support order type and degree

This client imports the public order-type and degree interface from a separate module. Its
coefficient-one series have supports of ordinary ordinal types `1 + ω = ω`, `ω + ω`, and
`(ω + 1) * ω = ω²`. The asymmetric sum and product distinguish ordinary ordinal arithmetic from
Hessenberg arithmetic at the level of order type. The degree certificates separately distinguish
LM24's leading-Cantor-exponent degree from the support order type itself and from the incorrect rule
that two consecutive infinite blocks have degree two.

The `ω + ω` fixture tests the ordinal calculation independently of any displayed real-exponent
series. The finite fixture has two support points, while the zero fixture is checked separately,
so degree zero cannot accidentally include the zero series.
-/

universe u

public noncomputable section

namespace Tests

open Ordinal
open scoped HahnSeries

/-- A Hessenberg sum of terms of degrees two and one has degree two, not three. -/
theorem naturalSumDegree_separator :
    NatOrdinal.cantorDegree (ω^ (2 : NatOrdinal) + ω^ (1 : NatOrdinal)) = 2 := by
  rw [NatOrdinal.cantorDegree_add, NatOrdinal.cantorDegree_wpow,
    NatOrdinal.cantorDegree_wpow]
  simp

/-- The absorbing bottom value records that a Hessenberg product with zero is zero. -/
theorem naturalProductDegree_zero :
    NatOrdinal.cantorDegree ((0 : NatOrdinal) * ω^ (2 : NatOrdinal)) = ⊥ := by
  simp

private theorem naturalProductDegree_asymmetric :
    NatOrdinal.cantorDegree
        (ω^ (1 : NatOrdinal) * ω^ NatOrdinal.of Ordinal.omega0) =
      (NatOrdinal.of (Ordinal.omega0 + 1) : WithBot NatOrdinal) := by
  rw [NatOrdinal.cantorDegree_mul, NatOrdinal.cantorDegree_wpow,
    NatOrdinal.cantorDegree_wpow, ← WithBot.coe_add, WithBot.coe_eq_coe,
    add_comm, ← NatOrdinal.of_add_one]

private theorem ordinaryProductDegree_asymmetric :
    Ordinal.cantorDegree
        (Ordinal.omega0 * Ordinal.omega0 ^ Ordinal.omega0) =
      (NatOrdinal.of Ordinal.omega0 : WithBot NatOrdinal) := by
  have hproduct : Ordinal.omega0 * Ordinal.omega0 ^ Ordinal.omega0 =
      Ordinal.omega0 ^ Ordinal.omega0 := by
    calc
      Ordinal.omega0 * Ordinal.omega0 ^ Ordinal.omega0 =
          Ordinal.omega0 ^ (1 : Ordinal) *
            Ordinal.omega0 ^ Ordinal.omega0 := by
        rw [Ordinal.opow_one]
      _ = Ordinal.omega0 ^ ((1 : Ordinal) + Ordinal.omega0) := by
        exact (Ordinal.opow_add Ordinal.omega0 1 Ordinal.omega0).symm
      _ = Ordinal.omega0 ^ Ordinal.omega0 := by rw [Ordinal.one_add_omega0]
  rw [hproduct,
    Ordinal.cantorDegree_of_ne_zero
      (Ordinal.opow_ne_zero Ordinal.omega0 Ordinal.omega0_ne_zero),
    Ordinal.log_opow Ordinal.one_lt_omega0]

/-- Hessenberg and ordinary multiplication can have different leading Cantor exponents. -/
theorem naturalProductDegree_ne_ordinaryProductDegree :
    NatOrdinal.cantorDegree
        (ω^ (1 : NatOrdinal) * ω^ NatOrdinal.of Ordinal.omega0) ≠
      Ordinal.cantorDegree
        (Ordinal.omega0 * Ordinal.omega0 ^ Ordinal.omega0) := by
  rw [naturalProductDegree_asymmetric, ordinaryProductDegree_asymmetric]
  intro h
  have h' : NatOrdinal.of (Ordinal.omega0 + 1) =
      NatOrdinal.of Ordinal.omega0 := WithBot.coe_eq_coe.mp h
  exact (lt_add_one Ordinal.omega0).ne' (NatOrdinal.of.injective h')

private def cancelingSeries : ℤ⟦ℤ⟧ :=
  HahnSeries.single 0 1

private theorem cancelingSeries_ne_zero : cancelingSeries ≠ 0 := by
  simp [cancelingSeries]

private theorem cancelingSeries_support_finite : cancelingSeries.support.Finite :=
  (Set.finite_singleton 0).subset HahnSeries.support_single_subset

private theorem cancelingSeries_degree : cancelingSeries.degree = 0 :=
  HahnSeries.degree_eq_zero.mpr
    ⟨cancelingSeries_ne_zero, cancelingSeries_support_finite⟩

private theorem neg_cancelingSeries_degree : (-cancelingSeries).degree = 0 := by
  apply HahnSeries.degree_eq_zero.mpr
  constructor
  · simpa using cancelingSeries_ne_zero
  · exact cancelingSeries_support_finite.subset (HahnSeries.support_neg_subset _)

/-- LM24's additive degree inequality applies in a cancellation case and can be strict. -/
theorem degree_add_cancellation_boundary :
    ∃ x : ℤ⟦ℤ⟧,
      (x + -x).degree ≤ max x.degree (-x).degree ∧
        (x + -x).degree < max x.degree (-x).degree := by
  refine ⟨cancelingSeries, HahnSeries.degree_add_le _ _, ?_⟩
  rw [add_neg_cancel, HahnSeries.degree_zero, cancelingSeries_degree,
    neg_cancelingSeries_degree]
  simp

private def twoTermCoeffs : ℤ →₀ ℕ :=
  Finsupp.single 0 1 + Finsupp.single 1 1

/-- The Hahn series with coefficient one at exponents `0` and `1`. -/
def twoTermOrderTypeSeries : ℕ⟦ℤ⟧ :=
  HahnSeries.ofFinsupp twoTermCoeffs

/-- `twoTermOrderTypeSeries` has support `{0, 1}`. -/
@[simp]
theorem twoTermOrderTypeSeries_support :
    twoTermOrderTypeSeries.support = {0, 1} := by
  classical
  ext z
  by_cases hz0 : z = 0
  · simp [twoTermOrderTypeSeries, twoTermCoeffs, hz0]
  by_cases hz1 : z = 1
  · simp [twoTermOrderTypeSeries, twoTermCoeffs, hz1]
  · simp [twoTermOrderTypeSeries, twoTermCoeffs, hz0, hz1]

theorem twoTermOrderTypeSeries_ne_zero : twoTermOrderTypeSeries ≠ 0 := by
  apply HahnSeries.support_nonempty_iff.mp
  rw [twoTermOrderTypeSeries_support]
  simp

theorem twoTermOrderTypeSeries_support_finite :
    twoTermOrderTypeSeries.support.Finite := by
  rw [twoTermOrderTypeSeries_support]
  simp

/-- A nonzero series with two support points has degree zero. -/
theorem twoTermOrderTypeSeries_degree :
    twoTermOrderTypeSeries.degree = (0 : WithBot NatOrdinal) :=
  HahnSeries.degree_eq_zero.mpr
    ⟨twoTermOrderTypeSeries_ne_zero, twoTermOrderTypeSeries_support_finite⟩

/-- Interface smoke test: the multiplicative degree bound applies to two nonzero series whose
supports each have exactly two points. -/
theorem twoTermOrderTypeSeries_square_degree_le :
    twoTermOrderTypeSeries ≠ 0 ∧
      (twoTermOrderTypeSeries * twoTermOrderTypeSeries).degree ≤
        twoTermOrderTypeSeries.degree + twoTermOrderTypeSeries.degree :=
  ⟨twoTermOrderTypeSeries_ne_zero, HahnSeries.degree_mul_le _ _⟩

/-- The zero series has degree `⊥`, rather than degree zero. -/
theorem zeroOrderTypeSeries_degree :
    (0 : ℕ⟦ℤ⟧).degree = ⊥ :=
  HahnSeries.degree_zero

private instance : WellFoundedLT (Unit ⊕ₗ ℕ) :=
  (Sum.Lex.toLexRelIsoLT (α := Unit) (β := ℕ)).symm.toRelEmbedding.isWellFounded

/-- The coefficient-one Hahn series on the ordered sum of `Unit` and `ℕ`. -/
def oneAddOmegaOrderTypeSeries : ℕ⟦Unit ⊕ₗ ℕ⟧ where
  coeff _ := 1
  isPWO_support' := by
    simpa [Function.support] using
      Set.IsPWO.of_linearOrder (Set.univ : Set (Unit ⊕ₗ ℕ))

@[simp]
theorem oneAddOmegaOrderTypeSeries_support :
    oneAddOmegaOrderTypeSeries.support = Set.univ := by
  ext n
  simp [oneAddOmegaOrderTypeSeries]

theorem oneAddOmegaOrderTypeSeries_supportOrderType :
    oneAddOmegaOrderTypeSeries.supportOrderType = Ordinal.omega0 := by
  calc
    oneAddOmegaOrderTypeSeries.supportOrderType = typeLT (Unit ⊕ₗ ℕ) := by
      let e : oneAddOmegaOrderTypeSeries.support ≃o Unit ⊕ₗ ℕ :=
        (OrderIso.setCongr oneAddOmegaOrderTypeSeries.support Set.univ
          oneAddOmegaOrderTypeSeries_support).trans
            (OrderIso.Set.univ (α := Unit ⊕ₗ ℕ))
      exact HahnSeries.supportOrderType_eq_typeLT e
    _ = Ordinal.type (Sum.Lex (· < · : Unit → Unit → Prop)
        (· < · : ℕ → ℕ → Prop)) :=
      (Sum.Lex.toLexRelIsoLT (α := Unit) (β := ℕ)).ordinalType_congr.symm
    _ = Ordinal.omega0 := by
      rw [Ordinal.type_sum_lex, Ordinal.type_nat_lt]
      simp

theorem oneAddOmegaOrderTypeSeries_degree :
    oneAddOmegaOrderTypeSeries.degree = (1 : WithBot NatOrdinal) := by
  rw [HahnSeries.degree_eq_cantorDegree, oneAddOmegaOrderTypeSeries_supportOrderType,
    Ordinal.cantorDegree_omega]

/-- Ordinary `1 + ω` differs from the Hessenberg sum of `1` and `ω`. -/
theorem naturalOneAddOmega_ne_supportOrderType :
    NatOrdinal.of (1 : Ordinal) + NatOrdinal.of Ordinal.omega0 ≠
      NatOrdinal.of oneAddOmegaOrderTypeSeries.supportOrderType := by
  rw [oneAddOmegaOrderTypeSeries_supportOrderType]
  intro h
  rw [add_comm] at h
  have hone : NatOrdinal.of (1 : Ordinal) = 1 := rfl
  rw [hone, ← NatOrdinal.of_add_one] at h
  exact (lt_add_one Ordinal.omega0).ne' (NatOrdinal.of.injective h)

private instance : WellFoundedLT (ℕ ⊕ₗ ℕ) :=
  (Sum.Lex.toLexRelIsoLT (α := ℕ) (β := ℕ)).symm.toRelEmbedding.isWellFounded

/-- The coefficient-one Hahn series on the ordered sum of two copies of `ℕ`. -/
def omegaAddOmegaOrderTypeSeries : ℕ⟦ℕ ⊕ₗ ℕ⟧ where
  coeff _ := 1
  isPWO_support' := by
    simpa [Function.support] using
      Set.IsPWO.of_linearOrder (Set.univ : Set (ℕ ⊕ₗ ℕ))

@[simp]
theorem omegaAddOmegaOrderTypeSeries_support :
    omegaAddOmegaOrderTypeSeries.support = Set.univ := by
  ext n
  simp [omegaAddOmegaOrderTypeSeries]

theorem omegaAddOmegaOrderTypeSeries_supportOrderType :
    omegaAddOmegaOrderTypeSeries.supportOrderType =
      Ordinal.omega0 + Ordinal.omega0 := by
  calc
    omegaAddOmegaOrderTypeSeries.supportOrderType = typeLT (ℕ ⊕ₗ ℕ) := by
      let e : omegaAddOmegaOrderTypeSeries.support ≃o ℕ ⊕ₗ ℕ :=
        (OrderIso.setCongr omegaAddOmegaOrderTypeSeries.support Set.univ
          omegaAddOmegaOrderTypeSeries_support).trans
            (OrderIso.Set.univ (α := ℕ ⊕ₗ ℕ))
      exact HahnSeries.supportOrderType_eq_typeLT e
    _ = Ordinal.type (Sum.Lex (· < ·) (· < ·)) :=
      (Sum.Lex.toLexRelIsoLT (α := ℕ) (β := ℕ)).ordinalType_congr.symm
    _ = Ordinal.omega0 + Ordinal.omega0 := by
      rw [Ordinal.type_sum_lex, Ordinal.type_nat_lt]

/-- A support of ordinary ordinal type `ω + ω` has degree one. -/
theorem omegaAddOmegaOrderTypeSeries_degree :
    omegaAddOmegaOrderTypeSeries.degree = (1 : WithBot NatOrdinal) := by
  rw [HahnSeries.degree_eq_cantorDegree, omegaAddOmegaOrderTypeSeries_supportOrderType,
    Ordinal.cantorDegree_omega_add_omega]

private instance : WellFoundedLT (ℕ ⊕ₗ Unit) :=
  (Sum.Lex.toLexRelIsoLT (α := ℕ) (β := Unit)).symm.toRelEmbedding.isWellFounded

/-- A coefficient-one Hahn series whose support has ordinary type `(ω + 1) * ω`. -/
def omegaSuccTimesOmegaOrderTypeSeries : ℕ⟦ℕ ×ₗ (ℕ ⊕ₗ Unit)⟧ where
  coeff _ := 1
  isPWO_support' := by
    simpa [Function.support] using
      Set.IsPWO.of_linearOrder (Set.univ : Set (ℕ ×ₗ (ℕ ⊕ₗ Unit)))

@[simp]
theorem omegaSuccTimesOmegaOrderTypeSeries_support :
    omegaSuccTimesOmegaOrderTypeSeries.support = Set.univ := by
  ext n
  simp [omegaSuccTimesOmegaOrderTypeSeries]

theorem omegaSuccTimesOmegaOrderTypeSeries_supportOrderType :
    omegaSuccTimesOmegaOrderTypeSeries.supportOrderType =
      Ordinal.omega0 ^ (2 : Ordinal) := by
  calc
    omegaSuccTimesOmegaOrderTypeSeries.supportOrderType =
        typeLT (ℕ ×ₗ (ℕ ⊕ₗ Unit)) := by
      let e : omegaSuccTimesOmegaOrderTypeSeries.support ≃o ℕ ×ₗ (ℕ ⊕ₗ Unit) :=
        (OrderIso.setCongr omegaSuccTimesOmegaOrderTypeSeries.support Set.univ
          omegaSuccTimesOmegaOrderTypeSeries_support).trans
            (OrderIso.Set.univ (α := ℕ ×ₗ (ℕ ⊕ₗ Unit)))
      exact HahnSeries.supportOrderType_eq_typeLT e
    _ = (typeLT (ℕ ⊕ₗ Unit)) * (typeLT ℕ) := by
      -- The strict order on the lexicographic product synonym is definitionally `Prod.Lex`.
      change Ordinal.type
        (Prod.Lex (· < · : ℕ → ℕ → Prop)
          (· < · : (ℕ ⊕ₗ Unit) → (ℕ ⊕ₗ Unit) → Prop)) = _
      exact Ordinal.type_prod_lex (· < ·) (· < ·)
    _ = (Ordinal.omega0 + 1) * Ordinal.omega0 := by
      rw [Ordinal.type_nat_lt]
      congr 1
      calc
        typeLT (ℕ ⊕ₗ Unit) =
            Ordinal.type (Sum.Lex (· < · : ℕ → ℕ → Prop)
              (· < · : Unit → Unit → Prop)) :=
          (Sum.Lex.toLexRelIsoLT (α := ℕ) (β := Unit)).ordinalType_congr.symm
        _ = Ordinal.omega0 + 1 := by
          rw [Ordinal.type_sum_lex, Ordinal.type_nat_lt]
          simp
    _ = Ordinal.omega0 * Ordinal.omega0 :=
      Ordinal.add_mul_of_isSuccLimit Ordinal.one_add_omega0
        Ordinal.isSuccLimit_omega0
    _ = Ordinal.omega0 ^ (2 : Ordinal) := by
      have hsucc : Order.succ (1 : Ordinal) = 2 := one_add_one_eq_two
      rw [← hsucc, Ordinal.opow_succ, Ordinal.opow_one]

/-- A support of ordinary ordinal type `ω²` has degree two. -/
theorem omegaSuccTimesOmegaOrderTypeSeries_degree :
    omegaSuccTimesOmegaOrderTypeSeries.degree = (2 : WithBot NatOrdinal) := by
  rw [HahnSeries.degree_eq_cantorDegree,
    omegaSuccTimesOmegaOrderTypeSeries_supportOrderType,
    Ordinal.cantorDegree_omega_sq]

/-- Ordinary `(ω + 1) * ω` differs from the corresponding Hessenberg product. -/
theorem naturalOmegaSuccTimesOmega_ne_supportOrderType :
    NatOrdinal.of (Ordinal.omega0 + 1) * NatOrdinal.of Ordinal.omega0 ≠
      NatOrdinal.of omegaSuccTimesOmegaOrderTypeSeries.supportOrderType := by
  rw [omegaSuccTimesOmegaOrderTypeSeries_supportOrderType]
  have hfactor :
      NatOrdinal.of Ordinal.omega0 < NatOrdinal.of (Ordinal.omega0 + 1) :=
    NatOrdinal.of.lt_iff_lt.mpr (lt_add_one Ordinal.omega0)
  have homega : (0 : NatOrdinal) < NatOrdinal.of Ordinal.omega0 :=
    NatOrdinal.of.lt_iff_lt.mpr Ordinal.omega0_pos
  have hproduct :
      NatOrdinal.of Ordinal.omega0 * NatOrdinal.of Ordinal.omega0 <
        NatOrdinal.of (Ordinal.omega0 + 1) * NatOrdinal.of Ordinal.omega0 :=
    mul_lt_mul_of_pos_right hfactor homega
  have hord : Ordinal.omega0 * Ordinal.omega0 =
      Ordinal.omega0 ^ (2 : Ordinal) := by
    have hsucc : Order.succ (1 : Ordinal) = 2 := one_add_one_eq_two
    rw [← hsucc, Ordinal.opow_succ, Ordinal.opow_one]
  have hordinary : NatOrdinal.of (Ordinal.omega0 ^ (2 : Ordinal)) ≤
      NatOrdinal.of Ordinal.omega0 * NatOrdinal.of Ordinal.omega0 := by
    rw [← hord]
    simpa using NatOrdinal.omul_le_mul
      (NatOrdinal.of Ordinal.omega0) (NatOrdinal.of Ordinal.omega0)
  exact (hordinary.trans_lt hproduct).ne'

/-- A surreal Hahn monomial, used only to check the small-support degree interface. -/
def surrealHahnMonomial : SurrealHahnSeries.{u} :=
  SurrealHahnSeries.single 0 1

theorem surrealHahnMonomial_ne_zero :
    (surrealHahnMonomial : SurrealHahnSeries.{u}) ≠ 0 := by
  intro h
  have hcoeff := congrArg
    (fun x : SurrealHahnSeries.{u} ↦ x.coeff (0 : Surreal.{u})) h
  simp [surrealHahnMonomial] at hcoeff

theorem surrealHahnMonomial_support_finite :
    (surrealHahnMonomial : SurrealHahnSeries.{u}).support.Finite :=
  (Set.finite_singleton 0).subset SurrealHahnSeries.support_single_subset

/-- Interface smoke test: a nonzero surreal Hahn monomial has degree zero. -/
theorem surrealHahnMonomial_supportDegree :
    (surrealHahnMonomial : SurrealHahnSeries.{u}).supportDegree =
      (0 : WithBot NatOrdinal) :=
  SurrealHahnSeries.supportDegree_eq_zero.mpr
    ⟨surrealHahnMonomial_ne_zero, surrealHahnMonomial_support_finite⟩

end Tests
