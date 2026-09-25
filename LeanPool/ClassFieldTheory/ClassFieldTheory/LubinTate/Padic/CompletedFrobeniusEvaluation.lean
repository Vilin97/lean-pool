/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.CompletedFrobeniusLift
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
/-!
# Semilinear evaluation for completed p-adic Frobenius lifts

The completed unit-indexed Frobenius lift preserves the actual integral
closure valuation ring.  Its restriction is continuous for the maximal-
ideal adic topology and transports convergent Witt-coefficient power-series
evaluation by Witt Frobenius on coefficients.

Applying this to the standard-to-multiplicative comparison identifies the
image of the genuine completed multiplicative primitive point with its
actual multiplicative unit translate.
-/

@[expose] public section

noncomputable
section

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open ValuationTheory.DiscreteValuationField

private noncomputable local instance (priority := 50)
    padicCompletedFrobeniusEvaluationWittUniformSpace
    (p : ℕ) [Fact p.Prime] :
    UniformSpace (padicCompletedUnramifiedWittRing p) :=
  ⊥

private noncomputable local instance
    padicCompletedFrobeniusEvaluationTargetWithIdeal
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    WithIdeal
      (padicCompletedLevelCompleteDVF p n).valuationSubring where
  i := (padicCompletedLevelCompleteDVF p n).maximalIdeal

private noncomputable local instance
    padicCompletedFrobeniusEvaluationTargetCompleteSpace
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    CompleteSpace
      (padicCompletedLevelCompleteDVF p n).valuationSubring := by
  let target := padicCompletedLevelCompleteDVF p n
  have hadic : IsAdic target.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp target.isAdicComplete).1

private noncomputable local instance
    padicCompletedFrobeniusEvaluationTargetT2Space
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    T2Space
      (padicCompletedLevelCompleteDVF p n).valuationSubring := by
  let target := padicCompletedLevelCompleteDVF p n
  have hadic : IsAdic target.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp target.isAdicComplete).2

/-- Arithmetic Frobenius restricted to the valuation ring of the completed
maximal-unramified p-adic field. -/
noncomputable def padicCompletedUnramifiedFrobeniusIntegerEquiv
    (p : ℕ) [Fact p.Prime] :
    (padicCompletedUnramifiedCompleteDVF p).valuationSubring ≃+*
      (padicCompletedUnramifiedCompleteDVF p).valuationSubring where
  toFun x :=
    ⟨padicCompletedUnramifiedFrobenius p
        (x : padicCompletedUnramifiedField p), by
      change
        padicCompletedUnramifiedValuation p
            (padicCompletedUnramifiedFrobenius p
              (x : padicCompletedUnramifiedField p)) ≤ 1
      rw [padicCompletedUnramifiedFrobenius_valuation]
      exact x.property⟩
  invFun x :=
    ⟨(padicCompletedUnramifiedFrobenius p).symm
        (x : padicCompletedUnramifiedField p), by
      change
        padicCompletedUnramifiedValuation p
            ((padicCompletedUnramifiedFrobenius p).symm
              (x : padicCompletedUnramifiedField p)) ≤ 1
      rw [← padicCompletedUnramifiedFrobenius_valuation p
          ((padicCompletedUnramifiedFrobenius p).symm
            (x : padicCompletedUnramifiedField p)),
        (padicCompletedUnramifiedFrobenius p).apply_symm_apply]
      exact x.property⟩
  left_inv x := by
    apply Subtype.ext
    exact (padicCompletedUnramifiedFrobenius p).symm_apply_apply x
  right_inv x := by
    apply Subtype.ext
    exact (padicCompletedUnramifiedFrobenius p).apply_symm_apply x
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (padicCompletedUnramifiedFrobenius p)
      (x : padicCompletedUnramifiedField p)
      (y : padicCompletedUnramifiedField p)
  map_add' x y := by
    apply Subtype.ext
    exact map_add (padicCompletedUnramifiedFrobenius p)
      (x : padicCompletedUnramifiedField p)
      (y : padicCompletedUnramifiedField p)

/-- Coercion of the integral Frobenius restriction agrees with arithmetic
Frobenius on the completed-unramified fraction field. -/
@[simp]
theorem padicCompletedUnramifiedFrobeniusIntegerEquiv_coe
    (p : ℕ) [Fact p.Prime]
    (x : (padicCompletedUnramifiedCompleteDVF p).valuationSubring) :
    ((padicCompletedUnramifiedFrobeniusIntegerEquiv p x :
        (padicCompletedUnramifiedCompleteDVF p).valuationSubring) :
      padicCompletedUnramifiedField p) =
      padicCompletedUnramifiedFrobenius p
        (x : padicCompletedUnramifiedField p) :=
  rfl

/-- Coercion of the inverse integral Frobenius restriction agrees with
inverse arithmetic Frobenius on the fraction field. -/
@[simp]
theorem padicCompletedUnramifiedFrobeniusIntegerEquiv_symm_coe
    (p : ℕ) [Fact p.Prime]
    (x : (padicCompletedUnramifiedCompleteDVF p).valuationSubring) :
    (((padicCompletedUnramifiedFrobeniusIntegerEquiv p).symm x :
        (padicCompletedUnramifiedCompleteDVF p).valuationSubring) :
      padicCompletedUnramifiedField p) =
      (padicCompletedUnramifiedFrobenius p).symm
        (x : padicCompletedUnramifiedField p) :=
  rfl

/-- The inverse of a unit-indexed completed Frobenius lift acts on base
scalars through inverse arithmetic Frobenius. -/
@[simp]
theorem padicCompletedUnitFrobeniusLiftEquiv_symm_algebraMap
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ)
    (b : padicCompletedUnramifiedField p) :
    (padicCompletedUnitFrobeniusLiftEquiv p n u).symm
        (algebraMap (padicCompletedUnramifiedField p)
          (padicCompletedLevelField p n) b) =
      algebraMap (padicCompletedUnramifiedField p)
        (padicCompletedLevelField p n)
        ((padicCompletedUnramifiedFrobenius p).symm b) := by
  apply (padicCompletedUnitFrobeniusLiftEquiv p n u).injective
  rw [(padicCompletedUnitFrobeniusLiftEquiv p n u).apply_symm_apply,
    padicCompletedUnitFrobeniusLiftEquiv_algebraMap,
    (padicCompletedUnramifiedFrobenius p).apply_symm_apply]

/-- A unit-indexed completed Frobenius lift carries every element of the
selected completed-level valuation ring back into that valuation ring. -/
theorem padicCompletedUnitFrobeniusLiftEquiv_mem_valuationSubring
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ)
    (x : padicCompletedLevelField p n)
    (hx :
      x ∈ (padicCompletedLevelCompleteDVF p n).valuation.valuationSubring) :
    padicCompletedUnitFrobeniusLiftEquiv p n u x ∈
      (padicCompletedLevelCompleteDVF p n).valuation.valuationSubring := by
  let base := padicCompletedUnramifiedCompleteDVF p
  let target := padicCompletedLevelCompleteDVF p n
  let E := padicCompletedUnramifiedField p
  let L := padicCompletedLevelField p n
  let φ :
      base.valuationSubring ≃+* base.valuationSubring :=
    padicCompletedUnramifiedFrobeniusIntegerEquiv p
  let σ : L ≃+* L :=
    padicCompletedUnitFrobeniusLiftEquiv p n u
  let : IsIntegralClosure target.valuationSubring
      base.valuationSubring L :=
    padicCompletedLevelCompleteDVF_isIntegralClosure p n
  have hxIntegral : IsIntegral base.valuationSubring x :=
    (IsIntegralClosure.isIntegral_iff
      (A := target.valuationSubring)
      (R := base.valuationSubring)
      (B := L)).2 ⟨⟨x, hx⟩, rfl⟩
  have hcomp :
      (algebraMap base.valuationSubring L).comp φ.toRingHom =
        σ.toRingHom.comp (algebraMap base.valuationSubring L) := by
    apply RingHom.ext
    intro b
    change
      algebraMap E L ((φ b : base.valuationSubring) : E) =
        σ (algebraMap E L (b : E))
    rw [show φ = padicCompletedUnramifiedFrobeniusIntegerEquiv p by rfl,
      padicCompletedUnramifiedFrobeniusIntegerEquiv_coe,
      show σ = padicCompletedUnitFrobeniusLiftEquiv p n u by rfl,
      padicCompletedUnitFrobeniusLiftEquiv_algebraMap]
  have hσIntegral : IsIntegral base.valuationSubring (σ x) :=
    IsIntegral.map_of_comp_eq φ.toRingHom σ.toRingHom hcomp hxIntegral
  rcases
      (IsIntegralClosure.isIntegral_iff
        (A := target.valuationSubring)
        (R := base.valuationSubring)
        (B := L)).1 hσIntegral with
    ⟨z, hz⟩
  change target.valuation (σ x) ≤ 1
  rw [← hz]
  exact z.property

/-- The inverse of a unit-indexed completed Frobenius lift also preserves
the selected completed-level valuation ring. -/
theorem padicCompletedUnitFrobeniusLiftEquiv_symm_mem_valuationSubring
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ)
    (x : padicCompletedLevelField p n)
    (hx :
      x ∈ (padicCompletedLevelCompleteDVF p n).valuation.valuationSubring) :
    (padicCompletedUnitFrobeniusLiftEquiv p n u).symm x ∈
      (padicCompletedLevelCompleteDVF p n).valuation.valuationSubring := by
  let base := padicCompletedUnramifiedCompleteDVF p
  let target := padicCompletedLevelCompleteDVF p n
  let E := padicCompletedUnramifiedField p
  let L := padicCompletedLevelField p n
  let φ :
      base.valuationSubring ≃+* base.valuationSubring :=
    (padicCompletedUnramifiedFrobeniusIntegerEquiv p).symm
  let σ : L ≃+* L :=
    (padicCompletedUnitFrobeniusLiftEquiv p n u).symm
  let : IsIntegralClosure target.valuationSubring
      base.valuationSubring L :=
    padicCompletedLevelCompleteDVF_isIntegralClosure p n
  have hxIntegral : IsIntegral base.valuationSubring x :=
    (IsIntegralClosure.isIntegral_iff
      (A := target.valuationSubring)
      (R := base.valuationSubring)
      (B := L)).2 ⟨⟨x, hx⟩, rfl⟩
  have hcomp :
      (algebraMap base.valuationSubring L).comp φ.toRingHom =
        σ.toRingHom.comp (algebraMap base.valuationSubring L) := by
    apply RingHom.ext
    intro b
    change
      algebraMap E L ((φ b : base.valuationSubring) : E) =
        σ (algebraMap E L (b : E))
    rw [show φ =
        (padicCompletedUnramifiedFrobeniusIntegerEquiv p).symm by rfl,
      padicCompletedUnramifiedFrobeniusIntegerEquiv_symm_coe,
      show σ =
        (padicCompletedUnitFrobeniusLiftEquiv p n u).symm by rfl,
      padicCompletedUnitFrobeniusLiftEquiv_symm_algebraMap]
  have hσIntegral : IsIntegral base.valuationSubring (σ x) :=
    IsIntegral.map_of_comp_eq φ.toRingHom σ.toRingHom hcomp hxIntegral
  rcases
      (IsIntegralClosure.isIntegral_iff
        (A := target.valuationSubring)
        (R := base.valuationSubring)
        (B := L)).1 hσIntegral with
    ⟨z, hz⟩
  change target.valuation (σ x) ≤ 1
  rw [← hz]
  exact z.property

/-- Membership in the selected completed-level valuation ring is invariant
under every unit-indexed completed Frobenius lift. -/
theorem padicCompletedUnitFrobeniusLiftEquiv_mem_valuationSubring_iff
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ)
    (x : padicCompletedLevelField p n) :
    x ∈ (padicCompletedLevelCompleteDVF p n).valuation.valuationSubring ↔
      padicCompletedUnitFrobeniusLiftEquiv p n u x ∈
        (padicCompletedLevelCompleteDVF p n).valuation.valuationSubring := by
  constructor
  · exact padicCompletedUnitFrobeniusLiftEquiv_mem_valuationSubring p n u x
  · intro hx
    have hback :=
      padicCompletedUnitFrobeniusLiftEquiv_symm_mem_valuationSubring
        p n u
        (padicCompletedUnitFrobeniusLiftEquiv p n u x) hx
    simpa using hback

/-- The actual valuation-ring automorphism induced by a unit-indexed
completed Frobenius lift. -/
noncomputable def padicCompletedUnitFrobeniusIntegerEquiv
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    (padicCompletedLevelCompleteDVF p n).valuationSubring ≃+*
      (padicCompletedLevelCompleteDVF p n).valuationSubring :=
  higherPrincipalUnitGroup.valuationSubringRingEquivOfPreserves
    (padicCompletedLevelCompleteDVF p n)
    (padicCompletedUnitFrobeniusLiftEquiv p n u)
    (padicCompletedUnitFrobeniusLiftEquiv_mem_valuationSubring_iff
      p n u)

/-- Coercion of the integral completed Frobenius restriction agrees with
the ambient field automorphism. -/
@[simp]
theorem padicCompletedUnitFrobeniusIntegerEquiv_coe
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring) :
    ((padicCompletedUnitFrobeniusIntegerEquiv p n u x :
        (padicCompletedLevelCompleteDVF p n).valuationSubring) :
      padicCompletedLevelField p n) =
      padicCompletedUnitFrobeniusLiftEquiv p n u
        (x : padicCompletedLevelField p n) :=
  rfl

/-- Coercion of the inverse integral completed Frobenius restriction agrees
with the inverse ambient field automorphism. -/
@[simp]
theorem padicCompletedUnitFrobeniusIntegerEquiv_symm_coe
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring) :
    (((padicCompletedUnitFrobeniusIntegerEquiv p n u).symm x :
        (padicCompletedLevelCompleteDVF p n).valuationSubring) :
      padicCompletedLevelField p n) =
      (padicCompletedUnitFrobeniusLiftEquiv p n u).symm
        (x : padicCompletedLevelField p n) := by
  apply (padicCompletedUnitFrobeniusLiftEquiv p n u).injective
  rw [(padicCompletedUnitFrobeniusLiftEquiv p n u).apply_symm_apply]
  simpa using
    (padicCompletedUnitFrobeniusIntegerEquiv_coe
      p n u
      ((padicCompletedUnitFrobeniusIntegerEquiv p n u).symm x)).symm

/-- The integral completed Frobenius restriction is continuous for the
maximal-ideal adic topology. -/
theorem padicCompletedUnitFrobeniusIntegerEquiv_continuous
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    Continuous (padicCompletedUnitFrobeniusIntegerEquiv p n u) := by
  let target := padicCompletedLevelCompleteDVF p n
  let σ : padicCompletedLevelField p n ≃+*
      padicCompletedLevelField p n :=
    padicCompletedUnitFrobeniusLiftEquiv p n u
  let hpreserve :
      ∀ x : padicCompletedLevelField p n,
        x ∈ target.valuation.valuationSubring ↔
          σ x ∈ target.valuation.valuationSubring :=
    padicCompletedUnitFrobeniusLiftEquiv_mem_valuationSubring_iff p n u
  let r : target.valuationSubring ≃+* target.valuationSubring :=
    padicCompletedUnitFrobeniusIntegerEquiv p n u
  apply continuous_of_continuousAt_zero r
  rw [ContinuousAt, map_zero]
  have hadic : IsAdic target.maximalIdeal := rfl
  apply (hadic.hasBasis_nhds_zero.tendsto_right_iff).2
  intro m _
  apply (hadic.hasBasis_nhds_zero.mem_iff).2
  refine ⟨m, trivial, ?_⟩
  intro x hx
  exact
    (higherPrincipalUnitGroup.valuationSubringRingEquivOfPreserves_mem_maximalIdeal_pow_iff
        target σ hpreserve m x).2 hx

/-- The integral completed Frobenius restriction transports the canonical
Witt coefficient map by Witt-vector Frobenius. -/
theorem padicCompletedUnitFrobeniusIntegerEquiv_wittCoefficientHom
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ)
    (a : padicCompletedUnramifiedWittRing p) :
    padicCompletedUnitFrobeniusIntegerEquiv p n u
        (padicCompletedLevelWittCoefficientHom p n a) =
      padicCompletedLevelWittCoefficientHom p n
        (WittVector.frobenius a) := by
  apply Subtype.ext
  change
    padicCompletedUnitFrobeniusLiftEquiv p n u
        (((padicCompletedLevelWittCoefficientHom p n a :
            (padicCompletedLevelCompleteDVF p n).valuationSubring) :
          padicCompletedLevelField p n)) =
      (((padicCompletedLevelWittCoefficientHom p n
            (WittVector.frobenius a) :
          (padicCompletedLevelCompleteDVF p n).valuationSubring) :
        padicCompletedLevelField p n))
  rw [padicCompletedLevelWittCoefficientHom_apply,
    padicCompletedUnitFrobeniusLiftEquiv_algebraMap,
    padicCompletedUnramifiedFrobenius_algebraMap_witt,
    padicCompletedLevelWittCoefficientHom_apply]

private theorem padicCompletedHasEval_map_continuous
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (r :
      (padicCompletedLevelCompleteDVF p n).valuationSubring →+*
        (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hr : Continuous r)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hx : PowerSeries.HasEval x) :
    PowerSeries.HasEval (r x) :=
  hx.map hr

/-- A convergent completed-level evaluation point remains convergent after
applying the integral completed Frobenius restriction. -/
theorem padicCompletedUnitFrobeniusIntegerEquiv_hasEval
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hx : PowerSeries.HasEval x) :
    PowerSeries.HasEval
      (padicCompletedUnitFrobeniusIntegerEquiv p n u x) := by
  exact
    padicCompletedHasEval_map_continuous p n
      (padicCompletedUnitFrobeniusIntegerEquiv p n u).toRingHom
      (padicCompletedUnitFrobeniusIntegerEquiv_continuous p n u) x hx

/-- Convergent completed-level evaluation is semilinear for every
unit-indexed completed Frobenius lift: the point is acted on by the
integral lift and coefficients by Witt Frobenius. -/
theorem padicCompletedUnitFrobeniusIntegerEquiv_evaluation
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hx : PowerSeries.HasEval x)
    (f : PowerSeries (padicCompletedUnramifiedWittRing p)) :
    padicCompletedUnitFrobeniusIntegerEquiv p n u
        (padicCompletedLevelPowerSeriesEval p n x hx f) =
      padicCompletedLevelPowerSeriesEval p n
        (padicCompletedUnitFrobeniusIntegerEquiv p n u x)
        (padicCompletedUnitFrobeniusIntegerEquiv_hasEval p n u x hx)
        (PowerSeries.map WittVector.frobenius f) := by
  have hsource : HasSum
      (fun m : ℕ =>
        padicCompletedLevelWittCoefficientHom p n
            (PowerSeries.coeff m f) * x ^ m)
      (padicCompletedLevelPowerSeriesEval p n x hx f) := by
    rw [padicCompletedLevelPowerSeriesEval,
      PowerSeries.coe_eval₂Hom]
    exact PowerSeries.hasSum_eval₂
      (padicCompletedLevelWittCoefficientHom_continuous p n)
      hx f
  have hmapped := hsource.map
    (padicCompletedUnitFrobeniusIntegerEquiv p n u)
    (padicCompletedUnitFrobeniusIntegerEquiv_continuous p n u)
  have hmapped' : HasSum
      (fun m : ℕ =>
        padicCompletedLevelWittCoefficientHom p n
            (PowerSeries.coeff m
              (PowerSeries.map WittVector.frobenius f)) *
          (padicCompletedUnitFrobeniusIntegerEquiv p n u x) ^ m)
      (padicCompletedUnitFrobeniusIntegerEquiv p n u
        (padicCompletedLevelPowerSeriesEval p n x hx f)) := by
    convert hmapped using 1
    funext m
    simp only [Function.comp_apply, map_mul, map_pow,
      PowerSeries.coeff_map,
      padicCompletedUnitFrobeniusIntegerEquiv_wittCoefficientHom]
  apply HasSum.unique hmapped'
  rw [padicCompletedLevelPowerSeriesEval,
    PowerSeries.coe_eval₂Hom]
  exact PowerSeries.hasSum_eval₂
    (padicCompletedLevelWittCoefficientHom_continuous p n)
    (padicCompletedUnitFrobeniusIntegerEquiv_hasEval p n u x hx)
    (PowerSeries.map WittVector.frobenius f)

/-- The integral completed Frobenius restriction sends the chosen
primitive point to its actual completed standard unit translate. -/
@[simp]
theorem padicCompletedUnitFrobeniusIntegerEquiv_primitiveRoot
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    padicCompletedUnitFrobeniusIntegerEquiv p n u
        (padicCompletedPrimitiveRootInteger p n) =
      padicCompletedStandardPrimitivePointUnitAction p n u := by
  apply Subtype.ext
  change
    padicCompletedUnitFrobeniusLiftEquiv p n u
        (padicCompletedPrimitiveRoot p n) =
      (((padicCompletedStandardPrimitivePointUnitAction p n u :
          (padicCompletedLevelCompleteDVF p n).valuationSubring) :
        padicCompletedLevelField p n))
  exact padicCompletedUnitFrobeniusLiftEquiv_primitiveRoot p n u

/-- The integral completed Frobenius restriction sends the genuine
multiplicative primitive point to its actual multiplicative unit
translate. -/
theorem
    padicCompletedUnitFrobeniusIntegerEquiv_multiplicativePrimitivePoint
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    padicCompletedUnitFrobeniusIntegerEquiv p n u
        (padicCompletedMultiplicativePrimitivePoint p n) =
      padicCompletedMultiplicativePrimitivePointUnitAction p u n := by
  let lambda := padicCompletedPrimitiveRootInteger p n
  let hlambda := padicCompletedPrimitiveRootInteger_hasEval p n
  let H := padicCompletedStandardToMultiplicativeIntertwiner p
  let r :=
    padicCompletedUnitFrobeniusIntegerEquiv p n u
  have hpoint :
      r lambda =
        padicCompletedStandardPrimitivePointUnitAction p n u := by
    simpa only [r, lambda] using
      padicCompletedUnitFrobeniusIntegerEquiv_primitiveRoot p n u
  calc
    r (padicCompletedMultiplicativePrimitivePoint p n) =
        padicCompletedLevelPowerSeriesEval p n
          (r lambda)
          (padicCompletedUnitFrobeniusIntegerEquiv_hasEval
            p n u lambda hlambda)
          (PowerSeries.map WittVector.frobenius H) := by
      simpa only [r, lambda, hlambda, H,
        padicCompletedMultiplicativePrimitivePoint] using
        (padicCompletedUnitFrobeniusIntegerEquiv_evaluation
          p n u lambda hlambda H)
    _ =
        padicCompletedLevelPowerSeriesEval p n
          (padicCompletedStandardPrimitivePointUnitAction p n u)
          (padicCompletedStandardPrimitivePointUnitAction_hasEval p n u)
          H := by
      rw [padicCompletedStandardToMultiplicativeIntertwiner_frobenius]
      exact
        padicCompletedLevelPowerSeriesEval_congr_point p n
          (padicCompletedUnitFrobeniusIntegerEquiv_hasEval
            p n u lambda hlambda)
          (padicCompletedStandardPrimitivePointUnitAction_hasEval p n u)
          hpoint H
    _ = padicCompletedMultiplicativePrimitivePointUnitAction p u n := by
      simpa only [lambda, hlambda, H,
        padicCompletedStandardPrimitivePointUnitAction,
        padicCompletedMultiplicativePrimitivePointUnitAction,
        padicCompletedMultiplicativeUnitEndomorphism,
        padicCompletedMultiplicativeScalarEndomorphismValue,
        padicCompletedMultiplicativePrimitivePoint] using
        (padicCompletedStandardToMultiplicativeIntertwiner_eval_endomorphism
          p n lambda hlambda
            (u : (padicLocalField p).valuationSubring))

end LubinTate

end
