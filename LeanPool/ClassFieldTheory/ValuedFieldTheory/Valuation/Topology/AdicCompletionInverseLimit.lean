/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Topology.AdicCompletionInverseLimitRing
/-!
# Adic unit and higher-unit inverse limits

This file contains the algebraic and topological projective-limit descriptions
of unit groups of adically complete rings and complete discrete valuation
rings.  The underlying adic ring inverse-limit theory lives in
`AdicCompletionInverseLimitRing`.
-/

noncomputable section

namespace LubinTate
namespace Valuations

universe u v

open ValuationTheory.DiscreteValuationField
open ValuationTheory.Valuations
open Filter Set Topology
open scoped Valued

/-- The adic inverse-limit equivalence, unit form of the canonical adic-completion isomorphism. -/
def adicCompletionUnitsEquiv
    {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R] :
    Rˣ ≃* (AdicCompletion I R)ˣ :=
  Units.mapEquiv (adicCompletionAlgEquiv I).toRingEquiv.toMulEquiv

/-- The unit isomorphism is induced by the canonical ring map into the adic
completion. -/
theorem adicCompletionUnitsEquiv_apply
    {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R] (u : Rˣ) :
    (adicCompletionUnitsEquiv I u :
      AdicCompletion I R) =
      adicCompletionAlgEquiv I (u : R) :=
  rfl

/-- The adic inverse-limit equivalence, unit-coordinate injectivity: a unit of a complete ring is
determined by all of its finite reductions modulo `I ^ n`. -/
theorem adicCompletion_units_coordinates_injective
    {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    {u v : Rˣ}
    (h : ∀ n : ℕ,
      unitReduction (I ^ n) u = unitReduction (I ^ n) v) :
    u = v := by
  apply Units.ext
  apply adicCompletion_coordinates_injective I
  intro n
  exact congrArg Units.val (h n)

/-- The adic inverse-limit equivalence, unit-coordinate surjectivity against the adic completion:
every unit in the adic completion is represented by a unit of the complete
ring, and the finite quotient coordinates agree. -/
theorem adicCompletion_units_coordinates_surjective
    {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (z : (AdicCompletion I R)ˣ) :
    ∃ u : Rˣ,
      adicCompletionUnitsEquiv I u = z ∧
        ∀ n : ℕ,
          unitReduction (I ^ n) u =
            Units.map (AdicCompletion.evalₐ I n).toMonoidHom z := by
  refine ⟨(adicCompletionUnitsEquiv I).symm z, ?_, ?_⟩
  · simp
  · intro n
    ext
    simp [unitReduction]
    have hval :
        (((adicCompletionUnitsEquiv I).symm z : Rˣ) : R) =
          (adicCompletionAlgEquiv I).symm
            (z : AdicCompletion I R) := rfl
    rw [hval]
    simp [adicCompletionAlgEquiv]

/-- The adic inverse-limit equivalence, finite unit quotient form: if reduction modulo `I` is a
local quotient map, then `Rˣ / ker(Rˣ → (R/I)ˣ)` is `(R/I)ˣ`.  For valuation
rings and `I = 𝔭^n`, this is the finite stage of
`𝒪ˣ ≅ lim 𝒪ˣ/U⁽ⁿ⁾`. -/
noncomputable def unitsModIdealEquivQuotientUnits
    {R : Type*} [CommRing R] (I : Ideal R)
    [IsLocalHom (Ideal.Quotient.mk I)] :
    Rˣ ⧸ (unitReduction I).ker ≃* (R ⧸ I)ˣ :=
  QuotientGroup.quotientKerEquivOfSurjective (unitReduction I)
    (unitReduction_surjective_of_isLocalHom I)

/-- The finite unit quotient equivalence is induced by reduction. -/
theorem unitsModIdealEquivQuotientUnits_mk
    {R : Type*} [CommRing R] (I : Ideal R)
    [IsLocalHom (Ideal.Quotient.mk I)] (u : Rˣ) :
    unitsModIdealEquivQuotientUnits I (QuotientGroup.mk u) =
      unitReduction I u := by
  unfold unitsModIdealEquivQuotientUnits
    QuotientGroup.quotientKerEquivOfSurjective
    QuotientGroup.quotientKerEquivOfRightInverse
  exact QuotientGroup.kerLift_mk (unitReduction I) u

/-- In a local ring, reduction modulo a positive power of the maximal ideal is
a local quotient map. -/
theorem isLocalHom_quotient_maximalIdeal_pow
    {R : Type*} [CommRing R] [IsLocalRing R]
    {n : ℕ} (hn : 1 ≤ n) :
    IsLocalHom (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R) ^ n)) := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt (Nat.succ_le_iff.mp hn)
  have hpow_le :
      (IsLocalRing.maximalIdeal R) ^ n ≤ IsLocalRing.maximalIdeal R :=
    Ideal.pow_le_self hn0
  exact
    isLocalHom_of_le_jacobson_bot
      ((IsLocalRing.maximalIdeal R) ^ n)
      (hpow_le.trans
        (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal R)))

/-- The adic inverse-limit equivalence, finite unit quotient form for the maximal-ideal
filtration of a local ring. -/
noncomputable def unitsModMaximalIdealPowEquiv
    {R : Type*} [CommRing R] [IsLocalRing R]
    {n : ℕ} (hn : 1 ≤ n) :
    Rˣ ⧸ (unitReduction ((IsLocalRing.maximalIdeal R) ^ n)).ker ≃*
      (R ⧸ (IsLocalRing.maximalIdeal R) ^ n)ˣ := by
  letI : IsLocalHom
      (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R) ^ n)) :=
    isLocalHom_quotient_maximalIdeal_pow hn
  exact unitsModIdealEquivQuotientUnits
    ((IsLocalRing.maximalIdeal R) ^ n)

/-- The maximal-ideal finite unit quotient equivalence is induced by
reduction. -/
theorem unitsModMaximalIdealPowEquiv_mk
    {R : Type*} [CommRing R] [IsLocalRing R]
    {n : ℕ} (hn : 1 ≤ n) (u : Rˣ) :
    unitsModMaximalIdealPowEquiv (R := R) hn
        (QuotientGroup.mk u) =
      unitReduction ((IsLocalRing.maximalIdeal R) ^ n) u := by
  let : IsLocalHom
      (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R) ^ n)) :=
    isLocalHom_quotient_maximalIdeal_pow hn
  exact unitsModIdealEquivQuotientUnits_mk
    ((IsLocalRing.maximalIdeal R) ^ n) u

/-- The opaque projective-limit object `lim_n (R/I^n)^*` for quotient-unit
groups. -/
def adicUnitInverseLimit
    {R : Type*} [CommRing R] (I : Ideal R) : Type _ :=
  compatibleGroupFamilies (fun n : ℕ => (R ⧸ I ^ n)ˣ)
    (fun {_ _} hmn =>
      Units.map (Ideal.Quotient.factorPow I hmn).toMonoidHom)

/-- Defines `adicUnitInverseLimitCompatibleFamiliesEquiv`. -/
def adicUnitInverseLimitCompatibleFamiliesEquiv
    {R : Type*} [CommRing R] (I : Ideal R) :
    adicUnitInverseLimit I ≃
      compatibleGroupFamilies (fun n : ℕ => (R ⧸ I ^ n)ˣ)
        (fun {_ _} hmn =>
          Units.map (Ideal.Quotient.factorPow I hmn).toMonoidHom) := by
  unfold adicUnitInverseLimit
  exact Equiv.refl _

/-- Compatible unit families form a commutative group under coordinatewise multiplication. -/
instance adicUnitInverseLimit.instCommGroup
    {R : Type*} [CommRing R] (I : Ideal R) :
    CommGroup (adicUnitInverseLimit I) :=
  (adicUnitInverseLimitCompatibleFamiliesEquiv I).commGroup

/-- Defines `adicUnitInverseLimitRepresentation`. -/
def adicUnitInverseLimitRepresentation
    {R : Type*} [CommRing R] (I : Ideal R) :
    adicUnitInverseLimit I ≃*
      compatibleGroupFamilies (fun n : ℕ => (R ⧸ I ^ n)ˣ)
        (fun {_ _} hmn =>
          Units.map (Ideal.Quotient.factorPow I hmn).toMonoidHom) :=
  (adicUnitInverseLimitCompatibleFamiliesEquiv I).mulEquiv

/-- Defines `adicUnitInverseLimit_mk`. -/
def adicUnitInverseLimit_mk
    {R : Type*} [CommRing R] (I : Ideal R)
    (x : ∀ n : ℕ, (R ⧸ I ^ n)ˣ)
    (compatible : ∀ {m n : ℕ} (hmn : m ≤ n),
      Units.map (Ideal.Quotient.factorPow I hmn).toMonoidHom (x n) = x m) :
    adicUnitInverseLimit I :=
  (adicUnitInverseLimitCompatibleFamiliesEquiv I).symm ⟨x, compatible⟩

/-- Defines `adicUnitInverseLimit_eval`. -/
def adicUnitInverseLimit_eval
    {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    adicUnitInverseLimit I →* (R ⧸ I ^ n)ˣ where
  toFun x := (adicUnitInverseLimitCompatibleFamiliesEquiv I x).1 n
  map_one' := by rfl
  map_mul' _ _ := by rfl

/-- Evaluation of a compatible unit family returns its component at the selected level. -/
@[simp]
theorem adicUnitInverseLimit_eval_mk
    {R : Type*} [CommRing R] (I : Ideal R)
    (x : ∀ n : ℕ, (R ⧸ I ^ n)ˣ)
    (compatible : ∀ {m n : ℕ} (hmn : m ≤ n),
      Units.map (Ideal.Quotient.factorPow I hmn).toMonoidHom (x n) = x m)
    (n : ℕ) :
    adicUnitInverseLimit_eval I n (adicUnitInverseLimit_mk I x compatible) =
      x n := by
  rfl

/-- Two adic unit inverse-limit elements are equal when all evaluations agree. -/
@[ext]
theorem adicUnitInverseLimit_ext
    {R : Type*} [CommRing R] (I : Ideal R)
    {x y : adicUnitInverseLimit I}
    (h : ∀ n : ℕ, adicUnitInverseLimit_eval I n x =
      adicUnitInverseLimit_eval I n y) :
    x = y := by
  apply (adicUnitInverseLimitCompatibleFamiliesEquiv I).injective
  apply Subtype.ext
  funext n
  exact h n

/-- Evaluation commutes with the transition map between adic quotient levels. -/
theorem adicUnitInverseLimit_eval_transition
    {R : Type*} [CommRing R] (I : Ideal R)
    {m n : ℕ} (hmn : m ≤ n) (x : adicUnitInverseLimit I) :
    Units.map (Ideal.Quotient.factorPow I hmn).toMonoidHom
        (adicUnitInverseLimit_eval I n x) =
      adicUnitInverseLimit_eval I m x :=
  (adicUnitInverseLimitCompatibleFamiliesEquiv I x).2 hmn

/-- Units of the explicit projective-limit ring are the same as compatible
families of units in the finite quotient rings. -/
def adicQuotientInverseLimitUnitsEquiv
    {R : Type*} [CommRing R] (I : Ideal R) :
    (adicQuotientInverseLimit I)ˣ ≃*
      adicUnitInverseLimit I where
  toFun u := adicUnitInverseLimit_mk I
    (fun n => Units.map (adicQuotientInverseLimit_eval I n).toMonoidHom u)
    (fun hmn => by
      ext
      exact adicQuotientInverseLimit_eval_factorPow I hmn
        (u : adicQuotientInverseLimit I))
  invFun u :=
    { val := adicQuotientInverseLimit_mk I
        (fun n => (adicUnitInverseLimit_eval I n u : R ⧸ I ^ n))
        (fun hmn => congrArg Units.val
          (adicUnitInverseLimit_eval_transition I hmn u))
      inv := adicQuotientInverseLimit_mk I
        (fun n =>
          (((adicUnitInverseLimit_eval I n u)⁻¹ : (R ⧸ I ^ n)ˣ) :
            R ⧸ I ^ n))
        (fun hmn => by
          have h := congrArg Units.val
            (congrArg Inv.inv
              (adicUnitInverseLimit_eval_transition I hmn u))
          simpa using h)
      val_inv := by
        ext n
        exact Units.mul_inv (adicUnitInverseLimit_eval I n u)
      inv_val := by
        ext n
        exact Units.inv_mul (adicUnitInverseLimit_eval I n u) }
  left_inv u := by
    ext n
    rfl
  right_inv u := by
    ext n
    rfl
  map_mul' u v := by
    ext n
    rfl

/-- The adic inverse-limit equivalence, units of the adic completion are the projective limit of
the units of the finite quotient rings. -/
def adicCompletionUnitsEquivUnitInverseLimit
    {R : Type*} [CommRing R] (I : Ideal R) :
    (AdicCompletion I R)ˣ ≃* adicUnitInverseLimit I :=
  (Units.mapEquiv
      (adicCompletion_equiv_quotientInverseLimit I).toMulEquiv).trans
    (adicQuotientInverseLimitUnitsEquiv I)

/-- The adic inverse-limit equivalence, unit projective-limit form for a complete ring. -/
def unitsEquivUnitInverseLimit
    {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R] :
    Rˣ ≃* adicUnitInverseLimit I :=
  (adicCompletionUnitsEquiv I).trans
    (adicCompletionUnitsEquivUnitInverseLimit I)

/-- The complete-ring unit projective-limit isomorphism is induced by unit
reduction in each coordinate. -/
theorem unitsEquivUnitInverseLimit_apply
    {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (u : Rˣ) (n : ℕ) :
    adicUnitInverseLimit_eval I n (unitsEquivUnitInverseLimit I u) =
      unitReduction (I ^ n) u := by
  ext
  rfl

/-- The opaque positive-indexed unit inverse limit
`lim_n (R/I^(n+1))ˣ`. -/
def adicPositiveUnitInverseLimit
    {R : Type*} [CommRing R] (I : Ideal R) : Type _ :=
  compatibleGroupFamilies (fun n : ℕ => (R ⧸ I ^ (n + 1))ˣ)
    (fun {_ _} hmn =>
      Units.map
        (Ideal.Quotient.factorPow I (Nat.succ_le_succ hmn)).toMonoidHom)

/-- Defines `adicPositiveUnitInverseLimitCompatibleFamiliesEquiv`. -/
def adicPositiveUnitInverseLimitCompatibleFamiliesEquiv
    {R : Type*} [CommRing R] (I : Ideal R) :
    adicPositiveUnitInverseLimit I ≃
      compatibleGroupFamilies (fun n : ℕ => (R ⧸ I ^ (n + 1))ˣ)
        (fun {_ _} hmn =>
          Units.map
            (Ideal.Quotient.factorPow I
              (Nat.succ_le_succ hmn)).toMonoidHom) := by
  unfold adicPositiveUnitInverseLimit
  exact Equiv.refl _

/-- Positive-level compatible unit families form a commutative group. -/
instance adicPositiveUnitInverseLimit.instCommGroup
    {R : Type*} [CommRing R] (I : Ideal R) :
    CommGroup (adicPositiveUnitInverseLimit I) :=
  (adicPositiveUnitInverseLimitCompatibleFamiliesEquiv I).commGroup

/-- Defines `adicPositiveUnitInverseLimitRepresentation`. -/
def adicPositiveUnitInverseLimitRepresentation
    {R : Type*} [CommRing R] (I : Ideal R) :
    adicPositiveUnitInverseLimit I ≃*
      compatibleGroupFamilies (fun n : ℕ => (R ⧸ I ^ (n + 1))ˣ)
        (fun {_ _} hmn =>
          Units.map
            (Ideal.Quotient.factorPow I
              (Nat.succ_le_succ hmn)).toMonoidHom) :=
  (adicPositiveUnitInverseLimitCompatibleFamiliesEquiv I).mulEquiv

/-- Defines `adicPositiveUnitInverseLimit_mk`. -/
def adicPositiveUnitInverseLimit_mk
    {R : Type*} [CommRing R] (I : Ideal R)
    (x : ∀ n : ℕ, (R ⧸ I ^ (n + 1))ˣ)
    (compatible : ∀ {m n : ℕ} (hmn : m ≤ n),
      Units.map
          (Ideal.Quotient.factorPow I
            (Nat.succ_le_succ hmn)).toMonoidHom (x n) = x m) :
    adicPositiveUnitInverseLimit I :=
  (adicPositiveUnitInverseLimitCompatibleFamiliesEquiv I).symm
    ⟨x, compatible⟩

/-- Defines `adicPositiveUnitInverseLimit_eval`. -/
def adicPositiveUnitInverseLimit_eval
    {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    adicPositiveUnitInverseLimit I →* (R ⧸ I ^ (n + 1))ˣ where
  toFun x :=
    (adicPositiveUnitInverseLimitCompatibleFamiliesEquiv I x).1 n
  map_one' := by rfl
  map_mul' _ _ := by rfl

/-- Evaluation of a positive-level unit family returns its chosen component. -/
@[simp]
theorem adicPositiveUnitInverseLimit_eval_mk
    {R : Type*} [CommRing R] (I : Ideal R)
    (x : ∀ n : ℕ, (R ⧸ I ^ (n + 1))ˣ)
    (compatible : ∀ {m n : ℕ} (hmn : m ≤ n),
      Units.map
          (Ideal.Quotient.factorPow I
            (Nat.succ_le_succ hmn)).toMonoidHom (x n) = x m)
    (n : ℕ) :
    adicPositiveUnitInverseLimit_eval I n
        (adicPositiveUnitInverseLimit_mk I x compatible) = x n := by
  rfl

/-- Positive adic unit families are determined by all of their components. -/
@[ext]
theorem adicPositiveUnitInverseLimit_ext
    {R : Type*} [CommRing R] (I : Ideal R)
    {x y : adicPositiveUnitInverseLimit I}
    (h : ∀ n : ℕ, adicPositiveUnitInverseLimit_eval I n x =
      adicPositiveUnitInverseLimit_eval I n y) :
    x = y := by
  apply (adicPositiveUnitInverseLimitCompatibleFamiliesEquiv I).injective
  apply Subtype.ext
  funext n
  exact h n

/-- Positive-level evaluation respects the adic transition maps. -/
theorem adicPositiveUnitInverseLimit_eval_transition
    {R : Type*} [CommRing R] (I : Ideal R)
    {m n : ℕ} (hmn : m ≤ n) (x : adicPositiveUnitInverseLimit I) :
    Units.map
        (Ideal.Quotient.factorPow I
          (Nat.succ_le_succ hmn)).toMonoidHom
        (adicPositiveUnitInverseLimit_eval I n x) =
      adicPositiveUnitInverseLimit_eval I m x :=
  (adicPositiveUnitInverseLimitCompatibleFamiliesEquiv I x).2 hmn

/-- Defines `adicUnitInverseLimit_toPositive`. -/
def adicUnitInverseLimit_toPositive
    {R : Type*} [CommRing R] (I : Ideal R) :
    adicUnitInverseLimit I →
      adicPositiveUnitInverseLimit I :=
  fun u =>
    adicPositiveUnitInverseLimit_mk I
      (fun n => adicUnitInverseLimit_eval I (n + 1) u)
      (fun hmn => adicUnitInverseLimit_eval_transition I
        (Nat.succ_le_succ hmn) u)

/-- Defines `adicPositiveUnitInverseLimit_toAll`. -/
def adicPositiveUnitInverseLimit_toAll
    {R : Type*} [CommRing R] (I : Ideal R) :
    adicPositiveUnitInverseLimit I →
      adicUnitInverseLimit I :=
  fun u =>
    adicUnitInverseLimit_mk I (fun n => match n with
      | 0 => 1
      | k + 1 => adicPositiveUnitInverseLimit_eval I k u)
    (by
      intro m n hmn
      cases m with
      | zero =>
          ext
          have : Subsingleton (R ⧸ I ^ 0) := by
            simpa only [pow_zero, Ideal.one_eq_top] using
              (inferInstance : Subsingleton (R ⧸ (⊤ : Ideal R)))
          exact Subsingleton.elim _ _
      | succ m =>
          cases n with
          | zero => cases hmn
          | succ n =>
              exact adicPositiveUnitInverseLimit_eval_transition I
                (Nat.succ_le_succ_iff.mp hmn) u)

/-- Restricting an all-level unit family to positive levels and extending back is the identity. -/
theorem adicPositiveUnitInverseLimit_toPositive_toAll
    {R : Type*} [CommRing R] (I : Ideal R)
    (u : adicPositiveUnitInverseLimit I) :
    adicUnitInverseLimit_toPositive I
        (adicPositiveUnitInverseLimit_toAll I u) = u := by
  ext n
  rfl

/-- Extending a positive-level unit family and restricting again is the identity. -/
theorem adicUnitInverseLimit_toAll_toPositive
    {R : Type*} [CommRing R] (I : Ideal R)
    (u : adicUnitInverseLimit I) :
    adicPositiveUnitInverseLimit_toAll I
        (adicUnitInverseLimit_toPositive I u) = u := by
  ext n
  cases n with
  | zero =>
      have : Subsingleton (R ⧸ I ^ 0) := by
        simpa only [pow_zero, Ideal.one_eq_top] using
          (inferInstance : Subsingleton (R ⧸ (⊤ : Ideal R)))
      exact Subsingleton.elim _ _
  | succ n =>
      rfl

/-- The all-level unit inverse limit is equivalent to the positive-indexed
one.  This removes the degenerate `I^0` coordinate used by mathlib's adic
completion API. -/
def adicUnitInverseLimitEquivPositive
    {R : Type*} [CommRing R] (I : Ideal R) :
    adicUnitInverseLimit I ≃*
      adicPositiveUnitInverseLimit I where
  toFun := adicUnitInverseLimit_toPositive I
  invFun := adicPositiveUnitInverseLimit_toAll I
  left_inv := adicUnitInverseLimit_toAll_toPositive I
  right_inv := adicPositiveUnitInverseLimit_toPositive_toAll I
  map_mul' u v := by
    ext n
    rfl

/-- Complete-ring unit projective-limit form with the positive indexing. -/
def unitsEquivPositiveUnitInverseLimit
    {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R] :
    Rˣ ≃* adicPositiveUnitInverseLimit I :=
  (unitsEquivUnitInverseLimit I).trans
    (adicUnitInverseLimitEquivPositive I)

/-- The positive-indexed complete-ring unit inverse-limit isomorphism is
coordinatewise reduction modulo `I^(n+1)`. -/
theorem unitsEquivPositiveUnitInverseLimit_apply
    {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (u : Rˣ) (n : ℕ) :
    adicPositiveUnitInverseLimit_eval I n
        (unitsEquivPositiveUnitInverseLimit I u) =
      unitReduction (I ^ (n + 1)) u := by
  exact unitsEquivUnitInverseLimit_apply I u (n + 1)

/-- The first principal ideal generated by `π` has powers `π^nO`. -/
theorem dvrPowerIdeal_one_pow
    {O : Type*} [CommRing O] (π : O) (n : ℕ) :
    (uniformizerPowerIdeal π 1) ^ n = uniformizerPowerIdeal π n := by
  simp [uniformizerPowerIdeal, Ideal.span_singleton_pow]

/-- The principal-power ideals form a decreasing filtration. -/
theorem dvrPowerIdeal_le_of_le
    {O : Type*} [CommRing O] (π : O) {m n : ℕ} (hmn : m ≤ n) :
    uniformizerPowerIdeal π n ≤ uniformizerPowerIdeal π m := by
  rw [← dvrPowerIdeal_one_pow π m,
    ← dvrPowerIdeal_one_pow π n]
  exact Ideal.pow_le_pow_right hmn

/-- Transition map on the finite unit quotients `(O/π^(n+1)O)ˣ`. -/
def dvrPowerIdealUnitTransition
    {O : Type*} [CommRing O] (π : O) {m n : ℕ} (hmn : m ≤ n) :
    O ⧸ uniformizerPowerIdeal π (n + 1) →+*
      O ⧸ uniformizerPowerIdeal π (m + 1) :=
  Ideal.Quotient.factor
    (dvrPowerIdeal_le_of_le π (Nat.succ_le_succ hmn))

/-- The opaque positive-indexed projective limit
`lim_n (O/π^(n+1)O)ˣ`. -/
def dvrPowerIdealUnitInverseLimit
    {O : Type*} [CommRing O] (π : O) : Type _ :=
  compatibleGroupFamilies
    (fun n : ℕ => (O ⧸ uniformizerPowerIdeal π (n + 1))ˣ)
    (fun {_ _} hmn =>
      Units.map
        (dvrPowerIdealUnitTransition π hmn).toMonoidHom)

/-- Defines `dvrPowerIdealUnitInverseLimitCompatibleFamiliesEquiv`. -/
def dvrPowerIdealUnitInverseLimitCompatibleFamiliesEquiv
    {O : Type*} [CommRing O] (π : O) :
    dvrPowerIdealUnitInverseLimit π ≃
      compatibleGroupFamilies
        (fun n : ℕ => (O ⧸ uniformizerPowerIdeal π (n + 1))ˣ)
        (fun {_ _} hmn =>
          Units.map
            (dvrPowerIdealUnitTransition π hmn).toMonoidHom) := by
  unfold dvrPowerIdealUnitInverseLimit
  exact Equiv.refl _

/-- Compatible units modulo powers of a DVR element form a commutative group. -/
instance dvrPowerIdealUnitInverseLimit.instCommGroup
    {O : Type*} [CommRing O] (π : O) :
    CommGroup (dvrPowerIdealUnitInverseLimit π) :=
  (dvrPowerIdealUnitInverseLimitCompatibleFamiliesEquiv π).commGroup

/-- Defines `dvrPowerIdealUnitInverseLimitRepresentation`. -/
def dvrPowerIdealUnitInverseLimitRepresentation
    {O : Type*} [CommRing O] (π : O) :
    dvrPowerIdealUnitInverseLimit π ≃*
      compatibleGroupFamilies
        (fun n : ℕ => (O ⧸ uniformizerPowerIdeal π (n + 1))ˣ)
        (fun {_ _} hmn =>
          Units.map
            (dvrPowerIdealUnitTransition π hmn).toMonoidHom) :=
  (dvrPowerIdealUnitInverseLimitCompatibleFamiliesEquiv π).mulEquiv

/-- Defines `dvrPowerIdealUnitInverseLimit_mk`. -/
def dvrPowerIdealUnitInverseLimit_mk
    {O : Type*} [CommRing O] (π : O)
    (x : ∀ n : ℕ, (O ⧸ uniformizerPowerIdeal π (n + 1))ˣ)
    (compatible : ∀ {m n : ℕ} (hmn : m ≤ n),
      Units.map (dvrPowerIdealUnitTransition π hmn).toMonoidHom (x n) = x m) :
    dvrPowerIdealUnitInverseLimit π :=
  (dvrPowerIdealUnitInverseLimitCompatibleFamiliesEquiv π).symm
    ⟨x, compatible⟩

/-- Defines `dvrPowerIdealUnitInverseLimit_eval`. -/
def dvrPowerIdealUnitInverseLimit_eval
    {O : Type*} [CommRing O] (π : O) (n : ℕ) :
    dvrPowerIdealUnitInverseLimit π →*
      (O ⧸ uniformizerPowerIdeal π (n + 1))ˣ where
  toFun x :=
    (dvrPowerIdealUnitInverseLimitCompatibleFamiliesEquiv π x).1 n
  map_one' := by rfl
  map_mul' _ _ := by rfl

/-- DVR power-ideal unit families are equal when all coordinate evaluations agree. -/
@[ext]
theorem dvrPowerIdealUnitInverseLimit_ext
    {O : Type*} [CommRing O] (π : O)
    {x y : dvrPowerIdealUnitInverseLimit π}
    (h : ∀ n : ℕ, dvrPowerIdealUnitInverseLimit_eval π n x =
      dvrPowerIdealUnitInverseLimit_eval π n y) :
    x = y := by
  apply (dvrPowerIdealUnitInverseLimitCompatibleFamiliesEquiv π).injective
  apply Subtype.ext
  funext n
  exact h n

/-- The finite quotient-unit stage for `(π)^(n+1)` agrees with the canonical
stage `π^(n+1)O`. -/
def powerIdealStageEquiv
    {O : Type*} [CommRing O] (π : O) (n : ℕ) :
    (O ⧸ (uniformizerPowerIdeal π 1) ^ (n + 1))ˣ ≃*
      (O ⧸ uniformizerPowerIdeal π (n + 1))ˣ :=
  Units.mapEquiv
    (Ideal.quotientEquivAlgOfEq O
      (dvrPowerIdeal_one_pow π (n + 1))).toRingEquiv.toMulEquiv

/-- The finite stage equivalence is induced by the equality
`(πO)^(n+1) = π^(n+1)O`. -/
theorem powerIdealStageEquiv_apply
    {O : Type*} [CommRing O] (π : O) (n : ℕ)
    (u : (O ⧸ (uniformizerPowerIdeal π 1) ^ (n + 1))ˣ) :
    (powerIdealStageEquiv π n u :
      O ⧸ uniformizerPowerIdeal π (n + 1)) =
      (Ideal.quotientEquivAlgOfEq O
        (dvrPowerIdeal_one_pow π (n + 1))) (u : _) :=
  rfl

/-- The stage equivalences commute with the projective transition maps. -/
theorem powerIdealStageEquiv_factorPow
    {O : Type*} [CommRing O] (π : O) {m n : ℕ} (hmn : m ≤ n)
    (x : O ⧸ (uniformizerPowerIdeal π 1) ^ (n + 1)) :
    (Ideal.quotientEquivAlgOfEq O
      (dvrPowerIdeal_one_pow π (m + 1)))
        (Ideal.Quotient.factorPow (uniformizerPowerIdeal π 1)
          (Nat.succ_le_succ hmn) x) =
      dvrPowerIdealUnitTransition π hmn
        ((Ideal.quotientEquivAlgOfEq O
          (dvrPowerIdeal_one_pow π (n + 1))) x) := by
  refine Quotient.inductionOn' x ?_
  intro r
  change (Ideal.quotientEquivAlgOfEq O
      (dvrPowerIdeal_one_pow π (m + 1)))
        (Ideal.Quotient.factorPow (uniformizerPowerIdeal π 1)
          (Nat.succ_le_succ hmn)
          (Ideal.Quotient.mk ((uniformizerPowerIdeal π 1) ^ (n + 1)) r)) =
      dvrPowerIdealUnitTransition π hmn
        ((Ideal.quotientEquivAlgOfEq O
          (dvrPowerIdeal_one_pow π (n + 1)))
            (Ideal.Quotient.mk ((uniformizerPowerIdeal π 1) ^ (n + 1)) r))
  rw [Ideal.quotientEquivAlgOfEq_mk]
  simp [dvrPowerIdealUnitTransition, Ideal.Quotient.factorPow]

/-- The positive-indexed unit inverse limit for the principal ideal `(π)` is
the finite quotient-unit inverse limit `lim_n (O/π^(n+1)O)ˣ`. -/
def adicPositiveUnitInverseLimitEquivDVRPowerIdealUnitInverseLimit
    {O : Type*} [CommRing O] (π : O) :
    adicPositiveUnitInverseLimit (uniformizerPowerIdeal π 1) ≃*
      dvrPowerIdealUnitInverseLimit π :=
  (adicPositiveUnitInverseLimitRepresentation
      (uniformizerPowerIdeal π 1)).trans
    ((compatibleGroupFamiliesMulEquiv
      (fun n : ℕ => (O ⧸ (uniformizerPowerIdeal π 1) ^ (n + 1))ˣ)
      (fun n : ℕ => (O ⧸ uniformizerPowerIdeal π (n + 1))ˣ)
      (fun {_ _} hmn =>
        Units.map
          (Ideal.Quotient.factorPow (uniformizerPowerIdeal π 1)
            (Nat.succ_le_succ hmn)).toMonoidHom)
      (fun {_ _} hmn =>
        Units.map
          (dvrPowerIdealUnitTransition π hmn).toMonoidHom)
      (fun n => powerIdealStageEquiv π n)
      (by
        intro m n hmn u
        apply Units.ext
        exact (powerIdealStageEquiv_factorPow π hmn (u : _)).symm)).trans
      (dvrPowerIdealUnitInverseLimitRepresentation π).symm)

/-- Transition map on the positive-indexed quotients `Oˣ/U^(n+1)`. -/
def dvrHigherUnitQuotientTransition
    {O : Type*} [CommRing O] (π : O) {m n : ℕ} (hmn : m ≤ n) :
    Oˣ ⧸ higherUnitSubgroup π (n + 1) →*
      Oˣ ⧸ higherUnitSubgroup π (m + 1) :=
  QuotientGroup.map _ _ (MonoidHom.id Oˣ) <| by
    intro u hu
    exact higherUnitSubgroup_le_of_le π (Nat.succ_le_succ hmn) hu

private theorem dvrHigherUnitQuotientTransition_mk
    {O : Type*} [CommRing O] (π : O) {m n : ℕ} (hmn : m ≤ n) (u : Oˣ) :
    dvrHigherUnitQuotientTransition π hmn
        (u : Oˣ ⧸ higherUnitSubgroup π (n + 1)) =
      (u : Oˣ ⧸ higherUnitSubgroup π (m + 1)) := by
  have hmap :
      higherUnitSubgroup π (n + 1) ≤
        (higherUnitSubgroup π (m + 1)).comap (MonoidHom.id Oˣ) := by
    intro x hx
    exact higherUnitSubgroup_le_of_le π (Nat.succ_le_succ hmn) hx
  unfold dvrHigherUnitQuotientTransition
  exact QuotientGroup.map_mk
    (N := higherUnitSubgroup π (n + 1))
    (higherUnitSubgroup π (m + 1)) (MonoidHom.id Oˣ) hmap u

/-- A higher-unit quotient with discreteness fixed in its type. -/
structure DiscreteHigherUnitQuotient
    {O : Type*} [CommRing O] (π : O) (n : ℕ) where
  /-- The underlying higher-unit quotient class. -/
  val : Oˣ ⧸ higherUnitSubgroup π n

namespace DiscreteHigherUnitQuotient

/-- Defines `equiv`. -/
def equiv {O : Type*} [CommRing O] (π : O) (n : ℕ) :
    DiscreteHigherUnitQuotient π n ≃
      Oˣ ⧸ higherUnitSubgroup π n where
  toFun := val
  invFun := fun x => ⟨x⟩
  left_inv := fun x => by cases x; rfl
  right_inv := fun _ => rfl

/-- A discrete higher-unit quotient inherits its commutative group structure
from the concrete quotient. -/
instance {O : Type*} [CommRing O] (π : O) (n : ℕ) :
    CommGroup (DiscreteHigherUnitQuotient π n) :=
  (equiv π n).commGroup

/-- Each higher-unit quotient is equipped with the discrete topology. -/
instance {O : Type*} [CommRing O] (π : O) (n : ℕ) :
    TopologicalSpace (DiscreteHigherUnitQuotient π n) := ⊥

/-- The chosen topology on a higher-unit quotient is discrete. -/
instance {O : Type*} [CommRing O] (π : O) (n : ℕ) :
    DiscreteTopology (DiscreteHigherUnitQuotient π n) :=
  ⟨rfl⟩

/-- Defines `of`. -/
def of {O : Type*} [CommRing O] (π : O) (n : ℕ)
    (x : Oˣ ⧸ higherUnitSubgroup π n) :
    DiscreteHigherUnitQuotient π n :=
  ⟨x⟩

/-- Forgetting the discrete wrapper after inserting a quotient element recovers that element. -/
@[simp]
theorem val_of {O : Type*} [CommRing O] (π : O) (n : ℕ)
    (x : Oˣ ⧸ higherUnitSubgroup π n) : (of π n x).val = x :=
  rfl

/-- Defines `homeomorph`. -/
def homeomorph {O : Type*} [CommRing O] (π : O) (n : ℕ) :
    @Homeomorph (DiscreteHigherUnitQuotient π n)
      (Oˣ ⧸ higherUnitSubgroup π n)
      (inferInstance : TopologicalSpace
        (DiscreteHigherUnitQuotient π n))
      (⊥ : TopologicalSpace (Oˣ ⧸ higherUnitSubgroup π n)) := by
  letI : TopologicalSpace (Oˣ ⧸ higherUnitSubgroup π n) := ⊥
  letI : DiscreteTopology (Oˣ ⧸ higherUnitSubgroup π n) := ⟨rfl⟩
  exact
    { toEquiv := equiv π n
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

/-- The discrete comparison homeomorphism acts as the underlying quotient equivalence. -/
@[simp]
theorem homeomorph_apply {O : Type*} [CommRing O] (π : O) (n : ℕ)
    (x : DiscreteHigherUnitQuotient π n) : homeomorph π n x = x.val :=
  rfl

/-- The inverse discrete quotient equivalence wraps the concrete quotient element. -/
@[simp]
theorem equiv_symm_apply {O : Type*} [CommRing O]
    (π : O) (n : ℕ) (x : Oˣ ⧸ higherUnitSubgroup π n) :
    (equiv π n).symm x = of π n x :=
  rfl

end DiscreteHigherUnitQuotient

/-- The opaque direct quotient-system object `lim_n Oˣ/U^(n+1)`. -/
def dvrHigherUnitQuotientInverseLimit
    {O : Type*} [CommRing O] (π : O) : Type _ :=
  compatibleGroupFamilies
    (fun n : ℕ => Oˣ ⧸ higherUnitSubgroup π (n + 1))
    (fun {_ _} hmn => dvrHigherUnitQuotientTransition π hmn)

/-- Defines `dvrHigherUnitQuotientInverseLimitCompatibleFamiliesEquiv`. -/
def dvrHigherUnitQuotientInverseLimitCompatibleFamiliesEquiv
    {O : Type*} [CommRing O] (π : O) :
    dvrHigherUnitQuotientInverseLimit π ≃
      compatibleGroupFamilies
        (fun n : ℕ => Oˣ ⧸ higherUnitSubgroup π (n + 1))
        (fun {_ _} hmn => dvrHigherUnitQuotientTransition π hmn) := by
  unfold dvrHigherUnitQuotientInverseLimit
  exact Equiv.refl _

/-- The inverse limit of higher-unit quotients is a commutative group. -/
instance dvrHigherUnitQuotientInverseLimit.instCommGroup
    {O : Type*} [CommRing O] (π : O) :
    CommGroup (dvrHigherUnitQuotientInverseLimit π) :=
  (dvrHigherUnitQuotientInverseLimitCompatibleFamiliesEquiv π).commGroup

/-- Defines `dvrHigherUnitQuotientInverseLimitRepresentation`. -/
def dvrHigherUnitQuotientInverseLimitRepresentation
    {O : Type*} [CommRing O] (π : O) :
    dvrHigherUnitQuotientInverseLimit π ≃*
      compatibleGroupFamilies
        (fun n : ℕ => Oˣ ⧸ higherUnitSubgroup π (n + 1))
        (fun {_ _} hmn => dvrHigherUnitQuotientTransition π hmn) :=
  (dvrHigherUnitQuotientInverseLimitCompatibleFamiliesEquiv π).mulEquiv

/-- Defines `dvrHigherUnitQuotientInverseLimit_mk`. -/
def dvrHigherUnitQuotientInverseLimit_mk
    {O : Type*} [CommRing O] (π : O)
    (x : ∀ n : ℕ, Oˣ ⧸ higherUnitSubgroup π (n + 1))
    (compatible : ∀ {m n : ℕ} (hmn : m ≤ n),
      dvrHigherUnitQuotientTransition π hmn (x n) = x m) :
    dvrHigherUnitQuotientInverseLimit π :=
  (dvrHigherUnitQuotientInverseLimitCompatibleFamiliesEquiv π).symm
    ⟨x, compatible⟩

/-- Defines `dvrHigherUnitQuotientInverseLimit_eval`. -/
def dvrHigherUnitQuotientInverseLimit_eval
    {O : Type*} [CommRing O] (π : O) (n : ℕ) :
    dvrHigherUnitQuotientInverseLimit π →*
      Oˣ ⧸ higherUnitSubgroup π (n + 1) where
  toFun x :=
    (dvrHigherUnitQuotientInverseLimitCompatibleFamiliesEquiv π x).1 n
  map_one' := by rfl
  map_mul' _ _ := by rfl

/-- Evaluation of a higher-unit inverse-limit family returns its selected quotient component. -/
@[simp]
theorem dvrHigherUnitQuotientInverseLimit_eval_mk
    {O : Type*} [CommRing O] (π : O)
    (x : ∀ n : ℕ, Oˣ ⧸ higherUnitSubgroup π (n + 1))
    (compatible : ∀ {m n : ℕ} (hmn : m ≤ n),
      dvrHigherUnitQuotientTransition π hmn (x n) = x m)
    (n : ℕ) :
    dvrHigherUnitQuotientInverseLimit_eval π n
        (dvrHigherUnitQuotientInverseLimit_mk π x compatible) = x n := by
  rfl

/-- Higher-unit inverse-limit elements are determined by their evaluations at every level. -/
@[ext]
theorem dvrHigherUnitQuotientInverseLimit_ext
    {O : Type*} [CommRing O] (π : O)
    {x y : dvrHigherUnitQuotientInverseLimit π}
    (h : ∀ n : ℕ, dvrHigherUnitQuotientInverseLimit_eval π n x =
      dvrHigherUnitQuotientInverseLimit_eval π n y) :
    x = y := by
  apply (dvrHigherUnitQuotientInverseLimitCompatibleFamiliesEquiv π).injective
  apply Subtype.ext
  funext n
  exact h n

/-- Higher-unit evaluation is compatible with quotient transition maps. -/
theorem dvrHigherUnitQuotientInverseLimit_eval_transition
    {O : Type*} [CommRing O] (π : O)
    {m n : ℕ} (hmn : m ≤ n)
    (x : dvrHigherUnitQuotientInverseLimit π) :
    dvrHigherUnitQuotientTransition π hmn
        (dvrHigherUnitQuotientInverseLimit_eval π n x) =
      dvrHigherUnitQuotientInverseLimit_eval π m x :=
  (dvrHigherUnitQuotientInverseLimitCompatibleFamiliesEquiv π x).2 hmn

/-- The higher-unit inverse limit carries the topology induced by its discrete coordinates. -/
noncomputable instance dvrHigherUnitQuotientInverseLimit.instTopologicalSpace
    {O : Type*} [CommRing O] (π : O) :
    TopologicalSpace (dvrHigherUnitQuotientInverseLimit π) := by
  letI : (n : ℕ) → TopologicalSpace
      (Oˣ ⧸ higherUnitSubgroup π (n + 1)) := fun _ => ⊥
  exact
    (dvrHigherUnitQuotientInverseLimitCompatibleFamiliesEquiv π).topologicalSpace

private noncomputable def
    dvrHigherUnitQuotientInverseLimitRepresentationHomeomorph
    {O : Type*} [CommRing O] (π : O) :
    letI : (n : ℕ) → TopologicalSpace
      (Oˣ ⧸ higherUnitSubgroup π (n + 1)) := fun _ => ⊥
    dvrHigherUnitQuotientInverseLimit π ≃ₜ
      compatibleGroupFamilies
        (fun n : ℕ => Oˣ ⧸ higherUnitSubgroup π (n + 1))
        (fun {_ _} hmn => dvrHigherUnitQuotientTransition π hmn) := by
  letI : (n : ℕ) → TopologicalSpace
      (Oˣ ⧸ higherUnitSubgroup π (n + 1)) := fun _ => ⊥
  exact
    (dvrHigherUnitQuotientInverseLimitCompatibleFamiliesEquiv π).homeomorph

/-- Defines `dvrHigherUnitQuotientInverseLimit_discreteEval`. -/
def dvrHigherUnitQuotientInverseLimit_discreteEval
    {O : Type*} [CommRing O] (π : O) (n : ℕ) :
    dvrHigherUnitQuotientInverseLimit π →
      DiscreteHigherUnitQuotient π (n + 1) :=
  fun x => DiscreteHigherUnitQuotient.of π (n + 1)
    (dvrHigherUnitQuotientInverseLimit_eval π n x)

/-- Every coordinate evaluation from the higher-unit inverse limit to its
discrete quotient is continuous. -/
theorem dvrHigherUnitQuotientInverseLimit_discreteEval_continuous
    {O : Type*} [CommRing O] (π : O) (n : ℕ) :
    Continuous (dvrHigherUnitQuotientInverseLimit_discreteEval π n) := by
  let : (n : ℕ) → TopologicalSpace
      (Oˣ ⧸ higherUnitSubgroup π (n + 1)) := fun _ => ⊥
  let representation :=
    dvrHigherUnitQuotientInverseLimitRepresentationHomeomorph π
  have hraw : Continuous fun x : dvrHigherUnitQuotientInverseLimit π =>
      (dvrHigherUnitQuotientInverseLimitCompatibleFamiliesEquiv π x).1 n :=
    (continuous_apply n).comp
      (continuous_subtype_val.comp representation.continuous)
  have hmodel :=
    (DiscreteHigherUnitQuotient.homeomorph π (n + 1)).symm.continuous.comp
      hraw
  change Continuous (fun x : dvrHigherUnitQuotientInverseLimit π =>
    (DiscreteHigherUnitQuotient.equiv π (n + 1)).symm
      ((dvrHigherUnitQuotientInverseLimitCompatibleFamiliesEquiv π x).1 n)) at hmodel
  change Continuous (fun x : dvrHigherUnitQuotientInverseLimit π =>
    (DiscreteHigherUnitQuotient.equiv π (n + 1)).symm
      ((dvrHigherUnitQuotientInverseLimitCompatibleFamiliesEquiv π x).1 n))
  exact hmodel

/-- A map into the higher-unit inverse limit is continuous exactly when all
of its named discrete coordinates are continuous.  This is the public
universal property of the canonical prodiscrete topology; raw quotient
topology instances remain confined to the proof. -/
theorem dvrHigherUnitQuotientInverseLimit_continuous_iff
    {O : Type*} [CommRing O] {α : Type*} [TopologicalSpace α]
    (π : O) (f : α → dvrHigherUnitQuotientInverseLimit π) :
    Continuous f ↔
      ∀ n : ℕ, Continuous fun x =>
        dvrHigherUnitQuotientInverseLimit_discreteEval π n (f x) := by
  constructor
  · intro hf n
    exact
      (dvrHigherUnitQuotientInverseLimit_discreteEval_continuous π n).comp hf
  · intro h
    let : (n : ℕ) → TopologicalSpace
        (Oˣ ⧸ higherUnitSubgroup π (n + 1)) := fun _ => ⊥
    let : (n : ℕ) → DiscreteTopology
        (Oˣ ⧸ higherUnitSubgroup π (n + 1)) := fun _ => ⟨rfl⟩
    let representation :=
      dvrHigherUnitQuotientInverseLimitRepresentationHomeomorph π
    have hrepresentation : Continuous fun x => representation (f x) :=
      Continuous.subtype_mk
        (continuous_pi fun n => by
          have hraw :=
            (DiscreteHigherUnitQuotient.homeomorph π (n + 1)).continuous.comp
              (h n)
          change Continuous fun x =>
            dvrHigherUnitQuotientInverseLimit_eval π n (f x)
          exact hraw)
        (fun x => by
          change ∀ {i j : ℕ} (hij : i ≤ j),
            dvrHigherUnitQuotientTransition π hij
                ((dvrHigherUnitQuotientInverseLimitCompatibleFamiliesEquiv π
                  (f x)).1 j) =
              (dvrHigherUnitQuotientInverseLimitCompatibleFamiliesEquiv π
                (f x)).1 i
          exact
            (dvrHigherUnitQuotientInverseLimitCompatibleFamiliesEquiv π
              (f x)).2)
    have hback := representation.symm.continuous.comp hrepresentation
    exact hback.congr fun x => representation.symm_apply_apply (f x)

/-- The canonical homomorphism
`Oˣ → lim_n Oˣ/U^(n+1)`. -/
def unitsToHigherUnitQuotientInverseLimit
    {O : Type*} [CommRing O] (π : O) :
    Oˣ →* dvrHigherUnitQuotientInverseLimit π where
  toFun u := dvrHigherUnitQuotientInverseLimit_mk π
    (fun _ => QuotientGroup.mk u)
    (fun {m n} hmn =>
      dvrHigherUnitQuotientTransition_mk π (m := m) (n := n) hmn u)
  map_one' := by ext n; rfl
  map_mul' u v := by ext n; rfl

/-- The finite-stage isomorphisms
`Oˣ/U^(n+1) ≃ (O/π^(n+1)O)ˣ` commute with the projective transition maps. -/
theorem higherUnitQuotient_finiteStage_compat
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) {m n : ℕ} (hmn : m ≤ n)
    (q : Oˣ ⧸ higherUnitSubgroup π (n + 1)) :
    units_quotient_equiv hπ
        (Nat.succ_pos m)
        (dvrHigherUnitQuotientTransition π hmn q) =
      Units.map (dvrPowerIdealUnitTransition π hmn).toMonoidHom
        (units_quotient_equiv hπ
          (Nat.succ_pos n) q) := by
  refine QuotientGroup.induction_on q ?_
  intro u
  rw [dvrHigherUnitQuotientTransition_mk]
  ext
  simp [units_quotient_equiv_mk,
    dvrPowerIdealUnitTransition, unitReduction]

/-- The direct quotient-system `lim Oˣ/U^(n+1)` is equivalent to the finite
quotient-unit limit `lim (O/π^(n+1)O)ˣ`. -/
def higherUnitQuotientInverseLimitEquivPowerIdealUnitInverseLimit
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) :
    dvrHigherUnitQuotientInverseLimit π ≃*
      dvrPowerIdealUnitInverseLimit π :=
  (dvrHigherUnitQuotientInverseLimitRepresentation π).trans
    ((compatibleGroupFamiliesMulEquiv
      (fun n : ℕ => Oˣ ⧸ higherUnitSubgroup π (n + 1))
      (fun n : ℕ => (O ⧸ uniformizerPowerIdeal π (n + 1))ˣ)
      (fun {_ _} hmn => dvrHigherUnitQuotientTransition π hmn)
      (fun {_ _} hmn =>
        Units.map
          (dvrPowerIdealUnitTransition π hmn).toMonoidHom)
      (fun n => units_quotient_equiv hπ
        (Nat.succ_pos n))
      (by
        intro m n hmn q
        exact (higherUnitQuotient_finiteStage_compat
          hπ hmn q).symm)).trans
      (dvrPowerIdealUnitInverseLimitRepresentation π).symm)

/-- The adic inverse-limit equivalence, direct unit-quotient form:
if `O` is complete for the `(π)`-adic topology, then `Oˣ` is isomorphic to
the projective limit `lim_n Oˣ/U^(n+1)`. -/
def dvrUnitsEquivHigherUnitQuotientInverseLimit
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) [IsAdicComplete (uniformizerPowerIdeal π 1) O] :
    Oˣ ≃* dvrHigherUnitQuotientInverseLimit π :=
  ((unitsEquivPositiveUnitInverseLimit (uniformizerPowerIdeal π 1)).trans
    (adicPositiveUnitInverseLimitEquivDVRPowerIdealUnitInverseLimit π)).trans
    (higherUnitQuotientInverseLimitEquivPowerIdealUnitInverseLimit hπ).symm

/-- The direct unit-quotient inverse-limit isomorphism is the canonical
map, coordinatewise `u ↦ u mod U^(n+1)`. -/
theorem dvrUnitsEquivHigherUnitQuotientInverseLimit_apply
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) [IsAdicComplete (uniformizerPowerIdeal π 1) O]
    (u : Oˣ) (n : ℕ) :
    dvrHigherUnitQuotientInverseLimit_eval π n
        (dvrUnitsEquivHigherUnitQuotientInverseLimit hπ u) =
      QuotientGroup.mk u := by
  apply
    (units_quotient_equiv hπ
      (Nat.succ_pos n)).injective
  change units_quotient_equiv hπ (Nat.succ_pos n)
      (dvrHigherUnitQuotientInverseLimit_eval π n
        (dvrUnitsEquivHigherUnitQuotientInverseLimit hπ u)) =
    units_quotient_equiv hπ (Nat.succ_pos n)
      (QuotientGroup.mk u)
  rw [units_quotient_equiv_mk]
  change dvrPowerIdealUnitInverseLimit_eval π n
      ((higherUnitQuotientInverseLimitEquivPowerIdealUnitInverseLimit hπ)
        (dvrUnitsEquivHigherUnitQuotientInverseLimit hπ u)) =
    unitReduction (uniformizerPowerIdeal π (n + 1)) u
  simp [dvrUnitsEquivHigherUnitQuotientInverseLimit,
    adicPositiveUnitInverseLimitEquivDVRPowerIdealUnitInverseLimit,
    unitReduction]
  ext
  change (Ideal.quotientEquivAlgOfEq O
      (dvrPowerIdeal_one_pow π (n + 1)))
        (Ideal.Quotient.mk ((uniformizerPowerIdeal π 1) ^ (n + 1)) (u : O)) =
    Ideal.Quotient.mk (uniformizerPowerIdeal π (n + 1)) (u : O)
  rw [Ideal.quotientEquivAlgOfEq_mk]

/-- Equality in the finite higher-unit quotient is exactly congruence modulo
`π^nO` on the underlying elements. -/
theorem higherUnitQuotient_mk_eq_mk_iff_sub_mem
    {O : Type*} [CommRing O] (π : O) (n : ℕ) (u v : Oˣ) :
    (QuotientGroup.mk v : Oˣ ⧸ higherUnitSubgroup π n) =
        QuotientGroup.mk u ↔
      (v : O) - (u : O) ∈ uniformizerPowerIdeal π n := by
  constructor
  · intro h
    have hdiv : v / u ∈ higherUnitSubgroup π n := by
      exact (QuotientGroup.eq_iff_div_mem
        (N := higherUnitSubgroup π n) (x := v) (y := u)).1 h
    have hmem :
        ((v / u : Oˣ) : O) - 1 ∈ uniformizerPowerIdeal π n :=
      (mem_higherUnitSubgroup_iff_sub_one_mem_powerIdeal
        (π := π) (n := n) (u := v / u)).1 hdiv
    have hmul :
        (((v / u : Oˣ) : O) - 1) * (u : O) ∈
          uniformizerPowerIdeal π n :=
      (uniformizerPowerIdeal π n).mul_mem_right (u : O) hmem
    have hcalc :
        (((v / u : Oˣ) : O) - 1) * (u : O) = (v : O) - (u : O) := by
      calc
        (((v / u : Oˣ) : O) - 1) * (u : O)
            = ((v : O) * ((u⁻¹ : Oˣ) : O) - 1) * (u : O) := rfl
        _ = (v : O) * (((u⁻¹ : Oˣ) : O) * (u : O)) - (u : O) := by ring
        _ = (v : O) - (u : O) := by simp
    simpa [hcalc] using hmul
  · intro hsub
    have hmem :
        ((v / u : Oˣ) : O) - 1 ∈ uniformizerPowerIdeal π n := by
      have hmul :
          ((v : O) - (u : O)) * ((u⁻¹ : Oˣ) : O) ∈
            uniformizerPowerIdeal π n :=
        (uniformizerPowerIdeal π n).mul_mem_right ((u⁻¹ : Oˣ) : O) hsub
      convert hmul using 1
      calc
        ((v / u : Oˣ) : O) - 1
            = (v : O) * ((u⁻¹ : Oˣ) : O) - 1 := rfl
        _ = (v : O) * ((u⁻¹ : Oˣ) : O) -
              (u : O) * ((u⁻¹ : Oˣ) : O) := by simp
        _ = ((v : O) - (u : O)) * ((u⁻¹ : Oˣ) : O) := by ring
    have hdiv : v / u ∈ higherUnitSubgroup π n :=
      (mem_higherUnitSubgroup_iff_sub_one_mem_powerIdeal
        (π := π) (n := n) (u := v / u)).2 hmem
    exact (QuotientGroup.eq_iff_div_mem
      (N := higherUnitSubgroup π n) (x := v) (y := u)).2 hdiv

/-- The topology on a unit group induced by an explicitly chosen adic
topology on its ring. -/
@[reducible]
noncomputable def adicUnitsTopology
    {O : Type*} [CommRing O] (I : Ideal O) : TopologicalSpace Oˣ := by
  letI : TopologicalSpace O := I.adicTopology
  exact inferInstance

/-- Reduction to a higher-unit quotient is continuous for the adic topology
on `Oˣ` and the discrete topology on the finite quotient. -/
private theorem higherUnitQuotient_mk_continuous_adic_raw
    {O : Type*} [CommRing O] (π : O) (n : ℕ) :
    @Continuous Oˣ (Oˣ ⧸ higherUnitSubgroup π n)
      (adicUnitsTopology (uniformizerPowerIdeal π 1))
      (⊥ : TopologicalSpace (Oˣ ⧸ higherUnitSubgroup π n))
      (fun u : Oˣ =>
        (QuotientGroup.mk u : Oˣ ⧸ higherUnitSubgroup π n)) := by
  let : TopologicalSpace O := (uniformizerPowerIdeal π 1).adicTopology
  let : TopologicalSpace (Oˣ ⧸ higherUnitSubgroup π n) := ⊥
  let : DiscreteTopology (Oˣ ⧸ higherUnitSubgroup π n) := ⟨rfl⟩
  rw [continuous_iff_continuousAt]
  intro u
  change Filter.Tendsto
    (fun v : Oˣ => (QuotientGroup.mk v :
      Oˣ ⧸ higherUnitSubgroup π n)) (𝓝 u)
    (𝓝 (QuotientGroup.mk u : Oˣ ⧸ higherUnitSubgroup π n))
  rw [@nhds_discrete (Oˣ ⧸ higherUnitSubgroup π n) _ _]
  rw [Filter.tendsto_def]
  intro s hs
  rw [mem_pure] at hs
  let ball : Set O :=
    (fun y => (u : O) + y) ''
      (((uniformizerPowerIdeal π 1) ^ n : Ideal O) : Set O)
  have hball : ball ∈ 𝓝 (u : O) :=
    (Ideal.hasBasis_nhds_adic (uniformizerPowerIdeal π 1) (u : O)).mem_iff.mpr
      ⟨n, trivial, subset_rfl⟩
  have hpre : {v : Oˣ | (v : O) ∈ ball} ∈ 𝓝 u :=
    Units.continuous_val.continuousAt hball
  exact mem_of_superset hpre (by
    intro v hv
    rcases hv with ⟨z, hz, hzv⟩
    have hsub : (v : O) - (u : O) ∈ uniformizerPowerIdeal π n := by
      rw [← dvrPowerIdeal_one_pow π n]
      have hz_eq : (v : O) - (u : O) = z := by
        rw [← hzv]
        ring
      simpa [hz_eq] using hz
    have hq :
        (QuotientGroup.mk v : Oˣ ⧸ higherUnitSubgroup π n) =
          QuotientGroup.mk u :=
      (higherUnitQuotient_mk_eq_mk_iff_sub_mem
        π n u v).2 hsub
    simpa [hq] using hs)

/-- The quotient map from adic units to a named discrete higher-unit stage
is continuous. -/
theorem higherUnitQuotient_mk_continuous_adic
    {O : Type*} [CommRing O] (π : O) (n : ℕ) :
    Continuous fun u : WithTopology Oˣ
        (adicUnitsTopology (uniformizerPowerIdeal π 1)) =>
      DiscreteHigherUnitQuotient.of π n
        (QuotientGroup.mk u.ofTopology : Oˣ ⧸ higherUnitSubgroup π n) := by
  let : TopologicalSpace O := (uniformizerPowerIdeal π 1).adicTopology
  let : TopologicalSpace (Oˣ ⧸ higherUnitSubgroup π n) := ⊥
  let : DiscreteTopology (Oˣ ⧸ higherUnitSubgroup π n) := ⟨rfl⟩
  have hraw := higherUnitQuotient_mk_continuous_adic_raw π n
  have hunderlying : Continuous fun u :
      WithTopology Oˣ
      (adicUnitsTopology (uniformizerPowerIdeal π 1)) =>
        (QuotientGroup.mk u.ofTopology : Oˣ ⧸ higherUnitSubgroup π n) :=
    hraw.comp (WithTopology.continuous_ofTopology
      (adicUnitsTopology (uniformizerPowerIdeal π 1)))
  have hmodel :=
    (DiscreteHigherUnitQuotient.homeomorph π n).symm.continuous.comp
      hunderlying
  change Continuous (fun u : WithTopology Oˣ
      (adicUnitsTopology (uniformizerPowerIdeal π 1)) =>
    (DiscreteHigherUnitQuotient.equiv π n).symm
      (QuotientGroup.mk u.ofTopology : Oˣ ⧸ higherUnitSubgroup π n)) at hmodel
  simpa only [DiscreteHigherUnitQuotient.equiv_symm_apply] using hmodel

private noncomputable def unitsCompatibleFamiliesHomeomorph
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) [IsAdicComplete (uniformizerPowerIdeal π 1) O] :
    letI : TopologicalSpace O := (uniformizerPowerIdeal π 1).adicTopology
    letI : (n : ℕ) →
      TopologicalSpace (Oˣ ⧸ higherUnitSubgroup π (n + 1)) := fun _ => ⊥
    Oˣ ≃ₜ compatibleGroupFamilies
      (fun n : ℕ => Oˣ ⧸ higherUnitSubgroup π (n + 1))
      (fun {_ _} hmn => dvrHigherUnitQuotientTransition π hmn) := by
  letI : TopologicalSpace O := (uniformizerPowerIdeal π 1).adicTopology
  letI : (n : ℕ) →
      TopologicalSpace (Oˣ ⧸ higherUnitSubgroup π (n + 1)) := fun _ => ⊥
  letI : (n : ℕ) →
      DiscreteTopology (Oˣ ⧸ higherUnitSubgroup π (n + 1)) :=
    fun _ => ⟨rfl⟩
  let e := (dvrUnitsEquivHigherUnitQuotientInverseLimit hπ).trans
    (dvrHigherUnitQuotientInverseLimitRepresentation π)
  let c := (dvrHigherUnitQuotientInverseLimitRepresentation π).toMonoidHom.comp
    (unitsToHigherUnitQuotientInverseLimit π)
  refine
    { toFun := fun u => c u
      invFun := fun q => e.symm q
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · intro u
    have hc : c u = e u := by
      ext n
      exact (dvrUnitsEquivHigherUnitQuotientInverseLimit_apply
        hπ u n).symm
    change e.symm (c u) = u
    rw [hc]
    exact e.left_inv u
  · intro q
    ext n
    change (QuotientGroup.mk (e.symm q) :
        Oˣ ⧸ higherUnitSubgroup π (n + 1)) = q.1 n
    calc
      (QuotientGroup.mk (e.symm q) :
          Oˣ ⧸ higherUnitSubgroup π (n + 1)) =
          (e (e.symm q)).1 n :=
        (dvrUnitsEquivHigherUnitQuotientInverseLimit_apply
          hπ (e.symm q) n).symm
      _ = q.1 n := by simp [e.apply_symm_apply q]
  · change Continuous fun u : Oˣ => c u
    exact Continuous.subtype_mk
      (continuous_pi fun n => by
        simpa [c, unitsToHigherUnitQuotientInverseLimit] using
          (higherUnitQuotient_mk_continuous_adic_raw π (n + 1)))
      (by
        intro u m n hmn
        exact dvrHigherUnitQuotientTransition_mk π hmn u)
  · apply Units.continuous_iff.mpr
    constructor
    · rw [continuous_iff_continuousAt]
      intro q
      rw [ContinuousAt, Filter.tendsto_def]
      intro s hs
      rcases (Ideal.hasBasis_nhds_adic (uniformizerPowerIdeal π 1)
          ((e.symm q : Oˣ) : O)).mem_iff.mp hs with
        ⟨n, _hn, hns⟩
      let cylinder : Set (compatibleGroupFamilies
          (fun n : ℕ => Oˣ ⧸ higherUnitSubgroup π (n + 1))
          (fun {_ _} hmn => dvrHigherUnitQuotientTransition π hmn)) :=
        {q' | q'.1 n = q.1 n}
      have hcont_coord :
          Continuous fun q' : compatibleGroupFamilies
              (fun n : ℕ => Oˣ ⧸ higherUnitSubgroup π (n + 1))
              (fun {_ _} hmn => dvrHigherUnitQuotientTransition π hmn) =>
            q'.1 n := by
        exact (continuous_apply n).comp continuous_subtype_val
      have hcyl_open : IsOpen cylinder := by
        exact
          (isOpen_discrete
            ({q.1 n} : Set (Oˣ ⧸ higherUnitSubgroup π (n + 1)))).preimage
              hcont_coord
      have hqmem : q ∈ cylinder := rfl
      exact mem_of_superset (hcyl_open.mem_nhds hqmem) (by
        intro q' hq'
        apply hns
        have hmk :
            (QuotientGroup.mk (e.symm q') :
                Oˣ ⧸ higherUnitSubgroup π (n + 1)) =
              QuotientGroup.mk (e.symm q) := by
          calc
            (QuotientGroup.mk (e.symm q') :
                Oˣ ⧸ higherUnitSubgroup π (n + 1)) =
                (e (e.symm q')).1 n :=
              (dvrUnitsEquivHigherUnitQuotientInverseLimit_apply
                hπ (e.symm q') n).symm
            _ = q'.1 n := by simp [e.apply_symm_apply q']
            _ = q.1 n := hq'
            _ = (e (e.symm q)).1 n := by simp [e.apply_symm_apply q]
            _ = QuotientGroup.mk (e.symm q) :=
              dvrUnitsEquivHigherUnitQuotientInverseLimit_apply
                hπ (e.symm q) n
        have hsub_succ :
            ((e.symm q' : Oˣ) : O) - ((e.symm q : Oˣ) : O) ∈
              uniformizerPowerIdeal π (n + 1) :=
          (higherUnitQuotient_mk_eq_mk_iff_sub_mem
            π (n + 1) (e.symm q) (e.symm q')).1 hmk
        have hsub :
            ((e.symm q' : Oˣ) : O) - ((e.symm q : Oˣ) : O) ∈
              (uniformizerPowerIdeal π 1) ^ n := by
          rw [dvrPowerIdeal_one_pow π n]
          exact dvrPowerIdeal_le_of_le π (Nat.le_succ n) hsub_succ
        refine ⟨((e.symm q' : Oˣ) : O) - ((e.symm q : Oˣ) : O), hsub, ?_⟩
        change ((e.symm q : Oˣ) : O) +
            (((e.symm q' : Oˣ) : O) - ((e.symm q : Oˣ) : O)) =
          ((e.symm q' : Oˣ) : O)
        ring)
    · rw [continuous_iff_continuousAt]
      intro q
      rw [ContinuousAt, Filter.tendsto_def]
      intro s hs
      rcases (Ideal.hasBasis_nhds_adic (uniformizerPowerIdeal π 1)
          (((e.symm q)⁻¹ : Oˣ) : O)).mem_iff.mp hs with
        ⟨n, _hn, hns⟩
      let cylinder : Set (compatibleGroupFamilies
          (fun n : ℕ => Oˣ ⧸ higherUnitSubgroup π (n + 1))
          (fun {_ _} hmn => dvrHigherUnitQuotientTransition π hmn)) :=
        {q' | q'.1 n = q.1 n}
      have hcont_coord :
          Continuous fun q' : compatibleGroupFamilies
              (fun n : ℕ => Oˣ ⧸ higherUnitSubgroup π (n + 1))
              (fun {_ _} hmn => dvrHigherUnitQuotientTransition π hmn) =>
            q'.1 n := by
        exact (continuous_apply n).comp continuous_subtype_val
      have hcyl_open : IsOpen cylinder := by
        exact
          (isOpen_discrete
            ({q.1 n} : Set (Oˣ ⧸ higherUnitSubgroup π (n + 1)))).preimage
              hcont_coord
      have hqmem : q ∈ cylinder := rfl
      exact mem_of_superset (hcyl_open.mem_nhds hqmem) (by
        intro q' hq'
        apply hns
        have hmk :
            (QuotientGroup.mk (e.symm q') :
                Oˣ ⧸ higherUnitSubgroup π (n + 1)) =
              QuotientGroup.mk (e.symm q) := by
          calc
            (QuotientGroup.mk (e.symm q') :
                Oˣ ⧸ higherUnitSubgroup π (n + 1)) =
                (e (e.symm q')).1 n :=
              (dvrUnitsEquivHigherUnitQuotientInverseLimit_apply
                hπ (e.symm q') n).symm
            _ = q'.1 n := by simp [e.apply_symm_apply q']
            _ = q.1 n := hq'
            _ = (e (e.symm q)).1 n := by simp [e.apply_symm_apply q]
            _ = QuotientGroup.mk (e.symm q) :=
              dvrUnitsEquivHigherUnitQuotientInverseLimit_apply
                hπ (e.symm q) n
        have hinv_mk :
            (QuotientGroup.mk ((e.symm q')⁻¹ : Oˣ) :
                Oˣ ⧸ higherUnitSubgroup π (n + 1)) =
              QuotientGroup.mk ((e.symm q)⁻¹ : Oˣ) := by
          simpa using congrArg Inv.inv hmk
        have hinv_sub_succ :
            (((e.symm q')⁻¹ : Oˣ) : O) - (((e.symm q)⁻¹ : Oˣ) : O) ∈
              uniformizerPowerIdeal π (n + 1) :=
          (higherUnitQuotient_mk_eq_mk_iff_sub_mem
            π (n + 1) ((e.symm q)⁻¹ : Oˣ) ((e.symm q')⁻¹ : Oˣ)).1 hinv_mk
        have hinv_sub :
            (((e.symm q')⁻¹ : Oˣ) : O) - (((e.symm q)⁻¹ : Oˣ) : O) ∈
              (uniformizerPowerIdeal π 1) ^ n := by
          rw [dvrPowerIdeal_one_pow π n]
          exact dvrPowerIdeal_le_of_le π (Nat.le_succ n)
            hinv_sub_succ
        refine
          ⟨(((e.symm q')⁻¹ : Oˣ) : O) - (((e.symm q)⁻¹ : Oˣ) : O),
            hinv_sub, ?_⟩
        change (((e.symm q)⁻¹ : Oˣ) : O) +
            ((((e.symm q')⁻¹ : Oˣ) : O) - (((e.symm q)⁻¹ : Oˣ) : O)) =
          (((e.symm q')⁻¹ : Oˣ) : O)
        ring)

/-- The unit-group inverse-limit homeomorphism with the adic source and
prodiscrete target fixed at the type level. -/
noncomputable def unitsEquivHigherUnitQuotientInverseLimitHomeomorph
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π)
    [IsAdicComplete (uniformizerPowerIdeal π 1) O] :
    WithTopology Oˣ
        (adicUnitsTopology (uniformizerPowerIdeal π 1)) ≃ₜ
      dvrHigherUnitQuotientInverseLimit π := by
  letI : TopologicalSpace O := (uniformizerPowerIdeal π 1).adicTopology
  letI : (n : ℕ) → TopologicalSpace
      (Oˣ ⧸ higherUnitSubgroup π (n + 1)) := fun _ => ⊥
  let source := WithTopology.homeomorph
    (α := Oˣ)
    (topology := adicUnitsTopology (uniformizerPowerIdeal π 1))
  let algebraic := unitsCompatibleFamiliesHomeomorph hπ
  let target := dvrHigherUnitQuotientInverseLimitRepresentationHomeomorph π
  exact source.trans (algebraic.trans target.symm)

/-- Complete-DVF specialization of the adic inverse-limit equivalence: the valuation ring is canonically
isomorphic to its maximal-ideal adic completion. -/
def completeDVF_valuationSubring_adicCompletionAlgEquiv
    {K : Type u} [Field K]
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) :
    F.valuationSubring ≃ₐ[F.valuationSubring]
      AdicCompletion F.maximalIdeal F.valuationSubring :=
  adicCompletionAlgEquiv F.maximalIdeal

/-- Complete-DVF specialization of the adic inverse-limit equivalence: the valuation ring is the explicit
projective limit of its finite quotients by powers of the maximal ideal. -/
def completeDVF_valuationSubring_quotientInverseLimitEquiv
    {K : Type u} [Field K]
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) :
    F.valuationSubring ≃+*
      adicQuotientInverseLimit F.maximalIdeal :=
  adicQuotientInverseLimitEquiv F.maximalIdeal

/-- The complete-DVF projective-limit isomorphism is coordinatewise reduction
modulo `𝔭^n`. -/
theorem completeDVF_valuationSubring_quotientInverseLimitEquiv_apply
    {K : Type u} [Field K]
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)
    (x : F.valuationSubring) (n : ℕ) :
    adicQuotientInverseLimit_eval F.maximalIdeal n
        (completeDVF_valuationSubring_quotientInverseLimitEquiv F x) =
      Ideal.Quotient.mk (F.maximalIdeal ^ n) x := by
  exact adicQuotientInverseLimitEquiv_apply F.maximalIdeal x n

/-- Complete-DVF specialization of the adic inverse-limit equivalence, units of the valuation ring agree
with units of its maximal-ideal adic completion. -/
def completeDVF_units_adicCompletionUnitsEquiv
    {K : Type u} [Field K]
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) :
    F.valuationSubringˣ ≃*
      (AdicCompletion F.maximalIdeal F.valuationSubring)ˣ :=
  adicCompletionUnitsEquiv F.maximalIdeal

/-- The complete-DVF unit equivalence is induced by the canonical valuation-ring
map into the adic completion. -/
theorem completeDVF_units_adicCompletionUnitsEquiv_apply
    {K : Type u} [Field K]
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)
    (u : F.valuationSubringˣ) :
    (completeDVF_units_adicCompletionUnitsEquiv F u :
      AdicCompletion F.maximalIdeal F.valuationSubring) =
      completeDVF_valuationSubring_adicCompletionAlgEquiv F
        (u : F.valuationSubring) := by
  rfl

/-- Complete-DVF specialization of the adic inverse-limit equivalence, unit-coordinate injectivity. -/
theorem completeDVF_units_coordinates_injective
    {K : Type u} [Field K]
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)
    {u₁ u₂ : F.valuationSubringˣ}
    (h :
      ∀ n : ℕ,
        unitReduction (F.maximalIdeal ^ n) u₁ =
          unitReduction (F.maximalIdeal ^ n) u₂) :
    u₁ = u₂ := by
  exact adicCompletion_units_coordinates_injective
    F.maximalIdeal h

/-- Complete-DVF specialization of the adic inverse-limit equivalence, unit-coordinate surjectivity against
the adic completion. -/
theorem completeDVF_units_coordinates_surjective
    {K : Type u} [Field K]
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)
    (z : (AdicCompletion F.maximalIdeal F.valuationSubring)ˣ) :
    ∃ u : F.valuationSubringˣ,
      completeDVF_units_adicCompletionUnitsEquiv F u = z ∧
        ∀ n : ℕ,
          unitReduction (F.maximalIdeal ^ n) u =
            Units.map (AdicCompletion.evalₐ F.maximalIdeal n).toMonoidHom z := by
  exact adicCompletion_units_coordinates_surjective F.maximalIdeal z

/-- Complete-DVF specialization of the adic inverse-limit equivalence: units of the valuation ring are the
projective limit of the units of the finite quotient rings. -/
def completeDVF_unitsEquivUnitInverseLimit
    {K : Type u} [Field K]
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) :
    F.valuationSubringˣ ≃*
      adicUnitInverseLimit F.maximalIdeal :=
  unitsEquivUnitInverseLimit F.maximalIdeal

/-- The complete-DVF unit projective-limit isomorphism is coordinatewise unit
reduction modulo `𝔭^n`. -/
theorem completeDVF_unitsEquivUnitInverseLimit_apply
    {K : Type u} [Field K]
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)
    (u : F.valuationSubringˣ) (n : ℕ) :
    adicUnitInverseLimit_eval F.maximalIdeal n
        (completeDVF_unitsEquivUnitInverseLimit F u) =
      unitReduction (F.maximalIdeal ^ n) u := by
  exact unitsEquivUnitInverseLimit_apply F.maximalIdeal u n

/-- Complete-DVF specialization of the adic inverse-limit equivalence, finite unit quotient form:
`𝒪ˣ / ker(𝒪ˣ → (𝒪/𝔭ⁿ)ˣ) ≃ (𝒪/𝔭ⁿ)ˣ` for `n ≥ 1`. -/
noncomputable def completeDVF_unitsModMaximalIdealPowEquiv
    {K : Type u} [Field K]
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)
    {n : ℕ} (hn : 1 ≤ n) :
    F.valuationSubringˣ ⧸
        (unitReduction (F.maximalIdeal ^ n)).ker ≃*
      (F.valuationSubring ⧸ F.maximalIdeal ^ n)ˣ := by
  exact unitsModMaximalIdealPowEquiv
    (R := F.valuationSubring) hn

/-- The complete-DVF finite unit quotient equivalence is induced by reduction
modulo `𝔭ⁿ`. -/
theorem completeDVF_unitsModMaximalIdealPowEquiv_mk
    {K : Type u} [Field K]
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)
    {n : ℕ} (hn : 1 ≤ n) (u : F.valuationSubringˣ) :
    completeDVF_unitsModMaximalIdealPowEquiv F hn
        (QuotientGroup.mk u) =
      unitReduction (F.maximalIdeal ^ n) u := by
  exact unitsModMaximalIdealPowEquiv_mk
    (R := F.valuationSubring) hn u

/-- The adic inverse-limit equivalence, injectivity source: an element of the valuation ring is
determined by all of its reductions modulo powers of the maximal ideal. -/
theorem completeDVF_valuationSubring_quotient_coordinates_injective
    {K : Type u} [Field K]
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)
    {x y : F.valuationSubring}
    (h :
      ∀ n : ℕ,
        Ideal.Quotient.mk (F.maximalIdeal ^ n) x =
          Ideal.Quotient.mk (F.maximalIdeal ^ n) y) :
    x = y := by
  have hsub :
      ∀ n : ℕ, x - y ∈ F.maximalIdeal ^ n := by
    intro n
    exact
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem
        (I := F.maximalIdeal ^ n)
        (x := x) (y := y)).1 (h n)
  exact sub_eq_zero.mp (F.eq_zero_of_mem_maximalIdeal_pow_all hsub)

/-- The adic inverse-limit equivalence, unit injectivity source: a unit is determined by all of
its reductions modulo powers of the maximal ideal. -/
theorem completeDVF_units_quotient_coordinates_injective
    {K : Type u} [Field K]
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)
    {u₁ u₂ : F.valuationSubringˣ}
    (h :
      ∀ n : ℕ,
        Ideal.Quotient.mk (F.maximalIdeal ^ n) (u₁ : F.valuationSubring) =
          Ideal.Quotient.mk (F.maximalIdeal ^ n) (u₂ : F.valuationSubring)) :
    u₁ = u₂ := by
  exact F.unit_eq_of_idealQuotient_eq_all h

/-! ### Direct complete-valued-field form of the adic inverse-limit equivalence -/

/-- The adic inverse-limit equivalence, direct algebraic endpoint from valued-field completeness:
the canonical map from the valuation ring to the positive-indexed inverse
limit of its maximal-ideal quotients is a ring equivalence. -/
def completeValuedField_valuationSubringEquivPositiveQuotientInverseLimit
    {K : Type u} [Field K] {Gamma : Type v}
    [LinearOrderedCommGroupWithZero Gamma] [MulArchimedean Gamma]
    [Valued K Gamma]
    [(Valued.v : Valuation K Gamma).IsRankOneDiscrete]
    [CompleteSpace K] :
    let val := (Valued.v : Valuation K Gamma)
    let O := val.valuationSubring
    let m := IsLocalRing.maximalIdeal O
    O ≃+* adicPositiveQuotientInverseLimit m := by
  dsimp only
  let F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K :=
    completeDVFOfCompleteValuedField (K := K) (Gamma := Gamma)
  exact
    (completeDVF_valuationSubring_quotientInverseLimitEquiv F).trans
      (adicQuotientInverseLimitEquivPositive F.maximalIdeal)

/-- The direct valuation-ring equivalence is the canonical map,
coordinatewise reduction modulo `𝓅^(n+1)`. -/
theorem completeValuedField_valuationSubringEquivPositiveQuotientInverseLimit_apply
    {K : Type u} [Field K] {Gamma : Type v}
    [LinearOrderedCommGroupWithZero Gamma] [MulArchimedean Gamma]
    [Valued K Gamma]
    [(Valued.v : Valuation K Gamma).IsRankOneDiscrete]
    [CompleteSpace K]
    (x : (Valued.v : Valuation K Gamma).valuationSubring) (n : ℕ) :
    adicPositiveQuotientInverseLimit_eval
        (IsLocalRing.maximalIdeal
          (Valued.v : Valuation K Gamma).valuationSubring) n
        (completeValuedField_valuationSubringEquivPositiveQuotientInverseLimit
          (K := K) (Gamma := Gamma) x) =
      Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal
          (Valued.v : Valuation K Gamma).valuationSubring) ^ (n + 1)) x := by
  let val := (Valued.v : Valuation K Gamma)
  let O := val.valuationSubring
  let m := IsLocalRing.maximalIdeal O
  let : IsAdicComplete m O :=
    rankOneDiscreteValuationSubring_isAdicComplete
      (K := K) (Gamma := Gamma)
  change
    adicPositiveQuotientInverseLimit_eval m n
        (adicPositiveQuotientInverseLimitEquiv m x) =
      Ideal.Quotient.mk (m ^ (n + 1)) x
  exact adicPositiveQuotientInverseLimitEquiv_apply m x n

/-- The adic inverse-limit equivalence, direct topological endpoint: with the native valued
topology on the valuation ring and discrete topology at every finite stage,
the canonical ring equivalence is a homeomorphism. -/
def completeValuedField_valuationSubringPositiveQuotientInverseLimitHomeomorph
    {K : Type u} [Field K] {Gamma : Type v}
    [LinearOrderedCommGroupWithZero Gamma] [MulArchimedean Gamma]
    [Valued K Gamma]
    [(Valued.v : Valuation K Gamma).IsRankOneDiscrete]
    [CompleteSpace K] :
    let val := (Valued.v : Valuation K Gamma)
    let O := val.valuationSubring
    let m := IsLocalRing.maximalIdeal O
    O ≃ₜ adicPositiveQuotientInverseLimit m := by
  dsimp only
  let val := (Valued.v : Valuation K Gamma)
  let O := val.valuationSubring
  let m := IsLocalRing.maximalIdeal O
  letI : IsAdicComplete m O :=
    rankOneDiscreteValuationSubring_isAdicComplete
      (K := K) (Gamma := Gamma)
  have hadic : IsAdic m :=
    rankOneDiscreteValuationSubring_isAdic
      (K := K) (Gamma := Gamma)
  let hAdic := adicPositiveQuotientInverseLimitHomeomorph m
  let hNative := hadic.symm ▸ hAdic
  exact
    (WithTopology.homeomorph
      (α := O)
      (topology := (inferInstance : TopologicalSpace O))).symm.trans hNative

/-- A uniformizer of a complete rank-one discrete valued field is irreducible
in its valuation ring. -/
theorem completeValuedField_uniformizer_irreducible
    {K : Type u} [Field K] {Gamma : Type v}
    [LinearOrderedCommGroupWithZero Gamma] [MulArchimedean Gamma]
    [Valued K Gamma]
    [(Valued.v : Valuation K Gamma).IsRankOneDiscrete]
    [CompleteSpace K]
    {pi : (Valued.v : Valuation K Gamma).valuationSubring}
    (hpi : (Valued.v : Valuation K Gamma).IsUniformizer (pi : K)) :
    Irreducible pi := by
  let val := (Valued.v : Valuation K Gamma)
  let F : ValuationTheory.DiscreteValuationField.DVF.{u, v} K :=
    { ValueGroup := Gamma
      valuation := val }
  let : IsDiscreteValuationRing val.valuationSubring :=
    rankOneDiscreteValuationSubring_isDiscreteValuationRing
      (K := K) (Gamma := Gamma)
  exact (IsDiscreteValuationRing.irreducible_iff_uniformizer pi).2
    (F.maximalIdeal_eq_span_uniformizer hpi)

/-- For a uniformizer, the first principal-power ideal is the maximal
ideal of the valuation ring. -/
theorem completeValuedField_uniformizerPowerIdeal_one_eq_maximalIdeal
    {K : Type u} [Field K] {Gamma : Type v}
    [LinearOrderedCommGroupWithZero Gamma] [MulArchimedean Gamma]
    [Valued K Gamma]
    [(Valued.v : Valuation K Gamma).IsRankOneDiscrete]
    [CompleteSpace K]
    {pi : (Valued.v : Valuation K Gamma).valuationSubring}
    (hpi : (Valued.v : Valuation K Gamma).IsUniformizer (pi : K)) :
    uniformizerPowerIdeal pi 1 =
      IsLocalRing.maximalIdeal
        (Valued.v : Valuation K Gamma).valuationSubring := by
  let val := (Valued.v : Valuation K Gamma)
  let F : ValuationTheory.DiscreteValuationField.DVF.{u, v} K :=
    { ValueGroup := Gamma
      valuation := val }
  rw [uniformizerPowerIdeal, pow_one]
  change Ideal.span {pi} =
    IsLocalRing.maximalIdeal
      (Valued.v : Valuation K Gamma).valuationSubring
  have h := F.maximalIdeal_eq_span_uniformizer hpi
  change IsLocalRing.maximalIdeal
      (Valued.v : Valuation K Gamma).valuationSubring =
    Ideal.span {pi} at h
  exact h.symm

/-- Completeness of the valued field supplies completeness for the principal
uniformizer filtration used by the higher-unit quotients. -/
theorem completeValuedField_uniformizerIdeal_isAdicComplete
    {K : Type u} [Field K] {Gamma : Type v}
    [LinearOrderedCommGroupWithZero Gamma] [MulArchimedean Gamma]
    [Valued K Gamma]
    [(Valued.v : Valuation K Gamma).IsRankOneDiscrete]
    [CompleteSpace K]
    {pi : (Valued.v : Valuation K Gamma).valuationSubring}
    (hpi : (Valued.v : Valuation K Gamma).IsUniformizer (pi : K)) :
    IsAdicComplete (uniformizerPowerIdeal pi 1)
      (Valued.v : Valuation K Gamma).valuationSubring := by
  rw [completeValuedField_uniformizerPowerIdeal_one_eq_maximalIdeal hpi]
  exact rankOneDiscreteValuationSubring_isAdicComplete
    (K := K) (Gamma := Gamma)

/-- The native topology of the valuation ring is also the principal
uniformizer-adic topology. -/
theorem completeValuedField_uniformizerIdeal_isAdic
    {K : Type u} [Field K] {Gamma : Type v}
    [LinearOrderedCommGroupWithZero Gamma] [MulArchimedean Gamma]
    [Valued K Gamma]
    [(Valued.v : Valuation K Gamma).IsRankOneDiscrete]
    [CompleteSpace K]
    {pi : (Valued.v : Valuation K Gamma).valuationSubring}
    (hpi : (Valued.v : Valuation K Gamma).IsUniformizer (pi : K)) :
    IsAdic (uniformizerPowerIdeal pi 1) := by
  rw [completeValuedField_uniformizerPowerIdeal_one_eq_maximalIdeal hpi]
  exact rankOneDiscreteValuationSubring_isAdic
    (K := K) (Gamma := Gamma)

/-- The adic inverse-limit equivalence, direct unit-group endpoint from valued-field
completeness: the canonical map `𝒪ˣ → lim 𝒪ˣ/U⁽ⁿ⁾` is a
multiplicative equivalence. -/
def completeValuedField_unitsEquivHigherUnitQuotientInverseLimit
    {K : Type u} [Field K] {Gamma : Type v}
    [LinearOrderedCommGroupWithZero Gamma] [MulArchimedean Gamma]
    [Valued K Gamma]
    [(Valued.v : Valuation K Gamma).IsRankOneDiscrete]
    [CompleteSpace K]
    {pi : (Valued.v : Valuation K Gamma).valuationSubring}
    (hpi : (Valued.v : Valuation K Gamma).IsUniformizer (pi : K)) :
    (Valued.v : Valuation K Gamma).valuationSubringˣ ≃*
      dvrHigherUnitQuotientInverseLimit pi := by
  let O := (Valued.v : Valuation K Gamma).valuationSubring
  letI : IsDiscreteValuationRing O :=
    rankOneDiscreteValuationSubring_isDiscreteValuationRing
      (K := K) (Gamma := Gamma)
  letI : IsAdicComplete (uniformizerPowerIdeal pi 1) O :=
    completeValuedField_uniformizerIdeal_isAdicComplete hpi
  exact dvrUnitsEquivHigherUnitQuotientInverseLimit
    (completeValuedField_uniformizer_irreducible hpi)

/-- The direct unit equivalence is coordinatewise the canonical quotient map
`u ↦ u mod U⁽ⁿ⁺¹⁾`. -/
theorem completeValuedField_unitsEquivHigherUnitQuotientInverseLimit_apply
    {K : Type u} [Field K] {Gamma : Type v}
    [LinearOrderedCommGroupWithZero Gamma] [MulArchimedean Gamma]
    [Valued K Gamma]
    [(Valued.v : Valuation K Gamma).IsRankOneDiscrete]
    [CompleteSpace K]
    {pi : (Valued.v : Valuation K Gamma).valuationSubring}
    (hpi : (Valued.v : Valuation K Gamma).IsUniformizer (pi : K))
    (u : (Valued.v : Valuation K Gamma).valuationSubringˣ) (n : ℕ) :
    dvrHigherUnitQuotientInverseLimit_eval pi n
      (completeValuedField_unitsEquivHigherUnitQuotientInverseLimit
        hpi u) = QuotientGroup.mk u := by
  let O := (Valued.v : Valuation K Gamma).valuationSubring
  let : IsDiscreteValuationRing O :=
    rankOneDiscreteValuationSubring_isDiscreteValuationRing
      (K := K) (Gamma := Gamma)
  let : IsAdicComplete (uniformizerPowerIdeal pi 1) O :=
    completeValuedField_uniformizerIdeal_isAdicComplete hpi
  exact dvrUnitsEquivHigherUnitQuotientInverseLimit_apply
    (completeValuedField_uniformizer_irreducible hpi) u n

/-- The adic inverse-limit equivalence, direct topological unit endpoint: for the native topology
on `𝒪ˣ` and discrete topology on all finite quotients, the canonical
unit map is a homeomorphism. -/
def completeValuedField_unitsHigherUnitQuotientInverseLimitHomeomorph
    {K : Type u} [Field K] {Gamma : Type v}
    [LinearOrderedCommGroupWithZero Gamma] [MulArchimedean Gamma]
    [Valued K Gamma]
    [(Valued.v : Valuation K Gamma).IsRankOneDiscrete]
    [CompleteSpace K]
    {pi : (Valued.v : Valuation K Gamma).valuationSubring}
    (hpi : (Valued.v : Valuation K Gamma).IsUniformizer (pi : K)) :
    let O := (Valued.v : Valuation K Gamma).valuationSubring
    Oˣ ≃ₜ dvrHigherUnitQuotientInverseLimit pi := by
  dsimp only
  let O := (Valued.v : Valuation K Gamma).valuationSubring
  letI : IsDiscreteValuationRing O :=
    rankOneDiscreteValuationSubring_isDiscreteValuationRing
      (K := K) (Gamma := Gamma)
  letI : IsAdicComplete (uniformizerPowerIdeal pi 1) O :=
    completeValuedField_uniformizerIdeal_isAdicComplete hpi
  have hadic : IsAdic (uniformizerPowerIdeal pi 1) :=
    completeValuedField_uniformizerIdeal_isAdic hpi
  let hirr := completeValuedField_uniformizer_irreducible hpi
  let hAdic :
      WithTopology Oˣ
          (adicUnitsTopology (uniformizerPowerIdeal pi 1)) ≃ₜ
        dvrHigherUnitQuotientInverseLimit pi :=
    unitsEquivHigherUnitQuotientInverseLimitHomeomorph hirr
  have hUnitsTopology :
      (inferInstance : TopologicalSpace Oˣ) =
        adicUnitsTopology (uniformizerPowerIdeal pi 1) := by
    unfold adicUnitsTopology
    rw [← hadic]
  let hNative :
      WithTopology Oˣ
          (inferInstance : TopologicalSpace Oˣ) ≃ₜ
        dvrHigherUnitQuotientInverseLimit pi :=
    hUnitsTopology.symm ▸ hAdic
  exact
    (WithTopology.homeomorph
      (α := Oˣ)
      (topology := (inferInstance : TopologicalSpace Oˣ))).symm.trans hNative

end Valuations
end LubinTate
