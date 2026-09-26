/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.CardinalTruncation
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.CardinalTruncationDomainEquiv
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.HahnSeries.SignedFull
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.ArchimedeanAssumptions
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.HahnSeries.IntegerPart

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# Omnific integers and the bounded Hahn integer part

Every Conway normal form has support smaller than the universe cardinal bounding
`SurrealHahnSeries`. Conversely, every bounded nonpositive Hahn series whose constant
coefficient is an integer defines a small Conway normal form, hence an omnific integer.

This gives a ring equivalence between Conway's cut-defined omnific integers and the bounded Hahn
truncation integer part used by the set-sized form of LM24, Proposition 9.2.2.
-/

universe u

public noncomputable section

open Cardinal

namespace Surreal.OmnificInteger

/-- The universe-bounded Hahn truncation integer part corresponding to omnific integers. -/
abbrev SmallSupportIntegerPart :=
  HahnSeries.cardSuppLTTruncationIntegerPart
    (G := Surrealᵒᵈ) (R := ℝ) (κ := Surreal.smallSupportCardinal.{u})
      Surreal.realIntegerSubring

private def ofSmallSupportHahnSeries
    (b : SmallSupportIntegerPart.{u}) : SurrealHahnSeries.{u} := by
  let raw : HahnSeries Surrealᵒᵈ ℝ := b.1.1
  let f : Surreal.{u} → ℝ := fun i ↦ raw.coeff (OrderDual.toDual i)
  have hsmallRaw : Small.{u} raw.support := by
    rw [Cardinal.small_iff_lift_mk_lt_univ, Cardinal.lift_id]
    rw [← Surreal.smallSupportCardinal_eq_univ]
    exact ((HahnSeries.mem_cardSuppLTSubfield _).mp b.1.2 : raw.cardSupp < _)
  let e : Function.support f ≃ raw.support := {
    toFun i := ⟨OrderDual.toDual i.1, by
      rw [HahnSeries.mem_support]
      exact i.2⟩
    invFun i := ⟨i.1.ofDual, by
      change raw.coeff (OrderDual.toDual i.1.ofDual) ≠ 0
      rw [OrderDual.toDual_ofDual]
      exact (HahnSeries.mem_support _ _).mp i.2⟩
    left_inv i := by apply Subtype.ext; simp
    right_inv i := by apply Subtype.ext; simp
  }
  exact SurrealHahnSeries.mk f ((small_congr e).mpr hsmallRaw) (by
    change Set.WellFoundedOn (Function.support f)
      (fun i j ↦ OrderDual.toDual i < OrderDual.toDual j)
    apply Set.WellFoundedOn.mapsTo OrderDual.toDual
    · intro i hi
      exact hi
    · exact raw.isPWO_support.isWF)

private def ofSmallSupportSurreal
    (b : SmallSupportIntegerPart.{u}) : Surreal.{u} :=
  (ofSmallSupportHahnSeries b).toSurreal

private theorem toFullHahnSeries_ofSmallSupportSurreal
    (b : SmallSupportIntegerPart.{u}) :
    (ofSmallSupportSurreal b).toFullHahnSeries =
      (b.1.1 : HahnSeries Surrealᵒᵈ ℝ) := by
  ext i
  rw [Surreal.coeff_toFullHahnSeries, ofSmallSupportSurreal,
    SurrealHahnSeries.coeff_toSurreal]
  rw [ofSmallSupportHahnSeries, SurrealHahnSeries.coeff_mk]
  simp

/-- Recover the omnific integer represented by a bounded nonpositive Hahn integer part. -/
def ofSmallSupportIntegerPart
    (b : SmallSupportIntegerPart.{u}) : Surreal.OmnificInteger.{u} :=
  have hb := (HahnSeries.mem_cardSuppLTTruncationIntegerPart
    (Z := Surreal.realIntegerSubring)).mp b.2
  ⟨ofSmallSupportSurreal b, Surreal.mem_omnificIntegers.mpr
    (Surreal.isOmnificInteger_iff_normalForm.mpr ⟨by
      intro i hi
      have hfull : OrderDual.toDual i ∈
          (b.1.1 : HahnSeries Surrealᵒᵈ ℝ).support := by
        rw [← toFullHahnSeries_ofSmallSupportSurreal]
        exact Surreal.mem_support_toFullHahnSeries.mpr hi
      have hnonpos := hb.1 hfull
      change 0 ≤ i at hnonpos
      exact hnonpos, by
      rw [← Surreal.mem_realIntegerSubring]
      have hcoeff := congrArg
        (fun q : HahnSeries Surrealᵒᵈ ℝ ↦ q.coeff 0)
        (toFullHahnSeries_ofSmallSupportSurreal b)
      rw [Surreal.coeff_toFullHahnSeries] at hcoeff
      have hcoeff' : (ofSmallSupportSurreal b).coeff 0 =
          (b.1.1 : HahnSeries Surrealᵒᵈ ℝ).coeff 0 := by
        simpa using hcoeff
      rw [hcoeff']
      exact hb.2⟩)⟩

/-- Put an omnific integer into the universe-bounded Hahn truncation integer part. -/
def toSmallSupportIntegerPart
    (x : Surreal.OmnificInteger.{u}) : SmallSupportIntegerPart.{u} := by
  have hsmall : Small.{u} x.1.toFullHahnSeries.support := by
    let e : x.1.toFullHahnSeries.support ≃ x.1.support := {
      toFun i := ⟨i.1.ofDual, Surreal.mem_support_toFullHahnSeries.mp i.2⟩
      invFun i :=
        ⟨OrderDual.toDual i.1, Surreal.mem_support_toFullHahnSeries.mpr i.2⟩
      left_inv i := by apply Subtype.ext; simp
      right_inv i := by apply Subtype.ext; simp
    }
    exact (small_congr e).mpr inferInstance
  have hcard : x.1.toFullHahnSeries.cardSupp < Surreal.smallSupportCardinal.{u} := by
    rw [HahnSeries.cardSupp, Surreal.smallSupportCardinal_eq_univ]
    simpa only [Cardinal.lift_id] using
      (Cardinal.small_iff_lift_mk_lt_univ.mp hsmall)
  exact ⟨⟨x.1.toFullHahnSeries, hcard⟩, by
    rw [HahnSeries.mem_cardSuppLTTruncationIntegerPart]
    constructor
    · intro i hi
      apply x.toNonpositiveHahn.2
      simpa only [coe_toNonpositiveHahn] using hi
    · have hxint := x.toTruncationIntegerPart.2
      rw [HahnSeries.mem_truncationIntegerPart] at hxint
      simpa only [coe_toTruncationIntegerPart, coe_toNonpositiveHahn] using hxint⟩

/-- The bounded Hahn image has exactly the full Conway normal form as its underlying series. -/
@[simp]
theorem coe_toSmallSupportIntegerPart
    (x : Surreal.OmnificInteger.{u}) :
    ((toSmallSupportIntegerPart x :
      HahnSeries.CardSuppLTField (G := Surrealᵒᵈ) (R := ℝ)
        (κ := Surreal.smallSupportCardinal.{u})) : HahnSeries Surrealᵒᵈ ℝ) =
      x.1.toFullHahnSeries :=
  (rfl)

/-- Recovering a bounded Hahn integer part preserves its underlying full Hahn series. -/
@[simp]
theorem toFullHahnSeries_ofSmallSupportIntegerPart
    (b : SmallSupportIntegerPart.{u}) :
    (ofSmallSupportIntegerPart b).1.toFullHahnSeries =
      (b.1.1 : HahnSeries Surrealᵒᵈ ℝ) :=
  toFullHahnSeries_ofSmallSupportSurreal b

/-- Recovering the omnific integer after passing to bounded Hahn series is the identity. -/
@[simp]
theorem ofSmallSupportIntegerPart_toSmallSupportIntegerPart
    (x : Surreal.OmnificInteger.{u}) :
    ofSmallSupportIntegerPart (toSmallSupportIntegerPart x) = x := by
  apply Subtype.ext
  apply Surreal.toFullHahnSeries_injective
  change (ofSmallSupportSurreal (toSmallSupportIntegerPart x)).toFullHahnSeries =
    x.1.toFullHahnSeries
  rw [toFullHahnSeries_ofSmallSupportSurreal]
  rfl

/-- Returning to bounded Hahn series after recovering an omnific integer is the identity. -/
@[simp]
theorem toSmallSupportIntegerPart_ofSmallSupportIntegerPart
    (b : SmallSupportIntegerPart.{u}) :
    toSmallSupportIntegerPart (ofSmallSupportIntegerPart b) = b := by
  apply Subtype.ext
  apply Subtype.ext
  exact toFullHahnSeries_ofSmallSupportSurreal b

/-- Omnific integers are additively equivalent to the bounded Hahn truncation integer part. -/
def smallSupportIntegerPartAddEquiv :
    Surreal.OmnificInteger.{u} ≃+ SmallSupportIntegerPart.{u} where
  toFun := toSmallSupportIntegerPart
  invFun := ofSmallSupportIntegerPart
  left_inv := ofSmallSupportIntegerPart_toSmallSupportIntegerPart
  right_inv := toSmallSupportIntegerPart_ofSmallSupportIntegerPart
  map_add' x y := by
    apply Subtype.ext
    apply Subtype.ext
    exact Surreal.toFullHahnSeries_add x.1 y.1

/-- Evaluation of the additive Conway/Hahn equivalence. -/
@[simp]
theorem smallSupportIntegerPartAddEquiv_apply
    (x : Surreal.OmnificInteger.{u}) :
    smallSupportIntegerPartAddEquiv x = toSmallSupportIntegerPart x :=
  (rfl)

/-- The Conway/Hahn ring equivalence for universe-bounded omnific integers. -/
def smallSupportIntegerPartRingEquiv :
    Surreal.OmnificInteger.{u} ≃+* SmallSupportIntegerPart.{u} :=
  { smallSupportIntegerPartAddEquiv with
    map_mul' := by
      intro x y
      apply Subtype.ext
      apply Subtype.ext
      exact Surreal.toFullHahnSeries_mul x.1 y.1 }

/-- Evaluation of the Conway/Hahn ring equivalence. -/
@[simp]
theorem smallSupportIntegerPartRingEquiv_apply
    (x : Surreal.OmnificInteger.{u}) :
    smallSupportIntegerPartRingEquiv x = toSmallSupportIntegerPart x :=
  (rfl)

/-! ### Signed surreal exponents -/

/-- The bounded Hahn truncation integer part with `t = ω⁻¹` exponents written as ordinary
surreal numbers. -/
abbrev SignedSmallSupportIntegerPart :=
  HahnSeries.cardSuppLTTruncationIntegerPart
    (G := Surreal) (R := ℝ) (κ := Surreal.smallSupportCardinal.{u})
      Surreal.realIntegerSubring

/-- Reindex the dual-exponent bounded integer part by sending a Conway exponent `i` to the
ordinary surreal exponent `-i`. -/
def smallSupportIntegerPartSignedRingEquiv :
    SmallSupportIntegerPart.{u} ≃+* SignedSmallSupportIntegerPart.{u} :=
  HahnSeries.cardSuppLTTruncationIntegerPartRingEquiv
    Surreal.dualExponentOrderAddMonoidIso Surreal.realIntegerSubring

/-- Evaluation of signed exponent reindexing on bounded integer parts. -/
@[simp]
theorem smallSupportIntegerPartSignedRingEquiv_apply
    (b : SmallSupportIntegerPart.{u}) :
    smallSupportIntegerPartSignedRingEquiv b =
      HahnSeries.cardSuppLTTruncationIntegerPartRingEquiv
        Surreal.dualExponentOrderAddMonoidIso Surreal.realIntegerSubring b :=
  (rfl)

/-- Put an omnific integer into the bounded Hahn integer part with signed surreal exponents. -/
def toSignedSmallSupportIntegerPart
    (x : Surreal.OmnificInteger.{u}) : SignedSmallSupportIntegerPart.{u} :=
  smallSupportIntegerPartSignedRingEquiv (toSmallSupportIntegerPart x)

/-- The signed bounded Hahn image has exactly the signed full Conway normal form. -/
@[simp]
theorem coe_toSignedSmallSupportIntegerPart
    (x : Surreal.OmnificInteger.{u}) :
    ((toSignedSmallSupportIntegerPart x :
      HahnSeries.CardSuppLTField (G := Surreal) (R := ℝ)
        (κ := Surreal.smallSupportCardinal.{u})) : HahnSeries Surreal ℝ) =
      x.1.toSignedFullHahnSeries := by
  rw [toSignedSmallSupportIntegerPart,
    smallSupportIntegerPartSignedRingEquiv_apply,
    HahnSeries.coe_cardSuppLTTruncationIntegerPartRingEquiv,
    coe_toSmallSupportIntegerPart, Surreal.toSignedFullHahnSeries_eq]

/-- The nonpositive signed Hahn series underlying an omnific integer. -/
def toSignedNonpositiveHahn (x : Surreal.OmnificInteger.{u}) :
    HahnSeries.Nonpositive Surreal ℝ :=
  HahnSeries.CardSuppLTTruncationIntegerPart.toNonpositiveRingHom
    Surreal.realIntegerSubring (toSignedSmallSupportIntegerPart x)

/-- Coercing the signed nonpositive image recovers the signed full Conway normal form. -/
@[simp]
theorem coe_toSignedNonpositiveHahn (x : Surreal.OmnificInteger.{u}) :
    (x.toSignedNonpositiveHahn : HahnSeries Surreal ℝ) =
      x.1.toSignedFullHahnSeries := by
  rw [toSignedNonpositiveHahn,
    HahnSeries.CardSuppLTTruncationIntegerPart.coe_toNonpositiveRingHom,
    coe_toSignedSmallSupportIntegerPart]

/-- The signed-exponent Conway/Hahn ring equivalence for universe-bounded omnific integers. -/
@[blueprint "thm:signed-normal-form-omnific-integer-equivalence"
  (phase := "Surreal numbers and omnific integers")
  (title := "The signed normal-form isomorphism for omnific integers")
  (statement := /--
    For every universe $u$, signed Conway normal form restricts to a ring
    isomorphism
    \[
      \mathbf{Oz}_u\simeq
      \mathbb Z+\mathbb R((\mathbf{No}_u^{<0}))_{\kappa_u},
    \]
    where $\kappa_u$ is the universe cardinal.
  -/)
  (proof := /--
    Restrict Conway normal form to the omnific integers, then negate the
    exponents so that nonnegative Conway exponents become nonpositive
    exponents in the variable $t=\omega^{-1}$.
  -/)]
def signedSmallSupportIntegerPartRingEquiv :
    Surreal.OmnificInteger.{u} ≃+* SignedSmallSupportIntegerPart.{u} :=
  smallSupportIntegerPartRingEquiv.trans smallSupportIntegerPartSignedRingEquiv

/-- Evaluation of the signed Conway/Hahn ring equivalence. -/
@[simp]
theorem signedSmallSupportIntegerPartRingEquiv_apply
    (x : Surreal.OmnificInteger.{u}) :
    signedSmallSupportIntegerPartRingEquiv x =
      toSignedSmallSupportIntegerPart x :=
  (rfl)

end Surreal.OmnificInteger
