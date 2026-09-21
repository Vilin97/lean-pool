/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Nonpositive
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.HahnSeries.Full
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.OmnificInteger.NormalForm

/-!
# Omnific integers in the nonpositive Hahn integer part

This module packages Conway's normal-form characterization into LM24's Hahn-series orientation.
The order dual implements `t = ω⁻¹`, so a nonnegative Conway exponent becomes a nonpositive
Hahn exponent. The coefficient at exponent zero lands in the image of `ℤ → ℝ`.

The resulting map is an injective ring map.
-/

universe u

public noncomputable section

namespace Surreal

/-- The copy of the integers inside the real coefficient field. -/
def realIntegerSubring : Subring ℝ :=
  (Int.castRingHom ℝ).range

/-- The integer coefficient subring of the reals is isomorphic to `ℤ`. -/
noncomputable def realIntegerSubringEquiv : ℤ ≃+* realIntegerSubring :=
  RingEquiv.ofBijective (Int.castRingHom ℝ).rangeRestrict
    ⟨Int.cast_injective, RingHom.rangeRestrict_surjective _⟩

/-- The integer coefficient subring of the reals is pre-Schreier. -/
noncomputable instance instDecompositionMonoidRealIntegerSubring :
    DecompositionMonoid realIntegerSubring :=
  MulEquiv.decompositionMonoid realIntegerSubringEquiv.symm.toMulEquiv

/-- Membership in the real integer coefficient subring. -/
@[simp]
theorem mem_realIntegerSubring {r : ℝ} :
    r ∈ realIntegerSubring ↔ r ∈ Set.range ((↑) : ℤ → ℝ) :=
  Iff.rfl

namespace OmnificInteger

/-- The nonpositive full Hahn series underlying an omnific integer. -/
def toNonpositiveHahn (x : OmnificInteger.{u}) :
    HahnSeries.Nonpositive Surrealᵒᵈ ℝ :=
  ⟨toFullHahnSeries x.1, fun i hi ↦ by
    have hsupport := (isOmnificInteger_iff_normalForm.mp
      (mem_omnificIntegers.mp x.2)).1
    exact hsupport (mem_support_toFullHahnSeries.mp hi)⟩

/-- Coercing the nonpositive Hahn image recovers the full Conway Hahn series. -/
@[simp]
theorem coe_toNonpositiveHahn (x : OmnificInteger.{u}) :
    (x.toNonpositiveHahn : HahnSeries Surrealᵒᵈ ℝ) = toFullHahnSeries x.1 :=
  (rfl)

/-- The nonpositive Hahn image of omnific integers as an additive homomorphism. -/
def toNonpositiveHahnAddMonoidHom :
    OmnificInteger.{u} →+ HahnSeries.Nonpositive Surrealᵒᵈ ℝ where
  toFun := toNonpositiveHahn
  map_zero' := by
    apply Subtype.ext
    exact toFullHahnSeries_zero
  map_add' x y := by
    apply Subtype.ext
    exact toFullHahnSeries_add x.1 y.1

/-- Evaluation of the additive nonpositive Hahn map. -/
@[simp]
theorem toNonpositiveHahnAddMonoidHom_apply (x : OmnificInteger.{u}) :
    toNonpositiveHahnAddMonoidHom x = x.toNonpositiveHahn :=
  (rfl)

/-- The additive nonpositive Hahn map is injective. -/
theorem toNonpositiveHahn_injective :
    Function.Injective (toNonpositiveHahn :
      OmnificInteger.{u} → HahnSeries.Nonpositive Surrealᵒᵈ ℝ) := by
  intro x y hxy
  apply Subtype.ext
  apply toFullHahnSeries_injective
  have hraw := congrArg (fun q : HahnSeries.Nonpositive Surrealᵒᵈ ℝ ↦
    (q : HahnSeries Surrealᵒᵈ ℝ)) hxy
  simpa only [coe_toNonpositiveHahn] using hraw

/-- The nonpositive Hahn image preserves arbitrary omnific-integer products. -/
@[simp]
theorem toNonpositiveHahn_mul (x y : OmnificInteger.{u}) :
    toNonpositiveHahn (x * y) = toNonpositiveHahn x * toNonpositiveHahn y := by
  apply Subtype.ext
  exact toFullHahnSeries_mul x.1 y.1

/-- The Hahn truncation-integer-part element represented by an omnific integer. -/
def toTruncationIntegerPart (x : OmnificInteger.{u}) :
    HahnSeries.truncationIntegerPart Surrealᵒᵈ realIntegerSubring :=
  ⟨x.toNonpositiveHahn, by
    rw [HahnSeries.mem_truncationIntegerPart]
    change (toFullHahnSeries x.1).coeff 0 ∈ realIntegerSubring
    rw [coeff_toFullHahnSeries, mem_realIntegerSubring]
    change x.1.coeff 0 ∈ Set.range ((↑) : ℤ → ℝ)
    exact (isOmnificInteger_iff_normalForm.mp (mem_omnificIntegers.mp x.2)).2⟩

/-- Coercing the truncation-integer-part image recovers the nonpositive Hahn image. -/
@[simp]
theorem coe_toTruncationIntegerPart (x : OmnificInteger.{u}) :
    (x.toTruncationIntegerPart : HahnSeries.Nonpositive Surrealᵒᵈ ℝ) =
      x.toNonpositiveHahn :=
  by
    apply Subtype.ext
    rfl

/-- The truncation-integer-part image of omnific integers as an additive homomorphism. -/
def toTruncationIntegerPartAddMonoidHom :
    OmnificInteger.{u} →+
      HahnSeries.truncationIntegerPart Surrealᵒᵈ realIntegerSubring where
  toFun := toTruncationIntegerPart
  map_zero' := by
    apply Subtype.ext
    change toNonpositiveHahn (0 : OmnificInteger.{u}) = 0
    exact toNonpositiveHahnAddMonoidHom.map_zero
  map_add' x y := by
    apply Subtype.ext
    change toNonpositiveHahn (x + y) = toNonpositiveHahn x + toNonpositiveHahn y
    exact toNonpositiveHahnAddMonoidHom.map_add x y

/-- Evaluation of the additive truncation-integer-part map. -/
@[simp]
theorem toTruncationIntegerPartAddMonoidHom_apply (x : OmnificInteger.{u}) :
    toTruncationIntegerPartAddMonoidHom x = x.toTruncationIntegerPart :=
  (rfl)

/-- The additive truncation-integer-part map is injective. -/
theorem toTruncationIntegerPart_injective :
    Function.Injective (toTruncationIntegerPart : OmnificInteger.{u} →
      HahnSeries.truncationIntegerPart Surrealᵒᵈ realIntegerSubring) := by
  intro x y hxy
  apply toNonpositiveHahn_injective
  have h := congrArg (fun q : HahnSeries.truncationIntegerPart
    Surrealᵒᵈ realIntegerSubring ↦
      (q : HahnSeries.Nonpositive Surrealᵒᵈ ℝ)) hxy
  simpa only [coe_toTruncationIntegerPart] using h

/-- The truncation-integer-part image preserves arbitrary omnific-integer products. -/
@[simp]
theorem toTruncationIntegerPart_mul (x y : OmnificInteger.{u}) :
    toTruncationIntegerPart (x * y) =
      toTruncationIntegerPart x * toTruncationIntegerPart y := by
  apply Subtype.ext
  exact toNonpositiveHahn_mul x y

end OmnificInteger

end Surreal
