/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.DomainOrderType
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.HahnSeries.Full

/-!
# Conway normal forms with signed surreal exponents

The order dual in `Surreal.toFullHahnSeries` records the reversal from Conway's `ω` to
LM24's `t = ω⁻¹`. Sending a dual exponent `i` to the ordinary surreal exponent `-i` makes
that reversal explicit and places the normal form in a Hahn field whose exponent group is
`Surreal` itself. This is the orientation in which the surreal Archimedean-stratum assumptions
apply directly.
-/

universe u

public noncomputable section

namespace Surreal

/-- Negation identifies dual Conway exponents with signed ordinary surreal exponents. -/
def dualExponentOrderAddMonoidIso : Surrealᵒᵈ ≃+o Surreal :=
  { toFun := fun x ↦ -x.ofDual
    invFun := fun x ↦ OrderDual.toDual (-x)
    left_inv := by intro x; simp
    right_inv := by intro x; simp
    map_add' := by intro x y; simp [add_comm]
    map_le_map_iff' := by
      intro x y
      change -x.ofDual ≤ -y.ofDual ↔ y.ofDual ≤ x.ofDual
      exact neg_le_neg_iff }

/-- The signed-exponent map sends a dual exponent to the negative underlying surreal. -/
@[simp]
theorem dualExponentOrderAddMonoidIso_apply (x : Surrealᵒᵈ) :
    dualExponentOrderAddMonoidIso x = -x.ofDual :=
  (rfl)

/-- The inverse signed-exponent map sends `x` to the dual of `-x`. -/
@[simp]
theorem dualExponentOrderAddMonoidIso_symm_apply (x : Surreal.{u}) :
    dualExponentOrderAddMonoidIso.symm x = OrderDual.toDual (-x) :=
  (rfl)

/-- The full Conway normal form with the exponent of `t = ω⁻¹` written as an ordinary
surreal number. -/
def toSignedFullHahnSeries (x : Surreal.{u}) : HahnSeries Surreal ℝ :=
  HahnSeries.embDomainRingEquiv dualExponentOrderAddMonoidIso x.toFullHahnSeries

/-- The signed full series is exponent reindexing of the dual-exponent full series. -/
theorem toSignedFullHahnSeries_eq (x : Surreal.{u}) :
    toSignedFullHahnSeries x =
      HahnSeries.embDomainRingEquiv dualExponentOrderAddMonoidIso x.toFullHahnSeries :=
  (rfl)

/-- Evaluation of the signed Conway normal form at exponent `g`. -/
@[simp]
theorem coeff_toSignedFullHahnSeries (x g : Surreal.{u}) :
    x.toSignedFullHahnSeries.coeff g = x.coeff (-g) := by
  rw [toSignedFullHahnSeries_eq,
    ← dualExponentOrderAddMonoidIso.apply_symm_apply g,
    HahnSeries.embDomainRingEquiv_coeff,
    dualExponentOrderAddMonoidIso_symm_apply,
    coeff_toFullHahnSeries]
  simp

/-- Signed exponent reindexing preserves the zero Conway normal form. -/
@[simp]
theorem toSignedFullHahnSeries_zero :
    toSignedFullHahnSeries (0 : Surreal.{u}) = 0 := by
  rw [toSignedFullHahnSeries, toFullHahnSeries_zero, map_zero]

/-- Signed exponent reindexing preserves addition of Conway normal forms. -/
theorem toSignedFullHahnSeries_add (x y : Surreal.{u}) :
    toSignedFullHahnSeries (x + y) =
      toSignedFullHahnSeries x + toSignedFullHahnSeries y := by
  rw [toSignedFullHahnSeries_eq, toSignedFullHahnSeries_eq,
    toSignedFullHahnSeries_eq, toFullHahnSeries_add, map_add]

/-- Signed exponent reindexing preserves negation of Conway normal forms. -/
@[simp]
theorem toSignedFullHahnSeries_neg (x : Surreal.{u}) :
    toSignedFullHahnSeries (-x) = -toSignedFullHahnSeries x := by
  rw [toSignedFullHahnSeries_eq, toSignedFullHahnSeries_eq,
    toFullHahnSeries_neg, map_neg]

/-- Signed exponent reindexing preserves subtraction of Conway normal forms. -/
@[simp]
theorem toSignedFullHahnSeries_sub (x y : Surreal.{u}) :
    toSignedFullHahnSeries (x - y) =
      toSignedFullHahnSeries x - toSignedFullHahnSeries y := by
  rw [sub_eq_add_neg, toSignedFullHahnSeries_add, toSignedFullHahnSeries_neg]
  rfl

/-- The signed full Conway normal-form map is injective. -/
theorem toSignedFullHahnSeries_injective :
    Function.Injective (toSignedFullHahnSeries :
      Surreal.{u} → HahnSeries Surreal ℝ) :=
  (HahnSeries.embDomainRingEquiv dualExponentOrderAddMonoidIso).injective.comp
    toFullHahnSeries_injective

/-- A signed Hahn exponent occurs exactly when its negation occurs in the unsigned Conway
support. -/
theorem mem_support_toSignedFullHahnSeries {x g : Surreal.{u}} :
    g ∈ x.toSignedFullHahnSeries.support ↔ -g ∈ x.support := by
  rw [toSignedFullHahnSeries_eq, HahnSeries.support_embDomainRingEquiv]
  constructor
  · rintro ⟨i, hi, rfl⟩
    simpa using (mem_support_toFullHahnSeries.mp hi)
  · intro hg
    refine ⟨OrderDual.toDual (-g), mem_support_toFullHahnSeries.mpr ?_, ?_⟩
    · simpa using hg
    · simp

/-- Signed exponent reindexing preserves the LM24 degree of the Conway normal form. -/
@[simp]
theorem degree_toSignedFullHahnSeries (x : Surreal.{u}) :
    x.toSignedFullHahnSeries.degree = x.toFullHahnSeries.degree := by
  rw [HahnSeries.degree_eq_cantorDegree, HahnSeries.degree_eq_cantorDegree,
    toSignedFullHahnSeries_eq, HahnSeries.supportOrderType_embDomainRingEquiv]

/-- The signed full Conway normal form of a real is concentrated at exponent zero. -/
@[simp]
theorem toSignedFullHahnSeries_realCast (r : ℝ) :
    toSignedFullHahnSeries (r : Surreal.{u}) = HahnSeries.single 0 r := by
  rw [toSignedFullHahnSeries_eq, toFullHahnSeries_realCast]
  ext g
  rw [← dualExponentOrderAddMonoidIso.apply_symm_apply g,
    HahnSeries.embDomainRingEquiv_coeff]
  rw [dualExponentOrderAddMonoidIso_symm_apply]
  simp [HahnSeries.coeff_single]

/-- The signed full Conway normal form of `ω ^ x` is the monomial at exponent `-x`. -/
@[simp]
theorem toSignedFullHahnSeries_wpow (x : Surreal.{u}) :
    toSignedFullHahnSeries (ω^ x) = HahnSeries.single (-x) 1 := by
  rw [toSignedFullHahnSeries_eq, toFullHahnSeries_wpow,
    HahnSeries.embDomainRingEquiv_single]
  rfl

/-- The signed full Conway Hahn-series map preserves arbitrary surreal products. -/
@[simp]
theorem toSignedFullHahnSeries_mul (x y : Surreal.{u}) :
    toSignedFullHahnSeries (x * y) =
      toSignedFullHahnSeries x * toSignedFullHahnSeries y := by
  rw [toSignedFullHahnSeries_eq, toSignedFullHahnSeries_eq,
    toSignedFullHahnSeries_eq, toFullHahnSeries_mul, map_mul]

/-- Full Hahn multiplication compatibility is equivalent to its signed-exponent form. -/
theorem toSignedFullHahnSeries_mul_iff (x y : Surreal.{u}) :
    toSignedFullHahnSeries (x * y) =
        toSignedFullHahnSeries x * toSignedFullHahnSeries y ↔
      toFullHahnSeries (x * y) = toFullHahnSeries x * toFullHahnSeries y := by
  change HahnSeries.embDomainRingEquiv dualExponentOrderAddMonoidIso
      (x * y).toFullHahnSeries =
        HahnSeries.embDomainRingEquiv dualExponentOrderAddMonoidIso x.toFullHahnSeries *
          HahnSeries.embDomainRingEquiv dualExponentOrderAddMonoidIso y.toFullHahnSeries ↔ _
  rw [← map_mul]
  exact (HahnSeries.embDomainRingEquiv dualExponentOrderAddMonoidIso).injective.eq_iff

end Surreal
