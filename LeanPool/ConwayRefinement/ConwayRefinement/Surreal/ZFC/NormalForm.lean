/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.ZFC.Basic
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.HahnSeries.Transfer
public import Mathlib.Algebra.Order.Archimedean.Class
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Logic.Small.Basic

/-!
# Conway normal forms of class-coded surreal values

The Conway-equivalence classes of numeric ZFC game codes use the existing Conway normal-form
order equivalence. Coefficients and support are indexed by class-coded surreal exponents; support
is set-sized. The finite-support-class and reducedness predicates are stated directly on these
exponents, with exact equivalences to the corresponding formulas in the surreal field.

Reducedness uses the unsigned Conway-exponent orientation of LM24, Definition 8.2.6. It retains
the zero Archimedean class, which is relevant to constant coefficients other than zero and one.
-/

universe u

public noncomputable section

namespace ZFSet.Surreal

/-- The canonical Conway normal-form chart of the class-coded surreal field. -/
def toHahnSeriesOrderIso : Surreal.{u} ≃o SurrealHahnSeries.{u} :=
  orderRingEquiv.toOrderIso.trans _root_.Surreal.toHahnSeriesOrderIso

@[simp]
theorem toHahnSeriesOrderIso_apply (x : Surreal.{u}) :
    toHahnSeriesOrderIso x = (toSurreal x).toHahnSeries := by
  simp [toHahnSeriesOrderIso]

/-- The Conway normal form of a class-coded surreal value. -/
def toHahnSeries (x : Surreal.{u}) : SurrealHahnSeries.{u} := toHahnSeriesOrderIso x

@[simp]
theorem toHahnSeries_eq_toSurreal (x : Surreal.{u}) :
    toHahnSeries x = (toSurreal x).toHahnSeries := toHahnSeriesOrderIso_apply x

/-- A class value has a given normal form exactly when that series evaluates to its value. -/
theorem toHahnSeries_eq_iff (x : Surreal.{u}) (s : SurrealHahnSeries.{u}) :
    toHahnSeries x = s ↔ toSurreal x = s.toSurreal := by
  constructor
  · intro h
    have hvalue := congrArg SurrealHahnSeries.toSurreal h
    simpa only [toHahnSeries_eq_toSurreal, _root_.Surreal.toSurreal_toHahnSeries] using hvalue
  · intro h
    rw [toHahnSeries_eq_toSurreal, h, SurrealHahnSeries.toHahnSeries_toSurreal]

/-- The coefficient at a class-coded Conway exponent. -/
def coeff (x i : Surreal.{u}) : ℝ := (toHahnSeries x).coeff (toSurreal i)

@[simp]
theorem coeff_eq_toSurreal (x i : Surreal.{u}) :
    coeff x i = (toSurreal x).coeff (toSurreal i) := by
  rw [coeff, toHahnSeries_eq_toSurreal, _root_.Surreal.coeff_toHahnSeries]

/-- The Conway support, indexed by the class-coded surreal exponents. -/
def support (x : Surreal.{u}) : Set Surreal.{u} := toSurreal ⁻¹' (toSurreal x).support

/-- Membership in the class-coded support is detected by evaluating the exponent. -/
theorem mem_support_iff_toSurreal (x i : Surreal.{u}) :
    i ∈ support x ↔ toSurreal i ∈ (toSurreal x).support := (Iff.rfl)

@[simp]
theorem mem_support_iff (x i : Surreal.{u}) : i ∈ support x ↔ coeff x i ≠ 0 := by
  rw [mem_support_iff_toSurreal, _root_.Surreal.mem_support_iff, coeff_eq_toSurreal]

/-- Evaluation maps the class-coded support onto exactly the Conway support. -/
theorem image_support (x : Surreal.{u}) :
    toSurreal '' support x = (toSurreal x).support :=
  Set.image_preimage_eq _ toSurreal_surjective

/-- A normal form has only a set-sized collection of class-coded exponents. -/
instance (x : Surreal.{u}) : Small.{u} (support x) := by
  refine small_of_injective (f := fun i : support x ↦
    (⟨toSurreal i, (mem_support_iff_toSurreal x i).1 i.property⟩ :
      (toSurreal x).support)) ?_
  intro i j h
  apply Subtype.ext
  exact toSurreal_injective (congrArg Subtype.val h)

/-- Evaluation preserves the support intersection used by reducedness. -/
theorem image_support_inter_support_sub_one (x : Surreal.{u}) :
    toSurreal '' (support x ∩ support (x - 1)) =
      (toSurreal x).support ∩ (toSurreal x - 1).support := by
  rw [Set.image_inter toSurreal_injective, image_support, image_support,
    toSurreal_sub, toSurreal_one]

/-- Evaluation induces an order-preserving map on additive Archimedean classes. -/
def archimedeanClassMap :
    ArchimedeanClass Surreal.{u} →o ArchimedeanClass _root_.Surreal.{u} :=
  ArchimedeanClass.orderHom orderRingEquiv.toOrderRingHom.toOrderAddMonoidHom

@[simp]
theorem archimedeanClassMap_mk (i : Surreal.{u}) :
    archimedeanClassMap (ArchimedeanClass.mk i) = ArchimedeanClass.mk (toSurreal i) := by
  simp [archimedeanClassMap]

/-- Distinct class-coded Archimedean classes remain distinct after evaluation. -/
theorem archimedeanClassMap_injective : Function.Injective (archimedeanClassMap.{u}) :=
  ArchimedeanClass.orderHom_injective orderRingEquiv.injective

/-- Every surreal Archimedean class is represented by class-coded exponents. -/
theorem archimedeanClassMap_surjective : Function.Surjective (archimedeanClassMap.{u}) := by
  intro c
  induction c using ArchimedeanClass.ind with
  | mk i =>
    obtain ⟨j, rfl⟩ := toSurreal_surjective i
    exact ⟨ArchimedeanClass.mk j, archimedeanClassMap_mk j⟩

/-- Evaluation identifies exactly the Archimedean classes met by the two supports. -/
theorem image_supportArchimedeanClasses (x : Surreal.{u}) :
    archimedeanClassMap '' (ArchimedeanClass.mk '' support x) =
      ArchimedeanClass.mk '' (toSurreal x).support := by
  calc
    _ = (fun i ↦ ArchimedeanClass.mk (toSurreal i)) '' support x := by
      simp only [Set.image_image, archimedeanClassMap_mk]
    _ = ArchimedeanClass.mk '' (toSurreal '' support x) := by rw [Set.image_image]
    _ = _ := by rw [image_support]

/-- The Conway support meets only finitely many additive Archimedean classes. -/
def HasFiniteSupportClasses (x : Surreal.{u}) : Prop :=
  (ArchimedeanClass.mk '' support x).Finite

/-- The defining set formula for finite support-class number. -/
theorem hasFiniteSupportClasses_iff (x : Surreal.{u}) :
    HasFiniteSupportClasses x ↔ (ArchimedeanClass.mk '' support x).Finite := (Iff.rfl)

/-- Finite support-class number is unchanged by evaluation in the surreal field. -/
theorem hasFiniteSupportClasses_iff_toSurreal (x : Surreal.{u}) :
    HasFiniteSupportClasses x ↔ (ArchimedeanClass.mk '' (toSurreal x).support).Finite := by
  rw [hasFiniteSupportClasses_iff, ← image_supportArchimedeanClasses]
  exact (Set.finite_image_iff archimedeanClassMap_injective.injOn).symm

/-- LM24 reducedness: a nonzero class value whose support and support after subtracting one
intersect in a single Archimedean class, including the possible zero class. -/
def IsReduced (x : Surreal.{u}) : Prop :=
  x ≠ 0 ∧ ∃ c : ArchimedeanClass Surreal.{u},
    support x ∩ support (x - 1) ⊆ {i | ArchimedeanClass.mk i = c}

/-- The defining nonzero and support-intersection conditions for class-coded reducedness. -/
theorem isReduced_iff (x : Surreal.{u}) :
    IsReduced x ↔ x ≠ 0 ∧ ∃ c : ArchimedeanClass Surreal.{u},
      support x ∩ support (x - 1) ⊆ {i | ArchimedeanClass.mk i = c} := (Iff.rfl)

/-- Class-coded reducedness is exactly the unsigned Conway-support formula after evaluation. -/
theorem isReduced_iff_toSurreal (x : Surreal.{u}) :
    IsReduced x ↔ toSurreal x ≠ 0 ∧ ∃ c : ArchimedeanClass _root_.Surreal.{u},
      (toSurreal x).support ∩ (toSurreal x - 1).support ⊆
        {i | ArchimedeanClass.mk i = c} := by
  rw [isReduced_iff]
  have hzero : x ≠ 0 ↔ toSurreal x ≠ 0 := by
    constructor
    · intro hx h
      exact hx (toSurreal_injective (h.trans toSurreal_zero.symm))
    · intro hx h
      exact hx (h ▸ toSurreal_zero)
  constructor
  · rintro ⟨hx, c, hc⟩
    refine ⟨hzero.mp hx, archimedeanClassMap c, ?_⟩
    intro i hi
    rw [← image_support_inter_support_sub_one] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    change ArchimedeanClass.mk (toSurreal j) = archimedeanClassMap c
    rw [← archimedeanClassMap_mk]
    exact congrArg archimedeanClassMap (hc hj)
  · rintro ⟨hx, c, hc⟩
    obtain ⟨c, rfl⟩ := archimedeanClassMap_surjective c
    refine ⟨hzero.mpr hx, c, ?_⟩
    intro i hi
    apply archimedeanClassMap_injective
    rw [archimedeanClassMap_mk]
    apply hc
    rw [← image_support_inter_support_sub_one]
    exact ⟨i, hi, rfl⟩

end ZFSet.Surreal
