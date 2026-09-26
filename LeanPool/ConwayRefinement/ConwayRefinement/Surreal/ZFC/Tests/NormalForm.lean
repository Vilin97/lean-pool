/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.ZFC.Reduced
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.HahnSeries.NormalFormAdd

/-!
# A separate client of class-coded Conway normal forms

The chart and support-class predicates are used only through their public interfaces. The
normal form `ω + 2` separates reducedness from the incorrect variant that deletes exponent zero:
both its constant and its nonconstant term survive subtraction of one, in distinct Archimedean
classes. Zero is also tested separately, since nonzeroness is part of reducedness.
-/

universe u

public noncomputable section

namespace ZFSet.Surreal.Tests.NormalForm

/-- An arbitrary small Conway series is recovered from its class-coded value. -/
theorem chart_inverse (s : SurrealHahnSeries.{u}) :
    toHahnSeries (toHahnSeriesOrderIso.symm s) = s := by
  rw [toHahnSeries_eq_toSurreal, ← toHahnSeriesOrderIso_apply, OrderIso.apply_symm_apply]

/-- The native support remains set-sized after separately compiling the producer. -/
theorem support_small (x : Surreal.{u}) : Small.{u} (support x) := inferInstance

/-- Zero has finite support-class number. -/
theorem zero_hasFiniteSupportClasses : HasFiniteSupportClasses (0 : Surreal.{u}) := by
  rw [hasFiniteSupportClasses_iff_toSurreal, toSurreal_zero, _root_.Surreal.support_zero,
    Set.image_empty]
  exact Set.finite_empty

/-- Zero is not reduced, even though its support intersection is empty. -/
theorem zero_not_isReduced : ¬ IsReduced (0 : Surreal.{u}) := by
  simp only [isReduced_iff, ne_eq, not_true_eq_false, false_and, not_false_eq_true]

/-- The class-coded value with Conway normal form `ω + 2`. -/
def twoTerm : Surreal.{u} :=
  toHahnSeriesOrderIso.symm (SurrealHahnSeries.single 1 1 + SurrealHahnSeries.single 0 2)

/-- The two displayed terms are exactly the normal form of the class-coded example. -/
theorem toHahnSeries_twoTerm :
    toHahnSeries twoTerm.{u} = SurrealHahnSeries.single 1 1 + SurrealHahnSeries.single 0 2 :=
  chart_inverse _

private theorem coeff_eq_normalForm (x i : Surreal.{u}) :
    coeff x i = (toHahnSeries x).coeff (toSurreal i) := by
  rw [coeff_eq_toSurreal, toHahnSeries_eq_toSurreal, _root_.Surreal.coeff_toHahnSeries]

/-- The example has a nonzero constant coefficient distinct from one. -/
theorem twoTerm_coeff_zero : coeff twoTerm.{u} 0 = 2 := by
  rw [coeff_eq_normalForm, toHahnSeries_twoTerm, toSurreal_zero]
  simp [SurrealHahnSeries.coeff_add_apply, SurrealHahnSeries.coeff_single_of_ne]

/-- The example also has a nonzero coefficient at the nonzero exponent one. -/
theorem twoTerm_coeff_one : coeff twoTerm.{u} 1 = 1 := by
  rw [coeff_eq_normalForm, toHahnSeries_twoTerm, toSurreal_one]
  simp [SurrealHahnSeries.coeff_add_apply, SurrealHahnSeries.coeff_single_of_ne]

/-- The example is nonzero, as witnessed by its coefficient at exponent one. -/
theorem twoTerm_ne_zero : twoTerm.{u} ≠ 0 := by
  intro h
  have hcoeff := twoTerm_coeff_one.{u}
  rw [h, coeff_eq_toSurreal, toSurreal_zero, _root_.Surreal.coeff_zero] at hcoeff
  exact zero_ne_one hcoeff

private theorem coeff_sub_one (x i : Surreal.{u}) :
    coeff (x - 1) i = coeff x i - (Pi.single 0 1 : _root_.Surreal.{u} → ℝ) (toSurreal i) := by
  rw [coeff_eq_toSurreal, toSurreal_sub, toSurreal_one, coeff_eq_toSurreal]
  simp only [sub_eq_add_neg,
    _root_.Surreal.coeff_add, _root_.Surreal.coeff_neg, _root_.Surreal.coeff_one,
    Pi.add_apply, Pi.neg_apply]

/-- Both relevant coefficients remain nonzero after subtraction of one. -/
theorem twoTerm_sub_one_coeffs :
    coeff (twoTerm.{u} - 1) 0 = 1 ∧ coeff (twoTerm.{u} - 1) 1 = 1 := by
  rw [coeff_sub_one, coeff_sub_one, twoTerm_coeff_zero, twoTerm_coeff_one,
    toSurreal_zero, toSurreal_one]
  norm_num [Pi.single_apply]

/-- Exactly the exponents zero and one occur in the example. -/
theorem twoTerm_support : support twoTerm.{u} = {0, 1} := by
  ext i
  constructor
  · intro hi
    have h := (mem_support_iff_toSurreal twoTerm i).1 hi
    rw [← _root_.Surreal.support_toHahnSeries, ← toHahnSeries_eq_toSurreal,
      toHahnSeries_twoTerm] at h
    rcases SurrealHahnSeries.support_add_subset h with h | h
    · have he : toSurreal i = 1 := SurrealHahnSeries.support_single_subset h
      have hi1 : i = 1 := toSurreal_injective (he.trans toSurreal_one.symm)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, hi1, or_true]
    · have he : toSurreal i = 0 := SurrealHahnSeries.support_single_subset h
      have hi0 : i = 0 := toSurreal_injective (he.trans toSurreal_zero.symm)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, hi0, true_or]
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (rfl | rfl)
    · rw [mem_support_iff, twoTerm_coeff_zero]
      norm_num
    · rw [mem_support_iff, twoTerm_coeff_one]
      exact one_ne_zero

/-- The nonconstant example meets finitely many support classes. -/
theorem twoTerm_hasFiniteSupportClasses : HasFiniteSupportClasses twoTerm.{u} := by
  rw [hasFiniteSupportClasses_iff, twoTerm_support]
  exact ((Set.finite_singleton 1).insert 0).image _

/-- The zero exponent and nonzero exponent make the example genuinely non-reduced. -/
theorem twoTerm_not_isReduced : ¬ IsReduced twoTerm.{u} := by
  intro h
  obtain ⟨_, c, hc⟩ := (isReduced_iff twoTerm).1 h
  have hzero : ArchimedeanClass.mk (0 : Surreal.{u}) = c := hc ⟨by
    rw [mem_support_iff, twoTerm_coeff_zero]
    norm_num, by
    rw [mem_support_iff, twoTerm_sub_one_coeffs.1]
    exact one_ne_zero⟩
  have hone : ArchimedeanClass.mk (1 : Surreal.{u}) = c := hc ⟨by
    rw [mem_support_iff, twoTerm_coeff_one]
    exact one_ne_zero, by
    rw [mem_support_iff, twoTerm_sub_one_coeffs.2]
    exact one_ne_zero⟩
  have htop : ArchimedeanClass.mk (1 : Surreal.{u}) = ⊤ :=
    hone.trans (hzero.symm.trans ArchimedeanClass.mk_zero)
  exact one_ne_zero (ArchimedeanClass.mk_eq_top_iff.mp htop)

/-- Deleting zero would incorrectly satisfy a nonzero-only version of reducedness. -/
theorem twoTerm_nonzero_intersection_one_class :
    twoTerm.{u} ≠ 0 ∧ ∃ c : ArchimedeanClass Surreal.{u},
      (support twoTerm ∩ support (twoTerm - 1)) \ {0} ⊆
        {i | ArchimedeanClass.mk i = c} := by
  refine ⟨twoTerm_ne_zero, ArchimedeanClass.mk 1, ?_⟩
  intro i hi
  have hiSupport := hi.1.1
  rw [twoTerm_support, Set.mem_insert_iff, Set.mem_singleton_iff] at hiSupport
  rcases hiSupport with rfl | rfl
  · exact False.elim (hi.2 (Set.mem_singleton 0))
  · rfl

/-- The signed bridge can be used after separately compiling its producer. -/
theorem signed_reduced_iff (x : OmnificInteger.{u}) :
    IsReduced (x : Surreal.{u}) ↔
      HahnSeries.Nonpositive.IsReduced (OmnificInteger.ringEquiv x).toSignedNonpositiveHahn :=
  OmnificInteger.isReduced_iff_toSignedNonpositiveHahn x

end ZFSet.Surreal.Tests.NormalForm
