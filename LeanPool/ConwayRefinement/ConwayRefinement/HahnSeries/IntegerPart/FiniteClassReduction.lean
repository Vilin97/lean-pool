/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.ReducedCharacterization
public import Mathlib.Data.Set.Finite.Basic

/-!
# Removing the leading support class

The finite-product calculation preceding LM24, Definition 8.4.2 repeatedly separates the leading
reduction from the open truncation. The open truncation has a strictly smaller set of support
classes. In the nonzero-truncation case the reduction has closed truncation equal to itself and
open truncation equal to one, so it is reduced in the sense of LM24, Definition 8.2.6.

Support classes include the zero class `⊤`. Mathlib orders Archimedean classes oppositely to LM24;
the open truncation at the leading class therefore retains the strictly greater Mathlib classes.
-/

public noncomputable section

open FiniteArchimedeanClass
open scoped HahnSeries

namespace HahnSeries.Nonpositive

variable {K G R : Type*}
variable [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
variable [Module K G] [IsOrderedModule K G]

section Ring

variable [Ring R]

/-- The Archimedean classes met by the support, including the zero class when zero is in the
support. This is a set of classes, not a set of exponents. -/
def supportArchimedeanClasses (x : Nonpositive G R) : Set (ArchimedeanClass G) :=
  ArchimedeanClass.mk '' (x : R⟦G⟧).support

/-- A class meets the support exactly when it contains an exponent with nonzero coefficient. -/
theorem mem_supportArchimedeanClasses (x : Nonpositive G R) (c : ArchimedeanClass G) :
    c ∈ supportArchimedeanClasses x ↔
      ∃ g ∈ (x : R⟦G⟧).support, ArchimedeanClass.mk g = c :=
  (Iff.rfl)

/-- The zero series meets no Archimedean class. -/
@[simp]
theorem supportArchimedeanClasses_zero :
    supportArchimedeanClasses (0 : Nonpositive G R) = ∅ := by
  ext c
  simp [mem_supportArchimedeanClasses]

/-- Open-class truncation cannot introduce a support class. -/
theorem supportArchimedeanClasses_tau_subset (c : FiniteArchimedeanClass G)
    (x : Nonpositive G R) :
    supportArchimedeanClasses (tau (K := K) c x) ⊆ supportArchimedeanClasses x := by
  rintro _ ⟨g, hg, rfl⟩
  refine ⟨g, ?_, rfl⟩
  by_cases hball : g ∈ ball K c
  · rw [HahnSeries.mem_support, coeff_tau_of_mem c x hball] at hg
    exact hg
  · rw [HahnSeries.mem_support, coeff_tau_of_not_mem c x hball] at hg
    exact (hg rfl).elim

/-- A nonzero series meets its leading Archimedean class. -/
theorem leadingClass_mem_supportArchimedeanClasses (x : Nonpositive G R) (hx : x ≠ 0)
    (horder : (x : R⟦G⟧).order ≠ 0) :
    (leadingClass x horder).val ∈ supportArchimedeanClasses x := by
  refine ⟨(x : R⟦G⟧).order, ?_, (leadingClass_val x horder).symm⟩
  exact (HahnSeries.mem_support _ _).mpr
    (HahnSeries.coeff_order_eq_zero.not.mpr fun h ↦ hx (Subtype.ext h))

/-- Open truncation at the leading class removes that class from the support. -/
theorem leadingClass_not_mem_supportArchimedeanClasses_tau (x : Nonpositive G R)
    (horder : (x : R⟦G⟧).order ≠ 0) :
    (leadingClass x horder).val ∉
      supportArchimedeanClasses (tau (K := K) (leadingClass x horder) x) := by
  rintro ⟨g, hg, hclass⟩
  have hgCoeff :
      ((tau (K := K) (leadingClass x horder) x : Nonpositive G R) : R⟦G⟧).coeff g ≠ 0 :=
    (HahnSeries.mem_support _ _).mp hg
  have hgBall : g ∈ ball K (leadingClass x horder) := by
    by_contra hnot
    exact hgCoeff (coeff_tau_of_not_mem (K := K) (leadingClass x horder) x hnot)
  have hg0 : g ≠ 0 := by
    intro hgzero
    subst g
    exact (leadingClass x horder).prop hclass.symm
  have hlt := (FiniteArchimedeanClass.mem_ball_iff K).mp hgBall hg0
  exact (ne_of_lt hlt) (Subtype.ext hclass.symm)

/-- The open truncation at a nonconstant series' leading class has strictly fewer support
classes, in the sense of strict set inclusion. -/
theorem supportArchimedeanClasses_tau_ssubset (x : Nonpositive G R) (hx : x ≠ 0)
    (horder : (x : R⟦G⟧).order ≠ 0) :
    supportArchimedeanClasses (tau (K := K) (leadingClass x horder) x) ⊂
      supportArchimedeanClasses x := by
  refine Set.ssubset_iff_subset_ne.mpr
    ⟨supportArchimedeanClasses_tau_subset (leadingClass x horder) x, ?_⟩
  intro heq
  exact leadingClass_not_mem_supportArchimedeanClasses_tau x horder
    (heq ▸ leadingClass_mem_supportArchimedeanClasses x hx horder)

/-- A nonzero series contained in a closed class ball with open truncation one is reduced. -/
theorem isReduced_of_T_eq_self_of_tau_eq_one (c : FiniteArchimedeanClass G)
    (x : Nonpositive G R) (hx : x ≠ 0) (hT : T (K := K) c x = x)
    (htau : tau (K := K) c x = 1) : IsReduced x := by
  refine isReduced_of_support_inter_support_sub_one_subset hx c.val ?_
  rintro g ⟨hg, hgSub⟩
  have hg0 : g ≠ 0 := by
    intro hzero
    subst g
    have hcoeff := congrArg (fun y : Nonpositive G R ↦ (y : R⟦G⟧).coeff 0) htau
    rw [coeff_tau_of_mem (K := K) c x (zero_mem _)] at hcoeff
    have hsubCoeff := (HahnSeries.mem_support _ _).mp hgSub
    change (((x : R⟦G⟧) - 1).coeff 0) ≠ 0 at hsubCoeff
    rw [HahnSeries.coeff_sub, HahnSeries.coeff_one, hcoeff] at hsubCoeff
    simp at hsubCoeff
  have hgClosed : g ∈ closedBall K c := by
    by_contra hnot
    have hcoeff := (HahnSeries.mem_support _ _).mp hg
    rw [← hT, coeff_T_of_not_mem (K := K) c x hnot] at hcoeff
    exact hcoeff rfl
  have hgNotBall : g ∉ ball K c := by
    intro hball
    have hcoeff := congrArg (fun y : Nonpositive G R ↦ (y : R⟦G⟧).coeff g) htau
    rw [coeff_tau_of_mem (K := K) c x hball] at hcoeff
    change (x : R⟦G⟧).coeff g = (1 : R⟦G⟧).coeff g at hcoeff
    rw [HahnSeries.coeff_one, if_neg hg0] at hcoeff
    exact (HahnSeries.mem_support _ _).mp hg hcoeff
  have hle := (FiniteArchimedeanClass.mem_closedBall_iff K).mp hgClosed hg0
  have hnlt : ¬ c < FiniteArchimedeanClass.mk g hg0 := fun hlt ↦
    hgNotBall ((FiniteArchimedeanClass.mem_ball_iff K).mpr fun _ ↦ hlt)
  exact congrArg Subtype.val (le_antisymm (not_lt.mp hnlt) hle)

/-- A reduced series meets at most its reduced class and the zero class, hence finitely many
Archimedean classes even when its support is infinite. -/
theorem IsReduced.supportArchimedeanClasses_finite {x : Nonpositive G R} (hx : IsReduced x) :
    (supportArchimedeanClasses x).Finite := by
  obtain ⟨_, c, hc⟩ := hx.elim
  apply ((Set.finite_singleton c).insert ⊤).subset
  rintro _ ⟨g, hg, rfl⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  by_cases hg0 : g = 0
  · left
    rw [hg0, ArchimedeanClass.mk_zero]
  · right
    apply hc
    refine ⟨hg, ?_⟩
    rw [HahnSeries.mem_support]
    change ((x : R⟦G⟧) - 1).coeff g ≠ 0
    rw [HahnSeries.coeff_sub, HahnSeries.coeff_one, if_neg hg0, sub_zero]
    exact (HahnSeries.mem_support _ _).mp hg

end Ring

section Field

variable [Field R]

/-- A reduction with nonzero open truncation is fixed by the closed truncation. -/
theorem T_rho_of_tau_ne_zero (u : HahnEmbedding.ArchimedeanStrata K G)
    (c : FiniteArchimedeanClass G) (x : Nonpositive G R)
    (htau : tau (K := K) c x ≠ 0) :
    T (K := K) c (rho u c x) = rho u c x := by
  apply mul_right_cancel₀ htau
  calc
    T (K := K) c (rho u c x) * tau (K := K) c x =
        T (K := K) c (rho u c x) * T (K := K) c (tau (K := K) c x) := by rw [T_tau]
    _ = T (K := K) c (rho u c x * tau (K := K) c x) := (map_mul _ _ _).symm
    _ = T (K := K) c (T (K := K) c x) := by
      rw [rho_of_tau_ne_zero u c x htau, reductionQuotient_mul_tau]
    _ = T (K := K) c x := T_T c x
    _ = rho u c x * tau (K := K) c x := by
      rw [rho_of_tau_ne_zero u c x htau, reductionQuotient_mul_tau]

/-- A reduction with nonzero open truncation has open truncation one. -/
theorem tau_rho_of_tau_ne_zero (u : HahnEmbedding.ArchimedeanStrata K G)
    (c : FiniteArchimedeanClass G) (x : Nonpositive G R)
    (htau : tau (K := K) c x ≠ 0) :
    tau (K := K) c (rho u c x) = 1 := by
  apply mul_right_cancel₀ htau
  calc
    tau (K := K) c (rho u c x) * tau (K := K) c x =
        tau (K := K) c (rho u c x * tau (K := K) c x) := by
      simpa only [tau_tau] using
        ((tau (K := K) c).map_mul (rho u c x) (tau (K := K) c x)).symm
    _ = tau (K := K) c (T (K := K) c x) := by
      rw [rho_of_tau_ne_zero u c x htau, reductionQuotient_mul_tau]
    _ = tau (K := K) c x := tau_T c x
    _ = 1 * tau (K := K) c x := (one_mul _).symm

/-- The leading reduction of a nonzero, nonconstant series is reduced when the open truncation
is nonzero, as in LM24, Proposition 8.2.5. -/
theorem isReduced_rho_leadingClass_of_tau_ne_zero
    (u : HahnEmbedding.ArchimedeanStrata K G) (x : Nonpositive G R) (hx : x ≠ 0)
    (horder : (x : R⟦G⟧).order ≠ 0)
    (htau : tau (K := K) (leadingClass x horder) x ≠ 0) :
    IsReduced (rho u (leadingClass x horder) x) := by
  have hrho0 : rho u (leadingClass x horder) x ≠ 0 := by
    intro hrho
    have hfac := reductionQuotient_mul_tau u (leadingClass x horder) x
      (fun hzero ↦ htau ((tauBall_eq_zero_iff (leadingClass x horder) x).mp hzero))
    rw [← rho_of_tau_ne_zero u (leadingClass x horder) x htau,
      hrho, zero_mul, T_leadingClass] at hfac
    exact hx hfac.symm
  exact isReduced_of_T_eq_self_of_tau_eq_one (leadingClass x horder)
    (rho u (leadingClass x horder) x) hrho0
      (T_rho_of_tau_ne_zero u (leadingClass x horder) x htau)
      (tau_rho_of_tau_ne_zero u (leadingClass x horder) x htau)

end Field

end HahnSeries.Nonpositive
