/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.Reduction
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.Reduced

/-!
# Reducedness and leading-class reduction

This module proves the nonconstant case of LM24, Proposition 8.2.5 `(4) ↔ (5)`. For a
nonpositive Hahn series whose lowest exponent is nonzero, reducedness is equivalent to its
open truncation at the lowest exponent's Archimedean class being zero or one. The proof treats
the exponent zero explicitly: it belongs to both supports exactly when the constant coefficient
is neither zero nor one.
-/

public noncomputable section

namespace HahnSeries.Nonpositive

open FiniteArchimedeanClass

variable {K G R : Type*}
variable [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
variable [Module K G] [IsOrderedModule K G]
variable [Field R]

private theorem coeff_sub_one_of_ne_zero (x : Nonpositive G R) {g : G} (hg : g ≠ 0) :
    ((x - 1 : Nonpositive G R) : R⟦G⟧).coeff g = (x : R⟦G⟧).coeff g := by
  change ((x : R⟦G⟧) - 1).coeff g = _
  rw [HahnSeries.coeff_sub, HahnSeries.coeff_one, if_neg hg, sub_zero]

private theorem leadingClass_le_mk_of_mem_support (x : Nonpositive G R)
    (horder : (x : R⟦G⟧).order ≠ 0) {g : G} (hg : g ∈ (x : R⟦G⟧).support)
    (hg0 : g ≠ 0) :
    leadingClass x horder ≤ FiniteArchimedeanClass.mk g hg0 := by
  rw [show leadingClass x horder = FiniteArchimedeanClass.mk
    (x : R⟦G⟧).order horder by apply Subtype.ext; simp]
  apply (FiniteArchimedeanClass.mk_le_mk horder hg0).mpr
  have horderLe : (x : R⟦G⟧).order ≤ g :=
    HahnSeries.order_le_of_coeff_ne_zero ((HahnSeries.mem_support _ _).mp hg)
  have hgNonpos : g ≤ 0 := support_subset x hg
  simpa using ArchimedeanClass.min_le_mk_of_le_of_le horderLe hgNonpos

private theorem tau_eq_zero_of_support_nonzero_class
    (x : Nonpositive G R) (horder : (x : R⟦G⟧).order ≠ 0)
    (hcoeffZero : (x : R⟦G⟧).coeff 0 = 0)
    (hclass : ∀ g ∈ (x : R⟦G⟧).support, ∀ hg0 : g ≠ 0,
      FiniteArchimedeanClass.mk g hg0 = leadingClass x horder) :
    tau (K := K) (leadingClass x horder) x = 0 := by
  apply Subtype.ext
  ext g
  by_cases hg0 : g = 0
  · subst g
    rw [coeff_tau_of_mem]
    · exact hcoeffZero
    · exact zero_mem _
  by_cases hg : g ∈ (x : R⟦G⟧).support
  · rw [coeff_tau_of_not_mem]
    · simp
    · intro hball
      have hlt := (FiniteArchimedeanClass.mem_ball_iff K).mp hball hg0
      rw [hclass g hg hg0] at hlt
      exact lt_irrefl _ hlt
  · have hcoeff : (x : R⟦G⟧).coeff g = 0 :=
      not_ne_iff.mp ((HahnSeries.mem_support _ _).not.mp hg)
    by_cases hball : g ∈ ball K (leadingClass x horder)
    · rw [coeff_tau_of_mem _ _ hball, hcoeff]; simp
    · rw [coeff_tau_of_not_mem _ _ hball]; simp

private theorem tau_eq_C_constantCoeff_of_support_nonzero_class
    (x : Nonpositive G R) (horder : (x : R⟦G⟧).order ≠ 0)
    (hclass : ∀ g ∈ (x : R⟦G⟧).support, ∀ hg0 : g ≠ 0,
      FiniteArchimedeanClass.mk g hg0 = leadingClass x horder) :
    tau (K := K) (leadingClass x horder) x = C ((x : R⟦G⟧).coeff 0) := by
  apply Subtype.ext
  ext g
  by_cases hg0 : g = 0
  · subst g
    rw [coeff_tau_of_mem]
    · simp
    · exact zero_mem _
  · rw [coe_C]
    change ((tau (K := K) (leadingClass x horder) x : Nonpositive G R) :
      R⟦G⟧).coeff g = (HahnSeries.single 0 ((x : R⟦G⟧).coeff 0)).coeff g
    rw [HahnSeries.coeff_single, if_neg hg0]
    by_cases hg : g ∈ (x : R⟦G⟧).support
    · rw [coeff_tau_of_not_mem]
      intro hball
      have hlt := (FiniteArchimedeanClass.mem_ball_iff K).mp hball hg0
      rw [hclass g hg hg0] at hlt
      exact lt_irrefl _ hlt
    · have hcoeff : (x : R⟦G⟧).coeff g = 0 :=
        not_ne_iff.mp ((HahnSeries.mem_support _ _).not.mp hg)
      by_cases hball : g ∈ ball K (leadingClass x horder)
      · rw [coeff_tau_of_mem _ _ hball, hcoeff]
      · rw [coeff_tau_of_not_mem _ _ hball]

/-- LM24, Proposition 8.2.5 `(4) ↔ (5)` for a series with nonzero lowest exponent. -/
theorem isReduced_iff_tau_leadingClass_eq_zero_or_one
    (x : Nonpositive G R) (hx : x ≠ 0) (horder : (x : R⟦G⟧).order ≠ 0) :
    IsReduced x ↔
      tau (K := K) (leadingClass x horder) x = 0 ∨
        tau (K := K) (leadingClass x horder) x = 1 := by
  constructor
  · intro hReduced
    obtain ⟨_, d, hd⟩ := hReduced.elim
    have horderSupport : (x : R⟦G⟧).order ∈ (x : R⟦G⟧).support := by
      exact (HahnSeries.mem_support _ _).mpr
        (HahnSeries.coeff_order_eq_zero.not.mpr (fun h ↦ hx (Subtype.ext h)))
    have horderSubSupport :
        (x : R⟦G⟧).order ∈ ((x - 1 : Nonpositive G R) : R⟦G⟧).support := by
      rw [HahnSeries.mem_support, coeff_sub_one_of_ne_zero x horder]
      exact HahnSeries.coeff_order_eq_zero.not.mpr (fun h ↦ hx (Subtype.ext h))
    have hdLeading : ArchimedeanClass.mk (x : R⟦G⟧).order = d :=
      hd ⟨horderSupport, horderSubSupport⟩
    have hclass : ∀ g ∈ (x : R⟦G⟧).support, ∀ hg0 : g ≠ 0,
        FiniteArchimedeanClass.mk g hg0 = leadingClass x horder := by
      intro g hg hg0
      apply Subtype.ext
      rw [FiniteArchimedeanClass.val_mk, leadingClass_val]
      exact (hd ⟨hg, by
        rw [HahnSeries.mem_support, coeff_sub_one_of_ne_zero x hg0]
        exact (HahnSeries.mem_support _ _).mp hg⟩).trans hdLeading.symm
    have hconstant : (x : R⟦G⟧).coeff 0 = 0 ∨ (x : R⟦G⟧).coeff 0 = 1 := by
      by_contra hnot
      push Not at hnot
      have hzeroSupport : 0 ∈ (x : R⟦G⟧).support :=
        (HahnSeries.mem_support _ _).mpr hnot.1
      have hzeroSubSupport :
          0 ∈ ((x - 1 : Nonpositive G R) : R⟦G⟧).support := by
        rw [HahnSeries.mem_support]
        change (((x : R⟦G⟧) - 1).coeff 0) ≠ 0
        rw [HahnSeries.coeff_sub, HahnSeries.coeff_one, if_pos rfl]
        exact sub_ne_zero.mpr hnot.2
      have htop : (⊤ : ArchimedeanClass G) = d := hd ⟨hzeroSupport, hzeroSubSupport⟩
      exact (FiniteArchimedeanClass.mk (x : R⟦G⟧).order horder).prop
        (hdLeading.trans htop.symm)
    rcases hconstant with hzero | hone
    · exact Or.inl (tau_eq_zero_of_support_nonzero_class x horder hzero hclass)
    · right
      rw [tau_eq_C_constantCoeff_of_support_nonzero_class x horder hclass, hone]
      exact map_one C
  · intro htau
    refine isReduced_of_support_inter_support_sub_one_subset hx
      (ArchimedeanClass.mk (x : R⟦G⟧).order) ?_
    intro g hg
    have hgSupport := hg.1
    have hg0 : g ≠ 0 := by
      intro hzero
      subst g
      rcases htau with htau | htau
      · have hcoeff := congrArg
          (fun y : Nonpositive G R ↦ (y : R⟦G⟧).coeff 0) htau
        rw [coeff_tau_of_mem _ _ (zero_mem _)] at hcoeff
        exact ((HahnSeries.mem_support _ _).mp hgSupport) hcoeff
      · have hcoeff := congrArg
          (fun y : Nonpositive G R ↦ (y : R⟦G⟧).coeff 0) htau
        rw [coeff_tau_of_mem _ _ (zero_mem _)] at hcoeff
        change (x : R⟦G⟧).coeff 0 = (1 : R⟦G⟧).coeff 0 at hcoeff
        simp only [HahnSeries.coeff_one] at hcoeff
        have hsubCoeff := (HahnSeries.mem_support _ _).mp hg.2
        change (((x : R⟦G⟧) - 1).coeff 0) ≠ 0 at hsubCoeff
        rw [HahnSeries.coeff_sub, HahnSeries.coeff_one, hcoeff] at hsubCoeff
        simp at hsubCoeff
    have hle := leadingClass_le_mk_of_mem_support x horder hgSupport hg0
    have hnlt : ¬ leadingClass x horder < FiniteArchimedeanClass.mk g hg0 := by
      intro hlt
      have hball : g ∈ ball K (leadingClass x horder) :=
        (FiniteArchimedeanClass.mem_ball_iff K).mpr fun _ ↦ hlt
      rcases htau with htau | htau
      · have hcoeff := congrArg
          (fun y : Nonpositive G R ↦ (y : R⟦G⟧).coeff g) htau
        rw [coeff_tau_of_mem _ _ hball] at hcoeff
        exact ((HahnSeries.mem_support _ _).mp hgSupport) hcoeff
      · have hcoeff := congrArg
          (fun y : Nonpositive G R ↦ (y : R⟦G⟧).coeff g) htau
        rw [coeff_tau_of_mem _ _ hball] at hcoeff
        change (x : R⟦G⟧).coeff g = (1 : R⟦G⟧).coeff g at hcoeff
        simp only [HahnSeries.coeff_one, if_neg hg0] at hcoeff
        exact ((HahnSeries.mem_support _ _).mp hgSupport) hcoeff
    have heq : leadingClass x horder = FiniteArchimedeanClass.mk g hg0 :=
      le_antisymm hle (not_lt.mp hnlt)
    have hval := congrArg Subtype.val heq
    simpa using hval.symm

end HahnSeries.Nonpositive
