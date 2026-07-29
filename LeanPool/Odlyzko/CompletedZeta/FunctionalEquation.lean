/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.ClassThetaCenteredClassInvariant

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Complex Ideal NumberField NumberField.InfinitePlace NumberField.Units
open scoped nonZeroDivisors

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

omit [IsTotallyComplex K] in
open Classical in
theorem poleClearedCenteredClassThetaIntegral_functionalEquation
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    poleClearedCenteredClassThetaIntegral K I s =
      poleClearedCenteredClassThetaIntegral K
        (traceDualIdealUnit K I) (1 - s) := by
  rw [poleClearedCenteredClassThetaIntegral,
    poleClearedCenteredClassThetaIntegral,
    traceDualIdealUnit_traceDualIdealUnit]
  ring_nf

omit [IsTotallyComplex K] in
open Classical in
theorem poleClearedCenteredFractionalClassContribution_functionalEquation
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    poleClearedCenteredFractionalClassContribution K I s =
      poleClearedCenteredFractionalClassContribution K
        (traceDualIdealUnit K I) (1 - s) := by
  rw [poleClearedCenteredFractionalClassContribution,
    poleClearedCenteredFractionalClassContribution,
    poleClearedCenteredClassThetaIntegral_functionalEquation]

open Classical in
/-- A pole cleared completed dedekind zeta continuation used in the Odlyzko-bound argument. -/
noncomputable def poleClearedCompletedDedekindZetaContinuation (s : ℂ) : ℂ :=
  ∑ C : ClassGroup (𝓞 K),
    poleClearedCenteredFractionalClassContribution K
      (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C)) s

open Classical in
theorem differentiable_poleClearedCompletedDedekindZetaContinuation :
    Differentiable ℂ (poleClearedCompletedDedekindZetaContinuation K) := by
  unfold poleClearedCompletedDedekindZetaContinuation
  apply Differentiable.fun_sum
  intro C _
  exact differentiable_poleClearedCenteredFractionalClassContribution K
    (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C))

omit [IsTotallyComplex K] in
open Classical in
theorem mk_traceDual_inverseClassIdealRepresentative_eq_reindexed
    (C : ClassGroup (𝓞 K)) :
    ClassGroup.mk K
        (traceDualIdealUnit K
          (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C))) =
      ClassGroup.mk K
        (FractionalIdeal.mk0 K
          (inverseClassIdealRepresentative K
            (traceDualInverseClassEquiv K C))) := by
  rw [mk_traceDualIdealUnit_eq_traceDualClassEquiv,
    ClassGroup.mk_mk0, ClassGroup.mk_mk0,
    mk0_inverseClassIdealRepresentative,
    mk0_inverseClassIdealRepresentative,
    traceDualInverseClassEquiv_apply, inv_inv]

open Classical in
theorem poleClearedCompletedDedekindZetaContinuation_functionalEquation
    (s : ℂ) :
    poleClearedCompletedDedekindZetaContinuation K s =
      poleClearedCompletedDedekindZetaContinuation K (1 - s) := by
  rw [poleClearedCompletedDedekindZetaContinuation,
    poleClearedCompletedDedekindZetaContinuation]
  calc
    (∑ C : ClassGroup (𝓞 K),
        poleClearedCenteredFractionalClassContribution K
          (FractionalIdeal.mk0 K
            (inverseClassIdealRepresentative K C)) s) =
        ∑ C : ClassGroup (𝓞 K),
          poleClearedCenteredFractionalClassContribution K
            (traceDualIdealUnit K
              (FractionalIdeal.mk0 K
                (inverseClassIdealRepresentative K C))) (1 - s) := by
      apply Finset.sum_congr rfl
      intro C _
      exact
        poleClearedCenteredFractionalClassContribution_functionalEquation K
          (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C)) s
    _ = ∑ C : ClassGroup (𝓞 K),
          poleClearedCenteredFractionalClassContribution K
            (FractionalIdeal.mk0 K
              (inverseClassIdealRepresentative K
                (traceDualInverseClassEquiv K C))) (1 - s) := by
      apply Finset.sum_congr rfl
      intro C _
      exact congrFun
        (poleClearedCenteredFractionalClassContribution_eq_of_mk_eq K
          (traceDualIdealUnit K
            (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C)))
          (FractionalIdeal.mk0 K
            (inverseClassIdealRepresentative K
              (traceDualInverseClassEquiv K C)))
          (mk_traceDual_inverseClassIdealRepresentative_eq_reindexed K C))
        (1 - s)
    _ = ∑ C : ClassGroup (𝓞 K),
          poleClearedCenteredFractionalClassContribution K
            (FractionalIdeal.mk0 K
              (inverseClassIdealRepresentative K C)) (1 - s) := by
      exact Equiv.sum_comp (traceDualInverseClassEquiv K)
        (fun C ↦ poleClearedCenteredFractionalClassContribution K
          (FractionalIdeal.mk0 K
            (inverseClassIdealRepresentative K C)) (1 - s))

open Classical in
theorem poleClearedCompletedDedekindZetaContinuation_eq_completedDedekindZeta
    {s : ℂ} (hs : 1 < s.re) :
    poleClearedCompletedDedekindZetaContinuation K s =
      (Module.finrank ℚ K : ℂ) * s * (1 - s) *
        CompletedZeta.completed K s := by
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at hs
  have hs1 : s ≠ 1 := by
    intro h
    simp_all
  rw [poleClearedCompletedDedekindZetaContinuation]
  calc
    (∑ C : ClassGroup (𝓞 K),
        poleClearedCenteredFractionalClassContribution K
          (FractionalIdeal.mk0 K
            (inverseClassIdealRepresentative K C)) s) =
        ∑ C : ClassGroup (𝓞 K),
          (Module.finrank ℚ K : ℂ) * s * (1 - s) *
            centeredContinuedClassThetaIntegral K C s := by
      apply Finset.sum_congr rfl
      intro C _
      rw [poleClearedCenteredFractionalClassContribution,
        poleClearedCenteredClassThetaIntegral_eq_mul_continued K _ hs0 hs1,
        centeredContinuedClassThetaIntegral]
      ring
    _ = (Module.finrank ℚ K : ℂ) * s * (1 - s) *
          ∑ C : ClassGroup (𝓞 K),
            centeredContinuedClassThetaIntegral K C s := by
      rw [Finset.mul_sum]
    _ = _ := by
      rw [sum_centeredContinuedClassThetaIntegral K hs]

end NumberField.Odlyzko
