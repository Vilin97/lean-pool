/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.RightHalfPlane

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Complex Ideal IsDedekindDomain NumberField.InfinitePlace

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

/-- A completed dedekind xi used in the Odlyzko-bound argument. -/
noncomputable def completedDedekindXi (s : ℂ) : ℂ :=
  s * (s - 1) * CompletedZeta.completed K s

lemma completedDedekindXi_ne_zero_of_one_lt_re {s : ℂ}
    (hs : 1 < s.re) :
    completedDedekindXi K s ≠ 0 := by
  exact mul_ne_zero
    (mul_ne_zero
      (by
        intro h
        have : s.re = 0 := congrArg Complex.re h
        linarith)
      (by
        intro h
        have : s.re - 1 = 0 := by
          simpa using congrArg Complex.re h
        linarith))
    (completedDedekindZeta_ne_zero_of_one_lt_re K hs)

variable [IsTotallyComplex K]

theorem logDeriv_completedDedekindXi_rightHalfPlane {s : ℂ}
    (hs : 1 < s.re) :
    logDeriv (completedDedekindXi K) s =
      1 / s + 1 / (s - 1) +
        Complex.log ((|(discr K : ℝ)| : ℝ) : ℂ) / 2 +
        nrComplexPlaces K *
          (Complex.digamma s - Complex.log (2 * (Real.pi : ℂ))) -
        ∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
          primePowerLogTerm K pe.1 pe.2 s := by
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at hs
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have : s.re - 1 = 0 := by
      simpa using congrArg Complex.re h
    linarith
  have hdiffS : DifferentiableAt ℂ (fun z : ℂ ↦ z) s := differentiableAt_id
  have hdiffS1 : DifferentiableAt ℂ (fun z : ℂ ↦ z - 1) s := by simp
  have hprod0 : s * (s - 1) ≠ 0 := mul_ne_zero hs0 hs1
  have hdiffCompleted :
      DifferentiableAt ℂ (CompletedZeta.completed K) s := by
    change DifferentiableAt ℂ
      (fun z ↦ CompletedZeta.discriminantFactor K z *
        CompletedZeta.archimedeanFactor K z * dedekindZeta K z) s
    exact ((differentiable_dedekindDiscriminantFactor K s).mul
      (differentiableAt_dedekindArchimedeanFactor_of_isTotallyComplex K
        (by linarith))).mul
      (differentiableAt_dedekindZeta K hs)
  change logDeriv
    (fun z : ℂ ↦ z * (z - 1) * CompletedZeta.completed K z) s = _
  rw [logDeriv_mul (f := fun z : ℂ ↦ z * (z - 1))
      (g := CompletedZeta.completed K) s hprod0
      (completedDedekindZeta_ne_zero_of_one_lt_re K hs)
      (hdiffS.mul hdiffS1)
      hdiffCompleted,
    logDeriv_mul (f := fun z : ℂ ↦ z) (g := fun z : ℂ ↦ z - 1)
      s hs0 hs1 hdiffS hdiffS1,
    logDeriv_apply, logDeriv_apply]
  simp only [deriv_id'', deriv_sub_const, one_div]
  rw [logDeriv_completedDedekindZeta_rightHalfPlane_eq_primePower K hs]
  ring

end NumberField.Odlyzko
