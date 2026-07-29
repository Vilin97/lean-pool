/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.PrincipalClass

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Complex Ideal NumberField NumberField.Units
open scoped nonZeroDivisors

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

open Classical in
/-- An inverse class ideal representative used in the Odlyzko-bound argument. -/
noncomputable def inverseClassIdealRepresentative
    (C : ClassGroup (𝓞 K)) : (Ideal (𝓞 K))⁰ :=
  Classical.choose
    (ClassGroup.mk0_surjective (R := 𝓞 K) C⁻¹)

open Classical in
@[simp]
theorem mk0_inverseClassIdealRepresentative
    (C : ClassGroup (𝓞 K)) :
    ClassGroup.mk0 (inverseClassIdealRepresentative K C) = C⁻¹ :=
  Classical.choose_spec
    (ClassGroup.mk0_surjective (R := 𝓞 K) C⁻¹)

open Classical in
theorem partialDedekindZeta_eq_normalized_fundamentalConeZeta_of_mk0
    (C : ClassGroup (𝓞 K)) (J : (Ideal (𝓞 K))⁰)
    (hJ : ClassGroup.mk0 J = C⁻¹) {s : ℂ} (hs : 1 < s.re) :
    partialDedekindZeta K C s =
      (torsionOrder K : ℂ)⁻¹ *
        (absNorm (J : Ideal (𝓞 K)) : ℂ) ^ s *
        fundamentalConeZeta K J s := by
  have hcone :=
    fundamentalConeZeta_eq_torsion_mul_principalIdealZeta K J s
  have hprincipal :=
    principalIdealZeta_eq_inverseNormPower_mul_partialDedekindZeta K J hs
  have hclass : (ClassGroup.mk0 J)⁻¹ = C := by simp_all
  rw [hprincipal, hclass] at hcone
  have ht : (torsionOrder K : ℂ) ≠ 0 := by
    exact_mod_cast torsionOrder_ne_zero K
  have hnNat :
      absNorm (J : Ideal (𝓞 K)) ≠ 0 :=
    absNorm_ne_zero_of_nonZeroDivisors J
  have hn : (absNorm (J : Ideal (𝓞 K)) : ℂ) ≠ 0 := by simp_all
  have hpow :
      (absNorm (J : Ideal (𝓞 K)) : ℂ) ^ s *
          (absNorm (J : Ideal (𝓞 K)) : ℂ) ^ (-s) = 1 := by
    rw [← Complex.cpow_add s (-s) hn]
    simp
  grind

open Classical in
theorem partialDedekindZeta_eq_normalized_fundamentalConeZeta
    (C : ClassGroup (𝓞 K)) {s : ℂ} (hs : 1 < s.re) :
    partialDedekindZeta K C s =
      (torsionOrder K : ℂ)⁻¹ *
        (absNorm
          (inverseClassIdealRepresentative K C : Ideal (𝓞 K)) : ℂ) ^ s *
        fundamentalConeZeta K (inverseClassIdealRepresentative K C) s :=
  partialDedekindZeta_eq_normalized_fundamentalConeZeta_of_mk0 K C
    (inverseClassIdealRepresentative K C)
    (mk0_inverseClassIdealRepresentative K C) hs

open Classical in
theorem sum_normalized_fundamentalConeZeta
    {s : ℂ} (hs : 1 < s.re) :
    ∑ C : ClassGroup (𝓞 K),
        (torsionOrder K : ℂ)⁻¹ *
          (absNorm
            (inverseClassIdealRepresentative K C : Ideal (𝓞 K)) : ℂ) ^ s *
          fundamentalConeZeta K (inverseClassIdealRepresentative K C) s =
      NumberField.dedekindZeta K s := by
  rw [← sum_partialDedekindZeta K hs]
  apply Finset.sum_congr rfl
  intro C _
  exact
    (partialDedekindZeta_eq_normalized_fundamentalConeZeta K C hs).symm

end NumberField.Odlyzko
