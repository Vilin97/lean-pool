/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.ClassDecomposition

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Ideal IsDedekindDomain NumberField Submodule
open scoped nonZeroDivisors

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

open Classical in
/-- A principal ideal above used in the Odlyzko-bound argument. -/
abbrev PrincipalIdealAbove (J : (Ideal (𝓞 K))⁰) :=
  {I : (Ideal (𝓞 K))⁰ //
    (J : Ideal (𝓞 K)) ∣ I ∧ IsPrincipal (I : Ideal (𝓞 K))}

open Classical in
/-- An inverse ideal class used in the Odlyzko-bound argument. -/
abbrev InverseIdealClass (J : (Ideal (𝓞 K))⁰) :=
  {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = (ClassGroup.mk0 J)⁻¹}

open Classical in
/-- An inverse ideal class equiv principal ideal above used in the Odlyzko-bound argument. -/
noncomputable def inverseIdealClassEquivPrincipalIdealAbove
    (J : (Ideal (𝓞 K))⁰) :
    InverseIdealClass K J ≃ PrincipalIdealAbove K J := by
  let e₁ :
      InverseIdealClass K J ≃
        {I : {I : (Ideal (𝓞 K))⁰ // J ∣ I} //
          IsPrincipal (I.1 : Ideal (𝓞 K))} :=
    (Equiv.dvd J).subtypeEquiv fun I ↦ by
      rw [← ClassGroup.mk0_eq_one_iff (SetLike.coe_mem _)]
      simp only [Equiv.dvd_apply]
      change ClassGroup.mk0 I = (ClassGroup.mk0 J)⁻¹ ↔
        ClassGroup.mk0 (J * I) = 1
      rw [_root_.map_mul]
      constructor
      · simp_all
      · exact mul_eq_one_iff_eq_inv'.mp
  let e₂ :
      {I : {I : (Ideal (𝓞 K))⁰ // J ∣ I} //
          IsPrincipal (I.1 : Ideal (𝓞 K))} ≃
        {I : (Ideal (𝓞 K))⁰ // J ∣ I ∧
          IsPrincipal (I : Ideal (𝓞 K))} :=
    Equiv.subtypeSubtypeEquivSubtypeInter
      (fun I : (Ideal (𝓞 K))⁰ ↦ J ∣ I)
      (fun I ↦ IsPrincipal (I : Ideal (𝓞 K)))
  let e₃ :
      {I : (Ideal (𝓞 K))⁰ // J ∣ I ∧
          IsPrincipal (I : Ideal (𝓞 K))} ≃
        PrincipalIdealAbove K J :=
    Equiv.subtypeEquivRight fun I ↦ by
      rw [nonZeroDivisors_dvd_iff_dvd_coe]
  exact e₁.trans (e₂.trans e₃)

open Classical in
theorem absNorm_inverseIdealClassEquivPrincipalIdealAbove
    (J : (Ideal (𝓞 K))⁰) (I : InverseIdealClass K J) :
    absNorm (inverseIdealClassEquivPrincipalIdealAbove K J I).1.1 =
      absNorm (J : Ideal (𝓞 K)) *
        absNorm I.1.1 := by
  simp [inverseIdealClassEquivPrincipalIdealAbove, Equiv.dvd_apply,
    map_mul]

open Classical in
private def principalIdealAboveNormFiberEquiv
    (J : (Ideal (𝓞 K))⁰) (n : ℕ) :
    {I : PrincipalIdealAbove K J //
      absNorm I.1.1 = n} ≃
      {I : (Ideal (𝓞 K))⁰ //
        (J : Ideal (𝓞 K)) ∣ I ∧ IsPrincipal (I : Ideal (𝓞 K)) ∧
          absNorm (I : Ideal (𝓞 K)) = n} := by
  refine (Equiv.subtypeSubtypeEquivSubtypeInter
    (fun I : (Ideal (𝓞 K))⁰ ↦
      (J : Ideal (𝓞 K)) ∣ I ∧ IsPrincipal (I : Ideal (𝓞 K)))
    (fun I ↦ absNorm (I : Ideal (𝓞 K)) = n)).trans ?_
  exact Equiv.subtypeEquivRight fun _ ↦ by
    grind

private noncomputable instance finite_principalIdealAboveNormFiber
    (J : (Ideal (𝓞 K))⁰) (n : ℕ) :
    Finite {I : PrincipalIdealAbove K J //
      absNorm I.1.1 = n} := by
  letI : Fintype {I : Ideal (𝓞 K) // absNorm I = n} :=
    (Ideal.finite_setOf_absNorm_eq n).fintype
  let f :
      {I : (Ideal (𝓞 K))⁰ //
        (J : Ideal (𝓞 K)) ∣ I ∧ IsPrincipal (I : Ideal (𝓞 K)) ∧
          absNorm (I : Ideal (𝓞 K)) = n} →
        {I : Ideal (𝓞 K) // absNorm I = n} :=
    fun I ↦ ⟨I.1.1, I.2.2.2⟩
  have hf : Function.Injective f := fun I I' h ↦ by
    grind
  letI : Finite
      {I : (Ideal (𝓞 K))⁰ //
        (J : Ideal (𝓞 K)) ∣ I ∧ IsPrincipal (I : Ideal (𝓞 K)) ∧
          absNorm (I : Ideal (𝓞 K)) = n} :=
    Finite.of_injective f hf
  exact Finite.of_equiv _
    (principalIdealAboveNormFiberEquiv K J n).symm

open Classical in
private theorem summable_inverseNormPower_principalIdealAbove
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    Summable
      (fun I : PrincipalIdealAbove K J ↦
        ((absNorm I.1.1 : ℂ) ^ (-s))) := by
  let f : PrincipalIdealAbove K J → Ideal (𝓞 K) := fun I ↦ I.1.1
  have hf : Function.Injective f := fun I I' h ↦ by
    grind
  have hsum := (summable_idealInverseNormPower K hs).comp_injective hf
  apply hsum.congr
  intro I
  change idealInverseNormPower K s (f I) =
    ((absNorm I.1.1 : ℂ) ^ (-s))
  rw [idealInverseNormPower_of_ne_zero K s]
  change I.1.1 ≠ 0
  exact mem_nonZeroDivisors_iff_ne_zero.mp I.1.2

open Classical in
theorem hasSum_principalIdealAbove_inverseNormPower
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    HasSum
      (fun I : PrincipalIdealAbove K J ↦
        ((absNorm I.1.1 : ℂ) ^ (-s)))
      (principalIdealZeta K J s) := by
  let ν : PrincipalIdealAbove K J → ℕ :=
    fun I ↦ absNorm I.1.1
  have hν (I : PrincipalIdealAbove K J) : ν I ≠ 0 :=
    absNorm_ne_zero_of_nonZeroDivisors I.1
  have h := hasSum_inversePower_eq_lSeries_fiberCard ν hν
    (summable_inverseNormPower_principalIdealAbove K J hs)
  have hcoeff :
      (fun n ↦
        (Nat.card {I : PrincipalIdealAbove K J // ν I = n} : ℂ)) =
        (fun n ↦ (principalIdealNormCount K J n : ℂ)) := by
    funext n
    norm_cast
    exact Nat.card_congr (principalIdealAboveNormFiberEquiv K J n)
  rw [hcoeff] at h
  exact h

open Classical in
theorem principalIdealZeta_eq_inverseNormPower_mul_partialDedekindZeta
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    principalIdealZeta K J s =
      ((absNorm (J : Ideal (𝓞 K)) : ℂ) ^ (-s)) *
        partialDedekindZeta K (ClassGroup.mk0 J)⁻¹ s := by
  let e := inverseIdealClassEquivPrincipalIdealAbove K J
  have hclass := hasSum_inverseIdealClass_inverseNormPower K
    (ClassGroup.mk0 J)⁻¹ hs
  have hscaled :
      HasSum
        (fun I : InverseIdealClass K J ↦
          ((absNorm (J : Ideal (𝓞 K)) : ℂ) ^ (-s)) *
            ((absNorm I.1.1 : ℂ) ^ (-s)))
        (((absNorm (J : Ideal (𝓞 K)) : ℂ) ^ (-s)) *
          partialDedekindZeta K (ClassGroup.mk0 J)⁻¹ s) :=
    hclass.mul_left ((absNorm (J : Ideal (𝓞 K)) : ℂ) ^ (-s))
  have habove :
      HasSum
        (fun I : PrincipalIdealAbove K J ↦
          ((absNorm I.1.1 : ℂ) ^ (-s)))
        (((absNorm (J : Ideal (𝓞 K)) : ℂ) ^ (-s)) *
          partialDedekindZeta K (ClassGroup.mk0 J)⁻¹ s) := by
    apply e.hasSum_iff.mp
    change HasSum
      (fun I : InverseIdealClass K J ↦
        ((absNorm (e I).1.1 : ℂ) ^ (-s)))
      (((absNorm (J : Ideal (𝓞 K)) : ℂ) ^ (-s)) *
        partialDedekindZeta K (ClassGroup.mk0 J)⁻¹ s)
    have hfun :
        (fun I : InverseIdealClass K J ↦
          ((absNorm (e I).1.1 : ℂ) ^ (-s))) =
        (fun I : InverseIdealClass K J ↦
          ((absNorm (J : Ideal (𝓞 K)) : ℂ) ^ (-s)) *
            ((absNorm I.1.1 : ℂ) ^ (-s))) := by
      funext I
      rw [show e I = inverseIdealClassEquivPrincipalIdealAbove K J I from rfl,
        absNorm_inverseIdealClassEquivPrincipalIdealAbove]
      rw [Nat.cast_mul]
      exact Complex.mul_cpow_ofReal_nonneg
        (Nat.cast_nonneg _) (Nat.cast_nonneg _) (-s)
    simp_all
  exact (hasSum_principalIdealAbove_inverseNormPower K J hs).unique habove

end NumberField.Odlyzko
