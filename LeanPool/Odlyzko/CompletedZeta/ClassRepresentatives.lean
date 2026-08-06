/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.FundamentalConeSeries
public import LeanPool.Odlyzko.DedekindZeta.IdealSeries
public import Mathlib.Data.Fintype.BigOperators

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

section

open Ideal NumberField
open scoped nonZeroDivisors

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

open Classical in
/-- A class ideal norm count used in the Odlyzko-bound argument. -/
noncomputable def classIdealNormCount (C : ClassGroup (𝓞 K)) (n : ℕ) : ℕ :=
  Nat.card {I : (Ideal (𝓞 K))⁰ //
    ClassGroup.mk0 I = C ∧ absNorm (I : Ideal (𝓞 K)) = n}

open Classical in
/-- A partial dedekind zeta used in the Odlyzko-bound argument. -/
noncomputable def partialDedekindZeta (C : ClassGroup (𝓞 K)) (s : ℂ) : ℂ :=
  LSeries (fun n ↦ (classIdealNormCount K C n : ℂ)) s

private noncomputable def idealNormFiberEquivNonzero
    {n : ℕ} (hn : n ≠ 0) :
    {I : Ideal (𝓞 K) // absNorm I = n} ≃
      {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) = n} where
  toFun I :=
    ⟨⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr fun hI ↦
      hn <| I.2.symm.trans (Ideal.absNorm_eq_zero_iff.mpr hI)⟩, I.2⟩
  invFun I := ⟨I.1.1, I.2⟩
  left_inv I := by simp
  right_inv I := by
    simp

open Classical in
theorem sum_classIdealNormCount {n : ℕ} (hn : n ≠ 0) :
    ∑ C : ClassGroup (𝓞 K), classIdealNormCount K C n =
      idealNormCount K n := by
  let : Fintype {I : Ideal (𝓞 K) // absNorm I = n} :=
    (Ideal.finite_setOfPred_absNorm_eq n).fintype
  let : Fintype {I : (Ideal (𝓞 K))⁰ //
      absNorm (I : Ideal (𝓞 K)) = n} :=
    Fintype.ofEquiv _ (idealNormFiberEquivNonzero K hn)
  let e := fun C : ClassGroup (𝓞 K) ↦
    (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun I : (Ideal (𝓞 K))⁰ ↦ absNorm (I : Ideal (𝓞 K)) = n)
      (fun I ↦ ClassGroup.mk0 I = C)).trans
      (Equiv.subtypeEquivRight fun _ ↦ and_comm)
  calc
    _ = ∑ C : ClassGroup (𝓞 K),
        Nat.card {I : {I : (Ideal (𝓞 K))⁰ //
          absNorm (I : Ideal (𝓞 K)) = n} //
            ClassGroup.mk0 I.1 = C} := by
      apply Finset.sum_congr rfl
      intro C _
      exact (Nat.card_congr (e C)).symm
    _ = Nat.card
        (Σ C : ClassGroup (𝓞 K),
          {I : {I : (Ideal (𝓞 K))⁰ //
            absNorm (I : Ideal (𝓞 K)) = n} //
              ClassGroup.mk0 I.1 = C}) := Nat.card_sigma.symm
    _ = Nat.card {I : (Ideal (𝓞 K))⁰ //
        absNorm (I : Ideal (𝓞 K)) = n} :=
      Nat.card_congr
        (Equiv.sigmaFiberEquiv
          (fun I : {I : (Ideal (𝓞 K))⁰ //
            absNorm (I : Ideal (𝓞 K)) = n} ↦ ClassGroup.mk0 I.1))
    _ = idealNormCount K n := by
      rw [idealNormCount]
      exact Nat.card_congr (idealNormFiberEquivNonzero K hn).symm

open Classical in
theorem classIdealNormCount_le_idealNormCount
    (C : ClassGroup (𝓞 K)) (n : ℕ) :
    classIdealNormCount K C n ≤ idealNormCount K n := by
  let : Fintype {I : Ideal (𝓞 K) // absNorm I = n} :=
    (Ideal.finite_setOfPred_absNorm_eq n).fintype
  rw [classIdealNormCount, idealNormCount]
  let f :
      {I : (Ideal (𝓞 K))⁰ //
        ClassGroup.mk0 I = C ∧ absNorm (I : Ideal (𝓞 K)) = n} →
        {I : Ideal (𝓞 K) // absNorm I = n} :=
    fun I ↦ ⟨I.1.1, I.2.2⟩
  exact Nat.card_le_card_of_injective f fun I I' h ↦ by
    grind

open Classical in
theorem lSeriesSummable_classIdealNormCount
    (C : ClassGroup (𝓞 K)) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (classIdealNormCount K C n : ℂ)) s := by
  rw [LSeriesSummable]
  refine Summable.of_norm_bounded (lSeriesSummable_idealNormCount K hs).norm ?_
  intro n
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  simp only [LSeries.term_of_ne_zero hn.ne', norm_div,
    Complex.norm_natCast]
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast classIdealNormCount_le_idealNormCount K C n)
    (norm_nonneg _)

open Classical in
private def classIdealNormFiberEquiv
    (C : ClassGroup (𝓞 K)) (n : ℕ) :
    {I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C} //
      absNorm (I.1 : Ideal (𝓞 K)) = n} ≃
      {I : (Ideal (𝓞 K))⁰ //
        ClassGroup.mk0 I = C ∧ absNorm (I : Ideal (𝓞 K)) = n} :=
  Equiv.subtypeSubtypeEquivSubtypeInter
    (fun I : (Ideal (𝓞 K))⁰ ↦ ClassGroup.mk0 I = C)
    (fun I ↦ absNorm (I : Ideal (𝓞 K)) = n)

private noncomputable instance finite_classIdealNormFiber
    (C : ClassGroup (𝓞 K)) (n : ℕ) :
    Finite
      {I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C} //
        absNorm (I.1 : Ideal (𝓞 K)) = n} := by
  let : Fintype {I : Ideal (𝓞 K) // absNorm I = n} :=
    (Ideal.finite_setOfPred_absNorm_eq n).fintype
  let f :
      {I : (Ideal (𝓞 K))⁰ //
        ClassGroup.mk0 I = C ∧ absNorm (I : Ideal (𝓞 K)) = n} →
        {I : Ideal (𝓞 K) // absNorm I = n} :=
    fun I ↦ ⟨I.1.1, I.2.2⟩
  have hf : Function.Injective f := fun I I' h ↦ by
    grind
  let : Finite
      {I : (Ideal (𝓞 K))⁰ //
        ClassGroup.mk0 I = C ∧ absNorm (I : Ideal (𝓞 K)) = n} :=
    Finite.of_injective f hf
  exact Finite.of_equiv _
    (classIdealNormFiberEquiv K C n).symm

open Classical in
private theorem summable_inverseNormPower_inverseIdealClass
    (C : ClassGroup (𝓞 K)) {s : ℂ} (hs : 1 < s.re) :
    Summable
      (fun I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C} ↦
        ((absNorm (I.1 : Ideal (𝓞 K)) : ℂ) ^ (-s))) :=
  by
    let f :
        {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C} →
          Ideal (𝓞 K) :=
      fun I ↦ I.1.1
    have hf : Function.Injective f := fun I I' h ↦ by
      grind
    have hsum :=
      (summable_idealInverseNormPower K hs).comp_injective hf
    apply hsum.congr
    intro I
    change idealInverseNormPower K s (f I) =
      ((absNorm (I.1 : Ideal (𝓞 K)) : ℂ) ^ (-s))
    rw [idealInverseNormPower_of_ne_zero K s]
    change (I.1 : Ideal (𝓞 K)) ≠ 0
    exact mem_nonZeroDivisors_iff_ne_zero.mp I.1.2

open Classical in
theorem hasSum_inverseIdealClass_inverseNormPower
    (C : ClassGroup (𝓞 K)) {s : ℂ} (hs : 1 < s.re) :
    HasSum
      (fun I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C} ↦
        ((absNorm (I.1 : Ideal (𝓞 K)) : ℂ) ^ (-s)))
      (partialDedekindZeta K C s) := by
  let ν :
      {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C} → ℕ :=
    fun I ↦ absNorm (I.1 : Ideal (𝓞 K))
  have hν (I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C}) :
      ν I ≠ 0 :=
    absNorm_ne_zero_of_nonZeroDivisors I.1
  have h := hasSum_inversePower_eq_lSeries_fiberCard ν hν
    (summable_inverseNormPower_inverseIdealClass K C hs)
  have hcoeff :
      (fun n ↦
        (Nat.card
          {I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C} //
            ν I = n} : ℂ)) =
        (fun n ↦ (classIdealNormCount K C n : ℂ)) := by
    funext n
    norm_cast
    exact Nat.card_congr (classIdealNormFiberEquiv K C n)
  rw [hcoeff] at h
  exact h

open Classical in
theorem sum_partialDedekindZeta {s : ℂ} (hs : 1 < s.re) :
    ∑ C : ClassGroup (𝓞 K), partialDedekindZeta K C s =
      NumberField.dedekindZeta K s := by
  simp_rw [partialDedekindZeta]
  rw [dedekindZeta_eq_LSeries_idealNormCount]
  rw [← LSeries_sum (fun C _ ↦ lSeriesSummable_classIdealNormCount K C hs)]
  apply LSeries_congr
  intro n hn
  simp only [Finset.sum_apply]
  exact_mod_cast sum_classIdealNormCount K hn

end NumberField.Odlyzko

end

section

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
  let : Fintype {I : Ideal (𝓞 K) // absNorm I = n} :=
    (Ideal.finite_setOfPred_absNorm_eq n).fintype
  let f :
      {I : (Ideal (𝓞 K))⁰ //
        (J : Ideal (𝓞 K)) ∣ I ∧ IsPrincipal (I : Ideal (𝓞 K)) ∧
          absNorm (I : Ideal (𝓞 K)) = n} →
        {I : Ideal (𝓞 K) // absNorm I = n} :=
    fun I ↦ ⟨I.1.1, I.2.2.2⟩
  have hf : Function.Injective f := fun I I' h ↦ by
    grind
  let : Finite
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

end

section

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

end
