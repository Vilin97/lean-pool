/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.DedekindZeta.Convergence
public import LeanPool.Odlyzko.DedekindZeta.FiniteFiberSeries
public import Mathlib.NumberTheory.LSeries.Linearity
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Ideal IsDedekindDomain NumberField NumberField.Units Submodule
open scoped nonZeroDivisors

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

open mixedEmbedding fundamentalCone

/-- A principal ideal norm count used in the Odlyzko-bound argument. -/
noncomputable def principalIdealNormCount (J : (Ideal (𝓞 K))⁰) (n : ℕ) : ℕ :=
  Nat.card {I : (Ideal (𝓞 K))⁰ //
    (J : Ideal (𝓞 K)) ∣ I ∧ IsPrincipal (I : Ideal (𝓞 K)) ∧
      absNorm (I : Ideal (𝓞 K)) = n}

/-- A fundamental cone norm count used in the Odlyzko-bound argument. -/
noncomputable def fundamentalConeNormCount (J : (Ideal (𝓞 K))⁰) (n : ℕ) : ℕ :=
  Nat.card {a : idealSet K J //
    mixedEmbedding.norm (a : mixedSpace K) = n}

/-- An ideal set int norm used in the Odlyzko-bound argument. -/
noncomputable def idealSetIntNorm (J : (Ideal (𝓞 K))⁰) (a : idealSet K J) : ℕ :=
  intNorm (idealSetEquiv K J a).val

/-- An ideal set int norm fiber equiv used in the Odlyzko-bound argument. -/
noncomputable def idealSetIntNormFiberEquiv
    (J : (Ideal (𝓞 K))⁰) (n : ℕ) :
    {a : idealSet K J // idealSetIntNorm K J a = n} ≃
      {a : idealSet K J //
        mixedEmbedding.norm (a : mixedSpace K) = n} :=
  Equiv.subtypeEquivRight fun a ↦ by
    rw [idealSetIntNorm, ← intNorm_idealSetEquiv_apply]
    exact_mod_cast Iff.rfl

private theorem finite_idealSetIntNorm_fiber
    (J : (Ideal (𝓞 K))⁰) (n : ℕ) :
    Finite {a : idealSet K J // idealSetIntNorm K J a = n} := by
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
    ((idealSetEquivNorm K J n).symm.trans
      (idealSetIntNormFiberEquiv K J n).symm)

theorem fundamentalConeNormCount_eq_natCard_idealSetIntNorm
    (J : (Ideal (𝓞 K))⁰) (n : ℕ) :
    fundamentalConeNormCount K J n =
      Nat.card {a : idealSet K J // idealSetIntNorm K J a = n} := by
  rw [fundamentalConeNormCount]
  exact (Nat.card_congr (idealSetIntNormFiberEquiv K J n)).symm

theorem idealSetIntNorm_ne_zero
    (J : (Ideal (𝓞 K))⁰) (a : idealSet K J) :
    idealSetIntNorm K J a ≠ 0 := by
  have hpos := fundamentalCone.norm_pos_of_mem a.prop.1
  rw [← intNorm_idealSetEquiv_apply, ← idealSetIntNorm] at hpos
  have hnat : 0 < idealSetIntNorm K J a := by simp_all
  grind

theorem fundamentalConeNormCount_eq_torsion_mul
    (J : (Ideal (𝓞 K))⁰) (n : ℕ) :
    fundamentalConeNormCount K J n =
      principalIdealNormCount K J n * torsionOrder K := by
  -- v4.32's `torsionOrder` unfolds to `Fintype.card`; bridge to `Nat.card`
  -- before folding the product.
  rw [fundamentalConeNormCount, principalIdealNormCount, torsionOrder,
    ← Nat.card_eq_fintype_card, ← Nat.card_prod]
  exact Nat.card_congr (idealSetEquivNorm K J n)

theorem principalIdealNormCount_le_idealNormCount
    (J : (Ideal (𝓞 K))⁰) (n : ℕ) :
    principalIdealNormCount K J n ≤ idealNormCount K n := by
  letI : Fintype {I : Ideal (𝓞 K) // absNorm I = n} :=
    (Ideal.finite_setOf_absNorm_eq n).fintype
  rw [principalIdealNormCount, idealNormCount]
  let f :
      {I : (Ideal (𝓞 K))⁰ //
        (J : Ideal (𝓞 K)) ∣ I ∧ IsPrincipal (I : Ideal (𝓞 K)) ∧
          absNorm (I : Ideal (𝓞 K)) = n} →
        {I : Ideal (𝓞 K) // absNorm I = n} :=
    fun I ↦ ⟨I.1.1, I.2.2.2⟩
  exact Nat.card_le_card_of_injective f fun I I' h ↦ by
    grind

/-- A principal ideal zeta used in the Odlyzko-bound argument. -/
noncomputable def principalIdealZeta (J : (Ideal (𝓞 K))⁰) (s : ℂ) : ℂ :=
  LSeries (fun n ↦ (principalIdealNormCount K J n : ℂ)) s

/-- A fundamental cone zeta used in the Odlyzko-bound argument. -/
noncomputable def fundamentalConeZeta (J : (Ideal (𝓞 K))⁰) (s : ℂ) : ℂ :=
  LSeries (fun n ↦ (fundamentalConeNormCount K J n : ℂ)) s

theorem lSeriesSummable_principalIdealNormCount
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (principalIdealNormCount K J n : ℂ)) s := by
  rw [LSeriesSummable]
  refine Summable.of_norm_bounded (lSeriesSummable_idealNormCount K hs).norm ?_
  intro n
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  simp only [LSeries.term_of_ne_zero hn.ne', norm_div,
    Complex.norm_natCast]
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast principalIdealNormCount_le_idealNormCount K J n)
    (norm_nonneg _)

theorem lSeriesSummable_fundamentalConeNormCount
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (fundamentalConeNormCount K J n : ℂ)) s := by
  have hcoeff :
      (fun n ↦ (fundamentalConeNormCount K J n : ℂ)) =
        (torsionOrder K : ℂ) •
          (fun n ↦ (principalIdealNormCount K J n : ℂ)) := by
    funext n
    rw [fundamentalConeNormCount_eq_torsion_mul]
    simp [Pi.smul_apply, Nat.cast_mul, mul_comm]
  rw [hcoeff]
  exact (lSeriesSummable_principalIdealNormCount K J hs).smul _

theorem summable_idealSet_inverseNormPower
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun a : idealSet K J ↦
      ((idealSetIntNorm K J a : ℂ) ^ (-s))) := by
  letI (n : ℕ) :
      Finite {a : idealSet K J // idealSetIntNorm K J a = n} :=
    finite_idealSetIntNorm_fiber K J n
  apply summable_inversePower_of_lSeriesSummable_fiberCard
    (idealSetIntNorm K J) (idealSetIntNorm_ne_zero K J)
  convert lSeriesSummable_fundamentalConeNormCount K J hs using 1
  funext n
  rw [fundamentalConeNormCount_eq_natCard_idealSetIntNorm]

theorem hasSum_idealSet_inverseNormPower
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun a : idealSet K J ↦
      ((idealSetIntNorm K J a : ℂ) ^ (-s)))
      (fundamentalConeZeta K J s) := by
  letI (n : ℕ) :
      Finite {a : idealSet K J // idealSetIntNorm K J a = n} :=
    finite_idealSetIntNorm_fiber K J n
  have h := hasSum_inversePower_eq_lSeries_fiberCard
    (idealSetIntNorm K J) (idealSetIntNorm_ne_zero K J)
    (summable_idealSet_inverseNormPower K J hs)
  simpa only [fundamentalConeZeta,
    ← fundamentalConeNormCount_eq_natCard_idealSetIntNorm] using h

theorem fundamentalConeZeta_eq_torsion_mul_principalIdealZeta
    (J : (Ideal (𝓞 K))⁰) (s : ℂ) :
    fundamentalConeZeta K J s =
      (torsionOrder K : ℂ) * principalIdealZeta K J s := by
  have hcoeff :
      (fun n ↦ (fundamentalConeNormCount K J n : ℂ)) =
        (torsionOrder K : ℂ) •
          (fun n ↦ (principalIdealNormCount K J n : ℂ)) := by
    funext n
    rw [fundamentalConeNormCount_eq_torsion_mul]
    simp [Pi.smul_apply, Nat.cast_mul, mul_comm]
  rw [fundamentalConeZeta, hcoeff, LSeries_smul, principalIdealZeta]

end NumberField.Odlyzko
