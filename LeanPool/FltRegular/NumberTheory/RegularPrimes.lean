/-
Copyright (c) 2026 FltRegular contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FltRegular contributors
-/

module

public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID

/-!
# Regular primes

## Main definitions

* `IsRegularNumber`: a natural number `n` is regular if `n` is coprime with the cardinal of the
  class group.

-/

@[expose] public section

noncomputable section

open Nat Polynomial NumberField

open scoped NumberField

variable (n p : ℕ)

/-- A natural number `n` is regular if `n` is coprime with the cardinal of the class group. -/
def IsRegularNumber : Prop :=
  n.Coprime <| Fintype.card <| ClassGroup (𝓞 <| CyclotomicField n ℚ)

/-- The definition of regular primes. -/
def IsRegularPrime : Prop :=
  IsRegularNumber p

section TwoRegular

variable (K : Type*) [Field K]

variable (L : Type*) [Field L] [Algebra K L]

/-- The second cyclotomic field is equivalent to the base field. -/
def cyclotomicFieldTwoEquiv [IsCyclotomicExtension {2} K L] : L ≃ₐ[K] K := by
  suffices IsSplittingField K K (cyclotomic 2 K) by
    have : IsSplittingField K L (cyclotomic 2 K) :=
      IsCyclotomicExtension.splitting_field_cyclotomic 2 K L
    exact (IsSplittingField.algEquiv L (cyclotomic 2 K)).trans
      (IsSplittingField.algEquiv K <| cyclotomic 2 K).symm
  exact ⟨by simpa using Splits.X_sub_C (-1 : K),
    by simp [eq_iff_true_of_subsingleton]⟩

instance IsPrincipalIdealRing_of_IsCyclotomicExtension_two
    (L : Type*) [Field L] [CharZero L] [IsCyclotomicExtension {2} ℚ L] :
    IsPrincipalIdealRing (𝓞 L) :=
  let F : 𝓞 L ≃+* ℤ := (RingOfIntegers.mapRingEquiv
    (cyclotomicFieldTwoEquiv ℚ L).toRingEquiv).trans Rat.ringOfIntegersEquiv
  IsPrincipalIdealRing.of_surjective F.symm.toRingHom F.symm.surjective

instance : IsCyclotomicExtension {2} ℚ (CyclotomicField 2 ℚ) :=
  CyclotomicField.isCyclotomicExtension 2 ℚ

instance : IsPrincipalIdealRing (𝓞 (CyclotomicField 2 ℚ)) :=
  IsPrincipalIdealRing_of_IsCyclotomicExtension_two _

theorem isRegularPrime_two : IsRegularPrime 2 := by
  rw [IsRegularPrime, IsRegularNumber]
  convert coprime_one_right _
  exact (card_classGroup_eq_one_iff (R := 𝓞 (CyclotomicField 2 ℚ))).2 inferInstance

theorem isRegularPrime_three :
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    IsRegularPrime 3 := by
  let _ : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  rw [IsRegularPrime, IsRegularNumber]
  convert coprime_one_right _
  exact classNumber_eq_one_iff.2
    (IsCyclotomicExtension.Rat.three_pid (CyclotomicField _ ℚ))

end TwoRegular
