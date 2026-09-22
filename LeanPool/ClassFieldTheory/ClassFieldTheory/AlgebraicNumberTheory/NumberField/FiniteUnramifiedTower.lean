/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.ExtensionIndex
import Mathlib.NumberTheory.RamificationInertia.Unramified
/-!
# Finite-prime unramifiedness in towers of number fields

This file records the tower properties of being unramified at every
finite prime.  The transitivity and intermediate-field arguments are
proved from multiplicativity of ramification indices.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

attribute [local instance] Ideal.Quotient.field

universe u v w

/-- A number-field extension is unramified at finite places when every
height-one prime of the top ring of integers is unramified over the
base ring of integers. -/
def IsUnramifiedAtFinitePlaces
    (K : Type u) (L : Type v)
    [Field K]
    [Field L] [Algebra K L] : Prop :=
  ∀ P : HeightOneSpectrum (𝓞 L),
    Algebra.IsUnramifiedAt (𝓞 K) P.asIdeal

namespace IsUnramifiedAtFinitePlaces

/-- The identity extension is unramified at every finite place. -/
theorem refl
    (K : Type u) [Field K] [NumberField K] :
    IsUnramifiedAtFinitePlaces K K := by
  intro P
  change Algebra.FormallyUnramified (𝓞 K) (Localization P.asIdeal.primeCompl)
  infer_instance

variable
    {k : Type u} {K : Type v} {F : Type w}
    [Field k] [NumberField k]
    [Field K] [NumberField K]
    [Field F] [NumberField F]
    [Algebra k K] [Algebra k F] [Algebra K F]
    [IsScalarTower k K F]

/-- Finite-prime unramifiedness is transitive in a tower of number
fields. -/
theorem trans
    (hkK : IsUnramifiedAtFinitePlaces k K)
    (hKF : IsUnramifiedAtFinitePlaces K F) :
    IsUnramifiedAtFinitePlaces k F := by
  intro P
  let p : HeightOneSpectrum (𝓞 K) :=
    finitePlaceBelow (K := K) P
  let hPp : P.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  let : Module.Finite (𝓞 k) (𝓞 K) :=
    HilbertRamification.Dedekind.ringOfIntegers_moduleFinite
      (K := k) (L := K)
  let : Module.Finite (𝓞 K) (𝓞 F) :=
    HilbertRamification.Dedekind.ringOfIntegers_moduleFinite
      (K := K) (L := F)
  let : Module.Finite (𝓞 k) (𝓞 F) :=
    HilbertRamification.Dedekind.ringOfIntegers_moduleFinite
      (K := k) (L := F)
  let hkKp :
      Algebra.IsUnramifiedAt (𝓞 k) p.asIdeal :=
    hkK p
  let hKFP :
      Algebra.IsUnramifiedAt (𝓞 K) P.asIdeal :=
    hKF P
  have hLower :
      p.asIdeal.ramificationIdx (𝓞 k) = 1 :=
    Ideal.ramificationIdx_eq_one p.asIdeal (𝓞 k)
  have hUpper :
      P.asIdeal.ramificationIdx (𝓞 K) = 1 :=
    Ideal.ramificationIdx_eq_one P.asIdeal (𝓞 K)
  have hTower :
      P.asIdeal.ramificationIdx (𝓞 k) =
        p.asIdeal.ramificationIdx (𝓞 k) *
          P.asIdeal.ramificationIdx (𝓞 K) :=
    Ideal.ramificationIdx_tower
      (R := 𝓞 k) p.asIdeal P.asIdeal
  have hTop :
      P.asIdeal.ramificationIdx (𝓞 k) = 1 := by
    rw [hTower, hLower, hUpper, one_mul]
  have hBasePrime :
      P.asIdeal.under (𝓞 k) ≠ ⊥ := by
    simpa only [finitePlaceBelow_asIdeal] using
      (finitePlaceBelow (K := k) P).ne_bot
  let : Finite ((𝓞 k) ⧸ P.asIdeal.under (𝓞 k)) :=
    Ring.HasFiniteQuotients.finiteQuotient hBasePrime
  let :
      PerfectField (P.asIdeal.under (𝓞 k)).ResidueField :=
    PerfectField.ofFinite
  exact
    (Ideal.ramificationIdx_eq_one_iff
      (R := 𝓞 k) (S := 𝓞 F) (q := P.asIdeal)).1 hTop

/-- If the top of a number-field tower is unramified over the bottom,
then it is unramified over the intermediate field. -/
theorem top
    (hkF : IsUnramifiedAtFinitePlaces k F) :
    IsUnramifiedAtFinitePlaces K F := by
  intro P
  let :
      Algebra.IsUnramifiedAt (𝓞 k) P.asIdeal :=
    hkF P
  exact
    Algebra.IsUnramifiedAt.of_restrictScalars
      (𝓞 k) P.asIdeal

/-- If the top of a number-field tower is unramified over the bottom,
then the intermediate field is unramified over the bottom. -/
theorem bot
    (hkF : IsUnramifiedAtFinitePlaces k F) :
    IsUnramifiedAtFinitePlaces k K := by
  intro p
  let : Module.Finite (𝓞 k) (𝓞 K) :=
    HilbertRamification.Dedekind.ringOfIntegers_moduleFinite
      (K := k) (L := K)
  let : Module.Finite (𝓞 K) (𝓞 F) :=
    HilbertRamification.Dedekind.ringOfIntegers_moduleFinite
      (K := K) (L := F)
  let : Module.Finite (𝓞 k) (𝓞 F) :=
    HilbertRamification.Dedekind.ringOfIntegers_moduleFinite
      (K := k) (L := F)
  obtain ⟨⟨P, hPprime, hPp⟩⟩ :=
    p.asIdeal.nonempty_primesOver (S := 𝓞 F)
  let : P.IsPrime := hPprime
  let : P.LiesOver p.asIdeal := hPp
  have hPne : P ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot P
  let P' : HeightOneSpectrum (𝓞 F) :=
    { asIdeal := P
      isPrime := hPprime
      ne_bot := hPne }
  let :
      Algebra.IsUnramifiedAt (𝓞 k) P :=
    hkF P'
  have hTop :
      P.ramificationIdx (𝓞 k) = 1 :=
    Ideal.ramificationIdx_eq_one P (𝓞 k)
  have hTower :
      P.ramificationIdx (𝓞 k) =
        p.asIdeal.ramificationIdx (𝓞 k) *
          P.ramificationIdx (𝓞 K) :=
    Ideal.ramificationIdx_tower
      (R := 𝓞 k) p.asIdeal P
  have hLower :
      p.asIdeal.ramificationIdx (𝓞 k) = 1 :=
    (mul_eq_one.mp (hTower.symm.trans hTop)).1
  have hBasePrime :
      p.asIdeal.under (𝓞 k) ≠ ⊥ := by
    simpa only [finitePlaceBelow_asIdeal] using
      (finitePlaceBelow (K := k) p).ne_bot
  let : Finite ((𝓞 k) ⧸ p.asIdeal.under (𝓞 k)) :=
    Ring.HasFiniteQuotients.finiteQuotient hBasePrime
  let :
      PerfectField (p.asIdeal.under (𝓞 k)).ResidueField :=
    PerfectField.ofFinite
  exact
    (Ideal.ramificationIdx_eq_one_iff
      (R := 𝓞 k) (S := 𝓞 K) (q := p.asIdeal)).1 hLower

end IsUnramifiedAtFinitePlaces
