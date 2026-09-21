/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import Mathlib.RingTheory.FiniteLength
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Support

/-!
# Finite length at a minimal prime of a finite module

This file isolates the commutative-algebra localization statement used later:
if `P` is minimal over the annihilator of a finite module, then localization at
`P` is nonzero and has finite length.
-/

namespace AlgebraicAnalysis.MinimalPrimeFiniteLengthLocalization

noncomputable section

open scoped Pointwise

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

/-- A finite module over a Noetherian local ring has finite length as soon as
a power of the maximal ideal annihilates it. -/
theorem finiteLength_of_maximalIdeal_pow_smul_eq_bot
    [IsLocalRing A] [IsNoetherianRing A] [Module.Finite A M]
    {n : ℕ}
    (hpow : (IsLocalRing.maximalIdeal A ^ n) • (⊤ : Submodule A M) = ⊥) :
    IsFiniteLength A M := by
  induction n generalizing M with
  | zero =>
      have htop : (⊤ : Submodule A M) = ⊥ := by simpa using hpow
      have : Subsingleton M :=
        ⟨fun x y ↦ by
          have hx : x = 0 := by
            have : x ∈ (⊥ : Submodule A M) := by rw [← htop]; trivial
            simpa using this
          have hy : y = 0 := by
            have : y ∈ (⊥ : Submodule A M) := by rw [← htop]; trivial
            simpa using this
          exact hx.trans hy.symm⟩
      exact .of_subsingleton
  | succ n ih =>
      let m : Ideal A := IsLocalRing.maximalIdeal A
      let N : Submodule A M := m • (⊤ : Submodule A M)
      have hNpow : (m ^ n) • (⊤ : Submodule A N) = ⊥ := by
        rw [Submodule.eq_bot_iff]
        intro x hx
        apply Subtype.ext
        change (x : M) = 0
        have hx' : (x : M) ∈ (m ^ n) • N :=
          (Submodule.mem_smul_top_iff (I := m ^ n) N x).mp hx
        have hxbot : (x : M) ∈ (⊥ : Submodule A M) := by
          rw [← hpow, show IsLocalRing.maximalIdeal A = m from rfl,
            pow_succ, mul_smul]
          exact hx'
        simpa using hxbot
      have hNfinite : IsFiniteLength A N := ih hNpow
      let hQtor : Module.IsTorsionBySet A (M ⧸ N) m := by
        simpa only [N] using Module.isTorsionBySet_quotient_ideal_smul M m
      let : m.IsMaximal := by dsimp [m]; infer_instance
      let : Module (A ⧸ m) (M ⧸ N) := hQtor.module
      let : IsScalarTower A (A ⧸ m) (M ⧸ N) := hQtor.isScalarTower
      let : Field (A ⧸ m) := Ideal.Quotient.field m
      have : Module.Finite A (M ⧸ N) := Module.Finite.quotient A N
      have : Module.Finite (A ⧸ m) (M ⧸ N) :=
        Module.Finite.of_restrictScalars_finite A (A ⧸ m) (M ⧸ N)
      have hQartinianQuot : IsArtinian (A ⧸ m) (M ⧸ N) := inferInstance
      have hQartinian : IsArtinian A (M ⧸ N) := by
        let e : Submodule (A ⧸ m) (M ⧸ N) ≃o Submodule A (M ⧸ N) :=
          { Submodule.restrictScalarsEmbedding A (A ⧸ m) (M ⧸ N) with
            invFun := fun p ↦
              { carrier := p
                add_mem' := p.add_mem
                zero_mem' := p.zero_mem
                smul_mem' := by
                  rintro ⟨a⟩ x hx
                  exact p.smul_mem a hx }
            left_inv := by intro p; ext; rfl
            right_inv := by intro p; ext; rfl }
        exact ⟨e.symm.toOrderEmbedding.wellFounded hQartinianQuot.wf⟩
      rw [isFiniteLength_iff_isNoetherian_isArtinian]
      exact ⟨inferInstance,
        (isArtinian_iff_submodule_quotient N).mpr
          ⟨(isFiniteLength_iff_isNoetherian_isArtinian.mp hNfinite).2, hQartinian⟩⟩

variable {R G : Type*} [CommRing R]
  [AddCommGroup G] [Module R G]

/-- Localization preserves finite generation for the canonical localized
module. -/
theorem localizedModule_finite [Module.Finite R G]
    (P : Ideal R) [P.IsPrime] :
    Module.Finite (Localization P.primeCompl)
      (LocalizedModule P.primeCompl G) := by
  exact Module.Finite.of_isLocalizedModule P.primeCompl
    (LocalizedModule.mkLinearMap P.primeCompl G)

/-- A minimal prime over the annihilator belongs to the support, so the
corresponding localization is nonzero. -/
theorem localizedModule_nontrivial
    [Module.Finite R G] (P : Ideal R) [P.IsPrime]
    (hP : P ∈ (Module.annihilator R G).minimalPrimes) :
    Nontrivial (LocalizedModule P.primeCompl G) := by
  let p : PrimeSpectrum R := ⟨P, inferInstance⟩
  have hp : p ∈ Module.support R G :=
    Module.mem_support_iff_of_finite.mpr hP.1.2
  simpa [p] using (Module.mem_support_iff.mp hp)

/-- At a minimal prime over the module annihilator, the localized maximal
ideal lies in the radical of the mapped annihilator. -/
theorem maximalIdeal_le_radical_map_annihilator
    (P : Ideal R) [P.IsPrime]
    (hP : P ∈ (Module.annihilator R G).minimalPrimes) :
    IsLocalRing.maximalIdeal (Localization P.primeCompl) ≤
      (Ideal.map (algebraMap R (Localization P.primeCompl))
        (Module.annihilator R G)).radical := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  rw [Ideal.radical_eq_sInf, le_sInf_iff]
  rintro q ⟨hmap, hqprime⟩
  obtain ⟨hcomapPrime, hcomapLe⟩ :=
    ((IsLocalization.AtPrime.orderIsoOfPrime
      (Localization P.primeCompl) P) ⟨q, hqprime⟩).2
  rw [Ideal.map_le_iff_le_comap] at hmap ⊢
  exact hP.2 ⟨hcomapPrime, hmap⟩ hcomapLe

/-- Mapping the original annihilator into the localization gives elements
that annihilate every localized fraction. -/
theorem map_annihilator_le_localized_annihilator
    (P : Ideal R) [P.IsPrime] :
    Ideal.map (algebraMap R (Localization P.primeCompl))
        (Module.annihilator R G) ≤
      Module.annihilator (Localization P.primeCompl)
        (LocalizedModule P.primeCompl G) := by
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  rw [Ideal.mem_comap, Module.mem_annihilator]
  intro z
  induction z using LocalizedModule.induction_on with
  | _ g s =>
      change Localization.mk r (1 : P.primeCompl) •
        LocalizedModule.mk g s = 0
      rw [LocalizedModule.mk_smul_mk]
      have hrg : r • g = 0 := Module.mem_annihilator.mp hr g
      rw [hrg, LocalizedModule.zero_mk]

/-- A power of the localized maximal ideal annihilates the localized finite
module. -/
theorem exists_maximalIdeal_pow_le_localized_annihilator
    [IsNoetherianRing R] [Module.Finite R G]
    (P : Ideal R) [P.IsPrime]
    (hP : P ∈ (Module.annihilator R G).minimalPrimes) :
    ∃ n : ℕ, IsLocalRing.maximalIdeal (Localization P.primeCompl) ^ n ≤
      Module.annihilator (Localization P.primeCompl)
        (LocalizedModule P.primeCompl G) := by
  let A := Localization P.primeCompl
  have : IsNoetherianRing A :=
    IsLocalization.isNoetherianRing P.primeCompl A inferInstance
  have hrad : IsLocalRing.maximalIdeal A ≤
      (Module.annihilator A (LocalizedModule P.primeCompl G)).radical :=
    (maximalIdeal_le_radical_map_annihilator P hP).trans
      (Ideal.radical_mono (map_annihilator_le_localized_annihilator P))
  exact Ideal.exists_pow_le_of_le_radical_of_fg hrad
    (Module.Finite.iff_fg.mp (inferInstance :
      Module.Finite A (IsLocalRing.maximalIdeal A)))

/-- The localized module at a minimal prime over its annihilator has finite
length over the local ring. -/
theorem localizedModule_isFiniteLength
    [IsNoetherianRing R] [Module.Finite R G]
    (P : Ideal R) [P.IsPrime]
    (hP : P ∈ (Module.annihilator R G).minimalPrimes) :
    IsFiniteLength (Localization P.primeCompl)
      (LocalizedModule P.primeCompl G) := by
  let A := Localization P.primeCompl
  have : IsNoetherianRing A :=
    IsLocalization.isNoetherianRing P.primeCompl A inferInstance
  have : Module.Finite A (LocalizedModule P.primeCompl G) :=
    localizedModule_finite P
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_le_localized_annihilator P hP
  have hann : Module.annihilator A (LocalizedModule P.primeCompl G) •
      (⊤ : Submodule A (LocalizedModule P.primeCompl G)) = ⊥ := by
    rw [← Submodule.annihilator_top]
    exact Submodule.annihilator_smul
      (⊤ : Submodule A (LocalizedModule P.primeCompl G))
  apply finiteLength_of_maximalIdeal_pow_smul_eq_bot (n := n)
  apply le_antisymm
  · calc
      IsLocalRing.maximalIdeal A ^ n •
          (⊤ : Submodule A (LocalizedModule P.primeCompl G))
          ≤ Module.annihilator A (LocalizedModule P.primeCompl G) •
              (⊤ : Submodule A (LocalizedModule P.primeCompl G)) :=
            Submodule.smul_mono hn le_rfl
      _ = ⊥ := hann
  · exact bot_le

/-- The load-bearing package: localization at a minimal prime over the
annihilator is simultaneously nonzero and of finite length. -/
theorem localizedModule_nontrivial_and_isFiniteLength
    [IsNoetherianRing R] [Module.Finite R G]
    (P : Ideal R) [P.IsPrime]
    (hP : P ∈ (Module.annihilator R G).minimalPrimes) :
    Nontrivial (LocalizedModule P.primeCompl G) ∧
      IsFiniteLength (Localization P.primeCompl)
        (LocalizedModule P.primeCompl G) :=
  ⟨localizedModule_nontrivial P hP, localizedModule_isFiniteLength P hP⟩


end

end AlgebraicAnalysis.MinimalPrimeFiniteLengthLocalization
