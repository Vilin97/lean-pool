/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.DedekindZeta.IdealPrimeCode
public import LeanPool.Odlyzko.DedekindZeta.IdealPrimeWeights
public import LeanPool.Odlyzko.DedekindZeta.PrimeValueHom

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Ideal IsDedekindDomain

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

/-- A prime ideal at code used in the Odlyzko-bound argument. -/
noncomputable def primeIdealAtCode (p : ℕ) :
    Option (HeightOneSpectrum (𝓞 K)) := by
  classical
  exact if h : ∃ P, primeIdealCode K P = p then some (Classical.choose h) else none

lemma primeIdealAtCode_eq_some_iff {p : ℕ} {P : HeightOneSpectrum (𝓞 K)} :
    primeIdealAtCode K p = some P ↔ primeIdealCode K P = p := by
  classical
  constructor
  · intro h
    unfold primeIdealAtCode at h
    split at h
    · grind
    · simp at h
  · intro h
    unfold primeIdealAtCode
    rw [dif_pos ⟨P, h⟩]
    congr
    exact primeIdealCode_injective K
      ((Classical.choose_spec (show ∃ Q, primeIdealCode K Q = p from ⟨P, h⟩)).trans h.symm)

@[simp] lemma primeIdealAtCode_primeIdealCode
    (P : HeightOneSpectrum (𝓞 K)) :
    primeIdealAtCode K (primeIdealCode K P) = some P :=
  primeIdealAtCode_eq_some_iff K |>.2 rfl

/-- An encoded prime ideal weight used in the Odlyzko-bound argument. -/
noncomputable def encodedPrimeIdealWeight (s : ℂ) (p : ℕ) : ℂ :=
  (primeIdealAtCode K p).elim 0 fun P ↦
    inverseNormPower (primeIdealNorm K P) s

@[simp] lemma encodedPrimeIdealWeight_primeIdealCode
    (s : ℂ) (P : HeightOneSpectrum (𝓞 K)) :
    encodedPrimeIdealWeight K s (primeIdealCode K P) =
      inverseNormPower (primeIdealNorm K P) s := by
  simp [encodedPrimeIdealWeight]

private lemma inverseNormPower_primeIdeal_ne_zero
    (s : ℂ) (P : HeightOneSpectrum (𝓞 K)) :
    inverseNormPower (primeIdealNorm K P) s ≠ 0 := by
  rw [inverseNormPower, Complex.cpow_ne_zero_iff]
  left
  exact_mod_cast (Nat.zero_lt_of_lt (one_lt_primeIdealNorm K P)).ne'

lemma encodedPrimeIdealWeight_ne_zero_iff (s : ℂ) (p : ℕ) :
    encodedPrimeIdealWeight K s p ≠ 0 ↔
      ∃ P, primeIdealCode K P = p := by
  constructor
  · intro hw
    cases h : primeIdealAtCode K p with
    | none => simp [encodedPrimeIdealWeight, h] at hw
    | some P => exact ⟨P, (primeIdealAtCode_eq_some_iff K).1 h⟩
  · rintro ⟨P, hP⟩
    rw [encodedPrimeIdealWeight,
      (primeIdealAtCode_eq_some_iff K).2 hP]
    exact inverseNormPower_primeIdeal_ne_zero K s P

/-- An encoded ideal summand used in the Odlyzko-bound argument. -/
noncomputable def encodedIdealSummand (s : ℂ) : ℕ →*₀ ℂ :=
  primeValueHom (encodedPrimeIdealWeight K s)

lemma encodedIdealSummand_idealPrimeCode
    (s : ℂ) (I : NonzeroIdeal K) :
    encodedIdealSummand K s (idealPrimeCode K I) =
      ((absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-s)) := by
  rw [encodedIdealSummand, idealPrimeCode,
    primeValueHom_multiset_prod_of_prime
      (encodedPrimeIdealWeight K s)
      (prime_mem_idealPrimeCode_factors K I)]
  rw [inverseNormPower_nonzeroIdealEquivPrimeFactors]
  change
    (((idealPrimeFactors K I).map (primeIdealCode K)).map
      (encodedPrimeIdealWeight K s)).prod =
      ((idealPrimeFactors K I).map
        (fun P ↦ inverseNormPower (primeIdealNorm K P) s)).prod
  simp

lemma exists_idealPrimeCode_eq_of_primeFactors {n : ℕ} (hn : n ≠ 0)
    (hcodes : ∀ p ∈ (n.primeFactorsList : Multiset ℕ),
      ∃ P, primeIdealCode K P = p) :
    ∃ I : NonzeroIdeal K, idealPrimeCode K I = n := by
  classical
  let m : Multiset (HeightOneSpectrum (𝓞 K)) :=
    Multiset.pmap
      (fun p hp ↦ Classical.choose (hcodes p hp))
      (n.primeFactorsList : Multiset ℕ)
      (fun p hp ↦ hp)
  have hmap :
      m.map (primeIdealCode K) = (n.primeFactorsList : Multiset ℕ) := by
    -- At v4.32 `dsimp [m]` normalizes the `Multiset` coercion down to
    -- `List.map`/`List.pmap`, where `Multiset.map_pmap` no longer matches;
    -- unfold the `let` by hand instead.
    change (Multiset.pmap (fun p hp ↦ Classical.choose (hcodes p hp))
        (n.primeFactorsList : Multiset ℕ) (fun p hp ↦ hp)).map (primeIdealCode K) =
      (n.primeFactorsList : Multiset ℕ)
    rw [Multiset.map_pmap]
    calc
      Multiset.pmap
          (fun p hp ↦ primeIdealCode K (Classical.choose (hcodes p hp)))
          (n.primeFactorsList : Multiset ℕ) (fun p hp ↦ hp) =
          Multiset.pmap (fun p (_ : p ∈ (n.primeFactorsList : Multiset ℕ)) ↦ p)
            (n.primeFactorsList : Multiset ℕ) (fun p hp ↦ hp) := by grind
      _ = Multiset.map id (n.primeFactorsList : Multiset ℕ) :=
        Multiset.pmap_eq_map _ _ _ _
      _ = (n.primeFactorsList : Multiset ℕ) := Multiset.map_id _
  refine ⟨idealOfPrimeFactors K m, ?_⟩
  rw [idealPrimeCode, idealPrimeFactors_idealOfPrimeFactors, hmap,
    Multiset.prod_coe, Nat.prod_primeFactorsList hn]

lemma exists_idealPrimeCode_eq_of_encodedIdealSummand_ne_zero
    (s : ℂ) {n : ℕ} (hn : encodedIdealSummand K s n ≠ 0) :
    ∃ I : NonzeroIdeal K, idealPrimeCode K I = n := by
  have hn0 : n ≠ 0 := by grind
  apply exists_idealPrimeCode_eq_of_primeFactors K hn0
  intro p hp
  apply (encodedPrimeIdealWeight_ne_zero_iff K s p).1
  have hpsupp : p ∈ n.factorization.support := by simp_all
  have hprod : n.factorization.prod
      (fun q e ↦ encodedPrimeIdealWeight K s q ^ e) ≠ 0 := by
    simpa [encodedIdealSummand, primeValueHom, hn0] using hn
  have := (Finsupp.prod_ne_zero_iff.mp hprod p hpsupp)
  exact (pow_ne_zero_iff (Finsupp.mem_support_iff.mp hpsupp)).mp this

theorem encodedIdealSummand_ne_zero_iff (s : ℂ) (n : ℕ) :
    encodedIdealSummand K s n ≠ 0 ↔
      ∃ I : NonzeroIdeal K, idealPrimeCode K I = n := by
  constructor
  · exact exists_idealPrimeCode_eq_of_encodedIdealSummand_ne_zero K s
  · rintro ⟨I, rfl⟩
    rw [encodedIdealSummand_idealPrimeCode]
    apply Complex.cpow_ne_zero_iff.mpr
    left
    exact_mod_cast (show absNorm (I : Ideal (𝓞 K)) ≠ 0 by
      simpa [Ideal.absNorm_eq_zero_iff] using I.2)

end NumberField.Odlyzko
