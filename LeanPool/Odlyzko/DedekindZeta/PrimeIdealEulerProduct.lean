/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.DedekindZeta.EncodedIdealSummability
public import LeanPool.Odlyzko.DedekindZeta.IdealSeries

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Ideal IsDedekindDomain

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

lemma encodedIdealSummand_eq_extendByZero (s : ℂ) :
    (encodedIdealSummand K s : ℕ → ℂ) =
      extendByZero (idealPrimeCode K)
        (fun I : NonzeroIdeal K ↦
          ((absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-s))) := by
  funext n
  by_cases hn : encodedIdealSummand K s n = 0
  · rw [hn]
    symm
    apply extendByZero_eq_zero_of_not_mem_range
      (idealPrimeCode K) _
    intro hrange
    obtain ⟨I, hI⟩ := hrange
    exact ((encodedIdealSummand_ne_zero_iff K s n).2 ⟨I, hI⟩) hn
  · obtain ⟨I, hI⟩ :=
      (encodedIdealSummand_ne_zero_iff K s n).1 hn
    subst n
    rw [extendByZero_apply (idealPrimeCode K)
      (idealPrimeCode_injective K),
      encodedIdealSummand_idealPrimeCode]

theorem hasSum_encodedIdealSummand {s : ℂ} (hs : 1 < s.re) :
    HasSum (encodedIdealSummand K s) (NumberField.dedekindZeta K s) := by
  rw [encodedIdealSummand_eq_extendByZero]
  exact hasSum_extendByZero
    (idealPrimeCode K) (idealPrimeCode_injective K)
    (hasSum_nonzeroIdeal_inverseNormPower K hs)

/-- An encoded ideal factor used in the Odlyzko-bound argument. -/
noncomputable def encodedIdealFactor (s : ℂ) (p : Nat.Primes) : ℂ :=
  (1 - encodedIdealSummand K s p)⁻¹

lemma encodedIdealFactor_primeIdealCode (s : ℂ)
    (P : HeightOneSpectrum (𝓞 K)) :
    encodedIdealFactor K s (primeIdealCodeEmbedding K P) =
      primeIdealFactor K P s := by
  rw [encodedIdealFactor, encodedIdealSummand,
    show ((primeIdealCodeEmbedding K P : Nat.Primes) : ℕ) =
      primeIdealCode K P by rfl]
  rw [primeValueHom_apply_of_prime _
      (prime_primeIdealCode K P),
    encodedPrimeIdealWeight_primeIdealCode]
  rfl

lemma encodedIdealFactor_eq_one_of_not_mem_range (s : ℂ)
    (p : Nat.Primes)
    (hp : p ∉ Set.range (primeIdealCodeEmbedding K)) :
    encodedIdealFactor K s p = 1 := by
  have hnone : primeIdealAtCode K p = none := by
    cases h : primeIdealAtCode K p with
    | none => simp
    | some P =>
        exfalso
        apply hp
        refine ⟨P, Subtype.ext ?_⟩
        exact (primeIdealAtCode_eq_some_iff K).1 h
  rw [encodedIdealFactor, encodedIdealSummand,
    primeValueHom_apply_prime_subtype, encodedPrimeIdealWeight, hnone]
  simp

theorem dedekindZeta_primeIdeal_eulerProduct_hasProd {s : ℂ} (hs : 1 < s.re) :
    HasProd
      (fun P : HeightOneSpectrum (𝓞 K) ↦ primeIdealFactor K P s)
      (NumberField.dedekindZeta K s) := by
  have hEuler :
      HasProd (encodedIdealFactor K s)
        (∑' n, encodedIdealSummand K s n) := by
    exact EulerProduct.eulerProduct_completely_multiplicative_hasProd
      (summable_norm_encodedIdealSummand K hs)
  rw [(hasSum_encodedIdealSummand K hs).tsum_eq] at hEuler
  have hcodes :
      HasProd
        (encodedIdealFactor K s ∘ primeIdealCodeEmbedding K)
        (NumberField.dedekindZeta K s) :=
    ((primeIdealCodeEmbedding K).injective.hasProd_iff
      (encodedIdealFactor_eq_one_of_not_mem_range K s)).2 hEuler
  exact hcodes.congr_fun fun P ↦
    (encodedIdealFactor_primeIdealCode K s P).symm

theorem dedekindZeta_primeIdeal_eulerProduct_tprod {s : ℂ} (hs : 1 < s.re) :
    ∏' P : HeightOneSpectrum (𝓞 K), primeIdealFactor K P s =
      NumberField.dedekindZeta K s :=
  (dedekindZeta_primeIdeal_eulerProduct_hasProd K hs).tprod_eq

end NumberField.Odlyzko
