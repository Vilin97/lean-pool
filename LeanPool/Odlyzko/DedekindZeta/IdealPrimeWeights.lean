/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.DedekindZeta.IdealPrimeFactorization
public import LeanPool.Odlyzko.DedekindZeta.PrimeIdealFactor

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Complex Ideal IsDedekindDomain

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

theorem absNorm_idealOfPrimeFactors
    (m : Multiset (HeightOneSpectrum (𝓞 K))) :
    absNorm (idealOfPrimeFactors K m : Ideal (𝓞 K)) =
      (m.map (primeIdealNorm K)).prod := by
  rw [idealOfPrimeFactors_coe, map_multiset_prod]
  rw [Multiset.map_map]
  rfl

theorem inverseNormPower_idealOfPrimeFactors
    (m : Multiset (HeightOneSpectrum (𝓞 K))) (s : ℂ) :
    ((absNorm (idealOfPrimeFactors K m : Ideal (𝓞 K)) : ℂ) ^ (-s)) =
      (m.map (fun P ↦ inverseNormPower (primeIdealNorm K P) s)).prod := by
  rw [absNorm_idealOfPrimeFactors]
  induction m using Multiset.induction_on with
  | empty => simp
  | cons P m ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons]
      rw [Nat.cast_mul]
      rw [show
        ((primeIdealNorm K P : ℂ) *
            ((m.map (primeIdealNorm K)).prod : ℂ)) ^ (-s) =
          (primeIdealNorm K P : ℂ) ^ (-s) *
            ((m.map (primeIdealNorm K)).prod : ℂ) ^ (-s) by
        simpa only [ofReal_natCast] using mul_cpow_ofReal_nonneg
          (Nat.cast_nonneg (primeIdealNorm K P))
          (Nat.cast_nonneg (m.map (primeIdealNorm K)).prod) (-s)]
      rw [ih]
      rfl

theorem inverseNormPower_nonzeroIdealEquivPrimeFactors
    (I : NonzeroIdeal K) (s : ℂ) :
    ((absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-s)) =
      ((nonzeroIdealEquivPrimeFactors K I).map
        (fun P ↦ inverseNormPower (primeIdealNorm K P) s)).prod := by
  rw [← inverseNormPower_idealOfPrimeFactors]
  congr 2
  exact congr_arg absNorm
    (congr_arg Subtype.val
      ((nonzeroIdealEquivPrimeFactors K).left_inv I).symm)

end NumberField.Odlyzko
