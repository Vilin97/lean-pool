/-
Copyright (c) 2026 Imperial College London. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.DedekindZeta.LocalFactor
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-! TODO: Add doc-string. -/

@[expose] public section

open Ideal IsDedekindDomain

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

/-- A prime ideal norm used in the Odlyzko-bound argument. -/
noncomputable def primeIdealNorm (P : HeightOneSpectrum (𝓞 K)) : ℕ :=
  absNorm P.asIdeal

lemma one_lt_primeIdealNorm (P : HeightOneSpectrum (𝓞 K)) :
    1 < primeIdealNorm K P := by
  apply Nat.one_lt_iff_ne_zero_and_ne_one.mpr
  constructor
  · simpa [primeIdealNorm, Ideal.absNorm_eq_zero_iff] using P.ne_bot
  · simpa [primeIdealNorm, Ideal.absNorm_eq_one_iff] using P.isPrime.ne_top

/-- A prime ideal factor used in the Odlyzko-bound argument. -/
noncomputable def primeIdealFactor (P : HeightOneSpectrum (𝓞 K)) (s : ℂ) : ℂ :=
  localFactor (primeIdealNorm K P) s

lemma primeIdealFactor_ne_zero (P : HeightOneSpectrum (𝓞 K)) {s : ℂ} (hs : 0 < s.re) :
    primeIdealFactor K P s ≠ 0 :=
  localFactor_ne_zero (one_lt_primeIdealNorm K P) hs

end NumberField.Odlyzko
