/-
Copyright (c) 2026 Imperial College London. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.DedekindZeta.Coefficients
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Local Factor

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

namespace NumberField.Odlyzko

/-- An inverse norm power used in the Odlyzko-bound argument. -/
noncomputable def inverseNormPower (q : ℕ) (s : ℂ) : ℂ :=
  (q : ℂ) ^ (-s)

/-- A local factor used in the Odlyzko-bound argument. -/
noncomputable def localFactor (q : ℕ) (s : ℂ) : ℂ :=
  (1 - inverseNormPower q s)⁻¹

lemma norm_inverseNormPower (q : ℕ) (hq : 0 < q) (s : ℂ) :
    ‖inverseNormPower q s‖ = (q : ℝ) ^ (-s.re) := by
  simp [inverseNormPower, Complex.norm_natCast_cpow_of_pos hq]

lemma norm_inverseNormPower_lt_one {q : ℕ} (hq : 1 < q) {s : ℂ} (hs : 0 < s.re) :
    ‖inverseNormPower q s‖ < 1 := by
  rw [norm_inverseNormPower q (Nat.zero_lt_of_lt hq), Real.rpow_neg]
  · exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by simp_all) hs)
  · simp

lemma hasSum_inverseNormPower_pow {q : ℕ} (hq : 1 < q) {s : ℂ} (hs : 0 < s.re) :
    HasSum (fun e : ℕ ↦ inverseNormPower q s ^ e) (localFactor q s) := by
  simpa [localFactor] using
    hasSum_geometric_of_norm_lt_one (norm_inverseNormPower_lt_one hq hs)

lemma one_sub_inverseNormPower_ne_zero {q : ℕ} (hq : 1 < q) {s : ℂ} (hs : 0 < s.re) :
    1 - inverseNormPower q s ≠ 0 := by
  intro h
  have hpow : inverseNormPower q s = 1 := (eq_of_sub_eq_zero h).symm
  have hn := norm_inverseNormPower_lt_one hq hs
  simp_all

lemma localFactor_ne_zero {q : ℕ} (hq : 1 < q) {s : ℂ} (hs : 0 < s.re) :
    localFactor q s ≠ 0 :=
  inv_ne_zero (one_sub_inverseNormPower_ne_zero hq hs)

lemma hasDerivAt_inverseNormPower {q : ℕ} (hq : q ≠ 0) (s : ℂ) :
    HasDerivAt (inverseNormPower q)
      (inverseNormPower q s * Complex.log q * (-1)) s := by
  change HasDerivAt (fun z : ℂ ↦ (q : ℂ) ^ (-z))
    ((q : ℂ) ^ (-s) * Complex.log q * (-1)) s
  convert
    (hasDerivAt_neg s).const_cpow (c := (q : ℂ)) (Or.inl (Nat.cast_ne_zero.mpr hq))

end NumberField.Odlyzko
