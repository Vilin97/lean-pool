/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.DedekindZeta.LocalFactor
public import Mathlib.Analysis.Calculus.LogDeriv

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Complex

namespace NumberField.Odlyzko

theorem hasDerivAt_localFactor {q : ℕ} (hq : 1 < q) {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (localFactor q)
      (-(inverseNormPower q s * Complex.log q /
        (1 - inverseNormPower q s) ^ 2)) s := by
  have hx := hasDerivAt_inverseNormPower (q := q) (Nat.ne_zero_of_lt hq) s
  have hden : 1 - inverseNormPower q s ≠ 0 :=
    one_sub_inverseNormPower_ne_zero hq hs
  change HasDerivAt (fun z : ℂ ↦ (1 - inverseNormPower q z)⁻¹) _ s
  apply (hx.const_sub 1).fun_inv hden |>.congr_deriv
  ring

theorem logDeriv_localFactor {q : ℕ} (hq : 1 < q) {s : ℂ} (hs : 0 < s.re) :
    logDeriv (localFactor q) s =
      -(Complex.log q * inverseNormPower q s /
        (1 - inverseNormPower q s)) := by
  rw [logDeriv_apply, (hasDerivAt_localFactor hq hs).deriv]
  simp only [localFactor]
  grind

theorem hasSum_logDeriv_localFactor {q : ℕ} (hq : 1 < q) {s : ℂ} (hs : 0 < s.re) :
    HasSum
      (fun e : ℕ ↦ Complex.log q * inverseNormPower q s ^ (e + 1))
      (-logDeriv (localFactor q) s) := by
  have hgeom := hasSum_inverseNormPower_pow hq hs
  have hmul := hgeom.mul_left
    (Complex.log q * inverseNormPower q s)
  have hvalue :
      Complex.log q * inverseNormPower q s * localFactor q s =
        Complex.log q * inverseNormPower q s /
          (1 - inverseNormPower q s) := by
    simp [localFactor, div_eq_mul_inv]
  rw [logDeriv_localFactor hq hs, neg_neg, ← hvalue]
  grind

end NumberField.Odlyzko
