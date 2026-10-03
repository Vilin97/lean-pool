/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.Table.Common
public import LeanPool.Zeta5Irrational.Certificates
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Reusable upper certificates for arcsine potentials -/

public section

namespace Zeta5Irrational

/-- An upper certificate for an arcsine potential to the left of its support. -/
lemma Uω_le_left_certificate {a b t s q U : ℝ} (hab : a < b) (ht : t ≤ a) (hs : 0 ≤ s)
    (hsq : (t - a) * (t - b) ≤ s ^ 2) (hq : ((a + b) / 2 - t + s) / 2 ≤ q)
    (hlog : Real.log q ≤ U) : Uω a b t ≤ U := by
  rw [Uω_of_le hab ht]
  have hroot := sqrt_le_of_sq_le hs hsq
  have hroot0 := Real.sqrt_nonneg ((t - a) * (t - b))
  apply (Real.log_le_log (by linarith) ?_).trans hlog
  linarith

/-- An upper certificate for an arcsine potential to the right of its support. -/
lemma Uω_le_right_certificate {a b t s q U : ℝ} (hab : a < b) (ht : b ≤ t) (hs : 0 ≤ s)
    (hsq : (t - a) * (t - b) ≤ s ^ 2) (hq : (t - (a + b) / 2 + s) / 2 ≤ q)
    (hlog : Real.log q ≤ U) : Uω a b t ≤ U := by
  rw [Uω_of_ge hab ht]
  have hroot := sqrt_le_of_sq_le hs hsq
  have hroot0 := Real.sqrt_nonneg ((t - a) * (t - b))
  apply (Real.log_le_log (by linarith) ?_).trans hlog
  linarith

end Zeta5Irrational
