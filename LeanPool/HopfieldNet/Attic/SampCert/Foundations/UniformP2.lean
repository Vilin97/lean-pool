/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.Attic.SampCert.SLang
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Nat.Log
import LeanPool.HopfieldNet.Attic.SampCert.Util.Util
import LeanPool.HopfieldNet.Attic.SampCert.Foundations.Monad
import LeanPool.HopfieldNet.Attic.SampCert.Foundations.Auto
import LeanPool.HopfieldNet.Attic.SampCert.Foundations.UniformByte

/-!
# ``probUniformP2`` Properties

This file contains lemmas about ``probUniformP2``, a ``SLang`` sampler for the
uniform distribution on spaces whose size is a power of two.
-/

open Classical Nat PMF

namespace SLang


/--
Evaluates the ``probUniformP2`` distribution at a point inside of its support.
-/
@[simp]
theorem UniformPowerOfTwoSample_apply (n : PNat) (x : Nat) (h : x < 2 ^ (log 2 n)) :
  (UniformPowerOfTwoSample n) x = 1 / (2 ^ (log 2 n)) := by
  simp [UniformPowerOfTwoSample]
  rw [probUniformP2_eval_support]
  · simp
  trivial

/--
Evaluates the ``probUniformP2`` distribution at a point outside of its support
-/
@[simp]
theorem UniformPowerOfTwoSample_apply' (n : PNat) (x : Nat) (h : x ≥ 2 ^ (log 2 n)) :
  UniformPowerOfTwoSample n x = 0 := by
  simp [UniformPowerOfTwoSample]
  rw [probUniformP2_eval_zero]
  trivial

lemma if_simpl_up2 (n : PNat) (x x_1: Fin (2 ^ log 2 ↑n)) :
  (@ite ENNReal (x_1 = x) (propDecidable (x_1 = x)) 0 (@ite ENNReal ((@Fin.val (2 ^ log 2 ↑n) x) = (@Fin.val (2 ^ log 2 ↑n) x_1)) (propDecidable ((@Fin.val (2 ^ log 2 ↑n) x) = (@Fin.val (2 ^ log 2 ↑n) x_1))) 1 0)) = 0 := by
  split
  · simp
  · split
    · rename_i h1 h2
      cases x
      rename_i x p
      cases x_1
      rename_i y q
      simp at *
      subst h2
      contradiction
    · simp

/--
The ``SLang`` term ``uniformPowerOfTwo`` is a proper distribution on ``ℕ``.
-/
theorem UniformPowerOfTwoSample_normalizes (n : PNat) :
  ∑' i : ℕ, UniformPowerOfTwoSample n i = 1 := by
  rw [UniformPowerOfTwoSample]
  rw [← @sum_add_tsum_nat_add' _ _ _ _ _ _ (2 ^ (log 2 n))]
  · rw [Finset.sum_range]
    conv =>
      enter [1]
      congr
      · enter [2, a]
        skip
        rw [probUniformP2_eval_support (by exact a.isLt)]
      · enter [1, a]
        rw [probUniformP2_eval_zero (by exact Nat.le_add_left (2 ^ log 2 ↑n) a)]
    simp
    apply ENNReal.mul_inv_cancel
    · simp
    · simp
  exact ENNReal.summable

end SLang
