/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.SampCert.DifferentialPrivacy.Pure.DP
import LeanPool.HopfieldNet.SampCert.DifferentialPrivacy.Generic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Prod

/-!
# ``privPostProcess`` pure DP

This file establishes a pure DP bound for ``privPostProcess``
-/

noncomputable section

open Classical Set

namespace SLang

lemma privPostProcess_DP_bound {nq : Mechanism T U} {ε : NNReal} (h : PureDP nq ε) (f : U → V) :
  DP (privPostProcess nq f) ε := by
  simp [PureDP] at *
  rw [event_eq_singleton] at *
  simp [DP_singleton] at *
  intros l₁ l₂ neighbours x
  replace h := h l₁ l₂ neighbours
  simp [privPostProcess]
  apply ENNReal.div_le_of_le_mul
  rw [← ENNReal.tsum_mul_left]
  apply tsum_le_tsum _ ENNReal.summable (by aesop)
  intro i
  split
  · rename_i h
    subst h
    refine (ENNReal.div_le_iff_le_mul ?inl.hb0 ?inl.hbt).mp (h i)
    · aesop
    · right
      simp
      exact Real.exp_pos ε
  · simp

/--
``privPostProcess`` satisfies pure DP, for any surjective postprocessing function.
-/
theorem PureDP_PostProcess {f : U → V} (nq : Mechanism T U) (ε : NNReal) (h : PureDP nq ε) :
  PureDP (privPostProcess nq f) ε := by
  simp [PureDP] at *
  apply privPostProcess_DP_bound h

end SLang
