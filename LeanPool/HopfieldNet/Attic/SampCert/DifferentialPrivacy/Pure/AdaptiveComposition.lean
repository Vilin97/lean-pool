/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.SampCert.DifferentialPrivacy.Generic
import LeanPool.HopfieldNet.SampCert.DifferentialPrivacy.Pure.DP
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Prod
import Mathlib.Logic.IsEmpty

noncomputable section

open Classical Set

variable [Hu : Nonempty U]

namespace SLang

-- Better proof for Pure DP adaptive composition
theorem PureDP_ComposeAdaptive' (nq1 : List T → PMF U) (nq2 : U -> List T → PMF V) (ε₁ ε₂ : NNReal) (h1 : PureDP nq1 ε₁)  (h2 : ∀ u : U, PureDP (nq2 u) ε₂) :
  PureDP (privComposeAdaptive nq1 nq2) (ε₁ + ε₂) := by
  simp [PureDP] at *
  rw [event_eq_singleton] at *
  simp [DP_singleton] at *
  intros l₁ l₂ Hl₁l₂ u v
  rw [privComposeChainRule]
  rw [privComposeChainRule]
  rw [Real.exp_add]
  rw [ENNReal.ofReal_mul ?s1]
  case s1 => apply Real.exp_nonneg
  rw [ENNReal.div_eq_inv_mul]

  cases Classical.em ((nq1 l₂) u * (nq2 u l₂) v = 0)
  · rename_i Hz
    rw [Hz]
    simp
    simp at Hz
    cases Hz
    · cases (Classical.em (nq1 l₁ u = 0))
      · simp_all
      · rename_i HA HB
        exfalso
        have hcont := h1 l₁ l₂ Hl₁l₂ u
        simp [HA, division_def] at hcont
        rw [ENNReal.mul_top HB] at hcont
        simp_all
    · cases (Classical.em (nq2 u l₁ v = 0))
      · simp_all
      · rename_i HA HB
        exfalso
        have hcont := h2 u
        rw [event_eq_singleton] at hcont
        simp [DP_singleton] at hcont
        have hcont := hcont l₁ l₂ Hl₁l₂ v
        simp [HA, division_def] at hcont
        rw [ENNReal.mul_top HB] at hcont
        simp_all
  · rw [ENNReal.mul_inv]
    · rw [<- mul_assoc]
      rw [mul_right_comm]
      conv =>
        lhs
        arg 1
        rw [mul_assoc]
      rw [mul_right_comm]
      rw [← ENNReal.div_eq_inv_mul]
      rw [← ENNReal.div_eq_inv_mul]
      have h2a'_pre := h2 u
      rw [event_eq_singleton] at h2a'_pre
      simp [DP_singleton] at h2a'_pre
      exact (mul_le_mul' (h1 l₁ l₂ Hl₁l₂ u) (h2a'_pre l₁ l₂ Hl₁l₂ v))
    · left
      rename_i hnz
      intro HK
      simp_all
    · right
      intro HK
      simp_all
end SLang
