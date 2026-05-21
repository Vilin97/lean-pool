/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.Attic.SampCert.SLang
import LeanPool.HopfieldNet.Attic.SampCert.DifferentialPrivacy.Generic
import LeanPool.HopfieldNet.Attic.SampCert.DifferentialPrivacy.Neighbours
-- import SampCert.DifferentialPrivacy.Pure.DP
-- import SampCert.DifferentialPrivacy.ZeroConcentrated.DP
-- import SampCert.Util.Log

noncomputable section

open Classical

variable { T : Type }

namespace SLang

/--
Approximate differential privacy bound
-/
def DP' (m : Mechanism T U) (ε : ℝ) (δ : NNReal) : Prop :=
  ∀ l₁ l₂ : List T, Neighbour l₁ l₂ → ∀ S : Set U,
  (∑' x : U, if x ∈ S then m l₁ x else 0) ≤ δ + ENNReal.ofReal (Real.exp ε) * (∑' x : U, if x ∈ S then m l₂ x else 0)

/--
Approximate differential privacy
-/
def ApproximateDP (m : Mechanism T U) (ε : ℝ) (δ : NNReal) : Prop :=
  DP' m ε δ

/--
Approximate DP is trivial with δ ≥ 1
-/
theorem ApproximateDP_gt1 (m : Mechanism T U) (ε : ℝ) {δ : NNReal} (Hδ : 1 ≤ δ) : ApproximateDP m ε δ := by
  rw [ApproximateDP]
  rw [DP']
  intros l₁ l₂ _ S
  have H1 : (∑' (x : U), if x ∈ S then (m l₁) x else 0) ≤ 1 := by
    rw [<- PMF.tsum_coe (m l₁)]
    apply ENNReal.tsum_le_tsum
    intro u
    split <;> simp
  apply le_trans H1
  conv =>
    left
    rw [<- add_zero 1]
  apply add_le_add
  · simp
    trivial
  · apply mul_nonneg
    · exact zero_le (ENNReal.ofReal (Real.exp ε))
    · exact zero_le (∑' (x : U), if x ∈ S then (m l₂) x else 0)


end SLang
