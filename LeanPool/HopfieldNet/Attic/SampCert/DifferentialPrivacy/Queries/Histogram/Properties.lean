/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.SampCert.DifferentialPrivacy.Queries.Histogram.Code
import LeanPool.HopfieldNet.SampCert.DifferentialPrivacy.Sensitivity
import LeanPool.HopfieldNet.SampCert.DifferentialPrivacy.Abstract

/-!
# ``privHistogram`` Properties

This file proves abstract differential privacy for the noised histogram.
-/

open Classical Nat Int Real

noncomputable section

namespace SLang

variable {T : Type}
variable [dps : DPSystem T]
variable [HT : Inhabited T]

variable (numBins : ℕ+)
variable (B : Bins T numBins)

-- def exactBinCount (b : Fin num_bins) (l : List T) : ℤ :=
--   List.length (List.filter (fun v => B.bin v = b) l)

/-
exactBinCount is 1-sensitive
-/
theorem exactBinCount_sensitivity (b : Fin numBins) : sensitivity (exactBinCount numBins B b) 1 := by
  rw [sensitivity]
  intros l₁ l₂ HN
  cases HN
  · rename_i l₁' l₂' v' Hl₁ Hl₂
    rw [ Hl₁, Hl₂ ]
    rw [exactBinCount, exactBinCount]
    simp [List.filter_cons]
    aesop
  · rename_i l₁' v' l₂' Hl₁ Hl₂
    rw [ Hl₁, Hl₂ ]
    rw [exactBinCount, exactBinCount]
    simp [List.filter_cons]
    aesop
  · rename_i l₁' v₁' l₂' v₂' Hl₁ Hl₂
    rw [ Hl₁, Hl₂ ]
    rw [exactBinCount, exactBinCount]
    simp [List.filter_cons]
    -- There has to be a better way
    cases (Classical.em (B.bin v₁' = b)) <;> cases (Classical.em (B.bin v₂' = b))
    all_goals (rename_i Hrw1 Hrw2)
    all_goals (simp [Hrw1, Hrw2])

/--
DP bound for a noised bin count
-/
lemma privNoisedBinCount_DP (ε₁ ε₂ : ℕ+) (b : Fin numBins) :
  dps.prop (privNoisedBinCount numBins B ε₁ ε₂ b) (ε₁ / ((ε₂ * numBins : PNat))) := by
  unfold privNoisedBinCount
  apply dps.noise_prop
  apply exactBinCount_sensitivity

-- MARKUSDE: Looking at this proof it is clear that we need better tactic support for the abstract DP operators
-- MARKUSDE: - Lemmas with equality side conditions for the privacy cost
/--
DP bound for intermediate steps in the histogram calculation.
-/
lemma privNoisedHistogramAux_DP (ε₁ ε₂ : ℕ+) (n : ℕ) (Hn : n < numBins) :
  dps.prop (privNoisedHistogramAux numBins B ε₁ ε₂ n Hn) (n.succ * (ε₁ / (ε₂ * numBins : PNat))) := by
  induction n
  · unfold privNoisedHistogramAux
    simp only [Nat.cast_zero, succ_eq_add_one, zero_add, Nat.cast_one, Nat.cast_mul, one_mul]
    refine DPSystem.postprocess_prop
             (privCompose (privNoisedBinCount numBins B ε₁ ε₂ 0) (privConst (emptyHistogram numBins B)))
             (↑↑ε₁ / ↑↑(ε₂ * numBins)) ?G1
    apply (DPSystem_prop_ext _ ?HEq ?Hdp)
    case Hdp =>
      apply (DPSystem.compose_prop
              (privNoisedBinCount numBins B ε₁ ε₂ 0)
              (privConst (emptyHistogram numBins B))
              (↑↑ε₁ / ↑↑(ε₂ * numBins))
              0
              (privNoisedBinCount_DP numBins B ε₁ ε₂ 0)
              (DPSystem.const_prop (emptyHistogram numBins B)))
    case HEq => simp only [PNat.mul_coe, Nat.cast_mul, add_zero]
  · rename_i n IH
    unfold privNoisedHistogramAux
    simp only []
    refine DPSystem.postprocess_prop
      (privCompose (privNoisedBinCount numBins B ε₁ ε₂ ↑(n + 1))
      (privNoisedHistogramAux numBins B ε₁ ε₂ n (privNoisedHistogramAux.proof_2 numBins n Hn)))
      (↑(n + 1).succ * (↑↑ε₁ / ↑↑(ε₂ * numBins))) ?succ.a
    apply (@DPSystem_prop_ext _ _ _ (?C1 + ?C2) _ _ ?HCeq ?Hdp)
    case Hdp =>
      refine
        (DPSystem.compose_prop
          (privNoisedBinCount numBins B ε₁ ε₂ ↑(n + 1))
          (privNoisedHistogramAux numBins B ε₁ ε₂ n _) (↑↑ε₁ / ↑↑(ε₂ * numBins)) (↑n.succ * (↑↑ε₁ / ↑↑(ε₂ * numBins))) ?X ?Y)
      case X => exact privNoisedBinCount_DP numBins B ε₁ ε₂ ↑(n + 1)
      case Y => apply IH
    generalize (ε₁.val.cast / (ε₂ * numBins).val.cast : NNReal) = A
    conv =>
      enter [1, 1]
      rw [Eq.symm (one_mul A)]
    rw [<- add_mul]
    congr
    simp only [succ_eq_add_one, Nat.cast_add, Nat.cast_one]
    exact AddCommMagma.add_comm (OfNat.ofNat 1) (n.cast + OfNat.ofNat 1)

/--
DP bound for a noised histogram
-/
lemma privNoisedHistogram_DP (ε₁ ε₂ : ℕ+) :
  dps.prop (privNoisedHistogram numBins B ε₁ ε₂) (ε₁ / ε₂) := by
  unfold privNoisedHistogram
  apply (DPSystem_prop_ext _ ?HEq ?Hdp)
  case Hdp => apply privNoisedHistogramAux_DP
  case HEq =>
    simp
    rw [division_def]
    rw [division_def]
    rw [mul_inv]
    conv =>
      enter [1, 2]
      rw [<- mul_assoc]
      rw [mul_comm]
    generalize (ε₁.val.cast * ε₂.val.cast⁻¹ : NNReal)  = A
    rw [<- mul_assoc]
    conv =>
      enter [2]
      rw [Eq.symm (one_mul A)]
    congr
    unfold predBins
    cases numBins
    rename_i n' Hn'
    simp only [PNat.natPred_eq_pred, pred_eq_sub_one, cast_tsub, Nat.cast_one, PNat.mk_coe]
    rw [tsub_add_eq_max]
    rw [max_eq_left (one_le_cast.mpr Hn')]
    apply mul_inv_cancel
    intro HK
    simp_all
    rw [HK] at Hn'
    cases Hn'


/--
DP bound for the thresholding maximum
-/
lemma privMaxBinAboveThreshold_DP (ε₁ ε₂ : ℕ+) (τ : ℤ) :
  dps.prop (privMaxBinAboveThreshold numBins B ε₁ ε₂ τ) (ε₁ / ε₂) := by
  rw [privMaxBinAboveThreshold]
  apply dps.postprocess_prop
  apply privNoisedHistogram_DP

end SLang
