/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.TransferProbability23
import LeanPool.Feige.TransferAlgebra
import LeanPool.Feige.LikelihoodRatio

/-!
# Complete interface for the local exponential transfer step

This file packages the probability identity and the likelihood-ratio
order comparison in forms intended for pointwise use along an insertion
chain.
-/

open MeasureTheory Real Set
open scoped ENNReal

namespace Feige

namespace Lemma43

open TransferStein TransferTestFunctions ProbabilityTheory

/-- The probability quantities attached to one law. -/
noncomputable def F (ν : Measure ℝ) : ℝ :=
  ENNReal.toReal (ν (Ici 0))

/-- The upper transfer-test expectation for `ν`. -/
noncomputable def A (ν : Measure ℝ) (d : ℝ) : ℝ :=
  ∫ z, transferPhi d z ∂ν

/-- The lower transfer-test expectation for `ν`. -/
noncomputable def B (ν : Measure ℝ) (c : ℝ) : ℝ :=
  ∫ z, transferPsi c z ∂ν

/-- The upper crossing probability for `ν`. -/
noncomputable def u (ν : Measure ℝ) (d : ℝ) : ℝ :=
  uProbability ν d

/-- The lower crossing probability for `ν`. -/
noncomputable def v (ν : Measure ℝ) (c : ℝ) : ℝ :=
  vProbability ν c

/-- The sum of the upper and lower crossing probabilities. -/
noncomputable def w (ν : Measure ℝ) (c d : ℝ) : ℝ :=
  u ν d + v ν c

/-- The upper crossing probability normalized by total crossing mass. -/
noncomputable def theta (ν : Measure ℝ) (c d : ℝ) : ℝ :=
  u ν d / w ν c d

theorem w_pos
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {c d : ℝ}
    (hc : 0 < c) (hd : 0 < d) :
    0 < w ν c d := by
  rw [w, u, v, uProbability_eq_integral ν hd,
    vProbability_eq_integral ν hc, ← integral_add
      (integrable_uTailIntegrand ν hd) (integrable_vTailIntegrand ν hc)]
  apply (integral_pos_iff_support_of_nonneg
    (fun z => add_nonneg (uTailIntegrand_nonneg d z)
      (vTailIntegrand_nonneg c z))
    ((integrable_uTailIntegrand ν hd).add
      (integrable_vTailIntegrand ν hc))).2
  have hs : Function.support
      (fun z => uTailIntegrand d z + vTailIntegrand c z) = Set.univ := by
    ext z
    simp only [Function.mem_support, mem_univ, iff_true]
    by_cases hz : 0 ≤ z
    · have hu : 0 < uTailIntegrand d z := by
        rw [uTailIntegrand, ite_eq_left hz]
        exact exp_pos _
      exact ne_of_gt (add_pos_of_pos_of_nonneg hu
        (vTailIntegrand_nonneg c z))
    · have hv : 0 < vTailIntegrand c z := by
        rw [vTailIntegrand, ite_eq_left (lt_of_not_ge hz)]
        exact exp_pos _
      exact ne_of_gt (add_pos_of_nonneg_of_pos
        (uTailIntegrand_nonneg d z) hv)
  rw [hs, measure_univ]
  exact zero_lt_one

/-- Explicit, auditable identification between the actual tail
probabilities of two laws and the four likelihood-ratio integrals. -/
def DensityIdentification
    (f : ℝ → ℝ≥0∞) (νP νM : Measure ℝ)
    (a b c d : ℝ) : Prop :=
  ENNReal.ofReal (u νP d) =
      LikelihoodRatio.uIntegral (LikelihoodRatio.fPlus f a) d ∧
  ENNReal.ofReal (u νM d) =
      LikelihoodRatio.uIntegral (LikelihoodRatio.fMinus f b) d ∧
  ENNReal.ofReal (v νP c) =
      LikelihoodRatio.vIntegral (LikelihoodRatio.fPlus f a) c ∧
  ENNReal.ofReal (v νM c) =
      LikelihoodRatio.vIntegral (LikelihoodRatio.fMinus f b) c

/-- The four elementary relations among `A,B,F,u,v,w`, kept as an
explicit proposition so that no probability identification is hidden. -/
def ProbabilityRelations
    (νP νM : Measure ℝ) (c d : ℝ) : Prop :=
  B νP c = A νP d + w νP c d ∧
  B νM c = A νM d + w νM c d ∧
  F νP = B νP c - v νP c ∧
  F νM = B νM c - v νM c

/-- Identity half of the local transfer step, stated entirely in the actual
probability quantities of the two laws. -/
theorem transfer_identity
    (νP νM : Measure ℝ) [IsProbabilityMeasure νP]
    [IsProbabilityMeasure νM] {a b c d : ℝ}
    (hc : 0 < c) (hd : 0 < d)
    (hrel : ProbabilityRelations νP νM c d)
    (hA : d * (A νP d - A νM d) =
      a * u νP d + b * u νM d)
    (hB : c * (B νP c - B νM c) =
      a * v νP c + b * v νM c) :
    (1 - theta νM c d) * (A νP d - A νM d) -
        (c / (c + d)) * (F νP - F νM) =
      ((a - c) / (c + d)) * w νP c d *
        (theta νP c d - theta νM c d) := by
  rcases hrel with ⟨hBP, hBM, hFP, hFM⟩
  apply exponentialTransfer_identity
    (uPlus := u νP d) (uMinus := u νM d)
    (vPlus := v νP c) (vMinus := v νM c)
    (wPlus := w νP c d) (wMinus := w νM c d)
    (APlus := A νP d) (AMinus := A νM d)
    (BPlus := B νP c) (BMinus := B νM c)
    (FPlus := F νP) (FMinus := F νM)
    (thetaPlus := theta νP c d) (thetaMinus := theta νM c d)
  · rfl
  · rfl
  · exact ne_of_gt (w_pos νP hc hd)
  · exact ne_of_gt (w_pos νM hc hd)
  · exact hBP
  · exact hBM
  · exact hFP
  · exact hFM
  · rfl
  · rfl
  · exact hA
  · exact hB
  · linarith

/-- Order half of the local transfer step after identifying the four actual
tail probabilities with the corresponding convolution-density integrals.
The identification hypotheses are the exact interface needed from a
density-of-pushforward lemma. -/
theorem theta_plus_ge_theta_minus_of_fourPoint
    {f : ℝ → ℝ≥0∞} (hfmeas : Measurable f)
    (hflc : LikelihoodRatio.FourPointLogConcave f)
    {a b c d uP uM vP vM : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (huP0 : 0 ≤ uP) (huM0 : 0 ≤ uM)
    (hvM0 : 0 ≤ vM)
    (hwP : 0 < uP + vP) (hwM : 0 < uM + vM)
    (huP : ENNReal.ofReal uP = LikelihoodRatio.uIntegral
      (LikelihoodRatio.fPlus f a) d)
    (huM : ENNReal.ofReal uM = LikelihoodRatio.uIntegral
      (LikelihoodRatio.fMinus f b) d)
    (hvP : ENNReal.ofReal vP = LikelihoodRatio.vIntegral
      (LikelihoodRatio.fPlus f a) c)
    (hvM : ENNReal.ofReal vM = LikelihoodRatio.vIntegral
      (LikelihoodRatio.fMinus f b) c) :
    uM / (uM + vM) ≤ uP / (uP + vP) := by
  have hcrossE :=
    LikelihoodRatio.uMinus_mul_vPlus_le hfmeas hflc ha hb
      (c := c) (d := d)
  rw [← huM, ← hvP, ← huP, ← hvM] at hcrossE
  have hcross : uM * vP ≤ uP * vM := by
    rw [← ENNReal.ofReal_mul huM0, ← ENNReal.ofReal_mul huP0] at hcrossE
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg huP0 hvM0)).mp hcrossE
  exact LikelihoodRatio.theta_le_theta_of_cross hwP hwM hcross

/-- Order half in the named probability quantities. -/
theorem theta_order
    {f : ℝ → ℝ≥0∞} (hfmeas : Measurable f)
    (hflc : LikelihoodRatio.FourPointLogConcave f)
    (νP νM : Measure ℝ) [IsProbabilityMeasure νP]
    [IsProbabilityMeasure νM] {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 < c) (hd : 0 < d)
    (hid : DensityIdentification f νP νM a b c d) :
    theta νM c d ≤ theta νP c d := by
  rcases hid with ⟨huP, huM, hvP, hvM⟩
  unfold theta w
  exact theta_plus_ge_theta_minus_of_fourPoint hfmeas hflc ha hb
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    ENNReal.toReal_nonneg
    (w_pos νP hc hd) (w_pos νM hc hd)
    huP huM hvP hvM

/-- Full auditable local-transfer interface for one insertion-chain edge.
The analytic/probability identities and the density identifications are
separate named hypotheses, and the conclusion exposes the factorized
transfer identity, the likelihood-ratio order, and positivity of both
denominators. -/
theorem complete
    {f : ℝ → ℝ≥0∞} (hfmeas : Measurable f)
    (hflc : LikelihoodRatio.FourPointLogConcave f)
    (νP νM : Measure ℝ) [IsProbabilityMeasure νP]
    [IsProbabilityMeasure νM] {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 < c) (hd : 0 < d)
    (hrel : ProbabilityRelations νP νM c d)
    (hA : d * (A νP d - A νM d) =
      a * u νP d + b * u νM d)
    (hB : c * (B νP c - B νM c) =
      a * v νP c + b * v νM c)
    (hid : DensityIdentification f νP νM a b c d) :
    ((1 - theta νM c d) * (A νP d - A νM d) -
          (c / (c + d)) * (F νP - F νM) =
        ((a - c) / (c + d)) * w νP c d *
          (theta νP c d - theta νM c d)) ∧
      theta νM c d ≤ theta νP c d ∧
      0 < w νP c d ∧ 0 < w νM c d := by
  refine ⟨transfer_identity νP νM hc hd hrel hA hB,
    theta_order hfmeas hflc νP νM ha hb hc hd hid, ?_, ?_⟩
  · exact w_pos νP hc hd
  · exact w_pos νM hc hd

end Lemma43

end Feige
