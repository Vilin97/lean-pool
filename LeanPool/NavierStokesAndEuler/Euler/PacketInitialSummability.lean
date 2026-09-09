/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInitialInput
public import LeanPool.NavierStokesAndEuler.Euler.PacketUniformFrequencyScales
import LeanPool.NavierStokesAndEuler.Euler.PacketInitialScaleSummability
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! Source (22) for a sequence of the actual solved packet increments.
Only the source parameter cap and literal scale identities are supplied;
all field estimates and the geometric amplitude decay are derived. -/

@[expose] public section


noncomputable section

namespace EulerPacketInitial

open Set MeasureTheory EulerSmoothLimit EulerPhysicalL2Scaling EulerPacketInitialScale
  EulerPacketSourceScaleChoice EulerPacketSourceScaleSequence EulerPacketUniformFrequencyScales

variable {U : ℕ → Type} [∀ n, NormedAddCommGroup (U n)] [∀ n, InnerProductSpace ℝ (U n)]
  [∀ n, CompleteSpace (U n)] (A : ∀ n, Input (U n))
  (J : ℕ) (hJ : 2 ≤ J) (C c : ℝ) (hC : 0 < C) (hc : 0 ≤ c)
  (p q : ℕ) (X : ℝ) (hX : 1 ≤ X)
  (hparameter : ∀ n, (A n).parameterSize ≤ parameterEnvelope J C c p q X n)
  (hscale : ∀ n, (A n).parent.ell = supportScale J X n)
  (hσ : ∀ n, (A n).frame.sigma * scaleSequence J X n ≤ 2)
  (hk : ∀ n, 4 ≤ frequency J X n)
  (hfrequency : ∀ n, (A n).frequencyGuard (frequency J X n))

include hJ hC hc hX hparameter hscale hσ hk hfrequency in
theorem actual_high_summable (s : ℕ) :
    Summable (fun n => derivativeSum s ((A n).high (frequency J X n))) := by
  have hs := high_summable J hJ C c
    (EulerPacketInitialAmplitude.boundConstant*EulerPacketInitialCost.sourceConstant s)
    hC hc (mul_pos EulerPacketInitialAmplitude.constant_pos
        (EulerPacketInitialCost.sourceConstant_pos s))
    p q (EulerPacketInitialAmplitude.degree+EulerPacketInitialCost.sourcePower s) s X hX
  apply hs.of_nonneg_of_le
  · intro n
    exact Finset.sum_nonneg (fun _ _ => lpNorm_nonneg)
  · intro n
    have hb := ((A n).initial_bounds (scaleSequence J X n) (hσ n)
      (frequency J X n) (hk n) (hfrequency n) s).1
    rw [hscale n] at hb
    apply hb.trans
    unfold highMajorant
    apply mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    apply mul_le_mul_of_nonneg_left ?_ (by unfold supportScale frequency; positivity)
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (zero_le_one.trans (A n).parameterSize_one) (hparameter n) _)
      (mul_pos EulerPacketInitialAmplitude.constant_pos (EulerPacketInitialCost.sourceConstant_pos
          s)).le

include hJ hC hX hparameter hscale hσ hk hfrequency in
theorem actual_mean_summable (s : ℕ) :
    Summable (fun n => derivativeSum s ((A n).mean (frequency J X n))) := by
  have hs := mean_summable J hJ C c (EulerPacketInitialCost.sourceConstant s)
    hC (EulerPacketInitialCost.sourceConstant_pos s) p q (EulerPacketInitialCost.sourcePower s) s X
        hX
  apply hs.of_nonneg_of_le
  · intro n
    exact Finset.sum_nonneg (fun _ _ => lpNorm_nonneg)
  · intro n
    have hb := ((A n).initial_bounds (scaleSequence J X n) (hσ n)
      (frequency J X n) (hk n) (hfrequency n) s).2
    rw [hscale n] at hb
    apply hb.trans
    unfold meanMajorant
    apply mul_le_mul_of_nonneg_left ?_ (by unfold supportScale frequency; positivity)
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (zero_le_one.trans (A n).parameterSize_one) (hparameter n) _)
      (EulerPacketInitialCost.sourceConstant_pos s).le

end EulerPacketInitial
