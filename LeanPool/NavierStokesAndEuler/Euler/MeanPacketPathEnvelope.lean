/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketSobolevData
import LeanPool.NavierStokesAndEuler.Euler.MeanPacketEnvelopeBounds
import LeanPool.NavierStokesAndEuler.Euler.MeanPathLpBlocks

/-! A single uniform-time forcing bound suffices for the normalized mean estimates. -/

@[expose] public section


noncomputable section

namespace EulerMeanPacketProvider.SobolevData

open EulerSmoothLimit EulerMeanTimeTranslation EulerMeanTimeContinuousTranslation
  EulerParameterWordGevrey EulerGevrey EulerPacketProfileRecursion
open scoped ContDiff

variable {D : Data} {ι : Type*} [Fintype ι] {q : ℕ} {R : ℝ}

theorem radius_nonneg (E : SobolevData D ι q R) : 0 ≤ R := by
  have hr : 0 ≤ E.Rc := (by norm_num : (0 : ℝ) ≤ 1024).trans E.radius_lower
  have hrc := sobolevCoefficientRadius_nonneg (ι := ι) E.Rc hr
  have hm : 0 ≤ E.M := (by norm_num : (0 : ℝ) ≤ 1).trans E.inverse_cost_lower
  exact (mul_nonneg (mul_nonneg (by norm_num) hm) (by linarith)).trans E.radius_budget

/-- The fixed normalized time factor may be chosen as max(1,sqrt(T)); it
does not depend on the forcing grade or scalar envelope. -/
theorem path_envelope_bounds (E : SobolevData D ι q R)
    (hCf1 : 1 ≤ E.Cf) (hCfT : Real.sqrt D.T ≤ E.Cf)
    (directions : ι → Space) (hd : ∀ i, ‖directions i‖ ≤ 1)
    {raw : VectorField} (G : Forcing D raw) (d : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hb : ∀ n a, block directions q (fun b : Space => pathTranslation D.T b G.path) n a ≤
      A*majorant R d n) :
    (∀ n a, block directions q (fun b : Space => pathTranslation D.T b G.velocityPath) n a ≤
      A*(E.velocityAmplitude*majorant R (d+2) n)) ∧
    (∀ n a, block directions q (fun b : Space => pathTranslation D.T b G.derivativePath) n a ≤
      A*(E.derivativeAmplitude*majorant R (d+3) n)) ∧
    (∀ n a, block directions q (fun b : Space => pathTranslation D.T b G.pressureForcePath) n a ≤
      A*(E.pressureAmplitude*majorant R (d+3) n)) := by
  apply E.envelope_bounds directions hd G d A hA
  · intro n a
    have h := (pathLp_block_le directions q D.T D.T_pos.le G.path G.path_orbit n a).trans
      (mul_le_mul_of_nonneg_left (hb n a) (Real.sqrt_nonneg D.T))
    have hm := mul_nonneg hA (majorant_nonneg R E.radius_nonneg d n)
    have hc := mul_le_mul_of_nonneg_right hCfT hm
    exact h.trans (by nlinarith)
  · intro n a
    have hm := mul_nonneg hA (majorant_nonneg R E.radius_nonneg d n)
    have hc := mul_le_mul_of_nonneg_right hCf1 hm
    exact (hb n a).trans (by nlinarith)

end EulerMeanPacketProvider.SobolevData
