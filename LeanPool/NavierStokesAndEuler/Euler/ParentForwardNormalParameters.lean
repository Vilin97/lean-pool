/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentNormalPacketParameters
public import LeanPool.NavierStokesAndEuler.Euler.ParentForwardUniformCosts
import LeanPool.NavierStokesAndEuler.Euler.ParentPacketNeighborPolynomial

/-! The zero-history normal stage has the same fixed parameter envelope
as every positive-history stage. Its actual initial coordinate has norm one. -/

@[expose] public section


noncomputable section

namespace EulerParentPacketFrames.LabelData

open Set Real EulerSmoothLimit EulerTransverseFrameCoordinates EulerTransversePacketProvider
  EulerPacketSourceGeometry EulerPacketSourceScales EulerPacketSourceScaleChoice
  EulerPacketSourceScaleSequence EulerPacketBaseGuardScales EulerPacketLowConstants
  EulerParentPacketParameterCaps EulerNormalPacketParameters

variable {A : Parent} (L : LabelData A) (H : LowBounds A)
  {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (m : Space) (hm : ‖m‖ = 1) (R : U ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hsupport : IsCompact support)
  (P : ParentFrame (A.transverseData m hm R support hsupport) 0) (G : ForwardGuards P)

omit [CompleteSpace U] in
theorem forwardNormalParameterSize_bound (J D : ℕ) (hJ : 2 ≤ J) (C X : ℝ) (hC : 1 ≤ C) (hX : 1 ≤ X)
    (n : ℕ) (Ti : ℝ)
    (hbaseH : X ^ 1000 ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 7))
    (hbaseK : X ^ D ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 4))
    (hK : L.K ≤ previousFrequency J D X n ^ 80)
    (hTi : Ti ≤ 12 / baseHorizon J X)
    (hBc : H.Bc ≤ gradientConstant * X ^ 1000 + 2)
    (hL : H.L = EulerMeanHarmonic.boundaryLocalizationC1 * H.Bc + 1)
    (hΘ : P.horizon ≤ sourceTheta J C (scaleSequence J X) n)
    (hδ : G.δ = spike J X n) (hh : G.hchild = shear J X n)
    (hshear : P.shear = previousShear J X n) :
    L.geometryForwardParameterSize H m hm R support hsupport P G Ti G.initialCoordinate ≤
      envelope J C X n := by
  have hprev : 1 ≤ P.shear := hshear.symm ▸ previousShear_one J (by omega) X hX n
  have hterm : ‖G.initialCoordinate‖ ≤ terminalCap*L.K^4 := by
    rw [G.initialCoordinate_norm]
    exact one_le_mul_of_one_le_of_one_le terminalCap_one (one_le_pow₀ L.K_one)
  have hboundary := boundary_parameter_bound gradientConstant H.Bc H.L X hX hBc hL
  have hEi : P.epsilon⁻¹ ≤ 2*previousShear J X n := by
    rw [← hshear]
    exact P.epsilon_inv_le_twice_shear G.coupling_lower hprev
  have hbasepos := baseHorizon_pos J (by omega) (zero_lt_one.trans_le hX)
  have hraw := EulerPacketParameterEnvelope.source_size_le J D hJ X hX
    C (boundaryConstant gradientConstant) terminalCap 80 320 hC
    (boundaryConstant_pos gradientConstant gradient_nonneg).le (zero_le_one.trans terminalCap_one)
    (by norm_num) (by norm_num) (by norm_num) 4 (by norm_num) hbaseH hbaseK n
    L.K 0 Ti (560*P.horizon^10/P.epsilon) H.L ‖G.initialCoordinate‖ P.horizon P.epsilon⁻¹
    (zero_le_one.trans L.K_one) (by simpa only [rpow_ofNat] using hK)
    (by positivity) hTi hboundary hterm (zero_le_one.trans G.horizon_lower) hΘ
    (inv_nonneg.mpr G.epsilon_pos.le) hEi (by rw [div_eq_mul_inv])
  change EulerParentInitializedRadius.parameterSize L.K 0 Ti (560*P.horizon^10/P.epsilon)
    H.L G.δ ‖G.initialCoordinate‖+G.hchild ≤ _
  rw [hδ,hh]
  exact hraw

end EulerParentPacketFrames.LabelData
