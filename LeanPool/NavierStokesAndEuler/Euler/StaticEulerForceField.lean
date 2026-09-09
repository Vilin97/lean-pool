/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.StaticEulerRegularity
public import LeanPool.NavierStokesAndEuler.Euler.FieldTowerGraphGevrey

@[expose] public section

/-! The actual normalized Euler pressure force has smooth ordinary L²
slices, with all derivative tensors continuous in time. -/

noncomputable section

namespace EulerStaticEuler

open Set ContinuousLinearMap EulerSmoothLimit EulerLpTranslation
  EulerAllOrderCorrectionData EulerAllOrderDriftCorrection

variable (P : ℝ) [Fact (0 < P)] (u : SmoothL2Field Space) (C R : ℝ)
  (hC : 0 ≤ C) (hR : 0 ≤ R) (hu : u.HasJetBound C R) (hdiv : ∀ x, divergence u.field x=0)

def localForceField (t : Icc (0 : ℝ) (amplitude P C R hC hR)) : SmoothL2Field Space :=
  SmoothL2Field.mapField (((amplitude P C R hC hR)⁻¹)^2 • ContinuousLinearMap.id ℝ Space)
    ((exactPacket P u C R hC hR hu hdiv).pressure.zeroGraphField
      (EulerTimeRescaling.timeMap (amplitude P C R hC hR) (amplitude_pos P C R hC hR) t))

theorem localForceField_apply (t : Icc (0 : ℝ) (amplitude P C R hC hR)) (x : Space) :
    (localForceField P u C R hC hR hu hdiv t).field x=localForce P u C R hC hR hu hdiv (t,x) := by
  change ((amplitude P C R hC hR)⁻¹)^2 •
    ((exactPacket P u C R hC hR hu hdiv).pressure.zeroGraphField _).field x = _
  rw [FieldTower.zeroGraphField_apply]
  change ((amplitude P C R hC hR)⁻¹)^2 •
    (exactPacket P u C R hC hR hu hdiv).pressure.pointField _ _ =
      ((amplitude P C R hC hR)⁻¹)^2 •
        EulerConstantEuler.force (exactPacket P u C R hC hR hu hdiv) ((amplitude P C R hC hR)⁻¹*(t
          : ℝ),x)
  have ht := (EulerTimeRescaling.timeMap (amplitude P C R hC hR) (amplitude_pos P C R hC hR)
    t).property
  change (t : ℝ)/amplitude P C R hC hR ∈ Icc (0 : ℝ) 1 at ht
  have he : (amplitude P C R hC hR)⁻¹*(t : ℝ)=(t : ℝ)/amplitude P C R hC hR := by ring
  rw [he]
  simp only [EulerConstantEuler.force,ExactLiftedPacket.rawPressure,FieldTower.rawField,
    projIcc_of_mem zero_le_one ht]
  rfl

theorem localForceField_jetLp_continuous (n : ℕ) :
    Continuous (fun t => (localForceField P u C R hC hR hu hdiv t).jetLp n) :=
  SmoothL2Field.continuous_jetLp_mapField _ _
    (fun n => ((exactPacket P u C R hC hR hu hdiv).pressure.zeroGraphField_jetLp_continuous n).comp
      (EulerTimeRescaling.timeMap (amplitude P C R hC hR) (amplitude_pos P C R hC hR)).continuous) n

end EulerStaticEuler
