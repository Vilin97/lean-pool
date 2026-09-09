/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderTranslation
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpBoundedMap

@[expose] public section

/-! The adjoint of the genuine mixed cylinder translation is its inverse. -/

noncomputable section

namespace EulerLpCylinderTranslation

open ContinuousLinearMap InnerProductSpace EulerLiftedGradientSpace

variable (P : ℝ) [Fact (0 < P)] {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

theorem translate_adjoint (a : LiftTangent) :
    ((translate (V := V) P a).toContinuousLinearMap).adjoint =
      (translate P (-a)).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right ℝ
  intro v
  rw [adjoint_inner_left]
  change ⟪u,translate P a v⟫_ℝ = ⟪translate P (-a) u,v⟫_ℝ
  simpa only [translate_add,add_neg_cancel,translate_zero] using
    (translate (V := V) P a).inner_map_map (translate P (-a) u) v

end EulerLpCylinderTranslation

namespace EulerTimeLpBoundedMap

open Set MeasureTheory ContinuousLinearMap EulerTimeLp EulerVolterraConvolution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The actual continuous-time embedding commutes with bounded spatial maps. -/
theorem pathLp_timeLift (T : ℝ) (hT : 0 ≤ T) (A : E →L[ℝ] F)
    (f : C(Icc (0 : ℝ) T,E)) :
    pathLp T hT ((A.compLeftContinuous ℝ (Icc (0 : ℝ) T)) f) =
      timeLift T A (pathLp T hT f) := by
  apply Lp.ext
  filter_upwards [pathLp_ae T hT ((A.compLeftContinuous ℝ (Icc (0 : ℝ) T)) f),
    timeLift_ae T A (pathLp T hT f),pathLp_ae T hT f] with t hl hr hf
  rw [hl,hr,hf]
  rfl

end EulerTimeLpBoundedMap
