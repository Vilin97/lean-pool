/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeAmplitudeScaling
public import LeanPool.NavierStokesAndEuler.Euler.SmoothL2Gevrey
import LeanPool.NavierStokesAndEuler.Euler.PhysicalGraphGevrey
import Mathlib.Algebra.Order.Star.Real

/-! Quantitative spatial jet bounds under actual Euler time/amplitude
rescaling. The constants are explicit and the spatial radius is unchanged. -/

@[expose] public section


noncomputable section

namespace EulerTimeRescaling

open Set ContinuousLinearMap EulerSmoothLimit EulerLpTranslation
open scoped ContDiff BoundedContinuousFunction

variable {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Cache the standard `NormedAddCommGroup (E [×n]→L[ℝ] V)` instance to shorten typeclass
synthesis. -/
local instance instSmoothTimeAmplitudeBounds1 (n : ℕ) : NormedAddCommGroup (E [×n]→L[ℝ] V) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (E [×n]→L[ℝ] V)` instance to shorten typeclass synthesis. -/
local instance instSmoothTimeAmplitudeBounds2 (n : ℕ) : NormedSpace ℝ (E [×n]→L[ℝ] V) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] V))` instance to shorten typeclass
synthesis. -/
local instance instSmoothTimeAmplitudeBounds3 (n : ℕ) : NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] V))
    := inferInstance
/-- Cache the standard `NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] V))` instance to shorten typeclass
synthesis. -/
local instance instSmoothTimeAmplitudeBounds4 (n : ℕ) : NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] V)) :=
    inferInstance

theorem smul_id_norm_le (a : ℝ) (ha : 0 ≤ a) : ‖a • ContinuousLinearMap.id ℝ V‖ ≤ a := by
  apply opNorm_le_bound _ ha
  intro v
  simp only [smul_apply,id_apply,norm_smul,Real.norm_of_nonneg ha,le_refl]

theorem coefficient_jet_norm (ε : ℝ) (hε : 0 < ε)
    (A : SmoothTimeField (Icc (0 : ℝ) 1) E V) (n : ℕ) :
    ‖(coefficient ε hε A).jet n‖ ≤ ε⁻¹*‖A.jet n‖ := by
  apply ((A.compTime (timeMap ε hε)).map_jet_norm_le
    (ε⁻¹ • ContinuousLinearMap.id ℝ V) n).trans
  exact mul_le_mul (smul_id_norm_le ε⁻¹ (inv_nonneg.mpr hε.le))
    (A.compTime_jet_norm (timeMap ε hε) n) (norm_nonneg _) (inv_nonneg.mpr hε.le)

theorem derivativeCoefficient_jet_norm (ε : ℝ) (hε : 0 < ε)
    (A : SmoothTimeField (Icc (0 : ℝ) 1) E V) (n : ℕ) :
    ‖(derivativeCoefficient ε hε A).jet n‖ ≤ (ε⁻¹)^2*‖A.jet n‖ := by
  apply ((A.compTime (timeMap ε hε)).map_jet_norm_le
    ((ε⁻¹)^2 • ContinuousLinearMap.id ℝ V) n).trans
  exact mul_le_mul (smul_id_norm_le ((ε⁻¹)^2) (sq_nonneg _))
    (A.compTime_jet_norm (timeMap ε hε) n) (norm_nonneg _) (sq_nonneg _)

theorem mapField_hasJetBound (a : ℝ) (ha : 0 ≤ a) (F : SmoothL2Field V)
    (C R : ℝ) (hF : F.HasJetBound C R) :
    (SmoothL2Field.mapField (a • ContinuousLinearMap.id ℝ V) F).HasJetBound (a*C) R := by
  intro n
  apply (SmoothL2Field.norm_jetLp_map_le _ F n).trans
  apply (mul_le_mul_of_nonneg_right (smul_id_norm_le a ha) (norm_nonneg _)).trans
  exact (mul_le_mul_of_nonneg_left (hF n) ha).trans_eq (by ring)

end EulerTimeRescaling
