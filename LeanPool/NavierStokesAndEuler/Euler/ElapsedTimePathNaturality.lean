/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ElapsedTimePathGluing
public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderTranslation

/-! Bounded spatial maps and mixed derivative words commute with the actual elapsed-time join. -/

@[expose] public section


noncomputable section

namespace EulerElapsedTimePathGluing

open Set ContinuousLinearMap EulerTimeIntervalGlue EulerPacketTimePathGluing
  EulerVolterraConvolution EulerParameterWordGevrey
open scoped ContDiff

attribute [local instance] EulerPacketTimePathGluing.compactInterval

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S)
  (u : C(Icc (0 : ℝ) τ, E)) (v : C(Icc (0 : ℝ) (S - τ), E))
  (hm : u ⟨τ, hτ0, le_rfl⟩ = v ⟨0, le_rfl, sub_nonneg.mpr hτS⟩)

theorem join_map (L : E →L[ℝ] F) :
    L.compLeftContinuous ℝ (Icc (0 : ℝ) S) (join S τ hτ0 hτS u v hm) =
      join S τ hτ0 hτS (L.compLeftContinuous ℝ (Icc (0 : ℝ) τ) u)
        (L.compLeftContinuous ℝ (Icc (0 : ℝ) (S-τ)) v) (congrArg L hm) := by
  apply ContinuousMap.ext
  intro t
  change L (if (t : ℝ) ≤ τ then u (projIcc 0 τ hτ0 t)
    else v (elapsedTime S τ (projIcc τ S hτS t))) =
      if (t : ℝ) ≤ τ then L (u (projIcc 0 τ hτ0 t))
        else L (v (elapsedTime S τ (projIcc τ S hτS t)))
  split <;> rfl

end EulerElapsedTimePathGluing

namespace EulerLpCylinderTranslation

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerElapsedTimePathGluing EulerParameterWordGevrey
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S)
  (u : C(Icc (0 : ℝ) τ, CylinderL2 P V)) (v : C(Icc (0 : ℝ) (S - τ), CylinderL2 P V))
  (hm : u ⟨τ, hτ0, le_rfl⟩ = v ⟨0, le_rfl, sub_nonneg.mpr hτS⟩)

theorem join_translation (a : LiftTangent) :
    pathTranslate P a (join S τ hτ0 hτS u v hm) =
      join S τ hτ0 hτS (pathTranslate P a u) (pathTranslate P a v)
        (congrArg (translate P a) hm) :=
  join_map S τ hτ0 hτS u v hm (translate P a).toContinuousLinearMap

variable (hu : ContDiff ℝ ∞ (fun a => pathTranslate P a u))
  (hv : ContDiff ℝ ∞ (fun a => pathTranslate P a v))

include hu hv in
theorem join_orbit_contDiff :
    ContDiff ℝ ∞ (fun a => pathTranslate P a (join S τ hτ0 hτS u v hm)) := by
  have he : (fun a => pathTranslate P a (join S τ hτ0 hτS u v hm)) =
      fun a => join S τ hτ0 hτS (pathTranslate P a u) (pathTranslate P a v)
        (congrArg (translate P a) hm) := funext (join_translation P S τ hτ0 hτS u v hm)
  rw [he]
  exact join_contDiff S τ hτ0 hτS (fun a => pathTranslate P a u) (fun a => pathTranslate P a v)
    hu hv (fun a => congrArg (translate P a) hm)

include hu hv in
theorem join_orbit_block {ι : Type*} [Fintype ι] (directions : ι → LiftTangent) (q n : ℕ) (a :
    LiftTangent) :
    block directions q (fun b => pathTranslate P b (join S τ hτ0 hτS u v hm)) n a ≤
      block directions q (fun b => pathTranslate P b u) n a +
        block directions q (fun b => pathTranslate P b v) n a := by
  have he : (fun b => pathTranslate P b (join S τ hτ0 hτS u v hm)) =
      fun b => join S τ hτ0 hτS (pathTranslate P b u) (pathTranslate P b v)
        (congrArg (translate P b) hm) := funext (join_translation P S τ hτ0 hτS u v hm)
  rw [he]
  exact join_block_bound S τ hτ0 hτS (fun b => pathTranslate P b u) (fun b => pathTranslate P b v)
    hu hv (fun b => congrArg (translate P b) hm) directions q n a

end EulerLpCylinderTranslation
