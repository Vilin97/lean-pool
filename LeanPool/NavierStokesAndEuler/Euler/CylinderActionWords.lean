/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.IsometricActionWords
public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderOrbit
public import LeanPool.NavierStokesAndEuler.Euler.CylinderTranslationAdjoint
public import LeanPool.NavierStokesAndEuler.Euler.MeanPathLpBlocks

@[expose] public section

/-! Exact mixed-word invariance on cylinder L² and its time-function spaces. -/

noncomputable section

namespace EulerLpCylinderTranslation

open Set MeasureTheory ContinuousLinearMap EulerLiftedGradientSpace
  EulerTimeLp EulerTimeLpBoundedMap EulerParameterWordGevrey
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

section Path

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

theorem pathTranslate_norm_map (a : LiftTangent) (f : C(K,CylinderL2 P V)) :
    ‖pathTranslate P a f‖ = ‖f‖ := by
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (norm_nonneg f)).2
    intro t
    change ‖translate P a (f t)‖ ≤ ‖f‖
    rw [LinearIsometry.norm_map]
    exact f.norm_coe_le_norm t
  · apply (ContinuousMap.norm_le _ (norm_nonneg (pathTranslate P a f))).2
    intro t
    rw [← (translate P a).norm_map (f t)]
    exact (pathTranslate P a f).norm_coe_le_norm t

def pathTranslateIsometry (a : LiftTangent) : C(K,CylinderL2 P V) →ₗᵢ[ℝ] C(K,CylinderL2 P V) where
  toLinearMap := (pathTranslate P a).toLinearMap
  norm_map' := pathTranslate_norm_map P a

theorem path_block_constant {ι : Type*} [Fintype ι] (directions : ι → LiftTangent) (q : ℕ)
    (f : C(K,CylinderL2 P V)) (hf : ContDiff ℝ ∞ (fun a => pathTranslate P a f)) (n : ℕ) (a :
      LiftTangent) :
    block directions q (fun b => pathTranslate P b f) n a =
      block directions q (fun b => pathTranslate P b f) n 0 :=
  EulerIsometricAction.block_orbit_constant (X := LiftTangent)
    (E := C(K,CylinderL2 P V)) (ι := ι) (pathTranslateIsometry (K := K) (V := V) P)
    (fun a b u => pathTranslate_add P a b u) (fun u => pathTranslate_zero P u) directions q f hf n a

end Path

def timeTranslateIsometry (T : ℝ) (a : LiftTangent) :
    TimeLp T (CylinderL2 P V) →ₗᵢ[ℝ] TimeLp T (CylinderL2 P V) :=
  timeLiftIsometry T (translate P a)

theorem timeTranslateIsometry_add (T : ℝ) (a b : LiftTangent) (f : TimeLp T (CylinderL2 P V)) :
    timeTranslateIsometry P T a (timeTranslateIsometry P T b f) = timeTranslateIsometry P T (a+b) f
      := by
  apply Lp.ext
  filter_upwards [timeLift_ae T (translate P a).toContinuousLinearMap (timeTranslateIsometry P T b
    f),
    timeLift_ae T (translate P b).toContinuousLinearMap f,
    timeLift_ae T (translate P (a+b)).toContinuousLinearMap f] with t ha hb hab
  change timeTranslateIsometry P T a (timeTranslateIsometry P T b f) t = _ at ha
  change timeTranslateIsometry P T b f t = _ at hb
  change timeTranslateIsometry P T (a+b) f t = _ at hab
  rw [ha,hb,hab]
  exact translate_add P a b (f t)

theorem timeTranslateIsometry_zero (T : ℝ) (f : TimeLp T (CylinderL2 P V)) :
    timeTranslateIsometry P T 0 f = f := by
  apply Lp.ext
  filter_upwards [timeLift_ae T (translate P 0).toContinuousLinearMap f] with t ht
  change timeTranslateIsometry P T 0 f t = _ at ht
  rw [ht]
  exact translate_zero P (f t)

theorem time_block_constant {ι : Type*} [Fintype ι] (directions : ι → LiftTangent) (q : ℕ)
    (T : ℝ) (f : TimeLp T (CylinderL2 P V))
    (hf : ContDiff ℝ ∞ (fun a => timeLift T (translate P a).toContinuousLinearMap f))
    (n : ℕ) (a : LiftTangent) :
    block directions q (fun b => timeLift T (translate P b).toContinuousLinearMap f) n a =
      block directions q (fun b => timeLift T (translate P b).toContinuousLinearMap f) n 0 :=
  EulerIsometricAction.block_orbit_constant (X := LiftTangent)
    (E := TimeLp T (CylinderL2 P V)) (ι := ι) (timeTranslateIsometry (V := V) P T)
    (fun a b u => timeTranslateIsometry_add P T a b u)
    (fun u => timeTranslateIsometry_zero P T u) directions q f hf n a

theorem pathLp_orbit_contDiff (T : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T,CylinderL2 P V))
    (hf : ContDiff ℝ ∞ (fun a => pathTranslate P a f)) :
    ContDiff ℝ ∞ (fun a => timeLift T (translate P a).toContinuousLinearMap (pathLp T hT f)) := by
  have he : (fun a => timeLift T (translate P a).toContinuousLinearMap (pathLp T hT f)) =
      (pathLpOperator T hT) ∘ (fun a => pathTranslate P a f) := by
    funext a
    convert (pathLp_timeLift T hT (translate P a).toContinuousLinearMap f).symm using 1
    rfl
  rw [he]
  exact (pathLpOperator (E := CylinderL2 P V) T hT).contDiff.comp hf

/-- The actual Ctime-to-time-L² inclusion preserves all mixed word blocks
with exactly the square-root time length factor. -/
theorem pathLp_block_le {ι : Type*} [Fintype ι] (directions : ι → LiftTangent) (q : ℕ)
    (T : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T,CylinderL2 P V))
    (hf : ContDiff ℝ ∞ (fun a => pathTranslate P a f)) (n : ℕ) (a : LiftTangent) :
    block directions q (fun b => timeLift T (translate P b).toContinuousLinearMap (pathLp T hT f))
      n a ≤
      Real.sqrt T*block directions q (fun b => pathTranslate P b f) n a := by
  have he : (fun b => timeLift T (translate P b).toContinuousLinearMap (pathLp T hT f)) =
      (pathLpOperator T hT) ∘ (fun b => pathTranslate P b f) := by
    funext b
    convert (pathLp_timeLift T hT (translate P b).toContinuousLinearMap f).symm using 1
    rfl
  rw [he]
  exact (block_comp_clm_le directions q (pathLpOperator (E := CylinderL2 P V) T hT) _ hf n a).trans
    (mul_le_mul_of_nonneg_right
      (EulerMeanTimeContinuousTranslation.pathLpOperator_norm_sqrt T hT)
      (block_nonneg directions q _ n a))

end EulerLpCylinderTranslation
