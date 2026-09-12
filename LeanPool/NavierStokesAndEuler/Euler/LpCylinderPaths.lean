/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderTranslation
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevBlocks
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevLinear
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Continuous paths and actual mixed translations in supported cylinder L²

Inclusion and measurable-set projection act on actual continuous L² paths.
Projected translations form globally defined parameter families. Whenever a
translated compact support lies in the target region, the projection is the
identity, so these families are the true mixed translations there.
-/

@[expose] public section


noncomputable section

namespace EulerLpCylinderPaths

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpSupportedSubspace EulerLpCylinderTranslation EulerLpSupportedTranslation
      EulerParameterWordGevrey
open scoped ContDiff

variable (period : ℝ) [Fact (0 < period)]

/-- Supported: an abbreviation for `supportedSpace (V := V) (liftMeasure period) (spatialSet
period S) (spatialSet_measurable period S hS)`. -/
abbrev Supported (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (S : Set Space) (hS : MeasurableSet S) :=
  supportedSpace (V := V) (liftMeasure period) (spatialSet period S) (spatialSet_measurable period
      S hS)

variable {K V : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (S : Set Space) (hS : MeasurableSet S)

/-- Cache the standard `NormedAddCommGroup (CylinderL2 period V)` instance to shorten typeclass
synthesis. -/
local instance instLpCylinderPaths1 : NormedAddCommGroup (CylinderL2 period V) := inferInstance
/-- Cache the standard `NormedSpace ℝ (CylinderL2 period V)` instance to shorten typeclass
synthesis. -/
local instance instLpCylinderPaths2 : NormedSpace ℝ (CylinderL2 period V) := inferInstance
/-- Cache the standard `NormedAddCommGroup (Supported period V S hS)` instance to shorten
typeclass synthesis. -/
local instance instLpCylinderPaths3 : NormedAddCommGroup (Supported period V S hS) := inferInstance
/-- Cache the standard `NormedSpace ℝ (Supported period V S hS)` instance to shorten typeclass
synthesis. -/
local instance instLpCylinderPaths4 : NormedSpace ℝ (Supported period V S hS) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(K,CylinderL2 period V)` instance to shorten
typeclass synthesis. -/
local instance instLpCylinderPaths5 : NormedAddCommGroup C(K,CylinderL2 period V) := inferInstance
/-- Cache the standard `NormedSpace ℝ C(K,CylinderL2 period V)` instance to shorten typeclass
synthesis. -/
local instance instLpCylinderPaths6 : NormedSpace ℝ C(K,CylinderL2 period V) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(K,Supported period V S hS)` instance to shorten
typeclass synthesis. -/
local instance instLpCylinderPaths7 : NormedAddCommGroup C(K,Supported period V S hS) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(K,Supported period V S hS)` instance to shorten
typeclass synthesis. -/
local instance instLpCylinderPaths8 : NormedSpace ℝ C(K,Supported period V S hS) := inferInstance

/-- Inclusion of a supported path into the genuine ordinary L² path space. -/
def includePath : C(K,Supported period V S hS) →L[ℝ] C(K,CylinderL2 period V) :=
  (Supported period V S hS).subtypeL.compLeftContinuous ℝ K

/-- Projection of each ordinary L² value to the fixed supported subspace. -/
def projectPath : C(K,CylinderL2 period V) →L[ℝ] C(K,Supported period V S hS) :=
  (projection (V := V) (liftMeasure period) (spatialSet period S)
    (spatialSet_measurable period S hS)).compLeftContinuous ℝ K

omit [CompactSpace K] in
@[simp] theorem includePath_apply (f : C(K, Supported period V S hS)) (t : K) :
    includePath period S hS f t = (f t : CylinderL2 period V) := rfl

omit [CompactSpace K] in
@[simp] theorem projectPath_apply (f : C(K, CylinderL2 period V)) (t : K) :
    projectPath period S hS f t = projection (liftMeasure period) (spatialSet period S)
        (spatialSet_measurable period S hS) (f t) := rfl

/-- Time-path inclusion is a contraction (indeed an isometry). -/
theorem includePath_norm : ‖includePath (K := K) (V := V) period S hS‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro f
  rw [one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).2
  intro t
  exact f.norm_coe_le_norm t

/-- Supported projection is a contraction also in the uniform time norm. -/
theorem projectPath_norm : ‖projectPath (K := K) (V := V) period S hS‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro f
  rw [one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).2
  intro t
  exact (cutoff_norm (liftMeasure period) (spatialSet period S) (spatialSet_measurable period S hS)
      (f t)).trans (f.norm_coe_le_norm t)

omit [CompactSpace K] in
/-- Projecting an already supported continuous path fixes it. -/
theorem project_include (f : C(K, Supported period V S hS)) :
    projectPath period S hS (includePath period S hS f) = f := by
  apply ContinuousMap.ext
  intro t
  exact projection_supported (liftMeasure period) (spatialSet period S) (spatialSet_measurable
      period S hS) (f t)

/-- A globally defined actual mixed translation followed by supported projection. -/
def translatedData (u : CylinderL2 period V) (a : LiftTangent) : Supported period V S hS :=
  projection (liftMeasure period) (spatialSet period S) (spatialSet_measurable period S hS)
      (translate period a u)

/-- The corresponding globally defined family of actual continuous forcing paths. -/
def translatedForcing (f : C(K, CylinderL2 period V)) (a : LiftTangent) :
    C(K,Supported period V S hS) :=
  projectPath period S hS (pathTranslate period a f)

/-- On the allowed translation neighborhood, projected data are exact translations. -/
theorem translatedData_eq_intoLarger (S₀ : Set Space) (hS₀ : MeasurableSet S₀)
    (u : Supported period V S₀ hS₀) (a : LiftTangent)
    (ha : shiftedSet a.1 S₀ ⊆ S) :
    translatedData period S hS (u : CylinderL2 period V) a = EulerLpCylinderTranslation.intoLarger
        period a S₀ S hS₀ hS ha u := by
  exact projection_supported (liftMeasure period) (spatialSet period S) (spatialSet_measurable
      period S hS) (EulerLpCylinderTranslation.intoLarger period a S₀ S hS₀ hS ha u)

omit [CompactSpace K] in
/-- The same exact identity holds for whole continuous forcing paths. -/
theorem translatedForcing_eq_intoLarger (S₀ : Set Space) (hS₀ : MeasurableSet S₀)
    (f : C(K, Supported period V S₀ hS₀)) (a : LiftTangent)
    (ha : shiftedSet a.1 S₀ ⊆ S) :
    translatedForcing period S hS (includePath period S₀ hS₀ f) a =
      (EulerLpCylinderTranslation.intoLarger (V := V) period a S₀ S hS₀ hS
          ha).toContinuousLinearMap.compLeftContinuous ℝ K f := by
  apply ContinuousMap.ext
  intro t
  exact translatedData_eq_intoLarger period S hS S₀ hS₀ (f t) a ha

/-- Smoothness is inherited from the true ordinary L² translation orbit. -/
theorem translatedData_contDiff (u : CylinderL2 period V)
    (hu : ContDiff ℝ ∞ (fun a : LiftTangent => translate period a u)) :
    ContDiff ℝ ∞ (translatedData period S hS u) := by
  exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞) (E := CylinderL2 period V)
    (F := Supported period V S hS) (projection (liftMeasure period) (spatialSet period S)
        (spatialSet_measurable period S hS))).comp hu

/-- The supported parameter family has no larger actual derivative norm. -/
theorem norm_iteratedFDeriv_translatedData_le (u : CylinderL2 period V)
    (hu : ContDiff ℝ ∞ (fun a : LiftTangent => translate period a u)) (n : ℕ) (a : LiftTangent) :
    ‖iteratedFDeriv ℝ n (translatedData period S hS u) a‖ ≤
      ‖iteratedFDeriv ℝ n (fun b : LiftTangent => translate period b u) a‖ := by
  have h := (projection (V := V) (liftMeasure period) (spatialSet period S) (spatialSet_measurable
      period S hS)).norm_iteratedFDeriv_comp_left
    (hu.contDiffAt (x := a)) (n := n) (by simp)
  exact h.trans (by simpa only [one_mul] using
    mul_le_mul_of_nonneg_right (projection_norm (V := V) (liftMeasure period) (spatialSet period S)
        (spatialSet_measurable period S hS)) (norm_nonneg _))

/-- Uniform-time orbit smoothness is preserved by the fixed support projection. -/
theorem translatedForcing_contDiff (f : C(K, CylinderL2 period V))
    (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a f)) :
    ContDiff ℝ ∞ (translatedForcing period S hS f) := by
  exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞) (E := C(K,CylinderL2 period V))
    (F := C(K,Supported period V S hS)) (projectPath period S hS)).comp hf

/-- The projected forcing jets are bounded by the genuine uniform-time spatial orbit jets. -/
theorem norm_iteratedFDeriv_translatedForcing_le (f : C(K, CylinderL2 period V))
    (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a f))
    (n : ℕ) (a : LiftTangent) :
    ‖iteratedFDeriv ℝ n (translatedForcing period S hS f) a‖ ≤
      ‖iteratedFDeriv ℝ n (fun b : LiftTangent => pathTranslate period b f) a‖ := by
  have h := ContinuousLinearMap.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) (E := LiftTangent)
    (F := C(K,CylinderL2 period V)) (G := C(K,Supported period V S hS))
    (projectPath (K := K) (V := V) period S hS) (hf.contDiffAt (x := a)) (n := n) (by simp)
  exact h.trans (by simpa only [one_mul] using
    mul_le_mul_of_nonneg_right (projectPath_norm (K := K) (V := V) period S hS) (norm_nonneg _))


variable {ι : Type*} [Fintype ι] (directions : ι → LiftTangent) (q : ℕ)

/-- The true mixed initial-data derivative blocks are unchanged by support projection. -/
theorem translatedData_block_le (u : CylinderL2 period V)
    (hu : ContDiff ℝ ∞ (fun a : LiftTangent => translate period a u)) (n : ℕ) (a : LiftTangent) :
    block directions q (translatedData period S hS u) n a ≤
      block directions q (fun b : LiftTangent => translate period b u) n a := by
  have h := block_comp_clm_le directions q
    (projection (V := V) (liftMeasure period) (spatialSet period S) (spatialSet_measurable period S
        hS))
    (fun b : LiftTangent => translate period b u) hu n a
  exact h.trans ((mul_le_mul_of_nonneg_right
    (projection_norm (V := V) (liftMeasure period) (spatialSet period S) (spatialSet_measurable
        period S hS))
    (block_nonneg directions q _ n a)).trans_eq (one_mul _))

/-- The true mixed forcing derivative blocks are unchanged by support projection. -/
theorem translatedForcing_block_le (f : C(K, CylinderL2 period V))
    (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a f))
    (n : ℕ) (a : LiftTangent) :
    block directions q (translatedForcing period S hS f) n a ≤
      block directions q (fun b : LiftTangent => pathTranslate period b f) n a := by
  have h := block_comp_clm_le directions q (projectPath (V := V) period S hS)
    (fun b : LiftTangent => pathTranslate period b f) hf n a
  exact h.trans ((mul_le_mul_of_nonneg_right
    (projectPath_norm (K := K) (V := V) period S hS)
    (block_nonneg directions q _ n a)).trans_eq (one_mul _))

/-- Inclusion transfers the same fixed-Hq block to actual cylinder L². -/
theorem includePath_block_le (u : LiftTangent → C(K, Supported period V S hS))
    (hu : ContDiff ℝ ∞ u) (n : ℕ) (a : LiftTangent) :
    block directions q (fun b => includePath period S hS (u b)) n a ≤ block directions q u n a := by
  have h := block_comp_clm_le directions q (includePath (V := V) period S hS) u hu n a
  exact h.trans ((mul_le_mul_of_nonneg_right
    (includePath_norm (K := K) (V := V) period S hS)
    (block_nonneg directions q u n a)).trans_eq (one_mul _))

end EulerLpCylinderPaths
