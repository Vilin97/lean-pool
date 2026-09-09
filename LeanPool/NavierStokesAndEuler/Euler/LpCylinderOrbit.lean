/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderTranslation
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Actual mixed translation orbits are smooth everywhere as soon as they are smooth at zero. -/

@[expose] public section


noncomputable section

namespace EulerLpCylinderTranslation

open Set MeasureTheory ContinuousLinearMap EulerLiftedGradientSpace
open scoped ContDiff

variable (period : ℝ) [Fact (0 < period)]
  {V K : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace K] [CompactSpace K]

omit [CompactSpace K] in
@[simp] theorem pathTranslate_zero (f : C(K, CylinderL2 period V)) : pathTranslate period 0 f = f :=
    by
  apply ContinuousMap.ext
  intro t
  exact translate_zero period (f t)

omit [CompactSpace K] in
/-- The true uniform-time mixed translations obey the group law. -/
theorem pathTranslate_add (a b : LiftTangent) (f : C(K, CylinderL2 period V)) :
    pathTranslate period a (pathTranslate period b f) = pathTranslate period (a+b) f := by
  apply ContinuousMap.ext
  intro t
  exact translate_add period a b (f t)

/-- Local smoothness at zero propagates to the whole genuine mixed translation orbit. -/
theorem pathOrbit_contDiff_of_zero (f : C(K, CylinderL2 period V))
    (hzero : ContDiffAt ℝ ∞ (fun a : LiftTangent => pathTranslate period a f) 0) :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a f) := by
  apply contDiff_iff_contDiffAt.2
  intro a
  have hshift : ContDiffAt ℝ ∞ (fun b : LiftTangent => pathTranslate period (b-a) f) a := by
    have hz : ContDiffAt ℝ ∞ (fun b : LiftTangent => pathTranslate period b f) (a-a) := by
      simpa only [sub_self] using hzero
    exact ContDiffAt.comp (f := fun b : LiftTangent => b-a) a hz
      (contDiffAt_id.sub contDiffAt_const)
  have h := (pathTranslate (K := K) (V := V) period a).contDiff.contDiffAt.comp a hshift
  have he : (fun b : LiftTangent => pathTranslate period a (pathTranslate period (b-a) f)) =
      (fun b : LiftTangent => pathTranslate period b f) := by
    funext b
    rw [pathTranslate_add]
    congr 1
    abel_nf
  change ContDiffAt ℝ ∞ (fun b : LiftTangent => pathTranslate period a (pathTranslate period (b-a)
      f)) a at h
  rwa [he] at h

end EulerLpCylinderTranslation
