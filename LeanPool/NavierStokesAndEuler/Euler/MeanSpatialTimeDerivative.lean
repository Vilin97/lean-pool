/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanSpatialEvaluation

@[expose] public section

/-! Genuine time derivatives pass through the reconstructed ordinary spatial representatives. -/

noncomputable section


namespace EulerMeanSmoothRepresentative

open MeasureTheory EulerSmoothLimit EulerMeanSolenoidal EulerMeanOrdinaryLift
  EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevPointEvaluation
open scoped ContDiff

private local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

private theorem hasDerivAt_submodule_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Submodule ℝ E) (f : ℝ → S) (v : S) (t : ℝ) :
    HasDerivAt f v t ↔ HasDerivAt (fun s => (f s : E)) (v : E) t := by
  rw [hasDerivAt_iff_tendsto, hasDerivAt_iff_tendsto]
  rfl

private theorem hasDerivWithinAt_submodule_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Submodule ℝ E) (f : ℝ → S) (v : S) (U : Set ℝ) (t : ℝ) :
    HasDerivWithinAt f v U t ↔ HasDerivWithinAt (fun s => (f s : E)) (v : E) U t := by
  rw [hasDerivWithinAt_iff_tendsto, hasDerivWithinAt_iff_tendsto]
  rfl

/-- The derivative of the complete Sobolev array is fixed by the actual finite L² derivative tensors. -/
theorem ordinarySobolev_hasDerivAt (q : ℕ) (u : ℝ → EulerMeanSolenoidal.L2)
    (hu : ∀ t, SmoothOrbit (u t)) (v : EulerMeanSolenoidal.L2) (hv : SmoothOrbit v) (t : ℝ)
    (hjet : ∀ n ≤ q, HasDerivAt
      (fun s => iteratedFDeriv ℝ n (fun a : Space => EulerMeanSolenoidal.translation a (u s)) 0)
      (iteratedFDeriv ℝ n (fun a : Space => EulerMeanSolenoidal.translation a v) 0) t) :
    HasDerivAt (fun s => ordinarySobolev q (u s) (hu s)) (ordinarySobolev q v hv) t := by
  apply (hasDerivAt_submodule_iff (sobolevSubspace 1 q).toSubmodule _ _ _).mpr
  apply hasDerivAt_pi.mpr
  intro w
  change HasDerivAt (fun s => (ordinarySobolev q (u s) (hu s)).val w)
    ((ordinarySobolev q v hv).val w) t
  simp_rw [ordinarySobolev_coordinate]
  let L := ordinaryLift.toContinuousLinearMap.comp
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin w.1.val => Space) EulerMeanSolenoidal.L2
      (coordinateTuple w.2))
  exact L.hasFDerivAt.comp_hasDerivAt t (hjet w.1.val (Nat.le_of_lt_succ w.1.isLt))

theorem ordinarySobolev_hasDerivWithinAt (q : ℕ) (u : ℝ → EulerMeanSolenoidal.L2)
    (hu : ∀ t, SmoothOrbit (u t)) (v : EulerMeanSolenoidal.L2) (hv : SmoothOrbit v)
    (U : Set ℝ) (t : ℝ)
    (hjet : ∀ n ≤ q, HasDerivWithinAt
      (fun s => iteratedFDeriv ℝ n (fun a : Space => EulerMeanSolenoidal.translation a (u s)) 0)
      (iteratedFDeriv ℝ n (fun a : Space => EulerMeanSolenoidal.translation a v) 0) U t) :
    HasDerivWithinAt (fun s => ordinarySobolev q (u s) (hu s)) (ordinarySobolev q v hv) U t := by
  apply (hasDerivWithinAt_submodule_iff (sobolevSubspace 1 q).toSubmodule _ _ _ _).mpr
  apply hasDerivWithinAt_pi.mpr
  intro w
  change HasDerivWithinAt (fun s => (ordinarySobolev q (u s) (hu s)).val w)
    ((ordinarySobolev q v hv).val w) U t
  simp_rw [ordinarySobolev_coordinate]
  let L := ordinaryLift.toContinuousLinearMap.comp
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin w.1.val => Space) EulerMeanSolenoidal.L2
      (coordinateTuple w.2))
  exact L.hasFDerivAt.comp_hasDerivWithinAt t (hjet w.1.val (Nat.le_of_lt_succ w.1.isLt))

/-- The actual pointwise time derivative equals the smooth representative of the L² derivative. -/
theorem representative_hasDerivAt (u : ℝ → EulerMeanSolenoidal.L2) (hu : ∀ t, SmoothOrbit (u t))
    (v : EulerMeanSolenoidal.L2) (hv : SmoothOrbit v) (t : ℝ)
    (hjet : ∀ n ≤ 3, HasDerivAt
      (fun s => iteratedFDeriv ℝ n (fun a : Space => EulerMeanSolenoidal.translation a (u s)) 0)
      (iteratedFDeriv ℝ n (fun a : Space => EulerMeanSolenoidal.translation a v) 0) t)
    (x : Space) :
    HasDerivAt (fun s => representative (u s) (hu s) x) (representative v hv x) t := by
  have H := (pointEvaluation 1 (x, 0)).hasFDerivAt.comp_hasDerivAt t
    (ordinarySobolev_hasDerivAt 3 u hu v hv t hjet)
  simpa only [Function.comp_def, pointEvaluation_ordinary] using H

theorem representative_hasDerivWithinAt (u : ℝ → EulerMeanSolenoidal.L2)
    (hu : ∀ t, SmoothOrbit (u t)) (v : EulerMeanSolenoidal.L2) (hv : SmoothOrbit v)
    (U : Set ℝ) (t : ℝ)
    (hjet : ∀ n ≤ 3, HasDerivWithinAt
      (fun s => iteratedFDeriv ℝ n (fun a : Space => EulerMeanSolenoidal.translation a (u s)) 0)
      (iteratedFDeriv ℝ n (fun a : Space => EulerMeanSolenoidal.translation a v) 0) U t)
    (x : Space) :
    HasDerivWithinAt (fun s => representative (u s) (hu s) x) (representative v hv x) U t := by
  have H := (pointEvaluation 1 (x, 0)).hasFDerivAt.comp_hasDerivWithinAt t
    (ordinarySobolev_hasDerivWithinAt 3 u hu v hv U t hjet)
  simpa only [Function.comp_def, pointEvaluation_ordinary] using H

end EulerMeanSmoothRepresentative
