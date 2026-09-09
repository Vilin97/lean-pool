/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeField
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-! Pullback of a bounded field by identity plus a bounded displacement.
Uniform spatial Lipschitz control proves continuity in the genuine sup norm. -/

noncomputable section


open scoped BoundedContinuousFunction ContDiff NNReal

namespace EulerBoundedFieldPullback

variable {E V : Type*} [NormedAddCommGroup E] [NormedAddCommGroup V]

def pullback (A : E →ᵇ V) (d : E →ᵇ E) : E →ᵇ V :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => A (x+d x))
    (A.continuous.comp (continuous_id.add d.continuous)) ‖A‖
    (fun x => A.norm_coe_le_norm (x+d x))

@[simp] theorem pullback_apply (A : E →ᵇ V) (d : E →ᵇ E) (x : E) :
    pullback A d x = A (x+d x) := rfl

theorem pullback_norm (A : E →ᵇ V) (d : E →ᵇ E) :
    ‖pullback A d‖ ≤ ‖A‖ :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (norm_nonneg A) _

theorem pullback_sub_norm (A B : E →ᵇ V) (d e : E →ᵇ E)
    (L : ℝ≥0) (hL : LipschitzWith L A) :
    ‖pullback A d - pullback B e‖ ≤ ‖A-B‖ + L * ‖d-e‖ := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).2
  intro x
  change ‖A (x+d x)-B (x+e x)‖ ≤ _
  calc
    _ ≤ ‖A (x+d x)-A (x+e x)‖ + ‖A (x+e x)-B (x+e x)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ L*‖d-e‖ + ‖A-B‖ := by
      apply add_le_add
      · have hh := hL.dist_le_mul (x+d x) (x+e x)
        rw [dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub] at hh
        exact hh.trans (mul_le_mul_of_nonneg_left ((d-e).norm_coe_le_norm x) L.coe_nonneg)
      · exact (A-B).norm_coe_le_norm (x+e x)
    _ = _ := add_comm _ _

variable {K : Type*} [TopologicalSpace K]

theorem continuous_pullback (A : C(K,E →ᵇ V)) (d : C(K,E →ᵇ E))
    (L : ℝ≥0) (hL : ∀ t, LipschitzWith L (A t)) :
    Continuous (fun t => pullback (A t) (d t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun s => norm_nonneg _)
    (fun s => pullback_sub_norm (A s) (A t) (d s) (d t) L (hL s))
  have hzero : Filter.Tendsto
      (fun s => ‖A s-A t‖ + (L : ℝ)*‖d s-d t‖) (nhds t) (nhds 0) := by
    have hc : Continuous (fun s => ‖A s-A t‖ + (L : ℝ)*‖d s-d t‖) :=
      ((A.continuous.sub continuous_const).norm).add
        (continuous_const.mul ((d.continuous.sub continuous_const).norm))
    simpa only [sub_self, norm_zero, mul_zero, add_zero] using hc.tendsto t
  exact hzero

def pathPullback (A : C(K,E →ᵇ V)) (d : C(K,E →ᵇ E))
    (L : ℝ≥0) (hL : ∀ t, LipschitzWith L (A t)) : C(K,E →ᵇ V) :=
  ⟨fun t => pullback (A t) (d t), continuous_pullback A d L hL⟩

@[simp] theorem pathPullback_apply (A : C(K,E →ᵇ V)) (d : C(K,E →ᵇ E))
    (L : ℝ≥0) (hL : ∀ t, LipschitzWith L (A t)) (t : K) (x : E) :
    pathPullback A d L hL t x = A t (x+d t x) := rfl

end EulerBoundedFieldPullback

namespace SmoothTimeField

universe u

variable {K E V : Type u} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

private local instance (n : ℕ) : NormedAddCommGroup (E [×n]→L[ℝ] V) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (E [×n]→L[ℝ] V) := inferInstance
private local instance (n : ℕ) : NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] V)) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] V)) := inferInstance

theorem jet_lipschitz (A : SmoothTimeField K E V) (n : ℕ) (t : K) :
    LipschitzWith ‖A.jet (n+1)‖₊ (A.jet n t) := by
  have he : (A.jet n t : E → E [×n]→L[ℝ] V) =
      iteratedFDeriv ℝ n (A.field t : E → V) := funext (A.jet_eq n t)
  rw [he]
  apply lipschitzWith_of_nnnorm_fderiv_le
    (((A.smooth t).iteratedFDeriv_right (m := ∞) (by simp)).differentiable (by simp))
  intro x
  change ‖fderiv ℝ (iteratedFDeriv ℝ n (A.field t : E → V)) x‖ ≤ ‖A.jet (n+1)‖
  rw [norm_fderiv_iteratedFDeriv, ← A.jet_eq]
  exact ((A.jet (n+1) t).norm_coe_le_norm x).trans ((A.jet (n+1)).norm_coe_le_norm t)

end SmoothTimeField
