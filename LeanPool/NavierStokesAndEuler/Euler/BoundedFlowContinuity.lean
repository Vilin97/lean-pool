/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.BoundedLipschitzFlow

@[expose] public section

/-! The actual bounded Lipschitz flow is jointly continuous in both times
and the initial point. Reversing its two time arguments gives its genuine
continuous inverse, so each fixed-time map is a homeomorphism. -/

noncomputable section

open Set Function Metric
open scoped Topology NNReal

namespace EulerBoundedLipschitzFlow.Data

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (V : EulerBoundedLipschitzFlow.Data E)

theorem flow_distance (s t s₀ t₀ : ℝ) (x x₀ : E) :
    dist (V.flow s t x) (V.flow s₀ t₀ x₀) ≤
      (dist x x₀ + V.speedBound*|s-s₀|) *
        Real.exp (V.lipschitzConstant*|t-s|) + V.speedBound*|t-t₀| := by
  have hs : dist x₀ (V.flow s₀ s x₀) ≤ V.speedBound*|s-s₀| := by
    simpa only [V.flow_initial, Real.dist_eq, abs_sub_comm s₀ s] using
      (V.flow_lipschitz_time s₀ x₀).dist_le_mul s₀ s
  have hx : dist x (V.flow s₀ s x₀) ≤ dist x x₀ + V.speedBound*|s-s₀| :=
    (dist_triangle x x₀ (V.flow s₀ s x₀)).trans (add_le_add (le_refl _) hs)
  have hspace := V.flow_distance_initial s t x (V.flow s₀ s x₀)
  rw [V.flow_cocycle] at hspace
  have ht : dist (V.flow s₀ t x₀) (V.flow s₀ t₀ x₀) ≤ V.speedBound*|t-t₀| := by
    simpa only [Real.dist_eq] using (V.flow_lipschitz_time s₀ x₀).dist_le_mul t t₀
  calc
    _ ≤ dist (V.flow s t x) (V.flow s₀ t x₀) + dist (V.flow s₀ t x₀) (V.flow s₀ t₀ x₀) :=
      dist_triangle _ _ _
    _ ≤ dist x (V.flow s₀ s x₀) * Real.exp (V.lipschitzConstant*|t-s|) +
        V.speedBound*|t-t₀| := add_le_add hspace ht
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_right hx (Real.exp_pos _).le) (le_refl _)

theorem flow_joint_continuous :
    Continuous (fun p : ℝ × (ℝ × E) => V.flow p.1 p.2.1 p.2.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p₀
  apply tendsto_iff_dist_tendsto_zero.2
  have hc : Continuous (fun p : ℝ × (ℝ × E) =>
      (dist p.2.2 p₀.2.2 + V.speedBound*|p.1-p₀.1|) *
        Real.exp (V.lipschitzConstant*|p.2.1-p.1|) + V.speedBound*|p.2.1-p₀.2.1|) := by
    fun_prop
  apply squeeze_zero
    (f := fun p : ℝ × (ℝ × E) => dist (V.flow p.1 p.2.1 p.2.2)
      (V.flow p₀.1 p₀.2.1 p₀.2.2))
    (g := fun p : ℝ × (ℝ × E) =>
      (dist p.2.2 p₀.2.2 + V.speedBound*|p.1-p₀.1|) *
        Real.exp (V.lipschitzConstant*|p.2.1-p.1|) + V.speedBound*|p.2.1-p₀.2.1|)
    (fun _ => dist_nonneg)
    (fun p => V.flow_distance p.1 p.2.1 p₀.1 p₀.2.1 p.2.2 p₀.2.2)
  simpa only [dist_self, sub_self, abs_zero, mul_zero, add_zero, zero_mul] using
    hc.tendsto p₀

def flowHomeomorph (s t : ℝ) : E ≃ₜ E where
  toFun := V.flow s t
  invFun := V.flow t s
  left_inv := V.flow_inverse s t
  right_inv := V.flow_inverse t s
  continuous_toFun := V.flow_joint_continuous.comp
    (continuous_const.prodMk (continuous_const.prodMk continuous_id))
  continuous_invFun := V.flow_joint_continuous.comp
    (continuous_const.prodMk (continuous_const.prodMk continuous_id))

def forward (t : ℝ) (x : E) : E := V.flow 0 t x

def backward (t : ℝ) (x : E) : E := V.flow t 0 x

@[simp] theorem backward_forward (t : ℝ) (x : E) :
    V.backward t (V.forward t x) = x := V.flow_inverse 0 t x

@[simp] theorem forward_backward (t : ℝ) (x : E) :
    V.forward t (V.backward t x) = x := V.flow_inverse t 0 x

@[simp] theorem forward_zero (x : E) : V.forward 0 x = x := V.flow_initial 0 x

@[simp] theorem backward_zero (x : E) : V.backward 0 x = x := V.flow_initial 0 x

theorem forward_hasDerivAt (t : ℝ) (x : E) :
    HasDerivAt (fun s => V.forward s x) (V.velocity t (V.forward t x)) t :=
  V.flow_hasDerivAt 0 t x

theorem forward_joint_continuous : Continuous (Function.uncurry V.forward) :=
  V.flow_joint_continuous.comp (continuous_const.prodMk continuous_id)

theorem backward_joint_continuous : Continuous (Function.uncurry V.backward) :=
  V.flow_joint_continuous.comp
    (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))

theorem forward_displacement (t : ℝ) (x : E) :
    dist (V.forward t x) x ≤ V.speedBound*|t| := by
  simpa only [forward, V.flow_initial, Real.dist_eq, sub_zero] using
    (V.flow_lipschitz_time 0 x).dist_le_mul t 0

end EulerBoundedLipschitzFlow.Data
