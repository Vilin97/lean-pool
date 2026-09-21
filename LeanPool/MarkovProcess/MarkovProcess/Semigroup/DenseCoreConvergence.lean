/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Convergence from a dense core

This module extends pointwise convergence of uniformly contractive continuous
linear maps from the range of a dense map to the whole ambient space.
-/

open Filter Topology

namespace MarkovProcess

/-- A family of continuous linear contractions that converges to the identity
on the range of a dense continuous linear map converges to the identity
everywhere. -/
theorem tendsto_of_denseRange_of_opNorm_le_one
    {E F ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {l : Filter ι} (T : ι → E →L[ℝ] E) (D : F →L[ℝ] E)
    (hT : ∀ i, ‖T i‖ ≤ 1) (hD : DenseRange D)
    (hcore : ∀ v, Tendsto (fun i ↦ T i (D v)) l (nhds (D v))) :
    ∀ f, Tendsto (fun i ↦ T i f) l (nhds f) := by
  intro f
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨v, hv⟩ := hD.exists_dist_lt f (div_pos hε (by norm_num : (0 : ℝ) < 3))
  have hv' : dist (D v) f < ε / 3 := by
    rw [dist_comm]
    exact hv
  have hcore_eventually : ∀ᶠ i in l, dist (T i (D v)) (D v) < ε / 3 :=
    (Metric.tendsto_nhds.mp (hcore v)) (ε / 3) (div_pos hε (by norm_num))
  filter_upwards [hcore_eventually] with i hi
  have hcontract : dist (T i f) (T i (D v)) ≤ dist f (D v) := by
    calc
      dist (T i f) (T i (D v)) ≤ ‖T i‖ * dist f (D v) := (T i).dist_le_opNorm f (D v)
      _ ≤ 1 * dist f (D v) :=
        mul_le_mul_of_nonneg_right (hT i) dist_nonneg
      _ = dist f (D v) := one_mul _
  calc
    dist (T i f) f ≤ dist (T i f) (T i (D v)) + dist (T i (D v)) f :=
      dist_triangle _ _ _
    _ ≤ dist (T i f) (T i (D v)) +
        (dist (T i (D v)) (D v) + dist (D v) f) :=
      add_le_add le_rfl (dist_triangle _ _ _)
    _ ≤ dist f (D v) + (dist (T i (D v)) (D v) + dist (D v) f) :=
      add_le_add hcontract le_rfl
    _ < ε / 3 + (ε / 3 + ε / 3) := by
      exact add_lt_add hv (add_lt_add hi hv')
    _ = ε := by ring

/-- Pointwise Cauchy convergence on the range of a dense continuous linear map
extends to the whole space for a sequence of contractions. -/
theorem cauchySeq_of_denseRange_of_opNorm_le_one
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : ℕ → E →L[ℝ] E) (D : F →L[ℝ] E)
    (hT : ∀ n, ‖T n‖ ≤ 1) (hD : DenseRange D)
    (hcore : ∀ v, CauchySeq (fun n ↦ T n (D v))) :
    ∀ x, CauchySeq (fun n ↦ T n x) := by
  intro x
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨v, hv⟩ := hD.exists_dist_lt x (div_pos hε (by norm_num : (0 : ℝ) < 3))
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (hcore v) (ε / 3)
    (div_pos hε (by norm_num))
  refine ⟨N, fun m hm n hn ↦ ?_⟩
  have hm_contract : dist (T m x) (T m (D v)) ≤ dist x (D v) := by
    calc
      dist (T m x) (T m (D v)) ≤ ‖T m‖ * dist x (D v) :=
        (T m).dist_le_opNorm x (D v)
      _ ≤ 1 * dist x (D v) := mul_le_mul_of_nonneg_right (hT m) dist_nonneg
      _ = dist x (D v) := one_mul _
  have hn_contract : dist (T n (D v)) (T n x) ≤ dist (D v) x := by
    calc
      dist (T n (D v)) (T n x) ≤ ‖T n‖ * dist (D v) x :=
        (T n).dist_le_opNorm (D v) x
      _ ≤ 1 * dist (D v) x := mul_le_mul_of_nonneg_right (hT n) dist_nonneg
      _ = dist (D v) x := one_mul _
  have hv' : dist (D v) x < ε / 3 := by
    rw [dist_comm]
    exact hv
  calc
    dist (T m x) (T n x) ≤
        dist (T m x) (T m (D v)) + dist (T m (D v)) (T n x) :=
      dist_triangle _ _ _
    _ ≤ dist (T m x) (T m (D v)) +
        (dist (T m (D v)) (T n (D v)) + dist (T n (D v)) (T n x)) :=
      add_le_add le_rfl (dist_triangle _ _ _)
    _ < ε / 3 + (ε / 3 + ε / 3) := by
      exact add_lt_add (lt_of_le_of_lt hm_contract hv)
        (add_lt_add (hN m hm n hn) (lt_of_le_of_lt hn_contract hv'))
    _ = ε := by ring

end MarkovProcess
