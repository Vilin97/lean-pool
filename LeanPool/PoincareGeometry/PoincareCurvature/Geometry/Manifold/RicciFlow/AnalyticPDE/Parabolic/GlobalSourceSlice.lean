/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.BanachSpace

/-!
# Time slices of global parabolic Holder data

A global parabolic `C^{0,α}` Banach element determines, at every time, a
bounded continuous spatial function.  This file packages that slice and proves
that the resulting path is continuous in the uniform norm.  These are the
source objects consumed by the Euclidean Duhamel solution operator.
-/

@[expose] public noncomputable section

open Real Set Filter Metric
open scoped Topology NNReal

namespace RicciFlow
namespace AnalyticPDE

variable {X E : Type*} [PseudoMetricSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

namespace ParabolicC0AlphaBanach

variable {α : ℝ}

/-- The evaluation function of a global parabolic Holder class has its full
Banach norm as a simultaneous sup and Holder constant. -/
theorem global_eval_parabolicHolderWith
    (q : ParabolicC0AlphaBanach X E α (Set.univ : Set (ℝ × X))) :
    ParabolicHolderWith ‖q‖ α
      (fun z => evalCLM z (Set.mem_univ z) q) Set.univ := by
  obtain ⟨v, rfl⟩ := mk_surjective q
  intro p _hp z _hz
  have h := norm_sub_le_parabolicC0AlphaNorm_mul
      (ParabolicC0AlphaSpace.toSubmodule v).2.holderOn
      (Set.mem_univ p) (Set.mem_univ z)
  rw [norm_mk]
  convert h using 1 <;> rfl

/-- A fixed-time slice of a global parabolic Holder class, packaged as a
bounded continuous spatial function. -/
def globalTimeSlice
    (hα : 0 < α)
    (q : ParabolicC0AlphaBanach X E α (Set.univ : Set (ℝ × X))) (t : ℝ) :
    BoundedContinuousFunction X E :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => evalCLM (t, x) (Set.mem_univ (t, x)) q)
    (by
      obtain ⟨v, rfl⟩ := mk_surjective q
      change Continuous (fun x => ParabolicC0AlphaSpace.toFun v (t, x))
      have hv : Continuous (ParabolicC0AlphaSpace.toFun v) :=
        continuousOn_univ.mp
          ((ParabolicC0AlphaSpace.toSubmodule v).2.continuousOn
            hα)
      exact hv.comp (continuous_const.prodMk continuous_id))
    ‖q‖
    (fun x => by
      obtain ⟨v, rfl⟩ := mk_surjective q
      rw [evalCLM_mk_apply, norm_mk]
      have h := norm_le_parabolicC0AlphaNorm
        (α := α)
        (ParabolicC0AlphaSpace.toSubmodule v).2.boundedOn
        (Set.mem_univ (t, x))
      convert h using 1 <;> rfl)

@[simp]
theorem globalTimeSlice_apply
    (hα : 0 < α)
    (q : ParabolicC0AlphaBanach X E α (Set.univ : Set (ℝ × X)))
    (t : ℝ) (x : X) :
    globalTimeSlice hα q t x = evalCLM (t, x) (Set.mem_univ (t, x)) q :=
  rfl

theorem norm_globalTimeSlice_apply_le
    (hα : 0 < α)
    (q : ParabolicC0AlphaBanach X E α (Set.univ : Set (ℝ × X)))
    (t : ℝ) (x : X) :
    ‖globalTimeSlice hα q t x‖ ≤ ‖q‖ := by
  obtain ⟨v, rfl⟩ := mk_surjective q
  rw [globalTimeSlice_apply, evalCLM_mk_apply, norm_mk]
  exact norm_le_parabolicC0AlphaNorm
    (ParabolicC0AlphaSpace.toSubmodule v).2.boundedOn (Set.mem_univ (t, x))

theorem norm_globalTimeSlice_le
    (hα : 0 < α)
    (q : ParabolicC0AlphaBanach X E α (Set.univ : Set (ℝ × X))) (t : ℝ) :
    ‖globalTimeSlice hα q t‖ ≤ ‖q‖ := by
  exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
    (globalTimeSlice hα q t).continuous (norm_nonneg q)
    (norm_globalTimeSlice_apply_le hα q t)

@[simp]
theorem globalTimeSlice_zero (hα : 0 < α) (t : ℝ) :
    globalTimeSlice hα
        (0 : ParabolicC0AlphaBanach X E α (Set.univ : Set (ℝ × X))) t = 0 := by
  ext x
  simp [globalTimeSlice_apply]

@[simp]
theorem globalTimeSlice_add (hα : 0 < α)
    (q r : ParabolicC0AlphaBanach X E α (Set.univ : Set (ℝ × X))) (t : ℝ) :
    globalTimeSlice hα (q + r) t = globalTimeSlice hα q t + globalTimeSlice hα r t := by
  ext x
  simp [globalTimeSlice_apply]

@[simp]
theorem globalTimeSlice_smul (hα : 0 < α) (c : ℝ)
    (q : ParabolicC0AlphaBanach X E α (Set.univ : Set (ℝ × X))) (t : ℝ) :
    globalTimeSlice hα (c • q) t = c • globalTimeSlice hα q t := by
  ext x
  simp [globalTimeSlice_apply]

/-- Uniform distance between two time slices is controlled by the parabolic
Holder modulus of the original class. -/
theorem dist_globalTimeSlice_le
    (hα : 0 < α)
    (q : ParabolicC0AlphaBanach X E α (Set.univ : Set (ℝ × X)))
    (t τ : ℝ) :
    dist (globalTimeSlice hα q t) (globalTimeSlice hα q τ) ≤
      ‖q‖ * |t - τ| ^ (α / 2) := by
  rw [BoundedContinuousFunction.dist_le
    (mul_nonneg (norm_nonneg q) (Real.rpow_nonneg (abs_nonneg _) _))]
  intro x
  simp only [globalTimeSlice_apply, dist_eq_norm]
  exact q.global_eval_parabolicHolderWith.time_slice_half_exponent
    (Set.mem_univ (t, x)) (Set.mem_univ (τ, x))

/-- For positive exponent, the global parabolic Holder class is a continuous
path of bounded continuous spatial functions. -/
theorem continuous_globalTimeSlice (hα : 0 < α)
    (q : ParabolicC0AlphaBanach X E α (Set.univ : Set (ℝ × X))) :
    Continuous (globalTimeSlice hα q) := by
  rw [continuous_iff_continuousAt]
  intro t
  rw [Metric.continuousAt_iff]
  intro ε hε
  by_cases hq0 : ‖q‖ = 0
  · refine ⟨1, zero_lt_one, fun {τ} _hτ => ?_⟩
    have hdist := dist_globalTimeSlice_le hα q τ t
    rw [hq0, zero_mul] at hdist
    exact lt_of_le_of_lt hdist hε
  · have hqpos : 0 < ‖q‖ := lt_of_le_of_ne (norm_nonneg q) (Ne.symm hq0)
    have hpow : ContinuousAt (fun τ : ℝ => |τ - t| ^ (α / 2)) t := by
      apply ContinuousAt.rpow
      · fun_prop
      · fun_prop
      · right
        positivity
    rw [Metric.continuousAt_iff] at hpow
    obtain ⟨δ, hδ, hδbound⟩ := hpow (ε / ‖q‖) (div_pos hε hqpos)
    refine ⟨δ, hδ, fun {τ} hτ => ?_⟩
    have hp := hδbound hτ
    have hz : (0 : ℝ) ^ (α / 2) = 0 := zero_rpow (by positivity)
    simp only [sub_self, abs_zero, hz] at hp
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg (τ - t)) (α / 2))] at hp
    have hdist := dist_globalTimeSlice_le hα q τ t
    exact hdist.trans_lt (by
      simpa only [mul_comm] using (lt_div_iff₀ hqpos).mp hp)

end ParabolicC0AlphaBanach

end AnalyticPDE
end RicciFlow
