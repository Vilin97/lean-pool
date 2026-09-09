/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpTranslation
public import LeanPool.NavierStokesAndEuler.Euler.LpDominatedDerivative
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-! The genuine L² derivative of translations of compact smooth ordinary-space fields. -/

noncomputable section


namespace EulerLpTranslation

open MeasureTheory EulerSmoothLimit EulerLpDerivative Filter
open scoped ContDiff Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def compactField (f : Space → V) (hc : HasCompactSupport f) (hf : ContDiff ℝ ∞ f) : L2Space V :=
  (hf.continuous.memLp_of_hasCompactSupport hc).toLp f

def compactDerivative (f : Space → V) (hc : HasCompactSupport f) (hf : ContDiff ℝ ∞ f) :
    L2Space (Space →L[ℝ] V) :=
  ((hf.fderiv_right (m := ∞) (by simp)).continuous.memLp_of_hasCompactSupport
    (hc.fderiv ℝ)).toLp (fderiv ℝ f)

theorem compactField_ae (f : Space → V) (hc : HasCompactSupport f) (hf : ContDiff ℝ ∞ f) :
    compactField f hc hf =ᵐ[volume] f := MemLp.coeFn_toLp _

theorem compactDerivative_ae (f : Space → V) (hc : HasCompactSupport f) (hf : ContDiff ℝ ∞ f) :
    compactDerivative f hc hf =ᵐ[volume] fderiv ℝ f := MemLp.coeFn_toLp _

/-- A single compactly supported L² function dominates every small translation increment. -/
theorem compact_increment_bound (f : Space → V) (hc : HasCompactSupport f)
    (hf : ContDiff ℝ ∞ f) :
    ∃ M : Space → ℝ, MemLp M 2 volume ∧ (∀ x, 0 ≤ M x) ∧
      ∀ a : Space, ‖a‖ ≤ 1 → ∀ x, ‖f (x+a)-f x‖ ≤ M x * ‖a‖ := by
  obtain ⟨R, hR⟩ := hc.isBounded.subset_closedBall (0 : Space)
  obtain ⟨C, hC⟩ := (hc.fderiv ℝ).exists_bound_of_continuous
    (hf.fderiv_right (m := ∞) (by simp)).continuous
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  let K := Metric.closedBall (0 : Space) (|R|+1)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hsupport : tsupport f ⊆ K := fun _ hx =>
    Metric.closedBall_subset_closedBall (by linarith [le_abs_self R]) (hR hx)
  refine ⟨K.indicator (fun _ => C), memLp_indicator_const 2 hK.isClosed.measurableSet C
    (Or.inr hK.measure_ne_top), ?_, ?_⟩
  · intro x
    exact Set.indicator_nonneg (fun _ _ => hC0) x
  · intro a ha x
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx]
      have h := Convex.norm_image_sub_le_of_norm_fderiv_le
        (𝕜 := ℝ) (f := f) (s := Set.univ) (fun y _ => hf.differentiable (by simp) y)
        (fun y _ => hC y) (convex_univ : Convex ℝ (Set.univ : Set Space))
        (Set.mem_univ x) (Set.mem_univ (x+a))
      simpa only [add_sub_cancel_left] using h
    · have hxf : x ∉ tsupport f := fun ht => hx (hsupport ht)
      have hxa : x+a ∉ tsupport f := by
        intro ht
        apply hx
        have hn : ‖x+a‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hR ht
        change dist x 0 ≤ |R|+1
        rw [dist_zero_right]
        have hh : ‖x‖ ≤ ‖x+a‖+‖a‖ := by
          simpa only [add_sub_cancel_right] using norm_sub_le (x+a) a
        linarith [le_abs_self R]
      simp only [image_eq_zero_of_notMem_tsupport hxa, image_eq_zero_of_notMem_tsupport hxf,
        sub_zero, norm_zero, Set.indicator_of_notMem hx, zero_mul, le_refl]

/-- Ordinary Fréchet differentiation and L² translation differentiation agree on compact smooth fields. -/
theorem compactField_hasFDerivAt (f : Space → V) (hc : HasCompactSupport f)
    (hf : ContDiff ℝ ∞ f) :
    HasFDerivAt (fun a : Space => translation a (compactField f hc hf))
      (derivativeMap volume (compactDerivative f hc hf)) 0 := by
  obtain ⟨M, hM, hM0, hbound⟩ := compact_increment_bound f hc hf
  apply EulerLpDerivative.hasFDerivAt_of_dominated volume
    (fun a : Space => translation a (compactField f hc hf)) (fun a x => f (x+a))
    _ (compactDerivative f hc hf) _ M hM (Eventually.of_forall hM0)
  · filter_upwards [Metric.ball_mem_nhds (0 : Space) zero_lt_one] with a ha
    apply Eventually.of_forall
    intro x
    simpa only [add_zero] using hbound a
      ((by simpa only [Metric.mem_ball, dist_zero_right] using ha : ‖a‖ < 1).le) x
  · intro a
    filter_upwards [translation_ae a (compactField f hc hf),
      (measurePreserving_add_right (volume : Measure Space) a).quasiMeasurePreserving.ae
        (compactField_ae f hc hf)] with x hx hy
    exact hx.trans hy
  · filter_upwards [compactDerivative_ae f hc hf] with x hx
    rw [hx]
    simpa only [zero_add] using
      (hasFDerivAt_comp_add_left (f := f) x (x := (0 : Space))).mpr
        (by simpa only [add_zero] using (hf.differentiable (by simp) x).hasFDerivAt)

end EulerLpTranslation
