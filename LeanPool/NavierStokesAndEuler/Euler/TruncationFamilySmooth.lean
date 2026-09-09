/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.FiniteEnergyTruncation
import Mathlib.Algebra.Order.Star.Real

/-!
# Time dependence of the radial truncation

The radial average and potential truncation preserve joint smoothness.
For a velocity smooth only on nonnegative times, the square-time pullback
is globally smooth. Pulling this family back along the continuous square
root recovers the original truncation, which is sufficient for the
continuous-in-time spatial-jet interface of `SmoothTimeField`.
-/

@[expose] public section


noncomputable section


open Set MeasureTheory Filter EulerSmoothLimit EulerVectorCalculus
open scoped ContDiff Topology

namespace Euler.ComparatorBridge

/-- Radial integration preserves joint smoothness with an auxiliary parameter. -/
theorem radialAverage_family_smooth (v : Space × ℝ → Space)
    (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (fun xt : Space × ℝ => radialAverage (fun y => v (y, xt.2)) xt.1) := by
  let F : (Space × ℝ) × ℝ → Space := fun p => p.2 • v (p.2 • p.1.1, p.1.2)
  have hF : ContDiff ℝ ∞ F := by
    exact contDiff_snd.smul (hv.comp
      ((contDiff_snd.smul contDiff_fst.fst).prodMk contDiff_fst.snd))
  exact EulerCompactParameterIntegral.integral_contDiff 0 1 (by norm_num) F hF

/-- The radial vector potential is jointly smooth in space and the parameter. -/
theorem radialPotential_family_smooth (v : Space × ℝ → Space)
    (hv : ContDiff ℝ ∞ v) (i : Fin 3) :
    ContDiff ℝ ∞ (fun xt : Space × ℝ => radialPotential (fun y => v (y, xt.2)) i xt.1) := by
  have hc (j : Fin 3) : ContDiff ℝ ∞ (fun x : Space => x j) :=
    (EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff
  have hb := radialAverage_family_smooth v hv
  exact ((hc _).comp contDiff_fst |>.mul ((hc _).comp hb)).sub
    ((hc _).comp contDiff_fst |>.mul ((hc _).comp hb))

/-- Spatial derivatives of a smooth joint family are jointly smooth. -/
theorem spatial_fderiv_family_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Space × ℝ → E) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun xt : Space × ℝ => fderiv ℝ (fun y => f (y, xt.2)) xt.1) := by
  have he (xt : Space × ℝ) : fderiv ℝ (fun y => f (y, xt.2)) xt.1 =
      (fderiv ℝ f xt).comp (ContinuousLinearMap.inl ℝ Space ℝ) := by
    exact (((hf.differentiable (by simp)) xt).hasFDerivAt.comp xt.1
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) xt.1 xt.2)).fderiv
  have hs := (hf.fderiv_right (m := ∞) (by simp)).clm_comp
    (contDiff_const (c := ContinuousLinearMap.inl ℝ Space ℝ))
  have heq : (fun xt : Space × ℝ => fderiv ℝ (fun y => f (y, xt.2)) xt.1) =
      (fun xt => (fderiv ℝ f xt).comp (ContinuousLinearMap.inl ℝ Space ℝ)) := funext he
  rw [heq]
  exact hs

/-- Curl, applied in the spatial variables only, preserves joint smoothness. -/
theorem curl_family_smooth (ψ : Fin 3 → Space × ℝ → ℝ)
    (hψ : ∀ i, ContDiff ℝ ∞ (ψ i)) :
    ContDiff ℝ ∞ (fun xt : Space × ℝ => curl (fun i y => ψ i (y, xt.2)) xt.1) := by
  apply (contDiff_piLp 2).mpr
  intro i
  exact ((spatial_fderiv_family_smooth (ψ (i + 2)) (hψ _)).clm_apply
    (contDiff_const (c := EuclideanSpace.single (i + 1) (1 : ℝ)))).sub
    ((spatial_fderiv_family_smooth (ψ (i + 1)) (hψ _)).clm_apply
      (contDiff_const (c := EuclideanSpace.single (i + 2) (1 : ℝ))))

/-- A fixed smooth cutoff gives a jointly smooth family of solenoidal truncations. -/
theorem potentialTruncation_family_smooth (v : Space × ℝ → Space)
    (hv : ContDiff ℝ ∞ v) (χ : Space → ℝ) (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (fun xt : Space × ℝ => potentialTruncation (fun y => v (y, xt.2)) χ xt.1) := by
  apply curl_family_smooth (fun i xt => χ xt.1 * radialPotential (fun y => v (y, xt.2)) i xt.1)
  intro i
  exact (hχ.comp contDiff_fst).mul (radialPotential_family_smooth v hv i)

/-- Squaring the time parameter turns smoothness on the closed half-space into
global smoothness, including at time zero. -/
theorem nonnegative_time_square_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Space × ℝ → E) (hv : ContDiffOn ℝ ∞ v (univ ×ˢ Ici 0)) :
    ContDiff ℝ ∞ (fun xt : Space × ℝ => v (xt.1, xt.2 ^ 2)) := by
  apply contDiffOn_univ.mp
  apply hv.comp (contDiff_fst.prodMk (contDiff_snd.pow 2)).contDiffOn
  intro xt _
  exact ⟨mem_univ _, show 0 ≤ xt.2 ^ 2 from sq_nonneg _⟩

/-- The radial truncation of a Comparator-smooth field has a globally smooth
square-time parametrization. -/
theorem potentialTruncation_square_family_smooth (v : Space × ℝ → Space)
    (hv : ContDiffOn ℝ ∞ v (univ ×ˢ Ici 0))
    (χ : Space → ℝ) (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (fun xt : Space × ℝ =>
      potentialTruncation (fun y => v (y, xt.2 ^ 2)) χ xt.1) :=
  potentialTruncation_family_smooth _ (nonnegative_time_square_smooth v hv) χ hχ

/-- The continuous time map used to recover the original compact time interval. -/
def sqrtTimeMap (T : ℝ) : C(Icc (0 : ℝ) T, Icc (0 : ℝ) (Real.sqrt T)) where
  toFun t := ⟨Real.sqrt t, Real.sqrt_nonneg _, Real.sqrt_le_sqrt t.property.2⟩
  continuous_toFun := (Real.continuous_sqrt.comp continuous_subtype_val).subtype_mk _

@[simp] theorem sqrtTimeMap_apply (T : ℝ) (t : Icc (0 : ℝ) T) :
    (sqrtTimeMap T t : ℝ) = Real.sqrt t := rfl

/-- Continuous square-root reparametrization recovers the exact original family. -/
theorem potentialTruncation_square_sqrt (v : Space × ℝ → Space)
    (χ : Space → ℝ) (x : Space) {t : ℝ} (ht : 0 ≤ t) :
    potentialTruncation (fun y => v (y, (Real.sqrt t) ^ 2)) χ x =
      potentialTruncation (fun y => v (y, t)) χ x := by
  rw [Real.sq_sqrt ht]


end Euler.ComparatorBridge
