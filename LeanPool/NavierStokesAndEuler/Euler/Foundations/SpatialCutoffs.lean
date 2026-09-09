/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.Gevrey
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.GevreyCutoff
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.SmoothLimit
import LeanPool.NavierStokesAndEuler.Euler.Foundations.GevreyFunctions
import Mathlib.Algebra.Order.Star.Real

/-!
# Spatial Cutoffs
-/

@[expose] public section

noncomputable section

namespace EulerSpatialCutoffs

open EulerGevrey EulerGevreyCutoff EulerGevreyFunctions EulerSmoothLimit
open scoped ContDiff
open Set

/-- The even one-dimensional bump normalized to have value one at the origin. -/
def normalizedBump (t : ℝ) : ℝ := rawBump t / rawBump 0

theorem normalizedBump_contDiff : ContDiff ℝ ∞ normalizedBump :=
  rawBump_contDiff.div_const _

theorem normalizedBump_zero : normalizedBump 0 = 1 :=
  div_self rawBump_pos_zero.ne'

theorem normalizedBump_even (t : ℝ) : normalizedBump (-t) = normalizedBump t := by
  simp only [normalizedBump, rawBump_even]

theorem normalizedBump_nonneg (t : ℝ) : 0 ≤ normalizedBump t :=
  div_nonneg (rawBump_nonneg t) rawBump_pos_zero.le

theorem normalizedBump_gevrey (n : ℕ) (t : ℝ) :
    |iteratedDeriv n normalizedBump t| ≤ (3 / rawBump 0) * majorant 16 0 n := by
  have he : normalizedBump = fun x => rawBump x * (rawBump 0)⁻¹ := by
    funext x
    simp [normalizedBump, div_eq_mul_inv]
  rw [he, iteratedDeriv_mul_const_field, abs_mul, abs_inv, abs_of_pos rawBump_pos_zero]
  have h := mul_le_mul_of_nonneg_right (rawBump_gevrey_bound n t)
    (inv_nonneg.mpr rawBump_pos_zero.le)
  simpa [majorant, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

/-- A plateau on the unit interval with support inside the interval of radius nine eighths. -/
def outerWindow (t : ℝ) : ℝ := transition (17 + 16 * t) * transition (17 - 16 * t)

theorem outerWindow_contDiff : ContDiff ℝ ∞ outerWindow :=
  (transition_contDiff.comp (contDiff_const.add (contDiff_const.mul contDiff_id))).mul
    (transition_contDiff.comp (contDiff_const.sub (contDiff_const.mul contDiff_id)))

theorem outerWindow_even (t : ℝ) : outerWindow (-t) = outerWindow t := by
  simp [outerWindow, sub_eq_add_neg, mul_comm]

theorem outerWindow_one (t : ℝ) (ht : |t| ≤ 1) : outerWindow t = 1 := by
  have ht' := abs_le.mp ht
  simp [outerWindow, transition_one_of_ge _ (show 1 ≤ 17 + 16 * t by linarith),
    transition_one_of_ge _ (show 1 ≤ 17 - 16 * t by linarith)]

theorem outerWindow_zero (t : ℝ) (ht : 9 / 8 ≤ |t|) : outerWindow t = 0 := by
  rcases le_abs.mp ht with h | h
  · simp [outerWindow, transition_zero_of_le _ (show 17 - 16 * t ≤ -1 by linarith)]
  · simp [outerWindow, transition_zero_of_le _ (show 17 + 16 * t ≤ -1 by linarith)]

theorem outerWindow_gevrey (n : ℕ) (t : ℝ) :
    |iteratedDeriv n outerWindow t| ≤
      (3 * (1 + 3 / bumpMass) ^ 2) * majorant 256 0 n := by
  let L : ℝ →L[ℝ] ℝ := (16 : ℝ) • ContinuousLinearMap.id ℝ ℝ
  have hn : ‖L‖ ≤ 16 := by
    apply L.opNorm_le_bound (by norm_num)
    intro y
    simp [L, norm_mul]
  have hmass := bumpMass_pos
  have hb : ∀ n t, |iteratedDeriv n transition t| ≤ (1 + 3 / bumpMass) * majorant 16 0 n :=
    fun n t => by simpa [majorant, mul_assoc] using transition_gevrey_bound n t
  have hp := affine_composition_bound transition transition_contDiff L 17 16
    (1 + 3 / bumpMass) 16 (by norm_num) (by positivity) (by norm_num) hn hb
  have hm := affine_composition_bound transition transition_contDiff (-L) 17 16
    (1 + 3 / bumpMass) 16 (by norm_num) (by positivity) (by norm_num)
    (by simpa using hn) hb
  have hf : ContDiff ℝ ∞ (fun y : ℝ => transition (L y + 17)) :=
    transition_contDiff.comp (L.contDiff.add contDiff_const)
  have hg : ContDiff ℝ ∞ (fun y : ℝ => transition ((-L) y + 17)) :=
    transition_contDiff.comp ((-L).contDiff.add contDiff_const)
  have h := product_bound _ _ hf hg 256 (1 + 3 / bumpMass) (1 + 3 / bumpMass)
    (by norm_num) (by positivity) (by positivity) (by norm_num at hp; exact hp)
    (by norm_num at hm; exact hm) n t
  have he : outerWindow = (fun y => transition (L y + 17) * transition ((-L) y + 17)) := by
    funext y
    simp [outerWindow, L, sub_eq_add_neg, add_comm]
  rw [he]
  simpa [L, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    Real.norm_eq_abs, sub_eq_add_neg, add_comm, pow_two, mul_assoc] using h

/-- Product of three copies of a scalar profile at a common coordinate scale. -/
def tensorCutoff (g : ℝ → ℝ) (a : ℝ) (x : Space) : ℝ := ∏ i : Fin 3, g (a * x i)

theorem tensorCutoff_contDiff (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (a : ℝ) :
    ContDiff ℝ ∞ (tensorCutoff g a) := by
  apply contDiff_prod
  intro i _
  have hc : ContDiff ℝ ∞ (fun y : Space => y i) :=
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff
  exact hg.comp (contDiff_const.mul hc)

theorem tensorCutoff_even (g : ℝ → ℝ) (hg : ∀ t, g (-t) = g t) (a : ℝ) (x : Space) :
    tensorCutoff g a (-x) = tensorCutoff g a x := by
  simp [tensorCutoff, hg]

theorem tensorCutoff_gevrey (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g)
    (a R A : ℝ) (ha : 0 ≤ a) (hR : 0 ≤ R) (hA : 0 ≤ A)
    (hb : ∀ n t, |iteratedDeriv n g t| ≤ A * majorant R 0 n)
    (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n (tensorCutoff g a) x‖ ≤ (3 * A) ^ 3 * majorant (R * a) 0 n := by
  have hL (i : Fin 3) : ‖(a • EuclideanSpace.proj i : Space →L[ℝ] ℝ)‖ ≤ a := by
    apply (a • EuclideanSpace.proj i : Space →L[ℝ] ℝ).opNorm_le_bound ha
    intro y
    simpa [Real.norm_eq_abs, abs_of_nonneg ha] using
      mul_le_mul_of_nonneg_left (PiLp.norm_apply_le y i) ha
  have hi (i : Fin 3) := linear_composition_bound g hg (a • EuclideanSpace.proj i)
    R A a hR hA ha (hL i) hb
  have h := finite_product_bound (Finset.univ : Finset (Fin 3))
    (fun i (y : Space) => g (a * y i))
    (fun i _ => hg.comp (contDiff_const.mul
      (show ContDiff ℝ ∞ (fun y : Space => y i) from
        (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff)))
    (R * a) A (mul_nonneg hR ha) hA (fun i _ k y => by
      simpa only [Function.comp_def, smul_apply, smul_eq_mul, PiLp.proj_apply] using hi i k y) n x
  have he : tensorCutoff g a = (fun y : Space => ∏ i : Fin 3, g (a * y i)) := rfl
  rw [he]
  simpa only [Finset.card_univ, Fintype.card_fin] using h

/-- Inner spatial cutoff used to localize the leading oscillatory packet. -/
def innerCutoff : Space → ℝ := tensorCutoff normalizedBump 4

/-- Outer plateau used by the compactly supported mean correction. -/
def outerCutoff : Space → ℝ := tensorCutoff outerWindow 1

theorem innerCutoff_contDiff : ContDiff ℝ ∞ innerCutoff :=
  tensorCutoff_contDiff _ normalizedBump_contDiff _

theorem outerCutoff_contDiff : ContDiff ℝ ∞ outerCutoff :=
  tensorCutoff_contDiff _ outerWindow_contDiff _

theorem innerCutoff_even (x : Space) : innerCutoff (-x) = innerCutoff x :=
  tensorCutoff_even _ normalizedBump_even _ _

theorem outerCutoff_even (x : Space) : outerCutoff (-x) = outerCutoff x :=
  tensorCutoff_even _ outerWindow_even _ _

theorem innerCutoff_nonneg (x : Space) : 0 ≤ innerCutoff x := by
  unfold innerCutoff tensorCutoff
  exact Finset.prod_nonneg (fun i _ => normalizedBump_nonneg _)

theorem innerCutoff_zero : innerCutoff 0 = 1 := by
  simp [innerCutoff, tensorCutoff, normalizedBump_zero]

theorem outerCutoff_one (x : Space) (hx : ‖x‖ ≤ 1) : outerCutoff x = 1 := by
  unfold outerCutoff tensorCutoff
  apply Finset.prod_eq_one
  intro i _
  apply outerWindow_one
  simpa only [one_mul, ← Real.norm_eq_abs] using (PiLp.norm_apply_le x i).trans hx

theorem innerCutoff_gevrey (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n innerCutoff x‖ ≤
      (9 / rawBump 0) ^ 3 * majorant 64 0 n := by
  have hpos := rawBump_pos_zero
  have h := tensorCutoff_gevrey _ normalizedBump_contDiff 4 16 (3 / rawBump 0)
    (by norm_num) (by norm_num) (by positivity) normalizedBump_gevrey n x
  simpa only [innerCutoff, show (16 : ℝ) * 4 = 64 by norm_num,
    show (3 : ℝ) * (3 / rawBump 0) = 9 / rawBump 0 by ring] using h

theorem outerCutoff_gevrey (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n outerCutoff x‖ ≤
      (9 * (1 + 3 / bumpMass) ^ 2) ^ 3 * majorant 256 0 n := by
  have h := tensorCutoff_gevrey _ outerWindow_contDiff 1 256 (3 * (1 + 3 / bumpMass) ^ 2)
    (by norm_num) (by norm_num) (by positivity) outerWindow_gevrey n x
  simpa only [outerCutoff, mul_one,
    show (3 : ℝ) * (3 * (1 + 3 / bumpMass) ^ 2) = 9 * (1 + 3 / bumpMass) ^ 2 by ring] using h


theorem cube_closed (r : ℝ) : IsClosed (({x : Space | ∀ i, |x i| ≤ r})) := by
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro i
  exact isClosed_le ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.abs) continuous_const

theorem norm_sq_le_of_mem_cube (r : ℝ) (hr : 0 ≤ r) (x : Space) (hx : x ∈ ({x : Space | ∀ i, |x i|
    ≤ r})) :
    ‖x‖ ^ 2 ≤ 3 * r ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    _ ≤ ∑ _i : Fin 3, r ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have h := (sq_le_sq₀ (abs_nonneg (x i)) hr).2 (hx i)
      simpa only [sq_abs] using h
    _ = _ := by simp

theorem tensorCutoff_support (g : ℝ → ℝ) (a b : ℝ) (ha : 0 < a)
    (hg : ∀ t, g t ≠ 0 → |t| ≤ b) :
    tsupport (tensorCutoff g a) ⊆ ({x : Space | ∀ i, |x i| ≤ b / a}) := by
  apply closure_minimal _ (cube_closed _)
  intro x hx i
  have hgx : g (a * x i) ≠ 0 := by
    exact (Finset.prod_ne_zero_iff.mp hx) i (Finset.mem_univ _)
  have h := hg (a * x i) hgx
  rw [abs_mul, abs_of_pos ha] at h
  exact (le_div_iff₀ ha).2 (by nlinarith)

theorem innerCutoff_support : tsupport innerCutoff ⊆ Metric.ball (0 : Space) (1 / 2) := by
  have hs := tensorCutoff_support normalizedBump 4 1 (by norm_num) (fun t ht => by
    have hraw : rawBump t ≠ 0 := fun h => ht (by simp [normalizedBump, h])
    exact abs_le.mpr (rawBump_support (subset_tsupport _ hraw)))
  intro x hx
  have hn := norm_sq_le_of_mem_cube (1 / 4) (by norm_num) x (hs hx)
  rw [Metric.mem_ball, dist_zero_right]
  nlinarith [norm_nonneg x]

theorem outerCutoff_support : tsupport outerCutoff ⊆ Metric.closedBall (0 : Space) 2 := by
  have hs := tensorCutoff_support outerWindow 1 (9 / 8) (by norm_num) (fun t ht => by
    by_contra h
    exact ht (outerWindow_zero t (le_of_lt (lt_of_not_ge h))))
  intro x hx
  have hc : x ∈ ({x : Space | ∀ i, |x i| ≤ 9 / 8}) := by simpa using hs hx
  have hn := norm_sq_le_of_mem_cube (9 / 8) (by norm_num) x hc
  rw [Metric.mem_closedBall, dist_zero_right]
  nlinarith [norm_nonneg x]

theorem innerCutoff_compactSupport : HasCompactSupport innerCutoff := by
  apply (isCompact_closedBall (0 : Space) (1 / 2)).of_isClosed_subset (isClosed_tsupport _)
  exact innerCutoff_support.trans Metric.ball_subset_closedBall

theorem outerCutoff_compactSupport : HasCompactSupport outerCutoff :=
  (isCompact_closedBall (0 : Space) 2).of_isClosed_subset (isClosed_tsupport _) outerCutoff_support

end EulerSpatialCutoffs
