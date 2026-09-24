/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientHGCloserCellsAnnulus

/-! # Finite annular decomposition of the pressure Riesz operator

A source restricted to a large ball is split into its near part and finitely
many dyadic annuli. The near part uses the global Calderón–Zygmund bound;
each annulus uses the exterior inverse-cube estimate.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean

noncomputable section
namespace CKN.Core.Step4

private theorem ball_indicator_hasCompactSupport
    (G : Vec3 → ℝ) (x : Vec3) {ρ : ℝ} (hρ : 0 < ρ) :
    HasCompactSupport ((vec3Ball x ρ).indicator G) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closure_vec3Ball hρ)
  intro y hy
  apply subset_closure
  by_contra hyB
  exact hy (Set.indicator_of_notMem hyB G)

private theorem nested_indicator_riesz_add
    (i j : Fin 3) {G : Vec3 → ℝ}
    (hG : MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    {A B : Set Vec3} (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B) :
    rieszSecondGradientExtensionOperator
      (rieszSecondL2Input i j) (rieszSecondL2_weak_type i j) (B.indicator G) =ᵐ[volume]
      rieszSecondGradientExtensionOperator
        (rieszSecondL2Input i j) (rieszSecondL2_weak_type i j) (A.indicator G) +
      rieszSecondGradientExtensionOperator
        (rieszSecondL2Input i j) (rieszSecondL2_weak_type i j) ((B \ A).indicator G) := by
  have h := pressure_riesz_component_indicator_add_ae i j (hG.indicator hB) hA
  have h₁ : A.indicator (B.indicator G) = A.indicator G := by
    funext x
    by_cases hx : x ∈ A
    · simp [hx, hAB hx]
    · simp [hx]
  have h₂ : Aᶜ.indicator (B.indicator G) = (B \ A).indicator G := by
    funext x
    by_cases hx : x ∈ A <;> by_cases hxB : x ∈ B <;> simp [hx, hxB]
  rwa [h₁, h₂] at h

/-- The local norm of a source restricted to a dyadic outer ball is bounded
by its near norm and the finite sum of exterior source masses. -/
theorem pressure_riesz_finite_annuli_eLpNorm_bound
    (i j : Fin 3) {G : Vec3 → ℝ}
    (hG : MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (x : Vec3) {r : ℝ} (hr : 0 < r) (N : ℕ) :
    eLpNorm (rieszSecondGradientExtensionOperator
      (rieszSecondL2Input i j) (rieszSecondL2_weak_type i j)
      ((vec3Ball x ((2 : ℝ) ^ N * (2 * r))).indicator G))
      (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict (vec3Ball x r)) ≤
      ENNReal.ofReal (czGradientComponentConstant rieszSecondWeakTypeConstant 1) *
        eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict (vec3Ball x (2 * r))) +
      ENNReal.ofReal (6912 * (4 * Real.pi)⁻¹) * volume (vec3Ball x r) ^ (5 / 6 : ℝ) *
        ∑ n ∈ Finset.range N,
          ENNReal.ofReal (2 * ((2 : ℝ) ^ n * (2 * r))) ^ (-3 : ℝ) *
            ∫⁻ y in vec3Ball x (2 * ((2 : ℝ) ^ n * (2 * r))), ‖G y‖ₑ := by
  let T : (Vec3 → ℝ) → Vec3 → ℝ :=
    rieszSecondGradientExtensionOperator (rieszSecondL2Input i j) (rieszSecondL2_weak_type i j)
  let ρ : ℕ → ℝ := fun n => (2 : ℝ) ^ n * (2 * r)
  have hρpos : ∀ n, 0 < ρ n := by intro n; dsimp [ρ]; positivity
  have hρstep : ∀ n, ρ (n + 1) = 2 * ρ n := by intro n; dsimp [ρ]; rw [pow_succ]; ring
  have hρbig : ∀ n, 2 * r ≤ ρ n := by
    intro n
    exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
  have hbase : eLpNorm (T ((vec3Ball x (2 * r)).indicator G))
      (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict (vec3Ball x r)) ≤
      ENNReal.ofReal (czGradientComponentConstant rieszSecondWeakTypeConstant 1) *
        eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict (vec3Ball x (2 * r))) := by
    calc
      _ ≤ eLpNorm (T ((vec3Ball x (2 * r)).indicator G)) (ENNReal.ofReal (6 / 5 : ℝ)) volume :=
        eLpNorm_mono_measure _ Measure.restrict_le_self
      _ ≤ ENNReal.ofReal (czGradientComponentConstant rieszSecondWeakTypeConstant 1) *
          eLpNorm ((vec3Ball x (2 * r)).indicator G) (ENNReal.ofReal (6 / 5 : ℝ)) volume :=
        pressure_riesz_component_eLpNorm_bound i j (hG.indicator (vec3Ball_measurable _ _))
          (ball_indicator_hasCompactSupport G x (by positivity))
      _ = _ := by rw [eLpNorm_indicator_eq_eLpNorm_restrict (vec3Ball_measurable _ _)]
  change eLpNorm (T ((vec3Ball x (ρ N)).indicator G)) _ _ ≤ _
  induction N with
  | zero => simpa [ρ] using hbase
  | succ N ih =>
    have hsub : vec3Ball x (ρ N) ⊆ vec3Ball x (ρ (N + 1)) := by
      intro y hy
      change vec3EuclideanNorm (y - x) < ρ (N + 1)
      rw [hρstep]
      exact lt_of_lt_of_le hy (by linarith only [hρpos N])
    have hadd := nested_indicator_riesz_add i j hG
      (vec3Ball_measurable x (ρ N)) (vec3Ball_measurable x (ρ (N + 1))) hsub
    have hann := pressure_riesz_annulus_eLpNorm_bound i j hG x hr (hρbig N)
    have hnorm : eLpNorm (T ((vec3Ball x (ρ (N + 1))).indicator G))
        (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict (vec3Ball x r)) ≤
        eLpNorm (T ((vec3Ball x (ρ N)).indicator G))
          (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict (vec3Ball x r)) +
        eLpNorm (T ((vec3Ball x (2 * ρ N) \ vec3Ball x (ρ N)).indicator G))
          (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict (vec3Ball x r)) := by
      calc
        _ = eLpNorm (T ((vec3Ball x (ρ N)).indicator G) +
            T ((vec3Ball x (ρ (N + 1)) \ vec3Ball x (ρ N)).indicator G))
            (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict (vec3Ball x r)) :=
          eLpNorm_congr_ae (ae_restrict_of_ae hadd)
        _ ≤ _ := by
          rw [hρstep N]
          exact eLpNorm_add_le (by norm_num)
    refine hnorm.trans ((add_le_add ih hann).trans_eq ?_)
    rw [Finset.sum_range_succ]
    dsimp only [ρ]
    ring

end CKN.Core.Step4
