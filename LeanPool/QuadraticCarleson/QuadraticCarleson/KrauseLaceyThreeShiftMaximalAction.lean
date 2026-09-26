/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyThreeShiftAction

/-!
# Maximal positive tails from the three shifted forests

The same three localization families work for every physical lower cutoff.
Consequently the maximal finite global positive-half tail is pointwise bounded
by the sum of the three genuine localized maximal tail operators. This is the
maximal-operator form of the deterministic three-grid reduction.
-/

@[expose] public section

open Function MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace KrauseLaceyThreeShiftGrid

open KrauseLaceyStoppingRecursion


noncomputable
section

/-- A finite positive-half global tail, with the paper's physical lower
length cutoff. -/
def finitePositiveGlobalTail
    (topScale : ℤ) (depths : Finset ℕ) (f : ℝ → ℂ) (ell : ℤ) (x : ℝ) : ℂ :=
  ∑ depth ∈ depths,
    if (2 : ℝ) ^ ell ≤ (2 : ℝ) ^ (topScale - (depth : ℤ) + 2) then
      ∫ t, annularQuadraticKernel
        (positiveDyadicAmplitude (topScale - (depth : ℤ))) 1 (x - t) * f t
    else 0

/-- The genuine supremum over all physical cutoffs above `ell₀`. -/
def finitePositiveGlobalTailMaximal
    (ell₀ topScale : ℤ) (depths : Finset ℕ) (f : ℝ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ ell : {ell : ℤ // ell₀ ≤ ell},
    ‖finitePositiveGlobalTail topScale depths f ell.1 x‖ₑ

-- Elaborating the parameterized product-kernel integral needs additional reduction budget.
theorem measurable_finitePositiveGlobalTail
    (topScale : ℤ) (depths : Finset ℕ) {f : ℝ → ℂ}
    (hf : Measurable f) (ell : ℤ) :
    Measurable (finitePositiveGlobalTail topScale depths f ell) := by
  classical
  unfold finitePositiveGlobalTail
  apply Finset.measurable_fun_sum depths
  intro depth hdepth
  by_cases hcut : (2 : ℝ) ^ ell ≤
      (2 : ℝ) ^ (topScale - (depth : ℤ) + 2)
  · simp only [ite_eq_left hcut]
    have ha : Continuous (positiveDyadicAmplitude (topScale - (depth : ℤ))) :=
      continuous_iff_continuousAt.mpr fun t ↦
        (hasDerivAt_positiveDyadicAmplitude (topScale - (depth : ℤ)) t).continuousAt
    have hp : Continuous (fun z : ℝ ↦ phase (z ^ 2)) := by
      unfold phase
      fun_prop
    have hk : Measurable (fun z : ℝ ↦
        annularQuadraticKernel
          (positiveDyadicAmplitude (topScale - (depth : ℤ))) 1 z) := by
      convert (ha.mul hp).measurable using 1
      funext z
      simp only [annularQuadraticKernel, one_mul, Pi.mul_apply]
    have hprod : Measurable (fun p : ℝ × ℝ ↦
        annularQuadraticKernel
          (positiveDyadicAmplitude (topScale - (depth : ℤ))) 1 (p.1 - p.2) * f p.2) := by
      exact (hk.comp (measurable_fst.sub measurable_snd)).mul
        (hf.comp measurable_snd)
    simpa only [Function.comp_def] using
      hprod.stronglyMeasurable.integral_prod_right'.measurable
  · simp only [ite_eq_right hcut]
    exact measurable_const

theorem measurable_finitePositiveGlobalTailMaximal
    (ell₀ topScale : ℤ) (depths : Finset ℕ) {f : ℝ → ℂ}
    (hf : Measurable f) :
    Measurable (finitePositiveGlobalTailMaximal ell₀ topScale depths f) :=
  Measurable.iSup fun ell ↦
    (measurable_finitePositiveGlobalTail topScale depths hf ell.1).enorm

/-- One concrete set of three shifted families simultaneously controls every
cutoff in the finite global maximal operator, and every family lies in its
canonical parent-closed forest. -/
theorem exists_threeShiftForests_globalTailMaximal
    (f : L0Infinity) (ell₀ topScale : ℤ) (depths : Finset ℕ)
    (maxDepth : ℕ) (hdepths : ∀ depth ∈ depths, depth ≤ maxDepth) :
    ∃ E : ℕ → Finset ℤ,
      (∀ shift,
        finiteOneShiftMultiscaleFamily topScale depths E shift ⊆
          completeFiniteShiftGridForest topScale shift maxDepth
            (finiteOneShiftMultiscaleAddresses depths E shift)) ∧
      ∀ x,
        finitePositiveGlobalTailMaximal ell₀ topScale depths f x ≤
          ∑ shift : Fin 3,
            localizedTailMaximal ell₀ (finiteShiftGridScale topScale shift)
              (finiteOneShiftMultiscaleFamily topScale depths E shift) f x := by
  obtain ⟨E, hforest, hsum⟩ :=
    exists_threeShiftForests_globalTail_all_thresholds
      f topScale depths maxDepth hdepths
  refine ⟨E, hforest, fun x ↦ ?_⟩
  apply iSup_le
  intro ell
  unfold finitePositiveGlobalTail
  rw [← hsum ell.1 x]
  apply (enorm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro shift hshift
  exact le_iSup
    (fun q : {q : ℤ // ell₀ ≤ q} ↦
      ‖localizedTailAction (finiteShiftGridScale topScale shift)
        (finiteOneShiftMultiscaleFamily topScale depths E shift) f q.1 x‖ₑ)
    ell


end
end KrauseLaceyThreeShiftGrid
end QuadraticCarleson
