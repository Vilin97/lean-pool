/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanHarmonicDerivatives
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import LeanPool.NavierStokesAndEuler.Euler.MeanHarmonicLaplacian
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Joint spatial coordinate derivatives and uniform energy bounds for
families supported in a fixed compact set. -/

@[expose] public section


noncomputable section

open Set MeasureTheory Laplacian EulerSmoothLimit EulerVectorCalculus EulerMeanHarmonic
open scoped ContDiff Topology

namespace EulerComparatorRecovery

theorem joint_scalar_partialDerivative_contDiffOn
    {u : ℝ × Space → ℝ} {S : Set ℝ}
    (hu : ContDiffOn ℝ ∞ u (S ×ˢ (univ : Set Space))) (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Space =>
      partialDerivative (fun y => u (z.1, y)) i z.2) (S ×ˢ (univ : Set Space)) := by
  have hd : ContDiffOn ℝ ∞ (fun z : ℝ × Space =>
      fderiv ℝ (fun y => u (z.1, y)) z.2) (S ×ˢ (univ : Set Space)) := by
    intro z hz
    have hf : ContDiffWithinAt ℝ ∞
        (fun q : (ℝ × Space) × Space => u (q.1.1, q.2))
        ((S ×ˢ (univ : Set Space)) ×ˢ (univ : Set Space)) (z, z.2) := by
      apply (hu z hz).comp (z, z.2)
        (contDiffWithinAt_fst.fst.prodMk contDiffWithinAt_snd)
      intro q hq
      exact ⟨hq.1.1, mem_univ _⟩
    have hf' := ContDiffWithinAt.fderivWithin
      (𝕜 := ℝ) (n := ∞) (m := ∞)
      (f := fun (z : ℝ × Space) (y : Space) => u (z.1, y))
      (s := S ×ˢ (univ : Set Space)) (t := (univ : Set Space))
      (g := fun z : ℝ × Space => z.2)
      hf contDiffWithinAt_snd uniqueDiffOn_univ (by simp) hz
      (by intro z hz; exact mem_univ _)
    simpa only [fderivWithin_univ] using hf'
  exact hd.clm_apply contDiffOn_const

theorem joint_wordDerivative_contDiffOn
    {u : ℝ × Space → ℝ} {S : Set ℝ}
    (hu : ContDiffOn ℝ ∞ u (S ×ˢ (univ : Set Space))) (word : List (Fin 3)) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Space =>
      wordDerivative word (fun y => u (z.1, y)) z.2) (S ×ˢ (univ : Set Space)) := by
  induction word with
  | nil => exact hu
  | cons i word ih => exact joint_scalar_partialDerivative_contDiffOn ih i

theorem joint_scalar_laplacian_contDiffOn
    {u : ℝ × Space → ℝ} {S : Set ℝ}
    (hu : ContDiffOn ℝ ∞ u (S ×ˢ (univ : Set Space))) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => Δ (fun y => u (z.1, y)) z.2)
      (S ×ˢ (univ : Set Space)) := by
  have hd : ContDiffOn ℝ ∞ (fun z : ℝ × Space => ∑ i : Fin 3,
      partialDerivative (partialDerivative (fun y => u (z.1, y)) i) i z.2)
      (S ×ˢ (univ : Set Space)) :=
    ContDiffOn.sum (fun i _ => joint_scalar_partialDerivative_contDiffOn
      (joint_scalar_partialDerivative_contDiffOn hu i) i)
  apply hd.congr
  intro z hz
  have hs : ContDiff ℝ ∞ (fun y => u (z.1, y)) :=
    hu.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun y => ⟨hz.1, mem_univ _⟩)
  exact laplacian_eq_coordinate_sum _ hs z.2

theorem tsupport_wordDerivative_subset (word : List (Fin 3)) (f : Space → ℝ) :
    tsupport (wordDerivative word f) ⊆ tsupport f := by
  induction word with
  | nil => exact Subset.rfl
  | cons i word ih =>
    exact (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans ih

theorem uniform_energy_of_compact_support
    {E : Type*} [NormedAddCommGroup E]
    (f : ℝ × Space → E) (T : ℝ) (K : Set Space) (hK : IsCompact K)
    (hf : ContinuousOn f (Icc (0 : ℝ) T ×ˢ K))
    (hsupport : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∉ K, f (t, x) = 0) :
    ∃ B : ℝ, ∀ t ∈ Icc (0 : ℝ) T, (∫ x, ‖f (t, x)‖ ^ 2) ≤ B := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hf
  refine ⟨(max C 0) ^ 2 * volume.real K, ?_⟩
  intro t ht
  have hind : (fun x => ‖f (t, x)‖ ^ 2) =
      K.indicator (fun x => ‖f (t, x)‖ ^ 2) := by
    funext x
    by_cases hx : x ∈ K
    · simp only [indicator_of_mem hx]
    · simp [indicator_of_notMem hx, hsupport t ht x hx]
  rw [hind, integral_indicator hK.measurableSet]
  apply (le_abs_self _).trans
  rw [← Real.norm_eq_abs]
  apply norm_setIntegral_le_of_norm_le_const hK.measure_lt_top
  intro x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) ((hC (t, x) ⟨ht, hx⟩).trans (le_max_left _ _)) 2

theorem wordDerivative_energy_uniform_of_compact_support
    (f : ℝ × Space → ℝ) (T : ℝ) (K : Set Space) (hK : IsCompact K)
    (hf : ContDiffOn ℝ ∞ f (Icc (0 : ℝ) T ×ˢ (univ : Set Space)))
    (hsupport : ∀ t ∈ Icc (0 : ℝ) T, tsupport (fun x => f (t, x)) ⊆ K)
    (word : List (Fin 3)) :
    ∃ B : ℝ, ∀ t ∈ Icc (0 : ℝ) T,
      (∫ x, wordDerivative word (fun y => f (t, y)) x ^ 2) ≤ B := by
  obtain ⟨B, hB⟩ := uniform_energy_of_compact_support
    (fun z : ℝ × Space => wordDerivative word (fun y => f (z.1, y)) z.2)
    T K hK
    ((joint_wordDerivative_contDiffOn hf word).continuousOn.mono
      (by intro z hz; exact ⟨hz.1, mem_univ _⟩))
    (by
      intro t ht x hx
      exact image_eq_zero_of_notMem_tsupport (fun hn =>
        hx (hsupport t ht (tsupport_wordDerivative_subset word _ hn))))
  refine ⟨B, fun t ht => ?_⟩
  simpa only [Real.norm_eq_abs, sq_abs] using hB t ht

end EulerComparatorRecovery
