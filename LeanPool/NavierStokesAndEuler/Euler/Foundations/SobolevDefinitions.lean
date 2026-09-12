/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.SchwartzDerivatives
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Sobolev weights and directional derivatives

The physical domain, embedding constant, and Schwartz derivatives used by the
cylinder estimates are independent of Fourier inversion.
-/

@[expose] public section

noncomputable section

namespace EulerSobolev

open MeasureTheory
open scoped SchwartzMap ENNReal ContDiff LineDeriv

/-- The real Euclidean domain of dimension `d`. -/
abbrev Domain (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The Fourier weight defining the inhomogeneous Sobolev order `s`. -/
noncomputable def besselWeight (d : ℕ) (s : ℝ) (ξ : Domain d) : ℝ :=
  (1 + ‖ξ‖ ^ 2) ^ (s / 2)

theorem besselWeight_temperate (d : ℕ) (s : ℝ) :
    (besselWeight d s).HasTemperateGrowth :=
  Function.hasTemperateGrowth_one_add_norm_sq_rpow (Domain d) (s / 2)

theorem besselWeight_pos (d : ℕ) (s : ℝ) (ξ : Domain d) : 0 < besselWeight d s ξ := by
  unfold besselWeight
  positivity

theorem besselWeight_neg_mul (d : ℕ) (s : ℝ) (ξ : Domain d) :
    besselWeight d (-s) ξ * besselWeight d s ξ = 1 := by
  unfold besselWeight
  rw [← Real.rpow_add (by positivity)]
  have he : -s / 2 + s / 2 = 0 := by ring
  rw [he, Real.rpow_zero]

theorem besselWeight_add (d : ℕ) (s t : ℝ) (ξ : Domain d) :
    besselWeight d (s + t) ξ = besselWeight d s ξ * besselWeight d t ξ := by
  unfold besselWeight
  rw [← Real.rpow_add (by positivity)]
  congr 1
  ring

/-- One derivative factor is absorbed by one Sobolev order. -/
theorem besselWeight_mul_norm_le (d : ℕ) (s : ℝ) (ξ : Domain d) :
    besselWeight d s ξ * ‖ξ‖ ≤ besselWeight d (s + 1) ξ := by
  have hn : ‖ξ‖ ≤ besselWeight d 1 ξ := by
    unfold besselWeight
    rw [← Real.sqrt_eq_rpow]
    calc
      ‖ξ‖ = Real.sqrt (‖ξ‖ ^ 2) := (Real.sqrt_sq (norm_nonneg ξ)).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by linarith)
  rw [besselWeight_add]
  exact mul_le_mul_of_nonneg_left hn (besselWeight_pos d s ξ).le

/-- The reciprocal Bessel weight is in L² exactly in the range needed here. -/
theorem reciprocal_weight_memLp (d : ℕ) (s : ℝ) (hs : (d : ℝ) < 2 * s) :
    MemLp (besselWeight d (-s)) 2 (volume : Measure (Domain d)) := by
  have hm : AEStronglyMeasurable (besselWeight d (-s)) (volume : Measure (Domain d)) :=
    (besselWeight_temperate d (-s)).1.continuous.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hm).2
  have hi : Integrable (fun ξ : Domain d => (1 + ‖ξ‖ ^ 2) ^ (-(2 * s) / 2)) volume :=
    integrable_rpow_neg_one_add_norm_sq (by simpa [Domain] using hs)
  apply hi.congr
  filter_upwards with ξ
  dsimp only [besselWeight]
  rw [← Real.rpow_mul_natCast (by positivity)]
  congr 1
  push_cast
  ring

/-- The reciprocal Fourier weight represented as a genuine `L²` element. -/
noncomputable def reciprocalWeightLp (d : ℕ) (s : ℝ) (hs : (d : ℝ) < 2 * s) :
    Lp ℝ 2 (volume : Measure (Domain d)) :=
  (reciprocal_weight_memLp d s hs).toLp (besselWeight d (-s))

/-- A finite Sobolev embedding constant: the `L²` norm of the reciprocal weight. -/
noncomputable def embeddingConstant (d : ℕ) (s : ℝ) (hs : (d : ℝ) < 2 * s) : ℝ :=
  ‖reciprocalWeightLp d s hs‖

end EulerSobolev

namespace EulerSobolevProducts

open EulerSobolev
open scoped SchwartzMap LineDeriv

/-- Repeated differentiation in one fixed direction, as a Schwartz function. -/
noncomputable def directional (d n : ℕ) (v : Domain d) (f : 𝓢(Domain d, ℂ)) :
    𝓢(Domain d, ℂ) := schwartzIteratedDerivative (fun _ : Fin n => v) f

end EulerSobolevProducts
