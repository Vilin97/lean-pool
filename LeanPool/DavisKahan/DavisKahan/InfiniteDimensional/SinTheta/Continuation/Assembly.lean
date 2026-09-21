/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SinTheta.Continuation.Transport
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum

/-! # Assembly -/

open TauCeti.DavisKahan.Angle


/-!
# Finite subdivision for spectral continuation

A Lipschitz path on the unit interval admits a uniform finite subdivision whose
adjacent values are less than one apart.  Applied to the fixed-contour Riesz
operator path, this supplies the local norm threshold required by the accepted
direct-rotation construction.

This module deliberately stops at the subdivision seam.  Spectral
identification will show that the Riesz operators are orthogonal projections;
the following assembly layer can then choose and compose the local direct
rotations.
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan.Foundation

open DavisKahan

open Set
open scoped InnerProductSpace unitInterval

universe v

section UniformSubdivision

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [CompleteSpace H] in
/-- A Lipschitz operator path on `[0,1]` has a uniform natural-number mesh on
which every adjacent operator difference has norm strictly below one. -/
theorem exists_uniform_subdivision_norm_sub_lt_one
    (P : ℝ → H →L[ℂ] H) (K : NNReal)
    (hP : LipschitzOnWith K P (Set.Icc (0 : ℝ) 1)) :
    ∃ n : ℕ, 0 < n ∧ ∀ k : ℕ, k < n →
      ‖P ((k : ℝ) / n) - P (((k + 1 : ℕ) : ℝ) / n)‖ < 1 := by
  obtain ⟨n, hn⟩ := exists_nat_gt (K : ℝ)
  have hnpos : 0 < n := by
    have hKnonneg : (0 : ℝ) ≤ K := K.coe_nonneg
    have hnreal : (0 : ℝ) < n := hKnonneg.trans_lt hn
    exact_mod_cast hnreal
  refine ⟨n, hnpos, ?_⟩
  intro k hk
  let t : ℝ := (k : ℝ) / n
  let u : ℝ := ((k + 1 : ℕ) : ℝ) / n
  have hnreal : (0 : ℝ) < n := Nat.cast_pos.mpr hnpos
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · dsimp [t]
      positivity
    · dsimp [t]
      rw [div_le_one hnreal]
      exact_mod_cast (Nat.le_of_lt hk)
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · dsimp [u]
      positivity
    · dsimp [u]
      rw [div_le_one hnreal]
      exact_mod_cast (Nat.succ_le_iff.mpr hk)
  have hdist : dist t u = 1 / (n : ℝ) := by
    rw [Real.dist_eq, abs_sub_comm]
    have htu : t ≤ u := by
      dsimp [t, u]
      exact div_le_div_of_nonneg_right
        (by exact_mod_cast Nat.le_succ k) hnreal.le
    rw [abs_of_nonneg (sub_nonneg.mpr htu)]
    dsimp [t, u]
    push_cast
    ring
  have hLip := hP.dist_le_mul t ht u hu
  have hsmall : (K : ℝ) * (1 / (n : ℝ)) < 1 := by
    rw [mul_one_div, div_lt_one hnreal]
    exact hn
  calc
    ‖P t - P u‖ = dist (P t) (P u) := by rw [dist_eq_norm]
    _ ≤ (K : ℝ) * dist t u := hLip
    _ = (K : ℝ) * (1 / (n : ℝ)) := by rw [hdist]
    _ < 1 := hsmall

/-- The common-margin affine Riesz path admits a subdivision whose adjacent
Riesz operators differ in norm by less than one. -/
theorem exists_uniform_subdivision_fixedContourRieszOperator_norm_sub_lt_one
    (Γ : PiecewiseC1ClosedContour) (A V : H →L[ℂ] H)
    (delta : ℝ) (hdelta : 0 < delta)
    (hself : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (operatorPath A V t).IsSymmetric)
    (hsep : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x : unitInterval,
      ∀ lam ∈ realSpectrum (operatorPath A V t),
        delta ≤ ‖Γ.path x - (lam : ℂ)‖) :
    ∃ n : ℕ, 0 < n ∧ ∀ k : ℕ, k < n →
      ‖fixedContourRieszOperator Γ
          (operatorPath A V ((k : ℝ) / n)) -
        fixedContourRieszOperator Γ
          (operatorPath A V (((k + 1 : ℕ) : ℝ) / n))‖ < 1 := by
  exact exists_uniform_subdivision_norm_sub_lt_one
    (fun t ↦ fixedContourRieszOperator Γ (operatorPath A V t))
    (Real.toNNReal
      |‖rieszNormalization‖ *
        (delta⁻¹ ^ 2 * ‖V‖ * Γ.contourLength)|)
    (lipschitzOnWith_fixedContourRieszOperator_operatorPath
      Γ A V (Set.Icc (0 : ℝ) 1) delta hdelta hself hsep)

end UniformSubdivision

end DavisKahanExt
end TauCeti
