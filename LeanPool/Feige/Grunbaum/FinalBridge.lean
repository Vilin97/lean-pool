/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
import LeanPool.Feige.Grunbaum.TruncationConcavity

/-!
# From truncation concavity to the Grünbaum volume bound
-/

open MeasureTheory Set

namespace Grunbaum

lemma trunc_mono {d : ℕ} {C : Set (Euc d)}
    {ℓ : Euc d →L[ℝ] ℝ} {s t : ℝ} (hst : s ≤ t) :
    trunc C ℓ s ⊆ trunc C ℓ t := by
  intro x hx
  change x ∈ C ∧ ℓ x ≤ s at hx
  change x ∈ C ∧ ℓ x ≤ t
  exact ⟨hx.1, hx.2.trans hst⟩

lemma cdfRoot_pow_dimension {d : ℕ} (C : Set (Euc d))
    (ℓ : Euc d →L[ℝ] ℝ) (t : ℝ) :
    cdfRoot C ℓ t ^ (d + 1) =
      (volume (trunc C ℓ t) / volume C).toReal := by
  unfold cdfRoot
  simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one,
      ENNReal.toReal_pow] using
    congrArg ENNReal.toReal
      (ENNReal.rpow_inv_natCast_pow (Nat.succ_ne_zero d)
        (volume (trunc C ℓ t) / volume C))

lemma truncVolumeRatio_mono {d : ℕ}
    (C : FullDimensionalConvexBody d) (ℓ : Euc d →L[ℝ] ℝ)
    {s t : ℝ} (hst : s ≤ t) :
    (volume (trunc (C : Set (Euc d)) ℓ s) /
        volume (C : Set (Euc d))).toReal ≤
      (volume (trunc (C : Set (Euc d)) ℓ t) /
        volume (C : Set (Euc d))).toReal := by
  have hvol :
      volume (trunc (C : Set (Euc d)) ℓ s) ≤
        volume (trunc (C : Set (Euc d)) ℓ t) :=
    measure_mono (trunc_mono (C := (C : Set (Euc d)))
      (ℓ := ℓ) hst)
  have hdiv :
      volume (trunc (C : Set (Euc d)) ℓ s) /
          volume (C : Set (Euc d)) ≤
        volume (trunc (C : Set (Euc d)) ℓ t) /
          volume (C : Set (Euc d)) :=
    ENNReal.div_le_div_right hvol (volume (C : Set (Euc d)))
  have hfinite :
      volume (trunc (C : Set (Euc d)) ℓ t) /
          volume (C : Set (Euc d)) ≠ ⊤ :=
    ENNReal.div_ne_top
      (volume_trunc_ne_top (C := (C : Set (Euc d))) C.isCompact ℓ t)
      C.volume_ne_zero
  exact ENNReal.toReal_mono hfinite hdiv

/-- Raise a lower bound on the CDF root at the centroid and enlarge the
centroid cut to any containing halfspace. -/
theorem grunbaum_bound_of_cdfRoot {d : ℕ}
    (C : FullDimensionalConvexBody d)
    (ℓ : Euc d →L[ℝ] ℝ) (a : ℝ)
    (hcentroid : ℓ C.centroid ≤ a)
    (hroot :
      (((d + 1 : ℕ) : ℝ) / (d + 2 : ℕ)) ≤
        cdfRoot (C : Set (Euc d)) ℓ (ℓ C.centroid)) :
    grunbaumConstant d ≤ halfspaceVolumeRatio C ℓ a := by
  have hpow :
      (((d + 1 : ℕ) : ℝ) / (d + 2 : ℕ)) ^ (d + 1) ≤
        cdfRoot (C : Set (Euc d)) ℓ (ℓ C.centroid) ^ (d + 1) :=
    pow_le_pow_left₀ (by positivity) hroot (d + 1)
  rw [cdfRoot_pow_dimension] at hpow
  have hmono := truncVolumeRatio_mono C ℓ hcentroid
  simpa only [grunbaumConstant, halfspaceVolumeRatio, trunc,
    closedHalfspace] using hpow.trans hmono

end Grunbaum
