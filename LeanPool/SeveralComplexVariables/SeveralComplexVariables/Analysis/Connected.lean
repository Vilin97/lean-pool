/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Normed.Module.Connected

/-!
# Connectedness of shells and exteriors of balls

In a real normed space of dimension at least two, spherical shells and exteriors of closed balls
centered at the origin are preconnected. The proofs are radial: a shell is the image of the product
of an interval and the unit sphere.

## Main results

* `isPreconnected_ball_diff_closedBall_zero`: A shell in a real normed space of dimension at least
  two is preconnected.
* `isPreconnected_compl_closedBall_zero`: The exterior of a closed norm ball is preconnected in
  real dimension at least two.
-/

public section

open Metric Set

/-- A shell in a real normed space of dimension at least two is preconnected. This radial argument
is independent of any analytic extension theorem. -/
theorem isPreconnected_ball_diff_closedBall_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (hdim : 1 < Module.rank ℝ E) {ρ R : ℝ} (hρ : 0 ≤ ρ) :
    IsPreconnected (ball (0 : E) R \ closedBall 0 ρ) := by
  let A : Set (ℝ × E) := Ioo ρ R ×ˢ sphere 0 1
  have hA : IsPreconnected A := isPreconnected_Ioo.prod
    (isPreconnected_sphere hdim (0 : E) 1)
  have hc : Continuous (fun p : ℝ × E => p.1 • p.2) := continuous_fst.smul continuous_snd
  have he : (fun p : ℝ × E => p.1 • p.2) '' A = ball (0 : E) R \ closedBall 0 ρ := by
    apply Subset.antisymm
    · rintro z ⟨⟨t, v⟩, ⟨ht, hv⟩, rfl⟩
      have hvn : ‖v‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hv
      have htn : 0 < t := hρ.trans_lt ht.1
      simpa [mem_ball, mem_closedBall, dist_zero_right, norm_smul,
        Real.norm_of_nonneg htn.le, hvn] using ⟨ht.2, ht.1⟩
    · intro z hz
      have hzR : ‖z‖ < R := by simpa [mem_ball, dist_zero_right] using hz.1
      have hzρ : ρ < ‖z‖ := by simpa [mem_closedBall, dist_zero_right] using hz.2
      have hn : 0 < ‖z‖ := hρ.trans_lt hzρ
      refine ⟨(‖z‖, ‖z‖⁻¹ • z), ⟨⟨hzρ, hzR⟩, ?_⟩, ?_⟩
      · simp [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hn.le),
          inv_mul_cancel₀ hn.ne']
      · simp [smul_smul, mul_inv_cancel₀ hn.ne']
  rw [← he]
  exact hA.image _ hc.continuousOn

/-- The exterior of a closed norm ball is preconnected in real dimension at least two. It is the
directed union of the finite shells. -/
theorem isPreconnected_compl_closedBall_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hdim : 1 < Module.rank ℝ E) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    IsPreconnected ((closedBall (0 : E) ρ)ᶜ) := by
  have h : IsPreconnected (⋃ n : ℕ, ball (0 : E) (n : ℝ) \ closedBall 0 ρ) := by
    rw [← sUnion_range]
    apply IsPreconnected.sUnion_directed
    · rintro s ⟨n, rfl⟩ t ⟨m, rfl⟩
      refine ⟨ball (0 : E) ((max n m : ℕ) : ℝ) \ closedBall 0 ρ, ⟨max n m, rfl⟩, ?_, ?_⟩
      · exact sdiff_subset_sdiff_left (ball_subset_ball (by exact_mod_cast le_max_left n m))
      · exact sdiff_subset_sdiff_left (ball_subset_ball (by exact_mod_cast le_max_right n m))
    · rintro s ⟨n, rfl⟩
      exact isPreconnected_ball_diff_closedBall_zero hdim hρ
  simpa only [← iUnion_sdiff, iUnion_ball_nat, ← compl_eq_univ_sdiff] using h

end

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
