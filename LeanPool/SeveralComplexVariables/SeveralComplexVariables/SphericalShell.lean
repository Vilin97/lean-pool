/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Analysis.Connected
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.HartogsExtension

/-!
# Punctured polydiscs, spherical shells, and exteriors of balls

Punctured product polydiscs extend by the proved Hartogs continuity theorem, without boundedness
assumptions. A radial argument proves connectedness of norm shells; spherical shell extension is
then a corollary of the general compact-hole theorem. For Euclidean spheres instantiate the
source with `EuclideanSpace ℂ ι`, not the supremum norm on `ι → ℂ`. References:
[Korevaar–Wiegerinck][KorevaarWiegerinck2017] (2017), Applications 2.6.2 and 2.8.3.

## Main results

* `exists_extension_sphericalShell`: **Spherical-shell extension.** This works for any norm in
  finite complex dimension at least two.

## References

* [J. Korevaar and J. Wiegerinck, *Several Complex Variables*][KorevaarWiegerinck2017]
-/

public section

open Metric Set
open scoped Topology

namespace SeveralComplexVariables

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- An isolated puncture in a product polydisc is removable in complex dimension at least two. The
nonempty base index type makes the dimension restriction explicit. -/
theorem exists_extension_punctured_polydisc {ι : Type*} [Fintype ι] [Nonempty ι]
    {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    {f : ((ι → ℂ) × ℂ) → F}
    (hf : AnalyticOnNhd ℂ f ((ball 0 r ×ˢ ball 0 R) \ {0})) :
    ∃ g, AnalyticOnNhd ℂ g (ball 0 r ×ˢ ball 0 R) ∧
      EqOn g f ((ball 0 r ×ˢ ball 0 R) \ {0}) := by
  classical
  have he : hartogsCylinder (ball (0 : ι → ℂ) r) (ball 0 r \ {0}) 0 R =
      (ball 0 r ×ˢ ball 0 R) \ {0} := by
    ext ⟨z, w⟩
    simp only [hartogsCylinder, mem_union, mem_prod, mem_sdiff, closedBall_zero,
      mem_singleton_iff, Prod.zero_eq_mk, Prod.mk.injEq]
    tauto
  have hn : (ball (0 : ι → ℂ) r \ {0}).Nonempty := by
    refine ⟨fun _ => (r / 2 : ℂ), ?_, ?_⟩
    · rw [mem_ball, dist_pi_lt_iff hr]
      intro i
      simpa [abs_of_pos hr] using half_lt_self hr
    · intro hz
      have heq := congrFun hz (Classical.arbitrary ι)
      change (r / 2 : ℂ) = 0 at heq
      have : (r / 2 : ℝ) = 0 := by exact_mod_cast heq
      linarith
  obtain ⟨g, hg, heq⟩ := exists_extension_hartogsCylinder isOpen_ball isPreconnected_ball
    (isOpen_ball.sdiff isClosed_singleton) hn sdiff_subset (le_refl 0) hR (he ▸ hf)
  exact ⟨g, hg, he ▸ heq⟩

/-- **Spherical-shell extension.** This works for any norm in finite complex dimension at
least two. The proof applies the general compact-hole theorem. -/
theorem exists_extension_sphericalShell {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (hdim : 2 ≤ Module.finrank ℂ E)
    {ρ R : ℝ} (hρ : 0 ≤ ρ) (hρR : ρ < R) {f : E → F}
    (hf : AnalyticOnNhd ℂ f (ball 0 R \ closedBall 0 ρ)) :
    ∃ g, AnalyticOnNhd ℂ g (ball 0 R) ∧ EqOn g f (ball 0 R \ closedBall 0 ρ) := by
  let : ProperSpace E := FiniteDimensional.proper ℂ E
  have hdimR : 1 < Module.finrank ℝ E := by
    rw [← Module.finrank_mul_finrank ℝ ℂ E, Complex.finrank_real_complex]
    omega
  have hrank : 1 < Module.rank ℝ E := by
    rw [← Module.finrank_eq_rank]
    exact_mod_cast hdimR
  exact exists_analyticOnNhd_extension_of_isCompact hdim isOpen_ball
    (isCompact_closedBall 0 ρ) (closedBall_subset_ball hρR)
    (isPreconnected_ball_diff_closedBall_zero hrank hρ) hf

/-- The infinite-outer-radius case of shell extension: a function outside a closed ball extends to
the whole space. This follows from the compact-hole theorem and imposes no boundedness at
infinity or near the inner sphere. -/
theorem exists_extension_exterior_closedBall {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (hdim : 2 ≤ Module.finrank ℂ E) {ρ : ℝ} (hρ : 0 ≤ ρ)
    {f : E → F} (hf : AnalyticOnNhd ℂ f (closedBall (0 : E) ρ)ᶜ) :
    ∃ g, AnalyticOnNhd ℂ g univ ∧ EqOn g f (closedBall (0 : E) ρ)ᶜ := by
  let : ProperSpace E := FiniteDimensional.proper ℂ E
  have hdimR : 1 < Module.finrank ℝ E := by
    rw [← Module.finrank_mul_finrank ℝ ℂ E, Complex.finrank_real_complex]
    omega
  have hrank : 1 < Module.rank ℝ E := by
    rw [← Module.finrank_eq_rank]
    exact_mod_cast hdimR
  simpa only [← compl_eq_univ_sdiff] using exists_analyticOnNhd_extension_of_isCompact hdim
    isOpen_univ (isCompact_closedBall 0 ρ) (subset_univ _)
    (by simpa only [← compl_eq_univ_sdiff] using isPreconnected_compl_closedBall_zero hrank hρ)
    (by simpa only [← compl_eq_univ_sdiff] using hf)

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
