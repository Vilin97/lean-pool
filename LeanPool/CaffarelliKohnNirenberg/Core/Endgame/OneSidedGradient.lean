/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.OneSidedSources
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.OneSidedCover

/-!
# Uniform one-sided gradient Morrey bounds

A finite geometric cover bounds the total gradient integral using only
the small-cylinder decay constant. The cover is selected before the
solution, so no solution-dependent large-scale integral enters the bound.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey


noncomputable section

namespace CKN.Core.Endgame

/-- Gradient Morrey constant associated with a finite geometric cover. -/
@[expose] def oneSidedGradientMorreyBound (M r₀ : ℝ) (N : ℕ) : ℝ≥0∞ :=
  oneSidedMorreyBound 2 (25 / 8) r₀ (ENNReal.ofReal (M ^ 2))
    ((N : ℝ≥0∞) * (ENNReal.ofReal (M ^ 2) * ENNReal.ofReal ((r₀ / 2) ^ (9 / 5 : ℝ))))

/-- Every finite cover gives a finite quantitative gradient bound. -/
theorem oneSidedGradientMorreyBound_lt_top (M r₀ : ℝ) (N : ℕ) :
    oneSidedGradientMorreyBound M r₀ N < ⊤ := by
  apply oneSidedMorreyBound_lt_top (by norm_num) ENNReal.ofReal_lt_top
  exact ENNReal.mul_lt_top (by simp only [ENNReal.natCast_lt_top])
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)

/-- Uniform decay gives a quantitative gradient Morrey bound. The covering
number is chosen before all domains and solutions. -/
theorem oneSided_gradient_morrey_of_decay
    (M r₀ : ℝ) (hM : 0 ≤ M) (hr₀ : 0 < r₀) (hrquarter : r₀ ≤ 1 / 4) :
    ∃ N : ℕ, ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
      {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
      closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I →
      (∀ z ∈ parabolicCylinder (0 : Vec3) 0 (3 / 4),
        ∀ r : ℝ, 0 < r → r ≤ r₀ →
          max (max (alpha u z r) (beta u Du z r)) (delta p z r ^ 2) ≤
            M * r ^ (2 / 5 : ℝ)) →
      ∀ i j : Fin 3, morreyNorm 2 (25 / 8 : ℝ)
        ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator (fun z => Du z i j)) ≤
          oneSidedGradientMorreyBound M r₀ N := by
  obtain ⟨N, hcover⟩ := exists_one_sided_integral_constant r₀ hr₀
  refine ⟨N, ?_⟩
  intro Ω I q u Du p f hsol hQ₁ hdec i j
  have hsmall : ∀ z ∈ parabolicCylinder (0 : Vec3) 0 (3 / 4),
      ∀ r : ℝ, 0 < r → r ≤ r₀ →
        cylinderPowerIntegral 2 (fun w => Du w i j) z r ≤
          ENNReal.ofReal (M ^ 2) * ENNReal.ofReal (r ^ (9 / 5 : ℝ)) := by
    intro z hz r hr hrr
    have hsub := (closure_small_cylinder_subset_unit hz hr.le (hrr.trans hrquarter)).trans hQ₁
    exact cylinder_gradient_component_of_decay M hM hsol hr hsub (hdec z hz r hr hrr) i j
  apply morreyNorm_one_sided_indicator_le 2 (25 / 8) r₀ (ENNReal.ofReal (M ^ 2))
    ((N : ℝ≥0∞) * (ENNReal.ofReal (M ^ 2) * ENNReal.ofReal ((r₀ / 2) ^ (9 / 5 : ℝ))))
    (by norm_num) (by norm_num) hr₀
  · intro z hz r hr hrr
    norm_num only [show (5 * (1 - 2 / (25 / 8)) : ℝ) = 9 / 5 by norm_num]
    exact hsmall z hz r hr hrr
  · apply hcover (fun w => ENNReal.ofReal |Du w i j| ^ (2 : ℝ))
      (ENNReal.ofReal (M ^ 2) * ENNReal.ofReal ((r₀ / 2) ^ (9 / 5 : ℝ)))
    intro z hz
    exact hsmall z hz (r₀ / 2) (by positivity) (by linarith only [hr₀])

end CKN.Core.Endgame
