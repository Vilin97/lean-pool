/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.OneSidedGradient

/-!
# Initial Morrey estimates on a larger interior cylinder

The initial velocity, pressure, and gradient estimates extend by zero from
the cylinder of radius eleven sixteenths. The numerical bounds agree with
the smaller-cylinder estimates; the gradient covering number is selected
before the domain and solution.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey


noncomputable section

namespace CKN.Core.Endgame

/-- Uniform scalar velocity Morrey control follows from one-sided decay and
the original unit-cylinder smallness hypothesis. -/
theorem wide_velocity_morrey_of_decay
    (M r₀ ε₀ : ℝ) (hM : 0 ≤ M) (hr₀ : 0 < r₀) (hrquarter : r₀ ≤ 1 / 4)
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hQ₁ : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hdata : (∫⁻ z in parabolicCylinder (0 : Vec3) 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε₀)
    (hdec : ∀ z ∈ parabolicCylinder (0 : Vec3) 0 (3 / 4),
      ∀ r : ℝ, 0 < r → r ≤ r₀ →
        max (max (alpha u z r) (beta u Du z r)) (delta p z r ^ 2) ≤
          M * r ^ (2 / 5 : ℝ)) (i : Fin 3) :
    morreyNorm 3 (25 / 3 : ℝ)
      ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator (fun z => u z i)) ≤
        oneSidedVelocityMorreyBound M r₀ ε₀ := by
  apply morreyNorm_one_sided_indicator_le_on_cylinder (11 / 16) 3 (25 / 3) r₀
    (ENNReal.ofReal ((2 * gagliardoConstant * M) ^ 3)) (ENNReal.ofReal ε₀)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hr₀
  · intro z hz r hr hrr
    have hsub := (closure_small_cylinder_subset_unit hz hr.le (hrr.trans hrquarter)).trans hQ₁
    have he := cylinder_velocity_component_of_decay M hM hsol hr hsub (hdec z hz r hr hrr) i
    norm_num only [show (5 * (1 - 3 / (25 / 3)) : ℝ) = 16 / 5 by norm_num]
    exact he
  · have hcomponent : ∀ z, ENNReal.ofReal |u z i| ^ (3 : ℝ) ≤
        ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) := by
      intro z
      apply ENNReal.rpow_le_rpow _ (by norm_num)
      apply ENNReal.ofReal_le_ofReal
      exact Real.abs_le_sqrt (Finset.single_le_sum
        (fun j _ => sq_nonneg (u z j)) (Finset.mem_univ i))
    calc
      _ ≤ ∫⁻ z in parabolicCylinder (0 : Vec3) 0 (11 / 16),
          ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) := lintegral_mono hcomponent
      _ ≤ ∫⁻ z in parabolicCylinder (0 : Vec3) 0 1,
          ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) :=
        lintegral_mono_set (parabolicCylinder_mono (by norm_num) (by norm_num))
      _ ≤ ∫⁻ z in parabolicCylinder (0 : Vec3) 0 1,
          ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
            ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
            ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q :=
        lintegral_mono (fun z => (le_add_right le_rfl).trans (le_add_right le_rfl))
      _ ≤ _ := hdata

/-- Uniform pressure Morrey control follows from one-sided decay and the
original unit-cylinder smallness hypothesis. -/
theorem wide_pressure_morrey_of_decay
    (M r₀ ε₀ : ℝ) (hM : 0 ≤ M) (hr₀ : 0 < r₀) (hrquarter : r₀ ≤ 1 / 4)
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hQ₁ : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hdata : (∫⁻ z in parabolicCylinder (0 : Vec3) 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε₀)
    (hdec : ∀ z ∈ parabolicCylinder (0 : Vec3) 0 (3 / 4),
      ∀ r : ℝ, 0 < r → r ≤ r₀ →
        max (max (alpha u z r) (beta u Du z r)) (delta p z r ^ 2) ≤
          M * r ^ (2 / 5 : ℝ)) :
    morreyNorm (3 / 2 : ℝ) (25 / 8 : ℝ)
      ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator p) ≤
        oneSidedPressureMorreyBound M r₀ ε₀ := by
  apply morreyNorm_one_sided_indicator_le_on_cylinder (11 / 16) (3 / 2) (25 / 8) r₀
    (ENNReal.ofReal (M ^ (3 / 2 : ℝ))) (ENNReal.ofReal ε₀)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hr₀
  · intro z hz r hr hrr
    have hsub := (closure_small_cylinder_subset_unit hz hr.le (hrr.trans hrquarter)).trans hQ₁
    have he := cylinder_pressure_of_decay M hM hsol hr hsub (hdec z hz r hr hrr)
    norm_num only [show (5 * (1 - (3 / 2) / (25 / 8)) : ℝ) = 13 / 5 by norm_num]
    exact he
  · calc
      _ ≤ ∫⁻ z in parabolicCylinder (0 : Vec3) 0 1,
          ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) :=
        lintegral_mono_set (parabolicCylinder_mono (by norm_num) (by norm_num))
      _ ≤ ∫⁻ z in parabolicCylinder (0 : Vec3) 0 1,
          ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
            ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
            ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q :=
        lintegral_mono (fun z => (le_add_left le_rfl).trans (le_add_right le_rfl))
      _ ≤ _ := hdata

/-- Uniform decay gives a quantitative gradient Morrey bound. The covering
number is chosen before all domains and solutions. -/
theorem wide_gradient_morrey_of_decay
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
        ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator (fun z => Du z i j)) ≤
          oneSidedGradientMorreyBound M r₀ N := by
  obtain ⟨N, hcover⟩ := exists_one_sided_integral_constant_on_cylinder
    (11 / 16) r₀ (by norm_num) (by norm_num) hr₀
  refine ⟨N, ?_⟩
  intro Ω I q u Du p f hsol hQ₁ hdec i j
  have hsmall : ∀ z ∈ parabolicCylinder (0 : Vec3) 0 (3 / 4),
      ∀ r : ℝ, 0 < r → r ≤ r₀ →
        cylinderPowerIntegral 2 (fun w => Du w i j) z r ≤
          ENNReal.ofReal (M ^ 2) * ENNReal.ofReal (r ^ (9 / 5 : ℝ)) := by
    intro z hz r hr hrr
    have hsub := (closure_small_cylinder_subset_unit hz hr.le (hrr.trans hrquarter)).trans hQ₁
    exact cylinder_gradient_component_of_decay M hM hsol hr hsub (hdec z hz r hr hrr) i j
  apply morreyNorm_one_sided_indicator_le_on_cylinder (11 / 16) 2 (25 / 8) r₀ (ENNReal.ofReal (M ^
    2))
    ((N : ℝ≥0∞) * (ENNReal.ofReal (M ^ 2) * ENNReal.ofReal ((r₀ / 2) ^ (9 / 5 : ℝ))))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hr₀
  · intro z hz r hr hrr
    norm_num only [show (5 * (1 - 2 / (25 / 8)) : ℝ) = 9 / 5 by norm_num]
    exact hsmall z hz r hr hrr
  · apply hcover (fun w => ENNReal.ofReal |Du w i j| ^ (2 : ℝ))
      (ENNReal.ofReal (M ^ 2) * ENNReal.ofReal ((r₀ / 2) ^ (9 / 5 : ℝ)))
    intro z hz
    exact hsmall z hz (r₀ / 2) (by positivity) (by linarith only [hr₀])

/-- The three initial Morrey estimates on the larger interior cylinder have
uniform numerical bounds and a covering number independent of the solution. -/
theorem wide_initial_morrey_of_decay
    (M r₀ ε₀ : ℝ) (hM : 0 ≤ M) (hr₀ : 0 < r₀) (hrquarter : r₀ ≤ 1 / 4) :
    ∃ N : ℕ, ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
      {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
      closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I →
      (∫⁻ z in parabolicCylinder (0 : Vec3) 0 1,
        ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
          ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
          ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε₀ →
      (∀ z ∈ parabolicCylinder (0 : Vec3) 0 (3 / 4),
        ∀ r : ℝ, 0 < r → r ≤ r₀ →
          max (max (alpha u z r) (beta u Du z r)) (delta p z r ^ 2) ≤
            M * r ^ (2 / 5 : ℝ)) →
      (∀ i : Fin 3, morreyNorm 3 (25 / 3 : ℝ)
        ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator (fun z => u z i)) ≤
          oneSidedVelocityMorreyBound M r₀ ε₀) ∧
      (∀ i j : Fin 3, morreyNorm 2 (25 / 8 : ℝ)
        ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator (fun z => Du z i j)) ≤
          oneSidedGradientMorreyBound M r₀ N) ∧
      morreyNorm (3 / 2 : ℝ) (25 / 8 : ℝ)
        ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator p) ≤
          oneSidedPressureMorreyBound M r₀ ε₀ := by
  obtain ⟨N, hgradient⟩ := wide_gradient_morrey_of_decay M r₀ hM hr₀ hrquarter
  refine ⟨N, ?_⟩
  intro Ω I q u Du p f hsol hQ₁ hdata hdec
  exact ⟨wide_velocity_morrey_of_decay M r₀ ε₀ hM hr₀ hrquarter hsol hQ₁ hdata hdec,
    hgradient hsol hQ₁ hdec,
    wide_pressure_morrey_of_decay M r₀ ε₀ hM hr₀ hrquarter hsol hQ₁ hdata hdec⟩

end CKN.Core.Endgame
