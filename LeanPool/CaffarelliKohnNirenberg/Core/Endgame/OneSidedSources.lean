/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.OneSidedEnergy
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.OneSidedMorrey

/-!
# Uniform one-sided velocity and pressure Morrey bounds

Small-cylinder estimates follow from decay. Large-cylinder estimates use
the original unit-cylinder small-data hypothesis, so the constants are
independent of the solution. Both estimates concern extension by zero from
the intermediate backward cylinder of radius `5/8`.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey


noncomputable section

namespace CKN.Core.Endgame

/-- Quarter-scale cylinders centered in the three-quarter cylinder have
closure in the closed unit cylinder. -/
theorem closure_small_cylinder_subset_unit
    {z : ParabolicPoint} {r : ℝ}
    (hz : z ∈ parabolicCylinder (0 : Vec3) 0 (3 / 4))
    (hr : 0 ≤ r) (hrquarter : r ≤ 1 / 4) :
    closure (parabolicCylinder z.1 z.2 r) ⊆
      closure (parabolicCylinder (0 : Vec3) 0 1) := by
  apply (closure_parabolicCylinder_mono hr hrquarter).trans
  apply closure_mono
  intro w hw
  rcases hz with ⟨hzx, hzt⟩
  rcases hw with ⟨hwx, hwt⟩
  refine ⟨?_, ?_⟩
  · change vec3EuclideanNorm (w.1 - 0) < 1
    rw [sub_zero]
    have htriangle : vec3EuclideanNorm w.1 ≤
        vec3EuclideanNorm (w.1 - z.1) + vec3EuclideanNorm z.1 := by
      simpa only [vec3EuclideanNorm_eq_l2, WithLp.toLp_sub, sub_add_cancel] using
        (norm_add_le (WithLp.toLp 2 (w.1 - z.1)) (WithLp.toLp 2 z.1))
    have hwx' : vec3EuclideanNorm (w.1 - z.1) < 1 / 4 := hwx
    have hzx' : vec3EuclideanNorm z.1 < 3 / 4 := by
      simpa only [mem_vec3Ball, sub_zero] using hzx
    linarith only [htriangle, hwx', hzx']
  · refine ⟨?_, hwt.2.trans hzt.2⟩
    have ht := hwt.1
    have hzlow := hzt.1
    norm_num at ht hzlow ⊢
    linarith only [ht, hzlow]

/-- The explicit uniform velocity Morrey constant. -/
@[expose] def oneSidedVelocityMorreyBound (M r₀ ε₀ : ℝ) : ℝ≥0∞ :=
  oneSidedMorreyBound 3 (25 / 3) r₀
    (ENNReal.ofReal ((2 * gagliardoConstant * M) ^ 3)) (ENNReal.ofReal ε₀)

/-- The explicit uniform pressure Morrey constant. -/
@[expose] def oneSidedPressureMorreyBound (M r₀ ε₀ : ℝ) : ℝ≥0∞ :=
  oneSidedMorreyBound (3 / 2) (25 / 8) r₀
    (ENNReal.ofReal (M ^ (3 / 2 : ℝ))) (ENNReal.ofReal ε₀)

/-- The velocity constant is finite. -/
theorem oneSidedVelocityMorreyBound_lt_top (M r₀ ε₀ : ℝ) :
    oneSidedVelocityMorreyBound M r₀ ε₀ < ⊤ :=
  oneSidedMorreyBound_lt_top (by norm_num) ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-- The pressure constant is finite. -/
theorem oneSidedPressureMorreyBound_lt_top (M r₀ ε₀ : ℝ) :
    oneSidedPressureMorreyBound M r₀ ε₀ < ⊤ :=
  oneSidedMorreyBound_lt_top (by norm_num) ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-- Uniform scalar velocity Morrey control follows from one-sided decay and
the original unit-cylinder smallness hypothesis. -/
theorem oneSided_velocity_morrey_of_decay
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
      ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator (fun z => u z i)) ≤
        oneSidedVelocityMorreyBound M r₀ ε₀ := by
  apply morreyNorm_one_sided_indicator_le 3 (25 / 3) r₀
    (ENNReal.ofReal ((2 * gagliardoConstant * M) ^ 3)) (ENNReal.ofReal ε₀)
    (by norm_num) (by norm_num) hr₀
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
      _ ≤ ∫⁻ z in parabolicCylinder (0 : Vec3) 0 (5 / 8),
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
theorem oneSided_pressure_morrey_of_decay
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
      ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator p) ≤
        oneSidedPressureMorreyBound M r₀ ε₀ := by
  apply morreyNorm_one_sided_indicator_le (3 / 2) (25 / 8) r₀
    (ENNReal.ofReal (M ^ (3 / 2 : ℝ))) (ENNReal.ofReal ε₀)
    (by norm_num) (by norm_num) hr₀
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

end CKN.Core.Endgame
