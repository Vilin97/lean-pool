/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step2.Interpolation
public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.Finiteness

/-!
# Cylinder energy estimates from decay

These estimates apply on backward cylinders, including cylinders with a fixed
top time. Their constants depend only on the given decay constant. They are
the scalar integral inputs for extension by zero across the top time face.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN.Core.Endgame

private theorem gradient_scale {M r : ℝ} (hr : 0 < r) :
    r * (M * r ^ (2 / 5 : ℝ)) ^ 2 = M ^ 2 * r ^ (9 / 5 : ℝ) := by
  have hp : (r ^ (2 / 5 : ℝ)) ^ 2 = r ^ (4 / 5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    norm_num
  rw [mul_pow, hp]
  calc
    r * (M ^ 2 * r ^ (4 / 5 : ℝ)) =
        M ^ 2 * (r ^ (1 : ℝ) * r ^ (4 / 5 : ℝ)) := by rw [Real.rpow_one]; ring
    _ = _ := by rw [← Real.rpow_add hr]; norm_num

private theorem pressure_scale {M r : ℝ} (hM : 0 ≤ M) (hr : 0 < r) :
    r ^ 2 * (M * r ^ (2 / 5 : ℝ)) ^ (3 / 2 : ℝ) =
      M ^ (3 / 2 : ℝ) * r ^ (13 / 5 : ℝ) := by
  rw [Real.mul_rpow hM (Real.rpow_nonneg hr.le _), ← Real.rpow_mul hr.le]
  norm_num
  calc
    r ^ 2 * (M ^ (3 / 2 : ℝ) * r ^ (3 / 5 : ℝ)) =
        M ^ (3 / 2 : ℝ) * (r ^ (2 : ℝ) * r ^ (3 / 5 : ℝ)) := by
      rw [Real.rpow_two]; ring
    _ = _ := by rw [← Real.rpow_add hr]; norm_num

/-- The Dirichlet energy has cylinder growth exponent `9/5`, corresponding
to scalar Morrey exponents `P = 2`, `τ = 25/8`. -/
theorem cylinder_gradient_energy_of_decay (M : ℝ) (hM : 0 ≤ M)
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hsub : closure (parabolicCylinder z.1 z.2 r) ⊆ spaceTimeSet Ω I)
    (hdec : max (max (alpha u z r) (beta u Du z r)) (delta p z r ^ 2) ≤
      M * r ^ (2 / 5 : ℝ)) :
    (∫⁻ w in parabolicCylinder z.1 z.2 r, ENNReal.ofReal (spatialGradientSq u Du w)) ≤
      ENNReal.ofReal (M ^ 2) * ENNReal.ofReal (r ^ (9 / 5 : ℝ)) := by
  have hb : beta u Du z r ≤ M * r ^ (2 / 5 : ℝ) :=
    (le_max_right _ _).trans ((le_max_left _ _).trans hdec)
  have hb0 : 0 ≤ beta u Du z r := by unfold beta; positivity
  have hb2 := (sq_le_sq₀ hb0 (mul_nonneg hM (Real.rpow_nonneg hr.le _))).mpr hb
  rw [sws_lintegral_spatialGradientSq_eq_ofReal_beta_sq hsol z hr hsub,
    ← ENNReal.ofReal_mul (sq_nonneg M)]
  apply ENNReal.ofReal_le_ofReal
  calc
    r * beta u Du z r ^ 2 ≤ r * (M * r ^ (2 / 5 : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_left hb2 hr.le
    _ = _ := gradient_scale hr

/-- Every scalar spatial derivative has the same uniform cylinder bound. -/
theorem cylinder_gradient_component_of_decay (M : ℝ) (hM : 0 ≤ M)
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hsub : closure (parabolicCylinder z.1 z.2 r) ⊆ spaceTimeSet Ω I)
    (hdec : max (max (alpha u z r) (beta u Du z r)) (delta p z r ^ 2) ≤
      M * r ^ (2 / 5 : ℝ)) (i j : Fin 3) :
    (∫⁻ w in parabolicCylinder z.1 z.2 r, ENNReal.ofReal |Du w i j| ^ (2 : ℝ)) ≤
      ENNReal.ofReal (M ^ 2) * ENNReal.ofReal (r ^ (9 / 5 : ℝ)) := by
  refine le_trans (lintegral_mono (fun w => ?_))
    (cylinder_gradient_energy_of_decay M hM hsol hr hsub hdec)
  rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  have hc : (Du w i j) ^ 2 ≤ spatialGradientSq u Du w := by
    unfold spatialGradientSq
    exact (Finset.single_le_sum (fun k _ => sq_nonneg (Du w i k))
      (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun k _ => Finset.sum_nonneg
        (fun l _ => sq_nonneg (Du w k l))) (Finset.mem_univ i))
  simpa only [Real.rpow_two, sq_abs] using hc

/-- Pressure has cylinder growth exponent `13/5`, corresponding to
`P = 3/2`, `τ = 25/8`. -/
theorem cylinder_pressure_of_decay (M : ℝ) (hM : 0 ≤ M)
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hsub : closure (parabolicCylinder z.1 z.2 r) ⊆ spaceTimeSet Ω I)
    (hdec : max (max (alpha u z r) (beta u Du z r)) (delta p z r ^ 2) ≤
      M * r ^ (2 / 5 : ℝ)) :
    (∫⁻ w in parabolicCylinder z.1 z.2 r, ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)) ≤
      ENNReal.ofReal (M ^ (3 / 2 : ℝ)) * ENNReal.ofReal (r ^ (13 / 5 : ℝ)) := by
  have hd : delta p z r ^ 2 ≤ M * r ^ (2 / 5 : ℝ) := (le_max_right _ _).trans hdec
  have hd0 : 0 ≤ delta p z r := by unfold delta; positivity
  have hcube : delta p z r ^ 3 ≤ (M * r ^ (2 / 5 : ℝ)) ^ (3 / 2 : ℝ) := by
    calc
      _ = (delta p z r ^ 2) ^ (3 / 2 : ℝ) := by
        rw [show delta p z r ^ 2 = delta p z r ^ (2 : ℝ) by
          norm_num [Real.rpow_natCast], ← Real.rpow_mul hd0]
        norm_num [Real.rpow_natCast]
      _ ≤ _ := Real.rpow_le_rpow (sq_nonneg _) hd (by norm_num)
  rw [sws_lintegral_abs_pow_eq_ofReal_delta_cube hsol z hr hsub,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hM _)]
  apply ENNReal.ofReal_le_ofReal
  calc
    r ^ 2 * delta p z r ^ 3 ≤ r ^ 2 * (M * r ^ (2 / 5 : ℝ)) ^ (3 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left hcube (sq_nonneg r)
    _ = _ := pressure_scale hM hr

private theorem velocity_scale {A r : ℝ} (hr : 0 < r) :
    r ^ 2 * (A * r ^ (2 / 5 : ℝ)) ^ 3 = A ^ 3 * r ^ (16 / 5 : ℝ) := by
  have hp : (r ^ (2 / 5 : ℝ)) ^ 3 = r ^ (6 / 5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    norm_num
  rw [mul_pow, hp]
  calc
    r ^ 2 * (A ^ 3 * r ^ (6 / 5 : ℝ)) =
        A ^ 3 * (r ^ (2 : ℝ) * r ^ (6 / 5 : ℝ)) := by rw [Real.rpow_two]; ring
    _ = _ := by rw [← Real.rpow_add hr]; norm_num

/-- Cubic velocity energy has growth exponent `16/5`. Finiteness is obtained
from suitable-solution energy before using the real-valued normalization. -/
theorem cylinder_velocity_energy_of_decay (M : ℝ) (hM : 0 ≤ M)
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hsub : closure (parabolicCylinder z.1 z.2 r) ⊆ spaceTimeSet Ω I)
    (hdec : max (max (alpha u z r) (beta u Du z r)) (delta p z r ^ 2) ≤
      M * r ^ (2 / 5 : ℝ)) :
    (∫⁻ w in parabolicCylinder z.1 z.2 r,
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ≤
      ENNReal.ofReal ((2 * gagliardoConstant * M) ^ 3) *
        ENNReal.ofReal (r ^ (16 / 5 : ℝ)) := by
  let A := M * r ^ (2 / 5 : ℝ)
  have hA : 0 ≤ A := mul_nonneg hM (Real.rpow_nonneg hr.le _)
  have hα : alpha u z r ≤ A :=
    (le_max_left _ _).trans ((le_max_left _ _).trans hdec)
  have hβ : beta u Du z r ≤ A :=
    (le_max_right _ _).trans ((le_max_left _ _).trans hdec)
  have hα0 : 0 ≤ alpha u z r := by unfold alpha; positivity
  have hβ0 : 0 ≤ beta u Du z r := by unfold beta; positivity
  have hC : 0 ≤ gagliardoConstant := by unfold gagliardoConstant; positivity
  have hprod : alpha u z r ^ (1 / 2 : ℝ) * beta u Du z r ^ (1 / 2 : ℝ) ≤ A := by
    calc
      _ ≤ A ^ (1 / 2 : ℝ) * A ^ (1 / 2 : ℝ) :=
        mul_le_mul (Real.rpow_le_rpow hα0 hα (by norm_num))
          (Real.rpow_le_rpow hβ0 hβ (by norm_num)) (by positivity) (by positivity)
      _ = A := by rw [← Real.sqrt_eq_rpow, Real.mul_self_sqrt hA]
  have hγ : gamma u z r ≤ 2 * gagliardoConstant * A := by
    have hi := gamma_le_gagliardo_of_sws hsol hr hsub
    have ht := mul_le_mul_of_nonneg_left hprod hC
    have ha := mul_le_mul_of_nonneg_left hα hC
    nlinarith only [hi, ht, ha]
  let IU := ∫⁻ w in parabolicCylinder z.1 z.2 r,
    ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)
  have hfinite : IU ≠ ∞ := caccioppoli_velocity_integral_ne_top hsol hr hsub
  have hIUreal : IU.toReal = r ^ (2 : ℝ) * gamma u z r ^ 3 := by
    have hcube : gamma u z r ^ 3 = r ^ (-2 : ℝ) * IU.toReal := gamma_cube_eq u z r hr
    rw [hcube, ← mul_assoc, ← Real.rpow_add hr]
    norm_num
  have hγ0 : 0 ≤ gamma u z r := by unfold gamma; positivity
  have hbound : IU ≤ ENNReal.ofReal (r ^ 2 * (2 * gagliardoConstant * A) ^ 3) := by
    apply (ENNReal.toReal_le_toReal hfinite ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal (by positivity), hIUreal, Real.rpow_two]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hγ0 hγ 3) (sq_nonneg r)
  calc
    _ ≤ ENNReal.ofReal (r ^ 2 * (2 * gagliardoConstant * A) ^ 3) := hbound
    _ = ENNReal.ofReal ((2 * gagliardoConstant * M) ^ 3) *
        ENNReal.ofReal (r ^ (16 / 5 : ℝ)) := by
      dsimp only [A]
      rw [← mul_assoc (2 * gagliardoConstant) M, velocity_scale hr,
        ENNReal.ofReal_mul (by positivity)]

/-- Each scalar velocity component has the cubic cylinder bound corresponding
to `P = 3`, `τ = 25/3`. -/
theorem cylinder_velocity_component_of_decay (M : ℝ) (hM : 0 ≤ M)
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hsub : closure (parabolicCylinder z.1 z.2 r) ⊆ spaceTimeSet Ω I)
    (hdec : max (max (alpha u z r) (beta u Du z r)) (delta p z r ^ 2) ≤
      M * r ^ (2 / 5 : ℝ)) (i : Fin 3) :
    (∫⁻ w in parabolicCylinder z.1 z.2 r, ENNReal.ofReal |u w i| ^ (3 : ℝ)) ≤
      ENNReal.ofReal ((2 * gagliardoConstant * M) ^ 3) *
        ENNReal.ofReal (r ^ (16 / 5 : ℝ)) := by
  refine le_trans (lintegral_mono (fun w => ?_))
    (cylinder_velocity_energy_of_decay M hM hsol hr hsub hdec)
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  apply ENNReal.ofReal_le_ofReal
  unfold vec3EuclideanNorm
  exact Real.abs_le_sqrt (Finset.single_le_sum
    (fun j _ => sq_nonneg (u w j)) (Finset.mem_univ i))

end CKN.Core.Endgame
