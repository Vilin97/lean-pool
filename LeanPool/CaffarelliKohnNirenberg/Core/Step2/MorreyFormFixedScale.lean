/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step2.Interpolation
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Cylinders

/-!
# Morrey Form Fixed Scale

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration

noncomputable section
namespace CKN

private theorem gradient_scale_real_fixed {M R : ℝ} (_ : 0 ≤ M) (hR : 0 < R) :
    R * (M * R ^ (2 / 5 : ℝ)) ^ 2 = M ^ 2 * R ^ (9 / 5 : ℝ) := by
  have hpow : (R ^ (2 / 5 : ℝ)) ^ 2 = R ^ (4 / 5 : ℝ) := by
    rw [show (R ^ (2 / 5 : ℝ)) ^ 2 = (R ^ (2 / 5 : ℝ)) ^ (2 : ℝ) by
      norm_num [Real.rpow_natCast], ← Real.rpow_mul hR.le]
    norm_num
  rw [mul_pow, hpow]
  calc
    R * (M ^ 2 * R ^ (4 / 5 : ℝ)) = M ^ 2 * (R ^ (1 : ℝ) * R ^ (4 / 5 : ℝ)) := by
      rw [Real.rpow_one]
      ring
    _ = M ^ 2 * R ^ (9 / 5 : ℝ) := by
      rw [← Real.rpow_add hR]
      norm_num

private theorem pressure_scale_real_fixed {M R : ℝ} (hM : 0 ≤ M) (hR : 0 < R) :
    R ^ 2 * (M * R ^ (2 / 5 : ℝ)) ^ (3 / 2 : ℝ) =
      M ^ (3 / 2 : ℝ) * R ^ (13 / 5 : ℝ) := by
  rw [Real.mul_rpow hM (Real.rpow_nonneg hR.le _), ← Real.rpow_mul hR.le]
  norm_num
  calc
    R ^ 2 * (M ^ (3 / 2 : ℝ) * R ^ (3 / 5 : ℝ)) =
        M ^ (3 / 2 : ℝ) * (R ^ (2 : ℝ) * R ^ (3 / 5 : ℝ)) := by
      norm_num [Real.rpow_natCast]
      ring
    _ = M ^ (3 / 2 : ℝ) * R ^ (13 / 5 : ℝ) := by
      rw [← Real.rpow_add hR]
      norm_num

private theorem fixed_velocity_integral_lt_top
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {x : Vec3} {t r : ℝ} (hr : 0 < r)
    (hsub : closure (parabolicCylinder x t (2 * r)) ⊆ spaceTimeSet Ω I) :
    (∫⁻ w in parabolicCylinder x t r,
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) < ⊤ := by
  obtain ⟨Ω', J, hbox, hcyl⟩ := exists_localBox_of_closure_subset
    hsol.1 hsol.2.1 (by positivity) hsub
  have hEtop := sws_timeSliceEnergyEssSup_lt_top hsol (z := (x, t))
    (r := 2 * r) (by positivity) hsub
  have hG := sws_gradient_integral_lt_top hsol (z := (x, t))
    (r := 2 * r) (by positivity) hsub
  let E := essSup (fun s => ∫⁻ y in vec3Ball x (2 * r),
    ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ))
    (volume.restrict (Set.Ioc (t - r ^ 2) t))
  have hTsub : Set.Ioc (t - r ^ 2) t ⊆ Set.Ioc (t - (2 * r) ^ 2) t := by
    intro s hs
    exact ⟨by nlinarith only [hs.1, hr], hs.2⟩
  have hpoint : ∀ s, (∫⁻ y in vec3Ball x (2 * r),
      ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ)) ≤
      timeSliceBallEnergy x (2 * r) s (fun w => vec3EuclideanNorm (u w)) := by
    intro s
    apply le_of_eq
    apply lintegral_congr
    intro y
    rw [Real.enorm_eq_ofReal (vec3EuclideanNorm_nonneg (u (y, s)))]
  have hE : E < ⊤ := lt_of_le_of_lt
    (essSup_mono_measure_and_ae (Measure.restrict_mono_set volume hTsub)
      (Filter.Eventually.of_forall hpoint)) (by
        simpa [timeSliceEnergyEssSup] using hEtop)
  let A := E ^ (1 / 2 : ℝ) + 1
  let G := (∫⁻ w in parabolicCylinder x t (2 * r),
      ENNReal.ofReal (spatialGradientSq u Du w)) + 1
  have h := step2_cylinder_l3_bound hsol hr hbox hcyl (Abar := A) (Gbar := G)
    (by dsimp [A]; exact ENNReal.add_lt_top.mpr ⟨
      ENNReal.rpow_lt_top_of_nonneg (by positivity) hE.ne, ENNReal.coe_lt_top⟩)
    (by exact (by dsimp [A, E]; exact le_add_right le_rfl))
    (by dsimp [G]; exact le_add_right le_rfl)
  apply lt_of_le_of_lt h
  have hA : A < ⊤ := by
    dsimp [A]
    exact ENNReal.add_lt_top.mpr ⟨
      ENNReal.rpow_lt_top_of_nonneg (by positivity) hE.ne, ENNReal.coe_lt_top⟩
  have hG' : G < ⊤ := by
    dsimp [G]
    exact ENNReal.add_lt_top.mpr ⟨hG, ENNReal.coe_lt_top⟩
  have hC : (ENNReal.ofReal ((3 : ℝ) ^ ((3 : ℝ) / 2 - 1)) * 3) *
      localSobolevConstant ^ (3 / 2 : ℝ) < ⊤ := by
    apply ENNReal.mul_lt_top
    · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.coe_lt_top
    · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        (by unfold localSobolevConstant; finiteness)
  have hsum : G ^ (3 / 4 : ℝ) * ENNReal.ofReal (r ^ 2) ^ (1 / 4 : ℝ) +
      ENNReal.ofReal (r ^ 2) * ((Real.toNNReal (32 / r) : ℝ≥0∞) * A) ^
        (3 / 2 : ℝ) < ⊤ := by
    refine ENNReal.add_lt_top.mpr ⟨?_, ?_⟩
    · exact ENNReal.mul_lt_top
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hG'.ne)
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
    · apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        (ENNReal.mul_ne_top ENNReal.coe_ne_top hA.ne)
  apply ENNReal.mul_lt_top
  · exact ENNReal.mul_lt_top (ENNReal.mul_lt_top hC
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hA.ne))
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (by norm_num))
  · exact hsum

/-- Fixed-scale localized integrals are controlled by the decay certificate.
The scale and the constants in this statement are independent of the solution
and of the centre. -/
theorem step2_fixed_scale_integrals
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {R M : ℝ} (hR : 0 < R) (hM : 1 ≤ M)
    (hsub : closure (parabolicCylinder z.1 z.2 (2 * R)) ⊆ spaceTimeSet Ω I)
    (hdec : max (max (alpha u z R) (beta u Du z R)) (delta p z R ^ 2) ≤
      M * R ^ (2 / 5 : ℝ)) :
    (∫⁻ w in parabolicCylinder z.1 z.2 R,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ≤
        ENNReal.ofReal (R ^ (2 : ℝ) *
          (2 * gagliardoConstant * (M * R ^ (2 / 5 : ℝ))) ^ 3) ∧
      (∫⁻ w in parabolicCylinder z.1 z.2 R,
        ENNReal.ofReal (spatialGradientSq u Du w)) ≤
        ENNReal.ofReal (M ^ 2 * R ^ (9 / 5 : ℝ)) ∧
      (∫⁻ w in parabolicCylinder z.1 z.2 R,
        ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)) ≤
        ENNReal.ofReal (M ^ (3 / 2 : ℝ) * R ^ (13 / 5 : ℝ)) := by
  have hsubR : closure (parabolicCylinder z.1 z.2 R) ⊆ spaceTimeSet Ω I :=
    (closure_mono (parabolicCylinder_mono (by positivity) (by nlinarith only [hR]))).trans hsub
  have hA : 0 ≤ M * R ^ (2 / 5 : ℝ) := by positivity
  have hα : alpha u z R ≤ M * R ^ (2 / 5 : ℝ) :=
    (le_max_left _ _).trans ((le_max_left _ _).trans hdec)
  have hβ : beta u Du z R ≤ M * R ^ (2 / 5 : ℝ) :=
    (le_max_right _ _).trans ((le_max_left _ _).trans hdec)
  have hδsq : delta p z R ^ 2 ≤ M * R ^ (2 / 5 : ℝ) :=
    (le_max_right _ _).trans hdec
  have hα0 : 0 ≤ alpha u z R := by unfold alpha; positivity
  have hβ0 : 0 ≤ beta u Du z R := by unfold beta; positivity
  have hC : 0 ≤ gagliardoConstant := by
    unfold gagliardoConstant
    positivity
  have hγ := gamma_le_gagliardo_of_sws hsol hR hsubR
  have hαroot : alpha u z R ^ (1 / 2 : ℝ) ≤
      (M * R ^ (2 / 5 : ℝ)) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow hα0 hα (by norm_num)
  have hβroot : beta u Du z R ^ (1 / 2 : ℝ) ≤
      (M * R ^ (2 / 5 : ℝ)) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow hβ0 hβ (by norm_num)
  have hprod : alpha u z R ^ (1 / 2 : ℝ) * beta u Du z R ^ (1 / 2 : ℝ) ≤
      (M * R ^ (2 / 5 : ℝ)) ^ (1 / 2 : ℝ) *
        (M * R ^ (2 / 5 : ℝ)) ^ (1 / 2 : ℝ) :=
    mul_le_mul hαroot hβroot (by positivity) (by positivity)
  have hApos : 0 < M * R ^ (2 / 5 : ℝ) := by positivity
  have hγbound : gamma u z R ≤ 2 * gagliardoConstant *
      (M * R ^ (2 / 5 : ℝ)) := by
    calc
      _ ≤ gagliardoConstant * alpha u z R ^ (1 / 2 : ℝ) *
          beta u Du z R ^ (1 / 2 : ℝ) + gagliardoConstant * alpha u z R := hγ
      _ ≤ gagliardoConstant * ((M * R ^ (2 / 5 : ℝ)) ^ (1 / 2 : ℝ) *
          (M * R ^ (2 / 5 : ℝ)) ^ (1 / 2 : ℝ)) +
          gagliardoConstant * (M * R ^ (2 / 5 : ℝ)) := by
        exact add_le_add
          (by simpa only [mul_assoc] using (mul_le_mul_of_nonneg_left hprod hC))
          (mul_le_mul_of_nonneg_left hα hC)
      _ = 2 * gagliardoConstant * (M * R ^ (2 / 5 : ℝ)) := by
        rw [← Real.rpow_add hApos]
        norm_num
        ring
  have hγ0 : 0 ≤ gamma u z R := by unfold gamma; positivity
  have hIU : (∫⁻ w in parabolicCylinder z.1 z.2 R,
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ≤
        ENNReal.ofReal (R ^ (2 : ℝ) *
          (2 * gagliardoConstant * (M * R ^ (2 / 5 : ℝ))) ^ 3) := by
    have hIUtop : (∫⁻ w in parabolicCylinder z.1 z.2 R,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) < ⊤ :=
      fixed_velocity_integral_lt_top hsol hR hsub
    have hγcube : gamma u z R ^ 3 = R ^ (-2 : ℝ) *
        (∫⁻ w in parabolicCylinder z.1 z.2 R,
          ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)).toReal := by
      exact gamma_cube_eq u z R hR
    have hIUreal : (∫⁻ w in parabolicCylinder z.1 z.2 R,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)).toReal =
        R ^ (2 : ℝ) * gamma u z R ^ 3 := by
      calc
        _ = (R ^ (2 : ℝ) * R ^ (-2 : ℝ)) *
            (∫⁻ w in parabolicCylinder z.1 z.2 R,
              ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)).toReal := by
          rw [← Real.rpow_add hR]
          norm_num
        _ = R ^ (2 : ℝ) * (R ^ (-2 : ℝ) *
            (∫⁻ w in parabolicCylinder z.1 z.2 R,
              ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)).toReal) := by
          rw [mul_assoc]
        _ = _ := by rw [← hγcube]
    have hcube : gamma u z R ^ 3 ≤
        (2 * gagliardoConstant * (M * R ^ (2 / 5 : ℝ))) ^ 3 :=
      pow_le_pow_left₀ hγ0 hγbound 3
    apply (ENNReal.toReal_le_toReal hIUtop.ne ENNReal.ofReal_ne_top).1
    rw [ENNReal.toReal_ofReal (by positivity), hIUreal]
    exact mul_le_mul_of_nonneg_left hcube (by positivity)
  have hID : (∫⁻ w in parabolicCylinder z.1 z.2 R,
      ENNReal.ofReal (spatialGradientSq u Du w)) ≤
        ENNReal.ofReal (M ^ 2 * R ^ (9 / 5 : ℝ)) := by
    have hsq : beta u Du z R ^ 2 ≤ (M * R ^ (2 / 5 : ℝ)) ^ 2 :=
      (sq_le_sq₀ hβ0 hA).2 hβ
    calc
      _ = ENNReal.ofReal (R * beta u Du z R ^ 2) :=
        sws_lintegral_spatialGradientSq_eq_ofReal_beta_sq hsol z hR hsubR
      _ ≤ ENNReal.ofReal (R * (M * R ^ (2 / 5 : ℝ)) ^ 2) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hsq hR.le)
      _ = _ := by
        rw [gradient_scale_real_fixed (by linarith only [hM]) hR]
  have hδ0 : 0 ≤ delta p z R := by unfold delta; positivity
  have hδcube : delta p z R ^ 3 ≤
      (M * R ^ (2 / 5 : ℝ)) ^ (3 / 2 : ℝ) := by
    calc
      _ = (delta p z R ^ 2) ^ (3 / 2 : ℝ) := by
        calc
          _ = delta p z R ^ (3 : ℝ) := by norm_num [Real.rpow_natCast]
          _ = delta p z R ^ ((2 : ℝ) * (3 / 2 : ℝ)) := by norm_num
          _ = (delta p z R ^ (2 : ℝ)) ^ (3 / 2 : ℝ) :=
            Real.rpow_mul hδ0 2 (3 / 2)
          _ = _ := by norm_num [Real.rpow_natCast]
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hδsq (by norm_num)
  have hIP : (∫⁻ w in parabolicCylinder z.1 z.2 R,
      ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)) ≤
        ENNReal.ofReal (M ^ (3 / 2 : ℝ) * R ^ (13 / 5 : ℝ)) := by
    calc
      _ = ENNReal.ofReal (R ^ 2 * delta p z R ^ 3) :=
        sws_lintegral_abs_pow_eq_ofReal_delta_cube hsol z hR hsubR
      _ ≤ ENNReal.ofReal (R ^ 2 * (M * R ^ (2 / 5 : ℝ)) ^ (3 / 2 : ℝ)) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hδcube (by positivity))
      _ = _ := by
        rw [pressure_scale_real_fixed (by linarith only [hM]) hR]
  exact ⟨hIU, hID, hIP⟩

end CKN
