/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.OscillationHarmonic
public import LeanPool.CaffarelliKohnNirenberg.Setting.UTensor
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Oscillation Lin34

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration
open CKN.Foundation.Heat

noncomputable section

namespace CKN

/-- The velocity oscillation in `eq:Chat`, with the spatial mean taken at each time. -/
@[expose]
def pressureChat (u : ParabolicPoint → Vec3) (z : ParabolicPoint) (r : ℝ) : ℝ :=
  r⁻¹ ^ 2 * ∫ w in parabolicCylinder z.1 z.2 r,
    vec3EuclideanNorm (meanFreeVec u z.1 r w.2 w.1) ^ (3 : ℕ)

/-- The unrooted pressure quantity `D` used in the integrated Lin estimate. -/
@[expose]
def pressureD (p : ParabolicPoint → ℝ) (z : ParabolicPoint) (r : ℝ) : ℝ :=
  r⁻¹ ^ 2 * ∫ w in parabolicCylinder z.1 z.2 r, |p w| ^ (3 / 2 : ℝ)

/-- Coefficient combining the singular-integral and harmonic pressure estimates. -/
noncomputable def lin34Constant (C₁₁ : ℝ) : ℝ :=
  (Real.sqrt 2 + 2 * (Real.pi * 4 / 3) *
      weakHarmonicInteriorSupConstant ^ (3 / 2 : ℝ)) *
    max 1 (C₁₁ ^ (3 / 2 : ℝ))

private lemma rpow_sum_three_halves {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ (3 / 2 : ℝ) ≤
      Real.sqrt 2 * (a ^ (3 / 2 : ℝ) + b ^ (3 / 2 : ℝ)) := by
  have h := Real.rpow_sum_le_const_mul_sum_rpow
    (s := (Finset.univ : Finset (Fin 2)))
    (f := ![a, b]) (p := (3 / 2 : ℝ)) (by norm_num)
  have h' : (|a| + |b|) ^ (3 / 2 : ℝ) ≤
      2 ^ ((3 / 2 : ℝ) - 1) * (|a| ^ (3 / 2 : ℝ) + |b| ^ (3 / 2 : ℝ)) := by
    simpa using h
  rw [abs_of_nonneg ha, abs_of_nonneg hb] at h'
  convert h' using 1; norm_num [Real.sqrt_eq_rpow]

theorem pressure_oscillation_integral_of_components
    {p p₁ H : Vec3 → ℝ} {x₀ : Vec3} {r : ℝ} {I₁ IH C₁₁ E : ℝ}
    (_ : 0 < r) (_ : 0 ≤ E) (_ : 0 ≤ C₁₁)
    (hp₁ : MemLp p₁ (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ r)))
    (hH : MemLp H (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ r)))
    (hrep : p =ᵐ[volume.restrict (euclideanBall x₀ r)] (p₁ + H))
    (hI₁ : ∫ x in euclideanBall x₀ r, |p₁ x| ^ (3 / 2 : ℝ) ≤ I₁)
    (hIH : ∫ x in euclideanBall x₀ r, |H x| ^ (3 / 2 : ℝ) ≤ IH) :
    ∫ x in euclideanBall x₀ r, |p x| ^ (3 / 2 : ℝ) ≤
      Real.sqrt 2 * (I₁ + IH) := by
  have hpint : Integrable (fun x => |p x| ^ (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ r)) := by
    have hsum0 := (hp₁.add hH).integrable_norm_rpow (by norm_num) (by norm_num)
    have hexp : (ENNReal.ofReal (3 / 2 : ℝ)).toReal = (3 / 2 : ℝ) := by
      norm_num
    have hsum : Integrable (fun x => ‖(p₁ + H) x‖ ^ (3 / 2 : ℝ))
        (volume.restrict (euclideanBall x₀ r)) := by
      simpa only [hexp] using hsum0
    apply hsum.congr
    filter_upwards [hrep] with x hx
    rw [hx]
    simp only [Pi.add_apply, Real.norm_eq_abs]
  have h₁ : Integrable (fun x => |p₁ x| ^ (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ r)) := by
    have h := hp₁.integrable_norm_rpow (by norm_num) (by norm_num)
    have hexp : (ENNReal.ofReal (3 / 2 : ℝ)).toReal = (3 / 2 : ℝ) := by
      norm_num
    simpa only [hexp, Real.norm_eq_abs] using h
  have h₂ : Integrable (fun x => |H x| ^ (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ r)) := by
    have h := hH.integrable_norm_rpow (by norm_num) (by norm_num)
    have hexp : (ENNReal.ofReal (3 / 2 : ℝ)).toReal = (3 / 2 : ℝ) := by
      norm_num
    simpa only [hexp, Real.norm_eq_abs] using h
  have hsumint : Integrable (fun x =>
      Real.sqrt 2 * (|p₁ x| ^ (3 / 2 : ℝ) + |H x| ^ (3 / 2 : ℝ)))
      (volume.restrict (euclideanBall x₀ r)) := by
    simpa only [Pi.add_apply, mul_add] using (h₁.add h₂).const_mul (Real.sqrt 2)
  have hpoint : (fun x => |p x| ^ (3 / 2 : ℝ)) ≤ᵐ[
      volume.restrict (euclideanBall x₀ r)] (fun x =>
        Real.sqrt 2 * (|p₁ x| ^ (3 / 2 : ℝ) + |H x| ^ (3 / 2 : ℝ))) := by
    filter_upwards [hrep] with x hx
    calc
      |p x| ^ (3 / 2 : ℝ) = |p₁ x + H x| ^ (3 / 2 : ℝ) := by
        rw [hx]
        rfl
      _ ≤ (|p₁ x| + |H x|) ^ (3 / 2 : ℝ) := by
        exact Real.rpow_le_rpow (abs_nonneg _) (abs_add_le _ _) (by norm_num)
      _ ≤ Real.sqrt 2 * (|p₁ x| ^ (3 / 2 : ℝ) + |H x| ^ (3 / 2 : ℝ)) :=
        rpow_sum_three_halves (abs_nonneg _) (abs_nonneg _)
  change (∫ x, |p x| ^ (3 / 2 : ℝ)
      ∂(volume.restrict (euclideanBall x₀ r))) ≤ _
  calc
    _ ≤ ∫ x, Real.sqrt 2 *
        (|p₁ x| ^ (3 / 2 : ℝ) + |H x| ^ (3 / 2 : ℝ))
          ∂(volume.restrict (euclideanBall x₀ r)) :=
      integral_mono_ae hpint hsumint hpoint
    _ = Real.sqrt 2 *
        ((∫ x in euclideanBall x₀ r, |p₁ x| ^ (3 / 2 : ℝ)) +
          (∫ x in euclideanBall x₀ r, |H x| ^ (3 / 2 : ℝ))) := by
      rw [integral_const_mul, integral_add h₁ h₂]
    _ ≤ Real.sqrt 2 * (I₁ + IH) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hI₁ hIH) (Real.sqrt_nonneg _)

theorem pressure_oscillation_integral_of_components_force
    {p p₁ H J : Vec3 → ℝ} {x₀ : Vec3} {r : ℝ} {I₁ IH IJ : ℝ}
    (hr : 0 < r)
    (hp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ r)))
    (hp₁ : MemLp p₁ (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ r)))
    (hH : MemLp H (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ r)))
    (hJ : MemLp J (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ r)))
    (hrep : p =ᵐ[volume.restrict (euclideanBall x₀ r)] (p₁ + H + J))
    (hI₁ : ∫ x in euclideanBall x₀ r, |p₁ x| ^ (3 / 2 : ℝ) ≤ I₁)
    (hIH : ∫ x in euclideanBall x₀ r, |H x| ^ (3 / 2 : ℝ) ≤ IH)
    (hIJ : ∫ x in euclideanBall x₀ r, |J x| ^ (3 / 2 : ℝ) ≤ IJ) :
    ∫ x in euclideanBall x₀ r, |p x| ^ (3 / 2 : ℝ) ≤
      2 * (I₁ + IH + IJ) := by
  have hqrep : p - J =ᵐ[volume.restrict (euclideanBall x₀ r)] (p₁ + H) := by
    filter_upwards [hrep] with x hx
    change p x - J x = p₁ x + H x
    rw [hx]
    simp only [Pi.add_apply]
    ring
  have hqmem : MemLp (p - J) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ r)) := hp.sub hJ
  have hqint : ∫ x in euclideanBall x₀ r, |(p - J) x| ^ (3 / 2 : ℝ) ≤
      Real.sqrt 2 * (I₁ + IH) := by
    exact pressure_oscillation_integral_of_components hr (by positivity) (by positivity)
      hp₁ hH hqrep hI₁ hIH
  have hpreprep : p =ᵐ[volume.restrict (euclideanBall x₀ r)] ((p - J) + J) := by
    filter_upwards [] with x
    change p x = (p x - J x) + J x
    ring
  have htotal := pressure_oscillation_integral_of_components hr (by positivity) (by positivity)
    hqmem hJ hpreprep hqint hIJ
  have hI₁nonneg : 0 ≤ I₁ := le_trans (integral_nonneg (fun x => by positivity)) hI₁
  have hIHnonneg : 0 ≤ IH := le_trans (integral_nonneg (fun x => by positivity)) hIH
  have hsqrt : Real.sqrt 2 ≤ 2 := by nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    _ ≤ Real.sqrt 2 * (Real.sqrt 2 * (I₁ + IH) + IJ) := htotal
    _ ≤ 2 * (I₁ + IH + IJ) := by
      have hsum : 0 ≤ I₁ + IH := add_nonneg hI₁nonneg hIHnonneg
      have hstep : Real.sqrt 2 * (Real.sqrt 2 * (I₁ + IH)) ≤
          2 * (I₁ + IH) := by
        rw [← mul_assoc, Real.mul_self_sqrt (by norm_num)]
      have hforce : Real.sqrt 2 * IJ ≤ 2 * IJ :=
        mul_le_mul_of_nonneg_right hsqrt (le_trans (by positivity) hIJ)
      calc
        Real.sqrt 2 * (Real.sqrt 2 * (I₁ + IH) + IJ) =
            Real.sqrt 2 * (Real.sqrt 2 * (I₁ + IH)) + Real.sqrt 2 * IJ := by ring
        _ ≤ 2 * (I₁ + IH) + 2 * IJ := add_le_add hstep hforce
        _ = 2 * (I₁ + IH + IJ) := by ring

/-! The harmonic contribution after the interior estimate and the named CZ input. -/

theorem pressureD_integrated_from_slices
    {p : ParabolicPoint → ℝ} {u : ParabolicPoint → Vec3}
    {z : ParabolicPoint} {r ρ C a b : ℝ}
    {F G H : ℝ → ℝ} {μ : Measure ℝ}
    (hF : Integrable F μ) (hG : Integrable G μ) (hH : Integrable H μ)
    (hpoint : ∀ᵐ t ∂μ, F t ≤ C * (a * G t + b * H t))
    (hDr : pressureD p z r = ∫ t, F t ∂μ)
    (hDρ : pressureD p z ρ = ∫ t, H t ∂μ)
    (hChat : pressureChat u z ρ = ∫ t, G t ∂μ) :
    pressureD p z r ≤ C * (a * pressureChat u z ρ + b * pressureD p z ρ) := by
  have hR : Integrable (fun t => C * (a * G t + b * H t)) μ := by
    exact ((hG.const_mul a).add (hH.const_mul b)).const_mul C
  calc
    pressureD p z r = ∫ t, F t ∂μ := hDr
    _ ≤ ∫ t, C * (a * G t + b * H t) ∂μ :=
      integral_mono_ae hF hR hpoint
    _ = C * (a * (∫ t, G t ∂μ) + b * (∫ t, H t ∂μ)) := by
      rw [integral_const_mul, integral_add (hG.const_mul a) (hH.const_mul b),
        integral_const_mul, integral_const_mul]
    _ = C * (a * pressureChat u z ρ + b * pressureD p z ρ) := by
      rw [hChat, hDρ]

/-- Coefficient for the forcing term in the localized pressure estimate. -/
@[expose]
noncomputable def lin34ForceConstant (C₁₃ : ℝ) : ℝ :=
  Real.sqrt 2 * (1 + C₁₃ ^ (3 / 2 : ℝ))

theorem pressureD_integrated_from_slices_force
    {p : ParabolicPoint → ℝ} {u : ParabolicPoint → Vec3}
    {z : ParabolicPoint} {r ρ C a b L : ℝ}
    {F G H J : ℝ → ℝ} {μ : Measure ℝ}
    (hC : 0 ≤ C) (hF : Integrable F μ) (hG : Integrable G μ)
    (hH : Integrable H μ) (hJ : Integrable J μ)
    (hpoint : ∀ᵐ t ∂μ, F t ≤ C * (a * G t + b * H t + J t))
    (hJbound : ∫ t, J t ∂μ ≤ L)
    (hDr : pressureD p z r = ∫ t, F t ∂μ)
    (hDρ : pressureD p z ρ = ∫ t, H t ∂μ)
    (hChat : pressureChat u z ρ = ∫ t, G t ∂μ) :
    pressureD p z r ≤ C *
      (a * pressureChat u z ρ + b * pressureD p z ρ + L) := by
  have hR : Integrable (fun t => C * (a * G t + b * H t + J t)) μ := by
    exact (((hG.const_mul a).add (hH.const_mul b)).add hJ).const_mul C
  have hsum : ∫ t, (a * G t + b * H t + J t) ∂μ ≤
      a * (∫ t, G t ∂μ) + b * (∫ t, H t ∂μ) + L := by
    calc
      ∫ t, (a * G t + b * H t + J t) ∂μ =
          a * (∫ t, G t ∂μ) + b * (∫ t, H t ∂μ) + ∫ t, J t ∂μ := by
        let A : ℝ → ℝ := fun t => a * G t + b * H t
        have hA : Integrable A μ := by
          exact (hG.const_mul a).add (hH.const_mul b)
        have hAint : ∫ t, A t ∂μ =
            a * (∫ t, G t ∂μ) + b * (∫ t, H t ∂μ) := by
          dsimp [A]
          rw [integral_add (hG.const_mul a) (hH.const_mul b),
            integral_const_mul, integral_const_mul]
        have hsum := integral_add hA hJ
        calc
          ∫ t, (a * G t + b * H t + J t) ∂μ =
              (∫ t, A t ∂μ) + ∫ t, J t ∂μ := by simpa [A] using hsum
          _ = _ := by rw [hAint]
      _ ≤ a * (∫ t, G t ∂μ) + b * (∫ t, H t ∂μ) + L := by
        calc
          _ = (∫ t, J t ∂μ) +
              (a * (∫ t, G t ∂μ) + b * (∫ t, H t ∂μ)) := by ring
          _ ≤ L + (a * (∫ t, G t ∂μ) + b * (∫ t, H t ∂μ)) :=
            add_le_add_left hJbound _
          _ = _ := by ring
  calc
    pressureD p z r = ∫ t, F t ∂μ := hDr
    _ ≤ ∫ t, C * (a * G t + b * H t + J t) ∂μ :=
      integral_mono_ae hF hR hpoint
    _ = C * (∫ t, (a * G t + b * H t + J t) ∂μ) := by
      rw [integral_const_mul]
    _ ≤ C * (a * (∫ t, G t ∂μ) + b * (∫ t, H t ∂μ) + L) :=
      mul_le_mul_of_nonneg_left hsum hC
    _ = C * (a * pressureChat u z ρ + b * pressureD p z ρ + L) := by
      rw [hChat, hDρ]

theorem pressure_lin34_integrated_force
    {p : ParabolicPoint → ℝ} {u : ParabolicPoint → Vec3}
    {z : ParabolicPoint} {r ρ C₁₃ lam : ℝ}
    {F G H J : ℝ → ℝ} {μ : Measure ℝ}
    (hC₁₃ : 0 ≤ C₁₃) (hF : Integrable F μ) (hG : Integrable G μ)
    (hH : Integrable H μ) (hJ : Integrable J μ)
    (hpoint : ∀ᵐ t ∂μ, F t ≤ lin34ForceConstant C₁₃ *
      ((ρ / r) ^ 2 * G t + (r / ρ) * H t + J t))
    (hJbound : ∫ t, J t ∂μ ≤ (r / ρ) ^ (3 / 2 : ℝ) * lam ^ (3 / 2 : ℝ))
    (hDr : pressureD p z r = ∫ t, F t ∂μ)
    (hDρ : pressureD p z ρ = ∫ t, H t ∂μ)
    (hChat : pressureChat u z ρ = ∫ t, G t ∂μ) :
    pressureD p z r ≤ lin34ForceConstant C₁₃ *
      ((ρ / r) ^ 2 * pressureChat u z ρ +
        (r / ρ) * pressureD p z ρ +
        (r / ρ) ^ (3 / 2 : ℝ) * lam ^ (3 / 2 : ℝ)) := by
  have hC : 0 ≤ lin34ForceConstant C₁₃ := by
    dsimp [lin34ForceConstant]
    positivity
  exact pressureD_integrated_from_slices_force hC hF hG hH hJ hpoint hJbound
    hDr hDρ hChat

end CKN
