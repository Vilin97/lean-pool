/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.I2
public import LeanPool.CaffarelliKohnNirenberg.Setting.SliceNormBounds

/-!
# I3

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

theorem caccioppoli_I3_holder
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {P U : α → ℝ≥0∞} {C : ℝ≥0∞}
    (hP : AEMeasurable P μ) (hU : AEMeasurable U μ)
    (hC : C ≠ ∞) :
    (∫⁻ x, C * P x * U x ∂μ) ≤
      C * (∫⁻ x, P x ^ (3 / 2 : ℝ) ∂μ) ^ (2 / 3 : ℝ) *
        (∫⁻ x, U x ^ (3 : ℝ) ∂μ) ^ (1 / 3 : ℝ) := by
  exact caccioppoli_I2_holder hP hU hC

theorem caccioppoli_I3_pressure_integral_identity
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) (z : ParabolicPoint)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    (∫⁻ w in parabolicCylinder z.1 z.2 ρ,
        ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)) =
      ENNReal.ofReal (ρ ^ 2 * delta p z ρ ^ 3) := by
  exact sws_lintegral_abs_pow_eq_ofReal_delta_cube hsol z hρ hsub

theorem caccioppoli_I3_normalization
    {κ δ γ K C₂₅ I₃ : ℝ} (hκ : 0 < κ)
    (_ : 0 ≤ δ) (hγ : 0 ≤ γ)
    (hKbound : K ≤ C₂₅ ^ 2)
    (hraw : I₃ ≤ K * κ⁻¹ ^ 2 * δ ^ 2 * γ) :
    I₃ ≤ (C₂₅ * κ⁻¹ * δ * γ ^ (1 / 2 : ℝ)) ^ 2 := by
  have hsqrt : (γ ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = γ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hγ]
    norm_num
  have hscale :
      (κ⁻¹ * δ * γ ^ (1 / 2 : ℝ)) ^ 2 = κ⁻¹ ^ 2 * δ ^ 2 * γ := by
    rw [mul_pow, mul_pow, hsqrt]
  calc
    I₃ ≤ K * (κ⁻¹ ^ 2 * δ ^ 2 * γ) := by simpa [mul_assoc] using hraw
    _ ≤ C₂₅ ^ 2 * (κ⁻¹ ^ 2 * δ ^ 2 * γ) := by
      gcongr
    _ = (C₂₅ * κ⁻¹ * δ * γ ^ (1 / 2 : ℝ)) ^ 2 := by
      rw [← hscale]
      ring

end CKN
