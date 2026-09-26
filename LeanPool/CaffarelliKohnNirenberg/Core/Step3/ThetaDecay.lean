/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Iteration.ThetaDecayAlgebra
public import LeanPool.CaffarelliKohnNirenberg.Core.Iteration.Arithmetic
public import LeanPool.CaffarelliKohnNirenberg.Core.Step2.Interpolation
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.PressureDecay
public import LeanPool.CaffarelliKohnNirenberg.Statements.Theta

/-!
# Theta Decay

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN.Core.Step3

open CKN

/-! The source-scale assembly below is the interface between the analytic
estimates and the elementary combination theorem.  The pressure estimate is
kept as a display-shaped input until the pressure decomposition estimates are
available at solution level. -/

/-- Assemble the first display of `lem:theta-decay` from the pressure and
Caccioppoli displays, using the established Gagliardo estimate. -/
theorem thetaDecay_of_pressure_and_caccioppoli
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ r C₁₄ C₁₅ C₂₅ C₂₆ : ℝ}
    (hρ : 0 < ρ) (hr : 0 < r) (hrr : r ≤ ρ / 2)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (_ : 0 ≤ C₁₄) (_ : 0 ≤ C₁₅)
    (hC₂₅ : 0 ≤ C₂₅) (hC₂₆ : 0 ≤ C₂₆)
    (hpressure : delta p z r ≤
      C₁₄ * (r / ρ) ^ (-1 / 2 : ℝ) * Real.sqrt (alpha u z ρ) *
          Real.sqrt (beta u Du z ρ) +
        C₁₄ * (r / ρ) ^ (1 / 3 : ℝ) * delta p z ρ +
        C₁₅ * (r / ρ) ^ (1 / 2 : ℝ) * Real.sqrt (lambda q f z ρ))
    (hcacc : alpha u z r + beta u Du z r ≤
      C₂₅ * (r / ρ) * alpha u z ρ +
        C₂₅ * (r / ρ)⁻¹ * Real.sqrt (alpha u z ρ) *
          Real.sqrt (beta u Du z ρ) * Real.sqrt (gamma u z ρ) +
        C₂₅ * (r / ρ)⁻¹ * delta p z ρ * Real.sqrt (gamma u z ρ) +
        C₂₆ * (r / ρ) ^ (-1 / 2 : ℝ) * Real.sqrt (gamma u z ρ) *
          Real.sqrt (lambda q f z ρ)) :
    theta (r / ρ) u Du p z r ≤
      thetaDecayC₂₇ gagliardoConstant C₁₄ C₂₅ * (r / ρ) ^ (2 / 3 : ℝ) *
          theta (r / ρ) u Du p z ρ +
        thetaDecayC₂₇ gagliardoConstant C₁₄ C₂₅ * (r / ρ) ^ (-5 : ℝ) *
          (beta u Du z ρ ^ (1 / 2 : ℝ) + beta u Du z ρ) *
          theta (r / ρ) u Du p z ρ +
        thetaDecayC₂₈ gagliardoConstant C₁₅ C₂₆ * (r / ρ) ^ (-1 / 2 : ℝ) *
          theta (r / ρ) u Du p z ρ ^ (1 / 2 : ℝ) *
          lambda q f z ρ ^ (1 / 2 : ℝ) +
        thetaDecayC₂₈ gagliardoConstant C₁₅ C₂₆ * (r / ρ) ^ (-3 : ℝ) *
          lambda q f z ρ := by
  have hκ : 0 < r / ρ := div_pos hr hρ
  have hκhalf : r / ρ ≤ 1 / 2 := by
    apply (div_le_iff₀ hρ).2
    convert hrr using 1
    ring
  have hγ := gamma_le_gagliardo_of_sws hsol hρ hsub
  have hγ' : gamma u z ρ ≤
      gagliardoConstant * Real.sqrt (alpha u z ρ) *
        Real.sqrt (beta u Du z ρ) + gagliardoConstant * alpha u z ρ := by
    simpa only [← Real.sqrt_eq_rpow] using hγ
  have hC₉ : 0 ≤ gagliardoConstant := by
    unfold gagliardoConstant
    positivity
  have hα : 0 ≤ alpha u z ρ := by
    unfold alpha
    positivity
  have hβ : 0 ≤ beta u Du z ρ := by
    unfold beta
    positivity
  have hδr : 0 ≤ delta p z r := by
    unfold delta
    positivity
  have hlam : 0 ≤ lambda q f z ρ := by
    unfold lambda
    positivity
  have h := thetaDecay_algebra
    (κ := r / ρ) (C₉ := gagliardoConstant) (C₁₄ := C₁₄)
    (C₁₅ := C₁₅) (C₂₅ := C₂₅) (C₂₆ := C₂₆)
    (α := alpha u z ρ) (β := beta u Du z ρ) (γ := gamma u z ρ)
    (δ := delta p z ρ) (lam := lambda q f z ρ)
    (αr := alpha u z r) (βr := beta u Du z r) (δr := delta p z r)
    hκ hκhalf hC₉ hC₂₅ hC₂₆ hα hβ hlam hδr hcacc hpressure hγ'
  simpa [theta, thetaValue, Real.sqrt_eq_rpow] using h

/-! This is the source-input wrapper.  The pressure side is kept conditional
on the annular cylinder inputs until the unconditional Pk bounds land. -/


/-- The small-`theta` display assembled from the same three source estimates. -/
theorem thetaDecay_small_of_pressure_and_caccioppoli
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ r C₁₄ C₁₅ C₂₅ C₂₆ : ℝ}
    (hρ : 0 < ρ) (hr : 0 < r) (hrr : r ≤ ρ / 2)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (_ : 0 ≤ C₁₄) (_ : 0 ≤ C₁₅)
    (hC₂₅ : 0 ≤ C₂₅) (hC₂₆ : 0 ≤ C₂₆)
    (hθ : theta (r / ρ) u Du p z ρ ≤ 1)
    (hpressure : delta p z r ≤
      C₁₄ * (r / ρ) ^ (-1 / 2 : ℝ) * Real.sqrt (alpha u z ρ) *
          Real.sqrt (beta u Du z ρ) +
        C₁₄ * (r / ρ) ^ (1 / 3 : ℝ) * delta p z ρ +
        C₁₅ * (r / ρ) ^ (1 / 2 : ℝ) * Real.sqrt (lambda q f z ρ))
    (hcacc : alpha u z r + beta u Du z r ≤
      C₂₅ * (r / ρ) * alpha u z ρ +
        C₂₅ * (r / ρ)⁻¹ * Real.sqrt (alpha u z ρ) *
          Real.sqrt (beta u Du z ρ) * Real.sqrt (gamma u z ρ) +
        C₂₅ * (r / ρ)⁻¹ * delta p z ρ * Real.sqrt (gamma u z ρ) +
        C₂₆ * (r / ρ) ^ (-1 / 2 : ℝ) * Real.sqrt (gamma u z ρ) *
          Real.sqrt (lambda q f z ρ)) :
    theta (r / ρ) u Du p z r ≤
      thetaDecayC₂₇ gagliardoConstant C₁₄ C₂₅ * (r / ρ) ^ (2 / 3 : ℝ) *
          theta (r / ρ) u Du p z ρ +
        2 * thetaDecayC₂₇ gagliardoConstant C₁₄ C₂₅ * (r / ρ) ^ (-5 : ℝ) *
          theta (r / ρ) u Du p z ρ ^ (1 / 2 : ℝ) *
          theta (r / ρ) u Du p z ρ +
        thetaDecayC₂₈ gagliardoConstant C₁₅ C₂₆ * (r / ρ) ^ (-1 / 2 : ℝ) *
          theta (r / ρ) u Du p z ρ ^ (1 / 2 : ℝ) *
          lambda q f z ρ ^ (1 / 2 : ℝ) +
        thetaDecayC₂₈ gagliardoConstant C₁₅ C₂₆ * (r / ρ) ^ (-3 : ℝ) *
          lambda q f z ρ := by
  have hκ : 0 < r / ρ := div_pos hr hρ
  have hκhalf : r / ρ ≤ 1 / 2 := by
    apply (div_le_iff₀ hρ).2
    convert hrr using 1
    ring
  have hγ := gamma_le_gagliardo_of_sws hsol hρ hsub
  have hγ' : gamma u z ρ ≤
      gagliardoConstant * Real.sqrt (alpha u z ρ) *
        Real.sqrt (beta u Du z ρ) + gagliardoConstant * alpha u z ρ := by
    simpa only [← Real.sqrt_eq_rpow] using hγ
  have hC₉ : 0 ≤ gagliardoConstant := by
    unfold gagliardoConstant
    positivity
  have hα : 0 ≤ alpha u z ρ := by
    unfold alpha
    positivity
  have hβ : 0 ≤ beta u Du z ρ := by
    unfold beta
    positivity
  have hδr : 0 ≤ delta p z r := by
    unfold delta
    positivity
  have hlam : 0 ≤ lambda q f z ρ := by
    unfold lambda
    positivity
  have hθ' : thetaValue (r / ρ) (alpha u z ρ) (beta u Du z ρ)
      (delta p z ρ) ≤ 1 := by
    simpa [theta, thetaValue] using hθ
  have h := thetaDecay_algebra_small
    (κ := r / ρ) (C₉ := gagliardoConstant) (C₁₄ := C₁₄)
    (C₁₅ := C₁₅) (C₂₅ := C₂₅) (C₂₆ := C₂₆)
    (α := alpha u z ρ) (β := beta u Du z ρ) (γ := gamma u z ρ)
    (δ := delta p z ρ) (lam := lambda q f z ρ)
    (αr := alpha u z r) (βr := beta u Du z r) (δr := delta p z r)
    hκ hκhalf hC₉ hC₂₅ hC₂₆ hα hβ hlam hδr hθ' hcacc hpressure hγ'
  simpa [theta, thetaValue, Real.sqrt_eq_rpow] using h

/-! The fixed-ratio wrapper below is a lower-level conditional adapter.  It
keeps the full pressure and Caccioppoli display bundle explicit; the Step 3
producer is `thetaDecay_T_of_inputs` in `ThetaDecayTShape.lean`. -/

/-! Lower-level conditional adapter: this is not the paper's Step 3 producer.
The producer-facing theorem is `thetaDecay_T_of_inputs`, whose only named analytic
input is the CZ pressure-one display. -/

end CKN.Core.Step3
