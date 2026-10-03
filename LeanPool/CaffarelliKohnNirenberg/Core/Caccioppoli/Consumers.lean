/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.Caccioppoli
public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.GammaAssembly
public import LeanPool.CaffarelliKohnNirenberg.Core.Iteration.Arithmetic

/-!
# Consumers

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

/-! Consumer-shaped interfaces for the two downstream Caccioppoli displays. -/

/-- The solution-level gamma-form Caccioppoli estimate. -/
theorem caccioppoli_gamma_display
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {C₂₅ C₂₆ : ℝ}
    (hC₂₅ : 0 ≤ C₂₅) (hC₂₆ : 0 ≤ C₂₆)
    (hK₁ : 6000 * ((Real.pi * 4 / 3) ^ (1 / 3 : ℝ) *
      ((32 + 3 * cutoffSecondDerivativeConstant) * 8000000 +
        6 * cutoffGradientConstant * 5000000)) ≤ C₂₅ ^ 2)
    (hK₂ : 6000 * (3 * (1500 * cutoffGradientConstant + 900000)) ≤ C₂₅ ^ 2)
    (hK₃ : 6000 * (3000 * cutoffGradientConstant + 1800000) ≤ C₂₅ ^ 2)
    (hK₄ : 6000 * (2000 * (4 * Real.pi / 3) ^
      (1 / (q / (q - 1)) - 1 / 3 : ℝ)) ≤ C₂₆ ^ 2) :
    ∀ {z : ParabolicPoint} {r ρ : ℝ}, 0 < ρ → 0 < r →
      r ≤ ρ / 2 →
      closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
      alpha u z r + beta u Du z r ≤
        C₂₅ * ((r / ρ) * gamma u z ρ +
          (r / ρ) ^ (-1 : ℝ) * gamma u z ρ ^ (3 / 2 : ℝ) +
          (r / ρ) ^ (-1 : ℝ) * delta p z ρ * gamma u z ρ ^ (1 / 2 : ℝ)) +
        C₂₆ * (r / ρ) ^ (-1 / 2 : ℝ) * gamma u z ρ ^ (1 / 2 : ℝ) *
          lambda q f z ρ ^ (1 / 2 : ℝ) := by
  intro z r ρ hρ hr hscale hsub
  obtain ⟨ε, hε, hεr, hfuture⟩ := caccioppoli_admissible_heat_cutoff_exists
    hr hρ hsol.2.1 hsub
  obtain ⟨c, hA, hcm, hcc, hcenter, hc, hmean⟩ :=
    caccioppoli_centered_hcenter hsol hρ hsub
  have hA₁ := (caccioppoli_cutoff_norm_measurable hsol hρ hsub).1.pow_const
    (2 : ℝ)
  have hvelocity := caccioppoli_velocity_integral_ne_top hsol hρ hsub
  have hLower := caccioppoli_energy_lower_of_raw hsol hρ hε hr hscale hεr
    hsub hfuture hA hcm hcenter hcc
  exact caccioppoli_gamma_of_raw_bounds hsol hρ hε hr hscale hεr hsub
    hC₂₅ hC₂₆ hK₁ hK₂ hK₃ hK₄ hc hcm hA₁ hmean hvelocity hLower
    rfl rfl rfl rfl

/-- The theta-decay display supplied by the public Caccioppoli theorem. -/
theorem caccioppoli_theta_display
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {C₂₇ : ℝ} {C₂₅ C₂₆ : ℝ}
    (hC₂₅ : caccioppoliC₂₅ ≤ C₂₅)
    (hC₂₆ : caccioppoliC₂₆ q ≤ C₂₆)
    (hC₂₇ : 0 < C₂₇) :
    ∀ {z : ParabolicPoint} {ρ : ℝ}, 0 < ρ →
      closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
      alpha u z (iterationKappa C₂₇ * ρ) + beta u Du z (iterationKappa C₂₇ * ρ) ≤
        C₂₅ * ((iterationKappa C₂₇ * ρ) / ρ) * alpha u z ρ +
          C₂₅ * ((iterationKappa C₂₇ * ρ) / ρ)⁻¹ *
            Real.sqrt (alpha u z ρ) * Real.sqrt (beta u Du z ρ) *
              Real.sqrt (gamma u z ρ) +
          C₂₅ * ((iterationKappa C₂₇ * ρ) / ρ)⁻¹ * delta p z ρ *
              Real.sqrt (gamma u z ρ) +
          C₂₆ * ((iterationKappa C₂₇ * ρ) / ρ) ^ (-1 / 2 : ℝ) *
            Real.sqrt (gamma u z ρ) * Real.sqrt (lambda q f z ρ) := by
  intro z ρ hρ hsub
  have hκ : 0 < iterationKappa C₂₇ := iterationKappa_pos hC₂₇
  have hr : 0 < iterationKappa C₂₇ * ρ := mul_pos hκ hρ
  have hhalf : iterationKappa C₂₇ * ρ ≤ ρ / 2 := by
    have hκ' := iterationKappa_le_half C₂₇
    have hmul := mul_le_mul_of_nonneg_right hκ' hρ.le
    nlinarith only [hmul]
  have hbase := caccioppoli hsol hρ hr hhalf hsub
  have hC₂₅' : 0 ≤ C₂₅ := by
    exact le_trans (by unfold caccioppoliC₂₅; positivity) hC₂₅
  have hC₂₆' : 0 ≤ C₂₆ := by
    exact le_trans (by unfold caccioppoliC₂₆; positivity) hC₂₆
  have hα : 0 ≤ alpha u z ρ := by unfold alpha; positivity
  have hβ : 0 ≤ beta u Du z ρ := by unfold beta; positivity
  have hγ : 0 ≤ gamma u z ρ := by unfold gamma; positivity
  have hδ : 0 ≤ delta p z ρ := by unfold delta; positivity
  have hLam : 0 ≤ lambda q f z ρ := by unfold lambda; positivity
  have hratio : 0 ≤ (iterationKappa C₂₇ * ρ) / ρ := by positivity
  have hratio_inv : 0 ≤ ((iterationKappa C₂₇ * ρ) / ρ)⁻¹ := by positivity
  have hratio_half : 0 ≤ ((iterationKappa C₂₇ * ρ) / ρ) ^ (-1 / 2 : ℝ) := by
    positivity
  have hαroot : 0 ≤ Real.sqrt (alpha u z ρ) := Real.sqrt_nonneg _
  have hβroot : 0 ≤ Real.sqrt (beta u Du z ρ) := Real.sqrt_nonneg _
  have hγroot : 0 ≤ Real.sqrt (gamma u z ρ) := Real.sqrt_nonneg _
  have hLamroot : 0 ≤ Real.sqrt (lambda q f z ρ) := Real.sqrt_nonneg _
  have hfirst : caccioppoliC₂₅ *
        ((iterationKappa C₂₇ * ρ) / ρ) * alpha u z ρ ≤
      C₂₅ * ((iterationKappa C₂₇ * ρ) / ρ) * alpha u z ρ := by
    calc
      _ = caccioppoliC₂₅ * (((iterationKappa C₂₇ * ρ) / ρ) *
          alpha u z ρ) := by ring
      _ ≤ C₂₅ * (((iterationKappa C₂₇ * ρ) / ρ) * alpha u z ρ) :=
        mul_le_mul_of_nonneg_right hC₂₅ (by positivity)
      _ = _ := by ring
  have hsecond : caccioppoliC₂₅ *
        ((iterationKappa C₂₇ * ρ) / ρ)⁻¹ *
          alpha u z ρ ^ (1 / 2 : ℝ) * beta u Du z ρ ^ (1 / 2 : ℝ) *
            gamma u z ρ ^ (1 / 2 : ℝ) ≤
      C₂₅ * ((iterationKappa C₂₇ * ρ) / ρ)⁻¹ *
        Real.sqrt (alpha u z ρ) * Real.sqrt (beta u Du z ρ) *
          Real.sqrt (gamma u z ρ) := by
    calc
      _ = caccioppoliC₂₅ * (((iterationKappa C₂₇ * ρ) / ρ)⁻¹ *
          (alpha u z ρ ^ (1 / 2 : ℝ) * beta u Du z ρ ^ (1 / 2 : ℝ) *
            gamma u z ρ ^ (1 / 2 : ℝ))) := by ring
      _ ≤ C₂₅ * (((iterationKappa C₂₇ * ρ) / ρ)⁻¹ *
          (alpha u z ρ ^ (1 / 2 : ℝ) * beta u Du z ρ ^ (1 / 2 : ℝ) *
            gamma u z ρ ^ (1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_right hC₂₅ (by positivity)
      _ = _ := by simp only [Real.sqrt_eq_rpow]; ring
  have hthird : caccioppoliC₂₅ *
        ((iterationKappa C₂₇ * ρ) / ρ)⁻¹ * delta p z ρ *
          gamma u z ρ ^ (1 / 2 : ℝ) ≤
      C₂₅ * ((iterationKappa C₂₇ * ρ) / ρ)⁻¹ * delta p z ρ *
        Real.sqrt (gamma u z ρ) := by
    calc
      _ = caccioppoliC₂₅ * (((iterationKappa C₂₇ * ρ) / ρ)⁻¹ *
          (delta p z ρ * gamma u z ρ ^ (1 / 2 : ℝ))) := by ring
      _ ≤ C₂₅ * (((iterationKappa C₂₇ * ρ) / ρ)⁻¹ *
          (delta p z ρ * gamma u z ρ ^ (1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_right hC₂₅ (by positivity)
      _ = _ := by simp only [Real.sqrt_eq_rpow]; ring
  have hfourth : caccioppoliC₂₆ q *
        ((iterationKappa C₂₇ * ρ) / ρ) ^ (-1 / 2 : ℝ) *
          gamma u z ρ ^ (1 / 2 : ℝ) * lambda q f z ρ ^ (1 / 2 : ℝ) ≤
      C₂₆ * ((iterationKappa C₂₇ * ρ) / ρ) ^ (-1 / 2 : ℝ) *
        Real.sqrt (gamma u z ρ) * Real.sqrt (lambda q f z ρ) := by
    calc
      _ = caccioppoliC₂₆ q * (((iterationKappa C₂₇ * ρ) / ρ) ^ (-1 / 2 : ℝ) *
          (gamma u z ρ ^ (1 / 2 : ℝ) * lambda q f z ρ ^ (1 / 2 : ℝ))) := by ring
      _ ≤ C₂₆ * (((iterationKappa C₂₇ * ρ) / ρ) ^ (-1 / 2 : ℝ) *
          (gamma u z ρ ^ (1 / 2 : ℝ) * lambda q f z ρ ^ (1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_right hC₂₆ (by positivity)
      _ = _ := by simp only [Real.sqrt_eq_rpow]; ring
  have hsum := add_le_add (add_le_add (add_le_add hfirst hsecond) hthird) hfourth
  simpa only [Real.sqrt_eq_rpow] using hbase.trans hsum

end CKN
