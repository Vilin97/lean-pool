/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.CaccioppoliEnergyLower
public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.CaccioppoliCentered
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.InteriorEstimatesBasic

/-!
# Caccioppoli

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration
open CKN.Foundation.Heat


noncomputable section

namespace CKN

/-- Squared common coefficient collecting the velocity and pressure terms in the Caccioppoli
estimate. -/
@[expose] def caccioppoliC₂₅BaseSquared : ℝ :=
  max ((32 + 3 * cutoffSecondDerivativeConstant) * 8000000 +
    6 * cutoffGradientConstant * 5000000)
    (max (poincareSobolevL1VectorConstant *
      (1500 * cutoffGradientConstant + 900000))
      (3000 * cutoffGradientConstant + 1800000))

/-- Square root of the common Caccioppoli coefficient, used before the final energy normalization.
-/
def caccioppoliC₂₅Base : ℝ := Real.sqrt caccioppoliC₂₅BaseSquared

/-- Velocity and pressure coefficient after normalizing the Caccioppoli energy bound. -/
@[expose] def caccioppoliC₂₅ : ℝ := Real.sqrt (6000 * caccioppoliC₂₅BaseSquared)

/-- Force coefficient in the Caccioppoli estimate for local integrability exponent `q`. -/
@[expose] def caccioppoliC₂₆ (q : ℝ) : ℝ :=
  Real.sqrt (6000 * (2000 * (4 * Real.pi / 3) ^
    (1 / (q / (q - 1)) - 1 / 3 : ℝ)))

private lemma caccioppoli_scale_raw_bound
    {R T C₀ C : ℝ} (hR : R ≤ (C₀ * T) ^ 2)
    (hC : C ^ 2 = 6000 * C₀ ^ 2) :
    6000 * R ≤ (C * T) ^ 2 := by
  calc
    6000 * R ≤ 6000 * (C₀ * T) ^ 2 :=
      mul_le_mul_of_nonneg_left hR (by norm_num)
    _ = 6000 * C₀ ^ 2 * T ^ 2 := by ring
    _ = C ^ 2 * T ^ 2 := by rw [hC]
    _ = (C * T) ^ 2 := by ring

theorem caccioppoli
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z₀ : ParabolicPoint} {ρ r : ℝ}
    (hρ : 0 < ρ) (hr : 0 < r) (hrr : r ≤ ρ / 2)
    (hsub : closure (parabolicCylinder z₀.1 z₀.2 ρ) ⊆ spaceTimeSet Ω I) :
    alpha u z₀ r + beta u Du z₀ r ≤
      caccioppoliC₂₅ * (r / ρ) * alpha u z₀ ρ +
        caccioppoliC₂₅ * (r / ρ)⁻¹ * alpha u z₀ ρ ^ (1 / 2 : ℝ) *
          beta u Du z₀ ρ ^ (1 / 2 : ℝ) * gamma u z₀ ρ ^ (1 / 2 : ℝ) +
        caccioppoliC₂₅ * (r / ρ)⁻¹ * delta p z₀ ρ *
          gamma u z₀ ρ ^ (1 / 2 : ℝ) +
        caccioppoliC₂₆ q * (r / ρ) ^ (-1 / 2 : ℝ) *
          gamma u z₀ ρ ^ (1 / 2 : ℝ) * lambda q f z₀ ρ ^ (1 / 2 : ℝ) := by
  obtain ⟨ε, hε, hεr, hfuture⟩ := caccioppoli_admissible_heat_cutoff_exists
    hr hρ hsol.2.1 hsub
  obtain ⟨c, hA, hcm, hcc, hcenter, _, _⟩ := caccioppoli_centered_hcenter
    hsol hρ hsub
  have hcg : 0 ≤ cutoffGradientConstant :=
    CKN.Foundation.Heat.cutoffGradientConstant_nonneg_global
  have hcs : 0 ≤ cutoffSecondDerivativeConstant :=
    CKN.Foundation.Heat.cutoffSecondDerivativeConstant_nonneg_global
  have hcp : 0 ≤ poincareSobolevL1VectorConstant := by
    unfold poincareSobolevL1VectorConstant
    positivity
  have hbase : 0 ≤ caccioppoliC₂₅BaseSquared := by
    unfold caccioppoliC₂₅BaseSquared
    apply le_max_of_le_left
    · positivity
  have hbaseC : 0 ≤ caccioppoliC₂₅Base := by
    unfold caccioppoliC₂₅Base
    positivity
  have hC₂₅ : 0 ≤ caccioppoliC₂₅ := by
    unfold caccioppoliC₂₅
    positivity
  have hC₂₆ : 0 ≤ caccioppoliC₂₆ q := by
    unfold caccioppoliC₂₆
    positivity
  have hbase_sq : caccioppoliC₂₅Base ^ 2 = caccioppoliC₂₅BaseSquared := by
    unfold caccioppoliC₂₅Base
    exact Real.sq_sqrt hbase
  have hC₂₅_sq : caccioppoliC₂₅ ^ 2 =
      6000 * caccioppoliC₂₅Base ^ 2 := by
    unfold caccioppoliC₂₅
    rw [Real.sq_sqrt]
    · rw [hbase_sq]
    · positivity
  have hC₂₆_sq : caccioppoliC₂₆ q ^ 2 =
      6000 * (2000 * (4 * Real.pi / 3) ^
        (1 / (q / (q - 1)) - 1 / 3 : ℝ)) := by
    unfold caccioppoliC₂₆
    rw [Real.sq_sqrt]
    positivity
  have hC₂₆_base_sq :
      (Real.sqrt (2000 * (4 * Real.pi / 3) ^
        (1 / (q / (q - 1)) - 1 / 3 : ℝ))) ^ 2 =
        2000 * (4 * Real.pi / 3) ^
          (1 / (q / (q - 1)) - 1 / 3 : ℝ) := by
    rw [Real.sq_sqrt]
    positivity
  have hC₂₆_sq' : caccioppoliC₂₆ q ^ 2 =
      6000 * (Real.sqrt (2000 * (4 * Real.pi / 3) ^
        (1 / (q / (q - 1)) - 1 / 3 : ℝ))) ^ 2 := by
    rw [hC₂₆_base_sq]
    exact hC₂₆_sq
  have hC₁ : ((32 + 3 * cutoffSecondDerivativeConstant) * 8000000 +
      6 * cutoffGradientConstant * 5000000) ≤ caccioppoliC₂₅Base ^ 2 := by
    rw [hbase_sq]
    exact le_max_left _ _
  have hC₂ : poincareSobolevL1VectorConstant *
      (1500 * cutoffGradientConstant + 900000) ≤
      caccioppoliC₂₅Base ^ 2 := by
    rw [hbase_sq]
    exact le_max_of_le_right (le_max_left _ _)
  have hC₃ : 3000 * cutoffGradientConstant + 1800000 ≤
      caccioppoliC₂₅Base ^ 2 := by
    rw [hbase_sq]
    exact le_max_of_le_right (le_max_right _ _)
  have hC₄ : 2000 * (4 * Real.pi / 3) ^
      (1 / (q / (q - 1)) - 1 / 3 : ℝ) ≤
      (Real.sqrt (2000 * (4 * Real.pi / 3) ^
        (1 / (q / (q - 1)) - 1 / 3 : ℝ))) ^ 2 := by
    rw [Real.sq_sqrt]
    positivity
  have hraw := caccioppoli_raw_term_bounds hsol
    (C₂₅ := caccioppoliC₂₅Base)
    (C₂₆ := Real.sqrt (2000 * (4 * Real.pi / 3) ^
      (1 / (q / (q - 1)) - 1 / 3 : ℝ)))
    (C_PS := poincareSobolevL1VectorConstant)
    hρ hε hr hrr hεr hsub hfuture
    (by unfold poincareSobolevL1VectorConstant; positivity)
    hC₁ hC₂ hC₃ hC₄ hA hcenter
  have hlower := caccioppoli_energy_lower_of_raw hsol hρ hε hr hrr hεr
    hsub hfuture hA hcm hcenter hcc
  have hlower' : (alpha u z₀ r + beta u Du z₀ r) ^ 2 ≤
      6000 * caccioppoliI1HeatCutoffRaw (u := u) (x₀ := z₀.1)
        (t₀ := z₀.2) (ρ := ρ) (ε := ε) (r := r) hρ hε +
      6000 * caccioppoliI2HeatCutoffRaw (u := u) (c := c)
        (x₀ := z₀.1) (t₀ := z₀.2) (ρ := ρ) (ε := ε) (r := r) hρ hε +
      6000 * caccioppoliI3HeatCutoffRaw (p := p) (v := u)
        (x₀ := z₀.1) (t₀ := z₀.2) (ρ := ρ) (ε := ε) (r := r) hρ hε +
      6000 * caccioppoliI4HeatCutoffRaw (u := u) (f := f)
        (x₀ := z₀.1) (t₀ := z₀.2) (ρ := ρ) (ε := ε) (r := r) hρ hε := by
    calc
      _ ≤ 6000 * (caccioppoliI1HeatCutoffRaw (u := u) (x₀ := z₀.1)
          (t₀ := z₀.2) (ρ := ρ) (ε := ε) (r := r) hρ hε +
        caccioppoliI2HeatCutoffRaw (u := u) (c := c) (x₀ := z₀.1)
          (t₀ := z₀.2) (ρ := ρ) (ε := ε) (r := r) hρ hε +
        caccioppoliI3HeatCutoffRaw (p := p) (v := u) (x₀ := z₀.1)
          (t₀ := z₀.2) (ρ := ρ) (ε := ε) (r := r) hρ hε +
        caccioppoliI4HeatCutoffRaw (u := u) (f := f) (x₀ := z₀.1)
          (t₀ := z₀.2) (ρ := ρ) (ε := ε) (r := r) hρ hε) := hlower
      _ = _ := by ring
  have hz₀ : (z₀.1, z₀.2) = z₀ := by
    cases z₀
    rfl
  have hI₁ := caccioppoli_scale_raw_bound
    (T := (r / ρ) * alpha u z₀ ρ) (C₀ := caccioppoliC₂₅Base)
    (C := caccioppoliC₂₅)
    (by simpa only [hz₀, mul_assoc] using hraw.1) hC₂₅_sq
  have hI₂ := caccioppoli_scale_raw_bound
    (T := (r / ρ)⁻¹ * alpha u z₀ ρ ^ (1 / 2 : ℝ) *
      beta u Du z₀ ρ ^ (1 / 2 : ℝ) * gamma u z₀ ρ ^ (1 / 2 : ℝ))
    (C₀ := caccioppoliC₂₅Base) (C := caccioppoliC₂₅)
    (by simpa only [hz₀, mul_assoc] using hraw.2.1) hC₂₅_sq
  have hI₃ := caccioppoli_scale_raw_bound
    (T := (r / ρ)⁻¹ * delta p z₀ ρ * gamma u z₀ ρ ^ (1 / 2 : ℝ))
    (C₀ := caccioppoliC₂₅Base) (C := caccioppoliC₂₅)
    (by simpa only [hz₀, mul_assoc] using hraw.2.2.1) hC₂₅_sq
  have hI₄ := caccioppoli_scale_raw_bound
    (T := (r / ρ) ^ (-1 / 2 : ℝ) * gamma u z₀ ρ ^ (1 / 2 : ℝ) *
      lambda q f z₀ ρ ^ (1 / 2 : ℝ))
    (C₀ := Real.sqrt (2000 * (4 * Real.pi / 3) ^
      (1 / (q / (q - 1)) - 1 / 3 : ℝ))) (C := caccioppoliC₂₆ q)
    (by simpa only [hz₀, mul_assoc] using hraw.2.2.2) hC₂₆_sq'
  have hκ : 0 < r / ρ := div_pos hr hρ
  apply caccioppoli_assemble_four_terms
    (αr := alpha u z₀ r) (βr := beta u Du z₀ r)
    (A := alpha u z₀ ρ) (B := beta u Du z₀ ρ)
    (G := gamma u z₀ ρ) (D := delta p z₀ ρ) (L := lambda q f z₀ ρ)
    (κ := r / ρ) (C₂₅ := caccioppoliC₂₅) (C₂₆ := caccioppoliC₂₆ q)
    (by unfold alpha; positivity) (by unfold beta; positivity)
    (by unfold alpha; positivity) (by unfold beta; positivity)
    (by unfold gamma; positivity) (by unfold delta; positivity)
    (by unfold lambda; positivity) hκ hC₂₅ hC₂₆ hlower'
    (by simpa only [mul_assoc] using hI₁)
    (by simpa only [mul_assoc] using hI₂)
    (by simpa only [mul_assoc] using hI₃)
    (by simpa only [mul_assoc] using hI₄)

end CKN
