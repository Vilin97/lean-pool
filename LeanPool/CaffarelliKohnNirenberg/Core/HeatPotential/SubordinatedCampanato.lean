/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.HeatPotential.SubordinatedEnd

/-!
# Subordinated Campanato

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric Filter
noncomputable section
namespace CKN.Core.HeatPotential
open CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

private lemma heatPotential_source_profile_of_morrey
    {F : ParabolicPoint → ℝ} {G : Fin 3 → ParabolicPoint → ℝ}
    {z : ParabolicPoint} {r γ θ₀ θ₁ P : ℝ}
    (hr : 0 < r) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hθ₀ : 1 / θ₀ = (2 - γ) / 5)
    (hθ₁ : 1 / θ₁ = (1 - γ) / 5)
    (hP : 1 ≤ P) (hPθ₀ : P ≤ θ₀) (hPθ₁ : P ≤ θ₁)
    (hF : AEMeasurable F volume) (hG : ∀ i : Fin 3, AEMeasurable (G i) volume)
    (hNF : morreyNorm P θ₀ F < ∞)
    (hNG : ∀ i : Fin 3, morreyNorm P θ₁ (G i) < ∞)
    (hSupportF : HasCompactSupport F)
    (hSupportG : ∀ i : Fin 3, HasCompactSupport (G i)) :
    let V : ℝ := (volume (parabolicCylinder 0 0 1)).toReal
    let BF : ℝ := V ^ (1 - 1 / P) * (morreyNorm P θ₀ F).toReal
    let BG : Fin 3 → ℝ := fun i =>
      V ^ (1 - 1 / P) * (morreyNorm P θ₁ (G i)).toReal
    let Cnear : ℝ :=
      2 * 1000 * (2 : ℝ) ^ (8 - 5 / θ₀) *
          (1 - (2 : ℝ) ^ (-γ))⁻¹ * (256 : ℝ) ^ γ * BF +
        ∑ i, 2 * 300000 * (2 : ℝ) ^ (10 - 1 - 5 / θ₁) *
          (1 - (2 : ℝ) ^ (-γ))⁻¹ * (256 : ℝ) ^ γ * BG i
    let A : ℕ → ℝ := fun j =>
      (2 * r * ((900000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 4) +
        2 * r * (10000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 5))) *
        ((2 * ((2 : ℝ) ^ (((j + 6 : ℤ) : ℝ) + 1) * r)) ^
          (5 * (1 - 1 / θ₀)) * BF) +
      ∑ i, (2 * r * ((60000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 5) +
        2 * r * (30000000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 6))) *
        ((2 * ((2 : ℝ) ^ (((j + 6 : ℤ) : ℝ) + 1) * r)) ^
          (5 * (1 - 1 / θ₁)) * BG i)
    let C : ℝ :=
      (1800000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₀)) - 16) +
        40000000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₀)) - 20)) * BF +
        ∑ i, (120000000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₁)) - 20) +
          120000000000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₁)) - 24)) * BG i
    (∀ j : ℕ, 0 ≤ A j) ∧
      (∀ j : ℕ, A j ≤ C * (2 : ℝ) ^ ((j : ℝ) * (γ - 1)) * r ^ γ) ∧
      (∀ p p' : ParabolicPoint,
        p ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r →
        p' ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r →
        |heatPotential F G p - heatPotential F G p'| ≤
          Cnear * r ^ γ + ∑' j : ℕ, A j) := by
  dsimp
  let V : ℝ := (volume (parabolicCylinder 0 0 1)).toReal
  let BF : ℝ := V ^ (1 - 1 / P) * (morreyNorm P θ₀ F).toReal
  let BG : Fin 3 → ℝ := fun i =>
    V ^ (1 - 1 / P) * (morreyNorm P θ₁ (G i)).toReal
  let Cnear : ℝ :=
    2 * 1000 * (2 : ℝ) ^ (8 - 5 / θ₀) *
        (1 - (2 : ℝ) ^ (-γ))⁻¹ * (256 : ℝ) ^ γ * BF +
      ∑ i, 2 * 300000 * (2 : ℝ) ^ (10 - 1 - 5 / θ₁) *
        (1 - (2 : ℝ) ^ (-γ))⁻¹ * (256 : ℝ) ^ γ * BG i
  let A : ℕ → ℝ := fun j =>
    (2 * r * ((900000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 4) +
      2 * r * (10000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 5))) *
      ((2 * ((2 : ℝ) ^ (((j + 6 : ℤ) : ℝ) + 1) * r)) ^
        (5 * (1 - 1 / θ₀)) * BF) +
    ∑ i, (2 * r * ((60000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 5) +
      2 * r * (30000000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 6))) *
      ((2 * ((2 : ℝ) ^ (((j + 6 : ℤ) : ℝ) + 1) * r)) ^
        (5 * (1 - 1 / θ₁)) * BG i)
  let C : ℝ :=
    (1800000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₀)) - 16) +
      40000000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₀)) - 20)) * BF +
      ∑ i, (120000000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₁)) - 20) +
        120000000000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₁)) - 24)) * BG i
  have hprofile := heatPotential_far_shell_profile_of_morrey
    (F := F) (G := G) hr hγ hθ₀ hθ₁ hP hPθ₀ hPθ₁ hNF hNG
  have hA : ∀ j : ℕ, 0 ≤ A j := by
    simpa [A, BF, BG, V] using hprofile.1
  have hAj : ∀ j : ℕ, A j ≤
      C * (2 : ℝ) ^ ((j : ℝ) * (γ - 1)) * r ^ γ := by
    simpa [A, C, BF, BG, V] using hprofile.2
  have hC : 0 ≤ C := by
    dsimp [C, BF, BG, V]
    positivity
  have hsum := heatPotential_far_shell_bound hγ1 (by
    exact hC) hr.le hA hAj
  have hpair : ∀ p p' : ParabolicPoint,
      p ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r →
      p' ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r →
      |heatPotential F G p - heatPotential F G p'| ≤
        Cnear * r ^ γ + ∑' j : ℕ, A j := by
    intro p p' hp hp'
    simpa [A, Cnear, BF, BG, V] using
      (heatPotential_pairwise_oscillation_bound_of_morrey
        (F := F) (G := G) (z := z) (p := p) (p' := p') hr hγ hγ1
        hθ₀ hθ₁ hP hPθ₀ hPθ₁ hF hG hNF hNG hSupportF hSupportG hp hp')
  exact ⟨hA, hAj, hpair⟩

theorem heatPotential_campanato_bound_of_morrey
    {F : ParabolicPoint → ℝ} {G : Fin 3 → ParabolicPoint → ℝ}
    {z : ParabolicPoint} {r γ θ₀ θ₁ P : ℝ}
    (hr : 0 < r) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hθ₀ : 1 / θ₀ = (2 - γ) / 5)
    (hθ₁ : 1 / θ₁ = (1 - γ) / 5)
    (hP : 1 ≤ P) (hPθ₀ : P ≤ θ₀) (hPθ₁ : P ≤ θ₁)
    (hF : AEMeasurable F volume) (hG : ∀ i : Fin 3, AEMeasurable (G i) volume)
    (hNF : morreyNorm P θ₀ F < ∞)
    (hNG : ∀ i : Fin 3, morreyNorm P θ₁ (G i) < ∞)
    (hSupportF : HasCompactSupport F)
    (hSupportG : ∀ i : Fin 3, HasCompactSupport (G i)) :
    let V : ℝ := (volume (parabolicCylinder 0 0 1)).toReal
    let BF : ℝ := V ^ (1 - 1 / P) * (morreyNorm P θ₀ F).toReal
    let BG : Fin 3 → ℝ := fun i =>
      V ^ (1 - 1 / P) * (morreyNorm P θ₁ (G i)).toReal
    let Cnear : ℝ :=
      2 * 1000 * (2 : ℝ) ^ (8 - 5 / θ₀) *
          (1 - (2 : ℝ) ^ (-γ))⁻¹ * (256 : ℝ) ^ γ * BF +
        ∑ i, 2 * 300000 * (2 : ℝ) ^ (10 - 1 - 5 / θ₁) *
          (1 - (2 : ℝ) ^ (-γ))⁻¹ * (256 : ℝ) ^ γ * BG i
    let C : ℝ :=
      (1800000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₀)) - 16) +
        40000000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₀)) - 20)) * BF +
        ∑ i, (120000000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₁)) - 20) +
          120000000000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₁)) - 24)) * BG i
    ParabolicBallLpOscillation (heatPotential F G) z r P ≤
      (Cnear + C * (1 - (2 : ℝ) ^ (γ - 1))⁻¹) * r ^ γ := by
  dsimp
  let V : ℝ := (volume (parabolicCylinder 0 0 1)).toReal
  let BF : ℝ := V ^ (1 - 1 / P) * (morreyNorm P θ₀ F).toReal
  let BG : Fin 3 → ℝ := fun i =>
    V ^ (1 - 1 / P) * (morreyNorm P θ₁ (G i)).toReal
  let Cnear : ℝ :=
    2 * 1000 * (2 : ℝ) ^ (8 - 5 / θ₀) *
        (1 - (2 : ℝ) ^ (-γ))⁻¹ * (256 : ℝ) ^ γ * BF +
      ∑ i, 2 * 300000 * (2 : ℝ) ^ (10 - 1 - 5 / θ₁) *
        (1 - (2 : ℝ) ^ (-γ))⁻¹ * (256 : ℝ) ^ γ * BG i
  let A : ℕ → ℝ := fun j =>
    (2 * r * ((900000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 4) +
      2 * r * (10000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 5))) *
      ((2 * ((2 : ℝ) ^ (((j + 6 : ℤ) : ℝ) + 1) * r)) ^
        (5 * (1 - 1 / θ₀)) * BF) +
    ∑ i, (2 * r * ((60000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 5) +
      2 * r * (30000000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 6))) *
      ((2 * ((2 : ℝ) ^ (((j + 6 : ℤ) : ℝ) + 1) * r)) ^
        (5 * (1 - 1 / θ₁)) * BG i)
  let C : ℝ :=
    (1800000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₀)) - 16) +
      40000000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₀)) - 20)) * BF +
      ∑ i, (120000000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₁)) - 20) +
        120000000000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₁)) - 24)) * BG i
  have hprofile := heatPotential_source_profile_of_morrey
    (F := F) (G := G) (z := z) hr hγ hγ1 hθ₀ hθ₁ hP hPθ₀ hPθ₁
      hF hG hNF hNG hSupportF hSupportG
  have hA : ∀ j : ℕ, 0 ≤ A j := by
    simpa [A, BF, BG, V] using hprofile.1
  have hfar : ∀ j : ℕ, A j ≤
      C * (2 : ℝ) ^ ((j : ℝ) * (γ - 1)) * r ^ γ := by
    simpa [A, C, BF, BG, V] using hprofile.2.1
  have hCnear : 0 ≤ Cnear := by
    dsimp [Cnear, BF, BG, V]
    have hpow : (2 : ℝ) ^ (-γ) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hγ])
    have hden : 0 ≤ (1 - (2 : ℝ) ^ (-γ))⁻¹ :=
      inv_nonneg.mpr (sub_nonneg.mpr hpow.le)
    positivity
  have hC : 0 ≤ C := by
    dsimp [C, BF, BG, V]
    positivity
  have hpair : ∀ w ∈ @Metric.closedBall ParabolicPoint
      parabolicPseudoMetricSpace z r,
      ∀ w' ∈ @Metric.closedBall ParabolicPoint
        parabolicPseudoMetricSpace z r,
      |heatPotential F G w - heatPotential F G w'| ≤
        Cnear * r ^ γ + ∑' j : ℕ, A j := by
    intro w hw w' hw'
    exact hprofile.2.2 w w' hw hw'
  have hK : 0 ≤ Cnear * r ^ γ + ∑' j : ℕ, A j :=
    add_nonneg (mul_nonneg hCnear (Real.rpow_nonneg hr.le _))
      (tsum_nonneg hA)
  have hdata := heatPotential_local_data_of_pairwise hr hP hK
    (heatPotential_aemeasurable_of_sources hF hG) hpair
  have hcamp := heatPotential_campanato_bound
    (h := heatPotential F G) (z := z) (r := r) (γ := γ) (p := P)
    (Cnear := Cnear) (Cfar := C) (Anear := Cnear * r ^ γ) (A := A)
    hγ.le hγ1 hr hP hCnear hC hdata.1 hdata.2
    (le_refl _) hA hfar hpair
  simpa [Cnear, C, BF, BG, V] using hcamp

theorem heatPotential_global_campanato_bound_of_morrey
    {F : ParabolicPoint → ℝ} {G : Fin 3 → ParabolicPoint → ℝ}
    {γ θ₀ θ₁ P : ℝ}
    (hγ : 0 < γ) (hγ1 : γ < 1)
    (hθ₀ : 1 / θ₀ = (2 - γ) / 5)
    (hθ₁ : 1 / θ₁ = (1 - γ) / 5)
    (hP : 1 ≤ P) (hPθ₀ : P ≤ θ₀) (hPθ₁ : P ≤ θ₁)
    (hF : AEMeasurable F volume) (hG : ∀ i : Fin 3, AEMeasurable (G i) volume)
    (hNF : morreyNorm P θ₀ F < ∞)
    (hNG : ∀ i : Fin 3, morreyNorm P θ₁ (G i) < ∞)
    (hSupportF : HasCompactSupport F)
    (hSupportG : ∀ i : Fin 3, HasCompactSupport (G i)) :
    let V : ℝ := (volume (parabolicCylinder 0 0 1)).toReal
    let BF : ℝ := V ^ (1 - 1 / P) * (morreyNorm P θ₀ F).toReal
    let BG : Fin 3 → ℝ := fun i =>
      V ^ (1 - 1 / P) * (morreyNorm P θ₁ (G i)).toReal
    let Cnear : ℝ :=
      2 * 1000 * (2 : ℝ) ^ (8 - 5 / θ₀) *
          (1 - (2 : ℝ) ^ (-γ))⁻¹ * (256 : ℝ) ^ γ * BF +
        ∑ i, 2 * 300000 * (2 : ℝ) ^ (10 - 1 - 5 / θ₁) *
          (1 - (2 : ℝ) ^ (-γ))⁻¹ * (256 : ℝ) ^ γ * BG i
    let C : ℝ :=
      (1800000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₀)) - 16) +
        40000000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₀)) - 20)) * BF +
        ∑ i, (120000000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₁)) - 20) +
          120000000000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₁)) - 24)) * BG i
    GlobalParabolicBallCampanatoBound (heatPotential F G) γ
      (Cnear + C * (1 - (2 : ℝ) ^ (γ - 1))⁻¹) P := by
  dsimp [GlobalParabolicBallCampanatoBound]
  intro z r hr
  simpa using heatPotential_campanato_bound_of_morrey
    (F := F) (G := G) (z := z) hr hγ hγ1 hθ₀ hθ₁ hP hPθ₀ hPθ₁
      hF hG hNF hNG hSupportF hSupportG

private lemma heatPotential_global_data_of_morrey
    {F : ParabolicPoint → ℝ} {G : Fin 3 → ParabolicPoint → ℝ}
    {γ θ₀ θ₁ P : ℝ}
    (hγ : 0 < γ) (hγ1 : γ < 1)
    (hθ₀ : 1 / θ₀ = (2 - γ) / 5)
    (hθ₁ : 1 / θ₁ = (1 - γ) / 5)
    (hP : 1 ≤ P) (hPθ₀ : P ≤ θ₀) (hPθ₁ : P ≤ θ₁)
    (hF : AEMeasurable F volume) (hG : ∀ i : Fin 3, AEMeasurable (G i) volume)
    (hNF : morreyNorm P θ₀ F < ∞)
    (hNG : ∀ i : Fin 3, morreyNorm P θ₁ (G i) < ∞)
    (hSupportF : HasCompactSupport F)
    (hSupportG : ∀ i : Fin 3, HasCompactSupport (G i)) :
    GlobalParabolicBallLpData (heatPotential F G) P := by
  intro z r hr
  let V : ℝ := (volume (parabolicCylinder 0 0 1)).toReal
  let BF : ℝ := V ^ (1 - 1 / P) * (morreyNorm P θ₀ F).toReal
  let BG : Fin 3 → ℝ := fun i =>
    V ^ (1 - 1 / P) * (morreyNorm P θ₁ (G i)).toReal
  let Cnear : ℝ :=
    2 * 1000 * (2 : ℝ) ^ (8 - 5 / θ₀) *
        (1 - (2 : ℝ) ^ (-γ))⁻¹ * (256 : ℝ) ^ γ * BF +
      ∑ i, 2 * 300000 * (2 : ℝ) ^ (10 - 1 - 5 / θ₁) *
        (1 - (2 : ℝ) ^ (-γ))⁻¹ * (256 : ℝ) ^ γ * BG i
  let A : ℕ → ℝ := fun j =>
    (2 * r * ((900000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 4) +
      2 * r * (10000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 5))) *
      ((2 * ((2 : ℝ) ^ (((j + 6 : ℤ) : ℝ) + 1) * r)) ^
        (5 * (1 - 1 / θ₀)) * BF) +
    ∑ i, (2 * r * ((60000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 5) +
      2 * r * (30000000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 6))) *
      ((2 * ((2 : ℝ) ^ (((j + 6 : ℤ) : ℝ) + 1) * r)) ^
        (5 * (1 - 1 / θ₁)) * BG i)
  have hprofile := heatPotential_source_profile_of_morrey
    (F := F) (G := G) (z := z) hr hγ hγ1 hθ₀ hθ₁ hP hPθ₀ hPθ₁
      hF hG hNF hNG hSupportF hSupportG
  have hA : ∀ j : ℕ, 0 ≤ A j := by
    simpa [A, BF, BG, V] using hprofile.1
  have hCnear : 0 ≤ Cnear := by
    dsimp [Cnear, BF, BG, V]
    have hpow : (2 : ℝ) ^ (-γ) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hγ])
    have hden : 0 ≤ (1 - (2 : ℝ) ^ (-γ))⁻¹ :=
      inv_nonneg.mpr (sub_nonneg.mpr hpow.le)
    positivity
  have hpair : ∀ w ∈ @Metric.closedBall ParabolicPoint
      parabolicPseudoMetricSpace z r,
      ∀ w' ∈ @Metric.closedBall ParabolicPoint
        parabolicPseudoMetricSpace z r,
      |heatPotential F G w - heatPotential F G w'| ≤
        Cnear * r ^ γ + ∑' j : ℕ, A j := by
    intro w hw w' hw'
    exact hprofile.2.2 w w' hw hw'
  have hK : 0 ≤ Cnear * r ^ γ + ∑' j : ℕ, A j :=
    add_nonneg (mul_nonneg hCnear (Real.rpow_nonneg hr.le _))
      (tsum_nonneg hA)
  exact heatPotential_local_data_of_pairwise hr hP hK
    (heatPotential_aemeasurable_of_sources hF hG) hpair

private lemma heatPotential_abs_rpow_of_local_data
    {h : ParabolicPoint → ℝ} {z : ParabolicPoint} {r p : ℝ}
    (hr : 0 < r) (hp : 1 ≤ p)
    (hint : IntegrableOn h
      (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) volume)
    (hfp : IntegrableOn
      (fun q => |h q - ⨍ x in
        @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r, h x| ^ p)
      (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) volume) :
    IntegrableOn (fun q => |h q| ^ p)
      (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) volume := by
  let B : Set ParabolicPoint :=
    @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r
  let c : ℝ := ⨍ x in B, h x
  have hintB : IntegrableOn h B volume := by simpa [B] using hint
  have hfpB : IntegrableOn (fun q => |h q - c| ^ p) B volume := by
    simpa [B, c] using hfp
  have hBtop : volume B < ∞ := by
    dsimp [B]
    exact parabolicBall_closedBall_top hr
  have hp0 : 0 ≤ p := le_trans zero_le_one hp
  have hmeas : AEStronglyMeasurable (fun q => |h q| ^ p)
      (volume.restrict B) := by
    exact (continuous_abs.rpow_const (fun _ => Or.inr hp0)).comp_aestronglyMeasurable
      hintB.aestronglyMeasurable
  have hsum : IntegrableOn
      (fun q => (2 : ℝ) ^ (p - 1) *
        (|h q - c| ^ p + |c| ^ p)) B volume := by
    exact (hfpB.add (integrableOn_const hBtop.ne)).const_mul ((2 : ℝ) ^ (p - 1))
  refine hsum.mono' hmeas ?_
  filter_upwards [ae_restrict_mem (by
    dsimp [B]
    exact measurableSet_closedBall)] with q hq
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) p)]
  have hsplit : |h q| ≤ |h q - c| + |c| := by
    have heq : (h q - c) + c = h q := by ring
    calc
      |h q| = |(h q - c) + c| := by rw [heq]
      _ ≤ |h q - c| + |c| := abs_add_le _ _
  calc
    |h q| ^ p ≤ (|h q - c| + |c|) ^ p :=
      Real.rpow_le_rpow (abs_nonneg _) hsplit hp0
    _ ≤ (2 : ℝ) ^ (p - 1) * (|h q - c| ^ p + |c| ^ p) := by
      have h := NNReal.rpow_add_le_mul_rpow_add_rpow
        ⟨|h q - c|, abs_nonneg _⟩ ⟨|c|, abs_nonneg _⟩ hp
      exact_mod_cast h

theorem prop_heat_morrey_hoelder
    {F : ParabolicPoint → ℝ} {G : Fin 3 → ParabolicPoint → ℝ}
    {γ θ₀ θ₁ P : ℝ}
    (hγ : 0 < γ) (hγ1 : γ < 1)
    (hθ₀ : 1 / θ₀ = (2 - γ) / 5)
    (hθ₁ : 1 / θ₁ = (1 - γ) / 5)
    (hP : 1 ≤ P) (hPθ₀ : P ≤ θ₀) (hPθ₁ : P ≤ θ₁)
    (hF : AEMeasurable F volume) (hG : ∀ i : Fin 3, AEMeasurable (G i) volume)
    (hNF : morreyNorm P θ₀ F < ∞)
    (hNG : ∀ i : Fin 3, morreyNorm P θ₁ (G i) < ∞)
    (hSupportF : HasCompactSupport F)
    (hSupportG : ∀ i : Fin 3, HasCompactSupport (G i)) :
    let V : ℝ := (volume (parabolicCylinder 0 0 1)).toReal
    let BF : ℝ := V ^ (1 - 1 / P) * (morreyNorm P θ₀ F).toReal
    let BG : Fin 3 → ℝ := fun i =>
      V ^ (1 - 1 / P) * (morreyNorm P θ₁ (G i)).toReal
    let Cnear : ℝ :=
      2 * 1000 * (2 : ℝ) ^ (8 - 5 / θ₀) *
          (1 - (2 : ℝ) ^ (-γ))⁻¹ * (256 : ℝ) ^ γ * BF +
        ∑ i, 2 * 300000 * (2 : ℝ) ^ (10 - 1 - 5 / θ₁) *
          (1 - (2 : ℝ) ^ (-γ))⁻¹ * (256 : ℝ) ^ γ * BG i
    let C : ℝ :=
      (1800000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₀)) - 16) +
        40000000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₀)) - 20)) * BF +
        ∑ i, (120000000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₁)) - 20) +
          120000000000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₁)) - 24)) * BG i
    ∃ barh : ParabolicPoint → ℝ,
      barh =ᵐ[volume] heatPotential F G ∧
        ParabolicHolderSeminormLE Set.univ barh γ
          (parabolicCampanatoHolderConstant γ P *
            (Cnear + C * (1 - (2 : ℝ) ^ (γ - 1))⁻¹)) ∧
        (∀ z : ParabolicPoint, ∀ R : ℝ, 0 < R →
          ∀ w ∈ Metric.ball z R,
            |barh w| ≤
              (2 : ℝ) ^ γ * (parabolicCampanatoHolderConstant γ P *
                (Cnear + C * (1 - (2 : ℝ) ^ (γ - 1))⁻¹)) * R ^ γ +
                (⨍ x in Metric.ball z R, |heatPotential F G x| ^ P) ^ (1 / P)) := by
  dsimp
  let V : ℝ := (volume (parabolicCylinder 0 0 1)).toReal
  let BF : ℝ := V ^ (1 - 1 / P) * (morreyNorm P θ₀ F).toReal
  let BG : Fin 3 → ℝ := fun i =>
    V ^ (1 - 1 / P) * (morreyNorm P θ₁ (G i)).toReal
  let Cnear : ℝ :=
    2 * 1000 * (2 : ℝ) ^ (8 - 5 / θ₀) *
        (1 - (2 : ℝ) ^ (-γ))⁻¹ * (256 : ℝ) ^ γ * BF +
      ∑ i, 2 * 300000 * (2 : ℝ) ^ (10 - 1 - 5 / θ₁) *
        (1 - (2 : ℝ) ^ (-γ))⁻¹ * (256 : ℝ) ^ γ * BG i
  let C : ℝ :=
    (1800000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₀)) - 16) +
      40000000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₀)) - 20)) * BF +
      ∑ i, (120000000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₁)) - 20) +
        120000000000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₁)) - 24)) * BG i
  have hcamp := heatPotential_global_campanato_bound_of_morrey
    (F := F) (G := G) hγ hγ1 hθ₀ hθ₁ hP hPθ₀ hPθ₁ hF hG hNF hNG
      hSupportF hSupportG
  have hdata := heatPotential_global_data_of_morrey
    (F := F) (G := G) hγ hγ1 hθ₀ hθ₁ hP hPθ₀ hPθ₁ hF hG hNF hNG
      hSupportF hSupportG
  have hlocal : LocallyIntegrable (heatPotential F G) volume := by
    intro x
    exact ⟨@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace x 1,
      Metric.closedBall_mem_nhds x one_pos, (hdata x one_pos).1⟩
  have hCnear : 0 ≤ Cnear := by
    dsimp [Cnear, BF, BG, V]
    have hpow : (2 : ℝ) ^ (-γ) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hγ])
    have hden : 0 ≤ (1 - (2 : ℝ) ^ (-γ))⁻¹ :=
      inv_nonneg.mpr (sub_nonneg.mpr hpow.le)
    positivity
  have hC : 0 ≤ C := by
    dsimp [C, BF, BG, V]
    positivity
  have hratio : 0 ≤ (1 - (2 : ℝ) ^ (γ - 1))⁻¹ := by
    exact inv_nonneg.mpr (sub_nonneg.mpr
      (heat_morrey_geometric_ratio_lt_one hγ1).le)
  have hK : 0 ≤ Cnear + C * (1 - (2 : ℝ) ^ (γ - 1))⁻¹ :=
    add_nonneg hCnear (mul_nonneg hC hratio)
  have hC22 : 0 ≤ parabolicCampanatoHolderConstant γ P := by
    unfold parabolicCampanatoHolderConstant
    have hT : 0 ≤ parabolicCampanatoTailConstant γ := by
      unfold parabolicCampanatoTailConstant
      exact one_div_nonneg.mpr (sub_nonneg.mpr
        (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hγ])).le)
    exact mul_nonneg (mul_nonneg (by linarith only [hT])
      (Real.rpow_nonneg (by norm_num) _)) (Real.rpow_nonneg (by norm_num) _)
  have h := campanato_holder hγ hγ1 hP hK hlocal hdata hcamp
  rcases h with ⟨barh, hbar, hholder⟩
  have hlinfty : ∀ z : ParabolicPoint, ∀ R : ℝ, 0 < R →
      ∀ w ∈ Metric.ball z R,
        |barh w| ≤
          (2 : ℝ) ^ γ * (parabolicCampanatoHolderConstant γ P *
            (Cnear + C * (1 - (2 : ℝ) ^ (γ - 1))⁻¹)) * R ^ γ +
            (⨍ x in Metric.ball z R, |heatPotential F G x| ^ P) ^ (1 / P) := by
    intro z R hR w hw
    let S : Set ParabolicPoint := Metric.ball z R
    have hSpos : 0 < volume S := by
      dsimp [S]
      exact volume_parabolicBall_pos hR
    have hStop : volume S < ∞ := by
      dsimp [S]
      exact volume_parabolicBall_lt_top hR
    have hSmeas : MeasurableSet S := by
      dsimp [S]
      exact measurableSet_ball
    have hdataR := hdata z hR
    have hSint : IntegrableOn (heatPotential F G) S volume := by
      exact hdataR.1.mono_set Metric.ball_subset_closedBall
    have hSabsP : IntegrableOn
        (fun x => |heatPotential F G x| ^ P) S volume := by
      exact (heatPotential_abs_rpow_of_local_data hR hP hdataR.1 hdataR.2).mono_set
        Metric.ball_subset_closedBall
    have hbarS : IntegrableOn barh S volume := by
      have hbarSae : barh =ᵐ[volume.restrict S] heatPotential F G :=
        ae_restrict_of_ae hbar
      exact hSint.congr hbarSae.symm
    have hdiff : IntegrableOn (fun q => barh w - barh q) S volume := by
      exact (integrableOn_const hStop.ne).sub hbarS
    have hdiffabs : IntegrableOn (fun q => |barh w - barh q|) S volume :=
      hdiff.norm
    have hbarabs : IntegrableOn (fun q => |barh q|) S volume := hbarS.abs
    have hdist : ∀ q ∈ S, parabolicDist w q ≤ 2 * R := by
      intro q hq
      rw [← dist_eq_parabolicDist]
      exact (calc
        dist w q ≤ dist w z + dist z q := dist_triangle w z q
        _ < R + R := add_lt_add (Metric.mem_ball.mp hw) (Metric.mem_ball'.mp hq)
        _ = 2 * R := by ring).le
    have hpoint : ∀ q ∈ S,
        |barh w - barh q| ≤
          (parabolicCampanatoHolderConstant γ P *
            (Cnear + C * (1 - (2 : ℝ) ^ (γ - 1))⁻¹)) * (2 * R) ^ γ := by
      intro q hq
      have hpow : parabolicDist w q ^ γ ≤ (2 * R) ^ γ :=
        Real.rpow_le_rpow (parabolicDist_nonneg _ _) (hdist q hq) hγ.le
      have hCK : 0 ≤ parabolicCampanatoHolderConstant γ P *
          (Cnear + C * (1 - (2 : ℝ) ^ (γ - 1))⁻¹) :=
        mul_nonneg hC22 hK
      exact (hholder w (Set.mem_univ _) q (Set.mem_univ _)).trans
        (mul_le_mul_of_nonneg_left hpow hCK)
    have hpt : ∀ q ∈ S, |barh w| ≤
        |barh w - barh q| + |barh q| := by
      intro q _
      calc
        |barh w| = |(barh w - barh q) + barh q| := by ring_nf
        _ ≤ |barh w - barh q| + |barh q| := abs_add_le _ _
    have hmain : |barh w| ≤
        (⨍ q in S, |barh w - barh q|) + ⨍ q in S, |barh q| := by
      calc
        |barh w| = ⨍ q in S, |barh w| :=
          (Integration.setAverage_const_of_pos_of_lt_top hSpos hStop _).symm
        _ ≤ ⨍ q in S, (|barh w - barh q| + |barh q|) :=
          Integration.setAverage_mono_of_ae (integrableOn_const hStop.ne)
            (hdiffabs.add hbarabs) (ae_restrict_of_forall_mem hSmeas hpt)
        _ = (⨍ q in S, |barh w - barh q|) + ⨍ q in S, |barh q| :=
          Integration.setAverage_add_of_integrableOn hdiffabs hbarabs
    have hfirst : (⨍ q in S, |barh w - barh q|) ≤
        (parabolicCampanatoHolderConstant γ P *
          (Cnear + C * (1 - (2 : ℝ) ^ (γ - 1))⁻¹)) * (2 * R) ^ γ := by
      have hmono := Integration.setAverage_mono_of_ae hdiffabs
        (integrableOn_const hStop.ne)
        (ae_restrict_of_forall_mem hSmeas hpoint)
      simpa only [Integration.setAverage_const_of_pos_of_lt_top hSpos hStop]
        using hmono
    have hsecond : (⨍ q in S, |barh q|) ≤
        (⨍ x in S, |heatPotential F G x| ^ P) ^ (1 / P) := by
      have hge : (⨍ q in S, |barh q|) =
          ⨍ q in S, |heatPotential F G q| := by
        exact setAverage_congr_fun hSmeas (by
          filter_upwards [hbar] with q hq _
          rw [hq])
      rw [hge]
      simpa using (Integration.setAverage_abs_rpow_norm_mono
        (f := heatPotential F G) (s := S) (q := 1) (p := P)
        (by norm_num) hP hSpos hStop hSint hSabsP)
    calc
      |barh w| ≤ (⨍ q in S, |barh w - barh q|) + ⨍ q in S, |barh q| := hmain
      _ ≤ (parabolicCampanatoHolderConstant γ P *
            (Cnear + C * (1 - (2 : ℝ) ^ (γ - 1))⁻¹)) * (2 * R) ^ γ +
          (⨍ x in S, |heatPotential F G x| ^ P) ^ (1 / P) :=
        add_le_add hfirst hsecond
      _ = (2 : ℝ) ^ γ * (parabolicCampanatoHolderConstant γ P *
            (Cnear + C * (1 - (2 : ℝ) ^ (γ - 1))⁻¹)) * R ^ γ +
          (⨍ x in Metric.ball z R, |heatPotential F G x| ^ P) ^ (1 / P) := by
        rw [Real.mul_rpow (by norm_num) hR.le]
        simp only [S]
        ring
  refine ⟨barh, ?_, ?_, ?_⟩
  · exact hbar
  · simpa [Cnear, C, BF, BG, V] using hholder
  · simpa [Cnear, C, BF, BG, V] using hlinfty


end CKN.Core.HeatPotential
