/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesAmplitude

/-! # Iterates Higher Energy Budget

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4

/-- The actual factorial weight at coordinate order n and increment i. -/
def iterateAnalyticWeight (n i : ℕ) (L : ℝ) : ℝ :=
  ((n + 2 * i).factorial : ℝ) * L ^ n

/-- Explicit remainder of the differentiated higher-increment energy equation.
It keeps the corrected term linear in q, both preceding amplitudes, and both lower
current-order kernels. This is a real formula, not an assumed energy estimate. -/
def iterateHigherEnergyBudget (n i : ℕ)
    (κ D a e L Ccoef Cs Cv Cf Gcur Gprev Gprevprev Nprev ρ q : ℝ)
    (d : ℕ → ℝ) : ℝ :=
  16 * Cs ^ 2 * q ^ 2 * Nprev ^ 2 * iterateAnalyticWeight n (i + 1) L ^ 2 +
  Cs ^ 2 * q ^ 2 * κ *
    ((192 + 13056 * Cv ^ 2) * Gprev ^ 2 * iterateAnalyticWeight n (i + 1) L ^ 2 +
      12288 * Ccoef ^ 2 * Gprevprev ^ 2 * iterateAnalyticWeight n i L ^ 2) +
  (24 * Cs ^ 2 * q ^ 2 + (1 + Cs ^ 2 * (32 * Ccoef ^ 2)) * q) *
    (4 * κ * Gprev ^ 2 * iterateAnalyticWeight n (i + 1) L ^ 2) +
  384 * Cf ^ 2 * ρ ^ 2 * (κ * Gprev ^ 2 * iterateAnalyticWeight n i L ^ 2) +
  32 * κ * Ccoef ^ 2 * ρ ^ 2 * Gprev ^ 2 * iterateAnalyticWeight n i L ^ 2 +
  2 * ((2 : ℝ) ^ 19 * a) * Gcur ^ 2 / L ^ 2 * iterateAnalyticWeight n (i + 1) L ^ 2 *
    (if n = 0 then 0 else d (n - 1) ^ 2) +
  16 / κ * (32 * a * e ^ 2) ^ 2 * Gcur ^ 2 * (2 * ((256 * e⁻¹) / L) ^ 2) ^ 2 *
    iterateAnalyticWeight n (i + 1) L ^ 2 *
    (∑ k ∈ Finset.range (n - 1), (1 / (4 : ℝ)) ^ k * d (n - 2 - k) ^ 2) +
  8 * D * (8192 * a * e) * Gprev * Gcur * (256 * e⁻¹) *
    iterateAnalyticWeight n (i + 1) L ^ 2 *
    ∑ k ∈ Finset.range n, (1 / (2 : ℝ)) ^ k * d (n - 1 - k)

/-- Explicit exceptional first-increment budget. Its material terms have
q squared; the lower current-order drift convolution is retained separately. -/
def iterateFirstEnergyBudget (n : ℕ)
    (κ D a e r L C Ccoef B Gcur N ρ q : ℝ) (d : ℕ → ℝ) : ℝ :=
  (16 * C ^ 2 + 24 * C ^ 2 * (8 + 544 * C ^ 2) +
    (96 * C ^ 2 + (8 + 32 * Real.sqrt (8 + 64 * C ^ 2)) * C ^ 2 +
      1 + 128 * C ^ 2 * Ccoef ^ 2)) * q ^ 2 * N ^ 2 * iterateAnalyticWeight n 1 L ^ 2 +
  384 * C ^ 2 * ρ ^ 2 * (N ^ 2 * iterateAnalyticWeight n 0 L ^ 2) +
  32 * Ccoef ^ 2 * ρ ^ 2 * N ^ 2 * iterateAnalyticWeight n 0 L ^ 2 +
  2 * ((2 : ℝ) ^ 19 * a) * Gcur ^ 2 / L ^ 2 * iterateAnalyticWeight n 1 L ^ 2 *
    (if n = 0 then 0 else d (n - 1) ^ 2) +
  16 / κ * (32 * a * e ^ 2) ^ 2 * Gcur ^ 2 * (2 * ((256 * e⁻¹) / L) ^ 2) ^ 2 *
    iterateAnalyticWeight n 1 L ^ 2 *
    (∑ k ∈ Finset.range (n - 1), (1 / (4 : ℝ)) ^ k * d (n - 2 - k) ^ 2) +
  8 * D * B * (N / Real.sqrt κ) * Gcur * r * iterateAnalyticWeight n 1 L ^ 2 *
    ∑ k ∈ Finset.range n, (1 / (2 : ℝ)) ^ k * d (n - 1 - k)

end AVenhance.Infra.Section4
