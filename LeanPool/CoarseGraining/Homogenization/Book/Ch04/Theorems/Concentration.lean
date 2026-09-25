/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Tails
public import Mathlib.Order.Filter.Finite
public import LeanPool.CoarseGraining.Homogenization.Probability.IndependentSums.GammaSigmaConcentration
public import LeanPool.CoarseGraining.Homogenization.Probability.IndependentSums.GammaSigmaExpRegime
public import LeanPool.CoarseGraining.Homogenization.Probability.IndependentSums.PsiConcentration
public import LeanPool.CoarseGraining.Homogenization.Probability.IndependentSums.PsiSigma
public import LeanPool.CoarseGraining.Homogenization.Probability.IndependentSums.Rosenthal

/-! # Concentration -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch04

/-!
# Public Section 4.2 concentration theorems

This file exposes the already-proved independent-sums results from Section 4.2
under the public Chapter 4 namespace.  Unlike the local-observable and
partition-average files, these are direct imported theorem endpoints: each
theorem is proved by the existing probability mini-library.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Explicit growth constant for the stretched-exponential class. -/
noncomputable abbrev gammaGrowthConst (σ : ℝ) : ℝ :=
  IndependentSums.gammaGrowthConst σ

/-- Explicit growth constant for the log-normal class. -/
noncomputable abbrev psiGrowthConst (σ : ℝ) : ℝ :=
  IndependentSums.psiGrowthConst σ

/-- The finite-family weak-tail triangle constant supplied by the Chapter 4
growth hypothesis. -/
noncomputable abbrev psiGrowthTriangleConst (K : ℝ) : ℝ :=
  4 * K ^ (12 : ℝ)

/-- The stretched-exponential weak-tail triangle constant. -/
noncomputable abbrev gammaTriangleConst (σ : ℝ) : ℝ :=
  IndependentSums.gammaTriangleConst σ

/-- The log-normal weak-tail triangle constant. -/
noncomputable abbrev psiSigmaTriangleConst (σ : ℝ) : ℝ :=
  IndependentSums.psiSigmaTriangleConst σ

/-- The moment-growth constant attached to `Gamma_sigma`. -/
noncomputable abbrev gammaMomentConst (σ : ℝ) : ℝ :=
  IndependentSums.gammaMomentConst σ

/-- The event-indicator scale `|log p|^{-1/sigma}` for `Gamma_sigma` tails. -/
noncomputable abbrev gammaIndicatorScale (σ p : ℝ) : ℝ :=
  IndependentSums.gammaIndicatorScale σ p

/-- Explicit product constant for the `Gamma_sigma` calculus.  If
`tau = sigma_1 sigma_2 / (sigma_1 + sigma_2)`, then the product rule below uses
the witness `2^(1/tau) A_1 A_2`. -/
noncomputable abbrev gammaProductConst (σ₁ σ₂ : ℝ) : ℝ :=
  2 ^ ((σ₁ * σ₂ / (σ₁ + σ₂))⁻¹)

/-- The Rosenthal/Bennett universal constant used in the finite-moment
endpoint. -/
noncomputable abbrev rosenthalBennettIntegralConst : ℝ :=
  IndependentSums.rosenthalBennettIntegralConst

/-- The exponential-regime endpoint constant for centered independent
`Gamma_sigma` summands. -/
noncomputable abbrev gammaSigmaExpRegimeEndpointConst (σ : ℝ) : ℝ :=
  IndependentSums.gammaSigmaExpRegimeEndpointConst σ

/-- The heavy-tail endpoint constant for centered independent `Gamma_sigma`
summands on the range `0 < sigma < 1`. -/
noncomputable abbrev gammaSigmaHeavyTailEndpointConst (σ : ℝ) : ℝ :=
  IndependentSums.gammaSigmaHeavyTailEndpointConst σ

/-- A public constant for the full `0 < sigma ≤ 2` centered independent
`Gamma_sigma` concentration theorem. -/
noncomputable def gammaSigmaIndependentSumConst (σ : ℝ) : ℝ :=
  if σ < 1 then gammaSigmaHeavyTailEndpointConst σ else gammaSigmaExpRegimeEndpointConst σ

/-- The log-normal centered independent-sum constant. -/
noncomputable abbrev psiSigmaIndependentSumConst (σ : ℝ) : ℝ :=
  IndependentSums.psiSigmaIndependentSumConst σ

/-! ## Weak-tail model classes and calculus -/

/-- The stretched-exponential model class is admissible. -/
theorem admissiblePsi_gammaSigma {σ : ℝ} (hσ : 0 ≤ σ) :
    AdmissiblePsi (gammaSigma σ) :=
  IndependentSums.admissiblePsi_gammaSigma hσ

/-- The log-normal model class is admissible. -/
theorem admissiblePsi_psiSigma {σ : ℝ} (hσ : 0 ≤ σ) :
    AdmissiblePsi (psiSigma σ) :=
  IndependentSums.admissiblePsi_psiSigma hσ

/-- Tail interpretation of the one-sided relation `X ≤ O_{Gamma_sigma}(A)`. -/
theorem isBigOWith_gammaSigma_iff {X : Ω → ℝ} {A σ : ℝ} :
    IsBigOWith μ (gammaSigma σ) X A ↔
      ∀ ⦃t : ℝ⦄, 1 ≤ t →
        μ.real (upperTailEvent X (A * t)) ≤ Real.exp (-(t ^ σ)) := by
  simpa using
    (IndependentSums.isBigOWith_gammaSigma_iff (μ := μ) (X := X) (A := A)
      (σ := σ))

/-- Tail interpretation of `X = O_{Gamma_sigma}(A)`. -/
theorem isBigO_gammaSigma_iff {X : Ω → ℝ} {A σ : ℝ} :
    IsBigO μ (gammaSigma σ) X A ↔
      ∀ ⦃t : ℝ⦄, 1 ≤ t →
        μ.real (absTailEvent X (A * t)) ≤ Real.exp (-(t ^ σ)) := by
  simpa using
    (IndependentSums.isBigO_gammaSigma_iff (μ := μ) (X := X) (A := A) (σ := σ))

/-- A stretched-exponential tail at exponent `σ` implies the same scale at
any smaller exponent `ρ`. -/
theorem IsBigOWith.gammaSigma_mono_exponent {X : Ω → ℝ} {A ρ σ : ℝ}
    (hρσ : ρ ≤ σ)
    (hX : IsBigOWith μ (gammaSigma σ) X A) :
    IsBigOWith μ (gammaSigma ρ) X A := by
  rw [isBigOWith_gammaSigma_iff] at hX ⊢
  intro t ht
  have hpow : t ^ ρ ≤ t ^ σ :=
    Real.rpow_le_rpow_of_exponent_le ht hρσ
  exact (hX ht).trans ((Real.exp_le_exp).2 (neg_le_neg hpow))

/-- A symmetric stretched-exponential tail at exponent `σ` implies the same
scale at any smaller exponent `ρ`. -/
theorem IsBigO.gammaSigma_mono_exponent {X : Ω → ℝ} {A ρ σ : ℝ}
    (hρσ : ρ ≤ σ)
    (hX : IsBigO μ (gammaSigma σ) X A) :
    IsBigO μ (gammaSigma ρ) X A := by
  rw [isBigO_gammaSigma_iff] at hX ⊢
  intro t ht
  have hpow : t ^ ρ ≤ t ^ σ :=
    Real.rpow_le_rpow_of_exponent_le ht hρσ
  exact (hX ht).trans ((Real.exp_le_exp).2 (neg_le_neg hpow))

/-- Tail interpretation of the one-sided relation `X ≤ O_{Psi_sigma}(A)`. -/
theorem isBigOWith_psiSigma_iff {X : Ω → ℝ} {A σ : ℝ} :
    IsBigOWith μ (psiSigma σ) X A ↔
      ∀ ⦃t : ℝ⦄, 1 ≤ t →
        μ.real (upperTailEvent X (A * t)) ≤
          Real.exp (-((σ ^ (2 : ℕ))⁻¹ * (Real.log (1 + σ * t)) ^ (2 : ℕ))) := by
  simpa using
    (IndependentSums.isBigOWith_psiSigma_iff (μ := μ) (X := X) (A := A)
      (σ := σ))

/-- Tail interpretation of `X = O_{Psi_sigma}(A)`. -/
theorem isBigO_psiSigma_iff {X : Ω → ℝ} {A σ : ℝ} :
    IsBigO μ (psiSigma σ) X A ↔
      ∀ ⦃t : ℝ⦄, 1 ≤ t →
        μ.real (absTailEvent X (A * t)) ≤
          Real.exp (-((σ ^ (2 : ℕ))⁻¹ * (Real.log (1 + σ * t)) ^ (2 : ℕ))) := by
  simpa using
    (IndependentSums.isBigO_psiSigma_iff (μ := μ) (X := X) (A := A) (σ := σ))

/-- `Gamma_sigma` satisfies the Chapter 4 weak-tail growth hypothesis. -/
theorem hasPsiGrowth_gammaSigma {σ : ℝ} (hσ : 0 < σ) :
    HasPsiGrowth (gammaSigma σ) (gammaGrowthConst σ) :=
  IndependentSums.hasPsiGrowth_gammaSigma hσ

/-- The explicit `Gamma_sigma` growth constant is admissible for the Chapter 4
calculus. -/
theorem two_le_gammaGrowthConst (σ : ℝ) :
    2 ≤ gammaGrowthConst σ :=
  IndependentSums.two_le_gammaGrowthConst σ

/-- `Psi_sigma` satisfies the Chapter 4 weak-tail growth hypothesis. -/
theorem hasPsiGrowth_psiSigma {σ : ℝ} (hσ : 1 ≤ σ) :
    HasPsiGrowth (psiSigma σ) (psiGrowthConst σ) :=
  IndependentSums.hasPsiGrowth_psiSigma hσ

/-- The explicit `Psi_sigma` growth constant is admissible for the Chapter 4
calculus. -/
theorem two_le_psiGrowthConst (σ : ℝ) :
    2 ≤ psiGrowthConst σ :=
  IndependentSums.two_le_psiGrowthConst σ

/-- Polynomial powers can be absorbed by dilating a weak-tail profile satisfying
the Chapter 4 growth hypothesis. -/
theorem hasPsiGrowth_rpow_absorption
    {Ψ : ℝ → ℝ} {K p t : ℝ} (hK : 1 ≤ K) (hΨ : HasPsiGrowth Ψ K)
    (hAdmissible : AdmissiblePsi Ψ) (ht : 1 ≤ t) :
    t ^ p * Ψ t ≤ Ψ ((K ^ Nat.ceil p) * t) :=
  IndependentSums.hasPsiGrowth_rpow_absorption hK hΨ hAdmissible ht

/-- The growth hypothesis forces log-squared minimal growth of an admissible
weak-tail profile. -/
theorem admissiblePsi_minimalGrowth
    {Ψ : ℝ → ℝ} {K t : ℝ} (hK : 2 ≤ K) (hΨ : HasPsiGrowth Ψ K)
    (hAdmissible : AdmissiblePsi Ψ) (ht : K ^ (2 : ℕ) ≤ t) :
    Real.exp (Real.log t ^ (2 : ℕ) / (9 * Real.log K)) ≤ Ψ t :=
  IndependentSums.admissiblePsi_minimalGrowth hK hΨ hAdmissible ht

/-- The growth hypothesis yields the abstract doubling estimate used in the
weak-tail triangle inequality. -/
theorem admissiblePsi_doubling
    {Ψ : ℝ → ℝ} {K q t s : ℝ} (hK : 2 ≤ K) (hΨ : HasPsiGrowth Ψ K)
    (hAdmissible : AdmissiblePsi Ψ) (hq : 2 ≤ q) (ht : 1 ≤ t) (hs : 1 ≤ s) :
    s ^ q ≤ K ^ (3 * q ^ (2 : ℕ)) * (Ψ (t * s) / Ψ t) :=
  IndependentSums.admissiblePsi_doubling hK hΨ hAdmissible hq ht hs

/-- The `q = 2` abstract doubling package generated by the growth hypothesis. -/
theorem admissiblePsi_hasPsiAbstractDoubling_two
    {Ψ : ℝ → ℝ} {K : ℝ} (hK : 2 ≤ K) (hΨ : HasPsiGrowth Ψ K)
    (hAdmissible : AdmissiblePsi Ψ) :
    HasPsiAbstractDoubling Ψ 2 (K ^ (12 : ℝ)) :=
  IndependentSums.admissiblePsi_hasPsiAbstractDoubling_two hK hΨ hAdmissible

/-- Finite-family generalized triangle inequality for a weak-tail profile
satisfying the Chapter 4 growth hypothesis. -/
theorem isBigO_finset_sum_of_isBigO_growth
    (s : Finset ι) {X : ι → Ω → ℝ} {a : ι → ℝ} {Ψ : ℝ → ℝ} {K : ℝ}
    [IsFiniteMeasure μ]
    (hK : 2 ≤ K) (hGrowth : HasPsiGrowth Ψ K)
    (hAdmissible : AdmissiblePsi Ψ)
    (hs : s.Nonempty)
    (ha : ∀ i ∈ s, 0 < a i)
    (hX : ∀ i ∈ s, IsBigO μ Ψ (X i) (a i))
    (hXm : ∀ i ∈ s, Measurable (X i)) :
    IsBigO μ Ψ (fun ω => Finset.sum s (fun i => X i ω))
      (psiGrowthTriangleConst K * Finset.sum s a) := by
  simpa [psiGrowthTriangleConst] using
    IndependentSums.isBigO_finset_sum_of_isBigO_growth_four_mul
      (μ := μ) (s := s) (X := X) (a := a) (Ψ := Ψ) (K := K)
      hK hGrowth hAdmissible hs ha hX hXm

/-- Average version of the growth-based weak-tail triangle inequality. -/
theorem isBigO_finsetAverage_of_isBigO_growth
    (s : Finset ι) {X : ι → Ω → ℝ} {a : ι → ℝ} {Ψ : ℝ → ℝ} {K : ℝ}
    [IsFiniteMeasure μ]
    (hK : 2 ≤ K) (hGrowth : HasPsiGrowth Ψ K)
    (hAdmissible : AdmissiblePsi Ψ)
    (hs : s.Nonempty)
    (ha : ∀ i ∈ s, 0 < a i)
    (hX : ∀ i ∈ s, IsBigO μ Ψ (X i) (a i))
    (hXm : ∀ i ∈ s, Measurable (X i)) :
    IsBigO μ Ψ
      (fun ω => ((s.card : ℝ)⁻¹) * Finset.sum s (fun i => X i ω))
      (psiGrowthTriangleConst K * (((s.card : ℝ)⁻¹) * Finset.sum s a)) := by
  simpa [psiGrowthTriangleConst] using
    IndependentSums.isBigO_finsetAverage_of_isBigO_growth_four_mul
      (μ := μ) (s := s) (X := X) (a := a) (Ψ := Ψ) (K := K)
      hK hGrowth hAdmissible hs ha hX hXm

/-- Finite-family generalized triangle inequality for `Gamma_sigma` tails. -/
theorem isBigO_finset_sum_of_isBigO_gammaSigma
    (s : Finset ι) {X : ι → Ω → ℝ} {a : ι → ℝ} {σ : ℝ}
    [IsFiniteMeasure μ]
    (hσ : 0 < σ)
    (hs : s.Nonempty)
    (ha : ∀ i ∈ s, 0 < a i)
    (hX : ∀ i ∈ s, IsBigO μ (gammaSigma σ) (X i) (a i))
    (hXm : ∀ i ∈ s, Measurable (X i)) :
    IsBigO μ (gammaSigma σ) (fun ω => Finset.sum s (fun i => X i ω))
      (gammaTriangleConst σ * Finset.sum s a) := by
  simpa [gammaTriangleConst] using
    IndependentSums.isBigO_finset_sum_of_isBigO_gammaSigma
      (μ := μ) (s := s) (X := X) (a := a) (σ := σ) hσ hs ha hX hXm

/-- Average version of the generalized triangle inequality for `Gamma_sigma`
tails. -/
theorem isBigO_finsetAverage_of_isBigO_gammaSigma
    (s : Finset ι) {X : ι → Ω → ℝ} {a : ι → ℝ} {σ : ℝ}
    [IsFiniteMeasure μ]
    (hσ : 0 < σ)
    (hs : s.Nonempty)
    (ha : ∀ i ∈ s, 0 < a i)
    (hX : ∀ i ∈ s, IsBigO μ (gammaSigma σ) (X i) (a i))
    (hXm : ∀ i ∈ s, Measurable (X i)) :
    IsBigO μ (gammaSigma σ)
      (fun ω => ((s.card : ℝ)⁻¹) * Finset.sum s (fun i => X i ω))
      (gammaTriangleConst σ * (((s.card : ℝ)⁻¹) * Finset.sum s a)) := by
  simpa [gammaTriangleConst] using
    IndependentSums.isBigO_finsetAverage_of_isBigO_gammaSigma
      (μ := μ) (s := s) (X := X) (a := a) (σ := σ) hσ hs ha hX hXm

/-- Finite-family generalized triangle inequality for `Psi_sigma` tails. -/
theorem isBigO_finset_sum_of_isBigO_psiSigma
    (s : Finset ι) {X : ι → Ω → ℝ} {a : ι → ℝ} {σ : ℝ}
    [IsFiniteMeasure μ]
    (hσ : 1 ≤ σ)
    (hs : s.Nonempty)
    (ha : ∀ i ∈ s, 0 < a i)
    (hX : ∀ i ∈ s, IsBigO μ (psiSigma σ) (X i) (a i))
    (hXm : ∀ i ∈ s, Measurable (X i)) :
    IsBigO μ (psiSigma σ) (fun ω => Finset.sum s (fun i => X i ω))
      (psiSigmaTriangleConst σ * Finset.sum s a) := by
  simpa [psiSigmaTriangleConst] using
    IndependentSums.isBigO_finset_sum_of_isBigO_psiSigma
      (μ := μ) (s := s) (X := X) (a := a) (σ := σ) hσ hs ha hX hXm

/-- Average version of the generalized triangle inequality for `Psi_sigma`
tails. -/
theorem isBigO_finsetAverage_of_isBigO_psiSigma
    (s : Finset ι) {X : ι → Ω → ℝ} {a : ι → ℝ} {σ : ℝ}
    [IsFiniteMeasure μ]
    (hσ : 1 ≤ σ)
    (hs : s.Nonempty)
    (ha : ∀ i ∈ s, 0 < a i)
    (hX : ∀ i ∈ s, IsBigO μ (psiSigma σ) (X i) (a i))
    (hXm : ∀ i ∈ s, Measurable (X i)) :
    IsBigO μ (psiSigma σ)
      (fun ω => ((s.card : ℝ)⁻¹) * Finset.sum s (fun i => X i ω))
      (psiSigmaTriangleConst σ * (((s.card : ℝ)⁻¹) * Finset.sum s a)) := by
  simpa [psiSigmaTriangleConst] using
    IndependentSums.isBigO_finsetAverage_of_isBigO_psiSigma
      (μ := μ) (s := s) (X := X) (a := a) (σ := σ) hσ hs ha hX hXm

/-- Product rule for nonnegative stretched-exponential upper tails, with
explicit constant `2^(1/tau)`, `tau = sigma_1 sigma_2 / (sigma_1 + sigma_2)`. -/
theorem isBigOWith_gammaSigma_mul
    {X Y : Ω → ℝ} {A B σ₁ σ₂ : ℝ}
    [IsFiniteMeasure μ]
    (hσ₁ : 0 < σ₁) (hσ₂ : 0 < σ₂)
    (hA : 0 ≤ A) (_hB : 0 ≤ B)
    (_hX_nonneg : ∀ ω, 0 ≤ X ω) (hY_nonneg : ∀ ω, 0 ≤ Y ω)
    (hX : IsBigOWith μ (gammaSigma σ₁) X A)
    (hY : IsBigOWith μ (gammaSigma σ₂) Y B) :
    IsBigOWith μ (gammaSigma (σ₁ * σ₂ / (σ₁ + σ₂)))
      (fun ω => X ω * Y ω) (gammaProductConst σ₁ σ₂ * A * B) := by
  intro t ht
  let τ : ℝ := σ₁ * σ₂ / (σ₁ + σ₂)
  let L : ℝ := gammaProductConst σ₁ σ₂
  let u : ℝ := (L * t) ^ (τ / σ₁)
  let v : ℝ := (L * t) ^ (τ / σ₂)
  have hσsum_pos : 0 < σ₁ + σ₂ := add_pos hσ₁ hσ₂
  have hτ_pos : 0 < τ := by
    dsimp [τ]
    exact div_pos (mul_pos hσ₁ hσ₂) hσsum_pos
  have hL_pos : 0 < L := by
    dsimp [L, gammaProductConst, τ]
    exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
  have hL_one : 1 ≤ L := by
    dsimp [L, gammaProductConst, τ]
    exact Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2) (inv_nonneg.mpr hτ_pos.le)
  have ht_nonneg : 0 ≤ t := le_trans zero_le_one ht
  have hLt_one : 1 ≤ L * t := by nlinarith
  have hLt_nonneg : 0 ≤ L * t := le_trans zero_le_one hLt_one
  have hLt_pos : 0 < L * t := lt_of_lt_of_le zero_lt_one hLt_one
  have hu_one : 1 ≤ u := by
    dsimp [u]
    exact Real.one_le_rpow hLt_one (div_nonneg hτ_pos.le hσ₁.le)
  have hv_one : 1 ≤ v := by
    dsimp [v]
    exact Real.one_le_rpow hLt_one (div_nonneg hτ_pos.le hσ₂.le)
  have hL_pow : L ^ τ = 2 := by
    dsimp [L, gammaProductConst, τ]
    calc
      ((2 : ℝ) ^ τ⁻¹) ^ τ = (2 : ℝ) ^ (τ⁻¹ * τ) := by
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ = (2 : ℝ) := by
        rw [inv_mul_cancel₀ hτ_pos.ne', Real.rpow_one]
  have hu_pow : u ^ σ₁ = 2 * t ^ τ := by
    calc
      u ^ σ₁ = (L * t) ^ ((τ / σ₁) * σ₁) := by
        dsimp [u]
        rw [← Real.rpow_mul hLt_nonneg]
      _ = (L * t) ^ τ := by
        congr 1
        field_simp [hσ₁.ne']
      _ = L ^ τ * t ^ τ := by
        rw [Real.mul_rpow hL_pos.le ht_nonneg]
      _ = 2 * t ^ τ := by
        rw [hL_pow]
  have hv_pow : v ^ σ₂ = 2 * t ^ τ := by
    calc
      v ^ σ₂ = (L * t) ^ ((τ / σ₂) * σ₂) := by
        dsimp [v]
        rw [← Real.rpow_mul hLt_nonneg]
      _ = (L * t) ^ τ := by
        congr 1
        field_simp [hσ₂.ne']
      _ = L ^ τ * t ^ τ := by
        rw [Real.mul_rpow hL_pos.le ht_nonneg]
      _ = 2 * t ^ τ := by
        rw [hL_pow]
  have huv : u * v = L * t := by
    calc
      u * v = (L * t) ^ (τ / σ₁) * (L * t) ^ (τ / σ₂) := rfl
      _ = (L * t) ^ (τ / σ₁ + τ / σ₂) := by
        rw [← Real.rpow_add hLt_pos]
      _ = (L * t) ^ (1 : ℝ) := by
        congr 1
        dsimp [τ]
        field_simp [hσ₁.ne', hσ₂.ne', hσsum_pos.ne']
        ring
      _ = L * t := by
        rw [Real.rpow_one]
  have hthreshold : (A * u) * (B * v) = (gammaProductConst σ₁ σ₂ * A * B) * t := by
    calc
      (A * u) * (B * v) = A * B * (u * v) := by ring
      _ = A * B * (L * t) := by rw [huv]
      _ = (gammaProductConst σ₁ σ₂ * A * B) * t := by
        dsimp [L]
        ring
  have hsubset :
      upperTailEvent (fun ω => X ω * Y ω)
          ((gammaProductConst σ₁ σ₂ * A * B) * t) ⊆
        upperTailEvent X (A * u) ∪ upperTailEvent Y (B * v) := by
    intro ω hω
    by_cases hXu : A * u < X ω
    · exact Or.inl hXu
    · right
      by_contra hYv
      have hX_le : X ω ≤ A * u := not_lt.mp hXu
      have hY_le : Y ω ≤ B * v := not_lt.mp hYv
      have hu_nonneg : 0 ≤ u := Real.rpow_nonneg hLt_nonneg _
      have hAu_nonneg : 0 ≤ A * u := mul_nonneg hA hu_nonneg
      have hprod_le : X ω * Y ω ≤ (A * u) * (B * v) :=
        mul_le_mul hX_le hY_le (hY_nonneg ω) hAu_nonneg
      exact not_lt_of_ge (by simpa [hthreshold] using hprod_le) hω
  have hX_tail :
      μ.real (upperTailEvent X (A * u)) ≤ Real.exp (-(2 * t ^ τ)) := by
    simpa [gammaSigma, hu_pow, Real.exp_neg] using hX hu_one
  have hY_tail :
      μ.real (upperTailEvent Y (B * v)) ≤ Real.exp (-(2 * t ^ τ)) := by
    simpa [gammaSigma, hv_pow, Real.exp_neg] using hY hv_one
  calc
    μ.real (upperTailEvent (fun ω => X ω * Y ω)
        ((gammaProductConst σ₁ σ₂ * A * B) * t))
      ≤ μ.real (upperTailEvent X (A * u) ∪ upperTailEvent Y (B * v)) := by
          exact measureReal_mono hsubset
    _ ≤ μ.real (upperTailEvent X (A * u)) + μ.real (upperTailEvent Y (B * v)) := by
          exact measureReal_union_le _ _
    _ ≤ Real.exp (-(2 * t ^ τ)) + Real.exp (-(2 * t ^ τ)) := by
          exact add_le_add hX_tail hY_tail
    _ = 2 * Real.exp (-2 * t ^ τ) := by ring_nf
    _ ≤ Real.exp (-(t ^ τ)) := by
          exact IndependentSums.two_mul_exp_neg_two_mul_le_exp_neg
            (x := t ^ τ) (Real.one_le_rpow ht hτ_pos.le)
    _ = (gammaSigma (σ₁ * σ₂ / (σ₁ + σ₂)) t)⁻¹ := by
          simp [gammaSigma, τ, Real.exp_neg]

/-- Power rule for nonnegative stretched-exponential upper-tail bounds. -/
theorem isBigOWith_gammaSigma_rpow_iff
    {X : Ω → ℝ} {A σ p : ℝ}
    [IsFiniteMeasure μ]
    (hp : 0 < p) (hA : 0 ≤ A) (hX_nonneg : ∀ ω, 0 ≤ X ω) :
    IsBigOWith μ (gammaSigma σ) X A ↔
      IsBigOWith μ (gammaSigma (σ / p)) (fun ω => X ω ^ p) (A ^ p) := by
  simpa using
    IndependentSums.isBigOWith_gammaSigma_rpow_iff
      (μ := μ) (X := X) (A := A) (σ := σ) (p := p) hp hA hX_nonneg

/-- Symmetric power rule for stretched-exponential tails. -/
theorem isBigO_gammaSigma_rpow_iff
    {X : Ω → ℝ} {A σ p : ℝ}
    [IsFiniteMeasure μ]
    (hp : 0 < p) (hA : 0 ≤ A) :
    IsBigO μ (gammaSigma σ) X A ↔
      IsBigO μ (gammaSigma (σ / p)) (fun ω => |X ω| ^ p) (A ^ p) := by
  simpa using
    IndependentSums.isBigO_gammaSigma_rpow_iff
      (μ := μ) (X := X) (A := A) (σ := σ) (p := p) hp hA

/-- Finite maximum rule for common-scale nonnegative `Gamma_sigma` upper-tail
bounds. -/
theorem isBigOWith_gammaSigma_finset_sup'
    (s : Finset ι) (hs : s.Nonempty) {X : ι → Ω → ℝ} {A σ : ℝ}
    [IsFiniteMeasure μ]
    (hσ : 0 < σ) (hs_card : 2 ≤ s.card)
    (hX : ∀ i ∈ s, IsBigOWith μ (gammaSigma σ) (X i) A) :
    IsBigOWith μ (gammaSigma σ) (fun ω => s.sup' hs (fun i => X i ω))
      (((3 * Real.log (s.card : ℝ)) ^ σ⁻¹) * A) := by
  simpa using
    IndependentSums.isBigOWith_gammaSigma_finset_sup'
      (μ := μ) (s := s) (hs := hs) (X := X) (A := A) (σ := σ)
      hσ hs_card hX

/-- Finite maximum rule for symmetric `Gamma_sigma` tails with nonuniform
scales. -/
theorem isBigO_gammaSigma_finset_sup'_of_scales
    (s : Finset ι) (hs : s.Nonempty) {X : ι → Ω → ℝ} {a : ι → ℝ} {σ : ℝ}
    [IsFiniteMeasure μ]
    (hσ : 0 < σ) (hs_card : 2 ≤ s.card)
    (hX : ∀ i ∈ s, IsBigO μ (gammaSigma σ) (X i) (a i)) :
    IsBigO μ (gammaSigma σ) (fun ω => s.sup' hs (fun i => X i ω))
      (((3 * Real.log (s.card : ℝ)) ^ σ⁻¹) * s.sup' hs a) := by
  simpa using
    IndependentSums.isBigO_gammaSigma_finset_sup'_of_scales
      (μ := μ) (s := s) (hs := hs) (X := X) (a := a) (σ := σ)
      hσ hs_card hX

/-- Event indicators have the logarithmic `Gamma_sigma` scale from the notes. -/
theorem isBigOWith_gammaSigma_indicator
    {E : Set Ω} {σ : ℝ}
    (hσ : 0 < σ) (hE_pos : 0 < μ.real E) (hE_lt_one : μ.real E < 1) :
    IsBigOWith μ (gammaSigma σ) (E.indicator fun _ => (1 : ℝ))
      (gammaIndicatorScale σ (μ.real E)) := by
  simpa [gammaIndicatorScale] using
    IndependentSums.isBigOWith_gammaSigma_indicator
      (μ := μ) (E := E) (σ := σ) hσ hE_pos hE_lt_one

/-- Symmetric event-indicator `Gamma_sigma` bound. -/
theorem isBigO_gammaSigma_indicator
    {E : Set Ω} {σ : ℝ}
    (hσ : 0 < σ) (hE_pos : 0 < μ.real E) (hE_lt_one : μ.real E < 1) :
    IsBigO μ (gammaSigma σ) (E.indicator fun _ => (1 : ℝ))
      (gammaIndicatorScale σ (μ.real E)) := by
  simpa [gammaIndicatorScale] using
    IndependentSums.isBigO_gammaSigma_indicator
      (μ := μ) (E := E) (σ := σ) hσ hE_pos hE_lt_one

/-! ## Moment growth and Rosenthal -/

/-- Moment growth of order `p^(1/sigma)` implies stretched-exponential upper
tails with the Chapter 4 constant `e M`. -/
theorem isBigOWith_gammaSigma_of_moment_growth
    {Y : Ω → ℝ} {M σ : ℝ}
    [IsProbabilityMeasure μ]
    (hσ : 0 < σ) (hM : 0 < M) (hY_nonneg : ∀ ω, 0 ≤ Y ω)
    (hY :
      ∀ ⦃p : ℝ⦄, 1 ≤ p →
        Integrable (fun ω => Y ω ^ p) μ ∧
          ∫ ω, Y ω ^ p ∂μ ≤ (M * p ^ σ⁻¹) ^ p) :
    IsBigOWith μ (gammaSigma σ) Y (Real.exp 1 * M) :=
  IndependentSums.isBigOWith_gammaSigma_of_moment_growth
    (μ := μ) (Y := Y) (M := M) (σ := σ) hσ hM hY_nonneg hY

/-- Symmetric moment-growth criterion for `Gamma_sigma` tails. -/
theorem isBigO_gammaSigma_of_moment_growth
    {X : Ω → ℝ} {M σ : ℝ}
    [IsProbabilityMeasure μ]
    (hσ : 0 < σ) (hM : 0 < M)
    (hX :
      ∀ ⦃p : ℝ⦄, 1 ≤ p →
        Integrable (fun ω => |X ω| ^ p) μ ∧
          ∫ ω, |X ω| ^ p ∂μ ≤ (M * p ^ σ⁻¹) ^ p) :
    IsBigO μ (gammaSigma σ) X (Real.exp 1 * M) :=
  IndependentSums.isBigO_gammaSigma_of_moment_growth
    (μ := μ) (X := X) (M := M) (σ := σ) hσ hM hX

/-- Tail control with witness `K` yields `p^(1/sigma)` moment growth. -/
theorem hasGammaMomentGrowthWith_of_isBigO_gammaSigma
    {X : Ω → ℝ} {K σ : ℝ}
    [IsProbabilityMeasure μ]
    (hσ : 0 < σ) (hK : 0 < K)
    (hXm : AEMeasurable X μ) (hX : IsBigO μ (gammaSigma σ) X K) :
    HasGammaMomentGrowthWith μ σ X (gammaMomentConst σ * K) := by
  simpa [gammaMomentConst] using
    IndependentSums.hasGammaMomentGrowthWith_of_isBigO_gammaSigma
      (μ := μ) (X := X) (K := K) (σ := σ) hσ hK hXm hX

/-- Explicit moment estimate associated to a `Gamma_sigma` tail witness. -/
theorem integral_abs_rpow_le_of_isBigO_gammaSigma
    {X : Ω → ℝ} {K σ p : ℝ}
    [IsProbabilityMeasure μ]
    (hσ : 0 < σ) (hK : 0 < K) (hp : 1 ≤ p)
    (hXm : AEMeasurable X μ) (hX : IsBigO μ (gammaSigma σ) X K) :
    ∫ ω, |X ω| ^ p ∂μ ≤ (gammaMomentConst σ * p ^ σ⁻¹ * K) ^ p := by
  simpa [gammaMomentConst, mul_assoc, mul_left_comm, mul_comm] using
    IndependentSums.integral_abs_rpow_le_of_isBigO_gammaSigma
      (μ := μ) (X := X) (K := K) (σ := σ) (p := p) hσ hK hp hXm hX

/-- Rosenthal's inequality in the max-term form from the notes. -/
theorem integral_abs_finsetSum_pow_rpow_inv_le_rosenthal_of_iIndepFun_of_integral_eq_zero
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} (hs : s.Nonempty) {p : ℕ}
    (hp : 2 ≤ p)
    (h_indep : ProbabilityTheory.iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_int : ∀ i ∈ s, Integrable (X i) μ)
    (h_sq_int : ∀ i ∈ s, Integrable (fun ω => X i ω ^ (2 : ℕ)) μ)
    (hmax_int : Integrable (fun ω => (s.sup' hs (fun i => |X i ω|)) ^ p) μ)
    (hXmean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0) :
    (∫ ω, |∑ i ∈ s, X i ω| ^ p ∂μ) ^ (1 / (p : ℝ)) ≤
      2 * (p : ℝ) * (∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ) ^
          (1 / (p : ℝ)) +
        4 * rosenthalBennettIntegralConst *
          (Real.sqrt p * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ)) := by
  have hcenter_eq :
      IndependentSums.centeredFinsetSum X μ s = fun ω => ∑ i ∈ s, X i ω := by
    have hmean_sum : ∑ i ∈ s, ∫ ω, X i ω ∂μ = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i hi
      exact hXmean i hi
    funext ω
    rw [IndependentSums.centeredFinsetSum, Finset.sum_sub_distrib, hmean_sum, sub_zero]
  simpa [hcenter_eq, rosenthalBennettIntegralConst] using
    IndependentSums.integral_abs_centeredFinsetSum_pow_rpow_inv_le_rosenthal
      (μ := μ) (X := X) (s := s) hs hp h_indep h_meas h_int h_sq_int hmax_int

/-- Rosenthal's polynomial-moment corollary for finite sums of centered
independent real random variables. -/
theorem integral_abs_finsetSum_pow_rpow_inv_le_rosenthal_polynomial_of_iIndepFun_of_integral_eq_zero
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} (hs : s.Nonempty) {p : ℕ}
    (hp : 2 ≤ p)
    (h_indep : ProbabilityTheory.iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (hLp_int : ∀ i ∈ s, Integrable (fun ω => |X i ω| ^ p) μ)
    (hXmean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0) :
    (∫ ω, |∑ i ∈ s, X i ω| ^ p ∂μ) ^ (1 / (p : ℝ)) ≤
      2 * (p : ℝ) * (∑ i ∈ s, ∫ ω, |X i ω| ^ p ∂μ) ^ (1 / (p : ℝ)) +
        4 * rosenthalBennettIntegralConst *
          (Real.sqrt p * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ)) := by
  simpa [rosenthalBennettIntegralConst] using
    IndependentSums.integral_abs_finsetSum_pow_rpow_inv_le_rosenthal_polynomial_of_iIndepFun_of_integral_eq_zero
      (μ := μ) (X := X) (s := s) hs hp h_indep h_meas hLp_int hXmean

/-- Uniform-`K` polynomial-moment Rosenthal corollary. -/
theorem integral_abs_finsetSum_pow_rpow_inv_le_rosenthal_uniform_polynomial_of_iIndepFun_of_integral_eq_zero
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} (hs : s.Nonempty) {p : ℕ} {K : ℝ}
    (hp : 2 ≤ p)
    (hK_nonneg : 0 ≤ K)
    (h_indep : ProbabilityTheory.iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (hLp_int : ∀ i ∈ s, Integrable (fun ω => |X i ω| ^ p) μ)
    (hXmean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0)
    (hK : ∀ i ∈ s, (∫ ω, |X i ω| ^ p ∂μ) ^ (1 / (p : ℝ)) ≤ K) :
    (∫ ω, |∑ i ∈ s, X i ω| ^ p ∂μ) ^ (1 / (p : ℝ)) ≤
      2 * (p : ℝ) * ((s.card : ℝ) ^ (1 / (p : ℝ)) * K) +
        4 * rosenthalBennettIntegralConst *
          (Real.sqrt p * (Real.sqrt (s.card : ℝ) * K)) := by
  simpa [rosenthalBennettIntegralConst] using
    IndependentSums.integral_abs_finsetSum_pow_rpow_inv_le_rosenthal_uniform_polynomial_of_iIndepFun_of_integral_eq_zero
      (μ := μ) (X := X) (s := s) hs hp hK_nonneg h_indep h_meas hLp_int hXmean hK

/-- Uniform-`K` polynomial-moment Rosenthal corollary for a.e.-measurable
summands.  This is the completed-law version used by Chapter 4 local-test
observables: independence is kept on the original local observables, while the
proof applies the measurable-mk representatives internally. -/
theorem integral_abs_finsetSum_pow_rpow_inv_le_rosenthal_uniform_polynomial_of_iIndepFun_of_integral_eq_zero_aemeasurable
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} (hs : s.Nonempty) {p : ℕ} {K : ℝ}
    (hp : 2 ≤ p)
    (hK_nonneg : 0 ≤ K)
    (h_indep : ProbabilityTheory.iIndepFun X μ)
    (h_aemeas : ∀ i, AEMeasurable (X i) μ)
    (hLp_int : ∀ i ∈ s, Integrable (fun ω => |X i ω| ^ p) μ)
    (hXmean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0)
    (hK : ∀ i ∈ s, (∫ ω, |X i ω| ^ p ∂μ) ^ (1 / (p : ℝ)) ≤ K) :
    (∫ ω, |∑ i ∈ s, X i ω| ^ p ∂μ) ^ (1 / (p : ℝ)) ≤
      2 * (p : ℝ) * ((s.card : ℝ) ^ (1 / (p : ℝ)) * K) +
        4 * rosenthalBennettIntegralConst *
          (Real.sqrt p * (Real.sqrt (s.card : ℝ) * K)) := by
  classical
  let Y : ι → Ω → ℝ := fun i => (h_aemeas i).mk (X i)
  have hXY : ∀ i, X i =ᵐ[μ] Y i := fun i => (h_aemeas i).ae_eq_mk
  have hY_indep : ProbabilityTheory.iIndepFun Y μ := h_indep.congr hXY
  have hY_meas : ∀ i, Measurable (Y i) := fun i => (h_aemeas i).measurable_mk
  have hY_Lp_int :
      ∀ i ∈ s, Integrable (fun ω => |Y i ω| ^ p) μ := by
    intro i hi
    refine (hLp_int i hi).congr ?_
    filter_upwards [hXY i] with ω hω
    simp [Y, ← hω]
  have hY_mean : ∀ i ∈ s, ∫ ω, Y i ω ∂μ = 0 := by
    intro i hi
    calc
      ∫ ω, Y i ω ∂μ = ∫ ω, X i ω ∂μ := by
        exact integral_congr_ae (hXY i).symm
      _ = 0 := hXmean i hi
  have hY_K :
      ∀ i ∈ s, (∫ ω, |Y i ω| ^ p ∂μ) ^ (1 / (p : ℝ)) ≤ K := by
    intro i hi
    have hint :
        ∫ ω, |Y i ω| ^ p ∂μ = ∫ ω, |X i ω| ^ p ∂μ := by
      exact integral_congr_ae (by
        filter_upwards [(hXY i).symm] with ω hω
        simp [Y, hω])
    simpa [hint] using hK i hi
  have hY_bound :=
    integral_abs_finsetSum_pow_rpow_inv_le_rosenthal_uniform_polynomial_of_iIndepFun_of_integral_eq_zero
      (μ := μ) (X := Y) (s := s) hs hp hK_nonneg hY_indep hY_meas
      hY_Lp_int hY_mean hY_K
  have hsum_eq :
      (fun ω => |∑ i ∈ s, X i ω| ^ p) =ᵐ[μ]
        fun ω => |∑ i ∈ s, Y i ω| ^ p := by
    have hAll : ∀ᵐ ω ∂μ, ∀ i ∈ s, X i ω = Y i ω := by
      rw [Filter.eventually_all_finset]
      intro i _hi
      exact hXY i
    filter_upwards [hAll] with ω hω
    congr 2
    exact Finset.sum_congr rfl fun i hi => by simp [hω i hi]
  have hint :
      ∫ ω, |∑ i ∈ s, X i ω| ^ p ∂μ =
        ∫ ω, |∑ i ∈ s, Y i ω| ^ p ∂μ :=
    integral_congr_ae hsum_eq
  simpa [hint] using hY_bound

/-! ## Independent-sum concentration endpoints -/

/-- Direct concentration in the exponential regime `1 ≤ sigma ≤ 2`. -/
theorem isBigO_gammaSigma_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero_expRegime
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} {σ K : ℝ}
    (h_indep : ProbabilityTheory.iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (hs : s.Nonempty)
    (hσ₁ : 1 ≤ σ) (hσ₂ : σ ≤ 2)
    (hK : 0 < K)
    (hX : ∀ i ∈ s, IsBigO μ (gammaSigma σ) (X i) K)
    (hXmean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0) :
    IsBigO μ (gammaSigma σ) (fun ω => ∑ i ∈ s, X i ω)
      (gammaSigmaExpRegimeEndpointConst σ * Real.sqrt (s.card : ℝ) * K) := by
  simpa [gammaSigmaExpRegimeEndpointConst] using
    IndependentSums.isBigO_gammaSigma_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero_expRegime
      (μ := μ) (X := X) (s := s) (σ := σ) (K := K)
      h_indep h_meas hs hσ₁ hσ₂ hK hX hXmean

/-- Averaged direct concentration in the exponential regime `1 ≤ sigma ≤ 2`. -/
theorem isBigO_gammaSigma_finsetAverage_of_iIndepFun_of_isBigO_of_integral_eq_zero_expRegime
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} {σ K : ℝ}
    (h_indep : ProbabilityTheory.iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (hs : s.Nonempty)
    (hσ₁ : 1 ≤ σ) (hσ₂ : σ ≤ 2)
    (hK : 0 < K)
    (hX : ∀ i ∈ s, IsBigO μ (gammaSigma σ) (X i) K)
    (hXmean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0) :
    IsBigO μ (gammaSigma σ)
      (fun ω => ((s.card : ℝ)⁻¹) * ∑ i ∈ s, X i ω)
      (gammaSigmaExpRegimeEndpointConst σ * (Real.sqrt (s.card : ℝ) / (s.card : ℝ)) * K) := by
  simpa [gammaSigmaExpRegimeEndpointConst] using
    IndependentSums.isBigO_gammaSigma_finsetAverage_of_iIndepFun_of_isBigO_of_integral_eq_zero_expRegime
      (μ := μ) (X := X) (s := s) (σ := σ) (K := K)
      h_indep h_meas hs hσ₁ hσ₂ hK hX hXmean

/-- Full centered independent-sum concentration for `Gamma_sigma`,
`0 < sigma ≤ 2`. -/
theorem isBigO_gammaSigma_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} {σ K : ℝ}
    (h_indep : ProbabilityTheory.iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (hs : s.Nonempty)
    (hσ₀ : 0 < σ) (hσ₂ : σ ≤ 2)
    (hK : 0 < K)
    (hX : ∀ i ∈ s, IsBigO μ (gammaSigma σ) (X i) K)
    (h_mean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0) :
    IsBigO μ (gammaSigma σ) (fun ω => ∑ i ∈ s, X i ω)
      (gammaSigmaIndependentSumConst σ * Real.sqrt (s.card : ℝ) * K) := by
  by_cases hσ_lt : σ < 1
  · simpa [gammaSigmaIndependentSumConst, hσ_lt, gammaSigmaHeavyTailEndpointConst] using
      IndependentSums.isBigO_gammaSigma_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero_of_lt_one
        (μ := μ) (X := X) (s := s) (σ := σ) (K := K)
        h_indep h_meas hs hσ₀ hσ_lt hK hX h_mean
  · have hσ₁ : 1 ≤ σ := le_of_not_gt hσ_lt
    simpa [gammaSigmaIndependentSumConst, hσ_lt, gammaSigmaExpRegimeEndpointConst] using
      isBigO_gammaSigma_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero_expRegime
        (μ := μ) (X := X) (s := s) (σ := σ) (K := K)
        h_indep h_meas hs hσ₁ hσ₂ hK hX h_mean

/-- Averaged full centered independent-sum concentration for `Gamma_sigma`,
`0 < sigma ≤ 2`. -/
theorem isBigO_gammaSigma_finsetAverage_of_iIndepFun_of_isBigO_of_integral_eq_zero
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} {σ K : ℝ}
    (h_indep : ProbabilityTheory.iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (hs : s.Nonempty)
    (hσ₀ : 0 < σ) (hσ₂ : σ ≤ 2)
    (hK : 0 < K)
    (hX : ∀ i ∈ s, IsBigO μ (gammaSigma σ) (X i) K)
    (h_mean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0) :
    IsBigO μ (gammaSigma σ)
      (fun ω => ((s.card : ℝ)⁻¹) * ∑ i ∈ s, X i ω)
      (gammaSigmaIndependentSumConst σ * (Real.sqrt (s.card : ℝ) / (s.card : ℝ)) * K) := by
  by_cases hσ_lt : σ < 1
  · simpa [gammaSigmaIndependentSumConst, hσ_lt, gammaSigmaHeavyTailEndpointConst] using
      IndependentSums.isBigO_gammaSigma_finsetAverage_of_iIndepFun_of_isBigO_of_integral_eq_zero_of_lt_one
        (μ := μ) (X := X) (s := s) (σ := σ) (K := K)
        h_indep h_meas hs hσ₀ hσ_lt hK hX h_mean
  · have hσ₁ : 1 ≤ σ := le_of_not_gt hσ_lt
    simpa [gammaSigmaIndependentSumConst, hσ_lt, gammaSigmaExpRegimeEndpointConst] using
      isBigO_gammaSigma_finsetAverage_of_iIndepFun_of_isBigO_of_integral_eq_zero_expRegime
        (μ := μ) (X := X) (s := s) (σ := σ) (K := K)
        h_indep h_meas hs hσ₁ hσ₂ hK hX h_mean

/-- Generic heavy-tail concentration estimate for centered finite independent
families under a weak-tail logarithmic constraint. -/
theorem measureReal_upperTailEvent_finset_sum_le_exp_card_mul_add_card_mul_invPsi_of_iIndepFun_of_isBigO_of_integral_eq_zero_of_log_constraint_rounded
    [IsProbabilityMeasure μ]
    {Ψ : ℝ → ℝ} {X : ι → Ω → ℝ} {s : Finset ι} {a l L CΨ M : ℝ}
    (h_indep : ProbabilityTheory.iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_int : ∀ i ∈ s, Integrable (X i) μ)
    (h_mean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0)
    (hAdmissible : AdmissiblePsi Ψ)
    (hCΨ_nonneg : 0 ≤ CΨ)
    (hCΨ :
      ∫⁻ t in Set.Ioi 1, ENNReal.ofReal (t / Ψ t) ∂volume ≤ ENNReal.ofReal CΨ)
    (hX : ∀ i ∈ s, IsBigO μ Ψ (X i) 1)
    (hl : 0 ≤ l) (hl1 : l ≤ 1) (hL : 1 ≤ L) (hM : 1 ≤ M)
    (hconstraint : ∀ i ∈ s, ∀ ⦃t : ℝ⦄, t ∈ Set.Icc 1 L →
      l * t ≤ Real.log (Ψ t) - 4 * Real.log t + Real.log M) :
    μ.real (upperTailEvent (fun ω => ∑ i ∈ s, X i ω) a) ≤
      Real.exp (-l * a + (s.card : ℝ) * (l ^ (2 : ℕ) * (3 + M + CΨ))) +
        (s.card : ℝ) * (Ψ L)⁻¹ := by
  simpa using
    IndependentSums.measureReal_upperTailEvent_finset_sum_le_exp_card_mul_add_card_mul_invPsi_of_iIndepFun_of_isBigO_of_integral_eq_zero_of_log_constraint_rounded
      (μ := μ) (Ψ := Ψ) (X := X) (s := s) (a := a) (l := l) (L := L)
      (CΨ := CΨ) (M := M)
      h_indep h_meas h_int h_mean hAdmissible hCΨ_nonneg hCΨ hX hl hl1 hL hM
      hconstraint

/-- Log-normal centered independent-sum concentration. -/
theorem isBigO_psiSigma_finset_sum_of_iIndepFun_of_isBigO_scale_of_integral_eq_zero
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} {σ K : ℝ}
    (h_indep : ProbabilityTheory.iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_int : ∀ i ∈ s, Integrable (X i) μ)
    (h_mean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0)
    (hs : s.Nonempty)
    (hσ : 1 ≤ σ) (hK : 0 < K)
    (hX : ∀ i ∈ s, IsBigO μ (psiSigma σ) (X i) K) :
    IsBigO μ (psiSigma σ) (fun ω => ∑ i ∈ s, X i ω)
      (psiSigmaIndependentSumConst σ * Real.sqrt (s.card : ℝ) * K) := by
  simpa [psiSigmaIndependentSumConst] using
    IndependentSums.isBigO_psiSigma_finset_sum_of_iIndepFun_of_isBigO_scale_of_integral_eq_zero
      (μ := μ) (X := X) (s := s) (σ := σ) (K := K)
      h_indep h_meas h_int h_mean hs hσ hK hX

/-- Averaged log-normal centered independent-sum concentration. -/
theorem isBigO_psiSigma_finsetAverage_of_iIndepFun_of_isBigO_scale_of_integral_eq_zero
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} {σ K : ℝ}
    (h_indep : ProbabilityTheory.iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_int : ∀ i ∈ s, Integrable (X i) μ)
    (h_mean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0)
    (hs : s.Nonempty)
    (hσ : 1 ≤ σ) (hK : 0 < K)
    (hX : ∀ i ∈ s, IsBigO μ (psiSigma σ) (X i) K) :
    IsBigO μ (psiSigma σ)
      (fun ω => ((s.card : ℝ)⁻¹) * ∑ i ∈ s, X i ω)
      (psiSigmaIndependentSumConst σ *
        (Real.sqrt (s.card : ℝ) / (s.card : ℝ)) * K) := by
  simpa [psiSigmaIndependentSumConst] using
    IndependentSums.isBigO_psiSigma_finsetAverage_of_iIndepFun_of_isBigO_scale_of_integral_eq_zero
      (μ := μ) (X := X) (s := s) (σ := σ) (K := K)
      h_indep h_meas h_int h_mean hs hσ hK hX

/-! ## Log-normal bridge -/

/-- Subgaussian upper tails imply log-normal upper tails for `exp X - 1`. -/
theorem isBigOWith_psiSigma_exp_sub_one_of_isBigOWith_gammaTwo
    {X : Ω → ℝ} {σ : ℝ}
    (hσ : 1 ≤ σ)
    (hX : IsBigOWith μ (gammaSigma 2) X σ) :
    IsBigOWith μ (psiSigma σ) (fun ω => Real.exp (X ω) - 1) (Real.exp σ - 1) := by
  simpa using
    IndependentSums.isBigOWith_psiSigma_exp_sub_one_of_isBigOWith_gammaTwo
      (μ := μ) (X := X) (σ := σ) hσ hX

/-- Log-normal upper tails for `exp X - 1` imply the matching subgaussian
upper-tail relation for `X`. -/
theorem isBigOWith_gammaTwo_of_isBigOWith_psiSigma_exp_sub_one
    {X : Ω → ℝ} {σ : ℝ}
    (hσ : 1 ≤ σ)
    (hX : IsBigOWith μ (psiSigma σ) (fun ω => Real.exp (X ω) - 1) σ) :
    IsBigOWith μ (gammaSigma 2) X σ := by
  simpa using
    IndependentSums.isBigOWith_gammaTwo_of_isBigOWith_psiSigma_exp_sub_one
      (μ := μ) (X := X) (σ := σ) hσ hX

end

end Ch04
end Book
end Homogenization
