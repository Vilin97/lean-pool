/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.TimeDependentTestConvergence
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.WeakGradientAssembly
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.LimitRepresentation

/-!
# Product-space identities for time-dependent Fourier cutoffs

The modewise weak identities are first regrouped as product-space integrals. This keeps the
bounded drift and the vector gradient in their natural Hilbert spaces before the physical-cell
representatives are substituted.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Homogenization
open scoped ENNReal RealInnerProductSpace Topology

namespace AVenhance.Infra.Parabolic.FourierGalerkin

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance cutoffProductMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance cutoffProductMeasureIsAddHaar : Measure.IsAddHaarMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance cutoffProductProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance cutoffProductProbabilityTorus : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance

/-- Product time-torus measure used for the time-dependent cutoff pairing. -/
abbrev TimeDependentCutoffProduct.cutoffProductMeasure :=
  GalerkinTimeMeasure.prod (volume : Measure Torus)

/-- Single unit coefficient selecting a real Fourier mode. -/
def TimeDependentCutoffProduct.cutoffProductUnitCoefficient (N : ℕ)
    (j : Fin (RealFourierDimension N)) : Coefficients (RealFourierDimension N) :=
  WithLp.toLp 2 (Pi.single j (1 : ℝ))

theorem TimeDependentCutoffProduct.cutoffProductModeExpansion_unit (N : ℕ)
    (j : Fin (RealFourierDimension N)) (x : Torus) :
    modeExpansion (RealFourierDimension N) (realFourierModeFin N)
      (TimeDependentCutoffProduct.cutoffProductUnitCoefficient N j) x = realFourierModeFin N j x
          := by
  simp [modeExpansion, TimeDependentCutoffProduct.cutoffProductUnitCoefficient]

theorem TimeDependentCutoffProduct.scalarProductTestLp_inner_integral_mode
    (U : ScalarProductTimeL2) (N : ℕ) (j : Fin (RealFourierDimension N))
    (η : ℝ → ℝ) (hη : MemLp η ⊤ GalerkinTimeMeasure) :
    Integrable (fun p : ℝ × Torus => U p *
      (η p.1 * realFourierModeL2 N j p.2)) TimeDependentCutoffProduct.cutoffProductMeasure ∧
    inner ℝ U (scalarProductTestLp η (realFourierModeL2 N j) hη) =
      ∫ p : ℝ × Torus, U p * (η p.1 * realFourierModeL2 N j p.2)
        ∂TimeDependentCutoffProduct.cutoffProductMeasure := by
  let V := scalarProductTestLp η (realFourierModeL2 N j) hη
  have htest : (fun p : ℝ × Torus => V p) =ᵐ[TimeDependentCutoffProduct.cutoffProductMeasure]
      fun p => η p.1 * realFourierModeL2 N j p.2 := by
    filter_upwards [scalarProductTest_memLp hη (realFourierModeL2 N j) |>.coeFn_toLp]
      with p hV
    simpa [V, scalarProductTestLp] using hV
  have hIntInner := MeasureTheory.L2.integrable_inner (𝕜 := ℝ) U V
  have hInt : Integrable (fun p : ℝ × Torus => U p *
      (η p.1 * realFourierModeL2 N j p.2)) TimeDependentCutoffProduct.cutoffProductMeasure := by
    apply hIntInner.congr
    filter_upwards [htest] with p hp
    rw [hp]
    simp [mul_comm]
  refine ⟨hInt, ?_⟩
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [htest] with p hp
  rw [hp]
  simp [mul_comm]

theorem TimeDependentCutoffProduct.gradientProductTestLp_inner_integral_mode
    (G : GradientProductTimeL2) (N : ℕ) (j : Fin (RealFourierDimension N))
    (η : ℝ → ℝ) (hη : MemLp η ⊤ GalerkinTimeMeasure) :
    Integrable (fun p : ℝ × Torus =>
      inner ℝ (G p) (η p.1 • realFourierModeGradL2 N j p.2))
          TimeDependentCutoffProduct.cutoffProductMeasure ∧
    inner ℝ G (gradientProductTestLp η (realFourierModeGradL2 N j) hη) =
      ∫ p : ℝ × Torus,
        inner ℝ (G p) (η p.1 • realFourierModeGradL2 N j p.2)
        ∂TimeDependentCutoffProduct.cutoffProductMeasure := by
  let V := gradientProductTestLp η (realFourierModeGradL2 N j) hη
  have htest : (fun p : ℝ × Torus => V p) =ᵐ[TimeDependentCutoffProduct.cutoffProductMeasure]
      fun p => η p.1 • realFourierModeGradL2 N j p.2 := by
    filter_upwards [gradientProductTest_memLp hη (realFourierModeGradL2 N j) |>.coeFn_toLp]
      with p hV
    simpa [V, gradientProductTestLp] using hV
  have hIntInner := MeasureTheory.L2.integrable_inner (𝕜 := ℝ) G V
  have hInt : Integrable (fun p : ℝ × Torus =>
      inner ℝ (G p) (η p.1 • realFourierModeGradL2 N j p.2))
          TimeDependentCutoffProduct.cutoffProductMeasure := by
    apply hIntInner.congr
    filter_upwards [htest] with p hp
    rw [hp]
  refine ⟨hInt, ?_⟩
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [htest] with p hp
  rw [hp]

theorem TimeDependentCutoffProduct.weightedDriftProductTestLp_inner_integral_mode
    (P : FrozenDriftProblem) (G : GradientProductTimeL2) (N : ℕ)
    (j : Fin (RealFourierDimension N)) (η : ℝ → ℝ)
    (hη : MemLp η ⊤ GalerkinTimeMeasure) :
    Integrable (fun p : ℝ × Torus => inner ℝ (G p)
      (P.weightedDriftProductTestFunction η N
          (TimeDependentCutoffProduct.cutoffProductUnitCoefficient N j) p))
      TimeDependentCutoffProduct.cutoffProductMeasure ∧
    inner ℝ G (P.weightedDriftProductTestLp η N
      (TimeDependentCutoffProduct.cutoffProductUnitCoefficient N j) hη) =
      ∫ p : ℝ × Torus,
        inner ℝ (G p) (P.weightedDriftProductTestFunction η N
          (TimeDependentCutoffProduct.cutoffProductUnitCoefficient N j) p)
              ∂TimeDependentCutoffProduct.cutoffProductMeasure := by
  let V := P.weightedDriftProductTestLp η N
      (TimeDependentCutoffProduct.cutoffProductUnitCoefficient N j) hη
  have htest : (fun p : ℝ × Torus => V p) =ᵐ[TimeDependentCutoffProduct.cutoffProductMeasure]
      P.weightedDriftProductTestFunction η N
          (TimeDependentCutoffProduct.cutoffProductUnitCoefficient N j) := by
    simpa [V, FrozenDriftProblem.weightedDriftProductTestLp] using
      (P.weightedDriftProductTest_memLp hη N
        (TimeDependentCutoffProduct.cutoffProductUnitCoefficient N j)).coeFn_toLp
  have hIntInner := MeasureTheory.L2.integrable_inner (𝕜 := ℝ) G V
  have hInt : Integrable (fun p : ℝ × Torus => inner ℝ (G p)
      (P.weightedDriftProductTestFunction η N
          (TimeDependentCutoffProduct.cutoffProductUnitCoefficient N j) p))
      TimeDependentCutoffProduct.cutoffProductMeasure := by
    apply hIntInner.congr
    filter_upwards [htest] with p hp
    rw [hp]
  refine ⟨hInt, ?_⟩
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [htest] with p hp
  rw [hp]

/-- The three finite sums in the time-dependent mode identity are the product-space pairings
against the value, drift-weighted value, and gradient of one finite Fourier cutoff. -/
theorem FrozenDriftProblem.synchronized_limit_spacetimeFourierCutoff_product_identity
    (P : FrozenDriftProblem) (Uprod : ScalarProductTimeL2) (Gprod : GradientProductTimeL2)
    {φ : ℝ → Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2))
    (N : ℕ)
    (hidentity :
      -(∑ j : Fin (RealFourierDimension N),
        inner ℝ Uprod (scalarProductTestLp
          (deriv (spacetimeRealFourierCoefficient φ N j))
          (realFourierModeL2 N j)
          (continuous_time_memLp_top
            ((spacetimeRealFourierCoefficient_contDiff_one hφ N j).continuous_deriv_one)))) +
       (∑ j : Fin (RealFourierDimension N),
        inner ℝ Gprod (P.weightedDriftProductTestLp
          (spacetimeRealFourierCoefficient φ N j) N
          (realFourierUnitCoefficient N j)
          (continuous_time_memLp_top
            (spacetimeRealFourierCoefficient_contDiff_one hφ N j).continuous))) +
       P.κ * (∑ j : Fin (RealFourierDimension N),
        inner ℝ Gprod (gradientProductTestLp
          (spacetimeRealFourierCoefficient φ N j)
          (realFourierModeGradL2 N j)
          (continuous_time_memLp_top
            (spacetimeRealFourierCoefficient_contDiff_one hφ N j).continuous))) =
       ∑ j : Fin (RealFourierDimension N),
        spacetimeRealFourierCoefficient φ N j 0 *
          inner ℝ P.initialTorusL2 (realFourierModeL2 N j)) :
    -(∫ p : ℝ × Torus,
        Uprod p * ∑ j : Fin (RealFourierDimension N),
          deriv (spacetimeRealFourierCoefficient φ N j) p.1 * realFourierModeL2 N j p.2
        ∂TimeDependentCutoffProduct.cutoffProductMeasure) +
      (∫ p : ℝ × Torus,
        ∑ j : Fin (RealFourierDimension N),
          inner ℝ (Gprod p)
            ((spacetimeRealFourierCoefficient φ N j p.1 *
              modeExpansion (RealFourierDimension N) (realFourierModeFin N)
                (realFourierUnitCoefficient N j) p.2) •
              WithLp.toLp 2
                (AVenhance.Infra.Torus.periodicToTorus (P.b p.1) p.2))
        ∂TimeDependentCutoffProduct.cutoffProductMeasure) +
      P.κ * (∫ p : ℝ × Torus,
        ∑ j : Fin (RealFourierDimension N),
          inner ℝ (Gprod p)
            (spacetimeRealFourierCoefficient φ N j p.1 •
              realFourierModeGradL2 N j p.2)
        ∂TimeDependentCutoffProduct.cutoffProductMeasure) =
      ∑ j : Fin (RealFourierDimension N),
        spacetimeRealFourierCoefficient φ N j 0 *
          inner ℝ P.initialTorusL2 (realFourierModeL2 N j) := by
  classical
  let hη (j : Fin (RealFourierDimension N)) :=
    continuous_time_memLp_top
      (spacetimeRealFourierCoefficient_contDiff_one hφ N j).continuous
  let hηd (j : Fin (RealFourierDimension N)) :=
    continuous_time_memLp_top
      ((spacetimeRealFourierCoefficient_contDiff_one hφ N j).continuous_deriv_one)
  have hA (j : Fin (RealFourierDimension N)) :=
    TimeDependentCutoffProduct.scalarProductTestLp_inner_integral_mode Uprod N j
      (deriv (spacetimeRealFourierCoefficient φ N j)) (hηd j)
  have hB (j : Fin (RealFourierDimension N)) :=
    TimeDependentCutoffProduct.weightedDriftProductTestLp_inner_integral_mode P Gprod N j
      (spacetimeRealFourierCoefficient φ N j) (hη j)
  have hC (j : Fin (RealFourierDimension N)) :=
    TimeDependentCutoffProduct.gradientProductTestLp_inner_integral_mode Gprod N j
      (spacetimeRealFourierCoefficient φ N j) (hη j)
  have hA' : (∑ j : Fin (RealFourierDimension N),
      inner ℝ Uprod (scalarProductTestLp
        (deriv (spacetimeRealFourierCoefficient φ N j))
        (realFourierModeL2 N j) (hηd j))) =
      ∫ p : ℝ × Torus, Uprod p * ∑ j : Fin (RealFourierDimension N),
        deriv (spacetimeRealFourierCoefficient φ N j) p.1 * realFourierModeL2 N j p.2
        ∂TimeDependentCutoffProduct.cutoffProductMeasure := by
    calc
      _ = ∑ j : Fin (RealFourierDimension N),
          ∫ p : ℝ × Torus, Uprod p *
            (deriv (spacetimeRealFourierCoefficient φ N j) p.1 *
              realFourierModeL2 N j p.2) ∂TimeDependentCutoffProduct.cutoffProductMeasure := by
            apply Finset.sum_congr rfl
            intro j hj
            exact (hA j).2
      _ = ∫ p : ℝ × Torus, ∑ j : Fin (RealFourierDimension N),
            Uprod p * (deriv (spacetimeRealFourierCoefficient φ N j) p.1 *
              realFourierModeL2 N j p.2) ∂TimeDependentCutoffProduct.cutoffProductMeasure :=
            (integral_finsetSum _ (fun j hj => (hA j).1)).symm
      _ = _ := by
            apply integral_congr_ae
            filter_upwards with p
            simp [Finset.mul_sum]
  have hB' : (∑ j : Fin (RealFourierDimension N),
      inner ℝ Gprod (P.weightedDriftProductTestLp
        (spacetimeRealFourierCoefficient φ N j) N (realFourierUnitCoefficient N j)
        (hη j))) =
      ∫ p : ℝ × Torus, ∑ j : Fin (RealFourierDimension N),
        inner ℝ (Gprod p)
          ((spacetimeRealFourierCoefficient φ N j p.1 *
            modeExpansion (RealFourierDimension N) (realFourierModeFin N)
              (realFourierUnitCoefficient N j) p.2) •
            WithLp.toLp 2 (AVenhance.Infra.Torus.periodicToTorus (P.b p.1) p.2))
        ∂TimeDependentCutoffProduct.cutoffProductMeasure := by
    calc
      _ = ∑ j : Fin (RealFourierDimension N),
          ∫ p : ℝ × Torus, inner ℝ (Gprod p)
            (P.weightedDriftProductTestFunction (spacetimeRealFourierCoefficient φ N j)
              N (realFourierUnitCoefficient N j) p)
                  ∂TimeDependentCutoffProduct.cutoffProductMeasure := by
            apply Finset.sum_congr rfl
            intro j hj
            exact (hB j).2
      _ = _ := (integral_finsetSum _ (fun j hj => (hB j).1)).symm
  have hC' : (∑ j : Fin (RealFourierDimension N),
      inner ℝ Gprod (gradientProductTestLp
        (spacetimeRealFourierCoefficient φ N j) (realFourierModeGradL2 N j) (hη j))) =
      ∫ p : ℝ × Torus, ∑ j : Fin (RealFourierDimension N),
        inner ℝ (Gprod p)
          (spacetimeRealFourierCoefficient φ N j p.1 •
            realFourierModeGradL2 N j p.2)
        ∂TimeDependentCutoffProduct.cutoffProductMeasure := by
    calc
      _ = ∑ j : Fin (RealFourierDimension N),
          ∫ p : ℝ × Torus,
            inner ℝ (Gprod p)
              (spacetimeRealFourierCoefficient φ N j p.1 •
                realFourierModeGradL2 N j p.2) ∂TimeDependentCutoffProduct.cutoffProductMeasure :=
                    by
            apply Finset.sum_congr rfl
            intro j hj
            exact (hC j).2
      _ = _ := (integral_finsetSum _ (fun j hj => (hC j).1)).symm
  rw [hA', hB', hC'] at hidentity
  simpa [hη, hηd, weightedDriftProductTestFunction, modeExpansion_unit,
    TimeDependentCutoffProduct.cutoffProductUnitCoefficient, realFourierUnitCoefficient] using
        hidentity

/-- The three finite Fourier cutoff integrands are integrable on time times the torus. -/
theorem FrozenDriftProblem.spacetimeFourierCutoff_product_integrable
    (P : FrozenDriftProblem) (Uprod : ScalarProductTimeL2) (Gprod : GradientProductTimeL2)
    {φ : ℝ → Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2)) (N : ℕ) :
    Integrable (fun p : ℝ × Torus => Uprod p *
      ∑ j : Fin (RealFourierDimension N),
        deriv (spacetimeRealFourierCoefficient φ N j) p.1 * realFourierModeL2 N j p.2)
      TimeDependentCutoffProduct.cutoffProductMeasure ∧
    Integrable (fun p : ℝ × Torus =>
      ∑ j : Fin (RealFourierDimension N),
        inner ℝ (Gprod p)
          ((spacetimeRealFourierCoefficient φ N j p.1 * realFourierModeFin N j p.2) •
            WithLp.toLp 2 (AVenhance.Infra.Torus.periodicToTorus (P.b p.1) p.2)))
      TimeDependentCutoffProduct.cutoffProductMeasure ∧
    Integrable (fun p : ℝ × Torus =>
      ∑ j : Fin (RealFourierDimension N),
        inner ℝ (Gprod p)
          (spacetimeRealFourierCoefficient φ N j p.1 • realFourierModeGradL2 N j p.2))
      TimeDependentCutoffProduct.cutoffProductMeasure := by
  classical
  let hη (j : Fin (RealFourierDimension N)) :=
    continuous_time_memLp_top
      (spacetimeRealFourierCoefficient_contDiff_one hφ N j).continuous
  let hηd (j : Fin (RealFourierDimension N)) :=
    continuous_time_memLp_top
      ((spacetimeRealFourierCoefficient_contDiff_one hφ N j).continuous_deriv_one)
  have hA (j : Fin (RealFourierDimension N)) :=
    TimeDependentCutoffProduct.scalarProductTestLp_inner_integral_mode Uprod N j
      (deriv (spacetimeRealFourierCoefficient φ N j)) (hηd j)
  have hB (j : Fin (RealFourierDimension N)) :=
    TimeDependentCutoffProduct.weightedDriftProductTestLp_inner_integral_mode P Gprod N j
      (spacetimeRealFourierCoefficient φ N j) (hη j)
  have hC (j : Fin (RealFourierDimension N)) :=
    TimeDependentCutoffProduct.gradientProductTestLp_inner_integral_mode Gprod N j
      (spacetimeRealFourierCoefficient φ N j) (hη j)
  refine ⟨?_, ?_, ?_⟩
  · have hsum := integrable_finsetSum Finset.univ (fun j hj => (hA j).1)
    have : Integrable (fun p : ℝ × Torus =>
        ∑ j : Fin (RealFourierDimension N),
          Uprod p * (deriv (spacetimeRealFourierCoefficient φ N j) p.1 *
            realFourierModeL2 N j p.2)) TimeDependentCutoffProduct.cutoffProductMeasure := by
      simpa using hsum
    exact this.congr (Filter.Eventually.of_forall fun p => by simp [Finset.mul_sum])
  · have hsum := integrable_finsetSum Finset.univ (fun j hj => (hB j).1)
    simpa [modeExpansion, TimeDependentCutoffProduct.cutoffProductUnitCoefficient,
      weightedDriftProductTestFunction] using hsum
  · exact integrable_finsetSum Finset.univ (fun j hj => (hC j).1)

end AVenhance.Infra.Parabolic.FourierGalerkin

end
