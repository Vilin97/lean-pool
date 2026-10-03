/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinSmoothTimeDerivative

/-! Finite Laplacian coefficients in terms of the Galerkin second derivative paths. -/

@[expose] public section

noncomputable section

open MeasureTheory
open Homogenization
open AVenhance.Infra.Parabolic.FourierGalerkin
open AVenhance.Infra.Torus

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance laplacianFourierMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance laplacianFourierMeasureHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance laplacianFourierProbability : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance laplacianFourierTorusProbability : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance

namespace AVenhance.Infra.Classical

theorem classicalFrequencyPair_mem_symmetricFrequencyBox_eventually
    (k : Fin 2 → ℤ) :
    ∃ K : ℕ, ∀ N, K ≤ N → frequencyPair k ∈ symmetricFrequencyBox N := by
  let K := max (k 0).natAbs (k 1).natAbs
  refine ⟨K, ?_⟩
  intro N hKN
  have h0 : (k 0).natAbs ≤ N := (Nat.le_trans (Nat.le_max_left _ _) hKN)
  have h1 : (k 1).natAbs ≤ N := (Nat.le_trans (Nat.le_max_right _ _) hKN)
  have h0' : |k 0| ≤ (N : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast h0
  have h1' : |k 1| ≤ (N : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast h1
  simp only [symmetricFrequencyBox, Finset.mem_product, Finset.mem_Icc, frequencyPair]
  exact ⟨abs_le.mp h0', abs_le.mp h1'⟩

/-- The Fourier coefficient of the Laplacian of a finite Fourier synthesis is the sum of the
Fourier coefficients of its two second derivative paths. -/
theorem classicalGalerkinFiniteLaplacian_fourierCoeff_eq_sum
    (N : ℕ) (c : Coefficients (RealFourierDimension N)) (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff
        (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
          (AVenhance.spaceLap (realFourierModeAmbientExpansion N c)) x : ℝ) : ℂ)) k =
      ∑ i : Fin 2, classicalComplexFourierCoeffCLM k
        (realFourierScalarMap N (realFourierWordDerivativeMap N [i, i] c)) := by
  let u := realFourierModeAmbientExpansion N c
  let q : Fin 2 → Vec 2 → ℝ := fun i => classicalWordDerivative [i, i] u
  have hu : ContDiff ℝ (⊤ : ℕ∞) u :=
    (realFourierModeAmbientExpansion_contDiff N c).of_le (by simp)
  have hup : AVenhance.IsZ2Periodic u := realFourierModeAmbientExpansion_periodic N c
  have hqcont (i : Fin 2) : Continuous (q i) :=
    (classicalWordDerivative_contDiff [i, i] u hu).continuous
  have hqper (i : Fin 2) : AVenhance.IsZ2Periodic (q i) :=
    AVenhance.Infra.Classical.periodic_spaceGrad_component
      (AVenhance.Infra.Classical.periodic_spaceGrad_component hup i) i
  have hlap : AVenhance.spaceLap u = fun x => ∑ i : Fin 2, q i x := by
    funext x
    simp [q, u, AVenhance.spaceLap, classicalWordDerivative, Fin.sum_univ_two]
  have hcomponentIntegrable (i : Fin 2) : Integrable
      (fun x : Torus => UnitAddTorus.mFourier (-k) x •
        ((AVenhance.Infra.Torus.periodicToTorus (q i) x : ℝ) : ℂ))
      (volume : Measure Torus) := by
    have hqInt : Integrable (AVenhance.Infra.Torus.periodicToTorus (q i))
        (volume : Measure Torus) :=
      (memLp_periodicToTorus_real (hqcont i) (hqper i)).integrable (by norm_num)
    have hqComplex : Integrable (fun x : Torus =>
        Complex.ofReal (AVenhance.Infra.Torus.periodicToTorus (q i) x))
        (volume : Measure Torus) := Complex.ofRealCLM.integrable_comp hqInt
    have hchar : AEStronglyMeasurable
        (fun x : Torus => UnitAddTorus.mFourier (-k) x) (volume : Measure Torus) :=
      (UnitAddTorus.mFourier (-k)).continuous.aestronglyMeasurable
    have hcharBound : ∀ x : Torus, ‖UnitAddTorus.mFourier (-k) x‖ ≤ 1 := by
      intro x
      exact (ContinuousMap.norm_coe_le_norm _ x).trans_eq UnitAddTorus.mFourier_norm
    exact (hqComplex.bdd_smul 1 hchar (Filter.Eventually.of_forall hcharBound)).congr
      (Filter.Eventually.of_forall fun x => by rfl)
  have hsumCoeff : UnitAddTorus.mFourierCoeff
      (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
        (AVenhance.spaceLap u) x : ℝ) : ℂ)) k =
      ∑ i : Fin 2, UnitAddTorus.mFourierCoeff
        (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus (q i) x : ℝ) : ℂ)) k := by
    unfold UnitAddTorus.mFourierCoeff
    rw [show (fun x : Torus => UnitAddTorus.mFourier (-k) x •
        ((AVenhance.Infra.Torus.periodicToTorus (AVenhance.spaceLap u) x : ℝ) : ℂ)) =
      fun x => ∑ i : Fin 2, UnitAddTorus.mFourier (-k) x •
        ((AVenhance.Infra.Torus.periodicToTorus (q i) x : ℝ) : ℂ) by
      funext x
      rw [hlap]
      change UnitAddTorus.mFourier (-k) x •
        ((∑ i : Fin 2, AVenhance.Infra.Torus.periodicToTorus (q i) x : ℝ) : ℂ) = _
      rw [Complex.ofReal_sum, Finset.smul_sum]]
    rw [integral_finsetSum Finset.univ (by
      intro i hi
      exact hcomponentIntegrable i)]
  rw [hsumCoeff]
  apply Finset.sum_congr rfl
  intro i hi
  rw [classicalRealPeriodicFourierCoeff_eq_clm (q i) (hqcont i) (hqper i) k]
  rw [← classicalGalerkinWordScalarMap_eq_periodicL2 N c [i, i]]

end AVenhance.Infra.Classical

end
