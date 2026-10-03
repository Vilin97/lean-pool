/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.WeakUniqueness.WeakEnergyPassage
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.WeakUniqueness.DriftYoung
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.WeakUniqueness.Gronwall

/-!
# Zero-data weak energy identity

The finite Fourier energy balances pass to the weak path using strong spacetime `L²`
convergence of both the scalar and gradient cutoffs. The resulting identity is the input for
uniqueness under a bounded drift.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Homogenization
open scoped Topology

namespace AVenhance.Infra.Parabolic.WeakUniqueness

open AVenhance.Infra.Parabolic.FourierGalerkin

theorem ZeroDataEnergy.weakEnergy_unitCube_volume_lt_top :
    volume AVenhance.unitCube < ⊤ := by
  unfold AVenhance.unitCube
  rw [volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]

local instance weakEnergy_zeroData_finite_unitCube :
    IsFiniteMeasure (volume.restrict AVenhance.unitCube) := by
  refine ⟨?_⟩
  simpa only [Measure.restrict_apply_univ] using ZeroDataEnergy.weakEnergy_unitCube_volume_lt_top

theorem ZeroDataEnergy.zeroData_memL2 :
    MemL2On AVenhance.unitCube (fun _ : Vec 2 => (0 : ℝ)) := by
  apply MemLp.of_bound measurable_const.aestronglyMeasurable 0
  filter_upwards with x
  simp

theorem ZeroDataEnergy.weakEnergy_region_product_integrable
    {F G : ℝ × Vec 2 → ℝ} {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hF : MemLp F 2 (volume.restrict AVenhance.timeCube))
    (hG : MemLp G 2 (volume.restrict AVenhance.timeCube)) :
    Integrable (fun p => F p * G p)
      (volume.restrict (weakEnergyRegion t)) := by
  have hprod : Integrable (fun p => F p * G p)
      (volume.restrict AVenhance.timeCube) := weak_product_integrable_timeCube hF hG
  exact hprod.mono_measure
    (Measure.restrict_mono (weakEnergy_region_subset_timeCube ht) le_rfl)

theorem ZeroDataEnergy.weakEnergy_square_integrable
    {F : ℝ × Vec 2 → ℝ}
    (hF : MemLp F 2 (volume.restrict AVenhance.timeCube)) :
    Integrable (fun p => F p ^ 2) (volume.restrict AVenhance.timeCube) :=
  (memLp_two_iff_integrable_sq hF.aestronglyMeasurable).1 hF

theorem ZeroDataEnergy.weakEnergy_timeMarginal_intervalIntegrable
    {F : ℝ × Vec 2 → ℝ}
    (hF : Integrable F (volume.restrict AVenhance.timeCube)) :
    IntervalIntegrable
      (fun s => ∫ x in AVenhance.unitCube, F (s, x)) volume 0 1 := by
  have hproduct : Integrable F
      ((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
        (volume.restrict AVenhance.unitCube)) := by
    rwa [← weakEnergy_timeCube_measure_eq_product]
  have htime : Integrable (fun s => ∫ x, F (s, x)
      ∂(volume.restrict AVenhance.unitCube))
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) := hproduct.integral_prod_left
  have hmeasure : volume.restrict (Set.Ioo (0 : ℝ) 1) =
      volume.restrict (Set.Ioc (0 : ℝ) 1) :=
    Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Ioc
  have htime' : Integrable (fun s => ∫ x, F (s, x)
      ∂(volume.restrict AVenhance.unitCube))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    rw [← hmeasure]
    exact htime
  rw [intervalIntegrable_iff, uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact htime'

theorem ZeroDataEnergy.weakEnergy_scalar_pairing_projection_tendsto
    {F U : ℝ × Vec 2 → ℝ} {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hF : MemLp F 2 (volume.restrict AVenhance.timeCube))
    (hU : MemLp U 2 (volume.restrict AVenhance.timeCube))
    (P : ℕ → ℝ × Vec 2 → ℝ)
    (he : ∀ N, MemLp (fun p => U p - P N p) 2
      (volume.restrict AVenhance.timeCube))
    (henergy : Tendsto (fun N => ∫ p in AVenhance.timeCube,
        (U p - P N p) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun N => ∫ p in weakEnergyRegion t, F p * P N p) atTop
      (𝓝 (∫ p in weakEnergyRegion t, F p * U p)) := by
  let μR := volume.restrict (weakEnergyRegion t)
  have hFU : Integrable (fun p => F p * U p) μR :=
    ZeroDataEnergy.weakEnergy_region_product_integrable ht hF hU
  have herr (N : ℕ) : Integrable (fun p => F p * (U p - P N p)) μR :=
    ZeroDataEnergy.weakEnergy_region_product_integrable ht hF (he N)
  have hpairError := weakEnergy_pairing_error_tendsto_on_region hF
    (fun N p => U p - P N p) he henergy ht
  have hidentity (N : ℕ) :
      (∫ p in weakEnergyRegion t, F p * P N p) =
        (∫ p in weakEnergyRegion t, F p * U p) -
          ∫ p in weakEnergyRegion t, F p * (U p - P N p) := by
    rw [← integral_sub (hFU) (herr N)]
    apply integral_congr_ae
    filter_upwards with p
    ring
  have hlimit := (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => ∫ p in weakEnergyRegion t, F p * U p)
        atTop (𝓝 (∫ p in weakEnergyRegion t, F p * U p))).sub hpairError
  have hlimit' : Tendsto (fun N =>
      (∫ p in weakEnergyRegion t, F p * U p) -
        ∫ p in weakEnergyRegion t, F p * (U p - P N p)) atTop
      (𝓝 (∫ p in weakEnergyRegion t, F p * U p)) := by
    simpa using hlimit
  exact hlimit'.congr' (Filter.Eventually.of_forall fun N => (hidentity N).symm)

theorem ZeroDataEnergy.weakEnergy_driftPairing_projection_tendsto
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {f : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ} {D : ℝ → Vec 2 → Vec 2}
    (hu : AVenhance.IsWeakSolutionGrad b κ f u D)
    (hb_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (hb_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ C)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun N => ∫ p in weakEnergyRegion t,
        Homogenization.vecDot (b p.1 p.2) (D p.1 p.2) *
          weakFourierModeProjection N u p.1 p.2)
      atTop (𝓝 (∫ p in weakEnergyRegion t,
        Homogenization.vecDot (b p.1 p.2) (D p.1 p.2) * u p.1 p.2)) := by
  let F : ℝ × Vec 2 → ℝ := fun p =>
    Homogenization.vecDot (b p.1 p.2) (D p.1 p.2)
  let U : ℝ × Vec 2 → ℝ := fun p => u p.1 p.2
  let P : ℕ → ℝ × Vec 2 → ℝ := fun N p =>
    weakFourierModeProjection N u p.1 p.2
  have hF : MemLp F 2 (volume.restrict AVenhance.timeCube) := by
    exact weakEnergy_drift_memLp_two hu hb_meas hb_bdd
  have hU : MemLp U 2 (volume.restrict AVenhance.timeCube) := by
    exact hu.2.2.1
  have he (N : ℕ) : MemLp (fun p => U p - P N p) 2
      (volume.restrict AVenhance.timeCube) := by
    exact hU.sub (weakEnergyProjection_memLp hu N)
  have henergy : Tendsto (fun N => ∫ p in AVenhance.timeCube,
      (U p - P N p) ^ 2) atTop (𝓝 0) := by
    simpa [U, P] using weakFourierProjection_scalar_spacetime_L2_tendsto hu
  have hconv := ZeroDataEnergy.weakEnergy_scalar_pairing_projection_tendsto ht hF hU P he henergy
  simpa [F, U, P] using hconv

theorem ZeroDataEnergy.weakEnergy_gradientPairing_projection_tendsto
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {f : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ} {D : ℝ → Vec 2 → Vec 2}
    (hu : AVenhance.IsWeakSolutionGrad b κ f u D)
    (i : Fin 2) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun N => ∫ p in weakEnergyRegion t,
        D p.1 p.2 i *
          AVenhance.spaceGrad (weakFourierModeProjection N u p.1) p.2 i)
      atTop (𝓝 (∫ p in weakEnergyRegion t, D p.1 p.2 i ^ 2)) := by
  let F : ℝ × Vec 2 → ℝ := fun p => D p.1 p.2 i
  let U : ℝ × Vec 2 → ℝ := fun p => D p.1 p.2 i
  let P : ℕ → ℝ × Vec 2 → ℝ := fun N p =>
    AVenhance.spaceGrad (weakFourierModeProjection N u p.1) p.2 i
  have hF : MemLp F 2 (volume.restrict AVenhance.timeCube) := hu.2.2.2.1 i
  have hU : MemLp U 2 (volume.restrict AVenhance.timeCube) := hF
  have he (N : ℕ) : MemLp (fun p => U p - P N p) 2
      (volume.restrict AVenhance.timeCube) := by
    exact hU.sub (weakEnergyGradient_memLp hu N i)
  have henergy : Tendsto (fun N => ∫ p in AVenhance.timeCube,
      (U p - P N p) ^ 2) atTop (𝓝 0) := by
    simpa [U, P] using weakFourierProjection_gradient_spacetime_L2_tendsto hu i
  have hconv := ZeroDataEnergy.weakEnergy_scalar_pairing_projection_tendsto ht hF hU P he henergy
  simpa [F, U, P, pow_two] using hconv

/-- A weak solution satisfies the full weak energy identity at every time. The drift term
is kept signed; boundedness of the drift is used only to justify the spacetime `L²` pairing
passage. -/
theorem weak_solution_energy_identity
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {f : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ} {D : ℝ → Vec 2 → Vec 2}
    (hu : AVenhance.IsWeakSolutionGrad b κ f u D)
    (hf : MemL2On AVenhance.unitCube f)
    (hb_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (hb_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ C)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    AVenhance.l2NormSq (u t) + 2 *
      ((∫ p in weakEnergyRegion t,
        Homogenization.vecDot (b p.1 p.2) (D p.1 p.2) * u p.1 p.2) +
       κ * ∫ p in weakEnergyRegion t,
        Homogenization.vecDot (D p.1 p.2) (D p.1 p.2)) = AVenhance.l2NormSq f := by
  let drift : ℝ × Vec 2 → ℝ := fun p =>
    Homogenization.vecDot (b p.1 p.2) (D p.1 p.2)
  let value : ℝ × Vec 2 → ℝ := fun p => u p.1 p.2
  let driftLimit : ℝ := ∫ p in weakEnergyRegion t, drift p * value p
  let gradientLimit : ℝ := ∑ i : Fin 2,
    ∫ p in weakEnergyRegion t, D p.1 p.2 i ^ 2
  let driftCut (N : ℕ) : ℝ := ∫ p in weakEnergyRegion t,
    drift p * weakFourierModeProjection N u p.1 p.2
  let gradientCut (N : ℕ) : ℝ := ∑ i : Fin 2,
    ∫ p in weakEnergyRegion t, D p.1 p.2 i *
      AVenhance.spaceGrad (weakFourierModeProjection N u p.1) p.2 i
  let cutoffEnergy (N : ℕ) : ℝ :=
    ‖weakFourierProjectionL2 N u t‖ ^ 2 +
      2 * (driftCut N + κ * gradientCut N)
  let fullEnergy : ℝ := AVenhance.l2NormSq (u t) +
      2 * (driftLimit + κ * gradientLimit)
  have hdriftMem : MemLp drift 2 (volume.restrict AVenhance.timeCube) :=
    weakEnergy_drift_memLp_two hu hb_meas hb_bdd
  have hvalueMem : MemLp value 2 (volume.restrict AVenhance.timeCube) := hu.2.2.1
  have hdriftConv : Tendsto driftCut atTop (𝓝 driftLimit) := by
    exact ZeroDataEnergy.weakEnergy_driftPairing_projection_tendsto hu hb_meas hb_bdd ht
  have hgradientConv : Tendsto gradientCut atTop (𝓝 gradientLimit) := by
    dsimp [gradientCut, gradientLimit]
    apply tendsto_finsetSum
    intro i hi
    exact ZeroDataEnergy.weakEnergy_gradientPairing_projection_tendsto hu i ht
  have hnormConv := weakFourierProjectionL2_normSq_tendsto hu t ht
  have hcutConv : Tendsto cutoffEnergy atTop (𝓝 fullEnergy) := by
    dsimp [cutoffEnergy, fullEnergy]
    exact hnormConv.add ((hdriftConv.add (hgradientConv.const_mul κ)).const_mul 2)
  have hfinite (N : ℕ) : cutoffEnergy N =
      ‖weakFourierProjectionL2 N (fun _ x => f x) 0‖ ^ 2 := by
    have henergy := weak_solution_finite_fourier_energy_identity hu hf N ht
    have hpair := weakEnergy_finiteProjection_pairing_integral hu N ht
    have hcoeffInit : weakFourierCoefficientPath N u 0 =
        weakFourierCoefficientPath N (fun _ x => f x) 0 := by
      ext i
      let ψ := realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)
      have hmode := weak_solution_mode_integral_path hu hf
        ((realFourierModeAmbient_contDiff N
          ((realFourierIndexEquivFin N).symm i)).of_le le_top)
        (realFourierModeAmbient_periodic N
          ((realFourierIndexEquivFin N).symm i)) 0 ⟨le_rfl, by norm_num⟩
      have hzero : weakModePairing u ψ 0 =
          weakModePairing (fun _ x => f x) ψ 0 := by
        simpa using hmode
      simp [weakFourierCoefficientPath, ψ, hzero]
    have hinitProjection : weakFourierProjectionL2 N u 0 =
        weakFourierProjectionL2 N (fun _ x => f x) 0 := by
      simp [weakFourierProjectionL2, hcoeffInit]
    have hcoeffNorm (s : ℝ) :
        ‖weakFourierCoefficientPath N u s‖ ^ 2 =
          ‖weakFourierProjectionL2 N u s‖ ^ 2 := by
      rw [weakFourierProjectionL2, realFourierScalarMap_norm]
    have hcoeffInitNorm : ‖weakFourierCoefficientPath N u 0‖ ^ 2 =
        ‖weakFourierProjectionL2 N (fun _ x => f x) 0‖ ^ 2 := by
      rw [hcoeffNorm 0, hinitProjection]
    have hdriftInt : Integrable
        (fun p => drift p * weakFourierModeProjection N u p.1 p.2)
        (volume.restrict (weakEnergyRegion t)) := by
      exact ZeroDataEnergy.weakEnergy_region_product_integrable ht hdriftMem
        (weakEnergyProjection_memLp hu N)
    have hgradientInt (i : Fin 2) : Integrable
        (fun p => D p.1 p.2 i *
          AVenhance.spaceGrad (weakFourierModeProjection N u p.1) p.2 i)
        (volume.restrict (weakEnergyRegion t)) := by
      exact ZeroDataEnergy.weakEnergy_region_product_integrable ht (hu.2.2.2.1 i)
        (weakEnergyGradient_memLp hu N i)
    have hdotInt : Integrable
        (fun p => Homogenization.vecDot (D p.1 p.2)
          (AVenhance.spaceGrad (weakFourierModeProjection N u p.1) p.2))
        (volume.restrict (weakEnergyRegion t)) := by
      have hsum := integrable_finsetSum Finset.univ (fun i hi => hgradientInt i)
      have hEq : (fun p : ℝ × Vec 2 => Homogenization.vecDot (D p.1 p.2)
          (AVenhance.spaceGrad (weakFourierModeProjection N u p.1) p.2)) =
          fun p : ℝ × Vec 2 => ∑ i : Fin 2, D p.1 p.2 i *
            AVenhance.spaceGrad (weakFourierModeProjection N u p.1) p.2 i := by
        funext p
        rfl
      rw [hEq]
      exact hsum
    have hdotIntegral :
        (∫ p in weakEnergyRegion t,
          Homogenization.vecDot (D p.1 p.2)
            (AVenhance.spaceGrad (weakFourierModeProjection N u p.1) p.2)) =
          gradientCut N := by
      change (∫ p in weakEnergyRegion t,
          ∑ i : Fin 2, D p.1 p.2 i *
            AVenhance.spaceGrad (weakFourierModeProjection N u p.1) p.2 i) = _
      rw [integral_finsetSum Finset.univ (fun i hi => hgradientInt i)]
    have hpairingDecomp :
        (∫ p in weakEnergyRegion t, 2 *
          (drift p * weakFourierModeProjection N u p.1 p.2 +
            κ * Homogenization.vecDot (D p.1 p.2)
              (AVenhance.spaceGrad (weakFourierModeProjection N u p.1) p.2))) =
          2 * (driftCut N + κ * gradientCut N) := by
      rw [integral_const_mul, integral_add hdriftInt (hdotInt.const_mul κ),
        integral_const_mul, hdotIntegral]
    have henergy' := henergy
    rw [hpair, hcoeffNorm t, hcoeffInitNorm] at henergy'
    rw [hpairingDecomp] at henergy'
    dsimp [cutoffEnergy]
    simpa using henergy'
  have hinitProjectionNorm : Tendsto
      (fun N => ‖weakFourierProjectionL2 N (fun _ x => f x) 0‖ ^ 2)
      atTop (𝓝 (AVenhance.l2NormSq f)) := by
    have hprojection := weakFourierProjectionL2_tendsto
      (u := fun _ x => f x) (t := 0) hf
    have hnorm := (continuous_norm.pow 2).continuousAt.tendsto.comp hprojection
    change Tendsto (fun N =>
      ‖weakFourierProjectionL2 N (fun _ x => f x) 0‖ ^ 2) atTop
      (𝓝 (‖(weakProjection_realCellToTorus_memLp hf).toLp
        (AVenhance.Infra.Torus.periodicToTorus f)‖ ^ 2)) at hnorm
    simpa only [weakProjection_scalarTransfer_normSq hf] using hnorm
  have hfiniteConv : Tendsto cutoffEnergy atTop (𝓝 (AVenhance.l2NormSq f)) := by
    exact hinitProjectionNorm.congr'
      (Filter.Eventually.of_forall fun N => (hfinite N).symm)
  have hlimitEq := tendsto_nhds_unique hcutConv hfiniteConv
  have hDproduct (i : Fin 2) : Integrable
      (fun p : ℝ × Vec 2 => D p.1 p.2 i * D p.1 p.2 i)
      (volume.restrict (weakEnergyRegion t)) :=
    ZeroDataEnergy.weakEnergy_region_product_integrable ht (hu.2.2.2.1 i) (hu.2.2.2.1 i)
  have hgradientLimit :
      (∫ p in weakEnergyRegion t,
        Homogenization.vecDot (D p.1 p.2) (D p.1 p.2)) = gradientLimit := by
    change (∫ p in weakEnergyRegion t,
        ∑ i : Fin 2, D p.1 p.2 i * D p.1 p.2 i) = _
    rw [integral_finsetSum Finset.univ (fun i hi => hDproduct i)]
    simp [gradientLimit, pow_two]
  rw [hgradientLimit]
  simpa [fullEnergy, driftLimit, gradientLimit, drift, value] using hlimitEq

/-- The zero-datum energy identity is the corresponding specialization of the full identity. -/
theorem weak_solution_zero_data_energy_identity
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ}
    {u : ℝ → Vec 2 → ℝ} {D : ℝ → Vec 2 → Vec 2}
    (hu : AVenhance.IsWeakSolutionGrad b κ (fun _ : Vec 2 => (0 : ℝ)) u D)
    (hb_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (hb_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ C)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    AVenhance.l2NormSq (u t) + 2 *
      ((∫ p in weakEnergyRegion t,
        Homogenization.vecDot (b p.1 p.2) (D p.1 p.2) * u p.1 p.2) +
       κ * ∫ p in weakEnergyRegion t,
        Homogenization.vecDot (D p.1 p.2) (D p.1 p.2)) = 0 := by
  have h := weak_solution_energy_identity hu ZeroDataEnergy.zeroData_memL2 hb_meas hb_bdd ht
  simpa [AVenhance.l2NormSq] using h

/-- The zero-data energy identity and the pointwise drift bound imply the parabolic energy
inequality, with the diffusion term absorbed by Young's inequality. -/
theorem weak_solution_zero_data_energy_inequality
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ}
    {u : ℝ → Vec 2 → ℝ} {D : ℝ → Vec 2 → Vec 2}
    (hu : AVenhance.IsWeakSolutionGrad b κ (fun _ : Vec 2 => (0 : ℝ)) u D)
    (hb_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (hb_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ C)
    (hκ : 0 < κ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1,
      AVenhance.l2NormSq (u t) ≤ B ^ 2 / κ *
        ∫ s in (0 : ℝ)..t, AVenhance.l2NormSq (u s) := by
  obtain ⟨B, hB, hBdot⟩ := frozenDrift_vecDot_bound b hb_bdd
  refine ⟨B, hB, ?_⟩
  intro t ht
  let drift : ℝ × Vec 2 → ℝ := fun p =>
    Homogenization.vecDot (b p.1 p.2) (D p.1 p.2)
  let value : ℝ × Vec 2 → ℝ := fun p => u p.1 p.2
  let normSq : ℝ × Vec 2 → ℝ := fun p =>
    euclideanVecNorm (D p.1 p.2) ^ 2
  let valueSq : ℝ × Vec 2 → ℝ := fun p => value p ^ 2
  let μR := volume.restrict (weakEnergyRegion t)
  have hμ : μR ≤ volume.restrict AVenhance.timeCube :=
    Measure.restrict_mono (weakEnergy_region_subset_timeCube ht) le_rfl
  have hdriftMem := weakEnergy_drift_memLp_two hu hb_meas hb_bdd
  have hvalueMem : MemLp value 2 (volume.restrict AVenhance.timeCube) := hu.2.2.1
  have hdriftValue : Integrable (fun p => drift p * value p)
      (volume.restrict AVenhance.timeCube) :=
    weak_product_integrable_timeCube hdriftMem hvalueMem
  have hvalueSq : Integrable valueSq (volume.restrict AVenhance.timeCube) := by
    exact ZeroDataEnergy.weakEnergy_square_integrable hvalueMem
  have hnormSq : Integrable normSq (volume.restrict AVenhance.timeCube) := by
    have hcoord (i : Fin 2) : Integrable
        (fun p : ℝ × Vec 2 => D p.1 p.2 i ^ 2)
        (volume.restrict AVenhance.timeCube) :=
      ZeroDataEnergy.weakEnergy_square_integrable (hu.2.2.2.1 i)
    have hsum := integrable_finsetSum Finset.univ (fun i hi => hcoord i)
    have heq : normSq = fun p => ∑ i : Fin 2, D p.1 p.2 i ^ 2 := by
      funext p
      change euclideanVecNorm (D p.1 p.2) ^ 2 = _
      exact (euclideanVecNorm_sq (D p.1 p.2)).trans
        (by simp [Homogenization.vecNormSq, Homogenization.vecDot, pow_two])
    rw [heq]
    exact hsum
  have hdriftRegion : Integrable (fun p => drift p * value p) μR :=
    hdriftValue.mono_measure hμ
  have hnormRegion : Integrable normSq μR := hnormSq.mono_measure hμ
  have hvalueRegion : Integrable valueSq μR := hvalueSq.mono_measure hμ
  have hmajor : Integrable (fun p => κ / 2 * normSq p +
      B ^ 2 / (2 * κ) * valueSq p) μR := by
    exact (hnormRegion.const_mul (κ / 2)).add
      (hvalueRegion.const_mul (B ^ 2 / (2 * κ)))
  have hregionMeas : MeasurableSet (weakEnergyRegion t) := by
    exact measurableSet_Ioo.prod (by
      unfold AVenhance.unitCube
      exact MeasurableSet.pi Set.countable_univ
        (fun _ _ => measurableSet_Ioo))
  have hpoint : ∀ᵐ p ∂μR,
      |drift p * value p| ≤ κ / 2 * normSq p +
        B ^ 2 / (2 * κ) * valueSq p := by
    filter_upwards [ae_restrict_mem hregionMeas] with p hp
    rcases hp with ⟨⟨ht0, htt⟩, _hx⟩
    have hpTime : p.1 ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨le_of_lt ht0, (lt_of_lt_of_le htt ht.2).le⟩
    have hdot := hBdot p.1 hpTime p.2 (D p.1 p.2)
    have hmul := mul_le_mul_of_nonneg_right hdot (abs_nonneg (value p))
    have hYoung := drift_product_le_young hκ (B := B)
      (a := euclideanVecNorm (D p.1 p.2)) (c := |value p|)
    dsimp [drift, value, normSq, valueSq]
    calc
      |Homogenization.vecDot (b p.1 p.2) (D p.1 p.2) * u p.1 p.2| =
          |Homogenization.vecDot (b p.1 p.2) (D p.1 p.2)| * |u p.1 p.2| := abs_mul _ _
      _ ≤ B * euclideanVecNorm (D p.1 p.2) * |u p.1 p.2| := hmul
      _ ≤ κ / 2 * euclideanVecNorm (D p.1 p.2) ^ 2 +
          B ^ 2 / (2 * κ) * (u p.1 p.2) ^ 2 := by
        simpa [sq_abs] using hYoung
  have hmono := integral_mono_ae hdriftRegion.abs hmajor hpoint
  have hmajorNorm : Integrable (fun p => κ / 2 * normSq p) μR := by
    simpa [mul_comm] using hnormRegion.const_mul (κ / 2)
  have hmajorValue : Integrable (fun p => B ^ 2 / (2 * κ) * valueSq p) μR := by
    simpa [mul_comm] using hvalueRegion.const_mul (B ^ 2 / (2 * κ))
  have hmajorNormIntegral :
      (∫ p in weakEnergyRegion t, κ / 2 * normSq p) =
        κ / 2 * (∫ p in weakEnergyRegion t, normSq p) := by
    rw [integral_const_mul]
  have hmajorValueIntegral :
      (∫ p in weakEnergyRegion t, B ^ 2 / (2 * κ) * valueSq p) =
        B ^ 2 / (2 * κ) * (∫ p in weakEnergyRegion t, valueSq p) := by
    rw [integral_const_mul]
  have hdriftBound :
      |∫ p in weakEnergyRegion t, drift p * value p| ≤
        (κ / 2 * (∫ p in weakEnergyRegion t, normSq p)) +
          (B ^ 2 / (2 * κ) * (∫ p in weakEnergyRegion t, valueSq p)) := by
    calc
      |∫ p in weakEnergyRegion t, drift p * value p| ≤
          ∫ p in weakEnergyRegion t, |drift p * value p| :=
            abs_integral_le_integral_abs
      _ ≤ ∫ p in weakEnergyRegion t,
          κ / 2 * normSq p + B ^ 2 / (2 * κ) * valueSq p := hmono
      _ = _ := by
        calc
          _ = (∫ p in weakEnergyRegion t, κ / 2 * normSq p) +
              ∫ p in weakEnergyRegion t, B ^ 2 / (2 * κ) * valueSq p :=
            integral_add hmajorNorm hmajorValue
          _ = (κ / 2 * (∫ p in weakEnergyRegion t, normSq p)) +
              (B ^ 2 / (2 * κ) * (∫ p in weakEnergyRegion t, valueSq p)) := by
            rw [hmajorNormIntegral, hmajorValueIntegral]
  have hnormEq (p : ℝ × Vec 2) :
      normSq p = Homogenization.vecDot (D p.1 p.2) (D p.1 p.2) := by
    change euclideanVecNorm (D p.1 p.2) ^ 2 = _
    exact (euclideanVecNorm_sq (D p.1 p.2)).trans rfl
  have hnormIntegral :
      (∫ p in weakEnergyRegion t, normSq p) =
        ∫ p in weakEnergyRegion t,
          Homogenization.vecDot (D p.1 p.2) (D p.1 p.2) := by
    apply integral_congr_ae
    exact ae_of_all _ hnormEq
  have hdiffusionNonneg : 0 ≤
      ∫ p in weakEnergyRegion t,
        Homogenization.vecDot (D p.1 p.2) (D p.1 p.2) := by
    apply integral_nonneg_of_ae
    filter_upwards with p
    exact Homogenization.vecNormSq_nonneg (D p.1 p.2)
  have hvalueRegionEq :
      (∫ p in weakEnergyRegion t, valueSq p) =
        ∫ s in (0 : ℝ)..t, AVenhance.l2NormSq (u s) := by
    rw [weakEnergy_region_integral_eq_interval hvalueSq ht]
    rfl
  have hEnergy := weak_solution_zero_data_energy_identity hu hb_meas hb_bdd ht
  have htarget : AVenhance.l2NormSq (u t) + κ *
      ∫ p in weakEnergyRegion t,
        Homogenization.vecDot (D p.1 p.2) (D p.1 p.2) ≤
      B ^ 2 / κ * ∫ s in (0 : ℝ)..t, AVenhance.l2NormSq (u s) := by
    have hcoeff : 2 * (B ^ 2 / (2 * κ)) = B ^ 2 / κ := by
      field_simp [ne_of_gt hκ]
    have hbound :
        |∫ p in weakEnergyRegion t,
          Homogenization.vecDot (b p.1 p.2) (D p.1 p.2) * u p.1 p.2| ≤
          (κ / 2 * (∫ p in weakEnergyRegion t,
            Homogenization.vecDot (D p.1 p.2) (D p.1 p.2))) +
          (B ^ 2 / (2 * κ) * (∫ s in (0 : ℝ)..t, AVenhance.l2NormSq (u s))) := by
      calc
        _ ≤ (κ / 2 * (∫ p in weakEnergyRegion t, normSq p)) +
            (B ^ 2 / (2 * κ) * (∫ p in weakEnergyRegion t, valueSq p)) := by
          change |∫ p in weakEnergyRegion t, drift p * value p| ≤ _
          exact hdriftBound
        _ = _ := by rw [hnormIntegral, hvalueRegionEq]
    let d : ℝ := ∫ p in weakEnergyRegion t,
      Homogenization.vecDot (b p.1 p.2) (D p.1 p.2) * u p.1 p.2
    let G : ℝ := ∫ p in weakEnergyRegion t,
      Homogenization.vecDot (D p.1 p.2) (D p.1 p.2)
    let R : ℝ := ∫ s in (0 : ℝ)..t, AVenhance.l2NormSq (u s)
    have hboundD : |d| ≤ κ / 2 * G + B ^ 2 / (2 * κ) * R := by
      simpa [d, G, R] using hbound
    have hnegative : -2 * d ≤ 2 * |d| := by
      nlinarith [neg_le_abs d]
    have hyoung : 2 * |d| ≤ κ * G + B ^ 2 / κ * R := by
      calc
        2 * |d| ≤ 2 * (κ / 2 * G + B ^ 2 / (2 * κ) * R) := by
          nlinarith [hboundD]
        _ = κ * G + 2 * (B ^ 2 / (2 * κ)) * R := by ring
        _ = κ * G + B ^ 2 / κ * R := by rw [hcoeff]
    have henergyEq : AVenhance.l2NormSq (u t) + 2 * κ * G = -2 * d := by
      dsimp [d, G]
      nlinarith [hEnergy]
    have hfinal : AVenhance.l2NormSq (u t) + κ * G ≤ B ^ 2 / κ * R := by
      linarith
    simpa [G, R] using hfinal
  have hdiffusionNonneg' : 0 ≤ κ *
      ∫ p in weakEnergyRegion t,
        Homogenization.vecDot (D p.1 p.2) (D p.1 p.2) :=
    mul_nonneg hκ.le hdiffusionNonneg
  linarith

/-- The exact weak energy identity makes the squared `L²` norm path continuous on the closed
time interval. The weak-test continuity in the class is the endpoint input to the Fourier
energy identity. -/
theorem weak_solution_zero_data_l2NormSq_continuousOn
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ}
    {u : ℝ → Vec 2 → ℝ} {D : ℝ → Vec 2 → Vec 2}
    (hu : AVenhance.IsWeakSolutionGrad b κ (fun _ : Vec 2 => (0 : ℝ)) u D)
    (hb_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (hb_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ C) :
    ContinuousOn (fun t => AVenhance.l2NormSq (u t)) (Set.Icc (0 : ℝ) 1) := by
  let drift : ℝ × Vec 2 → ℝ := fun p =>
    Homogenization.vecDot (b p.1 p.2) (D p.1 p.2)
  let value : ℝ × Vec 2 → ℝ := fun p => u p.1 p.2
  let spatialEnergy : ℝ × Vec 2 → ℝ := fun p =>
    Homogenization.vecDot (D p.1 p.2) (D p.1 p.2)
  let density : ℝ × Vec 2 → ℝ := fun p =>
    drift p * value p + κ * spatialEnergy p
  let marginal : ℝ → ℝ := fun s =>
    ∫ x in AVenhance.unitCube, density (s, x)
  have hdriftMem := weakEnergy_drift_memLp_two hu hb_meas hb_bdd
  have hvalueMem : MemLp value 2 (volume.restrict AVenhance.timeCube) := hu.2.2.1
  have hdriftValue : Integrable (fun p => drift p * value p)
      (volume.restrict AVenhance.timeCube) :=
    weak_product_integrable_timeCube hdriftMem hvalueMem
  have hspatialEnergy : Integrable spatialEnergy
      (volume.restrict AVenhance.timeCube) := by
    have hcoord (i : Fin 2) : Integrable
        (fun p : ℝ × Vec 2 => D p.1 p.2 i ^ 2)
        (volume.restrict AVenhance.timeCube) :=
      ZeroDataEnergy.weakEnergy_square_integrable (hu.2.2.2.1 i)
    have hsum := integrable_finsetSum Finset.univ (fun i hi => hcoord i)
    have heq : spatialEnergy = fun p => ∑ i : Fin 2, D p.1 p.2 i ^ 2 := by
      funext p
      simp [spatialEnergy, Homogenization.vecDot, pow_two]
    rw [heq]
    exact hsum
  have hdensity : Integrable density
      (volume.restrict AVenhance.timeCube) := by
    exact hdriftValue.add (by
      simpa [density, mul_comm] using hspatialEnergy.const_mul κ)
  have hmarginal : IntervalIntegrable marginal volume 0 1 := by
    exact ZeroDataEnergy.weakEnergy_timeMarginal_intervalIntegrable hdensity
  have hprimitive : ContinuousOn
      (fun t => ∫ s in (0 : ℝ)..t, marginal s) (Set.Icc (0 : ℝ) 1) := by
    simpa using AVenhance.Infra.ODE.continuousOn_intervalPrimitive hmarginal
  have hdriftRegion (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      Integrable (fun p => drift p * value p)
        (volume.restrict (weakEnergyRegion t)) :=
    hdriftValue.mono_measure
      (Measure.restrict_mono (weakEnergy_region_subset_timeCube ht) le_rfl)
  have hspatialRegion (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      Integrable spatialEnergy (volume.restrict (weakEnergyRegion t)) :=
    hspatialEnergy.mono_measure
      (Measure.restrict_mono (weakEnergy_region_subset_timeCube ht) le_rfl)
  have hsplit (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      (∫ p in weakEnergyRegion t, density p) =
        (∫ p in weakEnergyRegion t, drift p * value p) +
          κ * ∫ p in weakEnergyRegion t, spatialEnergy p := by
    calc
      _ = (∫ p in weakEnergyRegion t,
          drift p * value p + κ * spatialEnergy p) := rfl
      _ = (∫ p in weakEnergyRegion t, drift p * value p) +
          ∫ p in weakEnergyRegion t, κ * spatialEnergy p :=
        integral_add (hdriftRegion t ht) (by
          simpa [mul_comm] using (hspatialRegion t ht).const_mul κ)
      _ = _ := by rw [integral_const_mul]
  have hregionTime (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      (∫ p in weakEnergyRegion t, density p) =
        ∫ s in (0 : ℝ)..t, marginal s :=
    weakEnergy_region_integral_eq_interval hdensity ht
  have hrepresentation (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      AVenhance.l2NormSq (u t) = -2 * ∫ s in (0 : ℝ)..t, marginal s := by
    have henergy := weak_solution_zero_data_energy_identity hu hb_meas hb_bdd ht
    have henergy' : AVenhance.l2NormSq (u t) +
        2 * ∫ p in weakEnergyRegion t, density p = 0 := by
      rw [hsplit t ht]
      exact henergy
    rw [hregionTime t ht] at henergy'
    linarith
  have hscaled : ContinuousOn
      (fun t => -2 * ∫ s in (0 : ℝ)..t, marginal s) (Set.Icc (0 : ℝ) 1) := by
    simpa [mul_comm] using hprimitive.const_mul (-2)
  apply hscaled.congr
  intro t ht
  exact hrepresentation t ht

/-- Clamp time to the closed unit interval in the zero-initial-data energy argument. -/
def ZeroDataEnergy.weakZeroEnergyClamp (t : ℝ) : ℝ := max 0 (min t 1)

theorem ZeroDataEnergy.weakZeroEnergyClamp_mem (t : ℝ) :
    ZeroDataEnergy.weakZeroEnergyClamp t ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_right _ _)

theorem ZeroDataEnergy.weakZeroEnergyClamp_eq {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : ZeroDataEnergy.weakZeroEnergyClamp t = t := by
  simp [ZeroDataEnergy.weakZeroEnergyClamp, max_eq_right ht.1, min_eq_left ht.2]

theorem ZeroDataEnergy.weakZeroEnergyClamp_continuous : Continuous
    ZeroDataEnergy.weakZeroEnergyClamp := by
  exact continuous_const.max (continuous_id.min continuous_const)

/-- A bounded drift cannot support a nonzero zero-data weak solution. -/
theorem weak_solution_zero_data_eq_zero
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ}
    {u : ℝ → Vec 2 → ℝ} {D : ℝ → Vec 2 → Vec 2}
    (hu : AVenhance.IsWeakSolutionGrad b κ (fun _ : Vec 2 => (0 : ℝ)) u D)
    (hb_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (hb_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ C)
    (hκ : 0 < κ) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, AVenhance.l2NormSq (u t) = 0 := by
  obtain ⟨B, hB, hineq⟩ :=
    weak_solution_zero_data_energy_inequality hu hb_meas hb_bdd hκ
  let energyPath : ℝ → ℝ := fun t => AVenhance.l2NormSq (u t)
  let energyExtension : ℝ → ℝ := fun t => energyPath (ZeroDataEnergy.weakZeroEnergyClamp t)
  let C : ℝ := B ^ 2 / κ
  have hC : 0 ≤ C := div_nonneg (sq_nonneg B) hκ.le
  have hpathContinuous :=
    weak_solution_zero_data_l2NormSq_continuousOn hu hb_meas hb_bdd
  have hcontinuous : Continuous energyExtension := by
    change Continuous (fun t => energyPath (ZeroDataEnergy.weakZeroEnergyClamp t))
    exact hpathContinuous.comp_continuous ZeroDataEnergy.weakZeroEnergyClamp_continuous
      ZeroDataEnergy.weakZeroEnergyClamp_mem
  have hnonneg (t : ℝ) : 0 ≤ energyExtension t := by
    simp only [energyExtension, energyPath, AVenhance.l2NormSq]
    exact integral_nonneg fun x => sq_nonneg _
  have hinterval (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      (∫ s in (0 : ℝ)..t, energyExtension s) =
        ∫ s in (0 : ℝ)..t, energyPath s := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hsIcc : s ∈ Set.Icc (0 : ℝ) 1 := by
      rw [uIcc_of_le ht.1] at hs
      exact ⟨hs.1, hs.2.trans ht.2⟩
    change energyPath (ZeroDataEnergy.weakZeroEnergyClamp s) = energyPath s
    rw [ZeroDataEnergy.weakZeroEnergyClamp_eq hsIcc]
  have hgronwallInput (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      energyExtension t ≤ C * ∫ s in (0 : ℝ)..t, energyExtension s := by
    have hbase := hineq t ht
    rw [← hinterval t ht] at hbase
    simpa [energyExtension, energyPath, C, ZeroDataEnergy.weakZeroEnergyClamp_eq ht] using hbase
  have hzero := continuous_nonneg_eq_zero_of_integral_gronwall
    hcontinuous hC (fun t ht => hnonneg t) hgronwallInput
  intro t ht
  have h := hzero t ht
  simpa [energyExtension, energyPath, ZeroDataEnergy.weakZeroEnergyClamp_eq ht] using h

end AVenhance.Infra.Parabolic.WeakUniqueness

end
