/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.FrozenDrift
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.MatrixOperator
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.Basic

/-!
# Measurable drift Galerkin entries

This module transports the ambient drift hypotheses to the time-dependent entries of a
finite periodic weak-form matrix. The mode and gradient representatives are supplied explicitly;
the real Fourier frame can then use this bridge without changing the weak-form convention.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Homogenization
open scoped ENNReal

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance frozenMatrixMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance frozenMatrixMeasureIsAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance frozenMatrixProbability : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.Parabolic.FourierGalerkin

variable {n : ℕ}

theorem FrozenMatrix.frozenWeakEntry_drift_eq_unitCube
    (b : ℝ → Vec 2 → Vec 2) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hbper : ∀ s ∈ Set.Icc (0 : ℝ) 1, IsZ2Periodic (b s))
    (grad : Vec 2 → Vec 2) (weight : Vec 2 → ℝ)
    (hgradper : AVenhance.Infra.Torus.IsZdPeriodic grad)
    (hweightper : AVenhance.Infra.Torus.IsZdPeriodic weight) :
    (∫ x : Torus,
      vecDot (AVenhance.Infra.Torus.periodicToTorus (b t) x)
        (AVenhance.Infra.Torus.periodicToTorus grad x) *
          AVenhance.Infra.Torus.periodicToTorus weight x) =
      ∫ x in AVenhance.unitCube, Homogenization.vecDot (b t x) (grad x) * weight x := by
  let integrand : Vec 2 → ℝ := fun x => Homogenization.vecDot (b t x) (grad x) * weight x
  have hintegrand : AVenhance.Infra.Torus.IsZdPeriodic integrand := by
    intro k x
    simp only [integrand]
    have hb : b t (x + AVenhance.Infra.Torus.intVector k) = b t x := by
      have hshift : AVenhance.latticeShift k = AVenhance.Infra.Torus.intVector k := rfl
      rw [← hshift]
      exact hbper t ht k x
    rw [hb, hgradper k x, hweightper k x]
  calc
    _ = ∫ x : Torus, AVenhance.Infra.Torus.periodicToTorus integrand x := by
      apply integral_congr_ae
      filter_upwards with x
      rfl
    _ = ∫ x in AVenhance.Infra.Torus.unitCell 2, integrand x :=
      AVenhance.Infra.Torus.integral_periodicToTorus_eq_unitCell integrand
    _ = ∫ x in AVenhance.unitCube, integrand x :=
      AVenhance.Infra.Torus.integral_unitCell_eq_unitCube integrand

/-- Under the measurable and periodic drift assumptions, each weak-form matrix entry is
a.e. strongly measurable in time. Only the drift part varies with time; the diffusion part is a
fixed scalar integral. The torus integral is identified with the open-cell integral using
periodicity of the modes and the drift. -/
theorem frozenWeakFormMatrixEntry_time_aestronglyMeasurable
    (b : ℝ → Vec 2 → Vec 2)
    (hb_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (hb_per : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsZ2Periodic (b t))
    (κ : ℝ) (mode : Fin n → Torus → ℝ)
    (modeGrad : Fin n → Torus → Fin 2 → ℝ)
    (modeAmbient : Fin n → Vec 2 → ℝ)
    (modeGradAmbient : Fin n → Vec 2 → Fin 2 → ℝ)
    (hmode : ∀ i, mode i = AVenhance.Infra.Torus.periodicToTorus (modeAmbient i))
    (hgrad : ∀ i, modeGrad i =
      AVenhance.Infra.Torus.periodicToTorus (modeGradAmbient i))
    (hmode_meas : ∀ i, AEStronglyMeasurable (modeAmbient i)
      (volume.restrict AVenhance.unitCube))
    (hgrad_meas : ∀ i, AEStronglyMeasurable (modeGradAmbient i)
      (volume.restrict AVenhance.unitCube))
    (hmode_per : ∀ i, AVenhance.Infra.Torus.IsZdPeriodic (modeAmbient i))
    (hgrad_per : ∀ i j,
      AVenhance.Infra.Torus.IsZdPeriodic (fun x => modeGradAmbient i x j)) :
    ∀ i j, AEStronglyMeasurable
      (fun t => weakFormMatrixEntry
        (fun s x => AVenhance.Infra.Torus.periodicToTorus (b s) x)
        κ mode modeGrad t i j)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  intro i j
  have hdrift := frozenDrift_weakEntry_time_aestronglyMeasurable b hb_meas
    (modeGradAmbient j) (hgrad_meas j) (modeAmbient i) (hmode_meas i)
  let torusDrift : ℝ → ℝ := fun t =>
    ∫ x : Torus, vecDot (AVenhance.Infra.Torus.periodicToTorus (b t) x)
      (AVenhance.Infra.Torus.periodicToTorus (modeGradAmbient j) x) *
        AVenhance.Infra.Torus.periodicToTorus (modeAmbient i) x
  let cellDrift : ℝ → ℝ := fun t =>
    ∫ x in AVenhance.unitCube,
      Homogenization.vecDot (b t x) (modeGradAmbient j x) * modeAmbient i x
  have htorus_eq_cell : ∀ t ∈ Set.Icc (0 : ℝ) 1, torusDrift t = cellDrift t := by
    intro t ht
    have hgradperVec : AVenhance.Infra.Torus.IsZdPeriodic (modeGradAmbient j) := by
      intro k x
      funext l
      exact hgrad_per j l k x
    exact FrozenMatrix.frozenWeakEntry_drift_eq_unitCube b t ht hb_per
      (modeGradAmbient j) (modeAmbient i) hgradperVec
      (hmode_per i)
  have hdrift' : AEStronglyMeasurable torusDrift
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    have hcell_torus : cellDrift =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)] torusDrift := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact (htorus_eq_cell t ht).symm
    exact hdrift.congr hcell_torus
  let diffusion : ℝ := ∫ x : Torus,
    vecDot (modeGrad j x) (modeGrad i x)
  let bT : ℝ → Torus → Fin 2 → ℝ := fun t x =>
    AVenhance.Infra.Torus.periodicToTorus (b t) x
  have hweak : (fun t => weakFormMatrixEntry bT κ mode modeGrad t i j) =
      fun t => -torusDrift t - κ * diffusion := by
    funext t
    simp [weakFormMatrixEntry, torusDrift, diffusion, hmode, hgrad, bT]
  rw [hweak]
  have hsum : (fun t => -torusDrift t - κ * diffusion) =
      fun t => (-torusDrift t) + (-κ * diffusion) := by
    funext t
    ring
  rw [hsum]
  exact hdrift'.neg.add_const (-κ * diffusion)

/-- The weak-form coefficient matrix on the physical time interval, extended by zero to the
whole line for the measurable-coefficient ODE interface. -/
def frozenWeakFormCoefficient (b : ℝ → Vec 2 → Vec 2) (κ : ℝ)
    (mode : Fin n → Torus → ℝ) (modeGrad : Fin n → Torus → Fin 2 → ℝ) :
    ℝ → Coefficients n →L[ℝ] Coefficients n :=
  fun t => Set.indicator (Set.Icc (0 : ℝ) 1)
    (fun s => matrixCoefficientCLM (fun i j =>
      weakFormMatrixEntry
        (fun r x => AVenhance.Infra.Torus.periodicToTorus (b r) x)
        κ mode modeGrad s i j)) t

/-- Product measurability of the drift induces a globally a.e. strongly measurable
Galerkin coefficient after extending the physical-time matrix by zero. -/
theorem frozenWeakFormCoefficient_aestronglyMeasurable
    (b : ℝ → Vec 2 → Vec 2)
    (hb_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (hb_per : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsZ2Periodic (b t))
    (κ : ℝ) (mode : Fin n → Torus → ℝ)
    (modeGrad : Fin n → Torus → Fin 2 → ℝ)
    (modeAmbient : Fin n → Vec 2 → ℝ)
    (modeGradAmbient : Fin n → Vec 2 → Fin 2 → ℝ)
    (hmode : ∀ i, mode i = AVenhance.Infra.Torus.periodicToTorus (modeAmbient i))
    (hgrad : ∀ i, modeGrad i =
      AVenhance.Infra.Torus.periodicToTorus (modeGradAmbient i))
    (hmode_meas : ∀ i, AEStronglyMeasurable (modeAmbient i)
      (volume.restrict AVenhance.unitCube))
    (hgrad_meas : ∀ i, AEStronglyMeasurable (modeGradAmbient i)
      (volume.restrict AVenhance.unitCube))
    (hmode_per : ∀ i, AVenhance.Infra.Torus.IsZdPeriodic (modeAmbient i))
    (hgrad_per : ∀ i j,
      AVenhance.Infra.Torus.IsZdPeriodic (fun x => modeGradAmbient i x j)) :
    AEStronglyMeasurable (frozenWeakFormCoefficient b κ mode modeGrad) volume := by
  change AEStronglyMeasurable
    (Set.indicator (Set.Icc (0 : ℝ) 1) (fun s => matrixCoefficientCLM (fun i j =>
      weakFormMatrixEntry
        (fun r x => AVenhance.Infra.Torus.periodicToTorus (b r) x)
        κ mode modeGrad s i j))) volume
  rw [aestronglyMeasurable_indicator_iff measurableSet_Icc]
  exact matrixCoefficientCLM_aestronglyMeasurable fun i j =>
    frozenWeakFormMatrixEntry_time_aestronglyMeasurable b hb_meas hb_per κ mode modeGrad
      modeAmbient modeGradAmbient hmode hgrad hmode_meas hgrad_meas hmode_per hgrad_per i j

/-- A uniform bound on all physical-time matrix entries gives the global operator bound required
by the measurable linear ODE interface. The zero extension makes the outside-interval case
immediate. -/
theorem frozenWeakFormCoefficient_norm_le_of_entries
    (b : ℝ → Vec 2 → Vec 2) (κ : ℝ)
    (mode : Fin n → Torus → ℝ) (modeGrad : Fin n → Torus → Fin 2 → ℝ)
    {K : ℝ} (hK : 0 ≤ K)
    (hentry : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i j,
      |weakFormMatrixEntry
        (fun s x => AVenhance.Infra.Torus.periodicToTorus (b s) x)
        κ mode modeGrad t i j| ≤ K) :
    ∀ t, ‖frozenWeakFormCoefficient b κ mode modeGrad t‖ ≤ (n : ℝ) ^ 2 * K := by
  intro t
  have hbound_nonneg : 0 ≤ (n : ℝ) ^ 2 * K :=
    mul_nonneg (sq_nonneg _) hK
  by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
  · simpa [frozenWeakFormCoefficient, ht] using
      (matrixCoefficientCLM_norm_le_uniform
        (fun i j => weakFormMatrixEntry
          (fun s x => AVenhance.Infra.Torus.periodicToTorus (b s) x)
          κ mode modeGrad t i j)
        (fun i j => hentry t ht i j))
  · simpa [frozenWeakFormCoefficient, ht] using hbound_nonneg

/-- A finite mode family with explicit `L²` gradient/function bounds has uniformly bounded
    weak-form entries. The drift part uses only the measurable bounded drift estimate; the
diffusion term is controlled by the supplied finite-family gradient pairing bound. -/
theorem frozenWeakFormMatrixEntry_abs_bound
    (b : ℝ → Vec 2 → Vec 2)
    (hb_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ C)
    (κ : ℝ) (mode : Fin n → Torus → ℝ)
    (modeGrad : Fin n → Torus → Fin 2 → ℝ)
    {G U D : ℝ} (hG : 0 ≤ G) (hU : 0 ≤ U) (hD : 0 ≤ D)
    (hgrad_memLp : ∀ j,
      MemLp (fun x : Torus => euclideanVecNorm (modeGrad j x)) 2 volume)
    (hmode_memLp : ∀ i, MemLp (mode i) 2 volume)
    (hgrad_factor : ∀ j,
      0 ≤ (∫ x : Torus, euclideanVecNorm (modeGrad j x) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) ∧
      (∫ x : Torus, euclideanVecNorm (modeGrad j x) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) ≤ G)
    (hmode_factor : ∀ i,
      0 ≤ (∫ x : Torus, ‖mode i x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) ∧
      (∫ x : Torus, ‖mode i x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) ≤ U)
    (hdiffusion_bound : ∀ i j,
      |∫ x : Torus, vecDot (modeGrad j x) (modeGrad i x)| ≤ D) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i j,
      |weakFormMatrixEntry
        (fun s x => AVenhance.Infra.Torus.periodicToTorus (b s) x)
        κ mode modeGrad t i j| ≤ K := by
  obtain ⟨C, hC⟩ := hb_bdd
  have hC_nonneg : 0 ≤ C := by
    have h := hC (1 / 2) (by norm_num) 0
    exact (norm_nonneg _).trans h
  let B : ℝ := Real.sqrt 2 * C
  have hB : 0 ≤ B := mul_nonneg (Real.sqrt_nonneg _) hC_nonneg
  have hdot : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x v,
      |Homogenization.vecDot (b t x) v| ≤ B * euclideanVecNorm v := by
    intro t ht x v
    exact vecDot_le_of_supNorm_le hC_nonneg (hC t ht x)
  refine ⟨B * G * U + |κ| * D,
    add_nonneg (mul_nonneg (mul_nonneg hB hG) hU)
      (mul_nonneg (abs_nonneg _) hD), ?_⟩
  intro t ht i j
  let driftIntegrand : Torus → ℝ := fun x =>
    vecDot (AVenhance.Infra.Torus.periodicToTorus (b t) x) (modeGrad j x) * mode i x
  have hpoint : ∀ᵐ x ∂(volume : Measure Torus),
      |driftIntegrand x| ≤ B * (|euclideanVecNorm (modeGrad j x)| * |mode i x|) := by
    filter_upwards with x
    dsimp [driftIntegrand]
    have hdot' := hdot t ht (AVenhance.Infra.Torus.unitTorusRepresentative 2 x)
      (modeGrad j x)
    have heq : AVenhance.Infra.Torus.periodicToTorus (b t) x =
        b t (AVenhance.Infra.Torus.unitTorusRepresentative 2 x) := rfl
    rw [heq]
    calc
      |Homogenization.vecDot (b t (AVenhance.Infra.Torus.unitTorusRepresentative 2 x))
          (modeGrad j x) * mode i x| =
          |Homogenization.vecDot (b t (AVenhance.Infra.Torus.unitTorusRepresentative 2 x))
            (modeGrad j x)| * |mode i x| := abs_mul _ _
      _ ≤ (B * euclideanVecNorm (modeGrad j x)) * |mode i x| :=
        mul_le_mul_of_nonneg_right hdot' (abs_nonneg _)
      _ = B * (|euclideanVecNorm (modeGrad j x)| * |mode i x|) := by
        rw [abs_of_nonneg (euclideanVecNorm_nonneg _)]
        ring
  have hdrift := driftIntegral_bound_of_L2_or_not driftIntegrand
    (fun x => euclideanVecNorm (modeGrad j x)) (mode i) B hB hpoint
    (hgrad_memLp j) (hmode_memLp i)
  have hdriftFactor :
      B * (∫ x : Torus, ‖euclideanVecNorm (modeGrad j x)‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) *
        (∫ x : Torus, ‖mode i x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) ≤ B * G * U := by
    have hfirst := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hgrad_factor j).2 hB) (hmode_factor i).1
    have hsecond := mul_le_mul_of_nonneg_left (hmode_factor i).2 (mul_nonneg hB hG)
    simpa [Real.norm_eq_abs, abs_of_nonneg (euclideanVecNorm_nonneg _)] using
      hfirst.trans hsecond
  have hdriftAbs : |∫ x : Torus, driftIntegrand x| ≤ B * G * U := by
    have hbase : |∫ x : Torus, driftIntegrand x| ≤
        B * (∫ x : Torus, ‖euclideanVecNorm (modeGrad j x)‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) *
          (∫ x : Torus, ‖mode i x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
      simpa [abs_of_nonneg (euclideanVecNorm_nonneg _)] using hdrift
    exact hbase.trans hdriftFactor
  let diffusionIntegral : ℝ := ∫ x : Torus, vecDot (modeGrad j x) (modeGrad i x)
  have hentryEq : weakFormMatrixEntry
      (fun s x => AVenhance.Infra.Torus.periodicToTorus (b s) x)
      κ mode modeGrad t i j =
      -(∫ x : Torus, driftIntegrand x) - κ * diffusionIntegral := by
    simp [weakFormMatrixEntry, driftIntegrand, diffusionIntegral]
  have hentryAdd : weakFormMatrixEntry
      (fun s x => AVenhance.Infra.Torus.periodicToTorus (b s) x)
      κ mode modeGrad t i j =
      -(∫ x : Torus, driftIntegrand x) + (-(κ * diffusionIntegral)) := by
    rw [hentryEq]
    ring
  calc
    |weakFormMatrixEntry
      (fun s x => AVenhance.Infra.Torus.periodicToTorus (b s) x)
      κ mode modeGrad t i j| ≤
        |∫ x : Torus, driftIntegrand x| + |κ| * |diffusionIntegral| := by
          rw [hentryAdd]
          simpa [abs_neg, abs_mul] using
            (abs_add_le (-(∫ x : Torus, driftIntegrand x)) (-(κ * diffusionIntegral)))
    _ ≤ B * G * U + |κ| * D := by
      exact add_le_add hdriftAbs
        (mul_le_mul_of_nonneg_left (hdiffusion_bound i j) (abs_nonneg κ))

end AVenhance.Infra.Parabolic.FourierGalerkin

end
