/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.WeakUniqueness.WeakProjectionConvergence
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.WeakUniqueness.FiniteGalerkinEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.FrozenDrift
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinModeCalculus

/-!
# Strong spacetime cutoff convergence for weak solutions

This file turns the slice-wise Fourier cutoff estimates into the spacetime `L²` convergence
needed to pass pairings in the finite weak energy identity.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Homogenization
open AVenhance.Infra.Classical
open scoped Topology

namespace AVenhance.Infra.Parabolic.WeakUniqueness

open AVenhance.Infra.Parabolic.FourierGalerkin

theorem WeakEnergyPassage.weakEnergy_timeCube_measurable : MeasurableSet AVenhance.timeCube := by
  rw [AVenhance.timeCube]
  refine measurableSet_Ioo.prod ?_
  unfold AVenhance.unitCube
  exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioo)

theorem WeakEnergyPassage.weakEnergy_unitCube_volume_lt_top :
    volume AVenhance.unitCube < ⊤ := by
  unfold AVenhance.unitCube
  rw [volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]

local instance weakEnergy_finite_unitCube :
    IsFiniteMeasure (volume.restrict AVenhance.unitCube) := by
  refine ⟨?_⟩
  simpa only [Measure.restrict_apply_univ] using WeakEnergyPassage.weakEnergy_unitCube_volume_lt_top

theorem WeakEnergyPassage.weakEnergy_Ioo_volume_lt_top :
    volume (Set.Ioo (0 : ℝ) 1) < ⊤ := by
  rw [Real.volume_Ioo]
  norm_num

local instance weakEnergy_finite_Ioo :
    IsFiniteMeasure (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
  refine ⟨?_⟩
  simpa only [Measure.restrict_apply_univ] using WeakEnergyPassage.weakEnergy_Ioo_volume_lt_top

theorem weakEnergy_timeCube_measure_eq_product :
    (volume.restrict AVenhance.timeCube) =
      (volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
        (volume.restrict AVenhance.unitCube) := by
  rw [AVenhance.timeCube, Measure.prod_restrict,
    ← Measure.volume_eq_prod ℝ (Vec 2)]

local instance weakEnergy_finite_timeCube :
    IsFiniteMeasure (volume.restrict AVenhance.timeCube) := by
  rw [weakEnergy_timeCube_measure_eq_product]
  infer_instance

/-- Open time interval times the spatial unit cube for the weak energy integral. -/
def weakEnergyRegion (t : ℝ) : Set (ℝ × Vec 2) :=
  Set.Ioo (0 : ℝ) t ×ˢ AVenhance.unitCube

theorem WeakEnergyPassage.weakEnergy_region_measurable (t : ℝ) :
    MeasurableSet (weakEnergyRegion t) := by
  exact measurableSet_Ioo.prod (by
    unfold AVenhance.unitCube
    exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioo))

theorem weakEnergy_region_subset_timeCube {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    weakEnergyRegion t ⊆ AVenhance.timeCube := by
  intro p hp
  rcases hp with ⟨⟨h0, ht'⟩, hx⟩
  refine ⟨⟨h0, lt_of_lt_of_le ht' ht.2⟩, hx⟩

theorem weakEnergy_region_measure_eq_product (t : ℝ) :
    (volume.restrict (weakEnergyRegion t)) =
      (volume.restrict (Set.Ioo (0 : ℝ) t)).prod
        (volume.restrict AVenhance.unitCube) := by
  rw [weakEnergyRegion, Measure.prod_restrict,
    ← Measure.volume_eq_prod ℝ (Vec 2)]

theorem WeakEnergyPassage.weakEnergy_region_weighted_integrable
    {F : ℝ × Vec 2 → ℝ} (hF : Integrable F
      (volume.restrict AVenhance.timeCube))
    {c : ℝ → ℝ} (hc : Continuous c) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Integrable (fun p => F p * c p.1)
      (volume.restrict (weakEnergyRegion t)) := by
  have hregionF : Integrable F (volume.restrict (weakEnergyRegion t)) :=
    hF.mono_measure (Measure.restrict_mono (weakEnergy_region_subset_timeCube ht) le_rfl)
  have hweight : Continuous (fun p : ℝ × Vec 2 => c p.1) := hc.comp continuous_fst
  obtain ⟨C, _hC, hbound⟩ := weak_continuous_timeCube_bound hweight
  have hboundRegion : ∀ᵐ p ∂(volume.restrict (weakEnergyRegion t)),
      ‖c p.1‖ ≤ C := by
    filter_upwards [ae_restrict_mem (WeakEnergyPassage.weakEnergy_region_measurable t)] with p hp
    exact hbound p (weakEnergy_region_subset_timeCube ht hp)
  exact hregionF.mul_bdd hweight.measurable.aestronglyMeasurable hboundRegion

theorem WeakEnergyPassage.weakEnergy_region_weighted_fubini
    {F : ℝ × Vec 2 → ℝ} (hF : Integrable F
      (volume.restrict AVenhance.timeCube))
    {c : ℝ → ℝ} (hc : Continuous c) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∫ p in weakEnergyRegion t, F p * c p.1 =
      ∫ s in Set.Ioo (0 : ℝ) t,
        c s * ∫ x in AVenhance.unitCube, F (s, x) := by
  have hweighted := WeakEnergyPassage.weakEnergy_region_weighted_integrable hF hc ht
  have hweightedProd : Integrable (fun p => F p * c p.1)
      ((volume.restrict (Set.Ioo (0 : ℝ) t)).prod
        (volume.restrict AVenhance.unitCube)) := by
    rwa [← weakEnergy_region_measure_eq_product]
  have hprod := integral_prod (fun p : ℝ × Vec 2 => F p * c p.1) hweightedProd
  calc
    ∫ p in weakEnergyRegion t, F p * c p.1 =
        ∫ p, F p * c p.1
          ∂((volume.restrict (Set.Ioo (0 : ℝ) t)).prod
            (volume.restrict AVenhance.unitCube)) := by
              rw [← weakEnergy_region_measure_eq_product]
    _ =
        ∫ s, ∫ x, F (s, x) * c s
          ∂(volume.restrict AVenhance.unitCube)
          ∂(volume.restrict (Set.Ioo (0 : ℝ) t)) := hprod
    _ = ∫ s in Set.Ioo (0 : ℝ) t,
        c s * ∫ x in AVenhance.unitCube, F (s, x) := by
      apply integral_congr_ae
      filter_upwards with s
      rw [show (fun x : Vec 2 => F (s, x) * c s) =
          fun x => c s * F (s, x) by funext x; ring]
      rw [integral_const_mul]
    _ = ∫ s in Set.Ioo (0 : ℝ) t,
        c s * ∫ x in AVenhance.unitCube, F (s, x) := rfl

theorem weakEnergy_Ioo_intervalIntegral {F : ℝ → ℝ} {t : ℝ}
    (ht : 0 ≤ t) :
    (∫ s in Set.Ioo (0 : ℝ) t, F s) = ∫ s in (0 : ℝ)..t, F s := by
  have hmeas : volume.restrict (Set.Ioo (0 : ℝ) t) =
      volume.restrict (Set.Ioc (0 : ℝ) t) :=
    Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Ioc)
  calc
    ∫ s in Set.Ioo (0 : ℝ) t, F s =
        ∫ s, F s ∂(volume.restrict (Set.Ioo (0 : ℝ) t)) := rfl
    _ = ∫ s, F s ∂(volume.restrict (Set.Ioc (0 : ℝ) t)) := by rw [hmeas]
    _ = ∫ s in Set.Ioc (0 : ℝ) t, F s := rfl
    _ = ∫ s in (0 : ℝ)..t, F s := by
      rw [intervalIntegral.integral_of_le ht]

/-- Fubini on the truncated space-time cell, with the time variable written as an interval
integral from the initial time. -/
theorem weakEnergy_region_integral_eq_interval
    {F : ℝ × Vec 2 → ℝ}
    (hF : Integrable F (volume.restrict AVenhance.timeCube))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∫ p in weakEnergyRegion t, F p =
      ∫ s in (0 : ℝ)..t, ∫ x in AVenhance.unitCube, F (s, x) := by
  have hregion : Integrable F (volume.restrict (weakEnergyRegion t)) :=
    hF.mono_measure (Measure.restrict_mono (weakEnergy_region_subset_timeCube ht) le_rfl)
  have hproduct : Integrable F
      ((volume.restrict (Set.Ioo (0 : ℝ) t)).prod
        (volume.restrict AVenhance.unitCube)) := by
    rw [← weakEnergy_region_measure_eq_product]
    exact hregion
  calc
    ∫ p in weakEnergyRegion t, F p =
        ∫ s in Set.Ioo (0 : ℝ) t, ∫ x in AVenhance.unitCube, F (s, x) := by
          rw [weakEnergy_region_measure_eq_product, integral_prod F hproduct]
    _ = ∫ s in (0 : ℝ)..t, ∫ x in AVenhance.unitCube, F (s, x) :=
      weakEnergy_Ioo_intervalIntegral ht.1

theorem WeakEnergyPassage.weakEnergy_l2_pairing_bound {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ p, f p * g p ∂μ| ≤
      Real.sqrt (∫ p, f p ^ 2 ∂μ) * Real.sqrt (∫ p, g p ^ 2 ∂μ) := by
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (f := fun p => |f p|) (g := fun p => |g p|)
    (μ := μ) Real.HolderConjugate.two_two
    (ae_of_all _ fun p => abs_nonneg _)
    (ae_of_all _ fun p => abs_nonneg _)
    (by simpa [Real.norm_eq_abs] using hf.norm)
    (by simpa [Real.norm_eq_abs] using hg.norm)
  have hAbs : |∫ p, f p * g p ∂μ| ≤ ∫ p, |f p| * |g p| ∂μ := by
    simpa [Real.norm_eq_abs, abs_mul] using
      (norm_integral_le_integral_norm (fun p => f p * g p) (μ := μ))
  exact hAbs.trans (by
    simpa only [Real.rpow_two, sq_abs, Real.sqrt_eq_rpow, one_div] using hHolder)

theorem weakEnergy_pairing_error_tendsto_on_region
    {F : ℝ × Vec 2 → ℝ}
    (hF : MemLp F 2 (volume.restrict AVenhance.timeCube))
    (e : ℕ → ℝ × Vec 2 → ℝ)
    (he : ∀ N, MemLp (e N) 2 (volume.restrict AVenhance.timeCube))
    (henergy : Tendsto (fun N => ∫ p in AVenhance.timeCube, e N p ^ 2)
      atTop (𝓝 0))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun N => ∫ p in weakEnergyRegion t, F p * e N p)
      atTop (𝓝 0) := by
  let μR := volume.restrict (weakEnergyRegion t)
  let μC := volume.restrict AVenhance.timeCube
  have hμ : μR ≤ μC :=
    Measure.restrict_mono (weakEnergy_region_subset_timeCube ht) le_rfl
  have hFreg : MemLp F 2 μR := hF.mono_measure hμ
  have heReg (N : ℕ) : MemLp (e N) 2 μR := (he N).mono_measure hμ
  have hFsq : Integrable (fun p => F p ^ 2) μC :=
    (memLp_two_iff_integrable_sq hF.aestronglyMeasurable).1 hF
  have heSq (N : ℕ) : Integrable (fun p => e N p ^ 2) μC :=
    (memLp_two_iff_integrable_sq (he N).aestronglyMeasurable).1 (he N)
  have hFmono : ∫ p, F p ^ 2 ∂μR ≤ ∫ p, F p ^ 2 ∂μC :=
    integral_mono_measure hμ (ae_of_all _ fun p => sq_nonneg (F p)) hFsq
  have heMono (N : ℕ) : ∫ p, e N p ^ 2 ∂μR ≤ ∫ p, e N p ^ 2 ∂μC :=
    integral_mono_measure hμ (ae_of_all _ fun p => sq_nonneg (e N p)) (heSq N)
  have hroot := (Real.continuous_sqrt.tendsto 0).comp henergy
  have hupper : Tendsto (fun N =>
      Real.sqrt (∫ p in AVenhance.timeCube, F p ^ 2) *
        Real.sqrt (∫ p in AVenhance.timeCube, e N p ^ 2)) atTop (𝓝 0) := by
    simpa using hroot.const_mul (Real.sqrt (∫ p in AVenhance.timeCube, F p ^ 2))
  have habs : Tendsto (fun N =>
      |∫ p in weakEnergyRegion t, F p * e N p|) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _)
      (Filter.Eventually.of_forall ?_) hupper
    intro N
    have hpair := WeakEnergyPassage.weakEnergy_l2_pairing_bound (μ := μR) hFreg (heReg N)
    have hFsqrt := Real.sqrt_le_sqrt hFmono
    have heSqrt := Real.sqrt_le_sqrt (heMono N)
    have hFnonneg : 0 ≤ Real.sqrt (∫ p, F p ^ 2 ∂μC) := Real.sqrt_nonneg _
    calc
      |∫ p in weakEnergyRegion t, F p * e N p| ≤
          Real.sqrt (∫ p, F p ^ 2 ∂μR) * Real.sqrt (∫ p, e N p ^ 2 ∂μR) := hpair
      _ ≤ Real.sqrt (∫ p, F p ^ 2 ∂μC) * Real.sqrt (∫ p, e N p ^ 2 ∂μC) := by
        exact mul_le_mul hFsqrt heSqrt (Real.sqrt_nonneg _) hFnonneg
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [Real.norm_eq_abs] using habs

theorem weakEnergy_drift_memLp_two
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {f : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ} {D : ℝ → Vec 2 → Vec 2}
    (hu : AVenhance.IsWeakSolutionGrad b κ f u D)
    (hb_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (hb_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ C) :
    MemLp (fun p : ℝ × Vec 2 => Homogenization.vecDot (b p.1 p.2) (D p.1 p.2))
      2 (volume.restrict AVenhance.timeCube) := by
  obtain ⟨C, hC⟩ := hb_bdd
  have hsub : AVenhance.timeCube ⊆ Set.Icc (0 : ℝ) 1 ×ˢ Set.univ := by
    intro p hp
    refine ⟨⟨le_of_lt hp.1.1, le_of_lt hp.1.2⟩, Set.mem_univ _⟩
  have hb := hb_meas.mono_set hsub
  have hcoordMeas (i : Fin 2) : AEStronglyMeasurable
      (fun p : ℝ × Vec 2 => b p.1 p.2 i)
      (volume.restrict AVenhance.timeCube) := by
    exact (continuous_apply i).comp_aestronglyMeasurable hb
  have hcoordMem (i : Fin 2) : MemLp
      (fun p : ℝ × Vec 2 => b p.1 p.2 i) ⊤
      (volume.restrict AVenhance.timeCube) := by
    apply MemLp.of_bound (hcoordMeas i) C
    filter_upwards [ae_restrict_mem WeakEnergyPassage.weakEnergy_timeCube_measurable] with p hp
    have hbound := hC p.1 ⟨le_of_lt hp.1.1, le_of_lt hp.1.2⟩ p.2
    have hi := (pi_norm_le_iff_of_nonempty (b p.1 p.2)).1 hbound i
    simpa [Real.norm_eq_abs] using hi
  have hterm (i : Fin 2) : MemLp
      (fun p : ℝ × Vec 2 => b p.1 p.2 i * D p.1 p.2 i) 2
      (volume.restrict AVenhance.timeCube) := by
    exact (hcoordMem i).mul (hu.2.2.2.1 i)
  have hsum := (hterm 0).add (hterm 1)
  have heq : (fun p : ℝ × Vec 2 => Homogenization.vecDot
      (b p.1 p.2) (D p.1 p.2)) =
      fun p => b p.1 p.2 0 * D p.1 p.2 0 + b p.1 p.2 1 * D p.1 p.2 1 := by
    funext p
    simp [Homogenization.vecDot, Fin.sum_univ_succ]
  rw [heq]
  exact hsum

/-- Clamp an energy observation time to the closed unit interval. -/
def WeakEnergyPassage.weakEnergyClamp (t : ℝ) : ℝ := max 0 (min t 1)

theorem WeakEnergyPassage.weakEnergyClamp_mem (t : ℝ) :
    WeakEnergyPassage.weakEnergyClamp t ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_right _ _)

theorem WeakEnergyPassage.weakEnergyClamp_eq {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    WeakEnergyPassage.weakEnergyClamp t = t := by
  simp [WeakEnergyPassage.weakEnergyClamp, max_eq_right ht.1, min_eq_left ht.2]

theorem WeakEnergyPassage.weakEnergyClamp_continuous : Continuous
    WeakEnergyPassage.weakEnergyClamp := by
  exact continuous_const.max (continuous_id.min continuous_const)

/-- Extend the weak solution's pairing with one real Fourier mode to all times. -/
def WeakEnergyPassage.weakEnergyCoefficientExtension (N : ℕ) (u : ℝ → Vec 2 → ℝ)
    (i : Fin (RealFourierDimension N)) (t : ℝ) : ℝ :=
  weakModePairing u
    (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i))
    (WeakEnergyPassage.weakEnergyClamp t)

theorem WeakEnergyPassage.weakEnergyCoefficientExtension_continuous
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {f : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ} {D : ℝ → Vec 2 → Vec 2}
    (hu : AVenhance.IsWeakSolutionGrad b κ f u D) (N : ℕ)
    (i : Fin (RealFourierDimension N)) :
    Continuous (WeakEnergyPassage.weakEnergyCoefficientExtension N u i) := by
  unfold WeakEnergyPassage.weakEnergyCoefficientExtension
  have hpair := hu.2.2.2.2.2.2.1
    (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i))
    ((realFourierModeAmbient_contDiff N
      ((realFourierIndexEquivFin N).symm i)).of_le le_top)
    (realFourierModeAmbient_periodic N
      ((realFourierIndexEquivFin N).symm i))
  exact hpair.comp_continuous WeakEnergyPassage.weakEnergyClamp_continuous
      WeakEnergyPassage.weakEnergyClamp_mem

theorem WeakEnergyPassage.weakEnergyCoefficientExtension_eq
    (N : ℕ) (u : ℝ → Vec 2 → ℝ) (i : Fin (RealFourierDimension N))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    WeakEnergyPassage.weakEnergyCoefficientExtension N u i t =
      weakModePairing u
        (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)) t := by
  simp [WeakEnergyPassage.weakEnergyCoefficientExtension, WeakEnergyPassage.weakEnergyClamp_eq ht]

/-- Integrand for the forcing of a Fourier-mode pairing in the weak energy equation. -/
def WeakEnergyPassage.weakEnergyModeForcingIntegrand
    (b : ℝ → Vec 2 → Vec 2) (κ : ℝ) (D : ℝ → Vec 2 → Vec 2)
    (N : ℕ) (i : Fin (RealFourierDimension N)) (p : ℝ × Vec 2) : ℝ :=
  Homogenization.vecDot (b p.1 p.2) (D p.1 p.2) *
      realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i) p.2 +
    κ * Homogenization.vecDot (D p.1 p.2)
      (AVenhance.spaceGrad
        (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)) p.2)

theorem WeakEnergyPassage.weakEnergyModeForcingIntegrand_integrable
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {f : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ} {D : ℝ → Vec 2 → Vec 2}
    (hu : AVenhance.IsWeakSolutionGrad b κ f u D) (N : ℕ)
    (i : Fin (RealFourierDimension N)) :
    Integrable (WeakEnergyPassage.weakEnergyModeForcingIntegrand b κ D N i)
      (volume.restrict AVenhance.timeCube) := by
  let ψ := realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)
  have hψ : Continuous (fun p : ℝ × Vec 2 => ψ p.2) :=
    (realFourierModeAmbient_contDiff N
      ((realFourierIndexEquivFin N).symm i)).continuous.comp continuous_snd
  have hgrad (j : Fin 2) : Continuous (fun p : ℝ × Vec 2 =>
      AVenhance.spaceGrad ψ p.2 j) := by
    have hmode := (realFourierModeAmbient_contDiff N
      ((realFourierIndexEquivFin N).symm i)).continuous
    have hgradx : Continuous (fun x : Vec 2 => AVenhance.spaceGrad ψ x j) := by
      rw [show (fun x => AVenhance.spaceGrad ψ x j) =
          fun x => realFourierModeDerivativeScale
            ((realFourierIndexEquivFin N).symm i) j *
            realFourierModeAmbient N
              (realFourierModeIndexSwap ((realFourierIndexEquivFin N).symm i)) x by
        funext x
        rw [spaceGrad_realFourierModeAmbient]
        cases (realFourierIndexEquivFin N).symm i with
        | none => simp [realFourierModeDerivativeScale]
        | some q =>
          cases q with
          | mk p hs =>
            cases hs <;> simp [realFourierModeDerivativeScale]]
      exact continuous_const.mul
        (realFourierModeAmbient_contDiff N
          (realFourierModeIndexSwap ((realFourierIndexEquivFin N).symm i))).continuous
    exact hgradx.comp continuous_snd
  obtain ⟨Cψ, _hCψ, hψbound⟩ := weak_continuous_timeCube_bound hψ
  have hdrift := hu.2.2.2.2.2.1
  have hfirst : Integrable
      (fun p : ℝ × Vec 2 =>
        Homogenization.vecDot (b p.1 p.2) (D p.1 p.2) * ψ p.2)
      (volume.restrict AVenhance.timeCube) :=
    hdrift.mul_bdd hψ.measurable.aestronglyMeasurable (by
      filter_upwards [ae_restrict_mem WeakEnergyPassage.weakEnergy_timeCube_measurable] with p hp
      simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hψbound p hp)
  have hsecond (j : Fin 2) : Integrable
      (fun p : ℝ × Vec 2 => D p.1 p.2 j * AVenhance.spaceGrad ψ p.2 j)
      (volume.restrict AVenhance.timeCube) := by
    have hDj := (hu.2.2.2.1 j).integrable (by norm_num)
    obtain ⟨Cj, _hCj, hbound⟩ := weak_continuous_timeCube_bound (hgrad j)
    exact hDj.mul_bdd (hgrad j).measurable.aestronglyMeasurable (by
      filter_upwards [ae_restrict_mem WeakEnergyPassage.weakEnergy_timeCube_measurable] with p hp
      exact hbound p hp)
  have hsum : Integrable
      (fun p : ℝ × Vec 2 =>
        ∑ j : Fin 2, D p.1 p.2 j * AVenhance.spaceGrad ψ p.2 j)
      (volume.restrict AVenhance.timeCube) :=
    integrable_finsetSum Finset.univ (fun j hj => hsecond j)
  have hsecond' : Integrable
      (fun p : ℝ × Vec 2 => κ *
        Homogenization.vecDot (D p.1 p.2) (AVenhance.spaceGrad ψ p.2))
      (volume.restrict AVenhance.timeCube) := by
    have heq : (fun p : ℝ × Vec 2 => κ *
        Homogenization.vecDot (D p.1 p.2) (AVenhance.spaceGrad ψ p.2)) =
        fun p => κ * ∑ j : Fin 2,
          D p.1 p.2 j * AVenhance.spaceGrad ψ p.2 j := by
      funext p
      simp [Homogenization.vecDot]
    rw [heq]
    exact hsum.const_mul κ
  have hsum' := hfirst.add hsecond'
  have heq : WeakEnergyPassage.weakEnergyModeForcingIntegrand b κ D N i =
      fun p => Homogenization.vecDot (b p.1 p.2) (D p.1 p.2) * ψ p.2 +
        κ * Homogenization.vecDot (D p.1 p.2) (AVenhance.spaceGrad ψ p.2) := by
    funext p
    rfl
  rw [heq]
  exact hsum'

theorem WeakEnergyPassage.weakEnergyProjectionExpansion
    (N : ℕ) (u : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) :
    weakFourierModeProjection N u t x =
      ∑ i : Fin (RealFourierDimension N),
        weakModePairing u
          (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)) t *
          realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i) x := by
  simp [weakFourierModeProjection, realFourierModeAmbientExpansion,
    weakFourierCoefficientPath]

theorem WeakEnergyPassage.weakEnergyProjectionGradientExpansion
    (N : ℕ) (u : ℝ → Vec 2 → ℝ) (t : ℝ) (j : Fin 2) (x : Vec 2) :
    AVenhance.spaceGrad (weakFourierModeProjection N u t) x j =
      ∑ i : Fin (RealFourierDimension N),
        weakModePairing u
          (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)) t *
          AVenhance.spaceGrad
            (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)) x j := by
  rw [weakFourierModeProjection, spaceGrad_realFourierModeAmbientExpansion]
  change
    (∑ i : Fin (RealFourierDimension N),
      weakModePairing u
        (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)) t *
        realFourierModeDerivativeScale
          ((realFourierIndexEquivFin N).symm i) j *
        realFourierModeAmbient N
          (realFourierModeIndexSwap ((realFourierIndexEquivFin N).symm i)) x) =
    ∑ i : Fin (RealFourierDimension N),
      weakModePairing u
        (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)) t *
        AVenhance.spaceGrad
          (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)) x j
  apply Finset.sum_congr rfl
  intro i hi
  rw [spaceGrad_realFourierModeAmbient]
  cases (realFourierIndexEquivFin N).symm i with
  | none => simp [realFourierModeDerivativeScale]
  | some q =>
    cases q with
    | mk p hs =>
      cases hs <;> simp [realFourierModeDerivativeScale] <;> ring

theorem WeakEnergyPassage.weakEnergy_modeForcingSum_eq
    (b : ℝ → Vec 2 → Vec 2) (κ : ℝ) (D : ℝ → Vec 2 → Vec 2)
    (u : ℝ → Vec 2 → ℝ) (N : ℕ) (t : ℝ) (x : Vec 2) :
    ∑ i : Fin (RealFourierDimension N),
        weakModePairing u
          (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)) t *
          WeakEnergyPassage.weakEnergyModeForcingIntegrand b κ D N i (t, x) =
      Homogenization.vecDot (b t x) (D t x) * weakFourierModeProjection N u t x +
        κ * Homogenization.vecDot (D t x)
          (AVenhance.spaceGrad (weakFourierModeProjection N u t) x) := by
  rw [WeakEnergyPassage.weakEnergyProjectionExpansion]
  unfold WeakEnergyPassage.weakEnergyModeForcingIntegrand
  rw [show (∑ i : Fin (RealFourierDimension N),
        weakModePairing u
          (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)) t *
          (Homogenization.vecDot (b t x) (D t x) *
              realFourierModeAmbient N
                ((realFourierIndexEquivFin N).symm i) x +
            κ * Homogenization.vecDot (D t x)
              (AVenhance.spaceGrad
                (realFourierModeAmbient N
                  ((realFourierIndexEquivFin N).symm i)) x))) =
      (∑ i : Fin (RealFourierDimension N),
        weakModePairing u
          (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)) t *
          (Homogenization.vecDot (b t x) (D t x) *
            realFourierModeAmbient N
              ((realFourierIndexEquivFin N).symm i) x)) +
      κ * ∑ i : Fin (RealFourierDimension N),
        weakModePairing u
          (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)) t *
          Homogenization.vecDot (D t x)
            (AVenhance.spaceGrad
              (realFourierModeAmbient N
                ((realFourierIndexEquivFin N).symm i)) x) by
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    apply congrArg₂ (fun a b : ℝ => a + b)
    · rfl
    · calc
        (∑ i : Fin (RealFourierDimension N),
            weakModePairing u
              (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)) t *
            (κ * Homogenization.vecDot (D t x)
              (AVenhance.spaceGrad
                (realFourierModeAmbient N
                  ((realFourierIndexEquivFin N).symm i)) x))) =
            ∑ i : Fin (RealFourierDimension N), κ *
              (weakModePairing u
                (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)) t *
                Homogenization.vecDot (D t x)
                  (AVenhance.spaceGrad
                    (realFourierModeAmbient N
                      ((realFourierIndexEquivFin N).symm i)) x)) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = κ * ∑ i : Fin (RealFourierDimension N),
            weakModePairing u
              (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)) t *
            Homogenization.vecDot (D t x)
              (AVenhance.spaceGrad
                (realFourierModeAmbient N
                  ((realFourierIndexEquivFin N).symm i)) x) := by
          rw [Finset.mul_sum]]
  have hscalar :
      (∑ i : Fin (RealFourierDimension N),
        weakModePairing u
          (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)) t *
          (Homogenization.vecDot (b t x) (D t x) *
            realFourierModeAmbient N
              ((realFourierIndexEquivFin N).symm i) x)) =
      Homogenization.vecDot (b t x) (D t x) * weakFourierModeProjection N u t x := by
    rw [WeakEnergyPassage.weakEnergyProjectionExpansion]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hdot : Homogenization.vecDot (D t x)
      (AVenhance.spaceGrad (weakFourierModeProjection N u t) x) =
      ∑ i : Fin (RealFourierDimension N),
        weakModePairing u
          (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)) t *
          Homogenization.vecDot (D t x)
            (AVenhance.spaceGrad
              (realFourierModeAmbient N
                ((realFourierIndexEquivFin N).symm i)) x) := by
    have hgradVec : AVenhance.spaceGrad (weakFourierModeProjection N u t) x =
        fun j : Fin 2 =>
          ∑ i : Fin (RealFourierDimension N),
            weakModePairing u
              (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)) t *
              AVenhance.spaceGrad
                (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)) x j := by
      funext j
      exact WeakEnergyPassage.weakEnergyProjectionGradientExpansion N u t j x
    simp only [Homogenization.vecDot]
    rw [hgradVec]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hscalar, hdot]
  simp only [WeakEnergyPassage.weakEnergyProjectionExpansion]

theorem WeakEnergyPassage.weakEnergy_singleMode_integral
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {f : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ} {D : ℝ → Vec 2 → Vec 2}
    (hu : AVenhance.IsWeakSolutionGrad b κ f u D)
    (N : ℕ) (i : Fin (RealFourierDimension N)) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∫ s in (0 : ℝ)..t,
      weakModePairing u
        (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)) s *
      weakModeForcing b κ D
        (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)) s =
    ∫ p in weakEnergyRegion t,
      WeakEnergyPassage.weakEnergyModeForcingIntegrand b κ D N i p *
        WeakEnergyPassage.weakEnergyCoefficientExtension N u i p.1 := by
  let ψ := realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)
  have hψsmooth : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    (realFourierModeAmbient_contDiff N
      ((realFourierIndexEquivFin N).symm i)).of_le le_top
  have hq01 : IntervalIntegrable (weakModeForcing b κ D ψ) volume 0 1 :=
    weak_solution_mode_forcing_intervalIntegrable hu hψsmooth
  have hqT : IntervalIntegrable (weakModeForcing b κ D ψ) volume 0 t := by
    have hsubset : uIcc (0 : ℝ) t ⊆ uIcc 0 1 := by
      rw [uIcc_of_le ht.1, uIcc_of_le (by norm_num)]
      intro s hs
      exact ⟨hs.1, hs.2.trans ht.2⟩
    exact hq01.mono_set hsubset
  have hF := WeakEnergyPassage.weakEnergyModeForcingIntegrand_integrable hu N i
  have hc := WeakEnergyPassage.weakEnergyCoefficientExtension_continuous hu N i
  have hFub := WeakEnergyPassage.weakEnergy_region_weighted_fubini hF hc ht
  have hqDef (s : ℝ) :
      weakModeForcing b κ D ψ s =
        ∫ x in AVenhance.unitCube,
          WeakEnergyPassage.weakEnergyModeForcingIntegrand b κ D N i (s, x) := by
    rfl
  have htime :
      ∫ s in Set.Ioo (0 : ℝ) t,
        weakModePairing u ψ s * weakModeForcing b κ D ψ s =
      ∫ s in Set.Ioo (0 : ℝ) t,
        WeakEnergyPassage.weakEnergyCoefficientExtension N u i s *
          ∫ x in AVenhance.unitCube,
            WeakEnergyPassage.weakEnergyModeForcingIntegrand b κ D N i (s, x) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (measurableSet_Ioo)] with s hs
    have hscc : s ∈ Set.Icc (0 : ℝ) 1 := by
      refine ⟨le_of_lt hs.1, ?_⟩
      exact (lt_of_lt_of_le hs.2 ht.2).le
    rw [WeakEnergyPassage.weakEnergyCoefficientExtension_eq N u i hscc, hqDef]
  calc
    ∫ s in (0 : ℝ)..t,
        weakModePairing u ψ s * weakModeForcing b κ D ψ s =
      ∫ s in Set.Ioo (0 : ℝ) t,
        weakModePairing u ψ s * weakModeForcing b κ D ψ s :=
      (weakEnergy_Ioo_intervalIntegral ht.1).symm
    _ = ∫ s in Set.Ioo (0 : ℝ) t,
          WeakEnergyPassage.weakEnergyCoefficientExtension N u i s *
            ∫ x in AVenhance.unitCube,
              WeakEnergyPassage.weakEnergyModeForcingIntegrand b κ D N i (s, x) := htime
    _ = ∫ p in weakEnergyRegion t,
          WeakEnergyPassage.weakEnergyModeForcingIntegrand b κ D N i p *
            WeakEnergyPassage.weakEnergyCoefficientExtension N u i p.1 := hFub.symm

theorem weakEnergy_finiteProjection_pairing_integral
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {f : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ} {D : ℝ → Vec 2 → Vec 2}
    (hu : AVenhance.IsWeakSolutionGrad b κ f u D)
    (N : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∫ s in (0 : ℝ)..t,
      2 * ∑ i : Fin (RealFourierDimension N),
        weakModePairing u
            (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)) s *
          weakModeForcing b κ D
            (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)) s =
    ∫ p in weakEnergyRegion t,
      2 * (Homogenization.vecDot (b p.1 p.2) (D p.1 p.2) *
          weakFourierModeProjection N u p.1 p.2 +
        κ * Homogenization.vecDot (D p.1 p.2)
          (AVenhance.spaceGrad (weakFourierModeProjection N u p.1) p.2)) := by
  classical
  let c : Fin (RealFourierDimension N) → ℝ → ℝ :=
    fun i s => WeakEnergyPassage.weakEnergyCoefficientExtension N u i s
  let q : Fin (RealFourierDimension N) → ℝ → ℝ := fun i s =>
    weakModeForcing b κ D
      (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)) s
  have hc (i : Fin (RealFourierDimension N)) : Continuous (c i) :=
    WeakEnergyPassage.weakEnergyCoefficientExtension_continuous hu N i
  have hq (i : Fin (RealFourierDimension N)) :
      IntervalIntegrable (q i) volume 0 t := by
    let ψ := realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)
    have hq01 : IntervalIntegrable (weakModeForcing b κ D ψ) volume 0 1 :=
      weak_solution_mode_forcing_intervalIntegrable hu
        ((realFourierModeAmbient_contDiff N
          ((realFourierIndexEquivFin N).symm i)).of_le le_top)
    have hsubset : uIcc (0 : ℝ) t ⊆ uIcc 0 1 := by
      rw [uIcc_of_le ht.1, uIcc_of_le (by norm_num)]
      intro s hs
      exact ⟨hs.1, hs.2.trans ht.2⟩
    exact hq01.mono_set hsubset
  have hprod (i : Fin (RealFourierDimension N)) :
      IntervalIntegrable (fun s => c i s * q i s) volume 0 t := by
    have hbase := (hq i).mul_continuousOn (hc i).continuousOn
    convert hbase using 1
    funext s
    ring
  have hsumInterval :
      ∫ s in (0 : ℝ)..t, 2 * ∑ i : Fin (RealFourierDimension N),
          c i s * q i s =
        2 * ∑ i : Fin (RealFourierDimension N),
          ∫ s in (0 : ℝ)..t, c i s * q i s := by
    calc
      ∫ s in (0 : ℝ)..t, 2 * ∑ i : Fin (RealFourierDimension N),
          c i s * q i s =
        2 * ∫ s in (0 : ℝ)..t, ∑ i : Fin (RealFourierDimension N),
          c i s * q i s := by rw [intervalIntegral.integral_const_mul]
      _ = 2 * ∑ i : Fin (RealFourierDimension N),
          ∫ s in (0 : ℝ)..t, c i s * q i s := by
        rw [intervalIntegral.integral_finsetSum (fun i hi => hprod i)]
  have hcoeffIcc (i : Fin (RealFourierDimension N)) {s : ℝ}
      (hs : s ∈ Set.Icc (0 : ℝ) 1) :
      c i s = weakModePairing u
        (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)) s := by
    exact WeakEnergyPassage.weakEnergyCoefficientExtension_eq N u i hs
  have hsumIntervalOriginal :
      ∫ s in (0 : ℝ)..t, 2 * ∑ i : Fin (RealFourierDimension N),
          weakModePairing u
              (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)) s *
            q i s =
        2 * ∑ i : Fin (RealFourierDimension N),
          ∫ s in (0 : ℝ)..t, c i s * q i s := by
    calc
      ∫ s in (0 : ℝ)..t, 2 * ∑ i : Fin (RealFourierDimension N),
          weakModePairing u
              (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)) s *
            q i s =
        ∫ s in (0 : ℝ)..t, 2 * ∑ i : Fin (RealFourierDimension N),
          c i s * q i s := by
            apply intervalIntegral.integral_congr
            intro s hs
            apply congrArg (fun z : ℝ => (2 : ℝ) * z)
            apply Finset.sum_congr rfl
            intro i hi
            have hs01 : s ∈ Set.Icc (0 : ℝ) 1 := by
              rw [uIcc_of_le ht.1] at hs
              exact ⟨hs.1, hs.2.trans ht.2⟩
            rw [hcoeffIcc i hs01]
      _ = 2 * ∑ i : Fin (RealFourierDimension N),
          ∫ s in (0 : ℝ)..t, c i s * q i s := hsumInterval
  have hregionIntegrable (i : Fin (RealFourierDimension N)) :
      Integrable
        (fun p => WeakEnergyPassage.weakEnergyModeForcingIntegrand b κ D N i p * c i p.1)
        (volume.restrict (weakEnergyRegion t)) :=
    WeakEnergyPassage.weakEnergy_region_weighted_integrable
      (WeakEnergyPassage.weakEnergyModeForcingIntegrand_integrable hu N i) (hc i) ht
  have hsumRegion :
      ∑ i : Fin (RealFourierDimension N),
        ∫ p in weakEnergyRegion t,
          WeakEnergyPassage.weakEnergyModeForcingIntegrand b κ D N i p * c i p.1 =
      ∫ p in weakEnergyRegion t,
        ∑ i : Fin (RealFourierDimension N),
          WeakEnergyPassage.weakEnergyModeForcingIntegrand b κ D N i p * c i p.1 := by
    symm
    exact integral_finsetSum Finset.univ (fun i hi => hregionIntegrable i)
  calc
    ∫ s in (0 : ℝ)..t,
        2 * ∑ i : Fin (RealFourierDimension N),
          weakModePairing u
              (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)) s *
            weakModeForcing b κ D
              (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)) s =
      2 * ∑ i : Fin (RealFourierDimension N),
        ∫ s in (0 : ℝ)..t, c i s * q i s := by
          simpa [q] using hsumIntervalOriginal
    _ = 2 * ∑ i : Fin (RealFourierDimension N),
          ∫ p in weakEnergyRegion t,
            WeakEnergyPassage.weakEnergyModeForcingIntegrand b κ D N i p * c i p.1 := by
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          calc
            ∫ s in (0 : ℝ)..t, c i s * q i s =
                ∫ s in (0 : ℝ)..t,
                  weakModePairing u
                    (realFourierModeAmbient N
                      ((realFourierIndexEquivFin N).symm i)) s * q i s := by
                    apply intervalIntegral.integral_congr
                    intro s hs
                    have hs01 : s ∈ Set.Icc (0 : ℝ) 1 := by
                      rw [uIcc_of_le ht.1] at hs
                      exact ⟨hs.1, hs.2.trans ht.2⟩
                    change c i s * q i s =
                      weakModePairing u
                        (realFourierModeAmbient N
                          ((realFourierIndexEquivFin N).symm i)) s * q i s
                    rw [hcoeffIcc i hs01]
            _ = ∫ p in weakEnergyRegion t,
                  WeakEnergyPassage.weakEnergyModeForcingIntegrand b κ D N i p * c i p.1 := by
                    simpa [q, c] using WeakEnergyPassage.weakEnergy_singleMode_integral hu N i ht
    _ = 2 * ∫ p in weakEnergyRegion t,
          ∑ i : Fin (RealFourierDimension N),
            WeakEnergyPassage.weakEnergyModeForcingIntegrand b κ D N i p * c i p.1 := by
          rw [hsumRegion]
    _ = 2 * ∫ p in weakEnergyRegion t,
          Homogenization.vecDot (b p.1 p.2) (D p.1 p.2) *
              weakFourierModeProjection N u p.1 p.2 +
            κ * Homogenization.vecDot (D p.1 p.2)
              (AVenhance.spaceGrad (weakFourierModeProjection N u p.1) p.2) := by
          congr 1
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem (WeakEnergyPassage.weakEnergy_region_measurable t)] with
              p hp
          have htime : p.1 ∈ Set.Icc (0 : ℝ) 1 := by
            rcases hp with ⟨hpt, _⟩
            exact ⟨le_of_lt hpt.1, (lt_of_lt_of_le hpt.2 ht.2).le⟩
          have hpoint := WeakEnergyPassage.weakEnergy_modeForcingSum_eq b κ D u N p.1 p.2
          have hcoeff (i : Fin (RealFourierDimension N)) :
              c i p.1 = weakModePairing u
                (realFourierModeAmbient N
                  ((realFourierIndexEquivFin N).symm i)) p.1 := by
            exact hcoeffIcc i htime
          calc
            (∑ i : Fin (RealFourierDimension N),
                WeakEnergyPassage.weakEnergyModeForcingIntegrand b κ D N i p * c i p.1) =
              ∑ i : Fin (RealFourierDimension N),
                weakModePairing u
                  (realFourierModeAmbient N
                    ((realFourierIndexEquivFin N).symm i)) p.1 *
                WeakEnergyPassage.weakEnergyModeForcingIntegrand b κ D N i p := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  rw [hcoeff i]
                  ring
            _ = _ := hpoint
    _ = ∫ p in weakEnergyRegion t,
          2 * (Homogenization.vecDot (b p.1 p.2) (D p.1 p.2) *
              weakFourierModeProjection N u p.1 p.2 +
            κ * Homogenization.vecDot (D p.1 p.2)
              (AVenhance.spaceGrad (weakFourierModeProjection N u p.1) p.2)) := by
          rw [integral_const_mul]

/-- Finite Fourier projection built from the extended weak mode pairings. -/
def WeakEnergyPassage.weakEnergyProjectionExtension (N : ℕ) (u : ℝ → Vec 2 → ℝ)
    (p : ℝ × Vec 2) : ℝ :=
  ∑ i : Fin (RealFourierDimension N),
    weakModePairing u
      (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i))
      (WeakEnergyPassage.weakEnergyClamp p.1) *
        realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i) p.2

theorem WeakEnergyPassage.weakEnergyProjectionExtension_continuous
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {f : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ} {D : ℝ → Vec 2 → Vec 2}
    (hu : AVenhance.IsWeakSolutionGrad b κ f u D) (N : ℕ) :
    Continuous (WeakEnergyPassage.weakEnergyProjectionExtension N u) := by
  classical
  have hmode (i : Fin (RealFourierDimension N)) :
      Continuous (fun x : Vec 2 =>
        realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i) x) :=
    (realFourierModeAmbient_contDiff N
      ((realFourierIndexEquivFin N).symm i)).continuous
  have hcoef (i : Fin (RealFourierDimension N)) :
      Continuous (fun t : ℝ => weakModePairing u
        (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i))
        (WeakEnergyPassage.weakEnergyClamp t)) := by
    have hpair := hu.2.2.2.2.2.2.1
      (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i))
      ((realFourierModeAmbient_contDiff N
        ((realFourierIndexEquivFin N).symm i)).of_le le_top)
      (realFourierModeAmbient_periodic N
        ((realFourierIndexEquivFin N).symm i))
    exact hpair.comp_continuous WeakEnergyPassage.weakEnergyClamp_continuous
        WeakEnergyPassage.weakEnergyClamp_mem
  have hterm (i : Fin (RealFourierDimension N)) :
      Continuous (fun p : ℝ × Vec 2 =>
        weakModePairing u
          (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i))
          (WeakEnergyPassage.weakEnergyClamp p.1) *
          realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i) p.2) := by
    exact (hcoef i).comp continuous_fst |>.mul
      ((hmode i).comp continuous_snd)
  unfold WeakEnergyPassage.weakEnergyProjectionExtension
  exact continuous_finsetSum Finset.univ (fun i _ => hterm i)

theorem WeakEnergyPassage.weakEnergyProjectionExtension_eq_on
    (N : ℕ) (u : ℝ → Vec 2 → ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (x : Vec 2) :
    WeakEnergyPassage.weakEnergyProjectionExtension N u (t, x) =
      weakFourierModeProjection N u t x := by
  simp [WeakEnergyPassage.weakEnergyProjectionExtension, weakFourierModeProjection,
    realFourierModeAmbientExpansion, weakFourierCoefficientPath,
    WeakEnergyPassage.weakEnergyClamp_eq ht]

theorem weakEnergyProjection_memLp
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {f : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ} {D : ℝ → Vec 2 → Vec 2}
    (hu : AVenhance.IsWeakSolutionGrad b κ f u D) (N : ℕ) :
    MemLp (fun p : ℝ × Vec 2 => weakFourierModeProjection N u p.1 p.2) 2
      (volume.restrict AVenhance.timeCube) := by
  have hmem := weak_continuous_memLp_two_timeCube
    (WeakEnergyPassage.weakEnergyProjectionExtension_continuous hu N)
  have heq : WeakEnergyPassage.weakEnergyProjectionExtension N u =ᵐ[volume.restrict
      AVenhance.timeCube]
      fun p => weakFourierModeProjection N u p.1 p.2 := by
    filter_upwards [ae_restrict_mem WeakEnergyPassage.weakEnergy_timeCube_measurable] with p hp
    exact WeakEnergyPassage.weakEnergyProjectionExtension_eq_on N u
      ⟨le_of_lt hp.1.1, le_of_lt hp.1.2⟩ p.2
  exact MeasureTheory.MemLp.ae_eq heq hmem

/-- Coordinate gradient of the finite Fourier projection of a weak solution. -/
def WeakEnergyPassage.weakEnergyGradientExtension (N : ℕ) (u : ℝ → Vec 2 → ℝ)
    (i : Fin 2) (p : ℝ × Vec 2) : ℝ :=
  ∑ j : Fin (RealFourierDimension N),
    weakModePairing u
      (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm j))
      (WeakEnergyPassage.weakEnergyClamp p.1) *
      realFourierModeDerivativeScale
        ((realFourierIndexEquivFin N).symm j) i *
      realFourierModeAmbient N
        (realFourierModeIndexSwap ((realFourierIndexEquivFin N).symm j)) p.2

theorem WeakEnergyPassage.weakEnergyGradientExtension_continuous
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {f : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ} {D : ℝ → Vec 2 → Vec 2}
    (hu : AVenhance.IsWeakSolutionGrad b κ f u D) (N : ℕ) (i : Fin 2) :
    Continuous (WeakEnergyPassage.weakEnergyGradientExtension N u i) := by
  classical
  have hterm (j : Fin (RealFourierDimension N)) :
      Continuous (fun p : ℝ × Vec 2 =>
        weakModePairing u
          (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm j))
          (WeakEnergyPassage.weakEnergyClamp p.1) *
        realFourierModeDerivativeScale
          ((realFourierIndexEquivFin N).symm j) i *
        realFourierModeAmbient N
          (realFourierModeIndexSwap ((realFourierIndexEquivFin N).symm j)) p.2) := by
    have hpair := hu.2.2.2.2.2.2.1
      (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm j))
      ((realFourierModeAmbient_contDiff N
        ((realFourierIndexEquivFin N).symm j)).of_le le_top)
      (realFourierModeAmbient_periodic N
        ((realFourierIndexEquivFin N).symm j))
    have hcoef := hpair.comp_continuous WeakEnergyPassage.weakEnergyClamp_continuous
        WeakEnergyPassage.weakEnergyClamp_mem
    have hmode : Continuous (fun x : Vec 2 =>
        realFourierModeAmbient N
          (realFourierModeIndexSwap ((realFourierIndexEquivFin N).symm j)) x) :=
      (realFourierModeAmbient_contDiff N
        (realFourierModeIndexSwap ((realFourierIndexEquivFin N).symm j))).continuous
    exact ((hcoef.comp continuous_fst).mul continuous_const).mul (hmode.comp continuous_snd)
  unfold WeakEnergyPassage.weakEnergyGradientExtension
  exact continuous_finsetSum Finset.univ (fun j _ => hterm j)

theorem WeakEnergyPassage.weakEnergyGradientExtension_eq_on
    (N : ℕ) (u : ℝ → Vec 2 → ℝ) (i : Fin 2) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (x : Vec 2) :
    WeakEnergyPassage.weakEnergyGradientExtension N u i (t, x) =
      AVenhance.spaceGrad (weakFourierModeProjection N u t) x i := by
  rw [WeakEnergyPassage.weakEnergyGradientExtension, weakFourierModeProjection,
    spaceGrad_realFourierModeAmbientExpansion]
  simp only [weakFourierCoefficientPath, WeakEnergyPassage.weakEnergyClamp_eq ht, PiLp.toLp_apply]

theorem weakEnergyGradient_memLp
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {f : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ} {D : ℝ → Vec 2 → Vec 2}
    (hu : AVenhance.IsWeakSolutionGrad b κ f u D) (N : ℕ) (i : Fin 2) :
    MemLp (fun p : ℝ × Vec 2 =>
      AVenhance.spaceGrad (weakFourierModeProjection N u p.1) p.2 i) 2
      (volume.restrict AVenhance.timeCube) := by
  have hmem := weak_continuous_memLp_two_timeCube
    (WeakEnergyPassage.weakEnergyGradientExtension_continuous hu N i)
  have heq : WeakEnergyPassage.weakEnergyGradientExtension N u i =ᵐ[volume.restrict
      AVenhance.timeCube]
      fun p => AVenhance.spaceGrad (weakFourierModeProjection N u p.1) p.2 i := by
    filter_upwards [ae_restrict_mem WeakEnergyPassage.weakEnergy_timeCube_measurable] with p hp
    exact WeakEnergyPassage.weakEnergyGradientExtension_eq_on N u i
      ⟨le_of_lt hp.1.1, le_of_lt hp.1.2⟩ p.2
  exact MeasureTheory.MemLp.ae_eq heq hmem

theorem WeakEnergyPassage.weakEnergy_timeCube_integral_eq_Ioo_cell
    {F : ℝ × Vec 2 → ℝ}
    (hF : Integrable F (volume.restrict AVenhance.timeCube)) :
    ∫ p in AVenhance.timeCube, F p =
      ∫ t in Set.Ioo (0 : ℝ) 1,
        ∫ x in AVenhance.unitCube, F (t, x) := by
  have hprod : Integrable F
      ((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
        (volume.restrict AVenhance.unitCube)) := by
    rwa [← weakEnergy_timeCube_measure_eq_product]
  calc
    ∫ p in AVenhance.timeCube, F p =
        ∫ t, ∫ x, F (t, x) ∂(volume.restrict AVenhance.unitCube)
          ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
            rw [weakEnergy_timeCube_measure_eq_product, integral_prod F hprod]
    _ = ∫ t in Set.Ioo (0 : ℝ) 1,
          ∫ x in AVenhance.unitCube, F (t, x) := by
            rfl

/-- The finite real Fourier projections converge to a weak path in scalar spacetime `L²`. -/
theorem weakFourierProjection_scalar_spacetime_L2_tendsto
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {f : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ} {D : ℝ → Vec 2 → Vec 2}
    (hu : AVenhance.IsWeakSolutionGrad b κ f u D) :
    Tendsto (fun N => ∫ p in AVenhance.timeCube,
      (u p.1 p.2 - weakFourierModeProjection N u p.1 p.2) ^ 2)
      atTop (𝓝 0) := by
  have hcut := weakFourierProjection_strong_H1_time_convergence hu
  have herror (N : ℕ) : MemLp
      (fun p : ℝ × Vec 2 => u p.1 p.2 - weakFourierModeProjection N u p.1 p.2)
      2 (volume.restrict AVenhance.timeCube) := by
    exact hu.2.2.1.sub (weakEnergyProjection_memLp hu N)
  have hInt (N : ℕ) : Integrable
      (fun p : ℝ × Vec 2 =>
        (u p.1 p.2 - weakFourierModeProjection N u p.1 p.2) ^ 2)
      (volume.restrict AVenhance.timeCube) := by
    exact (memLp_two_iff_integrable_sq (herror N).aestronglyMeasurable).1 (herror N)
  have heq (N : ℕ) :
      (∫ p in AVenhance.timeCube,
        (u p.1 p.2 - weakFourierModeProjection N u p.1 p.2) ^ 2) =
      ∫ t in Set.Ioo (0 : ℝ) 1,
        AVenhance.l2NormSq
          (fun x => u t x - weakFourierModeProjection N u t x) := by
    rw [WeakEnergyPassage.weakEnergy_timeCube_integral_eq_Ioo_cell (hInt N)]
    rfl
  have hnonneg (N : ℕ) : 0 ≤ ∫ t in Set.Ioo (0 : ℝ) 1,
      AVenhance.l2NormSq
        (fun x => u t x - weakFourierModeProjection N u t x) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact integral_nonneg fun x => sq_nonneg _
  have hsum_nonneg : ∀ N, 0 ≤
      (∫ t in Set.Ioo (0 : ℝ) 1,
        AVenhance.l2NormSq
          (fun x => u t x - weakFourierModeProjection N u t x)) +
      ∑ i : Fin 2, ∫ t in Set.Ioo (0 : ℝ) 1,
        AVenhance.l2NormSq (fun x => D t x i -
          AVenhance.spaceGrad (weakFourierModeProjection N u t) x i) := by
    intro N
    apply add_nonneg (hnonneg N)
    exact Finset.sum_nonneg fun i hi => integral_nonneg_of_ae (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact integral_nonneg fun x => sq_nonneg _)
  have hbound : ∀ N, (∫ t in Set.Ioo (0 : ℝ) 1,
      AVenhance.l2NormSq
        (fun x => u t x - weakFourierModeProjection N u t x)) ≤
      (∫ t in Set.Ioo (0 : ℝ) 1,
        AVenhance.l2NormSq
          (fun x => u t x - weakFourierModeProjection N u t x)) +
      ∑ i : Fin 2, ∫ t in Set.Ioo (0 : ℝ) 1,
        AVenhance.l2NormSq (fun x => D t x i -
          AVenhance.spaceGrad (weakFourierModeProjection N u t) x i) := by
    intro N
    have hsum : 0 ≤ ∑ i : Fin 2, ∫ t in Set.Ioo (0 : ℝ) 1,
        AVenhance.l2NormSq (fun x => D t x i -
          AVenhance.spaceGrad (weakFourierModeProjection N u t) x i) :=
      Finset.sum_nonneg fun i hi => integral_nonneg_of_ae (by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        exact integral_nonneg fun x => sq_nonneg _)
    linarith
  have hlim : Tendsto (fun N =>
      ∫ t in Set.Ioo (0 : ℝ) 1,
        AVenhance.l2NormSq
          (fun x => u t x - weakFourierModeProjection N u t x))
      atTop (𝓝 0) := by
    exact squeeze_zero hnonneg hbound hcut
  exact hlim.congr' (Filter.Eventually.of_forall fun N => (heq N).symm)

/-- Every weak-gradient coordinate is approximated by the corresponding projected derivative in
spacetime `L²`. -/
theorem weakFourierProjection_gradient_spacetime_L2_tendsto
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {f : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ} {D : ℝ → Vec 2 → Vec 2}
    (hu : AVenhance.IsWeakSolutionGrad b κ f u D) (i : Fin 2) :
    Tendsto (fun N => ∫ p in AVenhance.timeCube,
      (D p.1 p.2 i -
        AVenhance.spaceGrad (weakFourierModeProjection N u p.1) p.2 i) ^ 2)
      atTop (𝓝 0) := by
  have hcut := weakFourierProjection_strong_H1_time_convergence hu
  have herror (N : ℕ) : MemLp
      (fun p : ℝ × Vec 2 => D p.1 p.2 i -
        AVenhance.spaceGrad (weakFourierModeProjection N u p.1) p.2 i)
      2 (volume.restrict AVenhance.timeCube) := by
    exact (hu.2.2.2.1 i).sub (weakEnergyGradient_memLp hu N i)
  have hInt (N : ℕ) : Integrable
      (fun p : ℝ × Vec 2 =>
        (D p.1 p.2 i -
          AVenhance.spaceGrad (weakFourierModeProjection N u p.1) p.2 i) ^ 2)
      (volume.restrict AVenhance.timeCube) := by
    exact (memLp_two_iff_integrable_sq (herror N).aestronglyMeasurable).1 (herror N)
  have heq (N : ℕ) :
      (∫ p in AVenhance.timeCube,
        (D p.1 p.2 i -
          AVenhance.spaceGrad (weakFourierModeProjection N u p.1) p.2 i) ^ 2) =
      ∫ t in Set.Ioo (0 : ℝ) 1,
        AVenhance.l2NormSq (fun x => D t x i -
          AVenhance.spaceGrad (weakFourierModeProjection N u t) x i) := by
    rw [WeakEnergyPassage.weakEnergy_timeCube_integral_eq_Ioo_cell (hInt N)]
    rfl
  have hnonneg (N : ℕ) : 0 ≤ ∫ t in Set.Ioo (0 : ℝ) 1,
      AVenhance.l2NormSq (fun x => D t x i -
        AVenhance.spaceGrad (weakFourierModeProjection N u t) x i) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact integral_nonneg fun x => sq_nonneg _
  have hbound (N : ℕ) :
      (∫ t in Set.Ioo (0 : ℝ) 1,
        AVenhance.l2NormSq (fun x => D t x i -
          AVenhance.spaceGrad (weakFourierModeProjection N u t) x i)) ≤
      (∫ t in Set.Ioo (0 : ℝ) 1,
        AVenhance.l2NormSq
          (fun x => u t x - weakFourierModeProjection N u t x)) +
      ∑ j : Fin 2, ∫ t in Set.Ioo (0 : ℝ) 1,
          AVenhance.l2NormSq (fun x => D t x j -
            AVenhance.spaceGrad (weakFourierModeProjection N u t) x j) := by
    have hscalar : 0 ≤ ∫ t in Set.Ioo (0 : ℝ) 1,
        AVenhance.l2NormSq
          (fun x => u t x - weakFourierModeProjection N u t x) := by
      apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact integral_nonneg fun x => sq_nonneg _
    have hi : ∫ t in Set.Ioo (0 : ℝ) 1,
        AVenhance.l2NormSq (fun x => D t x i -
          AVenhance.spaceGrad (weakFourierModeProjection N u t) x i) ≤
        ∑ j : Fin 2, ∫ t in Set.Ioo (0 : ℝ) 1,
          AVenhance.l2NormSq (fun x => D t x j -
            AVenhance.spaceGrad (weakFourierModeProjection N u t) x j) := by
      calc
        _ ≤ ∑ j ∈ (Finset.univ : Finset (Fin 2)),
            ∫ t in Set.Ioo (0 : ℝ) 1,
              AVenhance.l2NormSq (fun x => D t x j -
                AVenhance.spaceGrad (weakFourierModeProjection N u t) x j) :=
          Finset.single_le_sum (fun j hj => integral_nonneg_of_ae (by
            filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
            exact integral_nonneg fun x => sq_nonneg _)) (Finset.mem_univ i)
        _ = ∑ j : Fin 2, ∫ t in Set.Ioo (0 : ℝ) 1,
              AVenhance.l2NormSq (fun x => D t x j -
                AVenhance.spaceGrad (weakFourierModeProjection N u t) x j) := by simp
    linarith [hscalar, hi]
  have hlim : Tendsto (fun N => ∫ t in Set.Ioo (0 : ℝ) 1,
      AVenhance.l2NormSq (fun x => D t x i -
        AVenhance.spaceGrad (weakFourierModeProjection N u t) x i))
      atTop (𝓝 0) := squeeze_zero hnonneg hbound hcut
  exact hlim.congr' (Filter.Eventually.of_forall fun N => (heq N).symm)

end AVenhance.Infra.Parabolic.WeakUniqueness

end
