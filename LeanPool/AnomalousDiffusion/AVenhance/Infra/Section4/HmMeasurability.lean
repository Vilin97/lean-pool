/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.HmPerTimeRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.HmPerTimePairingInputs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.ScalarQuadraticL2
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.OpenInputs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesFlux
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ATensorHm
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LeadingErrorBoundsL2Ioi

/-! Positive-time spacetime measurability and finite-`L²` adapters for the
three fields used by the `H_m` per-time pairing interface. Quantitative rate
constants remain producer inputs: the Piola-source rate is supplied
directly, while the gradient and `d_m` rates are read from
`HmGradientContract` and `SourceErrorDContract`. The separate adapter
below bounds only the legacy `(flux - Kmat) : ∇Gbar` contraction. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Section4

open AVenhance.Infra.Section5.RelativeError

open AVenhance AVenhance.Infra.Section5
open AVenhance.Infra.Section5.Contracts
open AVenhance.Infra.Section5.Integration

theorem HmMeasurability.hm_meas_continuous_vecNorm_le_sqrt (v : Vec 2) :
    ‖v‖ ≤ Real.sqrt (vecNormSq v) := by
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
  intro i
  have hsq := Homogenization.sq_apply_le_vecNormSq v i
  have hsq' : ‖v i‖ ^ 2 ≤ (Real.sqrt (vecNormSq v)) ^ 2 := by
    simpa [Real.sq_sqrt (Homogenization.vecNormSq_nonneg v)] using hsq
  exact (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp hsq'

theorem HmMeasurability.hm_meas_vecNormSq_le_normSq (v : Vec 2) :
    ‖v‖ ^ 2 ≤ vecNormSq v := by
  have h := HmMeasurability.hm_meas_continuous_vecNorm_le_sqrt v
  have hsq := pow_le_pow_left₀ (norm_nonneg v) h 2
  simpa [Real.sq_sqrt (Homogenization.vecNormSq_nonneg v)] using hsq

theorem HmMeasurability.hm_meas_d_joint {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) {m : ℕ}
    (hm : 1 ≤ m) {κ κprev : ℝ} (hκ : 0 < κ)
    {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {Titer : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κ κprev θ₀ θprev Titer) :
    ContinuousOn
      (fun p : ℝ × Vec 2 => sourceErrorD I hΦ m κ (Titer (Nstar β)) p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) := by
  refine continuousOn_pi.mpr fun i => ?_
  exact AVenhance.Infra.Section5.Contracts.tc_sourceErrorD_continuousOn
    I hΦ m hm hκ hθprev hT i

/-- The five `AEStronglyMeasurable` fields consumed by
`hm_per_time_pairing_data_of_joint_fields_and_spacetime_eLpNorm`, deduced from
the actual joint-continuity construction. -/
theorem hm_actual_pairing_field_measurability
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) {κ κprev : ℝ}
    (hκ : 0 < κ) {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {Titer : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κ κprev θ₀ θprev Titer) :
    AEStronglyMeasurable
      (fun z : ℝ × Vec 2 => hmFrozenPiolaSource I hΦ m κ (Titer (Nstar β)) z.1 z.2)
        (volume.restrict timeCube) ∧
    AEStronglyMeasurable
      (fun z : ℝ × Vec 2 => spaceGrad
        (I.Hm hΦ m κ (Titer (Nstar β)) z.1) z.2) (volume.restrict timeCube) ∧
    AEStronglyMeasurable
      (fun z : ℝ × Vec 2 => Real.sqrt (vecNormSq
        (spaceGrad (I.Hm hΦ m κ (Titer (Nstar β)) z.1) z.2)))
        (volume.restrict timeCube) ∧
    AEStronglyMeasurable
      (fun z : ℝ × Vec 2 => sourceErrorD I hΦ m κ (Titer (Nstar β)) z.1 z.2)
        (volume.restrict timeCube) ∧
    AEStronglyMeasurable
      (fun z : ℝ × Vec 2 => Real.sqrt (vecNormSq
        (sourceErrorD I hΦ m κ (Titer (Nstar β)) z.1 z.2)))
        (volume.restrict timeCube) := by
  have hreg := hm_positive_time_actual_regular_data I hΦ hm hκ hθprev hT
  rcases hreg with ⟨_, _, _, _, hFJoint, hGJoint, _, _, _, _, _, _, _, _⟩
  have hHmOn := Hm_contDiffOn_Ioi_top I hΦ hm hκ hθprev hT
  have hGradJoint : ContinuousOn
      (fun p : ℝ × Vec 2 => spaceGrad
        (I.Hm hΦ m κ (Titer (Nstar β)) p.1) p.2)
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) := by
    refine continuousOn_pi.mpr fun j => ?_
    exact (Integration.contDiffOn_spaceGrad_slice_Ioi
      (F := fun t x => I.Hm hΦ m κ (Titer (Nstar β)) t x) hHmOn j).continuousOn
  have hVJoint := HmMeasurability.hm_meas_d_joint I hΦ (m := m) hm hκ hθprev hT
  have hGmeas :=
    AVenhance.Infra.Section5.RelativeError.aestronglyMeasurable_timeCube_of_continuousOn_Ioi
      hGJoint
  have hGradMeas := aestronglyMeasurable_timeCube_of_contDiffOn_Ioi
    hGradJoint
  have hGradMagJoint :=
    AVenhance.Infra.Section5.RelativeError.continuousOn_sqrt_vecNormSq
      (continuousOn_pi.mp hGradJoint)
  have hGradMagMeas :=
    AVenhance.Infra.Section5.RelativeError.aestronglyMeasurable_timeCube_of_continuousOn_Ioi
      hGradMagJoint
  have hVmeas := aestronglyMeasurable_timeCube_of_contDiffOn_Ioi
    hVJoint
  have hVMagJoint :=
    AVenhance.Infra.Section5.RelativeError.continuousOn_sqrt_vecNormSq
      (continuousOn_pi.mp hVJoint)
  have hVmagMeas :=
    AVenhance.Infra.Section5.RelativeError.aestronglyMeasurable_timeCube_of_continuousOn_Ioi
      hVMagJoint
  exact ⟨hGmeas, hGradMeas, hGradMagMeas, hVmeas, hVmagMeas⟩

/-- `HmGradientContract` gives the spacetime vector `L²` bound consumed by
the pairing assembler. The closed-time extension supplies the integrability
needed to interpret its real-valued energy as an actual square integral. -/
theorem hm_gradient_spacetime_eLpNorm_bound_of_contract
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) {κ κprev : ℝ}
    (hκ : 0 < κ) (hκprev : 0 < κprev)
    {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {Titer : ℕ → ℝ → Vec 2 → ℝ} {CH B : ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κ κprev θ₀ θprev Titer)
    (hCH : 0 ≤ CH) (hB : 0 ≤ B)
    (hContract : HmGradientContract I hΦ m κ κprev Titer CH B) :
    eLpNorm
      (fun z : ℝ × Vec 2 => spaceGrad (I.Hm hΦ m κ (Titer (Nstar β)) z.1) z.2)
      2 (volume.restrict timeCube) ≤
        ENNReal.ofReal
          (CH * epsilon β I.Λ (m - 1) ^ (4 * delta β) * B / Real.sqrt κprev) := by
  let V : ℝ × Vec 2 → Vec 2 := fun z =>
    spaceGrad (I.Hm hΦ m κ (Titer (Nstar β)) z.1) z.2
  let μ : Measure (ℝ × Vec 2) := volume.restrict timeCube
  let Q : ℝ := CH * epsilon β I.Λ (m - 1) ^ (4 * delta β) * B / Real.sqrt κprev
  have hHmOn := Hm_contDiffOn_Ioi_top I hΦ hm hκ hθprev hT
  have hVJoint : ContinuousOn V
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) := by
    refine continuousOn_pi.mpr fun j => ?_
    exact (Integration.contDiffOn_spaceGrad_slice_Ioi
      (F := fun t x => I.Hm hΦ m κ (Titer (Nstar β)) t x) hHmOn j).continuousOn
  have hVmeas : AEStronglyMeasurable V μ := by
    exact aestronglyMeasurable_timeCube_of_contDiffOn_Ioi
        hVJoint
  let M : ℝ × Vec 2 → ℝ := fun z => Real.sqrt (vecNormSq (V z))
  have hMJoint : ContinuousOn M
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) :=
    AVenhance.Infra.Section5.RelativeError.continuousOn_sqrt_vecNormSq (continuousOn_pi.mp hVJoint)
  have hMmeas : AEStronglyMeasurable M μ := by
    exact AVenhance.Infra.Section5.RelativeError.aestronglyMeasurable_timeCube_of_continuousOn_Ioi
        hMJoint
  obtain ⟨G, hGc, hGeq⟩ := sa_Hm_grad_extends I hΦ hm hκ hθprev hT
  have hGcont : ContinuousOn G (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) :=
    continuousOn_pi.mpr hGc
  have hGsqcont : ContinuousOn (fun z => vecNormSq (G z))
      (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) :=
    LeftToShow.continuous_vecNormSq_two.comp_continuousOn hGcont
  have hGsqInt : Integrable (fun z => vecNormSq (G z)) μ := by
    exact AVenhance.Infra.Section5.RelativeError.integrable_timeCube_of_continuousOn hGsqcont
  have hVsqeq : (fun z => vecNormSq (V z)) =ᵐ[μ]
      fun z => vecNormSq (G z) := by
    filter_upwards [MeasureTheory.ae_restrict_mem
      AVenhance.Infra.Section5.RelativeError.measurableSet_timeCube] with z hz
    exact congrArg vecNormSq (hGeq z ⟨hz.1.1, Set.mem_univ _⟩)
  have hVsqInt : Integrable (fun z => vecNormSq (V z)) μ := hGsqInt.congr hVsqeq.symm
  have hMsqInt : Integrable (fun z => M z ^ 2) μ := by
    refine hVsqInt.congr ?_
    filter_upwards with z
    simp only [M]
    exact (Real.sq_sqrt (Homogenization.vecNormSq_nonneg (V z))).symm
  have hEnergyNonneg : 0 ≤ spaceTimeGradNormSq
      (fun t x => spaceGrad (I.Hm hΦ m κ (Titer (Nstar β)) t) x) :=
    integral_nonneg fun z => vecNormSq_nonneg _
  have hQnonneg : 0 ≤ Q := by
    dsimp [Q]
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg hCH
        (Real.rpow_nonneg (le_of_lt
          (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le)) _)) hB
    · exact Real.sqrt_nonneg _
  have hRootBound : Real.sqrt (spaceTimeGradNormSq
      (fun t x => spaceGrad (I.Hm hΦ m κ (Titer (Nstar β)) t) x)) ≤ Q := by
    change Real.sqrt (spaceTimeGradNormSq
      (fun t x => spaceGrad (I.Hm hΦ m κ (Titer (Nstar β)) t) x)) ≤
        (CH * epsilon β I.Λ (m - 1) ^ (4 * delta β) * B) / Real.sqrt κprev
    apply (le_div_iff₀ (Real.sqrt_pos.2 hκprev)).2
    change Real.sqrt κprev * Real.sqrt (spaceTimeGradNormSq
      (fun s x => spaceGrad (I.Hm hΦ m κ (Titer (Nstar β)) s) x)) ≤
        CH * epsilon β I.Λ (m - 1) ^ (4 * delta β) * B at hContract
    nlinarith [hContract]
  have hEnergyBound : spaceTimeGradNormSq
      (fun t x => spaceGrad (I.Hm hΦ m κ (Titer (Nstar β)) t) x) ≤ Q ^ 2 :=
    (Real.sqrt_le_iff).mp hRootBound |>.2
  have hMenergy : (∫ z, M z ^ 2 ∂μ) ≤ Q ^ 2 := by
    have hEq : (∫ z, M z ^ 2 ∂μ) =
        spaceTimeGradNormSq
          (fun t x => spaceGrad (I.Hm hΦ m κ (Titer (Nstar β)) t) x) := by
      unfold M V μ AVenhance.spaceTimeGradNormSq
      refine setIntegral_congr_fun AVenhance.Infra.Section5.RelativeError.measurableSet_timeCube ?_
      intro z hz
      exact Real.sq_sqrt (Homogenization.vecNormSq_nonneg _)
    rw [hEq]
    exact hEnergyBound
  have hMbound := amnr_scalar_eLpNorm_two_le_of_square hMmeas hMsqInt hQnonneg hMenergy
  have hPoint (z : ℝ × Vec 2) : ‖V z‖ ≤ M z := HmMeasurability.hm_meas_continuous_vecNorm_le_sqrt
      (V z)
  have hVmono := eLpNorm_mono_ae hVmeas
    (Filter.Eventually.of_forall fun z => by
      calc
        ‖V z‖ ≤ M z := hPoint z
        _ = ‖M z‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)])
    (p := (2 : ENNReal))
  calc
    eLpNorm V 2 μ ≤ eLpNorm M 2 μ := hVmono
    _ ≤ ENNReal.ofReal Q := hMbound
    _ = ENNReal.ofReal
        (CH * epsilon β I.Λ (m - 1) ^ (4 * delta β) * B / Real.sqrt κprev) := by
      rfl

theorem HmMeasurability.hm_vector_spacetime_eLpNorm_bound_of_slice_energy
    {V : ℝ → Vec 2 → Vec 2} {Q : ℝ}
    (hVmeas : AEStronglyMeasurable
      (fun z : ℝ × Vec 2 => V z.1 z.2) (volume.restrict timeCube))
    (hVmagMeas : AEStronglyMeasurable
      (fun z : ℝ × Vec 2 => Real.sqrt (vecNormSq (V z.1 z.2)))
        (volume.restrict timeCube))
    (hVslice : ∀ t ∈ Set.Ioo (0 : ℝ) 1, Continuous (V t))
    (_hQ : 0 ≤ Q)
    (hEnergy : (∫⁻ t in Set.Ioo (0 : ℝ) 1,
      ENNReal.ofReal (Real.sqrt (gradNormSq (V t))) ^ 2) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal Q) :
    eLpNorm (fun z : ℝ × Vec 2 => V z.1 z.2) 2 (volume.restrict timeCube) ≤
      ENNReal.ofReal Q := by
  let μ : Measure (ℝ × Vec 2) := volume.restrict timeCube
  let M : ℝ × Vec 2 → ℝ := fun z => Real.sqrt (vecNormSq (V z.1 z.2))
  have hvol : (volume : Measure (ℝ × Vec 2)) =
      (volume : Measure ℝ).prod (volume : Measure (Vec 2)) :=
    Measure.volume_eq_prod ℝ (Vec 2)
  have hmeas : AEMeasurable (fun z : ℝ × Vec 2 => ‖M z‖ₑ ^ (2 : ℝ))
      (((volume : Measure ℝ).prod (volume : Measure (Vec 2))).restrict
        (Set.Ioo (0 : ℝ) 1 ×ˢ unitCube)) := by
    have h : AEMeasurable (fun z : ℝ × Vec 2 => ‖M z‖ₑ)
        (volume.restrict timeCube) := by
      simpa only [M] using hVmagMeas.enorm
    rw [hvol] at h
    exact (ENNReal.continuous_rpow_const (y := (2 : ℝ))).measurable.comp_aemeasurable h
  have hprod := setLIntegral_prod (μ := (volume : Measure ℝ))
    (ν := (volume : Measure (Vec 2)))
    (s := Set.Ioo (0 : ℝ) 1) (t := unitCube)
    (fun z : ℝ × Vec 2 => ‖M z‖ₑ ^ (2 : ℝ)) hmeas
  have hnorm : eLpNorm M 2 μ =
      (∫⁻ z in Set.Ioo (0 : ℝ) 1 ×ˢ unitCube, ‖M z‖ₑ ^ (2 : ℝ)
        ∂((volume : Measure ℝ).prod (volume : Measure (Vec 2)))) ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hVmagMeas]
    simp only [ENNReal.toReal_ofNat]
    rw [hvol]
    rfl
  have hsliceInt (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
      Integrable (fun x : Vec 2 => vecNormSq (V t x))
        (volume.restrict unitCube) := by
    have hcont : Continuous (fun x : Vec 2 => vecNormSq (V t x)) :=
      LeftToShow.continuous_vecNormSq_two.comp (hVslice t ht)
    exact LeftToShow.integrableOn_unitCube_of_continuous hcont
  have hsliceEq (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
      (∫⁻ x in unitCube, ‖M (t, x)‖ₑ ^ (2 : ℝ)) =
        ENNReal.ofReal (gradNormSq (V t)) := by
    have hpoint (x : Vec 2) : ‖M (t, x)‖ₑ ^ (2 : ℝ) =
        ENNReal.ofReal (vecNormSq (V t x)) := by
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _)
        (by norm_num : (0 : ℝ) ≤ 2)]
      simp [M, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt (Homogenization.vecNormSq_nonneg (V t x))]
    calc
      _ = ∫⁻ x in unitCube, ENNReal.ofReal (vecNormSq (V t x)) := by
        exact lintegral_congr fun x => hpoint x
      _ = ENNReal.ofReal (gradNormSq (V t)) := by
        unfold gradNormSq
        exact (ofReal_integral_eq_lintegral_ofReal (hsliceInt t ht)
          (Filter.Eventually.of_forall fun x =>
            Homogenization.vecNormSq_nonneg (V t x))).symm
  have hglobal :
      (∫⁻ z in Set.Ioo (0 : ℝ) 1 ×ˢ unitCube,
        ‖M z‖ₑ ^ (2 : ℝ)
          ∂((volume : Measure ℝ).prod (volume : Measure (Vec 2)))) =
        ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (gradNormSq (V t)) := by
    rw [hprod]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hsliceEq t ht
  have hgradNonneg (t : ℝ) : 0 ≤ gradNormSq (V t) := by
    unfold gradNormSq
    exact integral_nonneg fun x => Homogenization.vecNormSq_nonneg (V t x)
  have hcontractEq : (∫⁻ t in Set.Ioo (0 : ℝ) 1,
      ENNReal.ofReal (Real.sqrt (gradNormSq (V t))) ^ 2) =
        ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (gradNormSq (V t)) := by
    refine lintegral_congr fun t => ?_
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (hgradNonneg t)]
  have hMbound : eLpNorm M 2 μ ≤ ENNReal.ofReal Q := by
    rw [hnorm, hglobal]
    have hcontract := hEnergy
    rw [hcontractEq] at hcontract
    exact hcontract
  have hPoint (z : ℝ × Vec 2) : ‖V z.1 z.2‖ ≤ M z :=
    HmMeasurability.hm_meas_continuous_vecNorm_le_sqrt (V z.1 z.2)
  have hVbound := eLpNorm_mono_ae hVmeas
    (Filter.Eventually.of_forall fun z => by
      calc
        ‖V z.1 z.2‖ ≤ M z := hPoint z
        _ = ‖M z‖ := by rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)])
    (p := (2 : ENNReal))
  simpa only [μ] using hVbound.trans hMbound

/-- The `SourceErrorDContract` time-slice Euclidean rate supplies the matching
spacetime `eLpNorm` bound for `d_m`, with the same source-rate constant. -/
theorem hm_sourceErrorD_spacetime_eLpNorm_bound_of_contract
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) {κ κprev : ℝ}
    (hκ : 0 < κ) {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {Titer : ℕ → ℝ → Vec 2 → ℝ} {Cd B : ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κ κprev θ₀ θprev Titer)
    (hCd : 0 ≤ Cd) (hB : 0 ≤ B)
    (hContract : SourceErrorDContract I hΦ m κ Titer Cd B) :
    eLpNorm
      (fun z : ℝ × Vec 2 => sourceErrorD I hΦ m κ (Titer (Nstar β)) z.1 z.2)
      2 (volume.restrict timeCube) ≤
        ENNReal.ofReal
          (Cd * epsilon β I.Λ (m - 1) ^ (2 * delta β) * Real.sqrt κ * B) := by
  have hregular := hm_positive_time_actual_regular_data I hΦ hm hκ hθprev hT
  rcases hregular with ⟨_, _, _, _, _, _, _, _, _, hVslice, _, _, _, _⟩
  obtain ⟨_, _, _, hVmeas, hVmagMeas⟩ :=
    hm_actual_pairing_field_measurability I hΦ hm hκ hθprev hT
  have hQnonneg : 0 ≤ Cd * epsilon β I.Λ (m - 1) ^ (2 * delta β) * Real.sqrt κ * B := by
    have hε : 0 < epsilon β I.Λ (m - 1) :=
      Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
    positivity
  have hSliceEnergy : (∫⁻ t in Set.Ioo (0 : ℝ) 1,
      ENNReal.ofReal (Real.sqrt (gradNormSq
        (sourceErrorD I hΦ m κ (Titer (Nstar β)) t))) ^ 2) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal
          (Cd * epsilon β I.Λ (m - 1) ^ (2 * delta β) * Real.sqrt κ * B) := hContract
  exact HmMeasurability.hm_vector_spacetime_eLpNorm_bound_of_slice_energy hVmeas hVmagMeas
    (fun t ht => (hVslice t ht.1).continuous) hQnonneg hSliceEnergy

end AVenhance.Infra.Section4
