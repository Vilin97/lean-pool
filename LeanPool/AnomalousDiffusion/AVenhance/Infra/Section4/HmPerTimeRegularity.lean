/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.HmPerTimeAssembly
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.HmPerTimePairingInputs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.TIterateSmooth
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeInitialDefectMaterialFlow
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.PartIHmRegularityPeriodic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.BigBoundMeanZeroData
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermFluxesJoint
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermFluxesSlice
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermContinuityPointwiseTiny
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.ResidualFluxRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.HmBaseFluxIdentity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.HmSourcePairing
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.FlowDiffeo

/-! Positive-time regularity and material derivative for the actual `H_m` source, packaged for the
    per-time transported energy assembler. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Topology Homogenization
open scoped ContDiff
open AVenhance.Infra.Ergodic

namespace AVenhance.Infra.Section4

open AVenhance AVenhance.Infra.Section5
open AVenhance.Infra.Section5.Contracts
open AVenhance.Infra.Section5.Integration

/-- Joint time-space domain with strictly positive time. -/
abbrev HmPerTimeRegularity.hmPerTimePositiveDomain : Set (ℝ × Vec 2) :=
  Set.Ioi (0 : ℝ) ×ˢ Set.univ

theorem HmPerTimeRegularity.hmPerTime_stDiv_contDiffOn {p : ℕ}
    {F : ℝ × Vec 2 → Vec 2}
    (hF : ContDiffOn ℝ (p + 1) F HmPerTimeRegularity.hmPerTimePositiveDomain) :
    ContDiffOn ℝ p (AVenhance.Infra.Section5.stDiv F)
      HmPerTimeRegularity.hmPerTimePositiveDomain := by
  have hopen : IsOpen HmPerTimeRegularity.hmPerTimePositiveDomain := isOpen_Ioi.prod isOpen_univ
  have hD : ContDiffOn ℝ p (fun z => fderiv ℝ F z) HmPerTimeRegularity.hmPerTimePositiveDomain :=
    hF.fderiv_of_isOpen hopen (by simp)
  have hterm (i : Fin 2) : ContDiffOn ℝ p
      (fun z => (fderiv ℝ F z (0, basisVec i)) i) HmPerTimeRegularity.hmPerTimePositiveDomain := by
    have hv : ContDiffOn ℝ p
        (fun _ : ℝ × Vec 2 => ((0 : ℝ), basisVec i)) HmPerTimeRegularity.hmPerTimePositiveDomain :=
      contDiffOn_const
    have heval := hD.clm_apply hv
    have hproj := (contDiffOn_const : ContDiffOn ℝ p
      (fun _ : ℝ × Vec 2 => (ContinuousLinearMap.proj i : Vec 2 →L[ℝ] ℝ))
      HmPerTimeRegularity.hmPerTimePositiveDomain).clm_apply heval
    simpa using hproj
  unfold AVenhance.Infra.Section5.stDiv
  exact ContDiffOn.sum fun i hi => hterm i

theorem HmPerTimeRegularity.hmPerTime_endpoint_continuousOn
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) {κ κprev : ℝ}
    (hκ : 0 < κ) {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {Titer : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev
      (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κ κprev θ₀ θprev Titer)
    (r : ℕ) (hbudget : ∀ n ∈ Finset.range (Nstar β), 2 + r ≤ Nstar β) :
    ContinuousOn
      (fun p : ℝ × Vec 2 => hmEndpoint I hΦ m κ (Titer (Nstar β)) r p.1 p.2)
      HmPerTimeRegularity.hmPerTimePositiveDomain := by
  let T := Titer (Nstar β)
  have hflux := residual_pairEndpointFluxSum_contDiffOn I hΦ hm hκ
    hθprev hT (Nstar β) r 2 hbudget
  have hdiv : ContDiffOn ℝ 1
      (stDiv (amnrPairEndpointFluxSum I hΦ m (Nstar β) κ T r))
      HmPerTimeRegularity.hmPerTimePositiveDomain :=
          HmPerTimeRegularity.hmPerTime_stDiv_contDiffOn hflux
  apply ContinuousOn.congr hdiv.continuousOn
  intro p hp
  have hpos : HmPerTimeRegularity.hmPerTimePositiveDomain ∈ 𝓝 p :=
    (isOpen_Ioi.prod isOpen_univ).mem_nhds hp
  have hF : DifferentiableAt ℝ
      (amnrPairEndpointFluxSum I hΦ m (Nstar β) κ T r) p :=
    (hflux.differentiableOn (by norm_num) p hp).differentiableAt hpos
  exact frozen_hmEndpoint_eq_stDiv_pairEndpointFluxSum I hΦ m κ T r
    p.1 p.2 hF

theorem HmPerTimeRegularity.hmPerTime_terminalFlux_differentiable
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) {κ κprev : ℝ}
    (hκ : 0 < κ) {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {Titer : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev
      (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κ κprev θ₀ θprev Titer)
    {t : ℝ} (ht : 0 < t) (x : Vec 2) :
    DifferentiableAt ℝ
      (hmFrozenTerminalFlux I hΦ m κ (Titer (Nstar β)) t) x := by
  let T := Titer (Nstar β)
  have hN : 1 ≤ Nstar β := by
    have hbig := AVenhance.Infra.Ingredients.Nstar_ge_256 I.one_lt_beta I.beta_lt
    omega
  have hendpointOn := residual_pairEndpointFluxSum_contDiffOn I hΦ hm hκ
    hθprev hT (Nstar β) (Jcut β) 1
    (by
      intro n hn
      have hbudget := AVenhance.Infra.Section4.Jcut_budget hN
      omega)
  have hpoint : DifferentiableAt ℝ
      (amnrPairEndpointFluxSum I hΦ m (Nstar β) κ T (Jcut β)) (t, x) := by
    have hwithin := hendpointOn.differentiableOn
      (by norm_num) (t, x) ⟨ht, Set.mem_univ x⟩
    exact hwithin.differentiableAt
      (isOpen_Ioi.prod isOpen_univ |>.mem_nhds ⟨ht, Set.mem_univ x⟩)
  have heq : hmFrozenTerminalFlux I hΦ m κ T t =
      fun z => amnrPairEndpointFluxSum I hΦ m (Nstar β) κ T
        (Jcut β) (t, z) := by
    funext z i
    dsimp [hmFrozenTerminalFlux]
    rw [amnrPairEndpointFluxSum_eq_nested I hΦ m (Nstar β)
      κ T (Jcut β) (t, z)]
  have hsliceAt := hpoint.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
  rw [heq]
  exact hsliceAt.differentiableAt

theorem HmPerTimeRegularity.hmPerTime_joint_flowMap_continuous {β : ℝ}
    (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) :
    Continuous (fun p : ℝ × Vec 2 =>
      (p.1, I.xFlow hΦ m 0 p.1 p.2)) := by
  exact continuous_fst.prodMk
    (RelativeError.relative_initial_xFlow_joint_continuous I hΦ m 0)

variable {β : ℝ} (I : Ingredients β)
variable {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)

theorem HmPerTimeRegularity.hmPerTime_flowMap_mem {m : ℕ} {p : ℝ × Vec 2}
    (hp : p ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) :
    (p.1, I.xFlow hΦ m 0 p.1 p.2) ∈
      Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2)) := by
  exact ⟨hp.1, Set.mem_univ _⟩

/-- The regular Piola flux is spatially periodic at positive times. -/
theorem HmPerTimeRegularity.hmPerTime_regularFlux_periodic
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ)
    {t : ℝ} (hTper : IsZ2Periodic (T t)) :
    IsZ2Periodic (hmFrozenRegularFlux I hΦ m κ T t) := by
  have hgrad : IsZ2Periodic (spaceGrad (T t)) :=
    RelativeError.spaceGrad_isZ2Periodic (fun z x => hTper z x)
  intro z x
  simp only [hmFrozenRegularFlux]
  apply tsum_congr
  intro l
  have hF : I.flowGrad hΦ m l t (x + latticeShift z) =
      I.flowGrad hΦ m l t x := by
    ext i j
    exact amnr_flowGrad_spatial_periodic I hΦ m l t i j z x
  rw [hF, hgrad z x]

/-- The divergence of the regular Piola flux is spatially periodic. -/
theorem HmPerTimeRegularity.hmPerTime_piolaSource_periodic
    (m : ℕ) (hm : 1 ≤ m) (κ : ℝ) (T : ℝ → Vec 2 → ℝ)
    {t : ℝ} (hT : ContDiff ℝ ∞ (T t))
    (hTper : IsZ2Periodic (T t)) :
    IsZ2Periodic (hmFrozenPiolaSource I hΦ m κ T t) := by
  have hregular := HmPerTimeRegularity.hmPerTime_regularFlux_periodic I hΦ m κ T hTper
  have hsmooth := LeftJacobian.contDiff_pulledGapFlux I hΦ m hm
    (I.flux κ m t - I.Kmat κ m t) T t hT
  have hgrad (i : Fin 2) : IsZ2Periodic
      (spaceGrad (fun x => hmFrozenRegularFlux I hΦ m κ T t x i)) :=
    RelativeError.spaceGrad_isZ2Periodic (fun z x => congrFun (hregular z x) i)
  intro z x
  unfold hmFrozenPiolaSource vecDiv
  apply Finset.sum_congr rfl
  intro i hi
  exact congrFun (hgrad i z x) i

private theorem hm_positive_time_actual_regular_data_JointSource1 :
  ∀ {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec (2 : ℕ) → ℝ} (hΦ : IsStreamSeq I Φ) {m : ℕ}, (1
    : ℕ) ≤ m → ∀ {κ κprev : ℝ}, (0 : ℝ) < κ → ∀ {θ₀ : Vec (2 : ℕ) → ℝ} {θprev : ℝ → Vec (2 : ℕ)
    → ℝ} {Titer : ℕ → ℝ → Vec (2 : ℕ) → ℝ}, IsClassicalSol (streamVel (Φ (m - (1 : ℕ)))) κprev
    (fun (_ : ℝ) (_ : Vec (2 : ℕ)) => (0 : ℝ)) θ₀ θprev → I.IsTIterates hΦ m κ κprev θ₀ θprev
    Titer →
  let T : ℝ → Vec (2 : ℕ) → ℝ := Titer (Nstar β);
  (∀ (t : ℝ), (0 : ℝ) < t → ContDiff ℝ ∞ (T t)) → ContinuousOn (fun (p : ℝ × Vec (2 : ℕ)) =>
    hmFrozenPiolaSource I hΦ m κ T p.1 p.2) (Ioi (0 : ℝ) ×ˢ univ) ∧ ContinuousOn (fun (p : ℝ ×
    Vec (2 : ℕ)) => vecDiv (sourceErrorD I hΦ m κ T p.1) p.2) (Ioi (0 : ℝ) ×ˢ univ)
    := by
  intro β I Φ hΦ m hm κ κprev hκ θ₀ θprev Titer hθprev hT T hTslice
  have hdiv := AVenhance.Infra.Section5.Contracts.tc_vecDiv_sourceErrorD_continuousOn
    I hΦ m hm hκ hθprev hT
  have hbudget0 (n : ℕ) (_hn : n ∈ Finset.range (Nstar β)) :
      2 + 0 ≤ Nstar β := by
    have hbig := AVenhance.Infra.Ingredients.Nstar_ge_256 I.one_lt_beta I.beta_lt
    exact le_trans (by norm_num) hbig
  have hbudgetJ (n : ℕ) (_hn : n ∈ Finset.range (Nstar β)) :
      2 + Jcut β ≤ Nstar β := by
    have hbig := AVenhance.Infra.Ingredients.Nstar_ge_256 I.one_lt_beta I.beta_lt
    have hN : 1 ≤ Nstar β := by
      exact le_trans (by norm_num) hbig
    have hcut := AVenhance.Infra.Section4.Jcut_budget hN
    have hJ : 1 ≤ Jcut β := by
      unfold Jcut
      omega
    exact le_trans (by omega) hcut
  have hEnd0 := HmPerTimeRegularity.hmPerTime_endpoint_continuousOn I hΦ hm hκ hθprev hT 0
      hbudget0
  have hEndJ := HmPerTimeRegularity.hmPerTime_endpoint_continuousOn I hΦ hm hκ hθprev hT
    (Jcut β) hbudgetJ
  have hPiola : ContinuousOn
      (fun p : ℝ × Vec 2 => hmFrozenPiolaSource I hΦ m κ T p.1 p.2)
      HmPerTimeRegularity.hmPerTimePositiveDomain := by
    have heq (p : ℝ × Vec 2) (hp : p ∈ HmPerTimeRegularity.hmPerTimePositiveDomain) :
        hmFrozenPiolaSource I hΦ m κ T p.1 p.2 =
          hmEndpoint I hΦ m κ T (Jcut β) p.1 p.2 -
            hmEndpoint I hΦ m κ T 0 p.1 p.2 -
            vecDiv (sourceErrorD I hΦ m κ T p.1) p.2 := by
      have ht : 0 < p.1 := hp.1
      have hTreg : ContDiff ℝ ∞ (T p.1) := hTslice p.1 ht
      have hTail := HmPerTimeRegularity.hmPerTime_terminalFlux_differentiable I hΦ hm hκ
        hθprev hT ht p.2
      have hs := hm_frozen_endpoint_difference_source_split I hΦ hm κ T
        hTreg hTail
      linarith
    apply ContinuousOn.congr ((hEndJ.sub hEnd0).sub hdiv)
    intro p hp
    exact heq p hp
  exact ⟨hPiola, hdiv⟩

private theorem hm_positive_time_actual_regular_data_PairingCont1 :
  ∀ {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec (2 : ℕ) → ℝ} (hΦ : IsStreamSeq I Φ) {m : ℕ} {κ
    : ℝ} {Titer : ℕ → ℝ → Vec (2 : ℕ) → ℝ},
  let T : ℝ → Vec (2 : ℕ) → ℝ := Titer (Nstar β);
  ContinuousOn (fun (p : ℝ × Vec (2 : ℕ)) => I.Hm hΦ m κ T p.1 p.2) (Ioi (0 : ℝ) ×ˢ univ) → (∀
    (t : ℝ), (0 : ℝ) < t → IsZ2Periodic (I.Hm hΦ m κ T t)) → (∀ (t : ℝ), (0 : ℝ) < t → ∀ (i :
    Fin (2 : ℕ)), IsZ2Periodic fun (x : Vec (2 : ℕ)) => sourceErrorD I hΦ m κ T t x i) → (∀ (t :
    ℝ), (0 : ℝ) < t → ContDiff ℝ (1 : ℕ∞ω) (sourceErrorD I hΦ m κ T t)) → (∀ (t : ℝ), (0 : ℝ) <
    t → ContDiff ℝ (1 : ℕ∞ω) (I.Hm hΦ m κ T t)) → ContinuousOn (fun (p : ℝ × Vec (2 : ℕ)) =>
    hmFrozenPiolaSource I hΦ m κ T p.1 p.2) (Ioi (0 : ℝ) ×ˢ univ) ∧ ContinuousOn (fun (p : ℝ ×
    Vec (2 : ℕ)) => vecDiv (sourceErrorD I hΦ m κ T p.1) p.2) (Ioi (0 : ℝ) ×ˢ univ) → ∀ (a b :
    ℝ), (0 : ℝ) < a → a ≤ b → ContinuousOn (hmRegularPairing (F := I.Hm hΦ m κ T) (G :=
    hmFrozenPiolaSource I hΦ m κ T)) (Icc a b) ∧ ContinuousOn (hmFluxPairing (F := I.Hm hΦ m κ
    T) (V := sourceErrorD I hΦ m κ T)) (Icc a b)
    := by
  intro β I Φ hΦ m κ Titer T hHmJoint hFper hVper hV hF hJointSource a b ha hab
  have hcell : Set.Icc a b ×ˢ (Set.univ : Set (Vec 2)) ⊆
      Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2)) := by
    rintro ⟨t, x⟩ ⟨ht, _⟩
    exact ⟨lt_of_lt_of_le ha ht.1, Set.mem_univ x⟩
  have hFperCell : ∀ t, t ∈ Set.Icc a b →
      IsZ2Periodic (I.Hm hΦ m κ T t) := by
    intro t ht
    exact hFper t (lt_of_lt_of_le ha ht.1)
  have hVperCell : ∀ t, t ∈ Set.Icc a b → ∀ i : Fin 2,
      IsZ2Periodic (fun x => sourceErrorD I hΦ m κ T t x i) := by
    intro t ht
    exact hVper t (lt_of_lt_of_le ha ht.1)
  have hFCell : ∀ t, t ∈ Set.Icc a b →
      ContDiff ℝ 1 (I.Hm hΦ m κ T t) := by
    intro t ht
    exact hF t (lt_of_lt_of_le ha ht.1)
  have hVCell : ∀ t, t ∈ Set.Icc a b →
      ContDiff ℝ 1 (sourceErrorD I hΦ m κ T t) := by
    intro t ht
    exact hV t (lt_of_lt_of_le ha ht.1)
  exact hm_pairing_continuity_of_joint_fields hab
    (hHmJoint.mono hcell) (hJointSource.1.mono hcell)
    (hJointSource.2.mono hcell) hFperCell hVperCell hFCell hVCell

private theorem hm_positive_time_actual_regular_data_SourcePer2 :
  ∀ {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec (2 : ℕ) → ℝ} (hΦ : IsStreamSeq I Φ) {m : ℕ}, (1
    : ℕ) ≤ m → ∀ {κ κprev : ℝ} {Titer : ℕ → ℝ → Vec (2 : ℕ) → ℝ},
  let T : ℝ → Vec (2 : ℕ) → ℝ := Titer (Nstar β);
  (∀ (t : ℝ), (0 : ℝ) < t → (ContDiff ℝ ∞ (sourceErrorD I hΦ m κ (Titer (Nstar β)) t) ∧
    IsZ2Periodic (sourceErrorD I hΦ m κ (Titer (Nstar β)) t)) ∧ ContDiff ℝ ∞ (iterateError I hΦ
    m κ κprev Titer t) ∧ IsZ2Periodic (iterateError I hΦ m κ κprev Titer t)) → (∀ (t : ℝ), (0 :
    ℝ) < t → ContDiff ℝ ∞ (T t)) → (∀ (t : ℝ), (0 : ℝ) < t → IsZ2Periodic (T t)) → ∀ (t : ℝ), (0
    : ℝ) < t → IsZ2Periodic fun (x : Vec (2 : ℕ)) => hmFrozenPiolaSource I hΦ m κ T t x + vecDiv
    (sourceErrorD I hΦ m κ T t) x
    := by
  intro β I Φ hΦ m hm κ κprev Titer T hsourceData hTslice hTper t ht
  have hTreg : ContDiff ℝ ∞ (T t) := hTslice t ht
  have hregper := HmPerTimeRegularity.hmPerTime_piolaSource_periodic I hΦ m hm κ T
    hTreg (hTper t ht)
  have hvecper := (hsourceData t ht).1.2
  have hdivper : IsZ2Periodic
      (fun x => vecDiv (sourceErrorD I hΦ m κ T t) x) := by
    have hgradper (i : Fin 2) : IsZ2Periodic
        (spaceGrad (fun x => sourceErrorD I hΦ m κ T t x i)) :=
      RelativeError.spaceGrad_isZ2Periodic
        (fun z x => congrFun (hvecper z x) i)
    intro z x
    unfold vecDiv
    apply Finset.sum_congr rfl
    intro i hi
    exact congrFun (hgradper i z x) i
  intro z x
  change hmFrozenPiolaSource I hΦ m κ T t (x + latticeShift z) +
      vecDiv (sourceErrorD I hΦ m κ T t) (x + latticeShift z) =
    hmFrozenPiolaSource I hΦ m κ T t x + vecDiv (sourceErrorD I hΦ m κ T t) x
  exact congrArg₂ (· + ·) (hregper z x) (hdivper z x)

/-- The positive-time regularity and transport data needed by
`frozen_hm_positive_time_bounds_of_pairings_per_time`, for the actual
terminal iterate. The pairing and quantitative bounds remain explicit
arguments of that assembler. -/
theorem hm_positive_time_actual_regular_data
    {m : ℕ} (hm : 1 ≤ m) {κ κprev : ℝ} (hκ : 0 < κ)
    {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {Titer : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev
      (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κ κprev θ₀ θprev Titer) :
    let T := Titer (Nstar β)
    let X : ℝ → PeriodicVolumePreservingDiffeomorphism 2 :=
      fun t => AVenhance.Infra.Section5.LeftToShow.xFlowDiffeo I hΦ m 0 t
    (∀ t, 0 < t → IsZ2Periodic (I.Hm hΦ m κ T t)) ∧
    (∀ t, 0 < t → IsZ2Periodic
      (fun x => hmFrozenPiolaSource I hΦ m κ T t x +
        vecDiv (sourceErrorD I hΦ m κ T t) x)) ∧
    (∀ t, 0 < t → ∀ i : Fin 2,
      IsZ2Periodic (fun x => sourceErrorD I hΦ m κ T t x i)) ∧
    (∀ a b : ℝ, 0 < a → a ≤ b →
      ContinuousOn (hmRegularPairing
        (F := I.Hm hΦ m κ T)
        (G := hmFrozenPiolaSource I hΦ m κ T)) (Set.Icc a b) ∧
      ContinuousOn (hmFluxPairing
        (F := I.Hm hΦ m κ T)
        (V := sourceErrorD I hΦ m κ T)) (Set.Icc a b)) ∧
    ContinuousOn
      (fun p : ℝ × Vec 2 => I.Hm hΦ m κ T p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) ∧
    ContinuousOn
      (fun p : ℝ × Vec 2 => hmFrozenPiolaSource I hΦ m κ T p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) ∧
    ContinuousOn
      (fun p : ℝ × Vec 2 => vecDiv (sourceErrorD I hΦ m κ T p.1) p.2)
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) ∧
    (∀ t, 0 < t → ContDiff ℝ 1 (I.Hm hΦ m κ T t)) ∧
    (∀ t, 0 < t → Continuous (hmFrozenPiolaSource I hΦ m κ T t)) ∧
    (∀ t, 0 < t → ContDiff ℝ 1 (sourceErrorD I hΦ m κ T t)) ∧
    ContinuousOn
      (fun p : ℝ × Vec 2 => I.Hm hΦ m κ T p.1 ((X p.1).toFun p.2))
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) ∧
    ContinuousOn
      (fun p : ℝ × Vec 2 =>
        (fun x => hmFrozenPiolaSource I hΦ m κ T p.1 x +
          vecDiv (sourceErrorD I hΦ m κ T p.1) x)
          ((X p.1).toFun p.2))
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) ∧
    (∀ t, 0 < t → ∀ x,
      HasDerivAt (fun s => I.Hm hΦ m κ T s ((X s).toFun x))
        ((fun y => hmFrozenPiolaSource I hΦ m κ T t y +
          vecDiv (sourceErrorD I hΦ m κ T t) y) ((X t).toFun x)) t) ∧
    (∀ l : ℝ → ℤ,
      (∀ t, t ∈ Set.Ioc (0 : ℝ) 1 →
        0 < hmHalfCellEndpointAt I m l t) →
      ∀ t, t ∈ Set.Ioc (0 : ℝ) 1 →
        ContinuousOn (fun s => Real.sqrt (l2NormSq (I.Hm hΦ m κ T s)))
          (Set.Icc (min (hmHalfCellEndpointAt I m l t) t)
            (max (hmHalfCellEndpointAt I m l t) t))) := by
  dsimp
  let T : ℝ → Vec 2 → ℝ := Titer (Nstar β)
  let X : ℝ → PeriodicVolumePreservingDiffeomorphism 2 :=
    fun t => AVenhance.Infra.Section5.LeftToShow.xFlowDiffeo I hΦ m 0 t
  have hHmOn := Hm_contDiffOn_Ioi_top I hΦ hm hκ hθprev hT
  have hHmJoint : ContinuousOn
      (fun p : ℝ × Vec 2 => I.Hm hΦ m κ T p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) :=
    hHmOn.continuousOn
  have hsourceData (t : ℝ) (ht : 0 < t) :=
    actual_sourceErrors_regular_of_iterates I hΦ m hm κ κprev θ₀ θprev Titer
      hθprev hT ht
  have hFper : ∀ t, 0 < t → IsZ2Periodic (I.Hm hΦ m κ T t) := by
    intro t ht
    exact Hm_periodic_pos I hΦ hm hκ hθprev hT ht
  have hTslice (t : ℝ) (ht : 0 < t) :
      ContDiff ℝ (⊤ : ℕ∞) (T t) := by
    exact tIterate_space_contDiff I hΦ hT hθprev le_rfl ht.le
  have hTper (t : ℝ) (ht : 0 < t) : IsZ2Periodic (T t) :=
    tIterate_periodic I hΦ hT hθprev le_rfl ht.le
  have hVper : ∀ t, 0 < t → ∀ i : Fin 2,
      IsZ2Periodic (fun x => sourceErrorD I hΦ m κ T t x i) := by
    intro t ht i z x
    exact congrFun ((hsourceData t ht).1.2 z x) i
  have hV : ∀ t, 0 < t → ContDiff ℝ 1 (sourceErrorD I hΦ m κ T t) := by
    intro t ht
    exact ((hsourceData t ht).1.1).of_le (by norm_num)
  have hSourcePer : ∀ t, 0 < t → IsZ2Periodic
      (fun x => hmFrozenPiolaSource I hΦ m κ T t x +
        vecDiv (sourceErrorD I hΦ m κ T t) x) := by
    exact @hm_positive_time_actual_regular_data_SourcePer2 β I Φ hΦ m hm κ κprev Titer hsourceData
        hTslice hTper
  have hF : ∀ t, 0 < t → ContDiff ℝ 1 (I.Hm hΦ m κ T t) := by
    intro t ht
    exact (Hm_slice_contDiff_pos I hΦ hm hκ hθprev hT ht).of_le (by norm_num)
  have hG : ∀ t, 0 < t → Continuous (hmFrozenPiolaSource I hΦ m κ T t) := by
    intro t ht
    have hregular := LeftJacobian.contDiff_pulledGapFlux I hΦ m hm
      (I.flux κ m t - I.Kmat κ m t) T t (hTslice t ht)
    have hgrad (i : Fin 2) : Continuous
        (fun x => spaceGrad (fun y => hmFrozenRegularFlux I hΦ m κ T t y i) x i) := by
      have hcont := ((contDiff_pi.1 hregular) i).continuous_fderiv (by simp)
      have hcont' := hcont.clm_apply
        (continuous_const : Continuous (fun _ : Vec 2 => basisVec i))
      change Continuous (fun x => fderiv ℝ
        (fun y => hmFrozenRegularFlux I hΦ m κ T t y i) x (basisVec i))
      exact hcont'
    unfold hmFrozenPiolaSource vecDiv
    exact continuous_finsetSum _ fun i hi => hgrad i
  have hComp : ContinuousOn
      (fun p : ℝ × Vec 2 => I.Hm hΦ m κ T p.1 ((X p.1).toFun p.2))
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) := by
    have hflow : Continuous (fun p : ℝ × Vec 2 =>
        (p.1, (X p.1).toFun p.2)) := by
      convert HmPerTimeRegularity.hmPerTime_joint_flowMap_continuous I hΦ m using 1
      funext p
      simp [X, LeftToShow.xFlowDiffeo_toFun, Ingredients.xFlow]
    have hmapMem : ∀ p ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2)),
        (p.1, (X p.1).toFun p.2) ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2)) := by
      intro p hp
      exact ⟨hp.1, mem_univ _⟩
    have hcomp' := hHmOn.continuousOn.comp hflow.continuousOn hmapMem
    simpa [T, Function.comp_def] using hcomp'
  have hJointSource :
      ContinuousOn
        (fun p : ℝ × Vec 2 => hmFrozenPiolaSource I hΦ m κ T p.1 p.2)
        (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) ∧
      ContinuousOn
        (fun p : ℝ × Vec 2 => vecDiv (sourceErrorD I hΦ m κ T p.1) p.2)
        (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) := by
    exact @hm_positive_time_actual_regular_data_JointSource1 β I Φ hΦ m hm κ κprev hκ θ₀ θprev
        Titer hθprev hT hTslice
  have hrawSource : ContinuousOn
      (fun p : ℝ × Vec 2 => hmFrozenPiolaSource I hΦ m κ T p.1 p.2 +
        vecDiv (sourceErrorD I hΦ m κ T p.1) p.2)
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) :=
    hJointSource.1.add hJointSource.2
  have hSourceComp : ContinuousOn
      (fun p : ℝ × Vec 2 =>
        (fun x => hmFrozenPiolaSource I hΦ m κ T p.1 x +
          vecDiv (sourceErrorD I hΦ m κ T p.1) x)
          ((X p.1).toFun p.2))
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) := by
    have hflow : Continuous (fun p : ℝ × Vec 2 =>
        (p.1, (X p.1).toFun p.2)) := by
      convert HmPerTimeRegularity.hmPerTime_joint_flowMap_continuous I hΦ m using 1
      funext p
      simp [X, LeftToShow.xFlowDiffeo_toFun, Ingredients.xFlow]
    have hmapMem : MapsTo (fun p : ℝ × Vec 2 =>
        (p.1, (X p.1).toFun p.2))
        (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2)))
        (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) := by
      intro p hp
      have h := HmPerTimeRegularity.hmPerTime_flowMap_mem (I := I) (hΦ := hΦ) (m := m) hp
      simpa [X, LeftToShow.xFlowDiffeo_toFun, Ingredients.xFlow] using h
    have hsourceComp' := hrawSource.comp hflow.continuousOn hmapMem
    simpa [T, Function.comp_def] using hsourceComp'
  have hMaterial : ∀ t, 0 < t → ∀ x,
      HasDerivAt (fun s => I.Hm hΦ m κ T s ((X s).toFun x))
        ((fun y => hmFrozenPiolaSource I hΦ m κ T t y +
          vecDiv (sourceErrorD I hΦ m κ T t) y) ((X t).toFun x)) t := by
    intro t ht x
    have hendpoint := RelativeError.relative_initial_Hm_derivative_along_xFlow
      I hΦ hm hκ hθprev hT 0 ht x
    let y := (X t).toFun x
    have hTreg : ContDiff ℝ ∞ (T t) := hTslice t ht
    have hTail := HmPerTimeRegularity.hmPerTime_terminalFlux_differentiable I hΦ hm hκ
      hθprev hT ht y
    have hsplit := hm_frozen_endpoint_difference_source_split I hΦ hm κ T
      hTreg hTail
    have hflowEq : I.xFlow hΦ m 0 t x = (X t).toFun x := by
      simp [X, LeftToShow.xFlowDiffeo_toFun, Ingredients.xFlow]
    have hsplit' :
        hmEndpoint I hΦ m κ T (Jcut β) t ((X t).toFun x) -
          hmEndpoint I hΦ m κ T 0 t ((X t).toFun x) =
        hmFrozenPiolaSource I hΦ m κ T t ((X t).toFun x) +
          vecDiv (sourceErrorD I hΦ m κ T t) ((X t).toFun x) := by
      simpa [y, hflowEq] using hsplit
    exact hendpoint.congr_deriv hsplit'
  have hNormCont : ∀ l : ℝ → ℤ,
      (∀ t, t ∈ Set.Ioc (0 : ℝ) 1 →
        0 < hmHalfCellEndpointAt I m l t) →
      ∀ t, t ∈ Set.Ioc (0 : ℝ) 1 →
        ContinuousOn (fun s => Real.sqrt (l2NormSq (I.Hm hΦ m κ T s)))
          (Set.Icc (min (hmHalfCellEndpointAt I m l t) t)
            (max (hmHalfCellEndpointAt I m l t) t)) := by
    intro l hendpoint t ht
    let c := hmHalfCellEndpointAt I m l t
    have ha : 0 < min c t := lt_min (hendpoint t ht) ht.1
    have hcont := hm_transported_norm_continuous_of_joint
      (F := I.Hm hΦ m κ T) X hFper hComp
      (a := min c t) (b := max c t) ha
    simpa [c] using hcont
  have hPairingCont : ∀ a b : ℝ, 0 < a → a ≤ b →
      ContinuousOn (hmRegularPairing
        (F := I.Hm hΦ m κ T)
        (G := hmFrozenPiolaSource I hΦ m κ T)) (Set.Icc a b) ∧
      ContinuousOn (hmFluxPairing
        (F := I.Hm hΦ m κ T)
        (V := sourceErrorD I hΦ m κ T)) (Set.Icc a b) := by
    exact @hm_positive_time_actual_regular_data_PairingCont1 β I Φ hΦ m κ Titer hHmJoint hFper
        hVper hV hF hJointSource
  exact ⟨hFper, hSourcePer, hVper, hPairingCont, hHmJoint, hJointSource.1,
    hJointSource.2, hF, hG, hV, hComp, hSourceComp, hMaterial, hNormCont⟩

end AVenhance.Infra.Section4

end
