/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.A7DatumClosure
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.A8Assembly
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.AnomalousDissipationA3b
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.InitialLayer
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TJets
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.PartIAnsatz

/-! # Step-down and main theorem from exactly the remaining contracts

`A8Remaining β C₀` collects the still-unproduced inputs of step-down (both conjuncts) — each a
    contract in producer form — and nothing else:
* Big-bound estimate (inside step-down part (i)): `Normie3CenteredSourceContract` at the datum
    amplitude;
* Step-down part (i) at the datum amplitude: `HmSupContract` (feeds both `InitialLayerContract`, via
  `initialLayer_from_HmSup`, and `SectionFourAnsatzContract`, via `section_four_ansatz_bound`) and
  `SectionFourIterateContract`;
* Step-down part (ii) at the relative amplitude `S`, under the gate: the seven relative fields of
  `A8ContractProducers` (`gradient`, `material`, `jets`, `relative_initial`, `terms`, `leading`,
  `temperature`).  All of them reduce to the S-amplitude θ profile, but the
  composition is currently blocked by constant-order mismatches between the θ-profile producer and
      its
  consumers, so they stay hypotheses.
Every other big-bound/step-down input is discharged here by its datum-amplitude producer. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology
noncomputable section
namespace AVenhance.Infra.Section5.Contracts
open AVenhance AVenhance.Infra.Section4 AVenhance.Infra.Section5 Integration

/-- The big-bound estimate producers from the single remaining big-bound estimate contract
    (refactor of `bigbound_of_remaining`). -/
theorem a7Producers_of_remaining (β C₀ : ℝ)
    (hNormie3 : ∃ C C₁ : ℝ, OnA7Instances β C₀ C₁
      (fun I _Φ hΦ κ M _R θ₀ m _θprev T =>
        Normie3CenteredSourceContract I hΦ m (I.kappaSeq κ M m) T C (Real.sqrt (l2NormSq θ₀)))) :
    A7ContractProducers β C₀ :=
  { residual := residual_contract β C₀
    cutoff1_meanZero := cutoff1MeanZero_contract β C₀
    cutoff1_source := cutoff1Source_datum_closed_contract β C₀
    twistie1_hminus_source := twistie1HMinusSource_datum_closed_contract β C₀
    twistie3_flux_smooth := twistie3FluxSmooth_contract β C₀
    twistie3_flux_periodic := twistie3FluxPeriodic_contract β C₀
    twistie3_source := twistie3Source_datum_closed_contract β C₀
    group_meanZero := groupMeanZero_contract β C₀
    twistie4_centered_source := twistie4CenteredSource_datum_closed_contract β C₀
    twistie5_centered_source := twistie5CenteredSource_datum_closed_contract β C₀
    normie3_centered_source := hNormie3
    normie1_flux_smooth := normie1FluxSmooth_contract β C₀
    normie1_flux_periodic := normie1FluxPeriodic_contract β C₀
    normie1_source := normie1Source_datum_closed_contract β C₀
    normie2_flux_smooth := normie2FluxSmooth_contract β C₀
    normie2_flux_periodic := normie2FluxPeriodic_contract β C₀
    normie2_source := normie2Source_datum_closed_contract β C₀
    tiny_hminus_source := tinyHMinusSource_datum_closed_contract β C₀
    R46_flux_smooth := r46FluxSmooth_contract β C₀
    R46_flux_periodic := r46FluxPeriodic_contract β C₀
    R46_source := r46Source_datum_closed_contract β C₀
    term_continuous := termContinuous_contract β C₀ }

/-- Exactly the still-unproduced inputs of step-down (and hence of main theorem, with classical
    well-posedness), each in producer form.
The relative fields are those of `A8ContractProducers` (amplitude `S`, gate). -/
structure A8Remaining (β C₀ : ℝ) : Prop where
  /-- Big-bound estimate slot 8 at the datum amplitude. -/
  normie3 : ∃ C C₁ : ℝ, OnA7Instances β C₀ C₁
    (fun I _Φ hΦ κ M _R θ₀ m _θprev T =>
      Normie3CenteredSourceContract I hΦ m (I.kappaSeq κ M m) T C (Real.sqrt (l2NormSq θ₀)))
  /-- `e.Hm.Linfty` at the datum amplitude. -/
  hmSup : ∃ C C₁ : ℝ, OnA7Instances β C₀ C₁
    (fun I _Φ hΦ κ M _R θ₀ m _θprev T => HmSupContract I hΦ m (I.kappaSeq κ M m) θ₀ T C)
  /-- `e.Tm.thetam` at the datum amplitude. -/
  iterate : ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
    (fun I _Φ _hΦ _κ _M _R θ₀ m _θm θprev T => SectionFourIterateContract I m θ₀ θprev T C)
  /-- Relative `TGradientContract` at `S`. -/
  gradient : ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
    (fun I _Φ _hΦ κ M R _θ₀ m _θm θprev T => (6 : ℝ) / 5 ≤ β →
      epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
      TGradientContract β (I.kappaSeq κ M (m - 1)) T C (Real.sqrt (I.kappaSeq κ M (m - 1)) *
        Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x))))
  /-- Relative `TMaterialContract` at `S`. -/
  material : ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
    (fun I Φ _hΦ κ M R _θ₀ m _θm θprev T => (6 : ℝ) / 5 ≤ β →
      epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
      TMaterialContract I Φ m (I.kappaSeq κ M (m - 1)) T C (Real.sqrt (I.kappaSeq κ M (m - 1)) *
        Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x))))
  /-- Relative `TPositiveJetsContract` at `S`. -/
  jets : ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
    (fun I _Φ _hΦ κ M R _θ₀ m _θm θprev T => (6 : ℝ) / 5 ≤ β →
      epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
      TPositiveJetsContract I m T C (Real.sqrt (I.kappaSeq κ M (m - 1)) *
        Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x))))
  /-- Relative `InitialLayerContract` at `S`. -/
  relative_initial : ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
    (fun I _Φ hΦ κ M R _θ₀ m θm θprev T => (6 : ℝ) / 5 ≤ β →
      epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
      InitialLayerContract I hΦ m (I.kappaSeq κ M m) θm T C
        (Real.sqrt (I.kappaSeq κ M (m - 1)) *
          Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x))))
  /-- Relative `RelativeTermsContract` at `S` (includes slot 8 = normie3 at `S`). -/
  terms : ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
    (fun I _Φ hΦ κ M R _θ₀ m _θm θprev T => (6 : ℝ) / 5 ≤ β →
      epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
      RelativeTermsContract I hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) T C
        (Real.sqrt (I.kappaSeq κ M (m - 1)) *
          Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x))))
  /-- Relative `LeadingErrorContract` at `S`. -/
  leading : ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
    (fun I _Φ hΦ κ M R _θ₀ m _θm θprev T => (6 : ℝ) / 5 ≤ β →
      epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
      LeadingErrorContract I hΦ m (I.kappaSeq κ M m) T C (Real.sqrt (I.kappaSeq κ M (m - 1)) *
        Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x))))
  /-- Relative `TemperatureErrorContract` at `S`. -/
  temperature : ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
    (fun I _Φ _hΦ κ M R _θ₀ m _θm θprev T => (6 : ℝ) / 5 ≤ β →
      epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
      TemperatureErrorContract I m (I.kappaSeq κ M (m - 1)) θprev T C
        (Real.sqrt (I.kappaSeq κ M (m - 1)) *
          Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x))))

/-- The datum `InitialLayerContract` producer from the HTilde sup contract
    (`initialLayer_from_HmSup`). -/
theorem initialLayer_datum_of_hmSup (β C₀ : ℝ)
    (hS : ∃ C C₁ : ℝ, OnA7Instances β C₀ C₁
      (fun I _Φ hΦ κ M _R θ₀ m _θprev T => HmSupContract I hΦ m (I.kappaSeq κ M m) θ₀ T C)) :
    ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
      (fun I _Φ hΦ κ M _R θ₀ m θm _θprev T =>
        InitialLayerContract I hΦ m (I.kappaSeq κ M m) θm T C (Real.sqrt (l2NormSq θ₀))) := by
  obtain ⟨CHs, Ls, hs⟩ := hS
  obtain ⟨Ci, Li, hi⟩ := initialLayer_from_HmSup β C₀ CHs
  refine ⟨Ci, max Ls Li, ?_⟩
  intro I hz hx hh hΛ Φ hΦ κ hκ M hM hperm R hR θ₀ hs0 hp hmean ha m hm hmM θm θprev T hθm hθ hT
  exact hi I hz hx hh ((le_max_right _ _).trans hΛ) Φ hΦ κ hκ M hM hperm R hR θ₀ hs0 hp hmean ha
    m hm hmM θm θprev T hθm hθ hT
    (hs I hz hx hh ((le_max_left _ _).trans hΛ) Φ hΦ κ hκ M hM hperm R hR θ₀ hs0 hp hmean ha
      m hm hmM θprev T hθ hT)

/-- The datum `SectionFourAnsatzContract` producer from the HTilde sup contract and the first-order
slice jet. -/
theorem sectionFourAnsatz_datum_of_hmSup (β C₀ : ℝ)
    (hS : ∃ C C₁ : ℝ, OnA7Instances β C₀ C₁
      (fun I _Φ hΦ κ M _R θ₀ m _θprev T => HmSupContract I hΦ m (I.kappaSeq κ M m) θ₀ T C)) :
    ∃ C C₁ : ℝ, OnA7Instances β C₀ C₁
      (fun I _Φ hΦ κ M _R θ₀ m _θprev T =>
        SectionFourAnsatzContract I hΦ m (I.kappaSeq κ M m) θ₀ T C) := by
  obtain ⟨CHs, Ls, hs⟩ := hS
  obtain ⟨AT, Lj, hj⟩ := firstOrderSliceJet_contract β C₀
  obtain ⟨Ca, _, ha⟩ := section_four_ansatz_bound β C₀ (max AT 0) (max CHs 0)
    (le_max_right _ _) (le_max_right _ _)
  refine ⟨Ca, max Ls Lj, ?_⟩
  intro I hz hx hh hΛ Φ hΦ κ hκ M hM hperm R hR θ₀ hs0 hp hmean hana m hm hmM θprev T hθ hT
  have hm2 : 2 ≤ m := (mTheta0_spec I.one_lt_beta I.beta_lt I.two_pow_seven_le hR).1.trans hm
  have he : 0 < epsilon β I.Λ (m - 1) :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hB : 0 ≤ Real.sqrt (l2NormSq θ₀) := Real.sqrt_nonneg _
  have hjet := hj I hz hx hh ((le_max_right _ _).trans hΛ) Φ hΦ κ hκ M hM hperm R hR θ₀ hs0 hp
    hmean hana m hm hmM θprev T hθ hT
  have hsup := hs I hz hx hh ((le_max_left _ _).trans hΛ) Φ hΦ κ hκ M hM hperm R hR θ₀ hs0 hp
    hmean hana m hm hmM θprev T hθ hT
  have hjet' : FirstOrderSliceJetContract I m T (max AT 0) (Real.sqrt (l2NormSq θ₀)) := by
    intro i s hs'
    refine (hjet i s hs').trans ?_
    have hr : 0 ≤ epsilon β I.Λ (m - 1) ^ (-(1 + gamma β / 2)) := Real.rpow_nonneg he.le _
    gcongr
    exact le_max_left _ _
  have hsup' : HmSupContract I hΦ m (I.kappaSeq κ M m) θ₀ T (max CHs 0) := by
    intro t ht
    refine (hsup t ht).trans ?_
    have hr : 0 ≤ epsilon β I.Λ (m - 1) ^ delta β := Real.rpow_nonneg he.le _
    gcongr
    exact le_max_left _ _
  exact ha I hz hx hh Φ hΦ κ hκ M hM hperm m hm2 hmM θ₀ θprev T hθ hT hjet' hsup'

/-- The step-down estimate producers from exactly the remaining contracts. -/
theorem a8Producers_of_remaining (β C₀ : ℝ) (h : A8Remaining β C₀) : A8ContractProducers β C₀ :=
  { initial := initialLayer_datum_of_hmSup β C₀ h.hmSup
    ansatz := sectionFourAnsatz_datum_of_hmSup β C₀ h.hmSup
    iterate := h.iterate
    gradient := h.gradient
    material := h.material
    jets := h.jets
    relative_initial := h.relative_initial
    terms := h.terms
    leading := h.leading
    temperature := h.temperature }

/-- **Step-down from the remaining contracts**: the literal step-down statement (both conjuncts). -/
theorem indystepdown_of_remaining (β C₀ : ℝ) (h : A8Remaining β C₀) :
    IndyStepDownStatement β C₀ :=
  indystepdown_of_contracts β C₀ (a7Producers_of_remaining β C₀ h.normie3)
    (a8Producers_of_remaining β C₀ h)

end AVenhance.Infra.Section5.Contracts
