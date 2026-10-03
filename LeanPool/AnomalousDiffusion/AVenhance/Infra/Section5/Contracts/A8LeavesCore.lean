/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.A8LeavesTools
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.ThetaProfile
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TJets
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TJetsSecondOrder
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TMaterialFamily
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TemperatureError
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.RelativeInitialProfile
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ATensor

/-! # The S-amplitude core of step-down and six relative fields from the trace leaf

From the single leaf `t1hTrace` (the S-amplitude positive initial trace under the gate) we
derive the θ profile at every large enough radius constant (`thetaProfile_S_contract_of_T1h`) and a
bundle `SJets` of the T and V contracts at one common coefficient pair `(Cs, A)`; the six relative
fields `gradient`, `material`, `jets`, `relative_initial`, `leading`, `temperature` then follow.
-/

@[expose] public section

open MeasureTheory Homogenization
noncomputable section
namespace AVenhance.Infra.Section5.Contracts
open AVenhance AVenhance.Infra.Section4 AVenhance.Infra.Section5 Integration

/-- The S-amplitude temperature jets of one block instance, at one common `(Cs, A)`. -/
structure SJets {β : ℝ} (I : Ingredients β) (m : ℕ) (κprev : ℝ) (θprev : ℝ → Vec 2 → ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ) (R Cs A S : ℝ) : Prop where
  profile : ThetaProfileContract I m κprev θprev Cs S
  grad : TGradientContract β κprev T A S
  pos : TPositiveJetsContract I m T A S
  first : FirstOrderGradJetContract I m κprev T A S
  second : SecondOrderGradJetContract I m κprev T A S
  vinc : VIncrementContract I m κprev T Cs R S

/-- `SJets` as a block predicate, at the relative amplitude. -/
abbrev SJetsP (β Cs A : ℝ) : A8Pred β :=
  fun I _Φ _hΦ κ M R _θ₀ m _θm θprev T =>
    SJets I m (I.kappaSeq κ M (m - 1)) θprev T R Cs A (relS I κ M m θprev)

/-- The S-amplitude core: the θ profile at every radius constant above `CsS`, and the jet bundle
    at a
common `(Cs, A)`, all under the gate and all derived from the trace leaf. -/
theorem a8Core (β C₀ : ℝ)
    (hTr : ∃ Ctr : ℝ, 1 ≤ Ctr ∧ ∃ C₁ : ℝ, OnA8Instances β C₀ C₁
      (fun I _Φ _hΦ κ M R θ₀ m _θm θprev _T =>
        (6 : ℝ) / 5 ≤ β → epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
        T1hThetaInitialTraceInput β I κ M m θ₀ θprev Ctr)) :
    ∃ CsS : ℝ, 1 ≤ CsS ∧
      (∀ Cs : ℝ, CsS ≤ Cs → ∃ L : ℝ, OnA8Instances β C₀ L
        (fun I _Φ _hΦ κ M R _θ₀ m _θm θprev _T =>
          (6 : ℝ) / 5 ≤ β → epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
          ThetaProfileContract I m (I.kappaSeq κ M (m - 1)) θprev Cs (relS I κ M m θprev))) ∧
      ∃ Cs A L : ℝ, CsS ≤ Cs ∧ 1 ≤ Cs ∧ 1 ≤ A ∧ OnA8Instances β C₀ L
        (fun I _Φ _hΦ κ M R _θ₀ m _θm θprev T =>
          (6 : ℝ) / 5 ≤ β → epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
          SJets I m (I.kappaSeq κ M (m - 1)) θprev T R Cs A (relS I κ M m θprev)) := by
  obtain ⟨Ctr, hCtr, C₁tr, htr⟩ := hTr
  obtain ⟨CsS, hCsS, hprof⟩ := thetaProfile_S_contract_of_T1h β C₀ Ctr hCtr
  have hprofG : ∀ Cs : ℝ, CsS ≤ Cs → OnA8Instances β C₀ (max 0 C₁tr)
      (fun I _Φ _hΦ κ M R _θ₀ m _θm θprev _T =>
        (6 : ℝ) / 5 ≤ β → epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
        ThetaProfileContract I m (I.kappaSeq κ M (m - 1)) θprev Cs (relS I κ M m θprev)) :=
    fun Cs hCs => OnA8Instances.gate_mp (hprof Cs hCs) htr
  obtain ⟨Cs, A, C₁, hCsReq, hCs1, hA1, hjt⟩ := tJets_of_thetaProfile_contract β C₀ CsS
  obtain ⟨Cs₂, A₂, C₂, hCsReq₂, -, hA₂1, hj2⟩ :=
    secondOrderGradJet_of_thetaProfile_contract β C₀ CsS
  have hJ0 : OnA8Instances β C₀ C₁
      (fun I _Φ _hΦ κ M R _θ₀ m _θm θprev T =>
        ThetaProfileContract I m (I.kappaSeq κ M (m - 1)) θprev Cs (relS I κ M m θprev) →
        ThetaProfileContract I m (I.kappaSeq κ M (m - 1)) θprev Cs (relS I κ M m θprev) ∧
          TGradientContract β (I.kappaSeq κ M (m - 1)) T A (relS I κ M m θprev) ∧
          TPositiveJetsContract I m T A (relS I κ M m θprev) ∧
          FirstOrderGradJetContract I m (I.kappaSeq κ M (m - 1)) T A (relS I κ M m θprev) ∧
          VIncrementContract I m (I.kappaSeq κ M (m - 1)) T Cs R (relS I κ M m θprev)) :=
    OnA8Instances.map (OnA8Instances.of_A7_forall hjt)
      (fun _ _ _ _ _ _ _ _ _ _ _ h hp => ⟨hp, (h hp).1, (h hp).2.1, (h hp).2.2.1,
        (h hp).2.2.2.2⟩)
  have hJ := OnA8Instances.gate_mp hJ0 (hprofG Cs hCsReq)
  have hJ2 := OnA8Instances.gate_mp (OnA8Instances.of_A7_forall hj2) (hprofG Cs₂ hCsReq₂)
  have hAll := OnA8Instances.gate_and hJ hJ2
  have hA : 0 ≤ A := zero_le_one.trans hA1
  refine ⟨CsS, hCsS, fun Cs hCs => ⟨_, hprofG Cs hCs⟩, Cs, max A A₂, _, hCsReq, hCs1,
    le_max_of_le_left hA1, OnA8Instances.gate_map hAll ?_⟩
  intro I Φ hΦ κ M R θ₀ m θm θprev T h
  have hS := relS_nonneg I κ M m θprev
  obtain ⟨⟨hp, hg, hpos, hf, hv⟩, hsec⟩ := h
  exact ⟨hp, tGradientContract_mono hg (le_max_left _ _) hS,
    tPositiveJetsContract_mono hpos hA (le_max_left _ _) hS,
    firstOrderGradJetContract_mono hf hA (le_max_left _ _) hS,
    secondOrderGradJetContract_mono hsec (zero_le_one.trans hA₂1) (le_max_right _ _) hS, hv⟩

end AVenhance.Infra.Section5.Contracts

end
