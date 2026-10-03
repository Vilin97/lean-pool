/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.A8LeavesFields
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.RelativeTerms
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesFlux
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesCutoff
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesTiny
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesTwistie1
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredTwistie4
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredTwistie5
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredNormie3Contract
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.MeanZero
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.HmGradient
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.SourceErrorD

/-! # The relative `terms` field from the trace leaf and normie3 at `S`

The nine source producers at amplitude `S = relS`, all fed by the jet bundle `SJets` at one common
`(Cs, A)` (`a8Core`); `HmGradient` at `S` from the θ profile; `SourceErrorD` from the jets; the
mean-zero contracts from `MeanZero.lean`; `R46` from the gradient contract
(`relativeTerms_contract_of_nine_sources_and_gradient`).  The only extra input is normie3 at `S`.
-/

@[expose] public section

open MeasureTheory Homogenization
noncomputable section
namespace AVenhance.Infra.Section5.Contracts
open AVenhance AVenhance.Infra.Section4 AVenhance.Infra.Section5 Integration

/-- The nine source producers at the relative amplitude, from the trace leaf and normie3. -/
theorem a8_nineSources_of_trace (β C₀ : ℝ) (hTr : A8TraceLeaf β C₀)
    (hN3 : ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
      (fun I _Φ hΦ κ M R _θ₀ m _θm θprev T => (6 : ℝ) / 5 ≤ β →
        epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
        Normie3CenteredSourceContract I hΦ m (I.kappaSeq κ M m) T C
          (Real.sqrt (I.kappaSeq κ M (m - 1)) *
            Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x))))) :
    RelativeNineSourceProducers β C₀ := by
  obtain ⟨CsS, hCsS, hprofG, Cs, A, L, hCsS', hCs1, hA1, hB⟩ := a8Core β C₀ hTr
  have hA0 : 0 ≤ A := zero_le_one.trans hA1
  -- cutoff1
  obtain ⟨C1, -, C1₁, h1⟩ := cutoff1Source_contract β C₀ A hA0
  have h1' : OnA8Instances β C₀ C1₁ (fun I Φ hΦ κ M R θ₀ m θm θprev T =>
      SJetsP β Cs A I Φ hΦ κ M R θ₀ m θm θprev T →
        Cutoff1SourceContract I hΦ m (I.kappaSeq κ M m) T C1 (relS I κ M m θprev)) :=
    OnA8Instances.map (OnA8Instances.of_A7_forall h1) (fun _ _ _ _ _ _ _ _ _ _ _ h hb => h hb.grad)
  -- twistie1
  obtain ⟨C2, -, C2₁, h2⟩ := twistie1HMinusSource_contract β C₀ A hA0
  obtain ⟨Lz2, hz2⟩ := twistie1MeanZero_contract β C₀
  have h2' : OnA8Instances β C₀ C2₁ (fun I Φ hΦ κ M R θ₀ m θm θprev T =>
      SJetsP β Cs A I Φ hΦ κ M R θ₀ m θm θprev T →
        Twistie1MeanZeroContract I hΦ m (I.kappaSeq κ M m) T →
        Twistie1HMinusSourceContract I hΦ m (I.kappaSeq κ M m) T C2 (relS I κ M m θprev)) :=
    OnA8Instances.map (OnA8Instances.of_A7_forall h2)
      (fun _ _ _ _ _ _ _ _ _ _ _ h hb => h hb.pos hb.grad hb.first hb.second)
  have h2'' := OnA8Instances.map₂ h2' (OnA8Instances.of_A7 hz2)
    (Z := fun I Φ hΦ κ M R θ₀ m θm θprev T =>
      SJetsP β Cs A I Φ hΦ κ M R θ₀ m θm θprev T →
        Twistie1HMinusSourceContract I hΦ m (I.kappaSeq κ M m) T C2 (relS I κ M m θprev))
    (fun _ _ _ _ _ _ _ _ _ _ _ h hz hb => h hb hz)
  -- twistie3
  obtain ⟨C3, -, C3₁, h3⟩ := twistie3Source_contract β C₀ A hA0
  have h3' : OnA8Instances β C₀ C3₁ (fun I Φ hΦ κ M R θ₀ m θm θprev T =>
      SJetsP β Cs A I Φ hΦ κ M R θ₀ m θm θprev T →
        Twistie3SourceContract I hΦ m (I.kappaSeq κ M m) T C3 (relS I κ M m θprev)) :=
    OnA8Instances.map (OnA8Instances.of_A7_forall h3) (fun _ _ _ _ _ _ _ _ _ _ _ h hb => h hb.grad)
  -- twistie4
  obtain ⟨C4, -, C4₁, h4⟩ := twistie4CenteredSource_contract β C₀ A hA0
  have h4' : OnA8Instances β C₀ C4₁ (fun I Φ hΦ κ M R θ₀ m θm θprev T =>
      SJetsP β Cs A I Φ hΦ κ M R θ₀ m θm θprev T →
        Twistie4CenteredSourceContract I hΦ m (I.kappaSeq κ M m) T C4 (relS I κ M m θprev)) :=
    OnA8Instances.map (OnA8Instances.of_A7_forall h4)
      (fun _ _ _ _ _ _ _ _ _ _ _ h hb => h hb.pos hb.grad hb.first)
  -- twistie5
  obtain ⟨C5, -, C5₁, h5⟩ := twistie5CenteredSource_contract β C₀ A hA0
  have h5' : OnA8Instances β C₀ C5₁ (fun I Φ hΦ κ M R θ₀ m θm θprev T =>
      SJetsP β Cs A I Φ hΦ κ M R θ₀ m θm θprev T →
        Twistie5CenteredSourceContract I hΦ m (I.kappaSeq κ M m) T C5 (relS I κ M m θprev)) :=
    OnA8Instances.map (OnA8Instances.of_A7_forall h5)
      (fun _ _ _ _ _ _ _ _ _ _ _ h hb => h hb.pos hb.grad hb.first)
  -- normie1
  obtain ⟨C6, -, C6₁, h6⟩ := normie1Source_contract β C₀ A hA0
  have h6' : OnA8Instances β C₀ C6₁ (fun I Φ hΦ κ M R θ₀ m θm θprev T =>
      SJetsP β Cs A I Φ hΦ κ M R θ₀ m θm θprev T →
        Normie1SourceContract I hΦ m (I.kappaSeq κ M m) T C6 (relS I κ M m θprev)) :=
    OnA8Instances.map (OnA8Instances.of_A7_forall h6)
      (fun _ _ _ _ _ _ _ _ _ _ _ h hb => h hb.first hb.grad)
  -- normie2: HTilde gradient from the θ profile
  obtain ⟨Ch, CH, Ch₁, hChS, hCH, hhm⟩ := hmGradient_of_thetaProfile_contract β C₀ CsS hCsS
  obtain ⟨Lh, hPh⟩ := hprofG Ch hChS
  have hHm := OnA8Instances.gate_mp (OnA8Instances.of_A7_forall hhm) hPh
  obtain ⟨C7, -, C7₁, h7⟩ := normie2Source_contract β C₀ CH hCH
  have h7' := OnA8Instances.gate_mp (OnA8Instances.of_A7_forall h7) hHm
  -- tiny
  obtain ⟨Cd, Cd₁, hCd, hsd⟩ := sourceErrorD_of_jets_contract β C₀ Cs A (by linarith) hA0
  have hsd' : OnA8Instances β C₀ Cd₁ (fun I Φ hΦ κ M R θ₀ m θm θprev T =>
      SJetsP β Cs A I Φ hΦ κ M R θ₀ m θm θprev T →
        SourceErrorDContract I hΦ m (I.kappaSeq κ M m) T Cd (relS I κ M m θprev)) :=
    OnA8Instances.map_R (OnA8Instances.of_A7_forall hsd)
      (fun I _ _ _ _ R _ m _ _ _ hR hm h hb =>
        h R (epsilon_radius_le_of_mTheta0 I hR hm) hb.profile hb.vinc hb.grad)
  obtain ⟨Lz8, hz8⟩ := tinyMeanZero_contract β C₀
  obtain ⟨C8, -, C8₁, h8⟩ := tinyHMinusSource_contract β C₀ Cd Cs hCd (by linarith)
  have h8' := OnA8Instances.map_R
    (OnA8Instances.and (OnA8Instances.and hsd' (OnA8Instances.of_A7 hz8))
      (OnA8Instances.of_A7_forall h8))
    (Q := fun I Φ hΦ κ M R θ₀ m θm θprev T =>
      SJetsP β Cs A I Φ hΦ κ M R θ₀ m θm θprev T →
        TinyHMinusSourceContract I hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) T C8
          (relS I κ M m θprev))
    (fun I _ _ _ _ R _ m _ _ _ hR hm h hb =>
      h.2 R (epsilon_radius_le_of_mTheta0 I hR hm) (h.1.1 hb) hb.vinc h.1.2)
  refine
    { cutoff1_source := ⟨C1, _, OnA8Instances.gate_mp h1' hB⟩
      twistie1_source := ⟨C2, _, OnA8Instances.gate_mp h2'' hB⟩
      twistie3_source := ⟨C3, _, OnA8Instances.gate_mp h3' hB⟩
      twistie4_centered_source := ⟨C4, _, OnA8Instances.gate_mp h4' hB⟩
      twistie5_centered_source := ⟨C5, _, OnA8Instances.gate_mp h5' hB⟩
      normie3_centered_source := hN3
      normie1_source := ⟨C6, _, OnA8Instances.gate_mp h6' hB⟩
      normie2_source := ⟨C7, _, h7'⟩
      tiny_source := ⟨C8, _, OnA8Instances.gate_mp h8' hB⟩ }

/-- normie3 at the relative amplitude `S` (gate) from the trace leaf: the producer
`normie3CenteredSource_contract` fed by the S-amplitude jets, as for `twistie5`. -/
theorem a8_normie3S_of_trace (β C₀ : ℝ) (hTr : A8TraceLeaf β C₀) :
    ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
      (fun I _Φ hΦ κ M R _θ₀ m _θm θprev T => (6 : ℝ) / 5 ≤ β →
        epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
        Normie3CenteredSourceContract I hΦ m (I.kappaSeq κ M m) T C
          (Real.sqrt (I.kappaSeq κ M (m - 1)) *
            Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x)))) := by
  obtain ⟨CsS, hCsS, hprofG, Cs, A, L, hCsS', hCs1, hA1, hB⟩ := a8Core β C₀ hTr
  have hA0 : 0 ≤ A := zero_le_one.trans hA1
  obtain ⟨C9, -, C9₁, h9⟩ := normie3CenteredSource_contract β C₀ A hA0
  have h9' : OnA8Instances β C₀ C9₁ (fun I Φ hΦ κ M R θ₀ m θm θprev T =>
      SJetsP β Cs A I Φ hΦ κ M R θ₀ m θm θprev T →
        Normie3CenteredSourceContract I hΦ m (I.kappaSeq κ M m) T C9 (relS I κ M m θprev)) :=
    OnA8Instances.map (OnA8Instances.of_A7_forall h9)
      (fun _ _ _ _ _ _ _ _ _ _ _ h hb => h hb.pos hb.grad hb.first)
  exact ⟨C9, _, OnA8Instances.gate_mp h9' hB⟩

/-- The relative `terms` field from the trace leaf and normie3 at `S`. -/
theorem a8_terms_of_trace (β C₀ : ℝ) (hTr : A8TraceLeaf β C₀)
    (hN3 : ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
      (fun I _Φ hΦ κ M R _θ₀ m _θm θprev T => (6 : ℝ) / 5 ≤ β →
        epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
        Normie3CenteredSourceContract I hΦ m (I.kappaSeq κ M m) T C
          (Real.sqrt (I.kappaSeq κ M (m - 1)) *
            Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x))))) :
    ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
      (fun I _Φ hΦ κ M R _θ₀ m _θm θprev T => (6 : ℝ) / 5 ≤ β →
        epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
        RelativeTermsContract I hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) T C
          (Real.sqrt (I.kappaSeq κ M (m - 1)) *
            Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x)))) :=
  relativeTerms_contract_of_nine_sources_and_gradient β C₀
    (a8_nineSources_of_trace β C₀ hTr hN3) (a8_gradient_of_trace β C₀ hTr)

end AVenhance.Infra.Section5.Contracts

end
