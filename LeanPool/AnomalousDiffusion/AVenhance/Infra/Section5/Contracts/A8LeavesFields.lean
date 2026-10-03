/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.A8LeavesCore

/-! # Six relative fields of `A8Remaining` from the trace leaf

`gradient`, `material`, `jets`, `relative_initial`, `leading`, `temperature`, each derived from
`a8Core` and the corresponding producer.  The trace premise `hTr` is the `t1hTrace` leaf of
`A8Leaves`.
-/

@[expose] public section

open MeasureTheory Homogenization
noncomputable section
namespace AVenhance.Infra.Section5.Contracts
open AVenhance AVenhance.Infra.Section4 AVenhance.Infra.Section5 Integration

/-- The trace leaf (S amplitude, gate). -/
def A8TraceLeaf (β C₀ : ℝ) : Prop :=
  ∃ Ctr : ℝ, 1 ≤ Ctr ∧ ∃ C₁ : ℝ, OnA8Instances β C₀ C₁
    (fun I _Φ _hΦ κ M R θ₀ m _θm θprev _T =>
      (6 : ℝ) / 5 ≤ β → epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
      T1hThetaInitialTraceInput β I κ M m θ₀ θprev Ctr)

theorem a8_gradient_of_trace (β C₀ : ℝ) (hTr : A8TraceLeaf β C₀) :
    ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
      (fun I _Φ _hΦ κ M R _θ₀ m _θm θprev T => (6 : ℝ) / 5 ≤ β →
        epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
        TGradientContract β (I.kappaSeq κ M (m - 1)) T C (Real.sqrt (I.kappaSeq κ M (m - 1)) *
          Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x)))) := by
  obtain ⟨_, _, _, Cs, A, L, _, _, _, hB⟩ := a8Core β C₀ hTr
  exact ⟨A, L, OnA8Instances.gate_map hB (fun _ _ _ _ _ _ _ _ _ _ _ hb => hb.grad)⟩

theorem a8_jets_of_trace (β C₀ : ℝ) (hTr : A8TraceLeaf β C₀) :
    ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
      (fun I _Φ _hΦ κ M R _θ₀ m _θm θprev T => (6 : ℝ) / 5 ≤ β →
        epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
        TPositiveJetsContract I m T C (Real.sqrt (I.kappaSeq κ M (m - 1)) *
          Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x)))) := by
  obtain ⟨_, _, _, Cs, A, L, _, _, _, hB⟩ := a8Core β C₀ hTr
  exact ⟨A, L, OnA8Instances.gate_map hB (fun _ _ _ _ _ _ _ _ _ _ _ hb => hb.pos)⟩

theorem a8_material_of_trace (β C₀ : ℝ) (hTr : A8TraceLeaf β C₀) :
    ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
      (fun I Φ _hΦ κ M R _θ₀ m _θm θprev T => (6 : ℝ) / 5 ≤ β →
        epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
        TMaterialContract I Φ m (I.kappaSeq κ M (m - 1)) T C (Real.sqrt (I.kappaSeq κ M (m - 1)) *
          Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x)))) := by
  obtain ⟨CsS, hCsS, hprofG, -⟩ := a8Core β C₀ hTr
  obtain ⟨Cm, Am, C₁m, hCmReq, -, hjm⟩ := tMaterial_of_thetaProfile_contract β C₀ CsS hCsS
  obtain ⟨Lm, hP⟩ := hprofG Cm hCmReq
  exact ⟨Am, _, OnA8Instances.gate_mp (OnA8Instances.of_A7_forall hjm) hP⟩

theorem a8_relative_initial_of_trace (β C₀ : ℝ) (hTr : A8TraceLeaf β C₀) :
    ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
      (fun I _Φ hΦ κ M R _θ₀ m θm θprev T => (6 : ℝ) / 5 ≤ β →
        epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
        InitialLayerContract I hΦ m (I.kappaSeq κ M m) θm T C
          (Real.sqrt (I.kappaSeq κ M (m - 1)) *
            Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x)))) := by
  obtain ⟨_, _, _, Cs, A, L, _, hCs1, _, hB⟩ := a8Core β C₀ hTr
  obtain ⟨Ci, C₁i, hi⟩ := initialLayer_from_relative_profiles β C₀ A Cs (by linarith)
  have hi' : OnA8Instances β C₀ C₁i
      (fun I _Φ hΦ κ M R _θ₀ m θm θprev T =>
        SJets I m (I.kappaSeq κ M (m - 1)) θprev T R Cs A (relS I κ M m θprev) →
        InitialLayerContract I hΦ m (I.kappaSeq κ M m) θm T Ci (relS I κ M m θprev)) :=
    OnA8Instances.map hi (fun _ _ _ _ _ _ _ _ _ _ _ h hb => h hb.pos hb.profile hb.vinc)
  exact ⟨Ci, _, OnA8Instances.gate_mp hi' hB⟩

theorem a8_leading_of_trace (β C₀ : ℝ) (hTr : A8TraceLeaf β C₀) :
    ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
      (fun I _Φ hΦ κ M R _θ₀ m _θm θprev T => (6 : ℝ) / 5 ≤ β →
        epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
        LeadingErrorContract I hΦ m (I.kappaSeq κ M m) T C (Real.sqrt (I.kappaSeq κ M (m - 1)) *
          Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x)))) := by
  obtain ⟨_, _, _, Cs, A, L, _, hCs1, hA1, hB⟩ := a8Core β C₀ hTr
  obtain ⟨Ca, -, Λ₀, hl⟩ := RelativeError.relative_leading_error_of_jets β C₀ A Cs hA1 (by linarith)
  have hl' : OnA8Instances β C₀ Λ₀
      (fun I _Φ hΦ κ M R _θ₀ m _θm θprev T =>
        SJets I m (I.kappaSeq κ M (m - 1)) θprev T R Cs A (relS I κ M m θprev) →
        LeadingErrorContract I hΦ m (I.kappaSeq κ M m) T Ca (relS I κ M m θprev)) := by
    intro I hz hx hh hΛ Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp hmean ha m hm hmM θm θprev T hθm hθ
      hT hb
    have hm2 : 2 ≤ m := (mTheta0_spec I.one_lt_beta I.beta_lt I.two_pow_seven_le hR).1.trans hm
    exact hl I hz hx hh hΛ Φ hΦ κ hκ M hM hperm m hm2 hmM θ₀ θprev T hθ hT hb.grad hb.first R
      (epsilon_radius_le_of_mTheta0 I hR hm) hb.profile hb.vinc
  exact ⟨Ca, _, OnA8Instances.gate_mp hl' hB⟩

theorem a8_temperature_of_trace (β C₀ : ℝ) (hTr : A8TraceLeaf β C₀) :
    ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
      (fun I _Φ _hΦ κ M R _θ₀ m _θm θprev T => (6 : ℝ) / 5 ≤ β →
        epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
        TemperatureErrorContract I m (I.kappaSeq κ M (m - 1)) θprev T C
          (Real.sqrt (I.kappaSeq κ M (m - 1)) *
            Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x)))) := by
  obtain ⟨CsS, _, hprofG, Cs, A, L, hCsS, hCs1, _, hB⟩ := a8Core β C₀ hTr
  obtain ⟨CsT, Ct, C₁T, hCsT, -, hT⟩ := temperatureError_of_thetaProfile_contract β C₀ Cs hCs1
  obtain ⟨LT, hP⟩ := hprofG CsT (hCsS.trans hCsT)
  have hT' : OnA8Instances β C₀ C₁T
      (fun I _Φ _hΦ κ M R _θ₀ m _θm θprev T =>
        (ThetaProfileContract I m (I.kappaSeq κ M (m - 1)) θprev CsT (relS I κ M m θprev) ∧
          SJets I m (I.kappaSeq κ M (m - 1)) θprev T R Cs A (relS I κ M m θprev)) →
        TemperatureErrorContract I m (I.kappaSeq κ M (m - 1)) θprev T Ct (relS I κ M m θprev)) :=
    OnA8Instances.map_R hT (fun I _ _ κ M R _ m _ θprev T hR _ h hb =>
      h _ (relS_nonneg I κ M m θprev) hb.1
        (vIncrementContract_mono hb.2.vinc (by linarith) hCsT hR (relS_nonneg I κ M m θprev)))
  exact ⟨Ct, _, OnA8Instances.gate_mp hT' (OnA8Instances.gate_and hP hB)⟩

end AVenhance.Infra.Section5.Contracts

end
