/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ATensorJets
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ATensorBound
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ATensorHm
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LeadingError
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.OpenInputs

/-! # `hLeadingError` from the S-amplitude temperature jets

Composition of the following steps:
* `relative_iterate_gradient_jets` (ATA): the θ_{m-1} profile and the V-increment
  amplitude conclusion, both with amplitude `S`, give the positive spatial jets of `∇T_i` for every
  partial iterate;
* `relative_Amnr_tensor_of_jets` (ATB): the S-amplitude AMNR Hessian tensor estimate,
  from stream-function and diffusivity bounds and the actual recursion;
* `relative_Hm_gradient_actual` (ATC): on open time, `√κ_m‖∇HTilde_m‖ ≤ CH ε^{4δ} S`;
* `relative_leading_error`: the leading-error bound.

The remaining premises are `hT0`, `hT1` and the two named
upstream jets `hTheta` and `hV`, in their exact shapes with amplitude `S`. -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance

/-- `RelativeLeaves.hLeadingError` from the first-order T profile and the S-amplitude jets. -/
theorem relative_leading_error_of_jets (β C₀ A Cs : ℝ) (hA : 1 ≤ A) (hCs : 0 < Cs) :
    ∃ Ca : ℝ, 0 ≤ Ca ∧ ∃ Λ₀ : ℝ, ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ →
      I.Chat ≤ C₀ → Λ₀ ≤ (I.Λ : ℝ) →
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, ∀ hΦ : IsStreamSeq I Φ,
      ∀ κ : ℝ, κ ∈ permissibleSet β I.Λ → ∀ M : ℕ, 1 ≤ M → κ ∈ permittedInterval β I.Λ M →
      ∀ m : ℕ, 2 ≤ m → m ≤ M →
      ∀ (θ₀ : Vec 2 → ℝ) (θprev : ℝ → Vec 2 → ℝ) (T : ℕ → ℝ → Vec 2 → ℝ),
        IsClassicalSol (streamVel (Φ (m - 1))) (I.kappaSeq κ M (m - 1)) (fun _ _ => 0) θ₀ θprev →
        I.IsTIterates hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) θ₀ θprev T →
      let S := Real.sqrt (I.kappaSeq κ M (m - 1)) *
        Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x))
      -- (hT0) √ν ‖∇T‖ ≤ A S
      Integration.TGradientContract β (I.kappaSeq κ M (m - 1)) T A S →
      -- (hT1) the first-order word part of the coordinate energy profile
      Integration.FirstOrderGradJetContract I m (I.kappaSeq κ M (m - 1)) T A S →
      ∀ Rθ : ℝ, epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) ≤ Rθ →
      -- (hTheta) the θ_{m-1} profile, amplitude S
      Integration.ThetaProfileContract I m (I.kappaSeq κ M (m - 1)) θprev Cs S →
      -- (hV) the V-increment amplitude conclusion, amplitude S
      Integration.VIncrementContract I m (I.kappaSeq κ M (m - 1)) T Cs Rθ S →
      Real.sqrt (I.kappaSeq κ M m) * Real.sqrt (spaceTimeGradNormSq (fun s x =>
          spaceGrad (I.ansatz hΦ m (I.kappaSeq κ M m) (T (Nstar β)) s) x -
            LeftToShow.leadingGrad I hΦ m (I.kappaSeq κ M m) (T (Nstar β)) s x)) ≤
        Ca * epsilon β I.Λ (m - 1) ^ (2 * delta β) * S := by
  obtain ⟨Cg, hCg, Λa, hJets⟩ := relative_iterate_gradient_jets β Cs hCs
  obtain ⟨CA, hCA, Λb, hTensor⟩ :=
    relative_Amnr_tensor_of_jets β C₀ Cg (max Cs 1) hCg (le_max_right _ _)
  obtain ⟨CH, hCH, Λc, hHm⟩ := relative_Hm_gradient_actual β C₀ CA hCA
  obtain ⟨Ca, hCa, hLead⟩ := relative_leading_error β C₀ A CH hA hCH
  refine ⟨Ca, hCa, max Λa (max Λb Λc), ?_⟩
  intro I hz hx hh hΛ Φ hΦ κ hκ M hM hperm m hm hmM θ₀ θprev T hθprev hT S hT0 hT1
    Rθ hRθ hTheta hV
  have hΛa : Λa ≤ (I.Λ : ℝ) := (le_max_left _ _).trans hΛ
  have hΛb : Λb ≤ (I.Λ : ℝ) := ((le_max_left _ _).trans (le_max_right _ _)).trans hΛ
  have hΛc : Λc ≤ (I.Λ : ℝ) := ((le_max_right _ _).trans (le_max_right _ _)).trans hΛ
  obtain ⟨K, -, hK⟩ := LeftToShow.left_to_show_scales β C₀
  obtain ⟨hκm, hmono, -⟩ := hK I hz hx hh κ hκ M hM hperm m hm hmM
  have hκp : 0 < I.kappaSeq κ M (m - 1) := hκm.trans_le hmono
  have hS : 0 ≤ S := by positivity
  have hjets := hJets I hΛa Φ hΦ κ M m hm θ₀ θprev T hκm hκp hθprev hT S Rθ hS hRθ hTheta hV
  have htensor := hTensor I hz hx hh hΛb Φ hΦ κ hκ M hM hperm m hm hmM θ₀ θprev T hθprev hT S hS
    hjets
  have hHgrad := hHm I hz hx hh hΛc Φ hΦ κ hκ M hM hperm m hm hmM θ₀ θprev T hθprev hT S hS
    htensor
  exact hLead I hz hx hh Φ hΦ κ hκ M hM hperm m hm hmM θ₀ θprev T hθprev hT hT0 hT1 hHgrad

end AVenhance.Infra.Section5.RelativeError
