/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeInitialDefectContract
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeInitialDefectCorrectorDelta
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeInitialDefectHmJets
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.Scales
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.MStar

/-! Uniform assembly of the exact relative initial-layer contract from the
genuine gradient trace and iterate spatial jets. No Hm estimate is assumed. -/

@[expose] public section

noncomputable section
open MeasureTheory Filter Topology Homogenization AVenhance
open AVenhance.Infra.Section4 AVenhance.Infra.Section5 AVenhance.Infra.Section5.Integration
namespace AVenhance.Infra.Section5.Contracts

/-- Constants precede the step-down estimate data. The only remaining inputs are the initial
n=1 gradient trace and the gradient-only spatial jets of the actual iterates. -/
theorem initialLayer_from_relative_jets (β C₀ Ctrace Cg Cl : ℝ)
    (hCg : 0 ≤ Cg) (hCl : 1 ≤ Cl) :
    ∃ Ci C₁ : ℝ, OnA8Instances β C₀ C₁
      (fun I _Φ hΦ κ M _R g m θm θprev T =>
        let ν := I.kappaSeq κ M (m - 1)
        let S := Real.sqrt ν * Real.sqrt (spaceTimeGradNormSq (fun t x => spaceGrad (θprev t) x))
        (∀ i : Fin 2, Real.sqrt (l2NormSq (fun x => spaceGrad g x i)) ≤
          Ctrace * ((1 : ℕ).factorial : ℝ) *
            (Ctrace / epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2)) ^ (1 : ℕ) * S) →
        (∀ i, i ≤ Nstar β → ∀ (p : Fin 2) (α : List (Fin 2)), α.length ≤ Nstar β →
          eLpNorm (amnrWord (fun y => streamVel (_Φ (m - 1)) y.1 y.2)
              (α.map some) (amnrTGradient (T i) p)) 2
            ((volume.restrict (Set.uIoc 0 1)).prod (volume.restrict unitCube)) ≤
            ENNReal.ofReal (Cg * S / Real.sqrt ν *
              (Cl * epsilon β I.Λ (m - 1) ^ (-(1 + gamma β / 2))) ^ α.length)) →
        InitialLayerContract I hΦ m (I.kappaSeq κ M m) θm T Ci S) := by
  obtain ⟨Ccorr, hCcorr, hcorr⟩ := RelativeError.relative_initial_corrector_delta_uniform β C₀
      Ctrace
  obtain ⟨CH, hCH, ΛH, hHm⟩ := RelativeError.relative_initial_Hm_uniform_of_jets β C₀ Cg Cl hCg hCl
  obtain ⟨K, _, hK⟩ := LeftToShow.left_to_show_scales β C₀
  refine ⟨Ccorr + CH + 1, ΛH, ?_⟩
  intro I hz hx hh hΛ Φ hΦ κ hκp M hM hperm R hR g hg _hgper hmean _hanalytic
    m hm0 hmM θm θprev T hu hp hT
  dsimp only
  intro htrace hjets
  have hm : 2 ≤ m := (mTheta0_spec I.one_lt_beta I.beta_lt I.two_pow_seven_le hR).1.trans hm0
  obtain ⟨hκm, hκle, -⟩ := hK I hz hx hh κ hκp M hM hperm m hm hmM
  have hν : 0 < I.kappaSeq κ M (m - 1) := hκm.trans_le hκle
  let S := Real.sqrt (I.kappaSeq κ M (m - 1)) *
    Real.sqrt (spaceTimeGradNormSq (fun t x => spaceGrad (θprev t) x))
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hcorrector := hcorr I hz hx hh κ hκp M hM hperm m hm hmM Φ hΦ g hg θprev T hT S hS htrace
  have hpositive := hHm I hz hx hh hΛ Φ hΦ κ hκp M hM hperm m hm hmM g θprev T hp hT S hS hjets
  have hb : 0 < tauPP β I.Λ m / 2 :=
    div_pos (Infra.Cutoff.tauPP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le) (by norm_num)
  have hnear : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < tauPP β I.Λ m / 2 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_lt_nhds hb)
  have hHmevent : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      Real.sqrt (l2NormSq (I.Hm hΦ m (I.kappaSeq κ M m) (T (Nstar β)) s)) ≤
        CH * epsilon β I.Λ (m - 1) ^ delta β * S := by
    filter_upwards [hnear, self_mem_nhdsWithin] with s hs hspos
    exact hpositive s ⟨hspos, hs.le⟩
  exact RelativeError.relative_initialLayer_from_estimates I hΦ (by omega) hκm hν hu hp hT hmean
    hcorrector hHmevent

end AVenhance.Infra.Section5.Contracts
