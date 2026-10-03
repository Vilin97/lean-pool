/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.A8Leaves
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.TraceInstanceAdapters
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.SectionFourIterate
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.HmSup

/-! # Step-down producer helper

Step-down (`IndyStepDownStatement`) from the three leaves, two of which are produced here:
`iterate` and the S-amplitude trace. The only remaining hypothesis is the HTilde sup
leaf `HmSupContract` at the datum amplitude. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology
noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5 Integration

/-- The produced S-amplitude trace leaf, in the `A8LeavesLeftJacobian` shape. -/
theorem t1hTrace_leaf_contract (β C₀ : ℝ) :
    ∃ Ctr : ℝ, 1 ≤ Ctr ∧ ∃ C₁ : ℝ, OnA8Instances β C₀ C₁
      (fun I _Φ _hΦ κ M R θ₀ m _θm θprev _T =>
        (6 : ℝ) / 5 ≤ β → epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
        T1hThetaInitialTraceInput β I κ M m θ₀ θprev Ctr) := by
  obtain ⟨Ctr, L, hCtr, h⟩ := RelativeError.e44_uniformTrace_for_T1h_contracts β C₀
  exact ⟨Ctr, hCtr, L, h⟩

/-- **Step-down from the HTilde sup leaf alone** (every other leaf produced). -/
theorem indystepdown_of_hmSup (β C₀ : ℝ)
    (hmSup : ∃ C C₁ : ℝ, OnA7Instances β C₀ C₁
      (fun I _Φ hΦ κ M _R θ₀ m _θprev T => HmSupContract I hΦ m (I.kappaSeq κ M m) θ₀ T C)) :
    IndyStepDownStatement β C₀ :=
  indystepdown_of_leaves_e53 β C₀
    ⟨hmSup, sectionFourIterate_contract β C₀, t1hTrace_leaf_contract β C₀⟩

/-- The HTilde sup leaf from the Piola-source rate family. -/
theorem hmSup_leaf_of_piolaRate (β C₀ : ℝ)
    (hP : ∃ Creg C₁ : ℝ, OnA7Instances β C₀ C₁
      (fun I _Φ hΦ κ M _R θ₀ m _θprev T =>
        HmPiolaSourceRate I hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) T Creg
          (Real.sqrt (l2NormSq θ₀)))) :
    ∃ C C₁ : ℝ, OnA7Instances β C₀ C₁
      (fun I _Φ hΦ κ M _R θ₀ m _θprev T => HmSupContract I hΦ m (I.kappaSeq κ M m) θ₀ T C) := by
  obtain ⟨Creg, C₁, hP⟩ := hP
  obtain ⟨CHs, C₂, hS⟩ := hmSup_contract_onA7_of_piola_source_rate β C₀ Creg
  refine ⟨CHs, max C₁ C₂, ?_⟩
  intro I hz hx hh hΛ Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp hmean ha m hm hmM θprev T hθ hT
  exact hS I hz hx hh ((le_max_right _ _).trans hΛ) Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp hmean ha
    m hm hmM θprev T hθ hT
    (hP I hz hx hh ((le_max_left _ _).trans hΛ) Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp hmean ha
      m hm hmM θprev T hθ hT)

/-- **Step-down from the Piola-source rate alone** (every other leaf produced). -/
theorem indystepdown_of_piolaRate (β C₀ : ℝ)
    (hP : ∃ Creg C₁ : ℝ, OnA7Instances β C₀ C₁
      (fun I _Φ hΦ κ M _R θ₀ m _θprev T =>
        HmPiolaSourceRate I hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) T Creg
          (Real.sqrt (l2NormSq θ₀)))) :
    IndyStepDownStatement β C₀ :=
  indystepdown_of_hmSup β C₀ (hmSup_leaf_of_piolaRate β C₀ hP)

end AVenhance.Infra.Section5.Contracts

end
