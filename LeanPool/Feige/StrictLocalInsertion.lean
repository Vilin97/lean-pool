/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.InsertionTerminalLaw
import LeanPool.Feige.TwoPointReindex

/-!
# Strict local insertion and the strict two-point bound

This module assembles all interior insertion edges with the terminal edge,
then feeds the resulting local insertion principle into the permutation
reduction for an arbitrary (not initially ordered) strict system.
-/

namespace Feige

noncomputable section

/-- The analytic insertion construction realizes the complete strict local
insertion hypothesis used by the ordered induction. -/
theorem strictOrderedLocalInsertion : StrictOrderedLocalInsertion := by
  intro n γ β hγpos hγle hβpos hγord σ g hg
  let Fs : Fin n → List LikelihoodRatio.SignedExpFactor :=
    fun j ↦
      LikelihoodRatio.commonFactors
        (fun i : Fin n ↦ γ i.castSucc)
        (fun i : Fin n ↦ β i.castSucc)
        (fun i ↦ hγpos i.castSucc)
        (fun i ↦ hβpos i.castSucc)
        (chainState σ j.castSucc) (σ j)
  exact exists_insertChainPerm_dominates_reveal_of_realizedEdges
    γ β hγpos hγle hβpos hγord σ hg Fs
    (fun j ↦ realizesInsertionEdge_interior γ β hγpos hβpos σ j)
    (terminalCommonLaw β)
    (terminalCommonLaw_Ioi_zero β hβpos)
    (realizesInsertionEdge_terminal γ β hγpos hβpos σ)

/-- For every strict two-point system, without any prior ordering of its
coordinates, the rejection mass at a nonnegative threshold is at most the
threshold. -/
theorem strictTwoPoint_rejectionMass_le_alpha
    {m : ℕ} (γ β : Fin m → ℝ)
    (hγpos : ∀ i, 0 < γ i) (hγle : ∀ i, γ i ≤ 1)
    (hβpos : ∀ i, 0 < β i)
    {α : ℝ} (hα : 0 ≤ α) :
    twoPointRejectionMass γ β α ≤ α :=
  strictTwoPoint_rejection_le_of_localInsertion
    strictOrderedLocalInsertion γ β hγpos hγle hβpos hα

end

end Feige
