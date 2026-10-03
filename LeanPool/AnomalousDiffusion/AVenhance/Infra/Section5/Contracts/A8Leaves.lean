/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.A8A0Remaining
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.A8LeavesTerms

/-! # Step-down and main theorem from the five leaves

`A8Leaves β C₀` collects the five leaves that remain after the seven relative fields of
`A8Remaining` are derived from the S-amplitude trace (`thetaProfile_S_contract_of_T1h`, the
T/V/HTilde jet producers, the nine abstract-amplitude source producers,
    `relative_leading_error_of_jets`,
`temperatureError_of_thetaProfile_contract`, `initialLayer_from_relative_profiles`).
-/

@[expose] public section

open MeasureTheory Homogenization Filter Topology
noncomputable section
namespace AVenhance.Infra.Section5.Contracts
open AVenhance AVenhance.Infra.Section4 AVenhance.Infra.Section5 Integration

/-- The five leaves of step-down. -/
structure A8Leaves (β C₀ : ℝ) : Prop where
  /-- normie3 at the datum amplitude. -/
  normie3 : ∃ C C₁ : ℝ, OnA7Instances β C₀ C₁ (fun I _Φ hΦ κ M _R θ₀ m _θprev T =>
    Normie3CenteredSourceContract I hΦ m (I.kappaSeq κ M m) T C (Real.sqrt (l2NormSq θ₀)))
  /-- normie3 at the relative amplitude S, gate. -/
  normie3S : ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁ (fun I _Φ hΦ κ M R _θ₀ m _θm θprev T =>
    (6 : ℝ) / 5 ≤ β → epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
    Normie3CenteredSourceContract I hΦ m (I.kappaSeq κ M m) T C
      (Real.sqrt (I.kappaSeq κ M (m - 1)) *
        Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x))))
  /-- HTilde sup at the datum amplitude. -/
  hmSup : ∃ C C₁ : ℝ, OnA7Instances β C₀ C₁
    (fun I _Φ hΦ κ M _R θ₀ m _θprev T => HmSupContract I hΦ m (I.kappaSeq κ M m) θ₀ T C)
  /-- e.Tm.thetam at the datum amplitude. -/
  iterate : ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
    (fun I _Φ _hΦ _κ _M _R θ₀ m _θm θprev T => SectionFourIterateContract I m θ₀ θprev T C)
  /-- The S-amplitude positive initial trace, gate. -/
  t1hTrace : ∃ Ctr : ℝ, 1 ≤ Ctr ∧ ∃ C₁ : ℝ, OnA8Instances β C₀ C₁
    (fun I _Φ _hΦ κ M R θ₀ m _θm θprev _T =>
      (6 : ℝ) / 5 ≤ β → epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
      T1hThetaInitialTraceInput β I κ M m θ₀ θprev Ctr)

/-- **Step-down inputs from the five leaves**: all ten fields of `A8Remaining`. -/
theorem a8Remaining_of_leaves (β C₀ : ℝ) (h : A8Leaves β C₀) : A8Remaining β C₀ :=
  { normie3 := h.normie3
    hmSup := h.hmSup
    iterate := h.iterate
    gradient := a8_gradient_of_trace β C₀ h.t1hTrace
    material := a8_material_of_trace β C₀ h.t1hTrace
    jets := a8_jets_of_trace β C₀ h.t1hTrace
    relative_initial := a8_relative_initial_of_trace β C₀ h.t1hTrace
    terms := a8_terms_of_trace β C₀ h.t1hTrace h.normie3S
    leading := a8_leading_of_trace β C₀ h.t1hTrace
    temperature := a8_temperature_of_trace β C₀ h.t1hTrace }

/-- **Step-down from the five leaves**: the literal step-down statement (both conjuncts). -/
theorem indystepdown_of_leaves (β C₀ : ℝ) (h : A8Leaves β C₀) :
    IndyStepDownStatement β C₀ :=
  indystepdown_of_remaining β C₀ (a8Remaining_of_leaves β C₀ h)

/-- The three step-down leaves left after: both normie3 leaves are produced
(`normie3CenteredSource_datum_closed_contract`, `a8_normie3S_of_trace`). -/
structure A8LeavesLeftJacobian (β C₀ : ℝ) : Prop where
  /-- HTilde sup at the datum amplitude. -/
  hmSup : ∃ C C₁ : ℝ, OnA7Instances β C₀ C₁
    (fun I _Φ hΦ κ M _R θ₀ m _θprev T => HmSupContract I hΦ m (I.kappaSeq κ M m) θ₀ T C)
  /-- e.Tm.thetam at the datum amplitude. -/
  iterate : ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
    (fun I _Φ _hΦ _κ _M _R θ₀ m _θm θprev T => SectionFourIterateContract I m θ₀ θprev T C)
  /-- The S-amplitude positive initial trace, gate. -/
  t1hTrace : ∃ Ctr : ℝ, 1 ≤ Ctr ∧ ∃ C₁ : ℝ, OnA8Instances β C₀ C₁
    (fun I _Φ _hΦ κ M R θ₀ m _θm θprev _T =>
      (6 : ℝ) / 5 ≤ β → epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
      T1hThetaInitialTraceInput β I κ M m θ₀ θprev Ctr)

theorem a8Leaves_of_e53 (β C₀ : ℝ) (h : A8LeavesLeftJacobian β C₀) : A8Leaves β C₀ :=
  { normie3 := normie3CenteredSource_datum_closed_contract β C₀
    normie3S := a8_normie3S_of_trace β C₀ h.t1hTrace
    hmSup := h.hmSup
    iterate := h.iterate
    t1hTrace := h.t1hTrace }

/-- **Step-down from the three leaves.** -/
theorem indystepdown_of_leaves_e53 (β C₀ : ℝ) (h : A8LeavesLeftJacobian β C₀) :
    IndyStepDownStatement β C₀ :=
  indystepdown_of_leaves β C₀ (a8Leaves_of_e53 β C₀ h)

end AVenhance.Infra.Section5.Contracts

end
