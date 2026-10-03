/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.WeakEnergyIdentity
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.IndyStepDown
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.ClassicalWellposed
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.AnomalousDissipationA3b

/-!
# Proof of the main theorem, and its conditional assembly from analytic dissipation

`anomalous_dissipation` is the proof of the main theorem (`AVenhance.anomalous_dissipation`): its
statement is the public one without the `IsContinuousIntoHolder` conjunct, which the public
statement derives from this theorem at a larger exponent. It is proved from
the step-down estimate (`AVenhance.indystepdown`) and classical well-posedness
    (`AVenhance.classical_wellposed`)
by `Infra.Section5.Integration.anomalous_dissipation_of_A8_A1c` (the stream-function estimates are
    used inside).
The theorem takes only the range of `α`; the drift and all other inputs are constructed
internally. The module also proves the measurability of Hölder drifts used in the `H¹`
reduction.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open Homogenization

namespace AVenhance.Proofs

theorem AnomalousDissipation.holder_drift_aestronglyMeasurable {α : ℝ}
    {b : ℝ → Vec 2 → Vec 2} (hb : IsHolderClass α b) :
    AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)) := by
  exact hb.2.1.aestronglyMeasurable
    (measurableSet_Icc.prod MeasurableSet.univ)

/-- The main theorem with the drift class `IsHolderClass`; see `AVenhance.anomalous_dissipation`. -/
theorem anomalous_dissipation (α : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) :
    ∃ b : ℝ → Vec 2 → Vec 2, IsHolderClass α b ∧ IsDivFree b ∧
      ∃ ϱ : ℝ → ℝ, (∀ r, 0 < ϱ r ∧ ϱ r ≤ 1) ∧
        ∀ (θ₀ : Vec 2 → ℝ) (Dθ₀ : Vec 2 → Vec 2),
          IsPeriodicH1With θ₀ Dθ₀ → MeanZeroOn unitCube θ₀ →
          ∀ (θ : ℝ → ℝ → Vec 2 → ℝ) (Dθ : ℝ → ℝ → Vec 2 → Vec 2),
            (∀ κ : ℝ, 0 < κ → IsWeakSolutionGrad b κ θ₀ (θ κ) (Dθ κ)) →
            Filter.limsup (fun κ : ℝ => κ * spaceTimeGradNormSq (Dθ κ)) (𝓝[>] 0) ≥
              ϱ (Real.sqrt (l2NormSq θ₀) / Real.sqrt (gradNormSq Dθ₀)) ^ 2 * l2NormSq θ₀ :=
  Infra.Section5.Integration.anomalous_dissipation_of_A8_A1c
    (fun β C₀ => AVenhance.indystepdown β C₀) AVenhance.classical_wellposed α hα₀ hα₁

end AVenhance.Proofs

end
