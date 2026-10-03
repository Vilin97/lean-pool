/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.H1Reduction
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.A0Facts
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.WeakUniqueness.DivergenceFreeEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.WeakWellposed

/-!
# Divergence-free weak energy identities for §5

The endpoint energy input follows from the weak energy identity for `L²` data. The
well-posedness input is discharged by the weak well-posedness proof.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open Homogenization
open AVenhance.Infra.Parabolic.WeakUniqueness

namespace AVenhance.Infra.Section5

/-- Difference energy identity in the source class used by the §5 reduction. -/
theorem weak_solution_divFree_difference_energy_identity
    (b : ℝ → Vec 2 → Vec 2) {κ : ℝ} {f g : Vec 2 → ℝ}
    {θ η : ℝ → Vec 2 → ℝ} {Dθ Dη : ℝ → Vec 2 → Vec 2}
    (hf : MemL2On AVenhance.unitCube f) (hg : MemL2On AVenhance.unitCube g)
    (hθ : AVenhance.IsWeakSolutionGrad b κ f θ Dθ)
    (hη : AVenhance.IsWeakSolutionGrad b κ g η Dη)
    (hb_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (hb_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ C)
    (hb_per : ∀ t ∈ Set.Icc (0 : ℝ) 1, AVenhance.IsZ2Periodic (b t))
    (hdiv : AVenhance.IsDivFree b) :
    AVenhance.l2NormSq (θ 1 - η 1) +
      2 * κ * AVenhance.spaceTimeGradNormSq (fun t x => Dθ t x - Dη t x) =
        AVenhance.l2NormSq (f - g) := by
  have hdiff := isWeakSolutionGrad_sub hf hg hθ hη
  have hdatum : MemL2On AVenhance.unitCube (fun x => f x - g x) := hf.sub hg
  have henergy := weak_solution_divFree_energy_identity hdiff hdatum
    hb_meas hb_bdd hb_per hdiv 1 ⟨by norm_num, le_rfl⟩
  change AVenhance.l2NormSq (fun x => θ 1 x - η 1 x) +
      2 * κ * (∫ p in Set.Ioo (0 : ℝ) 1 ×ˢ AVenhance.unitCube,
        Homogenization.vecNormSq (Dθ p.1 p.2 - Dη p.1 p.2)) =
    AVenhance.l2NormSq (fun x => f x - g x)
  simpa [AVenhance.spaceTimeGradNormSq, AVenhance.timeCube,
    AVenhance.Infra.Parabolic.WeakUniqueness.weakEnergyRegion] using henergy

/-- §5 `DifferenceEnergyInput`, with the `L²` data hypotheses used by every reduction consumer. -/
theorem differenceEnergyInput_of_divFree_and_l2Data
    (b : ℝ → Vec 2 → Vec 2)
    (hb_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (hb_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ C)
    (hb_per : ∀ t ∈ Set.Icc (0 : ℝ) 1, AVenhance.IsZ2Periodic (b t))
    (hdiv : AVenhance.IsDivFree b) :
    DifferenceEnergyInput b := by
  intro κ hκ f g hf hg θ η Dθ Dη hθ hη
  exact weak_solution_divFree_difference_energy_identity b
    hf hg hθ hη hb_meas hb_bdd hb_per hdiv

/-- The weak well-posedness theorem supplies the existence-and-uniqueness input used by the H¹
    reduction. -/
theorem weakWellposedInput_of_A1
    (b : ℝ → Vec 2 → Vec 2)
    (hb_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (hb_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ C)
    (hb_per : ∀ t ∈ Set.Icc (0 : ℝ) 1, AVenhance.IsZ2Periodic (b t)) :
    WeakWellposedInput b := by
  intro κ hκ θ₀ hθ₀_L2
  exact AVenhance.weak_wellposed b hb_meas hb_bdd hb_per κ hκ θ₀ hθ₀_L2

/-- A weak solution with divergence-free periodic drift satisfies the exact energy input
used by the conditional §5.4 dissipation bound. -/
theorem divFree_energy_dissipation_bound
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {f : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ} {D : ℝ → Vec 2 → Vec 2}
    (hu : AVenhance.IsWeakSolutionGrad b κ f u D)
    (hf : MemL2On AVenhance.unitCube f)
    (hb_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (hb_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ C)
    (hb_per : ∀ t ∈ Set.Icc (0 : ℝ) 1, AVenhance.IsZ2Periodic (b t))
    (hdiv : AVenhance.IsDivFree b) :
    κ * AVenhance.spaceTimeGradNormSq D ≤ AVenhance.l2NormSq f / 2 := by
  apply energy_dissipation_bound_conditional
  · intro t ht
    exact weak_solution_divFree_energy_identity hu hf hb_meas hb_bdd hb_per hdiv t ht

end AVenhance.Infra.Section5

end
