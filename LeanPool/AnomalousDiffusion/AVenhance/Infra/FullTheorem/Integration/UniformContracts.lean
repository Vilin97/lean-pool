/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsWeakSolution
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsDivFree
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsPeriodicH1With
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.TimeCube
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.SpaceTimeGradNormSq
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.IsClassicalSol
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.IsThetaAnalytic
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.IsAdmissibleStream
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.StreamVel
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.H1Reduction

/-! # Inputs for the uniform-regularity part (ii) of the combined main theorem

* `ForcedEnergySupContract`: the sup-in-time `L²` form of the stream-difference estimate
  (hypotheses of `Section5.RelativeError.stream_difference_energy`);
* `HeatApproxH1Contract`: `Section5.analytic_approximation` with the extra conjunct that the
  heat approximant does not increase the `H¹` seminorm;
* `WeakDifferenceContract`: the `L²` contraction of the difference of two weak solutions with
  the same divergence-free drift. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance.Infra.FullTheorem

open AVenhance

/-- Sup-in-time `L²` bound for `θ − θ_M`, with the hypotheses of the stream-difference estimate. -/
def ForcedEnergySupContract : Prop :=
  ∀ {b : ℝ → Vec 2 → Vec 2}
    (_hb_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (_hb_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ C)
    (_hb_per : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsZ2Periodic (b t))
    (_hdiv : IsDivFree b)
    {φ : ℝ → Vec 2 → ℝ}
    (_hφ_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => φ p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (_hφ_per : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsZ2Periodic (φ t))
    (_hφ_diff : ∀ t ∈ Set.Icc (0 : ℝ) 1, Differentiable ℝ (φ t))
    (_hbφ : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, b t x = streamVel φ t x)
    {Ψ : ℝ → Vec 2 → ℝ} (_hΨ : IsAdmissibleStream Ψ) {κ : ℝ} (_hκ : 0 < κ)
    {g : Vec 2 → ℝ} (_hg : ContDiff ℝ (⊤ : ℕ∞) g) (_hgp : IsZ2Periodic g)
    {θM : ℝ → Vec 2 → ℝ}
    (_hθM : IsClassicalSol (streamVel Ψ) κ (fun _ _ => 0) g θM)
    {θ : ℝ → Vec 2 → ℝ} {Dθ : ℝ → Vec 2 → Vec 2}
    (_hθ : IsWeakSolutionGrad b κ g θ Dθ)
    {η : ℝ} (_hη : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, |φ t x - Ψ t x| ≤ η),
    ∀ t ∈ Set.Icc (0 : ℝ) 1, Real.sqrt (l2NormSq (fun x => θ t x - θM t x)) ≤
      (η / κ) * (Real.sqrt κ * Real.sqrt (spaceTimeGradNormSq (fun t x => spaceGrad (θM t) x)))

/-- `analytic_approximation` with the additional `H¹` contraction conjunct. -/
def HeatApproxH1Contract : Prop :=
  ∀ {f : Vec 2 → ℝ} {Df : Vec 2 → Vec 2}
    (_hf : IsPeriodicH1With f Df) (_hm : MeanZeroOn unitCube f) (_hA : 0 < l2NormSq f)
    {α : ℝ} (_hα : 0 < α) (_hαsmall : α ≤ 1 / 4),
    ∃ g : Vec 2 → ℝ, MemL2On unitCube g ∧ IsZ2Periodic g ∧ MeanZeroOn unitCube g ∧
      ContDiff ℝ (⊤ : ℕ∞) g ∧
      IsThetaAnalytic (α * Infra.Section5.datumLength f Df / 2) g ∧
      l2NormSq (f - g) ≤ α ^ 2 * l2NormSq f ∧
      l2NormSq f / 4 ≤ l2NormSq g ∧
      gradNormSq (spaceGrad g) ≤ gradNormSq Df

/-- Two weak solutions with the same bounded divergence-free drift: the `L²` distance does not
exceed the `L²` distance of the data, at every time in `[0,1]`. -/
def WeakDifferenceContract : Prop :=
  ∀ {b : ℝ → Vec 2 → Vec 2}
    (_hb_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (_hb_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ C)
    (_hb_per : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsZ2Periodic (b t))
    (_hdiv : IsDivFree b) {κ : ℝ} (_hκ : 0 < κ)
    {f g : Vec 2 → ℝ} (_hf : MemL2On unitCube f) (_hg : MemL2On unitCube g)
    {θ θ' : ℝ → Vec 2 → ℝ} {Dθ Dθ' : ℝ → Vec 2 → Vec 2}
    (_hθ : IsWeakSolutionGrad b κ f θ Dθ) (_hθ' : IsWeakSolutionGrad b κ g θ' Dθ'),
    ∀ t ∈ Set.Icc (0 : ℝ) 1, l2NormSq (fun x => θ t x - θ' t x) ≤ l2NormSq (fun x => f x - g x)

end AVenhance.Infra.FullTheorem
