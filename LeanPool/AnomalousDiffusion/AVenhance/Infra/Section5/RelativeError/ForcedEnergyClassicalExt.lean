/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ForcedEnergyClassicalReg
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ForcedEnergySmooth
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ForcedEnergyModes

/-!
# Globally continuous extensions of a classical solution and its derivatives

Composing with `t ↦ max t 0` gives continuous functions on all of `ℝ × ℝ²` that agree with the
classical solution, its gradient and its time derivative on `t ≥ 0`. They give the regularity
clauses of the weak-solution predicate.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Homogenization
open scoped Topology

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance.Infra.Parabolic.WeakUniqueness

/-- Extension of a classical solution by `t ↦ max t 0`. -/
def clExt (θ : ℝ → Vec 2 → ℝ) (p : ℝ × Vec 2) : ℝ := θ (max p.1 0) p.2

/-- Extension of the spatial gradient components. -/
def clGradExt (θ : ℝ → Vec 2 → ℝ) (i : Fin 2) (p : ℝ × Vec 2) : ℝ :=
  classicalJointFDeriv θ (max p.1 0, p.2) (0, basisVec i)

/-- Extension of the time derivative. -/
def clTimeExt (θ : ℝ → Vec 2 → ℝ) (p : ℝ × Vec 2) : ℝ :=
  classicalJointFDeriv θ (max p.1 0, p.2) (1, 0)

theorem clMap_continuous : Continuous (fun p : ℝ × Vec 2 => (max p.1 0, p.2)) :=
  (continuous_fst.max continuous_const).prodMk continuous_snd

theorem clMap_mem (p : ℝ × Vec 2) : (max p.1 0, p.2) ∈ classicalHalfSpace :=
  ⟨Set.mem_Ici.mpr (le_max_right _ _), mem_univ _⟩

variable {θ : ℝ → Vec 2 → ℝ}

theorem clExt_continuous
    (hθ : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry θ) classicalHalfSpace) :
    Continuous (clExt θ) :=
  ContinuousOn.comp_continuous hθ.continuousOn clMap_continuous clMap_mem

theorem clJoint_continuous
    (hθ : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry θ) classicalHalfSpace) :
    Continuous (fun p : ℝ × Vec 2 => classicalJointFDeriv θ (max p.1 0, p.2)) :=
  ContinuousOn.comp_continuous (classicalJointFDeriv_continuousOn hθ) clMap_continuous clMap_mem

theorem clGradExt_continuous
    (hθ : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry θ) classicalHalfSpace) (i : Fin 2) :
    Continuous (clGradExt θ i) :=
  (clJoint_continuous hθ).clm_apply continuous_const

theorem clTimeExt_continuous
    (hθ : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry θ) classicalHalfSpace) :
    Continuous (clTimeExt θ) :=
  (clJoint_continuous hθ).clm_apply continuous_const

theorem clExt_eq {p : ℝ × Vec 2} (hp : 0 ≤ p.1) : clExt θ p = θ p.1 p.2 := by
  simp [clExt, max_eq_left hp]

theorem clGradExt_eq (hθ : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry θ) classicalHalfSpace)
    {p : ℝ × Vec 2} (hp : 0 ≤ p.1) (i : Fin 2) :
    clGradExt θ i p = AVenhance.spaceGrad (θ p.1) p.2 i := by
  simp only [clGradExt, max_eq_left hp]
  exact (classical_spaceGrad_eq_joint hθ hp p.2 i).symm

theorem clTimeExt_eq (hθ : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry θ) classicalHalfSpace)
    {p : ℝ × Vec 2} (hp : 0 < p.1) :
    clTimeExt θ p = deriv (fun s => θ s p.2) p.1 := by
  simp only [clTimeExt, max_eq_left hp.le]
  exact (classical_deriv_eq_joint hθ hp p.2).deriv.symm

end AVenhance.Infra.Section5.RelativeError

end
