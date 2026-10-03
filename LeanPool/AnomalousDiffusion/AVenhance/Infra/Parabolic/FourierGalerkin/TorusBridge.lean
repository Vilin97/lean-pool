/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.Basic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.Fourier
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.Slicing
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.Calculus
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.FourierCalculus
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.FrozenBridge
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.SpaceGrad

/-!
# Real-valued periodic integration by parts for Galerkin tests

This bridge specializes the landed complex torus-calculus theorem to the real gradient and
the open unit-cell carrier used by the parabolic weak formulation.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open Homogenization

namespace AVenhance.Infra.Parabolic.FourierGalerkin

/-- Closed spatial unit cell used for compactness and periodic integration. -/
def TorusBridge.closedCell : Set (Vec 2) :=
  Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1

theorem TorusBridge.isCompact_closedCell : IsCompact TorusBridge.closedCell := by
  simpa [TorusBridge.closedCell] using (isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc)

theorem TorusBridge.unitCell_subset_closedCell : AVenhance.Infra.Torus.unitCell 2 ⊆
    TorusBridge.closedCell := by
  intro x hx
  simp only [AVenhance.Infra.Torus.unitCell, AVenhance.Infra.Torus.unitCellAt,
    Set.mem_ofPred_eq, zero_add] at hx
  simp only [TorusBridge.closedCell, Set.mem_pi, mem_univ, forall_true_left]
  intro i
  exact ⟨le_of_lt (hx i).1, (hx i).2⟩

theorem TorusBridge.continuousOn_unitCell_integrable {f : Vec 2 → ℝ}
    (hf : Continuous f) : IntegrableOn f (AVenhance.Infra.Torus.unitCell 2) := by
  exact (hf.continuousOn.integrableOn_compact TorusBridge.isCompact_closedCell).mono_set
    TorusBridge.unitCell_subset_closedCell

theorem TorusBridge.realToComplex_periodic {f : Vec 2 → ℝ}
    (hperiodic : AVenhance.IsZ2Periodic f) :
    AVenhance.Infra.Torus.IsZdPeriodic (AVenhance.Infra.Torus.realToComplex f) := by
  intro k x
  have h := (AVenhance.Infra.Torus.isZdPeriodic_iff_frozen f).2 hperiodic k x
  exact congrArg (fun y : ℝ => (y : ℂ)) h

theorem TorusBridge.continuous_spaceGrad_coord {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ ⊤ f) (i : Fin 2) : Continuous (fun x => AVenhance.spaceGrad f x i) := by
  exact (hf.continuous_fderiv (by simp)).clm_apply continuous_const

end AVenhance.Infra.Parabolic.FourierGalerkin

end
