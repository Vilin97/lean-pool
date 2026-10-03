/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesVelocityRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesComponentEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesIntegralCauchy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWeightedIntegrability
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesPositiveGrouping

/-! Integrated all-order drift errors with linear lower-energy dependence. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

theorem IteratesVelocityEnergy.velocity_list_integrable {α : Type*} (P : List α) (f : α →
    AmnrSpace → ℝ)
    (hf : ∀ p ∈ P, IntegrableOn (f p) timeCube) :
    IntegrableOn (fun z => (P.map (fun p => f p z)).sum) timeCube := by
  induction P with
  | nil => exact integrableOn_zero
  | cons p P ih =>
    exact (hf p List.mem_cons_self).add
      (ih (fun q hq => hf q (List.mem_cons_of_mem p hq)))

theorem IteratesVelocityEnergy.velocity_list_integral {α : Type*} (P : List α) (f : α → AmnrSpace
    → ℝ)
    (hf : ∀ p ∈ P, IntegrableOn (f p) timeCube) :
    (∫ z in timeCube, (P.map (fun p => f p z)).sum) =
      (P.map (fun p => ∫ z in timeCube, f p z)).sum := by
  induction P with
  | nil => simp
  | cons p P ih =>
    have ht : ∀ q ∈ P, IntegrableOn (f q) timeCube := fun q hq => hf q (List.mem_cons_of_mem p hq)
    simp only [List.map_cons, List.sum_cons]
    rw [integral_add (hf p List.mem_cons_self) (IteratesVelocityEnergy.velocity_list_integrable P
        f ht), ih ht]

theorem IteratesVelocityEnergy.velocity_list_abs_sum {α : Type*} (P : List α) (f : α → ℝ) :
    |(P.map f).sum| ≤ (P.map (fun p => |f p|)).sum := by
  induction P with
  | nil => simp
  | cons p P ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (abs_add_le _ _).trans (add_le_add le_rfl ih)

end AVenhance.Infra.Section4
