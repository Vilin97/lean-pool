/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWeightedFlux
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesEnergyIntegrability

/-! Space-time forcing estimates for the actual ordered coefficient flux. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

theorem IteratesWeightedSpaceTime.iterate_integrable_list_sum {α : Type*} (P : List α)
    (f : α → AmnrSpace → ℝ) (hf : ∀ p ∈ P, IntegrableOn (f p) timeCube) :
    IntegrableOn (fun z => (P.map (fun p => f p z)).sum) timeCube := by
  induction P with
  | nil => exact integrableOn_zero
  | cons p P ih =>
    exact (hf p List.mem_cons_self).add (ih (fun q hq => hf q (List.mem_cons_of_mem p hq)))

theorem IteratesWeightedSpaceTime.iterate_integral_list_sum {α : Type*} (P : List α)
    (f : α → AmnrSpace → ℝ) (hf : ∀ p ∈ P, IntegrableOn (f p) timeCube) :
    (∫ z in timeCube, (P.map (fun p => f p z)).sum) =
      (P.map (fun p => ∫ z in timeCube, f p z)).sum := by
  induction P with
  | nil => simp
  | cons p P ih =>
    have hp := hf p List.mem_cons_self
    have ht : ∀ q ∈ P, IntegrableOn (f q) timeCube :=
      fun q hq => hf q (List.mem_cons_of_mem p hq)
    simp only [List.map_cons, List.sum_cons]
    rw [integral_add hp (IteratesWeightedSpaceTime.iterate_integrable_list_sum P f ht), ih ht]

/-- Weighted all-order forcing control on the space-time cell.
Integrability premises concern the actual fields; no quantitative forcing
estimate or norm recurrence is assumed. -/
theorem iterate_split_flux_spacetime_pairing_bound
    (P : List (List (Fin 2) × List (Fin 2)))
    (A : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → ℝ)
    (a : ℝ → Vec 2 → Vec 2)
    (ρ D : List (Fin 2) × List (Fin 2) → ℝ)
    (hρ : ∀ p ∈ P, 0 < ρ p)
    (hAj : ∀ t x, ∀ p ∈ P, ∀ i j,
      |iterateSpatialWord p.1 (fun y => A t y i j) x| ≤ D p)
    (ha : IntegrableOn (fun z : AmnrSpace => vecNormSq (a z.1 z.2)) timeCube)
    (hv : ∀ p ∈ P, IntegrableOn (fun z : AmnrSpace =>
      vecNormSq (spaceGrad (iterateSpatialWord p.2 (v z.1)) z.2)) timeCube)
    (hp : IntegrableOn (fun z : AmnrSpace =>
      vecDot (a z.1 z.2) (iterateSplitFlux P (A z.1) (v z.1) z.2)) timeCube) :
    |∫ z in timeCube, vecDot (a z.1 z.2) (iterateSplitFlux P (A z.1) (v z.1) z.2)| ≤
      (P.map ρ).sum * spaceTimeGradNormSq a +
      (P.map (fun p => D p ^ 2 / ρ p * spaceTimeGradNormSq
        (fun t => spaceGrad (iterateSpatialWord p.2 (v t))))).sum := by
  have hterm (p : List (Fin 2) × List (Fin 2)) (h : p ∈ P) :
      IntegrableOn (fun z : AmnrSpace => D p ^ 2 / ρ p *
        vecNormSq (spaceGrad (iterateSpatialWord p.2 (v z.1)) z.2)) timeCube :=
    (hv p h).const_mul _
  have hs := IteratesWeightedSpaceTime.iterate_integrable_list_sum P _ hterm
  have him := integral_mono hp.abs ((ha.const_mul (P.map ρ).sum).add hs)
    (fun z => iterate_split_flux_pairing_abs_bound P (A z.1) (v z.1) z.2
      (a z.1 z.2) ρ D hρ (hAj z.1 z.2))
  change (∫ z in timeCube, |vecDot (a z.1 z.2) (iterateSplitFlux P (A z.1) (v z.1) z.2)|) ≤
    (∫ z in timeCube, (P.map ρ).sum * vecNormSq (a z.1 z.2) +
      (P.map (fun p => D p ^ 2 / ρ p *
        vecNormSq (spaceGrad (iterateSpatialWord p.2 (v z.1)) z.2))).sum) at him
  rw [integral_add (ha.const_mul (P.map ρ).sum) hs, integral_const_mul,
    IteratesWeightedSpaceTime.iterate_integral_list_sum P _ hterm] at him
  simp only [integral_const_mul] at him
  exact abs_integral_le_integral_abs.trans him

end AVenhance.Infra.Section4
