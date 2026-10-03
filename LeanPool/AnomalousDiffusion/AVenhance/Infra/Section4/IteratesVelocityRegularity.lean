/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesVelocityYoung
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWeightedIntegrability

/-! Natural regularity and periodicity of the explicit velocity terms. -/

@[expose] public section

noncomputable section
open Homogenization
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Velocity and scalar periodicity pass to every differentiated split term. -/
theorem iterateVelocitySplit_periodic {b : Vec 2 → Vec 2} {v : Vec 2 → ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hbp : IsZ2Periodic b) (hvp : IsZ2Periodic v)
    (P : List (List (Fin 2) × List (Fin 2))) :
    IsZ2Periodic (iterateVelocitySplit P b v) := by
  intro k x
  unfold iterateVelocitySplit
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply List.map_congr_left
  intro p _
  have hbj := iterateSpatialWord_periodic (contDiff_pi.mp hb j)
    (fun k x => congrFun (hbp k x) j) p.1
  have hgj := iterate_gradient_periodic ((iterateSpatialWord_smooth hv p.2).of_le (by simp))
    (iterateSpatialWord_periodic hv hvp p.2)
  rw [hbj k x, congrFun (hgj k x) j]

/-- Joint continuity of the split sum follows from the actual smooth carriers
up to zero, independently of the material error's ambient derivative at zero. -/
theorem iterateVelocitySplit_continuousOn
    {b : ℝ → Vec 2 → Vec 2} {v : ℝ → Vec 2 → ℝ}
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => b z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (P : List (List (Fin 2) × List (Fin 2))) :
    ContinuousOn (fun z : AmnrSpace => iterateVelocitySplit P (b z.1) (v z.1) z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  have hc : ∀ p ∈ P, ContinuousOn
      (fun z : AmnrSpace => iterateMatrixWord
        (fun y => (fun (_ : Fin 2) j => b z.1 y j : Matrix (Fin 2) (Fin 2) ℝ)) p.1 z.2)
        (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    intro p _
    apply continuousOn_pi.mpr
    intro _
    apply continuousOn_pi.mpr
    intro j
    exact (iterateSpatialWord_smooth_up_to_initial (u := fun t x => b t x j) (contDiffOn_pi.mp hb
        j) p.1).continuousOn
  exact (continuous_apply (0 : Fin 2)).comp_continuousOn
    (iterateSplitFlux_continuousOn_of_jets (A := fun t y => fun (_ : Fin 2) j => b t y j) P hc hv)

end AVenhance.Infra.Section4
