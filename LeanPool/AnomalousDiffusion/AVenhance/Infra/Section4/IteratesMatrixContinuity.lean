/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWeightedIntegrability

/-! Natural continuity and integrability of actual matrix pairings. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Actual vector and matrix continuity give joint pairing continuity. -/
theorem iterate_matrix_pairing_continuousOn {a b : AmnrSpace → Vec 2}
    {A : AmnrSpace → Matrix (Fin 2) (Fin 2) ℝ} {S : Set AmnrSpace}
    (ha : ContinuousOn a S) (hb : ContinuousOn b S) (hA : ContinuousOn A S) :
    ContinuousOn (fun z => vecDot (a z) ((A z).mulVec (b z))) S := by
  unfold vecDot Matrix.mulVec dotProduct
  apply continuousOn_finsetSum Finset.univ
  intro i _
  exact ((continuous_apply i).comp_continuousOn ha).mul
    (continuousOn_finsetSum Finset.univ (fun j _ =>
      ((continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn hA)).mul
        ((continuous_apply j).comp_continuousOn hb)))

/-- Natural timeCube integrability requires no quantitative pairing bound. -/
theorem iterate_matrix_pairing_integrable {a b : AmnrSpace → Vec 2}
    {A : AmnrSpace → Matrix (Fin 2) (Fin 2) ℝ}
    (ha : ContinuousOn a (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hb : ContinuousOn b (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hA : ContinuousOn A (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    IntegrableOn (fun z => vecDot (a z) ((A z).mulVec (b z))) timeCube :=
  iterate_timeCube_integrable_of_continuousOn (iterate_matrix_pairing_continuousOn ha hb hA)

end AVenhance.Infra.Section4
