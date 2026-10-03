/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesVelocityRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesComponentEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTruncatedLinearPairing

/-! Linear integrated control of each actual material velocity term. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Each material commutator term uses one actual velocity jet and the
actual lower scalar gradient energy. The second factor may be the primitive
contracted preceding Hessian; only its natural L2 bound is needed. -/
theorem iterate_truncated_velocity_word_term_linear_bound
    {b : ℝ → Vec 2 → Vec 2} {v : ℝ → Vec 2 → ℝ} {a : AmnrSpace → ℝ}
    {s : ℝ} (hs1 : s ≤ 1)
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => b z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (ha : ContinuousOn a (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (r p : List (Fin 2)) (j : Fin 2) {D H G : ℝ}
    (hD : 0 ≤ D) (hH : 0 ≤ H) (hG : 0 ≤ G)
    (hjet : ∀ t x, |iterateSpatialWord r (fun y => b t y j) x| ≤ D)
    (hEa : (∫ z in timeCube, a z ^ 2) ≤ H ^ 2)
    (hEv : spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord p (v t))) ≤ G ^ 2) :
    |∫ z in iterateTruncatedCell s, a z * (iterateSpatialWord r (fun y => b z.1 y j) z.2 *
      spaceGrad (iterateSpatialWord p (v z.1)) z.2 j)| ≤ D * H * G := by
  have hq := (iterateSpatialWord_smooth_up_to_initial (u := fun t x => b t x j)
    (contDiffOn_pi.mp hb j) r).continuousOn
  have hg := (continuous_apply j).comp_continuousOn
    (iterate_word_gradient_smooth_up_to_initial hv p).continuousOn
  exact iterate_truncated_coefficient_linear_pairing_bound hs1 ha hg hq hH hG hD
    (fun z => hjet z.1 z.2) hEa
    ((iterate_word_gradient_component_energy_bound hv p j).trans hEv)

end AVenhance.Infra.Section4
