/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesCancellation
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesCrossIntegrability

/-! Natural integrability of the transported half-square cancellation. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The half-square identity has no separately assumed temporal or material
integrability. Continuous primitive derivatives and the actual C1 carriers
supply every pairing, including the initial boundary. -/
theorem iterate_material_matrix_square_cancellation_of_smooth
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    {Q : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {H : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hQ : ∀ i j, ContDiffOn ℝ 1 (fun z : AmnrSpace => Q z.1 i j)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hQd : ∀ i j, Continuous (fun t => deriv (fun s => Q s i j) t))
    (hH : ∀ i j, ContDiffOn ℝ 1 (fun z : AmnrSpace => H z.1 z.2 i j)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hHs : ∀ t, 0 < t → ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => H t x i j))
    (hHp : ∀ t, 0 < t → ∀ i j, IsZ2Periodic (fun x => H t x i j))
    {s : ℝ} (hs : 0 ≤ s) :
    (∫ t in 0..s, ∫ x in unitCube,
      (∑ i : Fin 2, ∑ j : Fin 2, deriv (fun r => Q r i j) t * H t x i j) *
      (∑ i : Fin 2, ∑ j : Fin 2, Q t i j * H t x i j)) =
      (l2NormSq (fun x => ∑ i : Fin 2, ∑ j : Fin 2, Q s i j * H s x i j) -
        l2NormSq (fun x => ∑ i : Fin 2, ∑ j : Fin 2, Q 0 i j * H 0 x i j)) / 2 -
      (∫ t in 0..s, ∫ x in unitCube,
        (∑ i : Fin 2, ∑ j : Fin 2, Q t i j *
          amnrMaterial (streamVel φ) (fun r y => H r y i j) t x) *
        (∑ i : Fin 2, ∑ j : Fin 2, Q t i j * H t x i j)) := by
  let f := fun t x => ∑ i : Fin 2, ∑ j : Fin 2, Q t i j * H t x i j
  have hf : ContDiffOn ℝ 1 (fun z : AmnrSpace => f z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ => (hQ i j).mul (hH i j)))
  have hb : ContinuousOn (fun z : AmnrSpace => streamVel φ z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    (AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ).smooth.continuous.continuousOn
  have hg : ContinuousOn (fun z : AmnrSpace =>
      (∑ i : Fin 2, ∑ j : Fin 2, deriv (fun r => Q r i j) z.1 * H z.1 z.2 i j) *
      f z.1 z.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    (continuousOn_finsetSum Finset.univ (fun i _ =>
      continuousOn_finsetSum Finset.univ (fun j _ =>
        ((hQd i j).comp continuous_fst).continuousOn.mul (hH i j).continuousOn))).mul
            hf.continuousOn
  have hj (i j : Fin 2) := iterate_material_cross_pairing_integrable
    (u := fun t x => f t x * Q t i j) (v := fun t x => H t x i j) hb
    (hf.continuousOn.mul (hQ i j).continuousOn) (hH i j) hs
  have hJ := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hj i j))
  apply iterate_material_matrix_square_cancellation hφ hQ hH hHs hHp hs
    (iterate_time_cross_pairing_integrable hf.continuousOn hf hs)
    (iterate_time_cell_integrable_of_continuousOn hg hs)
  convert hJ using 1
  funext z
  change (∑ i : Fin 2, ∑ j : Fin 2, Q z.1 i j *
      amnrMaterial (streamVel φ) (fun t x => H t x i j) z.1 z.2) * f z.1 z.2 =
    ∑ i : Fin 2, ∑ j : Fin 2, f z.1 z.2 * Q z.1 i j *
      amnrMaterial (streamVel φ) (fun t x => H t x i j) z.1 z.2
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end AVenhance.Infra.Section4
