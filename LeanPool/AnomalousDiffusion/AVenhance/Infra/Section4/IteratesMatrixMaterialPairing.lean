/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesMaterialMatrixRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesMatrixContractionEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesCrossCell
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesIntegralCauchy

/-! # Iterates Matrix Material Pairing

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The material contraction pairs linearly with the Hessian contraction on
 every terminal cell, using full nonnegative component energies. -/
theorem iterate_terminal_matrix_material_pairing_bound
    {b : ℝ → Vec 2 → Vec 2} {Q : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {H : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hb : ContinuousOn (fun z : AmnrSpace => b z.1 z.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hQ : ∀ j k, ContDiffOn ℝ 1 (fun z : AmnrSpace => Q z.1 j k)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hH : ∀ j k, ContDiffOn ℝ 1 (fun z : AmnrSpace => H z.1 z.2 j k)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {D G M s : ℝ} (hD : 0 ≤ D) (hG : 0 ≤ G) (hM : 0 ≤ M)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hQb : ∀ t j k, |Q t j k| ≤ D)
    (hE : ∀ j k, (∫ z in timeCube, (H z.1 z.2 j k) ^ 2) ≤ G ^ 2)
    (hME : ∀ j k, (∫ z in timeCube,
      (amnrMaterial b (fun t x => H t x j k) z.1 z.2) ^ 2) ≤ M ^ 2) :
    |∫ t in 0..s, ∫ x in unitCube,
      (∑ j : Fin 2, ∑ k : Fin 2, Q t j k *
        amnrMaterial b (fun r y => H r y j k) t x) *
      (∑ j : Fin 2, ∑ k : Fin 2, Q t j k * H t x j k)| ≤ 16 * D ^ 2 * M * G := by
  let f := fun t x => ∑ j : Fin 2, ∑ k : Fin 2, Q t j k * H t x j k
  let a := fun t x => ∑ j : Fin 2, ∑ k : Fin 2,
    Q t j k * amnrMaterial b (fun r y => H r y j k) t x
  have hf : ContinuousOn (fun z : AmnrSpace => f z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    (ContDiffOn.sum (fun j _ => ContDiffOn.sum (fun k _ => (hQ j k).mul (hH j k)))).continuousOn
  have hQc (j k : Fin 2) : ContinuousOn (fun t => Q t j k) (Set.Ici (0 : ℝ)) :=
    (hQ j k).continuousOn.comp (continuousOn_id.prodMk (continuousOn_const (c := (0 : Vec 2))))
      (fun _ ht => ⟨ht, Set.mem_univ _⟩)
  have haI := iterate_material_matrix_contraction_square_integrable hb hQc hH
  have hfI := iterate_timeCube_integrable_of_continuousOn (hf.pow 2)
  have hpI : IntegrableOn (fun z : AmnrSpace => a z.1 z.2 * f z.1 z.2) timeCube := by
    have hi (j k : Fin 2) := iterate_material_cross_timeCube_integrable
      (u := fun t x => f t x * Q t j k) (v := fun t x => H t x j k)
      hb (hf.mul (hQ j k).continuousOn) (hH j k)
    have ht := integrable_finsetSum Finset.univ (fun j _ =>
      integrable_finsetSum Finset.univ (fun k _ => hi j k))
    unfold IntegrableOn
    convert ht using 1
    funext z
    dsimp only [a]
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have haE := iterate_material_matrix_contraction_energy_bound hb hQc hH hD hQb hME
  have hfE := iterate_matrix_contraction_spacetime_energy_bound
    (fun j k => (hQ j k).continuousOn) (fun j k => (hH j k).continuousOn) hD hQb hE
  have hsub := iterateTruncatedCell_subset hs1
  have ht := iterate_integral_pairing_bound
    (by positivity : 0 ≤ 4 * D * M) (by positivity : 0 ≤ 4 * D * G)
    (haI.mono_set hsub) (hfI.mono_set hsub) (hpI.mono_set hsub)
    ((iterate_truncated_nonnegative_integral_le haI (fun _ => sq_nonneg _) hs1).trans haE)
    ((iterate_truncated_nonnegative_integral_le hfI (fun _ => sq_nonneg _) hs1).trans hfE)
  rw [iterate_truncated_integral_eq_interval_of_integrable hpI hs hs1] at ht
  exact ht.trans_eq (by ring)

end AVenhance.Infra.Section4
