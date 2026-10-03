/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesHessianFactor
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesStreamPairing

/-! Scalar matrix-contraction energies with exact four-component accounting. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Actual continuous matrix entries have a terminal contraction energy bound. -/
theorem iterate_matrix_contraction_l2_bound
    (Q : Matrix (Fin 2) (Fin 2) ℝ) {H : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hH : ∀ j k, Continuous (fun x => H x j k)) {D G : ℝ}
    (hD : 0 ≤ D) (hQ : ∀ j k, |Q j k| ≤ D)
    (hE : ∀ j k, l2NormSq (fun x => H x j k) ≤ G ^ 2) :
    l2NormSq (fun x => ∑ j : Fin 2, ∑ k : Fin 2, Q j k * H x j k) ≤ (4 * D * G) ^ 2 := by
  have hc : Continuous (fun x => ∑ j : Fin 2, ∑ k : Fin 2, Q j k * H x j k) :=
    continuous_finsetSum Finset.univ (fun j _ =>
      continuous_finsetSum Finset.univ (fun k _ => continuous_const.mul (hH j k)))
  have hi (j k : Fin 2) := iterate_continuous_cell_integrable ((hH j k).pow 2)
  change ∀ j k, IntegrableOn (fun x => (H x j k) ^ 2) unitCube at hi
  have hsum := integrable_finsetSum Finset.univ (fun j _ =>
    integrable_finsetSum Finset.univ (fun k _ => hi j k))
  have ht := integral_mono (iterate_continuous_cell_integrable (hc.pow 2))
    (hsum.const_mul (4 * D ^ 2)) (fun x => iterate_hessian_contraction_sq_bound Q (H x) hD hQ)
  dsimp only [Pi.pow_apply] at ht
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun j _ =>
    integrable_finsetSum Finset.univ (fun k _ => hi j k))] at ht
  simp_rw [integral_finsetSum Finset.univ (fun k _ => hi _ k)] at ht
  change l2NormSq (fun x => ∑ j : Fin 2, ∑ k : Fin 2, Q j k * H x j k) ≤
    4 * D ^ 2 * (∑ j : Fin 2, ∑ k : Fin 2, l2NormSq (fun x => H x j k)) at ht
  simp only [Fin.sum_univ_two] at ht
  have hsumE := add_le_add (add_le_add (hE 0 0) (hE 0 1)) (add_le_add (hE 1 0) (hE 1 1))
  have hm := mul_le_mul_of_nonneg_left hsumE (by positivity : 0 ≤ 4 * D ^ 2)
  simp only [Fin.sum_univ_two] at *
  nlinarith only [ht, hm]

/-- The same entrywise accounting applies to the actual full time cell. -/
theorem iterate_matrix_contraction_spacetime_energy_bound
    {Q : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {H : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hQ : ∀ j k, ContinuousOn (fun z : AmnrSpace => Q z.1 j k)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hH : ∀ j k, ContinuousOn (fun z : AmnrSpace => H z.1 z.2 j k)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) {D G : ℝ} (hD : 0 ≤ D)
    (hQb : ∀ t j k, |Q t j k| ≤ D)
    (hE : ∀ j k, (∫ z in timeCube, (H z.1 z.2 j k) ^ 2) ≤ G ^ 2) :
    (∫ z in timeCube, (∑ j : Fin 2, ∑ k : Fin 2, Q z.1 j k * H z.1 z.2 j k) ^ 2) ≤
      (4 * D * G) ^ 2 := by
  have hc : ContinuousOn (fun z : AmnrSpace => ∑ j : Fin 2, ∑ k : Fin 2,
      Q z.1 j k * H z.1 z.2 j k) (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    continuousOn_finsetSum Finset.univ (fun j _ =>
      continuousOn_finsetSum Finset.univ (fun k _ => (hQ j k).mul (hH j k)))
  have hi (j k : Fin 2) := iterate_timeCube_integrable_of_continuousOn ((hH j k).pow 2)
  change ∀ j k, IntegrableOn (fun z : AmnrSpace => (H z.1 z.2 j k) ^ 2) timeCube at hi
  have hsum := integrable_finsetSum Finset.univ (fun j _ =>
    integrable_finsetSum Finset.univ (fun k _ => hi j k))
  have ht := integral_mono (iterate_timeCube_integrable_of_continuousOn (hc.pow 2))
    (hsum.const_mul (4 * D ^ 2)) (fun z =>
      iterate_hessian_contraction_sq_bound (Q z.1) (H z.1 z.2) hD (hQb z.1))
  dsimp only [Pi.pow_apply] at ht
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun j _ =>
    integrable_finsetSum Finset.univ (fun k _ => hi j k))] at ht
  simp_rw [integral_finsetSum Finset.univ (fun k _ => hi _ k)] at ht
  simp only [Fin.sum_univ_two] at ht
  have hsumE := add_le_add (add_le_add (hE 0 0) (hE 0 1)) (add_le_add (hE 1 0) (hE 1 1))
  have hm := mul_le_mul_of_nonneg_left hsumE (by positivity : 0 ≤ 4 * D ^ 2)
  simp only [Fin.sum_univ_two] at *
  nlinarith only [ht, hm]

end AVenhance.Infra.Section4
