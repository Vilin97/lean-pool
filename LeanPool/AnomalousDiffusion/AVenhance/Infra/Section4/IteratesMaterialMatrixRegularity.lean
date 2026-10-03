/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesMaterialSquareRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesHessianFactor

/-! Initial-time representatives of actual material matrix contractions. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- A time-only continuous matrix and actual C1 scalar entries give an
integrable square of the material contraction, including the initial boundary. -/
theorem iterate_material_matrix_contraction_square_integrable
    {b : ℝ → Vec 2 → Vec 2} {Q : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {H : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hb : ContinuousOn (fun z : AmnrSpace => b z.1 z.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hQ : ∀ j k, ContinuousOn (fun t => Q t j k) (Set.Ici (0 : ℝ)))
    (hH : ∀ j k, ContDiffOn ℝ 1 (fun z : AmnrSpace => H z.1 z.2 j k)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    IntegrableOn (fun z : AmnrSpace =>
      (∑ j : Fin 2, ∑ k : Fin 2, Q z.1 j k *
        amnrMaterial b (fun t x => H t x j k) z.1 z.2) ^ 2) timeCube := by
  let S : Set AmnrSpace := Set.Ici (0 : ℝ) ×ˢ Set.univ
  let f := fun (j k : Fin 2) (z : AmnrSpace) => H z.1 z.2 j k
  have hS : UniqueDiffOn ℝ S := (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ
  have hc : ContinuousOn (fun z : AmnrSpace => ∑ j : Fin 2, ∑ k : Fin 2,
      Q z.1 j k * fderivWithin ℝ (f j k) S z (1, b z.1 z.2)) S := by
    apply continuousOn_finsetSum Finset.univ
    intro j _
    apply continuousOn_finsetSum Finset.univ
    intro k _
    have hd := (hH j k).continuousOn_fderivWithin hS (by norm_num)
    exact ((hQ j k).comp continuousOn_fst (fun _ hz => hz.1)).mul
      (hd.clm_apply (continuousOn_const.prodMk hb))
  have hi := iterate_timeCube_integrable_of_continuousOn (hc.pow 2)
  change IntegrableOn (fun z : AmnrSpace => (∑ j : Fin 2, ∑ k : Fin 2,
    Q z.1 j k * fderivWithin ℝ (f j k) S z (1, b z.1 z.2)) ^ 2) timeCube at hi
  apply hi.congr
  apply (ae_restrict_mem iterate_timeCube_isOpen.measurableSet).mono
  intro z hz
  apply congrArg (fun r : ℝ => r ^ 2)
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  have hn : S ∈ nhds z := prod_mem_nhds (Ici_mem_nhds hz.1.1) Filter.univ_mem
  have hf := ((hH j k).contDiffAt hn).differentiableAt (by simp)
  rw [fderivWithin_of_mem_nhds (𝕜 := ℝ) (f := f j k) hn]
  exact amnrOp_material (b := fun z : AmnrSpace => b z.1 z.2) hf

/-- Actual entrywise material energies control the actual primitive contraction.
Natural integrability is proved from the C1 carriers, not separately assumed. -/
theorem iterate_material_matrix_contraction_energy_bound
    {b : ℝ → Vec 2 → Vec 2} {Q : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {H : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hb : ContinuousOn (fun z : AmnrSpace => b z.1 z.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hQc : ∀ j k, ContinuousOn (fun t => Q t j k) (Set.Ici (0 : ℝ)))
    (hH : ∀ j k, ContDiffOn ℝ 1 (fun z : AmnrSpace => H z.1 z.2 j k)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) {D G : ℝ} (hD : 0 ≤ D)
    (hQ : ∀ t j k, |Q t j k| ≤ D)
    (hE : ∀ j k, (∫ z in timeCube,
      (amnrMaterial b (fun t x => H t x j k) z.1 z.2) ^ 2) ≤ G ^ 2) :
    (∫ z in timeCube, (∑ j : Fin 2, ∑ k : Fin 2, Q z.1 j k *
      amnrMaterial b (fun t x => H t x j k) z.1 z.2) ^ 2) ≤ (4 * D * G) ^ 2 := by
  have hMi (j k : Fin 2) := iterate_material_square_integrable (u := fun t x => H t x j k) hb (hH
      j k)
  have hsum := integrable_finsetSum Finset.univ (fun j _ =>
    integrable_finsetSum Finset.univ (fun k _ => hMi j k))
  have ht := integral_mono (iterate_material_matrix_contraction_square_integrable hb hQc hH)
    (hsum.const_mul (4 * D ^ 2)) (fun z => iterate_hessian_contraction_sq_bound (Q z.1)
      (fun j k => amnrMaterial b (fun t x => H t x j k) z.1 z.2) hD (hQ z.1))
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun j _ =>
    integrable_finsetSum Finset.univ (fun k _ => hMi j k))] at ht
  simp_rw [integral_finsetSum Finset.univ (fun k _ => hMi _ k)] at ht
  simp only [Fin.sum_univ_two] at ht
  have hsumE := add_le_add (add_le_add (hE 0 0) (hE 0 1)) (add_le_add (hE 1 0) (hE 1 1))
  have hm := mul_le_mul_of_nonneg_left hsumE (by positivity : 0 ≤ 4 * D ^ 2)
  simp only [Fin.sum_univ_two]
  nlinarith only [ht, hm]

end AVenhance.Infra.Section4
