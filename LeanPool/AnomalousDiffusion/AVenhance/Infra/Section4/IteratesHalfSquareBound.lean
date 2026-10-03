/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesCancellationRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesMatrixMaterialPairing

/-! # Iterates Half Square Bound

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Quantitative transported half-square with its terminal boundary retained.
The primitive bound and actual scalar component energies are the only sizes. -/
theorem iterate_material_half_square_bound
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    {Q : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {H : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hQ : ∀ j k, ContDiffOn ℝ 1 (fun z : AmnrSpace => Q z.1 j k)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hQd : ∀ j k, Continuous (fun t => deriv (fun r => Q r j k) t))
    (hH : ∀ j k, ContDiffOn ℝ 1 (fun z : AmnrSpace => H z.1 z.2 j k)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hHs : ∀ t, 0 < t → ∀ j k, ContDiff ℝ (⊤ : ℕ∞) (fun x => H t x j k))
    (hHp : ∀ t, 0 < t → ∀ j k, IsZ2Periodic (fun x => H t x j k))
    (hQ0 : ∀ j k, Q 0 j k = 0)
    {D G M T s : ℝ} (hD : 0 ≤ D) (hG : 0 ≤ G) (hM : 0 ≤ M)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hQb : ∀ t j k, |Q t j k| ≤ D)
    (hE : ∀ j k, (∫ z in timeCube, (H z.1 z.2 j k) ^ 2) ≤ G ^ 2)
    (hME : ∀ j k, (∫ z in timeCube,
      (amnrMaterial (streamVel φ) (fun t x => H t x j k) z.1 z.2) ^ 2) ≤ M ^ 2)
    (hTE : ∀ j k, l2NormSq (fun x => H s x j k) ≤ T ^ 2) :
    |∫ t in 0..s, ∫ x in unitCube,
      (∑ j : Fin 2, ∑ k : Fin 2, deriv (fun r => Q r j k) t * H t x j k) *
      (∑ j : Fin 2, ∑ k : Fin 2, Q t j k * H t x j k)| ≤
        8 * D ^ 2 * T ^ 2 + 16 * D ^ 2 * M * G := by
  have hc (j k : Fin 2) : Continuous (fun x => H s x j k) :=
    (hH j k).continuousOn.comp_continuous
      (continuous_const.prodMk continuous_id) (fun _ => ⟨hs, Set.mem_univ _⟩)
  have ht := iterate_matrix_contraction_l2_bound (Q s) hc hD (hQb s) hTE
  have hb : ContinuousOn (fun z : AmnrSpace => streamVel φ z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    (AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ).smooth.continuous.continuousOn
  have hp := iterate_terminal_matrix_material_pairing_bound hb hQ hH hD hG hM hs hs1 hQb hE hME
  have he := iterate_material_matrix_square_cancellation_of_smooth hφ hQ hQd hH hHs hHp hs
  simp only [hQ0, zero_mul, Finset.sum_const_zero, l2NormSq, zero_pow (by norm_num : 2 ≠ 0),
      integral_zero, sub_zero] at he
  rw [he]
  have hn : 0 ≤ l2NormSq (fun x => ∑ j : Fin 2, ∑ k : Fin 2, Q s j k * H s x j k) :=
    integral_nonneg (fun _ => sq_nonneg _)
  have ha := abs_add_le (l2NormSq (fun x => ∑ j : Fin 2, ∑ k : Fin 2,
    Q s j k * H s x j k) / 2)
    (-(∫ t in 0..s, ∫ x in unitCube,
      (∑ j : Fin 2, ∑ k : Fin 2, Q t j k *
        amnrMaterial (streamVel φ) (fun r y => H r y j k) t x) *
      (∑ j : Fin 2, ∑ k : Fin 2, Q t j k * H t x j k)))
  rw [abs_neg, abs_of_nonneg (div_nonneg hn (by norm_num))] at ha
  rw [← sub_eq_add_neg] at ha
  unfold l2NormSq at ha ht
  nlinarith only [ha, ht, hp]

end AVenhance.Infra.Section4
