/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesComponentEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWeightedIntegrability

/-! Actual preceding Hessian contraction for the transferred drift error. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

theorem IteratesHessianFactor.four_square_le (a b c d : ℝ) :
    (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith only [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d),
    sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]

/-- Four actual Hessian components control the scalar matrix contraction. -/
theorem iterate_hessian_contraction_sq_bound (Q H : Matrix (Fin 2) (Fin 2) ℝ)
    {D : ℝ} (hD : 0 ≤ D) (hQ : ∀ j k, |Q j k| ≤ D) :
    (∑ j : Fin 2, ∑ k : Fin 2, Q j k * H j k) ^ 2 ≤
      4 * D ^ 2 * ∑ j : Fin 2, ∑ k : Fin 2, (H j k) ^ 2 := by
  have ht : ∀ j k, (Q j k * H j k) ^ 2 ≤ D ^ 2 * (H j k) ^ 2 := by
    intro j k
    have hs := (sq_le_sq₀ (abs_nonneg (Q j k)) hD).mpr (hQ j k)
    simpa only [mul_pow, sq_abs] using mul_le_mul_of_nonneg_right hs (sq_nonneg (H j k))
  have hs := IteratesHessianFactor.four_square_le (Q 0 0 * H 0 0) (Q 0 1 * H 0 1)
    (Q 1 0 * H 1 0) (Q 1 1 * H 1 1)
  simp only [Fin.sum_univ_two] at *
  nlinarith only [hs, ht 0 0, ht 0 1, ht 1 0, ht 1 1]

/-- The actual preceding Hessian factor is continuous up to initial time. -/
theorem iterate_hessian_factor_continuousOn
    {v : ℝ → Vec 2 → ℝ} {Q : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hQc : ContinuousOn Q (Set.Ici (0 : ℝ))) (w : List (Fin 2)) :
    ContinuousOn (fun z : AmnrSpace => ∑ j : Fin 2, ∑ k : Fin 2, Q z.1 j k *
      spaceGrad (fun y => spaceGrad (iterateSpatialWord w (v z.1)) y k) z.2 j)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  have hqc : ContinuousOn (fun z : AmnrSpace => Q z.1) (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    hQc.comp continuousOn_fst (fun _ hz => hz.1)
  have hg (k : Fin 2) := (iterate_word_gradient_smooth_up_to_initial hv (k :: w)).continuousOn
  have hc : ContinuousOn (fun z : AmnrSpace => ∑ j : Fin 2, ∑ k : Fin 2, Q z.1 j k *
      spaceGrad (fun y => spaceGrad (iterateSpatialWord w (v z.1)) y k) z.2 j)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    apply continuousOn_finsetSum Finset.univ
    intro j _
    apply continuousOn_finsetSum Finset.univ
    intro k _
    exact ((continuous_apply k).comp_continuousOn ((continuous_apply j).comp_continuousOn hqc)).mul
      ((continuous_apply j).comp_continuousOn (hg k))
  exact hc

/-- Continuity and the L2 estimate of the actual preceding Hessian factor.
 The only quantitative scalar premises are preceding gradient energies. -/
theorem iterate_hessian_factor_energy_bound
    {v : ℝ → Vec 2 → ℝ} {Q : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hQc : ContinuousOn Q (Set.Ici (0 : ℝ))) (w : List (Fin 2))
    {D G : ℝ} (hD : 0 ≤ D) (hQ : ∀ t j k, |Q t j k| ≤ D)
    (hE : ∀ k : Fin 2,
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord (k :: w) (v t))) ≤ G ^ 2) :
    (∫ z in timeCube, (∑ j : Fin 2, ∑ k : Fin 2, Q z.1 j k *
      spaceGrad (fun y => spaceGrad (iterateSpatialWord w (v z.1)) y k) z.2 j) ^ 2) ≤
      (4 * D * G) ^ 2 := by
  have hc := iterate_hessian_factor_continuousOn hv hQc w
  have hgi (k : Fin 2) := iterate_word_gradient_energy_integrable hv (k :: w)
  have hsumI : IntegrableOn (fun z : AmnrSpace => ∑ k : Fin 2,
      vecNormSq (spaceGrad (iterateSpatialWord (k :: w) (v z.1)) z.2)) timeCube :=
    integrable_finsetSum Finset.univ (fun k _ => hgi k)
  have ht := integral_mono (iterate_timeCube_integrable_of_continuousOn (hc.pow 2))
    (hsumI.const_mul (4 * D ^ 2)) (fun z => by
      have hs := iterate_hessian_contraction_sq_bound (Q z.1)
        (fun j k => spaceGrad (fun y => spaceGrad (iterateSpatialWord w (v z.1)) y k) z.2 j)
        hD (hQ z.1)
      simpa only [Pi.pow_apply, Pi.mul_apply, iterateSpatialWord, vecNormSq, vecDot,
          Fin.sum_univ_two, pow_two,
        mul_comm, add_comm, add_left_comm, add_assoc] using hs)
  simp only [Pi.pow_apply, integral_const_mul, integral_finsetSum Finset.univ (fun k _ => hgi k)]
      at ht
  have he : (∑ k : Fin 2, spaceTimeGradNormSq
      (fun t => spaceGrad (iterateSpatialWord (k :: w) (v t)))) ≤ 2 * G ^ 2 := by
    simpa only [Fin.sum_univ_two, ← two_mul] using add_le_add (hE 0) (hE 1)
  change _ ≤ 4 * D ^ 2 * (∑ k : Fin 2, spaceTimeGradNormSq
      (fun t => spaceGrad (iterateSpatialWord (k :: w) (v t)))) at ht
  have hm := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 4 * D ^ 2)
  have hp : 0 ≤ D ^ 2 * G ^ 2 := by positivity
  nlinarith only [ht, hm, hp]

end AVenhance.Infra.Section4
