/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordForcingFlux
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordFluxEnergy

/-! All-order forcing-gradient energy from preceding L2 gradient energies. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Integrate the explicit forcing-gradient expansion. The only quantitative
scalar premise concerns the preceding field's actual gradient energies. -/
theorem iterate_word_forcing_energy_bound
    {A : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → ℝ}
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hA : ∀ t, 0 < t → ContDiff ℝ (⊤ : ℕ∞) (A t))
    (hcoef : ∀ r : List (Fin 2),
      ContinuousOn (fun z : AmnrSpace => iterateMatrixWord (A z.1) r z.2)
        (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (w : List (Fin 2)) (D E : ℕ → ℝ)
    (hD : ∀ t x r, ∀ j k, |iterateMatrixWord (A t) r x j k| ≤ D r.length)
    (hE : ∀ r : List (Fin 2), r.length ≤ w.length + 2 →
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord r (v t))) ≤ E r.length)
    (hFI : IntegrableOn (fun z : AmnrSpace => vecNormSq (spaceGrad
      (iterateSpatialWord w (vecDiv (fun y => (A z.1 y).mulVec (spaceGrad (v z.1) y)))) z.2))
          timeCube) :
    spaceTimeGradNormSq (fun t => spaceGrad
      (iterateSpatialWord w (vecDiv (fun y => (A t y).mulVec (spaceGrad (v t) y))))) ≤
      64 * ∑ j ∈ Finset.range (w.length + 3),
        (Nat.choose (w.length + 2) j : ℝ) ^ 2 * (2 : ℝ) ^ j * (D j) ^ 2 * E (w.length + 2 - j) := by
  let f := fun (k i : Fin 2) (z : AmnrSpace) =>
    vecNormSq (iterateWordFlux (A z.1) (v z.1) (i :: k :: w) z.2)
  have hf (k i : Fin 2) : IntegrableOn (f k i) timeCube := by
    have hc := iterateSplitFlux_continuousOn_of_jets (iterateSpatialSplits (i :: k :: w))
      (fun p _ => hcoef p.1) hv
    exact iterate_timeCube_integrable_of_continuousOn
      ((iterate_vecNormSq_continuous continuous_id).comp_continuousOn hc)
  have hb (k i : Fin 2) : (∫ z in timeCube, f k i z) ≤
      8 * ∑ j ∈ Finset.range (w.length + 3),
        (Nat.choose (w.length + 2) j : ℝ) ^ 2 * (2 : ℝ) ^ j * (D j) ^ 2 * E (w.length + 2 - j) := by
    have h := iterate_word_flux_energy_bound hv (i :: k :: w) (fun p _ => hcoef p.1) D E
      (fun t x p _ j a => hD t x p.1 j a)
      (fun p hp => hE p.2 (by have hs := iterateSpatialSplits_orders (i :: k :: w) hp; simp only
          [List.length_cons] at hs; omega))
    simpa only [List.length_cons, Nat.add_assoc, Nat.reduceAdd, spaceTimeGradNormSq, f] using h
  have hsum : IntegrableOn (fun z : AmnrSpace => 2 * ∑ k : Fin 2, ∑ i : Fin 2, f k i z) timeCube :=
    ((integrable_finsetSum Finset.univ (fun k _ =>
      integrable_finsetSum Finset.univ (fun i _ => hf k i))).const_mul 2)
  have him := integral_mono_ae hFI hsum
    ((ae_restrict_mem (iterate_timeCube_isOpen.measurableSet)).mono (fun z hz => by
      have hvs : ContDiff ℝ (⊤ : ℕ∞) (v z.1) :=
        hv.comp_contDiff (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (z.1, x)))
          (fun _ => ⟨hz.1.1.le, Set.mem_univ _⟩)
      exact iterate_word_forcing_gradient_flux_sq_bound (hA z.1 hz.1.1) hvs w z.2))
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun k _ =>
    integrable_finsetSum Finset.univ (fun i _ => hf k i))] at him
  simp_rw [integral_finsetSum Finset.univ (fun i _ => hf _ i)] at him
  have hs := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin 2))) =>
    Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 2))) => hb k i))
  have hm := mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 2)
  simp only [Fin.sum_univ_two] at hm
  apply him.trans
  simp only [Fin.sum_univ_two]
  nlinarith only [hm]

end AVenhance.Infra.Section4
