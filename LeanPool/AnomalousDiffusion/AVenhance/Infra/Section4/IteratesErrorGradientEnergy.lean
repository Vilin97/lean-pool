/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesErrorGradient
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesErrorRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesVectorSquares

/-! Actual differentiated material-error energy for the previous increment. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Exact actual error-gradient expansion and the one-jet bound give its
 square in terms of longer error words and the undifferentiated gradient. -/
theorem iterate_material_error_gradient_sq_bound
    {b : ℝ → Vec 2 → Vec 2} {v : ℝ → Vec 2 → ℝ}
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => b z.1 z.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ)) {t : ℝ} (ht : 0 < t)
    (w : List (Fin 2)) (x : Vec 2) {B : ℝ}
    (hB : ∀ j k, |spaceGrad (fun y => b t y k) x j| ≤ B) :
    vecNormSq (spaceGrad (fun y => iterateWordMaterialError (fun z : AmnrSpace => b z.1 z.2) w
      (fun z => v z.1 z.2) (t, y)) x) ≤
      2 * (∑ j : Fin 2, iterateWordMaterialError (fun z : AmnrSpace => b z.1 z.2) (j :: w)
        (fun z => v z.1 z.2) (t, x) ^ 2) +
      8 * B ^ 2 * vecNormSq (spaceGrad (iterateSpatialWord w (v t)) x) := by
  let A : Matrix (Fin 2) (Fin 2) ℝ := fun j k => spaceGrad (fun y => b t y k) x j
  let e : Vec 2 := fun j => iterateWordMaterialError (fun z : AmnrSpace => b z.1 z.2) (j :: w)
    (fun z => v z.1 z.2) (t, x)
  have he : spaceGrad (fun y => iterateWordMaterialError (fun z : AmnrSpace => b z.1 z.2) w
      (fun z => v z.1 z.2) (t, y)) x = e - A.mulVec (spaceGrad (iterateSpatialWord w (v t)) x) := by
    funext j
    exact iterate_material_error_gradient_formula hb hv ht w x j
  rw [he]
  have ht := iterate_vecNormSq_sub_le e (A.mulVec (spaceGrad (iterateSpatialWord w (v t)) x))
  have hm := iterate_matrix_vector_sq_bound A (spaceGrad (iterateSpatialWord w (v t)) x) hB
  have hn : vecNormSq e = ∑ j : Fin 2, e j ^ 2 := by simp only [vecNormSq, vecDot, pow_two]
  rw [hn] at ht
  change vecNormSq _ ≤ 2 * (∑ j : Fin 2, e j ^ 2) + _
  linarith only [ht, hm]

/-- The actual material-error gradient energy requires no differentiated
 error bound as a premise. All natural integrability is proved. -/
theorem iterate_material_error_gradient_energy_bound
    {b : ℝ → Vec 2 → Vec 2} {v : ℝ → Vec 2 → ℝ}
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => b z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (w : List (Fin 2)) {B : ℝ}
    (hB : ∀ t x j k, |spaceGrad (fun y => b t y k) x j| ≤ B) :
    spaceTimeGradNormSq (fun t x => spaceGrad (fun y => iterateWordMaterialError
      (fun z : AmnrSpace => b z.1 z.2) w (fun z => v z.1 z.2) (t, y)) x) ≤
      2 * (∑ j : Fin 2, ∫ z in timeCube, iterateWordMaterialError
        (fun z : AmnrSpace => b z.1 z.2) (j :: w) (fun z => v z.1 z.2) z ^ 2) +
      8 * B ^ 2 * spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord w (v t))) := by
  have hi (j : Fin 2) := iterate_material_error_energy_integrable hb hv (j :: w)
  have hsum := integrable_finsetSum Finset.univ (fun j _ => hi j)
  have hg := iterate_word_gradient_energy_integrable hv w
  have hmono : (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) ⊆
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := fun z hz => ⟨(show 0 < z.1 from hz.1).le, hz.2⟩
  have ht := integral_mono_ae (iterate_material_error_gradient_energy_integrable hb hv w)
    ((hsum.const_mul 2).add (hg.const_mul (8 * B ^ 2))) (by
      apply (ae_restrict_mem iterate_timeCube_isOpen.measurableSet).mono
      intro z hz
      exact iterate_material_error_gradient_sq_bound (hb.mono hmono) (hv.mono hmono) hz.1.1 w z.2
          (hB z.1 z.2))
  have ha := integral_add (hsum.const_mul 2) (hg.const_mul (8 * B ^ 2))
  dsimp only [Pi.add_apply] at ht
  rw [ha, integral_const_mul, integral_const_mul,
    integral_finsetSum Finset.univ (fun j _ => hi j)] at ht
  exact ht

end AVenhance.Infra.Section4
