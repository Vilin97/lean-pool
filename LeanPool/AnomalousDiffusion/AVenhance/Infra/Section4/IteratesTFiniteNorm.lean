/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesL2FiniteTriangle
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesActualCoordinateInduction

/-! # Iterates TFinite Norm

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Finite telescoping gives the actual T mixed-norm triangle inequality.
The scalar and gradient words may be chosen independently. -/
theorem iterate_T_finite_norm_triangle {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ} (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (hθ : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => θprev z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) {K : ℕ} (hK : K ≤ Nstar β)
    (v w : List (Fin 2)) {s : ℝ} (hs : 0 ≤ s) :
    Real.sqrt (l2NormSq (iterateSpatialWord v (T K s))) + Real.sqrt κprev *
      Real.sqrt (spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord w (T K t)))) ≤
      ∑ i ∈ Finset.range (K + 1),
        (Real.sqrt (l2NormSq (iterateSpatialWord v (iterateIncrement T i s))) + Real.sqrt κprev *
          Real.sqrt (spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord w
              (iterateIncrement T i t))))) := by
  have hu (i : ℕ) (hi : i ∈ Finset.range (K + 1)) :=
    iterateIncrement_smooth_up_to_initial I hΦ hT hθ (i := i) (by
      have ht := Finset.mem_range.mp hi
      omega)
  have hslice (i : ℕ) (hi : i ∈ Finset.range (K + 1)) (t : ℝ) (ht : 0 ≤ t) :
      ContDiff ℝ (⊤ : ℕ∞) (iterateIncrement T i t) :=
    (hu i hi).comp_contDiff (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)))
      (fun _ => ⟨ht, Set.mem_univ _⟩)
  have hword (p : List (Fin 2)) (t : ℝ) (ht : 0 ≤ t) :
      iterateSpatialWord p (T K t) =
        fun x => ∑ i ∈ Finset.range (K + 1), iterateSpatialWord p (iterateIncrement T i t) x := by
    have he : T K t = fun x => ∑ i ∈ Finset.range (K + 1), iterateIncrement T i t x :=
      funext (iterate_eq_sum_increments T K t)
    rw [he]
    exact iterateSpatialWord_sum _ _ (fun i hi => hslice i hi t ht) p
  have hscalar := iterate_scalar_integral_L2_sum (μ := volume.restrict unitCube)
    (S := Set.univ) (Finset.range (K + 1))
    (fun i x => iterateSpatialWord v (iterateIncrement T i s) x)
    (fun i hi => (iterateSpatialWord_smooth (hslice i hi s hs) v).continuous.continuousOn)
    (fun q hq => iterate_unitCube_integrable_of_continuous (continuousOn_univ.mp hq))
  have hgrad := iterate_vector_integral_L2_sum (μ := volume.restrict timeCube)
    (S := Set.Ici (0 : ℝ) ×ˢ Set.univ) (Finset.range (K + 1))
    (fun i z => spaceGrad (iterateSpatialWord w (iterateIncrement T i z.1)) z.2)
    (fun i hi => (iterate_word_gradient_smooth_up_to_initial (hu i hi) w).continuousOn)
    (fun q hq => iterate_timeCube_integrable_of_continuousOn hq)
  have hg : (fun z : AmnrSpace => spaceGrad (iterateSpatialWord w (T K z.1)) z.2)
      =ᵐ[volume.restrict timeCube]
      (fun z => ∑ i ∈ Finset.range (K + 1), spaceGrad (iterateSpatialWord w (iterateIncrement T i
          z.1)) z.2) := by
    have hm : MeasurableSet timeCube :=
      measurableSet_Ioo.prod (MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioo))
    filter_upwards [ae_restrict_mem hm] with z hz
    funext j
    change iterateSpatialWord (j :: w) (T K z.1) z.2 = _
    rw [hword (j :: w) z.1 hz.1.1.le]
    simp only [iterateSpatialWord, Finset.sum_apply]
  have hge := integral_congr_ae (hg.fun_comp vecNormSq)
  dsimp only [Function.comp_def] at hge
  unfold l2NormSq at hscalar ⊢
  rw [hword v s hs]
  unfold spaceTimeGradNormSq
  rw [hge]
  calc
    _ ≤ (∑ i ∈ Finset.range (K + 1), Real.sqrt (∫ x in unitCube,
        (iterateSpatialWord v (iterateIncrement T i s) x) ^ 2)) + Real.sqrt κprev *
        (∑ i ∈ Finset.range (K + 1), Real.sqrt (∫ z in timeCube,
          vecNormSq (spaceGrad (iterateSpatialWord w (iterateIncrement T i z.1)) z.2))) :=
      add_le_add hscalar (mul_le_mul_of_nonneg_left hgrad (Real.sqrt_nonneg _))
    _ = _ := by rw [Finset.mul_sum, ← Finset.sum_add_distrib]

/-- The T zeroth-order branch uses only integrated gradient norms. -/
theorem iterate_T_gradient_triangle {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ} (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (hθ : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => θprev z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) {K : ℕ} (hK : K ≤ Nstar β)
    (w : List (Fin 2)) :
    Real.sqrt κprev * Real.sqrt (spaceTimeGradNormSq
      (fun t => spaceGrad (iterateSpatialWord w (T K t)))) ≤
      ∑ i ∈ Finset.range (K + 1), Real.sqrt κprev * Real.sqrt (spaceTimeGradNormSq
        (fun t => spaceGrad (iterateSpatialWord w (iterateIncrement T i t)))) := by
  have hu (i : ℕ) (hi : i ∈ Finset.range (K + 1)) :=
    iterateIncrement_smooth_up_to_initial I hΦ hT hθ (i := i) (by
      have ht := Finset.mem_range.mp hi
      omega)
  have hslice (i : ℕ) (hi : i ∈ Finset.range (K + 1)) (t : ℝ) (ht : 0 ≤ t) :
      ContDiff ℝ (⊤ : ℕ∞) (iterateIncrement T i t) :=
    (hu i hi).comp_contDiff (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)))
      (fun _ => ⟨ht, Set.mem_univ _⟩)
  have hword (p : List (Fin 2)) (t : ℝ) (ht : 0 ≤ t) :
      iterateSpatialWord p (T K t) =
        fun x => ∑ i ∈ Finset.range (K + 1), iterateSpatialWord p (iterateIncrement T i t) x := by
    have he : T K t = fun x => ∑ i ∈ Finset.range (K + 1), iterateIncrement T i t x :=
      funext (iterate_eq_sum_increments T K t)
    rw [he]
    exact iterateSpatialWord_sum _ _ (fun i hi => hslice i hi t ht) p
  have hgrad := iterate_vector_integral_L2_sum (μ := volume.restrict timeCube)
    (S := Set.Ici (0 : ℝ) ×ˢ Set.univ) (Finset.range (K + 1))
    (fun i z => spaceGrad (iterateSpatialWord w (iterateIncrement T i z.1)) z.2)
    (fun i hi => (iterate_word_gradient_smooth_up_to_initial (hu i hi) w).continuousOn)
    (fun q hq => iterate_timeCube_integrable_of_continuousOn hq)
  have hg : (fun z : AmnrSpace => spaceGrad (iterateSpatialWord w (T K z.1)) z.2)
      =ᵐ[volume.restrict timeCube]
      (fun z => ∑ i ∈ Finset.range (K + 1), spaceGrad (iterateSpatialWord w (iterateIncrement T i
          z.1)) z.2) := by
    have hm : MeasurableSet timeCube :=
      measurableSet_Ioo.prod (MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioo))
    filter_upwards [ae_restrict_mem hm] with z hz
    funext j
    change iterateSpatialWord (j :: w) (T K z.1) z.2 = _
    rw [hword (j :: w) z.1 hz.1.1.le]
    simp only [iterateSpatialWord, Finset.sum_apply]
  have hge := integral_congr_ae (hg.fun_comp vecNormSq)
  dsimp only [Function.comp_def] at hge
  unfold spaceTimeGradNormSq
  rw [hge]
  exact (mul_le_mul_of_nonneg_left hgrad (Real.sqrt_nonneg κprev)).trans_eq
    (by rw [Finset.mul_sum])

end AVenhance.Infra.Section4
