/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTFiniteNorm
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesFiniteAnalyticSum
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesProfileNorms
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesAnalyticRadiusDoubling

/-! # Iterates TAnalytic Assembly

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The analytic T upgrade at positive scalar order, with abstract amplitude.
This is a finite-sum helper; actual PDE l.V supplies its increment estimates. -/
theorem iterate_T_positive_analytic_of_increment_bounds {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ} (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (hθ : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => θprev z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {N L η : ℝ} (hκ : 0 < κprev) (hN : 0 ≤ N) (hL : 0 ≤ L)
    (hη : 0 ≤ η) (hsmall : η ≤ 1 / 4)
    (hbase : iterateCoordinateEnergyProfile θprev κprev N L 0)
    (hV : ∀ i, 1 ≤ i → i ≤ Nstar β → ∀ v w : List (Fin 2), v.length = w.length →
      ∀ s, 0 ≤ s → s ≤ 1 →
      Real.sqrt (l2NormSq (iterateSpatialWord v (iterateIncrement T i s))) + Real.sqrt κprev *
        Real.sqrt (spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord w (iterateIncrement
            T i t)))) ≤
      N * iterateAmplitude η i * iterateAnalyticWeight v.length i L)
    (v w : List (Fin 2)) (hvw : v.length = w.length) (hv : 1 ≤ v.length)
    {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    Real.sqrt (l2NormSq (iterateSpatialWord v (T (Nstar β) s))) + Real.sqrt κprev *
      Real.sqrt (spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord w (T (Nstar β) t)))) ≤
      N * (4 : ℝ) ^ Nstar β * ((2 * Nstar β).factorial : ℝ) *
        (v.length.factorial : ℝ) * (4 * L) ^ v.length := by
  have ht := iterate_T_finite_norm_triangle I hΦ hT hθ le_rfl v w hs
  have hsum : (∑ i ∈ Finset.range (Nstar β + 1),
      (Real.sqrt (l2NormSq (iterateSpatialWord v (iterateIncrement T i s))) + Real.sqrt κprev *
        Real.sqrt (spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord w (iterateIncrement
            T i t)))))) ≤
      2 * N * ∑ i ∈ Finset.range (Nstar β + 1),
        iterateAmplitude η i * ((v.length + 2 * i).factorial : ℝ) * L ^ v.length := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hiN : i ≤ Nstar β := by have h := Finset.mem_range.mp hi; omega
    by_cases hi0 : i = 0
    · subst i
      have hb := iterate_profile_mixed_norm hκ hN hL hbase v w hvw (Or.inl hv) hs hs1
      simpa [iterateIncrement_zero, hT.1, iterateAmplitude, iterateAnalyticWeight, mul_assoc]
          using hb
    · have hb := hV i (by omega) hiN v w hvw s hs hs1
      have hA : 0 ≤ iterateAmplitude η i := by unfold iterateAmplitude; split_ifs <;> positivity
      have hn : 0 ≤ N * iterateAmplitude η i * iterateAnalyticWeight v.length i L :=
        mul_nonneg (mul_nonneg hN hA) (iterateAnalyticWeight_nonneg _ _ hL)
      have hm : N * iterateAmplitude η i * iterateAnalyticWeight v.length i L ≤
          2 * N * (iterateAmplitude η i * ((v.length + 2 * i).factorial : ℝ) * L ^ v.length) := by
        unfold iterateAnalyticWeight at hn ⊢
        linarith only [hn]
      exact hb.trans hm
  have ha := mul_le_mul_of_nonneg_left (iterate_finite_analytic_sum hη hsmall hL v.length (Nstar β))
    (by positivity : 0 ≤ 2 * N)
  have hd := iterate_positive_order_radius_double (L := 4 * L) (by positivity : 0 ≤ 2 * L)
    (by linarith only []) hv
  have hm := mul_le_mul_of_nonneg_left hd
    (show 0 ≤ N * (4 : ℝ) ^ Nstar β * ((2 * Nstar β).factorial : ℝ) * (v.length.factorial : ℝ) by
        positivity)
  calc
    _ ≤ _ := ht.trans hsum
    _ ≤ 2 * N * ((4 : ℝ) ^ Nstar β * ((2 * Nstar β).factorial : ℝ) *
        (v.length.factorial : ℝ) * (2 * L) ^ v.length) := ha
    _ ≤ _ := by
      convert hm using 1
      ring

/-- Zeroth T order is exclusively a gradient estimate; no scalar supremum is
present in either its hypotheses or its conclusion. -/
theorem iterate_T_zero_gradient_relative_of_increment_bounds {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ} (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (hθ : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => θprev z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {N η : ℝ} (hN : 0 ≤ N) (hη : 0 ≤ η) (hsmall : η ≤ 1)
    (hzero : Real.sqrt κprev * Real.sqrt (spaceTimeGradNormSq (fun t => spaceGrad (θprev t))) ≤ N)
    (hV : ∀ i, 1 ≤ i → i ≤ Nstar β → Real.sqrt κprev *
      Real.sqrt (spaceTimeGradNormSq (fun t => spaceGrad (iterateIncrement T i t))) ≤
        N * iterateAmplitude η i * ((2 * i).factorial : ℝ)) :
    Real.sqrt κprev * Real.sqrt (spaceTimeGradNormSq (fun t => spaceGrad (T (Nstar β) t))) ≤
      N * (1 + η * (Nstar β : ℝ) * ((2 * Nstar β).factorial : ℝ)) := by
  have ht := iterate_T_gradient_triangle I hΦ hT hθ le_rfl []
  have hsum : (∑ i ∈ Finset.range (Nstar β + 1), Real.sqrt κprev *
      Real.sqrt (spaceTimeGradNormSq (fun t => spaceGrad (iterateIncrement T i t)))) ≤
      N * ∑ i ∈ Finset.range (Nstar β + 1), iterateAmplitude η i * ((2 * i).factorial : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    by_cases hi0 : i = 0
    · subst i; simpa [iterateAmplitude, hT.1] using hzero
    · have hiN : i ≤ Nstar β := by have h := Finset.mem_range.mp hi; omega
      simpa only [mul_assoc] using hV i (by omega) hiN
  have ha := mul_le_mul_of_nonneg_left (iterate_finite_gradient_amplitude_sum hη hsmall (Nstar β))
      hN
  simpa only [iterateSpatialWord, mul_assoc] using ht.trans (hsum.trans ha)

end AVenhance.Infra.Section4
