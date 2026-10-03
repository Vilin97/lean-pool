/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesErrorGradientEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesAnalyticErrorEnergy

/-! Actual previous material-error gradient in the induction's analytic weights. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The actual error-gradient energy uses only scalar gradient orders up to
 n. Its factorial has shift n+a+1, exactly fitting the next increment. -/
theorem iterate_analytic_material_error_gradient_energy_bound
    {b : ℝ → Vec 2 → Vec 2} {v : ℝ → Vec 2 → ℝ}
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => b z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (w : List (Fin 2)) (a : ℕ)
    {B G r L : ℝ} (hL : 0 < L) (hg : 2 * (r / L) ^ 2 ≤ 1 / 2)
    (hjet : ∀ t x (q : List (Fin 2)), 1 ≤ q.length → ∀ j,
      |iterateSpatialWord q (fun y => b t y j) x| ≤ B * (q.length.factorial : ℝ) * r ^ q.length)
    (hE : ∀ q : List (Fin 2), q.length ≤ w.length →
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord q (v t))) ≤
        G ^ 2 * (((q.length + a).factorial : ℝ) * L ^ q.length) ^ 2) :
    spaceTimeGradNormSq (fun t x => spaceGrad (fun y => iterateWordMaterialError
      (fun z : AmnrSpace => b z.1 z.2) w (fun z => v z.1 z.2) (t, y)) x) ≤
      136 * B ^ 2 * r ^ 2 * G ^ 2 * (((w.length + 1 + a).factorial : ℝ) * L ^ w.length) ^ 2 := by
  have hfirst : ∀ t x j k, |spaceGrad (fun y => b t y k) x j| ≤ B * r := by
    intro t x j k
    simpa only [iterateSpatialWord, List.length_cons, List.length_nil, Nat.factorial_one,
      Nat.reduceAdd, Nat.cast_one, mul_one, pow_one] using hjet t x [j] (by simp) k
  have ht := iterate_material_error_gradient_energy_bound hb hv w hfirst
  have he (j : Fin 2) : (∫ z in timeCube, iterateWordMaterialError
      (fun z : AmnrSpace => b z.1 z.2) (j :: w) (fun z => v z.1 z.2) z ^ 2) ≤
      32 * B ^ 2 * r ^ 2 * G ^ 2 * (((w.length + 1 + a).factorial : ℝ) * L ^ w.length) ^ 2 := by
    have hs := iterate_analytic_material_error_energy_bound hb hv (j :: w) a hL hg
      (B := B) (G := G) (fun t x p hp k => hjet t x p.1
        (by simpa using (List.mem_filter.mp hp).2) k)
      (fun p hp => hE p.2 (by
        have ho := iterateSpatialSplits_orders (j :: w) (List.mem_filter.mp hp).1
        have hl : 1 ≤ p.1.length := by simpa using (List.mem_filter.mp hp).2
        simp only [List.length_cons] at ho
        omega))
    have heq : 32 * B ^ 2 * G ^ 2 * (r / L) ^ 2 *
        (((w.length + 1 + a).factorial : ℝ) * L ^ (w.length + 1)) ^ 2 =
        32 * B ^ 2 * r ^ 2 * G ^ 2 * (((w.length + 1 + a).factorial : ℝ) * L ^ w.length) ^ 2 := by
      simp only [pow_succ]
      field_simp
    simpa only [List.length_cons, heq] using hs
  have hf : ((w.length + a).factorial : ℝ) ≤ ((w.length + 1 + a).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega : w.length + a ≤ w.length + 1 + a)
  have hw := (hE w le_rfl).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity)
      (mul_le_mul_of_nonneg_right hf (by positivity : 0 ≤ L ^ w.length)) 2) (sq_nonneg G))
  have hbase := mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ 8 * (B * r) ^ 2)
  have he0 := he 0
  have he1 := he 1
  simp only [Fin.sum_univ_two] at ht
  nlinarith only [ht, he0, he1, hbase]

end AVenhance.Infra.Section4
