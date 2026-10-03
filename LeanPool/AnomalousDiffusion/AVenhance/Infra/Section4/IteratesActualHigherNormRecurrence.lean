/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesActualHigherEnergyRecurrence
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesEnergyRecurrenceNorm

/-! # Iterates Actual Higher Norm Recurrence

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Actual differentiated norm recurrence, obtained from the quantitative
energy equation at time one and at the requested terminal time. -/
theorem iterate_actual_higher_increment_norm_recurrence {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ} (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (hθ : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hm : 2 ≤ m) (hκm : 0 < κm) (hκ : 0 < κprev)
    (hflow : ∀ l : ℤ, ContDiff ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => I.flowGrad hΦ m l z.1 z.2))
    (hflowp : ∀ t, 0 < t → ∀ l : ℤ, IsZ2Periodic (I.flowGrad hΦ m l t))
    (hA3 : ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
      barNorm n (2 ^ 8 * (epsilon β I.Λ j)⁻¹) (Φ j t) ≤
        ENNReal.ofReal (2 ^ 5 * a β I.Λ j * epsilon β I.Λ j ^ 2 *
          (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3)))
    (i : ℕ) (hi0 : 1 ≤ i) (hi : i + 1 ≤ Nstar β) (w : List (Fin 2))
    {Ccoef Cs Cv Cf Gcur Gprev Gprevprev Nprev r L D Bflow ρ q : ℝ}
    (hL : 0 < L) (hg : 2 * (r / L) ^ 2 ≤ 1 / 2)
    (hvel : 2 * ((256 * (epsilon β I.Λ (m - 1))⁻¹) / L) ^ 2 ≤ 1 / 4)
    (hD : 0 ≤ D) (hCs : 0 ≤ Cs) (hCv : 0 ≤ Cv) (hCf : 0 ≤ Cf)
    (hGc : 0 ≤ Gcur) (hGp : 0 ≤ Gprev) (hρ : 0 ≤ ρ) (hq : 0 < q)
    (hQ : ∀ t j k, |iterateKmatPrimitive I κm m t j k| ≤ D)
    (hscale : D * L ^ 2 ≤ Cs * q)
    (hvelocity : (8192 * a β I.Λ (m - 1) * epsilon β I.Λ (m - 1)) *
      (256 * (epsilon β I.Λ (m - 1))⁻¹) ≤ Cv * κprev * L ^ 2)
    (hFlowBound : ∀ t x j k, |gradMatrix (streamVel (Φ (m - 1)) t) x j k| ≤ Bflow)
    (hFlowScale : D * Bflow ≤ Cf * κprev * ρ)
    (hcoef : ∀ t x p, ∀ j k, |iterateMatrixWord
      (fun y => I.Kmat κm m t - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        I.sMat hΦ m κm t y) p x j k| ≤ κprev * Ccoef * (p.length.factorial : ℝ) * r ^ p.length)
    (hrem : ∀ t x p, ∀ j k, |iterateMatrixWord
      (fun y => timeAvgMat (I.Kmat κm m) - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        I.sMat hΦ m κm t y) p x j k| ≤ κprev * Ccoef * ρ * (p.length.factorial : ℝ) * r ^ p.length)
    (hprev : ∀ p : List (Fin 2), p.length ≤ w.length + 2 →
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord p (iterateIncrement T i t))) ≤
        Gprev ^ 2 * (((p.length + 2 * i).factorial : ℝ) * L ^ p.length) ^ 2)
    (hprevprev : ∀ p : List (Fin 2), p.length ≤ w.length + 2 →
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord p (iterateIncrement T (i - 1)
          t))) ≤
        Gprevprev ^ 2 * (((p.length + 2 * (i - 1)).factorial : ℝ) * L ^ p.length) ^ 2)
    (hterminal : ∀ p : List (Fin 2), p.length ≤ w.length + 2 → ∀ t, 0 ≤ t → t ≤ 1 →
      l2NormSq (iterateSpatialWord p (iterateIncrement T i t)) ≤
        Nprev ^ 2 * (((p.length + 2 * i).factorial : ℝ) * L ^ p.length) ^ 2)
    (d : ℕ → ℝ) (hd : ∀ n, 0 ≤ d n)
    (hlower : ∀ p : List (Fin 2), p.length < w.length →
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord p (iterateIncrement T (i + 1)
          t))) ≤
        Gcur ^ 2 * (((p.length + 2 * (i + 1)).factorial : ℝ) * L ^ p.length) ^ 2 * d p.length ^ 2)
    {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    (Real.sqrt (l2NormSq (iterateSpatialWord w (iterateIncrement T (i + 1) s))) +
      Real.sqrt κprev * Real.sqrt (spaceTimeGradNormSq
        (fun t => spaceGrad (iterateSpatialWord w (iterateIncrement T (i + 1) t))))) ^ 2 ≤
      24 * (iterateHigherEnergyBudget w.length i κprev D (a β I.Λ (m - 1))
        (epsilon β I.Λ (m - 1)) L Ccoef Cs Cv Cf Gcur Gprev Gprevprev Nprev ρ q d) := by
  have he (t : ℝ) : 0 ≤ l2NormSq (iterateSpatialWord w (iterateIncrement T (i + 1) t)) :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hv (z : AmnrSpace) : 0 ≤ vecNormSq
      (spaceGrad (iterateSpatialWord w (iterateIncrement T (i + 1) z.1)) z.2) := by
    unfold vecNormSq vecDot
    exact Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)
  apply iterate_energy_recurrence_norm_sq
    (gpart := fun t => ∫ z in iterateTruncatedCell t,
      vecNormSq (spaceGrad (iterateSpatialWord w (iterateIncrement T (i + 1) z.1)) z.2)) he
          (integral_nonneg hv)
    (fun _ => integral_nonneg hv) hκ.le rfl _ hs hs1
  intro t ht ht1
  exact iterate_actual_higher_increment_energy_recurrence I hΦ hT hθ hm hκm hκ hflow hflowp hA3 i
      hi0 hi w hL hg hvel hD hCs hCv hCf hGc hGp hρ hq hQ hscale hvelocity hFlowBound hFlowScale
      hcoef hrem hprev hprevprev hterminal d hd hlower ht ht1

end AVenhance.Infra.Section4
