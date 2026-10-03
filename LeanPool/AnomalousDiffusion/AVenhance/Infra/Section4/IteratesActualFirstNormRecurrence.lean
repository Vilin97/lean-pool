/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesActualFirstEnergyRecurrence
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesEnergyRecurrenceNorm

/-! # Iterates Actual First Norm Recurrence

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
theorem iterate_actual_first_increment_norm_recurrence {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) (hNstar : 1 ≤ Nstar β)
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
    (w : List (Fin 2)) {C Ccoef Gcur N B r L D Bflow ρ q : ℝ}
    (hL : 0 < L) (hg : 2 * (r / L) ^ 2 ≤ 1 / 2)
    (hvel : 2 * ((256 * (epsilon β I.Λ (m - 1))⁻¹) / L) ^ 2 ≤ 1 / 4)
    (hD : 0 ≤ D) (hC : 0 ≤ C) (hGc : 0 ≤ Gcur) (hN : 0 ≤ N)
    (hB : 0 ≤ B) (hr : 0 ≤ r) (hρ : 0 ≤ ρ) (hq : 0 < q) (hρq : ρ ≤ q)
    (hQ : ∀ t j k, |iterateKmatPrimitive I κm m t j k| ≤ D)
    (hscale : D * L ^ 2 ≤ C * q) (hvelocity : B * r ≤ C * κprev * L ^ 2)
    (hjet : ∀ t x (p : List (Fin 2)), 1 ≤ p.length → ∀ j,
      |iterateSpatialWord p (fun y => streamVel (Φ (m - 1)) t y j) x| ≤
        B * (p.length.factorial : ℝ) * r ^ p.length)
    (hFlowBound : ∀ t x j k, |gradMatrix (streamVel (Φ (m - 1)) t) x j k| ≤ Bflow)
    (hFlowScale : D * Bflow ≤ C * κprev * ρ)
    (hrem : ∀ t x p, ∀ j k, |iterateMatrixWord
      (fun y => timeAvgMat (I.Kmat κm m) - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        I.sMat hΦ m κm t y) p x j k| ≤ κprev * Ccoef * ρ * (p.length.factorial : ℝ) * r ^ p.length)
    (hbase : ∀ p : List (Fin 2), p.length ≤ w.length + 3 →
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord p (θprev t))) ≤
        (N / Real.sqrt κprev) ^ 2 * ((p.length.factorial : ℝ) * L ^ p.length) ^ 2)
    (hterminal : ∀ p : List (Fin 2), 1 ≤ p.length → p.length ≤ w.length + 2 → ∀ t, 0 ≤ t → t ≤ 1 →
      l2NormSq (iterateSpatialWord p (θprev t)) ≤
        N ^ 2 * ((p.length.factorial : ℝ) * L ^ p.length) ^ 2)
    (d : ℕ → ℝ) (hd : ∀ n, 0 ≤ d n)
    (hlower : ∀ p : List (Fin 2), p.length < w.length →
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord p (iterateIncrement T 1 t))) ≤
        Gcur ^ 2 * (((p.length + 2).factorial : ℝ) * L ^ p.length) ^ 2 * d p.length ^ 2)
    {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    (Real.sqrt (l2NormSq (iterateSpatialWord w (iterateIncrement T 1 s))) +
      Real.sqrt κprev * Real.sqrt (spaceTimeGradNormSq
        (fun t => spaceGrad (iterateSpatialWord w (iterateIncrement T 1 t))))) ^ 2 ≤
      24 * (iterateFirstEnergyBudget w.length κprev D (a β I.Λ (m - 1))
        (epsilon β I.Λ (m - 1)) r L C Ccoef B Gcur N ρ q d) := by
  have he (t : ℝ) : 0 ≤ l2NormSq (iterateSpatialWord w (iterateIncrement T 1 t)) :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hv (z : AmnrSpace) : 0 ≤ vecNormSq
      (spaceGrad (iterateSpatialWord w (iterateIncrement T 1 z.1)) z.2) := by
    unfold vecNormSq vecDot
    exact Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)
  apply iterate_energy_recurrence_norm_sq
    (gpart := fun t => ∫ z in iterateTruncatedCell t,
      vecNormSq (spaceGrad (iterateSpatialWord w (iterateIncrement T 1 z.1)) z.2)) he
          (integral_nonneg hv)
    (fun _ => integral_nonneg hv) hκ.le rfl _ hs hs1
  intro t ht ht1
  exact iterate_actual_first_increment_energy_recurrence I hΦ hNstar hT hθ hm hκm hκ hflow hflowp
      hA3 w hL hg hvel hD hC hGc hN hB hr hρ hq hρq hQ hscale hvelocity hjet hFlowBound hFlowScale
      hrem hbase hterminal d hd hlower ht ht1

end AVenhance.Infra.Section4
