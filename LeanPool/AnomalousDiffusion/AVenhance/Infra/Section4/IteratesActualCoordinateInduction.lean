/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesActualHigherNormRecurrence
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesActualFirstNormRecurrence
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesHigherBudgetSmall
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesFirstBudgetSmall
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesCoordinateInduction

/-! # Iterates Actual Coordinate Induction

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Actual all-order increment induction from coefficient jets, scalar scale
inequalities, and the analytic homogeneous base. No material, forcing, flux,
energy recurrence, or preceding increment estimate is assumed. -/
theorem iterate_actual_coordinate_induction_of_scales {β : ℝ} (I : Ingredients β)
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
    {Ccoef Cs C C₀ N B r L D Bflow ρ F : ℝ}
    (hL : 0 < L) (hg : 2 * (r / L) ^ 2 ≤ 1 / 2)
    (hvel : 2 * ((256 * (epsilon β I.Λ (m - 1))⁻¹) / L) ^ 2 ≤ 1 / 4)
    (hD : 0 ≤ D) (hCs : 0 ≤ Cs) (hC : 0 ≤ C) (hN : 0 ≤ N)
    (hB : 0 ≤ B) (hr : 0 ≤ r) (hρ : 0 < ρ) (hρq : ρ ≤ ρ * F ^ 2)
    (hC₀ : 1 ≤ C₀) (hF : C₀ ≤ F) (hlarge : 32 * C ≤ C₀)
    (hsmall : C₀ * (ρ * F ^ 2) ≤ 1)
    (hQ : ∀ t j k, |iterateKmatPrimitive I κm m t j k| ≤ D)
    (hscale : D * L ^ 2 ≤ Cs * (ρ * F ^ 2))
    (hvelocity : (8192 * a β I.Λ (m - 1) * epsilon β I.Λ (m - 1)) *
      (256 * (epsilon β I.Λ (m - 1))⁻¹) ≤ Cs * κprev * L ^ 2)
    (hBr : B * r = (8192 * a β I.Λ (m - 1) * epsilon β I.Λ (m - 1)) *
      (256 * (epsilon β I.Λ (m - 1))⁻¹))
    (hjet : ∀ t x (p : List (Fin 2)), 1 ≤ p.length → ∀ j,
      |iterateSpatialWord p (fun y => streamVel (Φ (m - 1)) t y j) x| ≤
        B * (p.length.factorial : ℝ) * r ^ p.length)
    (hFlowBound : ∀ t x j k, |gradMatrix (streamVel (Φ (m - 1)) t) x j k| ≤ Bflow)
    (hFlowScale : D * Bflow ≤ Cs * κprev * ρ)
    (hcoef : ∀ t x p, ∀ j k, |iterateMatrixWord
      (fun y => I.Kmat κm m t - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        I.sMat hΦ m κm t y) p x j k| ≤ κprev * Ccoef * (p.length.factorial : ℝ) * r ^ p.length)
    (hrem : ∀ t x p, ∀ j k, |iterateMatrixWord
      (fun y => timeAvgMat (I.Kmat κm m) - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        I.sMat hΦ m κm t y) p x j k| ≤ κprev * Ccoef * ρ * (p.length.factorial : ℝ) * r ^ p.length)
    (hbase : iterateCoordinateEnergyProfile θprev κprev N L 0)
    (hmat : 24 * amnrMaterialMajorantConstant Ccoef Cs Cs Cs ≤ C)
    (hfirst : 24 * (iterateFirstMaterialCoefficient Cs Ccoef + 384 * Cs ^ 2 + 32 * Ccoef ^ 2) ≤ C)
    (hu : (24 * (2 * ((2 : ℝ) ^ 19 * a β I.Λ (m - 1)) / L ^ 2)) / κprev ≤ C / F ^ 2)
    (hv : (24 * (16 / κprev * (32 * a β I.Λ (m - 1) * epsilon β I.Λ (m - 1) ^ 2) ^ 2 *
      (2 * ((256 * (epsilon β I.Λ (m - 1))⁻¹) / L) ^ 2) ^ 2)) / κprev ≤ C / F ^ 4)
    (hc : (24 * (8 * D * (8192 * a β I.Λ (m - 1) * epsilon β I.Λ (m - 1)) *
      (256 * (epsilon β I.Λ (m - 1))⁻¹))) / κprev ≤ C * ρ) :
    ∀ i, i ≤ Nstar β → iterateCoordinateEnergyProfile (iterateIncrement T i) κprev
      (N * iterateAmplitude (C₀ * (ρ * F ^ 2)) i) L i := by
  have hp : 0 < C₀ := by linarith only [hC₀]
  have hFp : 0 < F := hp.trans_le hF
  have hq : 0 < ρ * F ^ 2 := mul_pos hρ (sq_pos_of_pos hFp)
  have hη : 0 < C₀ * (ρ * F ^ 2) := mul_pos hp hq
  have he := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m - 1)
  have ha : 0 ≤ a β I.Λ (m - 1) := by unfold a; positivity
  apply iterate_coordinate_two_index_induction hκ
  · simpa only [iterateIncrement_zero, hT.1] using hbase
  · intro i hi0 hi hpast w hlower s hs hs1
    cases i with
    | zero => omega
    | succ j =>
      by_cases hj : j = 0
      · subst j
        have hvelocity' : B * r ≤ Cs * κprev * L ^ 2 := by rw [hBr]; exact hvelocity
        have hc' : (24 * (8 * D * B * r)) / κprev ≤ C * ρ := by
          have heq : 8 * D * B * r = 8 * D *
              ((8192 * a β I.Λ (m - 1) * epsilon β I.Λ (m - 1)) *
                (256 * (epsilon β I.Λ (m - 1))⁻¹)) := by rw [← hBr]; ring
          rw [heq]
          convert hc using 1
          ring
        have hn := iterate_actual_first_increment_norm_recurrence I hΦ hi hT hθ hm hκm hκ
          hflow hflowp hA3 w hL hg hvel hD hCs
          (by positivity : 0 ≤ N * iterateAmplitude (C₀ * (ρ * F ^ 2)) 1 / Real.sqrt κprev)
          hN hB hr hρ.le hq hρq hQ hscale hvelocity' hjet hFlowBound hFlowScale hrem
          (fun p _ => by simpa only [iterateCoordinateEnergyProfile, iterateAnalyticWeight,
            Nat.mul_zero, Nat.add_zero] using hbase.2 p)
          (fun p hp _ t ht ht1 => by
            simpa only [iterateAnalyticWeight, Nat.mul_zero, Nat.add_zero] using hbase.1 p (Or.inl
                hp) t ht ht1)
          (fun _ => 1) (fun _ => by norm_num)
          (fun p hp => by
            simpa only [iterateAnalyticWeight, Nat.mul_one, one_pow, mul_one] using hlower p hp)
                hs hs1
        exact hn.trans (iterate_first_energy_budget_small w.length hκ hD ha he.le hB hr hL
          hρ hρq hC hC₀ hF hlarge hsmall hfirst hu hv hc')
      · have hjp : 1 ≤ j := by omega
        have hprev := hpast j (by omega)
        have hprevprev := hpast (j - 1) (by omega)
        have hn := iterate_actual_higher_increment_norm_recurrence I hΦ hT hθ hm hκm hκ
          hflow hflowp hA3 j hjp hi w hL hg hvel hD hCs hCs hCs
          (div_nonneg (mul_nonneg hN (iterateAmplitude_pos hη (j + 1)).le) (Real.sqrt_nonneg _))
          (div_nonneg (mul_nonneg hN (iterateAmplitude_pos hη j).le) (Real.sqrt_nonneg _))
          hρ.le hq hQ hscale hvelocity hFlowBound hFlowScale hcoef hrem
          (fun p _ => by simpa only [iterateAnalyticWeight] using hprev.2 p)
          (fun p _ => by simpa only [iterateAnalyticWeight] using hprevprev.2 p)
          (fun p _ t ht ht1 => by
            simpa only [iterateAnalyticWeight] using (hprev.1 p (Or.inr hjp) t ht ht1))
          (fun _ => 1) (fun _ => by norm_num)
          (fun p hp => by simpa only [iterateAnalyticWeight, one_pow, mul_one] using hlower p hp)
          hs hs1
        exact hn.trans (iterate_higher_energy_budget_small w.length hjp hκ hD ha he.le hL
          hρ hρq hC hC₀ hF hlarge hsmall hmat hu hv hc)

end AVenhance.Infra.Section4
