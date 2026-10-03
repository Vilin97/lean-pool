/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesActualHigherEnergyRecurrence
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesActualFirstCommutedCurrent
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesHomogeneousPreviousMaterial

/-! # Iterates Actual First Energy Recurrence

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Complete exceptional first-increment energy recurrence. The first material
forcing cancellation is derived from the actual homogeneous base equation. -/
theorem iterate_actual_first_increment_energy_recurrence {β : ℝ} (I : Ingredients β)
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
    l2NormSq (iterateSpatialWord w (iterateIncrement T 1 s)) / 2 +
      κprev * (∫ z in iterateTruncatedCell s,
        vecNormSq (spaceGrad (iterateSpatialWord w (iterateIncrement T 1 z.1)) z.2)) ≤
      l2NormSq (iterateSpatialWord w (iterateIncrement T 1 s)) / 4 +
      3 * κprev / 8 * spaceTimeGradNormSq
        (fun t => spaceGrad (iterateSpatialWord w (iterateIncrement T 1 t))) +
      iterateFirstEnergyBudget w.length κprev D (a β I.Λ (m - 1))
        (epsilon β I.Λ (m - 1)) r L C Ccoef B Gcur N ρ q d := by
  have hm1 : 1 ≤ m := by omega
  obtain ⟨hφ, _⟩ := hΦ.2 m hm1
  have hb : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => streamVel (Φ (m - 1)) z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    (AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ).smooth.contDiffOn
  have hu := iterateIncrement_smooth_up_to_initial I hΦ hT hθ.1 hNstar
  have hQc : ContinuousOn (fun z : AmnrSpace => iterateKmatPrimitive I κm m z.1)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    apply continuousOn_pi.mpr
    intro j
    apply continuousOn_pi.mpr
    intro k
    exact (iterateKmatPrimitive_entry_joint_contDiff I hκm hm1 j k).continuous.continuousOn
  have hslice {f : ℝ → Vec 2 → ℝ}
      (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => f z.1 z.2)
        (Set.Ici (0 : ℝ) ×ˢ Set.univ)) : ContDiff ℝ (⊤ : ℕ∞) (f s) :=
    hf.comp_contDiff (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (s, x)))
      (fun _ => ⟨hs, Set.mem_univ _⟩)
  have hbdy := iterate_word_boundary_squared_gain (hslice hu) (hslice hθ.1)
    (iterateIncrement_periodic I hΦ hT hθ.2.1 hNstar hs) (hθ.2.1 s hs) w 0
    (iterateKmatPrimitive I κm m s) hD hL hC hq.le (hQ s) hscale
    (fun j k => by
      simpa only [List.length_cons, Nat.add_zero, Nat.reduceAdd] using
        hterminal (j :: k :: w) (by simp) (by simp) s hs hs1)
  have hpm := iterate_homogeneous_terminal_previous_material_squared_gain hθ hb hu w hQc
    hB hr hC hκ hL hg hvelocity hjet
    (fun p hp => hbase p (by omega)) hD hC hq.le hQ hscale hs1
  have hcm := iterate_actual_first_commuted_current_material_bound I hΦ hNstar hm1 hκm hκ hθ hT hb
      w hflow
    hB hN hr hC hD hq hρ hρq hL hs hs1 hg hvelocity hQ hscale
    (fun j k t x p hp a => hjet t x p.1 (by simpa using (List.mem_filter.mp hp).2) a)
    hbase (fun t x p j k => by simpa only [mul_assoc] using hrem t x p j k)
    (fun j k => by
      simpa only [List.length_cons, Nat.reduceAdd, mul_pow, mul_assoc] using
        hterminal (j :: k :: w) (by simp) (by simp) s hs hs1)
    hGc d hd
    (fun t x p hp j => hjet t x p.1 (by
      have ht := iterateSpatialSplits_lower_order w hp
      have ho := iterateSpatialSplits_orders w (List.mem_filter.mp hp).1
      omega) j)
    (fun p hp => by
      have ht := hlower p.2 (iterateSpatialSplits_lower_order w hp)
      simpa only [mul_pow, mul_assoc] using ht)
  have hn := iterate_diffusive_gradient_normalization (N := N) hκ
  have hgp : κprev * spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord w (θprev t))) ≤
      N ^ 2 * ((w.length.factorial : ℝ) * L ^ w.length) ^ 2 := by
    have ht := mul_le_mul_of_nonneg_left (hbase w (by omega)) hκ.le
    simpa only [← mul_assoc, hn] using ht
  have hfm := iterate_terminal_flow_pairings_bound_of_continuity
    (flow := streamVel (Φ (m - 1)))
    (a := fun t => spaceGrad (iterateSpatialWord w (iterateIncrement T 1 t)))
    (b := fun t => spaceGrad (iterateSpatialWord w (θprev t)))
    hs1 hκ hC hρ (iterate_word_gradient_smooth_up_to_initial hu w).continuousOn
    (iterate_word_gradient_smooth_up_to_initial hθ.1 w).continuousOn hQc
    (iterate_flow_gradient_matrix_continuousOn hb) hQ hFlowBound hFlowScale hgp
  have hrm := iterate_terminal_mean_correction_small_flux_bound I hΦ hm1 hκm hκ hflow hu hθ.1 w
    0 hL hg hs1 hrem (fun p hp => by
      simpa only [Nat.add_zero] using hbase p.2 (by
        have ho := iterateSpatialSplits_orders w hp
        omega))
  have hsm := iterate_increment_terminal_all_word_stream_recurrence_of_A3 I hΦ hT hθ.1 hm hκ hA3
    hθ.2.1 hs hs1 1 hNstar w hL hvel d (fun p hp => by
      simpa only [Nat.mul_one] using hlower p hp)
  have henergy := iterate_increment_terminal_seven_flux_energy_inequality I hΦ hT hθ hflow hflowp
    hm1 hκm 0 hNstar w hs hs1
  simp only [iterateIncrement_zero, hT.1, Nat.zero_add] at henergy
  simp only [iterateFirstEnergyBudget, iterateAnalyticWeight, Nat.mul_one, Nat.mul_zero,
      Nat.add_zero,
    List.length_eq_zero_iff]
  simp only [Nat.add_zero] at hbdy
  have hnr : κprev * (N / Real.sqrt κprev) ^ 2 = N ^ 2 := hn
  have hrm' := hrm
  rw [show 32 * κprev * Ccoef ^ 2 * ρ ^ 2 * (N / Real.sqrt κprev) ^ 2 =
      32 * Ccoef ^ 2 * ρ ^ 2 * N ^ 2 by
        calc
          _ = 32 * Ccoef ^ 2 * ρ ^ 2 * (κprev * (N / Real.sqrt κprev) ^ 2) := by ring
          _ = _ := by rw [hnr]] at hrm'
  simp only [Nat.mul_one] at hsm
  simp only [Nat.add_zero] at hrm'
  nlinarith only [henergy, hbdy, hpm, hcm, hfm, hrm', hsm]

end AVenhance.Infra.Section4
