/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesActualSevenFluxEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesActualPreviousSquaredGain
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesActualTerminalCommuted
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesActualAllWordStream
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesActualSmallRemainderFlux
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesBoundarySquaredGain
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTerminalFlowRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesHigherEnergyBudget

/-! # Iterates Actual Higher Energy Recurrence

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Complete higher-increment energy recurrence from actual equations,
coefficient jets, and preceding or strictly lower current scalar energies.
In particular, no material, forcing, or flux energy budget is a premise. -/
theorem iterate_actual_higher_increment_energy_recurrence {β : ℝ} (I : Ingredients β)
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
    l2NormSq (iterateSpatialWord w (iterateIncrement T (i + 1) s)) / 2 +
      κprev * (∫ z in iterateTruncatedCell s,
        vecNormSq (spaceGrad (iterateSpatialWord w (iterateIncrement T (i + 1) z.1)) z.2)) ≤
      l2NormSq (iterateSpatialWord w (iterateIncrement T (i + 1) s)) / 4 +
      3 * κprev / 8 * spaceTimeGradNormSq
        (fun t => spaceGrad (iterateSpatialWord w (iterateIncrement T (i + 1) t))) +
      iterateHigherEnergyBudget w.length i κprev D (a β I.Λ (m - 1))
        (epsilon β I.Λ (m - 1)) L Ccoef Cs Cv Cf Gcur Gprev Gprevprev Nprev ρ q d := by
  have hm1 : 1 ≤ m := by omega
  have hei : i - 1 + 1 = i := by omega
  have he := AVenhance.Infra.Cutoff.epsilon_pos (m := m - 1)
    I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hrvel : 0 ≤ (256 * (epsilon β I.Λ (m - 1))⁻¹) / L := by positivity
  have hvel' : (256 * (epsilon β I.Λ (m - 1))⁻¹) / L ≤ 1 / 2 := by
    nlinarith only [hvel, hrvel]
  obtain ⟨hφ, _⟩ := hΦ.2 m hm1
  have hb : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => streamVel (Φ (m - 1)) z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    (AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ).smooth.contDiffOn
  have hu := iterateIncrement_smooth_up_to_initial I hΦ hT hθ.1 hi
  have hv := iterateIncrement_smooth_up_to_initial I hΦ hT hθ.1 (by omega : i ≤ Nstar β)
  have hQc : Continuous (iterateKmatPrimitive I κm m) := by
    apply continuous_pi
    intro j
    apply continuous_pi
    intro k
    exact (iterateKmatPrimitive_entry_contDiff I hκm hm1 j k).continuous
  have hQjoint : ContinuousOn (fun z : AmnrSpace => iterateKmatPrimitive I κm m z.1)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := (hQc.comp continuous_fst).continuousOn
  have hslice {f : ℝ → Vec 2 → ℝ}
      (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => f z.1 z.2)
        (Set.Ici (0 : ℝ) ×ˢ Set.univ)) : ContDiff ℝ (⊤ : ℕ∞) (f s) :=
    hf.comp_contDiff (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (s, x)))
      (fun _ => ⟨hs, Set.mem_univ _⟩)
  have hbdy := iterate_word_boundary_squared_gain (hslice hu) (hslice hv)
    (iterateIncrement_periodic I hΦ hT hθ.2.1 hi hs)
    (iterateIncrement_periodic I hΦ hT hθ.2.1 (by omega) hs) w (2 * i)
    (iterateKmatPrimitive I κm m s) hD hL hCs hq.le (hQ s) hscale
    (fun j k => by
      simpa only [List.length_cons, Nat.add_assoc, Nat.reduceAdd] using
        hterminal (j :: k :: w) (by simp) s hs hs1)
  have hpm := iterate_actual_previous_material_squared_gain_of_A3 I hΦ hT hθ hm hκm hflow hA3
    (i - 1) (by omega) w (C := Ccoef) (Gcur := Gprev) (Gprev := Gprevprev) hL hg
    (hvel.trans (by norm_num)) hcoef
    (fun p hp => by simpa only [hei] using hprev p hp) hprevprev hu hQjoint hQ hκ hs1
    hCs hCv hq.le hscale hvelocity
  have hcm := iterate_increment_terminal_commuted_current_material_corrected_bound I hΦ hT hθ
    hm hκm hκ hflow hs1 i hi w (Ccoef := Ccoef) (Cscale := Cs) (B := Gprev) (Gcur := Gcur)
    hL hg hD hCs hq hQc.continuousOn hQ hscale hcoef hprev hA3 hGp hGc hvel' d hd
    (fun p hp => by
      have ht := hlower p.2 (iterateSpatialSplits_lower_order w hp)
      simpa only [mul_pow, mul_assoc] using ht)
  have hgp := mul_le_mul_of_nonneg_left (hprev w (by omega)) hκ.le
  have hfm := iterate_terminal_flow_pairings_bound_of_continuity
    (flow := streamVel (Φ (m - 1)))
    (a := fun t => spaceGrad (iterateSpatialWord w (iterateIncrement T (i + 1) t)))
    (b := fun t => spaceGrad (iterateSpatialWord w (iterateIncrement T i t)))
    hs1 hκ hCf hρ (iterate_word_gradient_smooth_up_to_initial hu w).continuousOn
    (iterate_word_gradient_smooth_up_to_initial hv w).continuousOn hQjoint
    (iterate_flow_gradient_matrix_continuousOn hb) hQ hFlowBound hFlowScale hgp
  have hrm := iterate_terminal_mean_correction_small_flux_bound I hΦ hm1 hκm hκ hflow hu hv w
    (2 * i) hL hg hs1 hrem (fun p hp => hprev p.2 (by
      have ho := iterateSpatialSplits_orders w hp
      omega))
  have hsm := iterate_increment_terminal_all_word_stream_recurrence_of_A3 I hΦ hT hθ.1 hm hκ hA3
    hθ.2.1 hs hs1 (i + 1) hi w hL hvel d hlower
  have henergy := iterate_increment_terminal_seven_flux_energy_inequality I hΦ hT hθ hflow hflowp
    hm1 hκm i hi w hs hs1
  have hn : w.length + 2 + 2 * i = w.length + 2 * (i + 1) := by omega
  have hn' : w.length + 2 + 2 * (i - 1) = w.length + 2 * i := by omega
  simp only [hei, hn, hn'] at hpm hbdy hcm
  simp only [iterateHigherEnergyBudget, iterateAnalyticWeight]
  simp only [List.length_eq_zero_iff]
  nlinarith only [henergy, hbdy, hpm, hcm, hfm, hrm, hsm]

end AVenhance.Infra.Section4
