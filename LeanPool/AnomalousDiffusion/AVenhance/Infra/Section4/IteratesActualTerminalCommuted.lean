/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesActualTerminalCurrent
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTerminalCurrentSplit
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTerminalTransferredMaterial

/-! The full actual current material term with corrected remainder. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Actual stream-regularity data and forcing jets give the current oscillatory term, including
its strictly lower current-order linear commutator and the retained q remainder. -/
theorem iterate_increment_terminal_commuted_current_material_corrected_bound {β : ℝ} (I :
    Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ} (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (hθ : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hm : 2 ≤ m) (hκm : 0 < κm) (hκ : 0 < κprev)
    (hflow : ∀ l : ℤ, ContDiff ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => I.flowGrad hΦ m l z.1 z.2))
    {s : ℝ} (hs1 : s ≤ 1)
    (i : ℕ) (hi : i + 1 ≤ Nstar β) (w : List (Fin 2))
    {Ccoef Cscale B r L D q : ℝ}
    (hL : 0 < L) (hg : 2 * (r / L) ^ 2 ≤ 1 / 2)
    (hD : 0 ≤ D) (hCscale : 0 ≤ Cscale) (hq : 0 < q)
    {Q : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hQc : ContinuousOn Q (Set.Ici (0 : ℝ)))
    (hQ : ∀ t j k, |Q t j k| ≤ D) (hscale : D * L ^ 2 ≤ Cscale * q)
    (hcoef : ∀ t x p, ∀ j k, |iterateMatrixWord
      (fun y => I.Kmat κm m t - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        I.sMat hΦ m κm t y) p x j k| ≤ κprev * Ccoef * (p.length.factorial : ℝ) * r ^ p.length)
    (hprev : ∀ p : List (Fin 2), p.length ≤ w.length + 2 →
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord p (iterateIncrement T i t))) ≤
        B ^ 2 * (((p.length + 2 * i).factorial : ℝ) * L ^ p.length) ^ 2)
    (hA3 : ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
      barNorm n (2 ^ 8 * (epsilon β I.Λ j)⁻¹) (Φ j t) ≤
        ENNReal.ofReal (2 ^ 5 * a β I.Λ j * epsilon β I.Λ j ^ 2 *
          (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3)))
    {Gcur : ℝ} (hB : 0 ≤ B) (hGc : 0 ≤ Gcur)
    (hvel : (256 * (epsilon β I.Λ (m - 1))⁻¹) / L ≤ 1 / 2)
    (d : ℕ → ℝ) (hd : ∀ n, 0 ≤ d n)
    (hcur : ∀ p ∈ (iterateSpatialSplits w).filter (fun p => !p.1.isEmpty),
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord p.2 (iterateIncrement T (i + 1)
          t))) ≤
        (Gcur * ((p.2.length + 2 * (i + 1)).factorial : ℝ) * L ^ p.2.length * d p.2.length) ^ 2) :
    |∫ z in iterateTruncatedCell s, vecDot
      (spaceGrad (amnrMaterial (streamVel (Φ (m - 1)))
        (fun t => iterateSpatialWord w (iterateIncrement T (i + 1) t)) z.1) z.2)
      ((Q z.1).mulVec (spaceGrad (iterateSpatialWord w (iterateIncrement T i z.1)) z.2))| ≤
      κprev / 24 * spaceTimeGradNormSq
        (fun t => spaceGrad (iterateSpatialWord w (iterateIncrement T (i + 1) t))) +
      (24 * Cscale ^ 2 * q ^ 2 + (1 + Cscale ^ 2 * (32 * Ccoef ^ 2)) * q) *
        (4 * κprev * B ^ 2 *
          (((w.length + 2 + 2 * i).factorial : ℝ) * L ^ w.length) ^ 2) +
      8 * D * (8192 * a β I.Λ (m - 1) * epsilon β I.Λ (m - 1)) * B * Gcur *
        (256 * (epsilon β I.Λ (m - 1))⁻¹) *
        (((w.length + 2 * (i + 1)).factorial : ℝ) * L ^ w.length) ^ 2 *
        ∑ k ∈ Finset.range w.length, (1 / (2 : ℝ)) ^ k * d (w.length - 1 - k) := by
  have hm1 : 1 ≤ m := by omega
  have hp := iterate_increment_terminal_current_material_corrected_bound I hΦ hT hθ hm1 hκm hκ
    hflow hs1 i hi w hL hg hD hCscale hq hQc hQ hscale hcoef hprev
  have hv := iterateIncrement_smooth_up_to_initial I hΦ hT hθ.1 (by omega : i ≤ Nstar β)
  have hu := iterateIncrement_smooth_up_to_initial I hΦ hT hθ.1 hi
  obtain ⟨hφ, _⟩ := hΦ.2 m hm1
  have hb : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => streamVel (Φ (m - 1)) z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    (AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ).smooth.contDiffOn
  have hbp (t : ℝ) (_ : 0 < t) : IsZ2Periodic (streamVel (Φ (m - 1)) t) := by
    intro k x
    simpa using (AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ).periodic 0 k t x
  have hup (t : ℝ) (ht : 0 < t) : IsZ2Periodic (iterateIncrement T (i + 1) t) :=
    iterateIncrement_periodic I hΦ hT hθ.2.1 hi ht.le
  have hvp (t : ℝ) (ht : 0 < t) : IsZ2Periodic (iterateIncrement T i t) :=
    iterateIncrement_periodic I hΦ hT hθ.2.1 (by omega : i ≤ Nstar β) ht.le
  have ha := AVenhance.Infra.Cutoff.a_pos (m := m - 1) I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have he := AVenhance.Infra.Cutoff.epsilon_pos (m := m - 1) I.one_lt_beta I.beta_lt
      I.two_pow_seven_le
  have herr := iterate_terminal_transferred_material_error_analytic_bound hs1 hb hu hv hQc hbp hup
      hvp
    w (i + 1) hD (by positivity) hB hGc (by positivity) hL hvel d hd hQ
    (fun t x p hmem j => iterate_velocity_analytic_profile_of_A3 I hΦ hm hA3 t p.1
      (by
        have ho := iterateSpatialSplits_orders w (List.mem_filter.mp hmem).1
        have hl := iterateSpatialSplits_lower_order w hmem
        omega) x j)
    (fun k => by
      simpa only [List.length_cons, Nat.add_assoc, Nat.reduceAdd, mul_pow, mul_assoc,
        show w.length + 2 * (i + 1) - 1 = w.length + 1 + 2 * i by omega] using
        hprev (k :: w) (by simp only [List.length_cons]; omega)) hcur
  have hfs (t : ℝ) (l : ℤ) : ContDiff ℝ (⊤ : ℕ∞) (I.flowGrad hΦ m l t) :=
    (hflow l).comp (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)))
  have hA (t : ℝ) (_ : 0 ≤ t) : ContDiff ℝ (⊤ : ℕ∞)
      (fun y => I.Kmat κm m t - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        I.sMat hΦ m κm t y) := contDiff_const.add
      (AVenhance.Infra.Section5.sMat_spatial_contDiff I hΦ m hm1 κm t (hfs t))
  have hc := iterate_TForcing_coefficient_word_continuousOn I hΦ hm1 hκm κprev hflow
  have hFc := iterate_word_forcing_gradient_continuousOn hv hA hc w
  have hsol := increment_classical_forcing I hΦ hT hθ
    (fun t ht => (hA t ht.le).of_le (by simp)) i hi
  rw [iterate_terminal_commuted_current_pairing_split hs1 (v := fun t => iterateSpatialWord w
      (iterateIncrement T i t)) hsol hb
    (iterateSpatialWord_smooth_up_to_initial hv w) w hFc hQc]
  rw [sub_eq_add_neg]
  exact (abs_add_le _ _).trans (add_le_add hp (by simpa only [abs_neg] using herr))

end AVenhance.Infra.Section4
