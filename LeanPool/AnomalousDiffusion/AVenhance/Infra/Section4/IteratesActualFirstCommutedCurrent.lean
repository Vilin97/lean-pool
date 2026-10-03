/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesActualFirstCurrent
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTerminalCurrentSplit
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTerminalTransferredMaterial

/-! # Iterates Actual First Commuted Current

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

theorem iterate_actual_first_commuted_current_material_bound {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) (hNstar : 1 ≤ Nstar β)
    {m : ℕ} {κm κ : ℝ} (hm : 1 ≤ m) (hκm : 0 < κm) (hκ : 0 < κ)
    {θprev : ℝ → Vec 2 → ℝ} {u₀ : Vec 2 → ℝ}
    (hsol : IsClassicalSol (streamVel (Φ (m - 1))) κ (fun _ _ => 0) u₀ θprev)
    {T : ℕ → ℝ → Vec 2 → ℝ}
    (hT : I.IsTIterates hΦ m κm κ u₀ θprev T)
    (hb : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => streamVel (Φ (m - 1)) z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (w : List (Fin 2))
    (hflow : ∀ l : ℤ, ContDiff ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => I.flowGrad hΦ m l z.1 z.2))
    {B N r L C Ccoef D ρ q s : ℝ} (hB : 0 ≤ B) (hN : 0 ≤ N) (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hD : 0 ≤ D) (hq : 0 < q) (hρ : 0 ≤ ρ) (hρq : ρ ≤ q) (hL : 0 < L) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hg : 2 * (r / L) ^ 2 ≤ 1 / 2) (hscale : B * r ≤ C * κ * L ^ 2)
    (hQb : ∀ t j k, |iterateKmatPrimitive I κm m t j k| ≤ D)
    (hQscale : D * L ^ 2 ≤ C * q)
    (hjet : ∀ j k t x p, p ∈ (iterateSpatialSplits (j :: k :: w)).filter
      (fun p => decide (1 ≤ p.1.length)) → ∀ a,
      |iterateSpatialWord p.1 (fun y => streamVel (Φ (m - 1)) t y a) x| ≤
        B * (p.1.length.factorial : ℝ) * r ^ p.1.length)
    (hE : ∀ v : List (Fin 2), v.length ≤ w.length + 3 →
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord v (θprev t))) ≤
        (N / Real.sqrt κ) ^ 2 * ((v.length.factorial : ℝ) * L ^ v.length) ^ 2)
    (hcoef : ∀ t x v j k, |iterateMatrixWord
      (fun y => timeAvgMat (I.Kmat κm m) - κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        I.sMat hΦ m κm t y) v x j k| ≤
      κ * (Ccoef * ρ) * (v.length.factorial : ℝ) * r ^ v.length)
    (hTE : ∀ j k, l2NormSq (iterateSpatialWord (j :: k :: w) (θprev s)) ≤
      (N * ((w.length + 2).factorial : ℝ) * L ^ (w.length + 2)) ^ 2)
    {Gcur : ℝ} (hGc : 0 ≤ Gcur) (d : ℕ → ℝ) (hd : ∀ n, 0 ≤ d n)
    (hvel : ∀ t x p, p ∈ (iterateSpatialSplits w).filter (fun p => !p.1.isEmpty) → ∀ j,
      |iterateSpatialWord p.1 (fun y => streamVel (Φ (m - 1)) t y j) x| ≤
        B * (p.1.length.factorial : ℝ) * r ^ p.1.length)
    (hcur : ∀ p ∈ (iterateSpatialSplits w).filter (fun p => !p.1.isEmpty),
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord p.2 (iterateIncrement T 1 t))) ≤
        (Gcur * ((p.2.length + 2).factorial : ℝ) * L ^ p.2.length * d p.2.length) ^ 2) :
    |∫ z in iterateTruncatedCell s, vecDot
      (spaceGrad (amnrMaterial (streamVel (Φ (m - 1)))
        (fun t => iterateSpatialWord w (iterateIncrement T 1 t)) z.1) z.2)
      ((iterateKmatPrimitive I κm m z.1).mulVec
        (spaceGrad (iterateSpatialWord w (θprev z.1)) z.2))| ≤
      κ / 24 * spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord w (iterateIncrement T 1
          t))) +
      (96 * C ^ 2 + (8 + 32 * Real.sqrt (8 + 64 * C ^ 2)) * C ^ 2 +
        1 + 128 * C ^ 2 * Ccoef ^ 2) * q ^ 2 *
        (N * ((w.length + 2).factorial : ℝ) * L ^ w.length) ^ 2 +
      8 * D * B * (N / Real.sqrt κ) * Gcur * r *
        (((w.length + 2).factorial : ℝ) * L ^ w.length) ^ 2 *
        ∑ k ∈ Finset.range w.length, (1 / (2 : ℝ)) ^ k * d (w.length - 1 - k) := by
  have hp := iterate_actual_first_current_material_bound I hΦ hNstar hm hκm hκ hsol hT hb w hflow
    hB hN hr hC hD hq hρ hρq hL hs hs1 hg hscale hQb hQscale hjet hE hcoef hTE
  have hu := iterateIncrement_smooth_up_to_initial I hΦ hT hsol.1 hNstar
  have hQc : ContinuousOn (iterateKmatPrimitive I κm m) (Set.Ici (0 : ℝ)) := by
    apply continuousOn_pi.mpr
    intro j
    apply continuousOn_pi.mpr
    intro k
    exact (iterateKmatPrimitive_entry_contDiff I hκm hm j k).continuous.continuousOn
  obtain ⟨hφ, _⟩ := hΦ.2 m hm
  have hbp (t : ℝ) (_ : 0 < t) : IsZ2Periodic (streamVel (Φ (m - 1)) t) := by
    intro k x
    simpa using (AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ).periodic 0 k t x
  have hup (t : ℝ) (ht : 0 < t) : IsZ2Periodic (iterateIncrement T 1 t) :=
    iterateIncrement_periodic I hΦ hT hsol.2.1 hNstar ht.le
  have hgain : r / L ≤ 1 / 2 := by nlinarith only [hg]
  have herr := iterate_terminal_transferred_material_error_analytic_bound
    (Q := iterateKmatPrimitive I κm m) (Gprev := N / Real.sqrt κ)
    (Gcur := Gcur) (B := B) (r := r) (L := L) hs1 hb hu hsol.1 hQc hbp hup
    (fun t ht => hsol.2.1 t ht.le) w 1 hD hB (by positivity) hGc hr hL hgain d hd hQb hvel
    (fun k => by
      simpa only [List.length_cons, Nat.add_assoc, Nat.reduceAdd, mul_pow, mul_assoc,
        show w.length + 2 * 1 - 1 = w.length + 1 by omega] using
        hE (k :: w) (by simp only [List.length_cons]; omega))
    (fun p hp => by simpa only [Nat.mul_one] using hcur p hp)
  have hfs (t : ℝ) (l : ℤ) : ContDiff ℝ (⊤ : ℕ∞) (I.flowGrad hΦ m l t) :=
    (hflow l).comp (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)))
  have hA (t : ℝ) (_ : 0 ≤ t) : ContDiff ℝ (⊤ : ℕ∞)
      (fun y => I.Kmat κm m t - κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) + I.sMat hΦ m κm t y) :=
    contDiff_const.add (AVenhance.Infra.Section5.sMat_spatial_contDiff I hΦ m hm κm t (hfs t))
  have hinc := increment_classical_forcing I hΦ hT hsol
    (fun t ht => (hA t ht.le).of_le (by simp)) 0 (by simpa using hNstar)
  simp only [iterateIncrement_zero, hT.1] at hinc
  have hFc := iterate_word_forcing_gradient_continuousOn hsol.1 hA
    (iterate_TForcing_coefficient_word_continuousOn I hΦ hm hκm κ hflow) w
  rw [iterate_terminal_commuted_current_pairing_split hs1
    (v := fun t => iterateSpatialWord w (θprev t)) hinc hb
    (iterateSpatialWord_smooth_up_to_initial hsol.1 w) w hFc hQc]
  rw [sub_eq_add_neg]
  exact (abs_add_le _ _).trans (add_le_add hp (by simpa only [abs_neg, Nat.mul_one] using herr))

end AVenhance.Infra.Section4
