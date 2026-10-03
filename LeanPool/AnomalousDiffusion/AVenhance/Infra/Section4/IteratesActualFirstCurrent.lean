/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesActualFirstForcingPairing
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesRetainedCurrentRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordAnalyticForcing

/-! # Iterates Actual First Current

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

theorem iterate_actual_first_current_material_bound {β : ℝ} (I : Ingredients β)
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
      (N * ((w.length + 2).factorial : ℝ) * L ^ (w.length + 2)) ^ 2) :
    |∫ z in iterateTruncatedCell s, vecDot
      (spaceGrad (iterateSpatialWord w
        (amnrMaterial (streamVel (Φ (m - 1))) (iterateIncrement T 1) z.1)) z.2)
      ((iterateKmatPrimitive I κm m z.1).mulVec
        (spaceGrad (iterateSpatialWord w (θprev z.1)) z.2))| ≤
      κ / 24 * spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord w (iterateIncrement T 1
          t))) +
      (96 * C ^ 2 + (8 + 32 * Real.sqrt (8 + 64 * C ^ 2)) * C ^ 2 +
        1 + 128 * C ^ 2 * Ccoef ^ 2) * q ^ 2 *
        (N * ((w.length + 2).factorial : ℝ) * L ^ w.length) ^ 2 := by
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
  have hQc : ContinuousOn (iterateKmatPrimitive I κm m) (Set.Ici (0 : ℝ)) := by
    apply continuousOn_pi.mpr
    intro j
    apply continuousOn_pi.mpr
    intro k
    exact (iterateKmatPrimitive_entry_contDiff I hκm hm j k).continuous.continuousOn
  have hws := iterateSpatialWord_smooth_up_to_initial hsol.1 w
  have hwp (t : ℝ) (ht : 0 < t) : IsZ2Periodic (iterateSpatialWord w (θprev t)) := by
    have hus := hsol.1.comp_contDiff
      (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)))
      (fun _ => ⟨ht.le, Set.mem_univ _⟩)
    exact iterateSpatialWord_periodic hus (hsol.2.1 t ht.le) w
  have hbo : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => streamVel (Φ (m - 1)) z.1 z.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := hb.mono
    (show (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) ⊆
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) from fun z hz => ⟨(show 0 < z.1 from hz.1).le, hz.2⟩)
  have hp := iterate_terminal_retained_current_pairing_of_continuity
    (v := fun t => iterateSpatialWord w (θprev t)) hs1 hinc w hκ hQb hws hwp
    (fun _ ht => iterate_classical_forcing_spatial_smooth hinc hbo ht) hFc hQc
  have hForce := iterate_actual_first_forcing_pairing_bound I hΦ hNstar hm hκm hκ hsol hb w hflow
    hB hN hr hC hD hq hρ hρq hL hs hs1 hg hscale hQb hQscale hjet hE hcoef hTE
  have hLap := iterate_word_laplacian_gradient_energy_bound hsol.1 w
    (G := N / Real.sqrt κ * ((w.length + 2).factorial : ℝ) * L ^ (w.length + 2))
    (fun k => by
      simpa only [List.length_cons, Nat.add_assoc, Nat.reduceAdd, mul_pow, mul_assoc] using
        hE (k :: k :: w) (by simp only [List.length_cons]; omega))
  have hscaleSq := (sq_le_sq₀ (mul_nonneg hD (sq_nonneg L)) (mul_nonneg hC hq.le)).mpr hQscale
  have hn := iterate_diffusive_gradient_normalization (N := N) hκ
  have hLapTerm : 24 * κ * D ^ 2 * spaceTimeGradNormSq
      (fun t x j => spaceLap (fun y => spaceGrad (iterateSpatialWord w (θprev t)) y j) x) ≤
      96 * C ^ 2 * q ^ 2 * (N * ((w.length + 2).factorial : ℝ) * L ^ w.length) ^ 2 := by
    calc
      _ ≤ 24 * κ * D ^ 2 *
          (4 * (N / Real.sqrt κ * ((w.length + 2).factorial : ℝ) * L ^ (w.length + 2)) ^ 2) :=
        mul_le_mul_of_nonneg_left hLap (by positivity)
      _ = 96 * (κ * (N / Real.sqrt κ) ^ 2) *
          (((w.length + 2).factorial : ℝ) * L ^ w.length) ^ 2 * (D * L ^ 2) ^ 2 := by
        simp only [pow_add]
        ring
      _ = 96 * N ^ 2 * (((w.length + 2).factorial : ℝ) * L ^ w.length) ^ 2 *
          (D * L ^ 2) ^ 2 := by rw [hn]
      _ ≤ 96 * N ^ 2 * (((w.length + 2).factorial : ℝ) * L ^ w.length) ^ 2 *
          (C * q) ^ 2 := mul_le_mul_of_nonneg_left hscaleSq (by positivity)
      _ = _ := by ring
  exact hp.trans (by nlinarith only [hLapTerm, hForce])

end AVenhance.Infra.Section4
