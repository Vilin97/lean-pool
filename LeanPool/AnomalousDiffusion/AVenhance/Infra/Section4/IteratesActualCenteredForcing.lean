/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesCenteredHessianTransfer
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesActualHomogeneousHalfSquare

/-! # Iterates Actual Centered Forcing

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

theorem iterate_actual_centered_forcing_pairing_bound {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) (hNstar : 1 ≤ Nstar β)
    {m : ℕ} {κm κ : ℝ} (hm : 1 ≤ m) (hκm : 0 < κm) (hκ : 0 < κ)
    {u : ℝ → Vec 2 → ℝ} {u₀ : Vec 2 → ℝ}
    (hsol : IsClassicalSol (streamVel (Φ (m - 1))) κ (fun _ _ => 0) u₀ u)
    (hb : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => streamVel (Φ (m - 1)) z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (w : List (Fin 2))
    {B N r L C D q s : ℝ} (hB : 0 ≤ B) (hN : 0 ≤ N) (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hD : 0 ≤ D) (hq : 0 ≤ q) (hL : 0 < L) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hg : 2 * (r / L) ^ 2 ≤ 1 / 2) (hscale : B * r ≤ C * κ * L ^ 2)
    (hQb : ∀ t j k, |iterateKmatPrimitive I κm m t j k| ≤ D)
    (hQscale : D * L ^ 2 ≤ C * q)
    (hjet : ∀ j k t x p, p ∈ (iterateSpatialSplits (j :: k :: w)).filter
      (fun p => decide (1 ≤ p.1.length)) → ∀ a,
      |iterateSpatialWord p.1 (fun y => streamVel (Φ (m - 1)) t y a) x| ≤
        B * (p.1.length.factorial : ℝ) * r ^ p.1.length)
    (hE : ∀ v : List (Fin 2), v.length ≤ w.length + 3 →
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord v (u t))) ≤
        (N / Real.sqrt κ) ^ 2 * ((v.length.factorial : ℝ) * L ^ v.length) ^ 2)
    (hTE : ∀ j k, l2NormSq (iterateSpatialWord (j :: k :: w) (u s)) ≤
      (N * ((w.length + 2).factorial : ℝ) * L ^ (w.length + 2)) ^ 2) :
    |∫ z in iterateTruncatedCell s, vecDot
      (spaceGrad (fun y => ∑ j : Fin 2, ∑ k : Fin 2,
        (I.Kmat κm m z.1 j k - timeAvgMat (I.Kmat κm m) j k) *
          iterateSpatialWord (j :: k :: w) (u z.1) y) z.2)
      ((iterateKmatPrimitive I κm m z.1).mulVec
        (spaceGrad (iterateSpatialWord w (u z.1)) z.2))| ≤
      (8 + 32 * Real.sqrt (8 + 64 * C ^ 2)) * C ^ 2 * q ^ 2 *
        (N * ((w.length + 2).factorial : ℝ) * L ^ w.length) ^ 2 := by
  rw [iterate_centered_hessian_forcing_transfer I hNstar hm hκm hsol.1
    (fun t ht => hsol.2.1 t ht.le) w hs, abs_neg]
  exact iterate_actual_homogeneous_half_square_bound I hΦ hm hκm hκ hsol hb w
    hB hN hr hC hD hq hL hs hs1 hg hscale hQb hQscale hjet hE hTE

end AVenhance.Infra.Section4
