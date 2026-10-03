/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesPreviousMaterialScale

/-! # Iterates Actual Previous Squared Gain

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The actual preceding PDE gives both squared-gain amplitude contributions;
no material-gradient bound is supplied as an assumption. -/
theorem iterate_actual_previous_material_squared_gain_of_A3 {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ} (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (hθ : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hm : 2 ≤ m) (hκm : 0 < κm)
    (hflow : ∀ l : ℤ, ContDiff ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => I.flowGrad hΦ m l z.1 z.2))
    (hA3 : ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
      barNorm n (2 ^ 8 * (epsilon β I.Λ j)⁻¹) (Φ j t) ≤
        ENNReal.ofReal (2 ^ 5 * a β I.Λ j * epsilon β I.Λ j ^ 2 *
          (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3)))
    (i : ℕ) (hi : i + 1 ≤ Nstar β) (w : List (Fin 2)) {C Gcur Gprev r L : ℝ}
    (hL : 0 < L) (hg : 2 * (r / L) ^ 2 ≤ 1 / 2)
    (hvel : 2 * ((256 * (epsilon β I.Λ (m - 1))⁻¹) / L) ^ 2 ≤ 1 / 2)
    (hcoef : ∀ t x q, ∀ j k, |iterateMatrixWord
      (fun y => I.Kmat κm m t - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        I.sMat hΦ m κm t y) q x j k| ≤ κprev * C * (q.length.factorial : ℝ) * r ^ q.length)
    (hcur : ∀ q : List (Fin 2), q.length ≤ w.length + 2 →
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord q (iterateIncrement T (i + 1)
          t))) ≤
        Gcur ^ 2 * (((q.length + 2 * (i + 1)).factorial : ℝ) * L ^ q.length) ^ 2)
    (hprev : ∀ q : List (Fin 2), q.length ≤ w.length + 2 →
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord q (iterateIncrement T i t))) ≤
        Gprev ^ 2 * (((q.length + 2 * i).factorial : ℝ) * L ^ q.length) ^ 2)
    {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {Q : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hQc : ContinuousOn (fun z : AmnrSpace => Q z.1) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {D s : ℝ} (hQ : ∀ t j k, |Q t j k| ≤ D) (hκ : 0 < κprev) (hs1 : s ≤ 1)
    {Cs Cv q : ℝ} (hCs : 0 ≤ Cs) (hCv : 0 ≤ Cv) (hq : 0 ≤ q)
    (hscale : D * L ^ 2 ≤ Cs * q)
    (hvelocity : (8192 * a β I.Λ (m - 1) * epsilon β I.Λ (m - 1)) *
      (256 * (epsilon β I.Λ (m - 1))⁻¹) ≤ Cv * κprev * L ^ 2) :
    |∫ z in iterateTruncatedCell s, vecDot
      (spaceGrad (iterateSpatialWord w (u z.1)) z.2)
      ((Q z.1).mulVec (spaceGrad (amnrMaterial (streamVel (Φ (m - 1)))
        (fun t => iterateSpatialWord w (iterateIncrement T (i + 1) t)) z.1) z.2))| ≤
      κprev / 24 * spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord w (u t))) +
      Cs ^ 2 * q ^ 2 * κprev *
        ((192 + 13056 * Cv ^ 2) * Gcur ^ 2 *
          (((w.length + 2 + 2 * (i + 1)).factorial : ℝ) * L ^ w.length) ^ 2 +
        12288 * C ^ 2 * Gprev ^ 2 *
          (((w.length + 2 + 2 * i).factorial : ℝ) * L ^ w.length) ^ 2) := by
  have hp := iterate_actual_terminal_previous_material_pairing_bound_of_A3 I hΦ hT hθ hm hκm
    hflow hA3 i hi w hL hg hvel hcoef hcur hprev hu hQc hQ hκ hs1
  have he := AVenhance.Infra.Cutoff.epsilon_pos (m := m - 1)
    I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have ha := AVenhance.Infra.Cutoff.a_pos (m := m - 1)
    I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hs := iterate_previous_material_scale_bound w.length (2 * (i + 1)) (2 * i)
    (Cc := C) (Gc := Gcur) (Gp := Gprev) hκ
    ((abs_nonneg _).trans (hQ 0 0 0)) (by positivity) (by positivity) hL hCs hCv hq
    hscale hvelocity
  exact hp.trans (add_le_add le_rfl hs)

end AVenhance.Infra.Section4
