/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesActualMaterialGradient
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTerminalPreviousMaterial

/-! # Iterates Actual Previous Material

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The actual previous-increment PDE, coefficient jets, and scalar induction
bounds yield the complete terminal previous-material budget. -/
theorem iterate_actual_terminal_previous_material_pairing_bound_of_A3 {β : ℝ} (I : Ingredients β)
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
    {D s : ℝ} (hQ : ∀ t j k, |Q t j k| ≤ D) (hκ : 0 < κprev) (hs1 : s ≤ 1) :
    |∫ z in iterateTruncatedCell s, vecDot
      (spaceGrad (iterateSpatialWord w (u z.1)) z.2)
      ((Q z.1).mulVec (spaceGrad (amnrMaterial (streamVel (Φ (m - 1)))
        (fun t => iterateSpatialWord w (iterateIncrement T (i + 1) t)) z.1) z.2))| ≤
      κprev / 24 * spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord w (u t))) +
      24 * D ^ 2 / κprev * (
      8 * κprev ^ 2 * Gcur ^ 2 *
        (((w.length + 2 + 2 * (i + 1)).factorial : ℝ) * L ^ (w.length + 2)) ^ 2 +
      512 * κprev ^ 2 * C ^ 2 * Gprev ^ 2 *
        (((w.length + 2 + 2 * i).factorial : ℝ) * L ^ (w.length + 2)) ^ 2 +
      544 * (8192 * a β I.Λ (m - 1) * epsilon β I.Λ (m - 1)) ^ 2 *
        (256 * (epsilon β I.Λ (m - 1))⁻¹) ^ 2 * Gcur ^ 2 *
        (((w.length + 1 + 2 * (i + 1)).factorial : ℝ) * L ^ w.length) ^ 2) := by
  have hm1 : 1 ≤ m := by omega
  obtain ⟨hφ, _⟩ := hΦ.2 m hm1
  have hb : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => streamVel (Φ (m - 1)) z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    (AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ).smooth.contDiffOn
  have hv := iterateIncrement_smooth_up_to_initial I hΦ hT hθ.1 (by omega : i ≤ Nstar β)
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
  have hp := iterate_terminal_previous_material_pairing_bound hsol hb hu w hFc hQc hQ hκ hs1
  have he := iterate_increment_material_gradient_energy_bound_of_A3 I hΦ hT hθ hm hκm hflow
    hA3 i hi w hL hg hvel hcoef hcur hprev
  exact hp.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left he
    (by positivity : 0 ≤ 24 * D ^ 2 / κprev)))

end AVenhance.Infra.Section4
