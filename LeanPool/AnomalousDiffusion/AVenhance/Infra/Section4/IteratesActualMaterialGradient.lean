/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesMaterialGradientEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesActualErrorGradient
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordAnalyticForcing

/-! Actual increment material-gradient energy from forcing and velocity bounds. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The previous-increment material estimate follows from its actual PDE,
 analytic coefficient jets, the stream-regularity estimates, and the two preceding scalar energies.
 No material or differentiated forcing bound is supplied as a premise. -/
theorem iterate_increment_material_gradient_energy_bound_of_A3 {β : ℝ} (I : Ingredients β)
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
        Gprev ^ 2 * (((q.length + 2 * i).factorial : ℝ) * L ^ q.length) ^ 2) :
    spaceTimeGradNormSq (fun t => spaceGrad
      (amnrMaterial (streamVel (Φ (m - 1)))
        (fun s => iterateSpatialWord w (iterateIncrement T (i + 1) s)) t)) ≤
      8 * κprev ^ 2 * Gcur ^ 2 *
        (((w.length + 2 + 2 * (i + 1)).factorial : ℝ) * L ^ (w.length + 2)) ^ 2 +
      512 * κprev ^ 2 * C ^ 2 * Gprev ^ 2 *
        (((w.length + 2 + 2 * i).factorial : ℝ) * L ^ (w.length + 2)) ^ 2 +
      544 * (8192 * a β I.Λ (m - 1) * epsilon β I.Λ (m - 1)) ^ 2 *
        (256 * (epsilon β I.Λ (m - 1))⁻¹) ^ 2 * Gcur ^ 2 *
        (((w.length + 1 + 2 * (i + 1)).factorial : ℝ) * L ^ w.length) ^ 2 := by
  have hm1 : 1 ≤ m := by omega
  obtain ⟨hφ, _⟩ := hΦ.2 m hm1
  have hb : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => streamVel (Φ (m - 1)) z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    (AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ).smooth.contDiffOn
  have hv := iterateIncrement_smooth_up_to_initial I hΦ hT hθ.1 (by omega : i ≤ Nstar β)
  have hu := iterateIncrement_smooth_up_to_initial I hΦ hT hθ.1 hi
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
  have hmat := iterate_commuted_material_gradient_energy_bound hsol hb w hFc
  have hLap := iterate_word_laplacian_gradient_energy_bound hu w
    (G := Gcur * ((w.length + 2 + 2 * (i + 1)).factorial : ℝ) * L ^ (w.length + 2))
    (fun k => by
      simpa only [List.length_cons, Nat.add_assoc, Nat.reduceAdd, mul_pow, mul_assoc] using
        hcur (k :: k :: w) (by simp only [List.length_cons]; omega))
  have hForcing := iterate_increment_analytic_TForcing_energy_bound I hΦ hT hθ.1 hm1 hκm hflow
    i (by omega : i ≤ Nstar β) w (2 * i) hL hg hcoef hprev
  have hError := iterate_increment_error_gradient_energy_bound_of_A3 I hΦ hT hθ.1 hm hA3
    (i + 1) hi w hL hvel (fun q hq => hcur q (by omega))
  have h₁ := mul_le_mul_of_nonneg_left hLap (by positivity : 0 ≤ 2 * κprev ^ 2)
  have h₂ := mul_le_mul_of_nonneg_left hForcing (by norm_num : (0 : ℝ) ≤ 4)
  have h₃ := mul_le_mul_of_nonneg_left hError (by norm_num : (0 : ℝ) ≤ 4)
  nlinarith only [hmat, h₁, h₂, h₃]

end AVenhance.Infra.Section4
