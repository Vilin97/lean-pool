/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesActualMaterialGradient
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTruncatedCurrentRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesCurrentCorrectedBudget

/-! Actual current increment with the corrected material budget. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Derive the linear and quadratic oscillatory remainder from actual forcing
jets and the preceding increment energies. -/
theorem iterate_increment_terminal_current_material_corrected_bound {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ} (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (hθ : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hm : 1 ≤ m) (hκm : 0 < κm) (hκ : 0 < κprev)
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
        B ^ 2 * (((p.length + 2 * i).factorial : ℝ) * L ^ p.length) ^ 2) :
    |∫ z in iterateTruncatedCell s, vecDot
      (spaceGrad (iterateSpatialWord w
        (amnrMaterial (streamVel (Φ (m - 1))) (iterateIncrement T (i + 1)) z.1)) z.2)
      ((Q z.1).mulVec (spaceGrad (iterateSpatialWord w (iterateIncrement T i z.1)) z.2))| ≤
      κprev / 24 * spaceTimeGradNormSq
        (fun t => spaceGrad (iterateSpatialWord w (iterateIncrement T (i + 1) t))) +
      (24 * Cscale ^ 2 * q ^ 2 + (1 + Cscale ^ 2 * (32 * Ccoef ^ 2)) * q) *
        (4 * κprev * B ^ 2 *
          (((w.length + 2 + 2 * i).factorial : ℝ) * L ^ w.length) ^ 2) := by
  have hv := iterateIncrement_smooth_up_to_initial I hΦ hT hθ.1 (by omega : i ≤ Nstar β)
  have hfs (t : ℝ) (l : ℤ) : ContDiff ℝ (⊤ : ℕ∞) (I.flowGrad hΦ m l t) :=
    (hflow l).comp (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)))
  have hA (t : ℝ) (_ : 0 ≤ t) : ContDiff ℝ (⊤ : ℕ∞)
      (fun y => I.Kmat κm m t - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        I.sMat hΦ m κm t y) := contDiff_const.add
      (AVenhance.Infra.Section5.sMat_spatial_contDiff I hΦ m hm κm t (hfs t))
  have hc := iterate_TForcing_coefficient_word_continuousOn I hΦ hm hκm κprev hflow
  have hFc := iterate_word_forcing_gradient_continuousOn hv hA hc w
  have hsol := increment_classical_forcing I hΦ hT hθ
    (fun t ht => (hA t ht.le).of_le (by simp)) i hi
  have hwp (t : ℝ) (ht : 0 < t) : IsZ2Periodic
      (iterateSpatialWord w (iterateIncrement T i t)) := by
    have hs := hv.comp_contDiff
      (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (t, y)))
      (fun _ => ⟨ht.le, Set.mem_univ _⟩)
    exact iterateSpatialWord_periodic hs (iterateIncrement_periodic I hΦ hT hθ.2.1
      (by omega : i ≤ Nstar β) ht.le) w
  obtain ⟨hφ, _⟩ := hΦ.2 m hm
  have hb : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => streamVel (Φ (m - 1)) z.1 z.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) :=
    (AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ).smooth.contDiffOn
  have hp := iterate_truncated_current_word_material_pairing_bound_of_continuity hs1 hsol w hκ
    (mul_pos hκ hq) hQ (iterateSpatialWord_smooth_up_to_initial hv w) hwp
    (fun _ ht => iterate_classical_forcing_spatial_smooth hsol hb ht) hFc hQc
  have hLap := iterate_word_laplacian_gradient_energy_bound hv w
    (G := B * ((w.length + 2 + 2 * i).factorial : ℝ) * L ^ (w.length + 2))
    (fun k => by
      simpa only [List.length_cons, Nat.add_assoc, Nat.reduceAdd, mul_pow, mul_assoc] using
        hprev (k :: k :: w) (by simp only [List.length_cons]; omega))
  have hForce := iterate_increment_analytic_TForcing_energy_bound I hΦ hT hθ.1 hm hκm hflow
    i (by omega : i ≤ Nstar β) w (2 * i) hL hg hcoef hprev
  have hFact : ((w.length + 2 * i).factorial : ℝ) ≤
      ((w.length + 2 + 2 * i).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega : w.length + 2 * i ≤ w.length + 2 + 2 * i)
  have hweight := (sq_le_sq₀ (by positivity) (by positivity)).mpr
    (mul_le_mul_of_nonneg_right hFact (by positivity : 0 ≤ L ^ w.length))
  have hPrev := (hprev w (by omega)).trans
    (mul_le_mul_of_nonneg_left hweight (sq_nonneg B))
  have hGain := iterate_current_material_corrected_remainder_gain
    (g := spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord w (iterateIncrement T i t))))
    (gLap := spaceTimeGradNormSq (fun t x j => spaceLap
      (fun y => spaceGrad (iterateSpatialWord w (iterateIncrement T i t)) y j) x))
    (gF := spaceTimeGradNormSq (fun t => spaceGrad
      (iterateSpatialWord w (I.TForcing hΦ m κm κprev (iterateIncrement T i) t)))) hκ hD hCscale
    (by positivity : 0 ≤ 32 * Ccoef ^ 2) hq
    (by positivity : 0 ≤ 4 * κprev * B ^ 2 *
      (((w.length + 2 + 2 * i).factorial : ℝ) * L ^ w.length) ^ 2) hscale
    (E := 4 * κprev * B ^ 2 *
      (((w.length + 2 + 2 * i).factorial : ℝ) * L ^ w.length) ^ 2)
    (by
      have ht := mul_le_mul_of_nonneg_left hPrev hκ.le
      have hn : 0 ≤ κprev * B ^ 2 *
          (((w.length + 2 + 2 * i).factorial : ℝ) * L ^ w.length) ^ 2 := by positivity
      nlinarith only [ht, hn])
    (by
      have ht := mul_le_mul_of_nonneg_left hLap hκ.le
      convert ht using 1; simp only [pow_add]; ring)
    (by
      convert hForce using 1; simp only [pow_add]; ring)
  exact hp.trans (by linarith only [hGain])

end AVenhance.Infra.Section4
