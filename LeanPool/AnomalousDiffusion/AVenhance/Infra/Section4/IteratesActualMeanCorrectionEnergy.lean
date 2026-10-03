/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesMeanCorrectionRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesAnalyticMatrixForcing
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesDiffusiveMaterialScale

/-! # Iterates Actual Mean Correction Energy

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The noncentered first-step forcing remainder has a squared smallness
energy gain from actual mean/spatial coefficient jets and scalar bounds. -/
theorem iterate_actual_mean_correction_energy_bound {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} (hm : 1 ≤ m) (hκm : 0 < κm) (hκ : 0 < κprev)
    (hflow : ∀ l : ℤ, ContDiff ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => I.flowGrad hΦ m l z.1 z.2))
    {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (w : List (Fin 2))
    {N C ρ r L : ℝ} (hL : 0 < L) (hg : 2 * (r / L) ^ 2 ≤ 1 / 2)
    (hD : ∀ t x v j k, |iterateMatrixWord
      (fun y => timeAvgMat (I.Kmat κm m) - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        I.sMat hΦ m κm t y) v x j k| ≤
      κprev * (C * ρ) * (v.length.factorial : ℝ) * r ^ v.length)
    (hE : ∀ v : List (Fin 2), v.length ≤ w.length + 2 →
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord v (u t))) ≤
        (N / Real.sqrt κprev) ^ 2 * ((v.length.factorial : ℝ) * L ^ v.length) ^ 2) :
    spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord w (vecDiv
      (fun y => (timeAvgMat (I.Kmat κm m) - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        I.sMat hΦ m κm t y).mulVec (spaceGrad (u t) y))))) ≤
      128 * κprev * C ^ 2 * ρ ^ 2 * N ^ 2 *
        (((w.length + 2).factorial : ℝ) * L ^ (w.length + 2)) ^ 2 := by
  have hfs (t : ℝ) (l : ℤ) : ContDiff ℝ (⊤ : ℕ∞) (I.flowGrad hΦ m l t) :=
    (hflow l).comp (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)))
  have hA (t : ℝ) (_ : 0 ≤ t) : ContDiff ℝ (⊤ : ℕ∞)
      (fun y => timeAvgMat (I.Kmat κm m) - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        I.sMat hΦ m κm t y) := contDiff_const.add
    (AVenhance.Infra.Section5.sMat_spatial_contDiff I hΦ m hm κm t (hfs t))
  have ht := iterate_analytic_matrix_forcing_energy_bound hu hA
    (iterate_mean_correction_word_continuousOn I hΦ hm hκm κprev hflow) w 0 hL hg hD
    (fun v hv => by simpa only [Nat.add_zero] using hE v hv)
  simp only [Nat.add_zero] at ht
  have hn := iterate_diffusive_material_normalization (N := N) hκ
  have he : 128 * κprev ^ 2 * (C * ρ) ^ 2 * (N / Real.sqrt κprev) ^ 2 =
      128 * κprev * C ^ 2 * ρ ^ 2 * N ^ 2 := by
    calc
      _ = 128 * C ^ 2 * ρ ^ 2 * (κprev ^ 2 * (N / Real.sqrt κprev) ^ 2) := by ring
      _ = _ := by rw [hn]; ring
  rw [he] at ht
  exact ht

end AVenhance.Infra.Section4
