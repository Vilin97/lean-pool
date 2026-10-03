/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesActualMeanCorrectionEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesCancellation
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesFirstForcingGain
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTerminalTransposePairing

/-! # Iterates Actual First Remainder Pairing

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The actual noncentered first-step forcing pairing has a q-squared budget.
Its energy is derived from the literal mean/spatial matrix jets. -/
theorem iterate_actual_first_remainder_pairing_bound {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} (hm : 1 ≤ m) (hκm : 0 < κm) (hκ : 0 < κprev)
    (hflow : ∀ l : ℤ, ContDiff ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => I.flowGrad hΦ m l z.1 z.2))
    {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (w : List (Fin 2))
    {N C Cscale D ρ q r L s : ℝ} (hs1 : s ≤ 1) (hL : 0 < L)
    (hD : 0 ≤ D) (hCscale : 0 ≤ Cscale) (hρ : 0 ≤ ρ) (hq : 0 < q) (hρq : ρ ≤ q)
    (hg : 2 * (r / L) ^ 2 ≤ 1 / 2)
    (hQb : ∀ t j k, |iterateKmatPrimitive I κm m t j k| ≤ D)
    (hQscale : D * L ^ 2 ≤ Cscale * q)
    (hcoef : ∀ t x v j k, |iterateMatrixWord
      (fun y => timeAvgMat (I.Kmat κm m) - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        I.sMat hΦ m κm t y) v x j k| ≤
      κprev * (C * ρ) * (v.length.factorial : ℝ) * r ^ v.length)
    (hE : ∀ v : List (Fin 2), v.length ≤ w.length + 2 →
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord v (u t))) ≤
        (N / Real.sqrt κprev) ^ 2 * ((v.length.factorial : ℝ) * L ^ v.length) ^ 2) :
    |∫ z in iterateTruncatedCell s, vecDot
      (spaceGrad (iterateSpatialWord w (vecDiv (fun y =>
        (timeAvgMat (I.Kmat κm m) - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
          I.sMat hΦ m κm z.1 y).mulVec (spaceGrad (u z.1) y)))) z.2)
      ((iterateKmatPrimitive I κm m z.1).mulVec (spaceGrad (iterateSpatialWord w (u z.1)) z.2))| ≤
      (1 + 128 * Cscale ^ 2 * C ^ 2) * q ^ 2 *
        (N * ((w.length + 2).factorial : ℝ) * L ^ w.length) ^ 2 := by
  have hfs (t : ℝ) (l : ℤ) : ContDiff ℝ (⊤ : ℕ∞) (I.flowGrad hΦ m l t) :=
    (hflow l).comp (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)))
  have hA (t : ℝ) (_ : 0 ≤ t) : ContDiff ℝ (⊤ : ℕ∞)
      (fun y => timeAvgMat (I.Kmat κm m) - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        I.sMat hΦ m κm t y) := contDiff_const.add
    (AVenhance.Infra.Section5.sMat_spatial_contDiff I hΦ m hm κm t (hfs t))
  have hFc := iterate_word_forcing_gradient_continuousOn hu hA
    (iterate_mean_correction_word_continuousOn I hΦ hm hκm κprev hflow) w
  have hQc : ContinuousOn (fun z : AmnrSpace => iterateKmatPrimitive I κm m z.1)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    apply continuousOn_pi.mpr
    intro j
    apply continuousOn_pi.mpr
    intro k
    exact (iterateKmatPrimitive_entry_joint_contDiff I hκm hm j k).continuous.continuousOn
  have hp := iterate_terminal_transpose_pairing_bound_of_continuity
    (Q := iterateKmatPrimitive I κm m)
    (a := fun t => spaceGrad (iterateSpatialWord w (vecDiv (fun y =>
      (timeAvgMat (I.Kmat κm m) - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        I.sMat hΦ m κm t y).mulVec (spaceGrad (u t) y)))))
    (b := fun t => spaceGrad (iterateSpatialWord w (u t)))
    hs1 (mul_pos hκ (sq_pos_of_pos hq)) hFc
    (iterate_word_gradient_smooth_up_to_initial hu w).continuousOn hQc hQb
  have hForce := iterate_actual_mean_correction_energy_bound (N := N) (C := C) (ρ := ρ) (r := r)
      (L := L) I hΦ hm hκm hκ hflow hu w
    hL hg hcoef hE
  have hfact : (w.length.factorial : ℝ) ≤ ((w.length + 2).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega : w.length ≤ w.length + 2)
  have hweight := (sq_le_sq₀ (by positivity) (by positivity)).mpr
    (mul_le_mul_of_nonneg_right hfact (by positivity : 0 ≤ L ^ w.length))
  have hPrev := mul_le_mul_of_nonneg_left (hE w (by omega)) hκ.le
  have hn := iterate_diffusive_gradient_normalization (N := N) hκ
  have hPrev' : κprev * spaceTimeGradNormSq
      (fun t => spaceGrad (iterateSpatialWord w (u t))) ≤
      (N * ((w.length + 2).factorial : ℝ) * L ^ w.length) ^ 2 := by
    calc
      _ ≤ N ^ 2 * ((w.length.factorial : ℝ) * L ^ w.length) ^ 2 := by
        convert hPrev using 1
        rw [← mul_assoc, hn]
      _ ≤ N ^ 2 * (((w.length + 2).factorial : ℝ) * L ^ w.length) ^ 2 :=
        mul_le_mul_of_nonneg_left hweight (sq_nonneg N)
      _ = _ := by ring
  have hGain := iterate_first_remainder_forcing_gain (Ccoef := C) (L := L) hκ hD hCscale hρ hq
    (by positivity : 0 ≤ (N * ((w.length + 2).factorial : ℝ) * L ^ w.length) ^ 2)
    hQscale hρq hPrev' (by
      convert hForce using 1
      simp only [pow_add]
      ring)
  exact hp.trans hGain

end AVenhance.Infra.Section4
