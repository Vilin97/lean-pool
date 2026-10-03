/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordSource
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesStreamPairing

/-! Stream-regularity coefficient bounds in the first-derivative drift estimate. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open AVenhance

theorem IteratesStreamPhysical.iterate_A3_high_order_fraction_le_one {n : ℕ} (hn : 2 ≤ n) :
    ((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3 ≤ 1 := by
  have hp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  apply (div_le_one (pow_pos hp 3)).mpr
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have ht : 0 ≤ (n : ℝ) ^ 2 * ((n : ℝ) - 2) := mul_nonneg (sq_nonneg _) (by linarith)
  nlinarith only [hn', ht, sq_nonneg ((n : ℝ) - 2)]

/-- All high spatial stream jets obey the source factorial profile under the
stream-regularity premise. This is the coefficient profile used in the drift sum. -/
theorem iterate_stream_word_factorial_bound_of_A3 {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 2 ≤ m)
    (hA3 : ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
      barNorm n (2 ^ 8 * (epsilon β I.Λ j)⁻¹) (Φ j t) ≤
        ENNReal.ofReal (2 ^ 5 * a β I.Λ j * epsilon β I.Λ j ^ 2 *
          (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3)))
    (t : ℝ) (w : List (Fin 2)) (hw : 2 ≤ w.length) (x : Vec 2) :
    |iterateSpatialWord w (Φ (m - 1) t) x| ≤
      2 ^ 5 * a β I.Λ (m - 1) * epsilon β I.Λ (m - 1) ^ 2 *
        (w.length.factorial : ℝ) *
        (2 ^ 8 * (epsilon β I.Λ (m - 1))⁻¹) ^ w.length /
        ((w.length : ℝ) + 1) ^ 2 := by
  obtain ⟨hprev, _⟩ := hΦ.2 m (by omega)
  have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (t, y)) := by fun_prop
  have hs : ContDiff ℝ (⊤ : ℕ∞) (Φ (m - 1) t) := hprev.1.comp hmap
  have he : 0 < epsilon β I.Λ (m - 1) :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hbase : 0 ≤ 2 ^ 5 * a β I.Λ (m - 1) * epsilon β I.Λ (m - 1) ^ 2 := by
    unfold a
    positivity
  have hb := mul_le_of_le_one_right hbase
      (IteratesStreamPhysical.iterate_A3_high_order_fraction_le_one hw)
  have hbar := (hA3 (m - 1) (by omega) t w.length hw).trans (ENNReal.ofReal_le_ofReal hb)
  exact iterate_word_abs_factorial_bound_of_barNorm hs (by positivity) hbase w hbar x

/-- The Hessian entries needed by the first-derivative drift error have a
fixed numerical bound times the physical stream-amplitude scale. -/
theorem iterate_stream_second_jet_bound_of_A3 {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 2 ≤ m)
    (hA3 : ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
      barNorm n (2 ^ 8 * (epsilon β I.Λ j)⁻¹) (Φ j t) ≤
        ENNReal.ofReal (2 ^ 5 * a β I.Λ j * epsilon β I.Λ j ^ 2 *
          (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3)))
    (t : ℝ) (x : Vec 2) (i j : Fin 2) :
    |spaceGrad (fun y => spaceGrad (Φ (m - 1) t) y j) x i| ≤
      (2 : ℝ) ^ 19 * a β I.Λ (m - 1) := by
  have h := iterate_stream_word_factorial_bound_of_A3 I hΦ hm hA3 t [i, j] (by simp) x
  have hep : 0 < epsilon β I.Λ (m - 1) :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have he : epsilon β I.Λ (m - 1) ≠ 0 := hep.ne'
  have ha : 0 ≤ a β I.Λ (m - 1) := by unfold a; positivity
  norm_num [iterateSpatialWord] at h
  have heq : 32 * a β I.Λ (m - 1) * epsilon β I.Λ (m - 1) ^ 2 * 2 *
      (256 * (epsilon β I.Λ (m - 1))⁻¹) ^ 2 / 9 =
      (4194304 / 9 : ℝ) * a β I.Λ (m - 1) := by
    field_simp
    ring
  rw [heq] at h
  exact h.trans (mul_le_mul_of_nonneg_right (by norm_num) ha)

/-- The stream-regularity estimates also control every positive-order velocity jet appearing in
the material oscillatory errors. The component formula and derivative
commutation are proved from the stream velocity. -/
theorem iterate_velocity_word_bound_of_A3 {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 2 ≤ m)
    (hA3 : ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
      barNorm n (2 ^ 8 * (epsilon β I.Λ j)⁻¹) (Φ j t) ≤
        ENNReal.ofReal (2 ^ 5 * a β I.Λ j * epsilon β I.Λ j ^ 2 *
          (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3)))
    (t : ℝ) (w : List (Fin 2)) (hw : 1 ≤ w.length) (x : Vec 2) (i : Fin 2) :
    |iterateSpatialWord w (fun y => streamVel (Φ (m - 1)) t y i) x| ≤
      2 ^ 5 * a β I.Λ (m - 1) * epsilon β I.Λ (m - 1) ^ 2 *
        ((w.length + 1).factorial : ℝ) *
        (2 ^ 8 * (epsilon β I.Λ (m - 1))⁻¹) ^ (w.length + 1) /
        ((w.length : ℝ) + 2) ^ 2 := by
  obtain ⟨hprev, _⟩ := hΦ.2 m (by omega)
  have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (t, y)) := by fun_prop
  have hs : ContDiff ℝ (⊤ : ℕ∞) (Φ (m - 1) t) := hprev.1.comp hmap
  fin_cases i
  · change |iterateSpatialWord w (fun y => streamVel (Φ (m - 1)) t y (0 : Fin 2)) x| ≤ _
    have heq : (fun y => streamVel (Φ (m - 1)) t y 0) =
        -(fun y => spaceGrad (Φ (m - 1) t) y 1) := by
      funext y
      simp [streamVel, sigmaMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [heq, iterateSpatialWord_neg, iterateSpatialWord_gradient hs]
    have h := iterate_stream_word_factorial_bound_of_A3 I hΦ hm hA3 t (1 :: w) (by simpa using hw) x
    simpa only [Pi.neg_apply, abs_neg, iterateSpatialWord, List.length_cons,
      Nat.cast_add, Nat.cast_one, add_assoc, show (1 : ℝ) + 1 = 2 by norm_num] using h
  · change |iterateSpatialWord w (fun y => streamVel (Φ (m - 1)) t y (1 : Fin 2)) x| ≤ _
    have heq : (fun y => streamVel (Φ (m - 1)) t y 1) =
        fun y => spaceGrad (Φ (m - 1) t) y 0 := by
      funext y
      simp [streamVel, sigmaMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [heq, iterateSpatialWord_gradient hs]
    have h := iterate_stream_word_factorial_bound_of_A3 I hΦ hm hA3 t (0 :: w) (by simpa using hw) x
    simpa only [iterateSpatialWord, List.length_cons, Nat.cast_add, Nat.cast_one, add_assoc, show
        (1 : ℝ) + 1 = 2 by norm_num] using h

end AVenhance.Infra.Section4
