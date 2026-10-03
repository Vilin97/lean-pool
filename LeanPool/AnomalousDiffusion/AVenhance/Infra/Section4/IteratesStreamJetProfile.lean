/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesStreamCoefficient
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesStreamPhysical

/-! The stream-regularity estimates give the actual high stream-matrix analytic profile. -/

@[expose] public section

noncomputable section
open Homogenization
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open AVenhance

/-- The fixed skew matrix introduces no coefficient loss. -/
theorem iterate_stream_matrix_word_abs_le {φ : Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (w : List (Fin 2)) (x : Vec 2) (i j : Fin 2) :
    |iterateMatrixWord (fun y => φ y • sigmaMat) w x i j| ≤ |iterateSpatialWord w φ x| := by
  rw [iterateMatrixWord_stream hφ]
  fin_cases i <;> fin_cases j <;> simp [sigmaMat, abs_nonneg]

/-- High actual stream matrix jets obey the factorial profile under the
 stream-regularity premise. The additional source denominator is safely discarded. -/
theorem iterate_stream_matrix_profile_of_A3 {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m)
    (hA3 : ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
      barNorm n (2 ^ 8 * (epsilon β I.Λ j)⁻¹) (Φ j t) ≤
        ENNReal.ofReal (2 ^ 5 * a β I.Λ j * epsilon β I.Λ j ^ 2 *
          (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3)))
    (t : ℝ) (w : List (Fin 2)) (hw : 2 ≤ w.length) (x : Vec 2) (i j : Fin 2) :
    |iterateMatrixWord (fun y => Φ (m - 1) t y • sigmaMat) w x i j| ≤
      32 * a β I.Λ (m - 1) * epsilon β I.Λ (m - 1) ^ 2 *
        (w.length.factorial : ℝ) * (256 * (epsilon β I.Λ (m - 1))⁻¹) ^ w.length := by
  obtain ⟨hφ, _⟩ := hΦ.2 m (by omega)
  have hs : ContDiff ℝ (⊤ : ℕ∞) (Φ (m - 1) t) :=
    hφ.1.comp (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (t, y)))
  have ha := AVenhance.Infra.Cutoff.a_pos (m := m - 1) I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have he := AVenhance.Infra.Cutoff.epsilon_pos (m := m - 1) I.one_lt_beta I.beta_lt
      I.two_pow_seven_le
  have hd : 1 ≤ ((w.length : ℝ) + 1) ^ 2 := by
    have hn : (0 : ℝ) ≤ w.length := Nat.cast_nonneg _
    nlinarith only [hn, sq_nonneg (w.length : ℝ)]
  have ht := iterate_stream_word_factorial_bound_of_A3 I hΦ hm hA3 t w hw x
  norm_num only [show (2 : ℝ) ^ 5 = 32 by norm_num, show (2 : ℝ) ^ 8 = 256 by norm_num] at ht
  exact (iterate_stream_matrix_word_abs_le hs w x i j).trans
    (ht.trans (div_le_self (by positivity) hd))

end AVenhance.Infra.Section4
