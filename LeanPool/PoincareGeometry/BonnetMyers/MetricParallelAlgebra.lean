/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module


/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

public import LeanPool.PoincareGeometry.BonnetMyers.FiniteSum

/-! # Metric Parallel Algebra -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace BonnetMyersEntry

lemma metric_parallel_sum_cancel
    {n : ℕ} (w v dw dv u : Fin n → ℝ)
    (Γ : Fin n → Fin n → Fin n → ℝ) (G : Fin n → Fin n → ℝ)
    (hdw : ∀ i, dw i = -∑ l, ∑ k, w l * u k * Γ i l k)
    (hdv : ∀ j, dv j = -∑ l, ∑ k, v l * u k * Γ j l k) :
    ∑ i, ∑ j,
      ((dw i * v j + w i * dv j) * G i j +
        w i * v j *
          ((∑ l, ∑ k, u k * Γ l i k * G l j) +
            (∑ l, ∑ k, u k * Γ l j k * G i l))) = 0 := by
  simp_rw [hdw, hdv]
  ring_nf
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  simp_rw [sub_eq_add_neg, Finset.sum_mul]
  simp_rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
  have hAC :
      (∑ i, ∑ j, ∑ l, ∑ k,
        w l * u k * Γ i l k * v j * G i j) =
      (∑ i, ∑ j, ∑ l, ∑ k,
        v j * w i * (u k * Γ l i k * G l j)) := by
    calc
      (∑ i, ∑ j, ∑ l, ∑ k,
          w l * u k * Γ i l k * v j * G i j) =
          (∑ i, ∑ j, ∑ l, ∑ k,
            (w i * u k * Γ l i k * v j * G l j)) := by
        have hs := sum_swap_first_third
          (F := fun i j l k ↦ w i * u k * Γ l i k * v j * G l j)
        simpa only [mul_assoc] using hs
      _ = ∑ i, ∑ j, ∑ l, ∑ k,
            v j * w i * (u k * Γ l i k * G l j) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro l hl
        apply Finset.sum_congr rfl
        intro k hk
        ring
  have hBD :
      (∑ i, ∑ j, ∑ l, ∑ k,
        w i * (v l * u k * Γ j l k) * G i j) =
      (∑ i, ∑ j, ∑ l, ∑ k,
        v j * w i * (u k * Γ l j k * G i l)) := by
    calc
      (∑ i, ∑ j, ∑ l, ∑ k,
          w i * (v l * u k * Γ j l k) * G i j) =
          (∑ i, ∑ j, ∑ l, ∑ k,
            w i * (v j * u k * Γ l j k) * G i l) := by
        have hs := sum_swap_second_third
          (F := fun i j l k ↦ w i * (v j * u k * Γ l j k) * G i l)
        simpa only [mul_assoc] using hs
      _ = ∑ i, ∑ j, ∑ l, ∑ k,
            v j * w i * (u k * Γ l j k * G i l) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro l hl
        apply Finset.sum_congr rfl
        intro k hk
        ring
  rw [hAC, hBD]
  ring

lemma metric_parallel_frame_terms
    {n : ℕ} (w v u : Fin n → ℝ)
    (Γ : Fin n → Fin n → Fin n → ℝ) (G : Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, w i * v j *
      ((∑ l, ∑ k, u k * Γ l i k * G l j) +
        (∑ l, ∑ k, u k * Γ l j k * G i l))) =
      ∑ i, ∑ j,
        ((∑ l, ∑ k, w l * u k * Γ i l k) * v j +
          w i * (∑ l, ∑ k, v l * u k * Γ j l k)) * G i j := by
  have hAC :
      (∑ i, ∑ j, ∑ l, ∑ k,
        w l * u k * Γ i l k * v j * G i j) =
      (∑ i, ∑ j, ∑ l, ∑ k,
        v j * w i * (u k * Γ l i k * G l j)) := by
    calc
      (∑ i, ∑ j, ∑ l, ∑ k,
          w l * u k * Γ i l k * v j * G i j) =
          (∑ i, ∑ j, ∑ l, ∑ k,
            (w i * u k * Γ l i k * v j * G l j)) := by
        have hs := sum_swap_first_third
          (F := fun i j l k ↦ w i * u k * Γ l i k * v j * G l j)
        simpa only [mul_assoc] using hs
      _ = ∑ i, ∑ j, ∑ l, ∑ k,
            v j * w i * (u k * Γ l i k * G l j) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro l hl
        apply Finset.sum_congr rfl
        intro k hk
        ring
  have hBD :
      (∑ i, ∑ j, ∑ l, ∑ k,
        w i * (v l * u k * Γ j l k) * G i j) =
      (∑ i, ∑ j, ∑ l, ∑ k,
        v j * w i * (u k * Γ l j k * G i l)) := by
    calc
      (∑ i, ∑ j, ∑ l, ∑ k,
          w i * (v l * u k * Γ j l k) * G i j) =
          (∑ i, ∑ j, ∑ l, ∑ k,
            w i * (v j * u k * Γ l j k) * G i l) := by
        have hs := sum_swap_second_third
          (F := fun i j l k ↦ w i * (v j * u k * Γ l j k) * G i l)
        simpa only [mul_assoc] using hs
      _ = ∑ i, ∑ j, ∑ l, ∑ k,
            v j * w i * (u k * Γ l j k * G i l) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro l hl
        apply Finset.sum_congr rfl
        intro k hk
        ring
  calc
    (∑ i, ∑ j, w i * v j *
      ((∑ l, ∑ k, u k * Γ l i k * G l j) +
        (∑ l, ∑ k, u k * Γ l j k * G i l))) =
        (∑ i, ∑ j, ∑ l, ∑ k,
          v j * w i * (u k * Γ l i k * G l j)) +
      (∑ i, ∑ j, ∑ l, ∑ k,
          v j * w i * (u k * Γ l j k * G i l)) := by
      have hmul2 (a : ℝ) (f : Fin n → Fin n → ℝ) :
          a * (∑ l, ∑ k, f l k) = ∑ l, ∑ k, a * f l k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l hl
        rw [Finset.mul_sum]
      calc
        (∑ i, ∑ j, w i * v j *
          ((∑ l, ∑ k, u k * Γ l i k * G l j) +
            (∑ l, ∑ k, u k * Γ l j k * G i l))) =
            ∑ i, ∑ j,
              (w i * v j * (∑ l, ∑ k, u k * Γ l i k * G l j) +
                w i * v j * (∑ l, ∑ k, u k * Γ l j k * G i l)) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = (∑ i, ∑ j, w i * v j *
              (∑ l, ∑ k, u k * Γ l i k * G l j)) +
            (∑ i, ∑ j, w i * v j *
              (∑ l, ∑ k, u k * Γ l j k * G i l)) := by
          simp_rw [Finset.sum_add_distrib]
        _ = (∑ i, ∑ j, ∑ l, ∑ k,
              v j * w i * (u k * Γ l i k * G l j)) +
            (∑ i, ∑ j, ∑ l, ∑ k,
              v j * w i * (u k * Γ l j k * G i l)) := by
          congr 1
          · apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            rw [hmul2]
            apply Finset.sum_congr rfl
            intro l hl
            apply Finset.sum_congr rfl
            intro k hk
            ring
          · apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            rw [hmul2]
            apply Finset.sum_congr rfl
            intro l hl
            apply Finset.sum_congr rfl
            intro k hk
            ring
    _ = (∑ i, ∑ j, ∑ l, ∑ k,
          w l * u k * Γ i l k * v j * G i j) +
        (∑ i, ∑ j, ∑ l, ∑ k,
          w i * (v l * u k * Γ j l k) * G i j) := by
      rw [hAC, hBD]
    _ = ∑ i, ∑ j,
        ((∑ l, ∑ k, w l * u k * Γ i l k) * v j +
          w i * (∑ l, ∑ k, v l * u k * Γ j l k)) * G i j := by
      have hmul2 (a : ℝ) (f : Fin n → Fin n → ℝ) :
          a * (∑ l, ∑ k, f l k) = ∑ l, ∑ k, a * f l k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l hl
        rw [Finset.mul_sum]
      have hsum2_mul (f : Fin n → Fin n → ℝ) (a b : ℝ) :
          (∑ l, ∑ k, f l k) * a * b =
            ∑ l, ∑ k, f l k * a * b := by
        calc
          (∑ l, ∑ k, f l k) * a * b =
              (∑ l, ∑ k, f l k) * (a * b) := by ring
          _ = ∑ l, (∑ k, f l k) * (a * b) := by
            rw [Finset.sum_mul]
          _ = ∑ l, ∑ k, f l k * (a * b) := by
            apply Finset.sum_congr rfl
            intro l hl
            rw [Finset.sum_mul]
          _ = ∑ l, ∑ k, f l k * a * b := by
            apply Finset.sum_congr rfl
            intro l hl
            apply Finset.sum_congr rfl
            intro k hk
            ring
      calc
        (∑ i, ∑ j, ∑ l, ∑ k,
            w l * u k * Γ i l k * v j * G i j) +
          (∑ i, ∑ j, ∑ l, ∑ k,
            w i * (v l * u k * Γ j l k) * G i j) =
          (∑ i, ∑ j,
            (∑ l, ∑ k, w l * u k * Γ i l k) * v j * G i j) +
          (∑ i, ∑ j,
            (w i * (∑ l, ∑ k, v l * u k * Γ j l k)) * G i j) := by
            congr 1
            · apply Finset.sum_congr rfl
              intro i hi
              apply Finset.sum_congr rfl
              intro j hj
              symm
              exact hsum2_mul (fun l k ↦ w l * u k * Γ i l k)
                (v j) (G i j) |>.trans (by
                  apply Finset.sum_congr rfl
                  intro l hl
                  apply Finset.sum_congr rfl
                  intro k hk
                  ring)
            · apply Finset.sum_congr rfl
              intro i hi
              apply Finset.sum_congr rfl
              intro j hj
              calc
                ∑ l, ∑ k, w i * (v l * u k * Γ j l k) * G i j =
                    ∑ l, ∑ k, (w i * (v l * u k * Γ j l k)) * G i j := by
                      apply Finset.sum_congr rfl
                      intro l hl
                      apply Finset.sum_congr rfl
                      intro k hk
                      ring
                _ = (∑ l, ∑ k, w i * (v l * u k * Γ j l k)) * G i j := by
                      symm
                      rw [Finset.sum_mul]
                      apply Finset.sum_congr rfl
                      intro l hl
                      rw [Finset.sum_mul]
                _ = (w i * (∑ l, ∑ k, v l * u k * Γ j l k)) * G i j := by
                      congr 1
                      exact (hmul2 (w i) (fun l k ↦ v l * u k * Γ j l k)).symm
        _ = ∑ i, ∑ j,
            ((∑ l, ∑ k, w l * u k * Γ i l k) * v j +
              w i * (∑ l, ∑ k, v l * u k * Γ j l k)) * G i j := by
            symm
            calc
              ∑ i, ∑ j,
                  ((∑ l, ∑ k, w l * u k * Γ i l k) * v j +
                    w i * (∑ l, ∑ k, v l * u k * Γ j l k)) * G i j =
                  ∑ i, ((∑ j, (∑ l, ∑ k, w l * u k * Γ i l k) * v j * G i j) +
                    ∑ j, (w i * (∑ l, ∑ k, v l * u k * Γ j l k)) * G i j) := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    calc
                      ∑ j, ((∑ l, ∑ k, w l * u k * Γ i l k) * v j +
                        w i * (∑ l, ∑ k, v l * u k * Γ j l k)) * G i j =
                          ∑ j, ((∑ l, ∑ k, w l * u k * Γ i l k) * v j * G i j +
                            (w i * (∑ l, ∑ k, v l * u k * Γ j l k)) * G i j) := by
                            apply Finset.sum_congr rfl
                            intro j hj
                            ring
                      _ = (∑ j, (∑ l, ∑ k, w l * u k * Γ i l k) * v j * G i j) +
                          ∑ j, (w i * (∑ l, ∑ k, v l * u k * Γ j l k)) * G i j := by
                            exact Finset.sum_add_distrib
              _ = (∑ i, ∑ j, (∑ l, ∑ k, w l * u k * Γ i l k) * v j * G i j) +
                    (∑ i, ∑ j, (w i * (∑ l, ∑ k, v l * u k * Γ j l k)) * G i j) := by
                    rw [Finset.sum_add_distrib]

end BonnetMyersEntry
