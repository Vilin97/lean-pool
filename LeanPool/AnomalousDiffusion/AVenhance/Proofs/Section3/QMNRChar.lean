/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.QMNRRecursion

/-! Proof of the §3 characterization of the `qMNR` family. -/

@[expose] public section

noncomputable section

namespace AVenhance.Proofs.Ingredients

open MeasureTheory
open AVenhance

theorem qMNR_char {β : ℝ} (I : AVenhance.Ingredients β)
    (κ : ℝ) (_hκ : 0 < κ) (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    (∀ t, I.qMNR κ m n 0 t = I.jMN κ m n t - timeAvgMat (I.jMN κ m n)) ∧
    (∀ r, Function.Periodic (I.qMNR κ m n r) (4 * tau β I.Λ m)) ∧
    (∀ r, 1 ≤ r → timeAvgMat (I.qMNR κ m n r) = 0) ∧
    (∀ (r : ℕ) (t : ℝ) (i j : Fin 2),
      HasDerivAt (fun s => I.qMNR κ m n (r + 1) s i j)
        (-(I.qMNR κ m n r t i j)) t) ∧
    ∀ q' : ℕ → ℝ → Matrix (Fin 2) (Fin 2) ℝ,
      (∀ t, q' 0 t = I.jMN κ m n t - timeAvgMat (I.jMN κ m n)) →
      (∀ r, Function.Periodic (q' r) (4 * tau β I.Λ m)) →
      (∀ r, 1 ≤ r → timeAvgMat (q' r) = 0) →
      (∀ (r : ℕ) (t : ℝ) (i j : Fin 2),
        HasDerivAt (fun s => q' (r + 1) s i j) (-(q' r t i j)) t) →
      ∀ r, q' r = I.qMNR κ m n r := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t
    rfl
  · intro r
    exact AVenhance.Infra.Section3.qMNR_periodic I κ hm r
  · intro r hr
    obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
    exact AVenhance.Infra.Section3.qMNR_timeAvg_zero I κ m n s
  · intro r t i j
    exact AVenhance.Infra.Section3.qMNR_hasDerivAt I κ m n r t i j
  · intro q' hbase hperiod hmean hderiv
    exact AVenhance.Infra.Section3.qMNR_unique I κ hm q' hbase hperiod hmean hderiv

end AVenhance.Proofs.Ingredients

end
