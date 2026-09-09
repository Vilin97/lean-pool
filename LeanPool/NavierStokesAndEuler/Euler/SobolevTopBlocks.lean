/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevWordBlocks
import LeanPool.NavierStokesAndEuler.Euler.SobolevWordBlockCoordinates
import Mathlib.Algebra.Order.Star.Real

/-! Actual higher Sobolev norms controlled by lower norms and finitely many top derivative blocks.
-/

@[expose] public section


noncomputable section

namespace EulerSobolevTopBlocks

open EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevWordBlocks

variable (period : ℝ) [Fact (0 < period)]

/-- A full top derivative is literally a second derivative of one of the genuine top word blocks. -/
theorem top_word_block (q : ℕ) (u : SobolevSpace period (2 + q)) (w : Fin (2 + q) → Fin 4) :
    word period u (le_refl (2+q)) w =
      word period (wordBlock period 2 q (fun i => w (Fin.natAdd 2 i)) u) (le_refl 2)
        (fun i => w (Fin.castAdd q i)) := by
  rw [wordBlock_word, Fin.append_castAdd_natAdd]

/-- The genuine complete H^(q+2) norm is controlled by H^(q+1) and all order-q H² derivative blocks.
-/
theorem top_blocks_norm_sq (q : ℕ) (u : SobolevSpace period (2 + q)) :
    ‖u‖^2 ≤ ‖restrictOperator period (by omega : 1+q ≤ 2+q) u‖^2 +
      ∑ w : Fin q → Fin 4, ‖wordBlock period 2 q w u‖^2 := by
  have hsum : 0 ≤ ∑ w : Fin q → Fin 4, ‖wordBlock period 2 q w u‖^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hB : 0 ≤ ‖restrictOperator period (by omega : 1+q ≤ 2+q) u‖^2 +
      ∑ w : Fin q → Fin 4, ‖wordBlock period 2 q w u‖^2 := add_nonneg (sq_nonneg _) hsum
  apply (Real.le_sqrt (norm_nonneg u) hB).mp
  change ‖u.val‖ ≤ _
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
  rintro ⟨⟨n, hn⟩, w⟩
  apply Real.le_sqrt_of_sq_le
  by_cases hlow : n ≤ 1+q
  · have hnorm : ‖u.val ⟨⟨n, hn⟩, w⟩‖ ≤ ‖restrictOperator period (by omega : 1+q ≤ 2+q) u‖ :=
      word_norm_le period (restrictOperator period (by omega : 1+q ≤ 2+q) u)
        ⟨⟨n, Nat.lt_succ_of_le hlow⟩, w⟩
    nlinarith [norm_nonneg (u.val ⟨⟨n, hn⟩, w⟩), norm_nonneg (restrictOperator period (by
        omega : 1+q ≤ 2+q) u)]
  · have hn2 : n = 2+q := by omega
    subst n
    have hw := top_word_block period q u w
    change ‖word period u (le_refl (2+q)) w‖^2 ≤ _
    rw [hw]
    have hnorm := word_norm_le period (wordBlock period 2 q (fun i => w (Fin.natAdd 2 i)) u)
      (⟨⟨2, by omega⟩, fun i => w (Fin.castAdd q i)⟩ : SobolevWord 2)
    change ‖word period (wordBlock period 2 q (fun i => w (Fin.natAdd 2 i)) u)
      (le_refl 2) (fun i => w (Fin.castAdd q i))‖ ≤ _ at hnorm
    have hs := Finset.single_le_sum (fun v _ => sq_nonneg ‖wordBlock period 2 q v u‖)
      (Finset.mem_univ (fun i => w (Fin.natAdd 2 i)))
    nlinarith [norm_nonneg (word period (wordBlock period 2 q (fun i => w (Fin.natAdd 2 i)) u)
      (le_refl 2) (fun i => w (Fin.castAdd q i))),
      norm_nonneg (wordBlock period 2 q (fun i => w (Fin.natAdd 2 i)) u),
      sq_nonneg ‖restrictOperator period (by omega : 1+q ≤ 2+q) u‖]

end EulerSobolevTopBlocks
