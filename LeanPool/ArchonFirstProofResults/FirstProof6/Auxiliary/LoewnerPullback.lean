/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import LeanPool.ArchonFirstProofResults.FirstProof6.Auxiliary.LaplacianBasics

/-!
# Problem 6: Large epsilon-light vertex subsets -- Loewner Pullback

Congruence pullbacks for Loewner order and epsilon-lightness from Loewner bound.
-/

open Finset Matrix BigOperators

noncomputable section

namespace Problem6

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma sqrt_pullback_loewner
    (L : Matrix V V ℝ)
    (Lhalf : Matrix V V ℝ)
    (hLhalf_herm : Lhalf.IsHermitian)
    (hLhalf_sq : Lhalf * Lhalf = L)
    (M : Matrix V V ℝ) (u : ℝ)
    (hM : (u • (1 : Matrix V V ℝ) - M).PosSemidef) :
    (u • L - Lhalf * M * Lhalf).PosSemidef := by
  have h_eq : u • L - Lhalf * M * Lhalf =
      Lhalfᴴ * (u • (1 : Matrix V V ℝ) - M) * Lhalf := by
    rw [hLhalf_herm.eq]
    simp only [Matrix.mul_sub, Matrix.sub_mul, smul_mul_assoc, Matrix.mul_one,
               mul_smul_comm, Matrix.mul_assoc, ← hLhalf_sq]
  rw [h_eq]
  exact hM.conjTranspose_mul_mul_same Lhalf

lemma eps_light_of_loewner_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε u : ℝ) (_hε : 0 < ε) (hu : u ≤ ε)
    (S : Finset V)
    (Lhalf : Matrix V V ℝ)
    (hLhalf_herm : Lhalf.IsHermitian)
    (hLhalf_sq : Lhalf * Lhalf = graphLaplacian G)
    (M : Matrix V V ℝ)
    (hM_bound : (u • (1 : Matrix V V ℝ) - M).PosSemidef)
    (hM_conn : Lhalf * M * Lhalf = inducedLaplacian G S) :
    IsEpsLight G ε S := by
  unfold IsEpsLight
  have h_uL : (u • graphLaplacian G - inducedLaplacian G S).PosSemidef := by
    rw [← hM_conn]
    exact sqrt_pullback_loewner (graphLaplacian G) Lhalf hLhalf_herm hLhalf_sq M u hM_bound
  have h_split : ε • graphLaplacian G - inducedLaplacian G S =
      (u • graphLaplacian G - inducedLaplacian G S) + (ε - u) • graphLaplacian G := by
    rw [sub_smul]; abel
  rw [h_split]
  exact h_uL.add ((graphLaplacian_posSemidef G).smul (by linarith))

end Problem6

end
