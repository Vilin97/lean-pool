/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import LeanPool.ArchonFirstProofResults.FirstProof6.Auxiliary.LaplacianBasics

/-!
# Problem 6: Large epsilon-light vertex subsets -- Loewner Pullback

Normalized edge setup: congruence pullbacks for Loewner order,
square root pullback, and epsilon-lightness from Loewner bound.

## Main theorems

- `Problem6.sqrt_pullback_loewner`: square root pullback
- `Problem6.eps_light_of_loewner_bound`: epsilon-lightness from bound
-/

open Finset Matrix BigOperators

noncomputable section

namespace Problem6

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Normalized edge setup infrastructure

**Normalized edge setup (Step 1)**: For any graph G on V, there
exist PSD matrices `A : V -> Fin r -> Matrix V V R` (one per
(vertex, color) pair), with the property that:
(a) Each `A v g` is PSD
(b) For each vertex v, some color g has `A v g <= (e/n)*I`
(c) If M is a sum of selected `A v g`'s satisfying `M < u*I`
    with `u < e`, then each color class is e-light

The following sub-lemmas establish the mathematical
infrastructure needed. -/

/-- Sub-lemma: If L^{1/2} is a Hermitian matrix with L^{1/2} * L^{1/2} = L (on the relevant
    subspace), and M ≼ u*I, then L^{1/2} * M * L^{1/2} ≼ u * L.
    This is the key pullback that converts barrier domination into Laplacian domination. -/
lemma sqrt_pullback_loewner
    (L : Matrix V V ℝ)
    (Lhalf : Matrix V V ℝ)
    (hLhalf_herm : Lhalf.IsHermitian)
    (hLhalf_sq : Lhalf * Lhalf = L)
    (M : Matrix V V ℝ) (u : ℝ)
    (hM : (u • (1 : Matrix V V ℝ) - M).PosSemidef) :
    (u • L - Lhalf * M * Lhalf).PosSemidef := by
  -- u * L - Lhalf * M * Lhalf = u * (Lhalf * Lhalf) - Lhalf * M * Lhalf
  --   = Lhalf * (u * I - M) * Lhalf (since Lhalf^T = Lhalf for Hermitian)
  have h_eq : u • L - Lhalf * M * Lhalf =
      Lhalfᴴ * (u • (1 : Matrix V V ℝ) - M) * Lhalf := by
    rw [hLhalf_herm.eq]
    simp only [Matrix.mul_sub, Matrix.sub_mul, smul_mul_assoc, Matrix.mul_one,
               mul_smul_comm, Matrix.mul_assoc, ← hLhalf_sq]
  rw [h_eq]
  exact hM.conjTranspose_mul_mul_same Lhalf

/-- Sub-lemma: ε-lightness from Loewner bound on normalized Laplacian.
    If for some PSD Hermitian Lhalf with Lhalf^2 = L (the graph Laplacian),
    we have ∑_{e in E(S,S)} A_e ≼ ε * I where A_e = Lhalf_inv * L_e * Lhalf_inv,
    then S is ε-light.
    More precisely: if (ε * L - inducedLaplacian G S) is PSD when the inducedLaplacian
    is dominated by ε * graphLaplacian, then S is ε-light. The key step is showing
    that the Loewner bound on normalized edge contributions implies the Loewner bound
    on the original Laplacians.
    For this sub-lemma, we take the simple route: if we can show that
    ε * graphLaplacian G - inducedLaplacian G S is PSD, then S is ε-light by definition. -/
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
  -- Need: (ε • graphLaplacian G - inducedLaplacian G S).PosSemidef
  -- From sqrt_pullback_loewner: u • L - Lhalf * M * Lhalf is PSD
  -- i.e., u • L - L_S is PSD
  -- Since u ≤ ε: ε • L - L_S = (u • L - L_S) + (ε - u) • L is PSD (sum of PSD)
  have h_uL : (u • graphLaplacian G - inducedLaplacian G S).PosSemidef := by
    rw [← hM_conn]
    exact sqrt_pullback_loewner (graphLaplacian G) Lhalf hLhalf_herm hLhalf_sq M u hM_bound
  have h_split : ε • graphLaplacian G - inducedLaplacian G S =
      (u • graphLaplacian G - inducedLaplacian G S) +
      (ε - u) • graphLaplacian G := by
    rw [sub_smul]; abel
  rw [h_split]
  exact h_uL.add ((graphLaplacian_posSemidef G).smul (by linarith))

end Problem6

end
