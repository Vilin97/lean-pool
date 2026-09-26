/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.FinalConstruction

/-!
# Existence
-/

@[expose] public section

namespace EGZ

/-- Theorem 4.13, the Flag Decomposition Lemma, with all uniformity made
explicit.

The assertion `0 < δ` is the formal content of the paper's notation
`δ ≫_{d,ε} 1`; it does not mean that `δ` is numerically greater than one.
The harmless requirements `2 ≤ p₀` and `1 ≤ BK` expose bounds used by the
centered-lift and reciprocal-power formulations. -/
theorem flag_decomposition_lemma :
    ∀ (d : ℕ) (ε : ℝ), 0 < ε →
      ∃ (δ : ℝ) (Bcard : ℕ), 0 < δ ∧
        ∀ g : ℕ → ℕ, IsGrowing g →
          ∃ (p₀ BK : ℕ), 2 ≤ p₀ ∧ 1 ≤ BK ∧
            ∀ (p : ℕ) (hp : p.Prime), p₀ < p →
              ∀ f : FpCoord p d → ℕ, f ≠ 0 →
                HasFlagDecompositionConclusion hp f ε δ g Bcard BK := by
  intro d ε hε
  cases d with
  | zero => exact flag_decomposition_lemma_dimZero ε hε
  | succ d =>
    let ε' := min ε (1 / 2 : ℝ)
    have hε' : 0 < ε' := lt_min hε (by norm_num)
    obtain ⟨δ, Bcard, hδ, hconstruction⟩ :=
      flag_decomposition_lemma_posdim (d := d + 1) (by omega) ε' hε' (min_le_right _ _)
    refine ⟨δ, Bcard, hδ, ?_⟩
    intro g hg
    obtain ⟨p₀, BK, hp₀, hBK, hresult⟩ := hconstruction g hg
    refine ⟨p₀, BK, hp₀, hBK, ?_⟩
    intro p hp hpp f hf
    exact (hresult p hp hpp f hf).mono_epsilon (min_le_left _ _)

/-- Numbered alias for the Flag Decomposition Lemma. -/
theorem theorem_4_13 :
    ∀ (d : ℕ) (ε : ℝ), 0 < ε →
      ∃ (δ : ℝ) (Bcard : ℕ), 0 < δ ∧
        ∀ g : ℕ → ℕ, IsGrowing g →
          ∃ (p₀ BK : ℕ), 2 ≤ p₀ ∧ 1 ≤ BK ∧
            ∀ (p : ℕ) (hp : p.Prime), p₀ < p →
              ∀ f : FpCoord p d → ℕ, f ≠ 0 →
                HasFlagDecompositionConclusion hp f ε δ g Bcard BK :=
  flag_decomposition_lemma

end EGZ
