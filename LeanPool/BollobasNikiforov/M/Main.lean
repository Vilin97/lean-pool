/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import LeanPool.BollobasNikiforov.M.HalfPlane

/-!
# The planar Gram theorem for `M`

If planar vectors lie in a closed half-plane, `M` of their Gram matrix is
completely positive (`thm:matrix`).
-/

@[expose] public section

open Matrix

namespace BollobasNikiforov

noncomputable section

/-- **HP08.** `thm:matrix`: a closed half-plane of planar Gram vectors
makes `M` completely positive. -/
theorem matrix_theorem {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]
    (z : n → Fin 2 → ℝ) {w : Fin 2 → ℝ} (hw : w ≠ 0)
    (hwz : ∀ i, 0 ≤ w ⬝ᵥ z i) :
    IsCompletelyPositive (M (gram z)) := by
  rw [isCompletelyPositive_M_gram_iff_nonzero]
  set z' : {i // z i ≠ 0} → Fin 2 → ℝ := fun i => z i.1
  have hnz : ∀ i, z' i ≠ 0 := fun i => i.2
  have hwz' : ∀ i, 0 ≤ w ⬝ᵥ z' i := fun i => hwz i.1
  by_cases hnn : ∀ i j, 0 ≤ z' i ⬝ᵥ z' j
  · exact isCompletelyPositive_M_of_nonneg_inners z' hnn
  · push Not at hnn
    by_cases hopen : ∀ i, 0 < w ⬝ᵥ z' i
    · have : Nonempty {i // z i ≠ 0} := ⟨hnn.choose⟩
      obtain ⟨i0, hside⟩ := exists_supporting_minimizer z' hnz hw hopen
      by_cases huniq : ∀ i, det2 (normalize (z' i0)) (z' i) = 0 → i = i0
      · exact isCompletelyPositive_M_of_unique_minimizer z' hnz
          ⟨w, hw, hopen⟩ hnn i0 hside huniq
      · exact isCompletelyPositive_M_of_tied_minimizers z' hnz
          ⟨w, hw, hopen⟩ hnn i0 hside huniq
    · exact isCompletelyPositive_M_of_closed_halfplane z' hw hwz'

end

end BollobasNikiforov
