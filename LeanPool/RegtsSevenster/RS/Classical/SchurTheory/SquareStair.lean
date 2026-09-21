/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.SignResolve

/-!
# The natural dimension identity and square staircases

The dimension identity `nDim S₀ · ∏ eᵢ! = n! · ∏∏ diffs` at the
natural-number level, the staircase evaluation for square
diagrams, and the elementary factorial bounds feeding the square
growth estimate.
-/

namespace RS

open Finset

/-- **The natural dimension identity.** -/
theorem dim_mul_eq (μ : YoungDiagram)
    (S₀ : Submodule (MonoidAlgebra ℂ (Equiv.Perm (Fin μ.card)))
      (MonoidAlgebra ℂ (Equiv.Perm (Fin μ.card))))
    (hchar : ∀ π, jtChar μ π = nChar S₀ π) :
    nDim S₀ * ∏ i : Fin μ.rowLens.length,
      (eStair μ i).factorial =
    μ.card.factorial * ∏ i : Fin μ.rowLens.length,
      ∏ j ∈ Finset.Ioi i,
        (eStair μ (Fin.revPerm j) - eStair μ (Fin.revPerm i)) := by
  classical
  have h1 := jtChar_one_eq μ
  have h2 := diagramSchur_delta_mul μ
  have h3 : jtChar μ 1 = ((nDim S₀ : ℕ) : ℂ) := by
    rw [hchar 1, nChar, Representation.char_one]
    rfl
  have hkey : ((nDim S₀ : ℕ) : ℂ) *
      ∏ i : Fin μ.rowLens.length,
        ((eStair μ i).factorial : ℂ) =
      (μ.card.factorial : ℂ) *
        ∏ i : Fin μ.rowLens.length, ∏ j ∈ Finset.Ioi i,
          (((eStair μ (Fin.revPerm j)) : ℂ) -
            ((eStair μ (Fin.revPerm i)) : ℂ)) := by
    rw [← h3, h1, mul_assoc, h2]
  have hdiff : ∀ (i : Fin μ.rowLens.length)
      (j : Fin μ.rowLens.length), i < j →
      (((eStair μ (Fin.revPerm j)) : ℂ) -
        ((eStair μ (Fin.revPerm i)) : ℂ)) =
      (((eStair μ (Fin.revPerm j) -
        eStair μ (Fin.revPerm i) : ℕ)) : ℂ) := by
    intro i j hij
    have hrev : Fin.revPerm j < Fin.revPerm i := by
      have hi := i.isLt
      have hj' := j.isLt
      have h1' : ((Fin.revPerm j : Fin _) : ℕ) =
          _ - ((j : ℕ) + 1) := Fin.val_rev j
      have h2' : ((Fin.revPerm i : Fin _) : ℕ) =
          _ - ((i : ℕ) + 1) := Fin.val_rev i
      have hij' : (i : ℕ) < (j : ℕ) := hij
      rw [Fin.lt_def, h1', h2']
      omega
    rw [Nat.cast_sub (le_of_lt (eStair_strictAnti μ hrev))]
  rw [Finset.prod_congr rfl (fun i (_ : i ∈ Finset.univ) =>
    Finset.prod_congr rfl (fun j hj =>
      hdiff i j (Finset.mem_Ioi.mp hj)))] at hkey
  have hcast : ((nDim S₀ *
      ∏ i : Fin μ.rowLens.length, (eStair μ i).factorial : ℕ) :
        ℂ) =
      ((μ.card.factorial *
        ∏ i : Fin μ.rowLens.length, ∏ j ∈ Finset.Ioi i,
          (eStair μ (Fin.revPerm j) -
            eStair μ (Fin.revPerm i)) : ℕ) : ℂ) := by
    push_cast
    linear_combination hkey
  exact_mod_cast hcast

/-- The square diagram has `s` rows. -/
theorem square_rowLens_length (s : ℕ) :
    (squareDiagram s).rowLens.length = s := by
  rw [squareDiagram_rowLens, List.length_replicate]

/-- The square staircase evaluates to `2s − 1 − i`. -/
theorem eStair_square (s : ℕ)
    (i : Fin (squareDiagram s).rowLens.length) :
    eStair (squareDiagram s) i = s + ((s - 1) - (i : ℕ)) := by
  have hL := square_rowLens_length s
  have hi : (i : ℕ) < s := by
    have := i.isLt
    omega
  rw [eStair, List.get_eq_getElem, YoungDiagram.get_rowLens,
    rowLen_squareDiagram hi]
  omega

/-- Interval products are factorials. -/
theorem Ioi_prod_sub {L : ℕ} (i : Fin L) :
    (∏ j ∈ Finset.Ioi i, ((j : ℕ) - (i : ℕ))) =
      ((L - 1) - (i : ℕ)).factorial := by
  classical
  have hi := i.isLt
  have himg : (Finset.Ioi i).image (Fin.val) =
      Finset.Ico ((i : ℕ) + 1) L := by
    ext n
    simp only [Finset.mem_image, Finset.mem_Ioi, Finset.mem_Ico]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨hj, j.isLt⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨n, h2⟩, h1, rfl⟩
  have h1 : (∏ j ∈ Finset.Ioi i, ((j : ℕ) - (i : ℕ))) =
      ∏ n ∈ Finset.Ico ((i : ℕ) + 1) L, (n - (i : ℕ)) := by
    rw [← himg]
    rw [Finset.prod_image (fun a _ b _ hab => Fin.val_injective hab)]
  rw [h1, Finset.prod_Ico_eq_prod_range]
  rw [show L - ((i : ℕ) + 1) = (L - 1) - (i : ℕ) from by omega]
  rw [Finset.prod_congr rfl (fun t (_ : t ∈ Finset.range
      ((L - 1) - (i : ℕ))) => show (i : ℕ) + 1 + t - (i : ℕ) =
    t + 1 from by omega)]
  exact Finset.prod_range_add_one_eq_factorial _

/-- Adding `r` to the argument multiplies the factorial by at most
`(d+r)^r`. -/
theorem factorial_add_le (d r : ℕ) :
    (d + r).factorial ≤ (d + r) ^ r * d.factorial := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [show d + (r + 1) = (d + r) + 1 from by omega,
      Nat.factorial_succ]
    calc (d + r + 1) * (d + r).factorial ≤
        (d + r + 1) * ((d + r) ^ r * d.factorial) :=
          Nat.mul_le_mul_left _ ih
      _ ≤ (d + r + 1) * ((d + r + 1) ^ r * d.factorial) := by
          refine Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _
            (Nat.pow_le_pow_left (by omega) r))
      _ = (d + (r + 1)) ^ (r + 1) * d.factorial := by
          rw [show d + (r + 1) = d + r + 1 from by omega, pow_succ]
          ring

/-- The shifted factorial bound: `(s+d)! ≤ (2s)^s · d!` for
`d < s`. -/
theorem shifted_factorial_le (s d : ℕ) (hd : d < s) :
    (s + d).factorial ≤ (2 * s) ^ s * d.factorial := by
  have h1 := factorial_add_le d s
  rw [show s + d = d + s from by omega]
  calc (d + s).factorial ≤ (d + s) ^ s * d.factorial := h1
    _ ≤ (2 * s) ^ s * d.factorial :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) s)

end RS
