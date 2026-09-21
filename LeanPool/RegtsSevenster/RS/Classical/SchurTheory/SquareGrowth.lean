/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.SquareStair

/-!
# The square dimension growth

Evaluating the natural dimension identity at square diagrams: the
Vandermonde side is the superfactorial, the factorial side is at
most `(2s)^(s²)` times it, so the dimension dominates
`(s²)^(s²) / (6s)^(s²) = (s/6)^(s²)` — beating any `R^(s²)` for
`s = 6(R+1)`.  The factorial lower bound `n^n ≤ 3^n·n!` enters as
the hypothesis `H3`, discharged in `FactorialBound.lean`.
-/

namespace RS

open Finset

/-- The square Vandermonde side is the superfactorial. -/
theorem square_V_eq (s : ℕ) :
    (∏ i : Fin (squareDiagram s).rowLens.length,
      ∏ j ∈ Finset.Ioi i,
        (eStair (squareDiagram s) (Fin.revPerm j) -
          eStair (squareDiagram s) (Fin.revPerm i))) =
    ∏ i : Fin (squareDiagram s).rowLens.length,
      (((squareDiagram s).rowLens.length - 1) - (i : ℕ)).factorial
    := by
  classical
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Ioi_prod_sub i]
  refine Finset.prod_congr rfl fun j hj => ?_
  have hL := square_rowLens_length s
  have hi := i.isLt
  have hj' := j.isLt
  have hij : i < j := Finset.mem_Ioi.mp hj
  have hij' : (i : ℕ) < (j : ℕ) := hij
  have hrj : ((Fin.revPerm j : Fin _) : ℕ) =
      _ - ((j : ℕ) + 1) := Fin.val_rev j
  have hri : ((Fin.revPerm i : Fin _) : ℕ) =
      _ - ((i : ℕ) + 1) := Fin.val_rev i
  rw [eStair_square s (Fin.revPerm j),
    eStair_square s (Fin.revPerm i), hrj, hri]
  omega

/-- The square factorial side is bounded by `(2s)^(s²)` times the
superfactorial. -/
theorem square_D_le (s : ℕ) (_hs : 1 ≤ s) :
    (∏ i : Fin (squareDiagram s).rowLens.length,
      (eStair (squareDiagram s) i).factorial) ≤
    (2 * s) ^ (s ^ 2) *
      ∏ i : Fin (squareDiagram s).rowLens.length,
        (((squareDiagram s).rowLens.length - 1) -
          (i : ℕ)).factorial := by
  classical
  have hL := square_rowLens_length s
  calc (∏ i : Fin (squareDiagram s).rowLens.length,
      (eStair (squareDiagram s) i).factorial) ≤
      ∏ i : Fin (squareDiagram s).rowLens.length,
        ((2 * s) ^ s *
          (((squareDiagram s).rowLens.length - 1) -
            (i : ℕ)).factorial) := by
        refine Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
          (fun i _ => ?_)
        rw [eStair_square s i]
        have hi := i.isLt
        rw [show ((squareDiagram s).rowLens.length - 1) -
            (i : ℕ) = (s - 1) - (i : ℕ) from by omega]
        exact shifted_factorial_le s ((s - 1) - (i : ℕ))
          (by omega)
    _ = ((2 * s) ^ s) ^ (squareDiagram s).rowLens.length *
        ∏ i : Fin (squareDiagram s).rowLens.length,
          (((squareDiagram s).rowLens.length - 1) -
            (i : ℕ)).factorial := by
        rw [Finset.prod_mul_distrib, Finset.prod_const,
          Finset.card_univ, Fintype.card_fin]
    _ = (2 * s) ^ (s ^ 2) *
        ∏ i : Fin (squareDiagram s).rowLens.length,
          (((squareDiagram s).rowLens.length - 1) -
            (i : ℕ)).factorial := by
        rw [← pow_mul, hL, sq]

open scoped Classical in
/-- **The square dimension growth**, modulo the factorial lower
bound. -/
theorem square_growth
    (H3 : ∀ n : ℕ, n ^ n ≤ 3 ^ n * n.factorial) (R : ℕ) :
    ∃ s : ℕ, ∀ S₀ : Submodule
      (MonoidAlgebra ℂ (Equiv.Perm (Fin (squareDiagram s).card)))
      (MonoidAlgebra ℂ (Equiv.Perm (Fin (squareDiagram s).card))),
      (∀ π, jtChar (squareDiagram s) π = nChar S₀ π) →
      R ^ (s ^ 2) < nDim S₀ := by
  refine ⟨6 * (R + 1), fun S₀ hchar => ?_⟩
  generalize hgen : 6 * (R + 1) = s at S₀ hchar ⊢
  have hs1 : 1 ≤ s := by omega
  have hid := dim_mul_eq (squareDiagram s) S₀ hchar
  rw [square_V_eq] at hid
  have hn : (squareDiagram s).card = s ^ 2 := squareDiagram_card s
  set V := ∏ i : Fin (squareDiagram s).rowLens.length,
    (((squareDiagram s).rowLens.length - 1) - (i : ℕ)).factorial
    with hV
  have hVpos : 0 < V :=
    Finset.prod_pos fun i _ => Nat.factorial_pos _
  have hD := square_D_le s hs1
  -- dim * (2s)^(s²) * V ≥ dim * D = (s²)! * V
  have h1 : (squareDiagram s).card.factorial * V ≤
      nDim S₀ * ((2 * s) ^ (s ^ 2) * V) := by
    rw [← hid]
    exact Nat.mul_le_mul_left _ hD
  have h2 : (s ^ 2).factorial ≤ nDim S₀ * (2 * s) ^ (s ^ 2) := by
    have h3 : (squareDiagram s).card.factorial * V ≤
        (nDim S₀ * (2 * s) ^ (s ^ 2)) * V := by
      calc (squareDiagram s).card.factorial * V ≤
          nDim S₀ * ((2 * s) ^ (s ^ 2) * V) := h1
        _ = (nDim S₀ * (2 * s) ^ (s ^ 2)) * V := by ring
    have h2' := Nat.le_of_mul_le_mul_right h3 hVpos
    exact hn ▸ h2'
  -- (s²)^(s²) ≤ 3^(s²) (s²)! ≤ dim * (6s)^(s²)
  have h4 : (s ^ 2) ^ (s ^ 2) ≤ nDim S₀ * (6 * s) ^ (s ^ 2) := by
    calc (s ^ 2) ^ (s ^ 2) ≤ 3 ^ (s ^ 2) * (s ^ 2).factorial :=
        H3 (s ^ 2)
      _ ≤ 3 ^ (s ^ 2) * (nDim S₀ * (2 * s) ^ (s ^ 2)) :=
        Nat.mul_le_mul_left _ h2
      _ = nDim S₀ * (3 ^ (s ^ 2) * (2 * s) ^ (s ^ 2)) := by ring
      _ = nDim S₀ * (6 * s) ^ (s ^ 2) := by
        rw [← Nat.mul_pow]
        congr 2
        ring
  -- (s²)^(s²) > R^(s²) * (6s)^(s²)
  have h5 : R ^ (s ^ 2) * (6 * s) ^ (s ^ 2) <
      (s ^ 2) ^ (s ^ 2) := by
    have h6s : (0 : ℕ) < 6 * s := by omega
    have hlt : R * (6 * s) < (R + 1) * (6 * s) :=
      mul_lt_mul_of_pos_right (by omega) h6s
    have heq : (R + 1) * (6 * s) = s ^ 2 := by
      rw [← hgen]
      ring
    have hbase : R * (6 * s) < s ^ 2 := heq ▸ hlt
    rw [← Nat.mul_pow]
    exact Nat.pow_lt_pow_left hbase
      (pow_ne_zero 2 (show s ≠ 0 from by omega))
  have h6 : R ^ (s ^ 2) * (6 * s) ^ (s ^ 2) <
      nDim S₀ * (6 * s) ^ (s ^ 2) := lt_of_lt_of_le h5 h4
  exact Nat.lt_of_mul_lt_mul_right h6

end RS
