/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.FixWeight
import LeanPool.RegtsSevenster.RS.Common.YoungDiagrams

/-!
# The Jacobi–Trudi virtual character

For a Young diagram `μ` with `n = μ.card` cells and `k` rows, the
virtual character `jtChar μ` is the signed sum, over `σ ∈ S_k`, of
the colour characters of the shifted compositions
`i ↦ μᵢ + σ(i) − i` (terms with a negative part vanish).  Its
Frobenius transform is the Jacobi–Trudi determinant
`diagramSchur μ`: each Leibniz term is evaluated by the colour
cycle sum.  The two cycle-type transport facts enter as explicit
hypotheses, discharged in `ColourCycleSum.lean`.
-/

namespace RS

open Finset Equiv

/-- List sums over `Fin` indexing. -/
private theorem list_sum_eq_fin_sum (l : List ℕ) :
    l.sum = ∑ i : Fin l.length, l.get i := by
  conv_lhs => rw [← List.ofFn_get l]
  rw [List.sum_ofFn]

/-- The signed Jacobi–Trudi degree of row `i` under `σ`. -/
def jtSigned (μ : YoungDiagram)
    (σ : Equiv.Perm (Fin μ.rowLens.length))
    (i : Fin μ.rowLens.length) : ℤ :=
  (μ.rowLens.get i : ℤ) + ((σ i : ℕ) : ℤ) - ((i : ℕ) : ℤ)

/-- The shifted composition sums to the diagram's size, the shifts
cancelling. -/
theorem sum_jtSigned (μ : YoungDiagram)
    (σ : Equiv.Perm (Fin μ.rowLens.length)) :
    ∑ i, jtSigned μ σ i = (μ.card : ℤ) := by
  unfold jtSigned
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [show (∑ i : Fin μ.rowLens.length, ((σ i : ℕ) : ℤ)) =
      ∑ i : Fin μ.rowLens.length, ((i : ℕ) : ℤ) from
    Equiv.sum_comp σ (fun i : Fin μ.rowLens.length =>
      ((i : ℕ) : ℤ))]
  rw [add_sub_cancel_right]
  rw [card_eq_sum_rowLens, list_sum_eq_fin_sum, Nat.cast_sum]

/-- The shifted composition attached to a Leibniz term, when
nonnegative. -/
def jtComp (μ : YoungDiagram)
    (σ : Equiv.Perm (Fin μ.rowLens.length))
    (i : Fin μ.rowLens.length) : ℕ :=
  (jtSigned μ σ i).toNat

/-- Hence when no part is negative the composition itself does. -/
theorem sum_jtComp (μ : YoungDiagram)
    (σ : Equiv.Perm (Fin μ.rowLens.length))
    (hp : ∀ i, 0 ≤ jtSigned μ σ i) :
    ∑ i, jtComp μ σ i = μ.card := by
  have h1 : ((∑ i, jtComp μ σ i : ℕ) : ℤ) = (μ.card : ℤ) := by
    rw [Nat.cast_sum]
    rw [Finset.sum_congr rfl
      (fun (i : Fin μ.rowLens.length) (_ : i ∈ Finset.univ) =>
        show ((jtComp μ σ i : ℕ) : ℤ) = jtSigned μ σ i from by
          rw [jtComp, Int.toNat_of_nonneg (hp i)])]
    exact sum_jtSigned μ σ
  exact_mod_cast h1

open scoped Classical in
/-- **The Jacobi–Trudi virtual character** of shape `μ`. -/
noncomputable def jtChar (μ : YoungDiagram)
    (π : Equiv.Perm (Fin μ.card)) : ℂ :=
  ∑ σ : Equiv.Perm (Fin μ.rowLens.length),
    ((Equiv.Perm.sign σ : ℤ) : ℂ) *
      (if ∀ i, 0 ≤ jtSigned μ σ i
        then (colourChar (jtComp μ σ) π : ℂ)
        else 0)

open scoped Classical in
/-- **The Frobenius formula for the Jacobi–Trudi character**: its
normalized cycle-weighted sum is the Jacobi–Trudi determinant. -/
theorem jtChar_frobenius (H1 : PermCongrCT) (H2 : SigmaCT)
    (μ : YoungDiagram) (t : ℕ → ℂ) :
    ((μ.card.factorial : ℂ))⁻¹ *
        ∑ π : Equiv.Perm (Fin μ.card),
          jtChar μ π * cycleProd t π =
      diagramSchur μ t := by
  classical
  have hswap : (∑ π : Equiv.Perm (Fin μ.card),
      jtChar μ π * cycleProd t π) =
      ∑ σ : Equiv.Perm (Fin μ.rowLens.length),
        ((Equiv.Perm.sign σ : ℤ) : ℂ) *
          (if ∀ i, 0 ≤ jtSigned μ σ i
            then ∑ π : Equiv.Perm (Fin μ.card),
              (colourChar (jtComp μ σ) π : ℂ) * cycleProd t π
            else 0) := by
    rw [Finset.sum_congr rfl (fun π (_ : π ∈ Finset.univ) => by
      rw [jtChar, Finset.sum_mul])]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    by_cases hp : ∀ i, 0 ≤ jtSigned μ σ i
    · rw [ite_eq_left hp, Finset.mul_sum]
      refine Finset.sum_congr rfl fun π _ => ?_
      rw [ite_eq_left hp, mul_assoc]
    · rw [ite_eq_right hp]
      rw [Finset.sum_eq_zero fun π _ => by
        rw [ite_eq_right hp, mul_zero, zero_mul]]
      rw [mul_zero]
  have hterm : ∀ σ : Equiv.Perm (Fin μ.rowLens.length),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        (if ∀ i, 0 ≤ jtSigned μ σ i
          then ∑ π : Equiv.Perm (Fin μ.card),
            (colourChar (jtComp μ σ) π : ℂ) * cycleProd t π
          else 0) =
      (μ.card.factorial : ℂ) *
        (((Equiv.Perm.sign σ : ℤ) : ℂ) *
          ∏ i, newtonHZ t (jtSigned μ σ i)) := by
    intro σ
    by_cases hp : ∀ i, 0 ≤ jtSigned μ σ i
    · rw [ite_eq_left hp]
      rw [colour_cycleSum H1 H2 t (jtComp μ σ) (sum_jtComp μ σ hp)]
      rw [show (∏ i, newtonHZ t (jtSigned μ σ i)) =
          ∏ i, newtonH t (jtComp μ σ i) from
        Finset.prod_congr rfl fun i _ => by
          rw [jtComp]
          conv_lhs => rw [← Int.toNat_of_nonneg (hp i)]
          rw [newtonHZ_natCast]]
      ring
    · rw [ite_eq_right hp]
      rw [not_forall] at hp
      obtain ⟨i0, hi0⟩ := hp
      rw [Finset.prod_eq_zero (Finset.mem_univ i0)
        (newtonHZ_neg t _ (not_le.mp hi0))]
      ring
  rw [hswap, Finset.sum_congr rfl (fun σ _ => hterm σ),
    ← Finset.mul_sum, ← mul_assoc,
    inv_mul_cancel₀
      (by exact_mod_cast Nat.factorial_ne_zero μ.card), one_mul]
  rw [diagramSchur, schurDet, ← Matrix.det_transpose,
    Matrix.det_apply']
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1

end RS
