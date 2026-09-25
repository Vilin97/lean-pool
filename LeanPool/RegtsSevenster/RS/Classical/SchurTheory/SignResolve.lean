/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.SymFun.DimFormula
public import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.JTSimple

/-!
# The sign resolution

The Jacobi–Trudi character degree is a ratio of positive naturals,
so in the `±`-dichotomy of `jtChar_pm_simple` only the positive
sign survives: the Jacobi–Trudi character IS a native character.
-/

@[expose] public section

namespace RS

open Finset

/-- The staircase exponents strictly decrease. -/
theorem eStair_strictAnti (μ : YoungDiagram)
    {i j : Fin μ.rowLens.length} (hij : i < j) :
    eStair μ j < eStair μ i := by
  have hmono : μ.rowLens.get j ≤ μ.rowLens.get i :=
    (List.sortedGE_iff_antitone_get.mp μ.rowLens_sorted)
      (le_of_lt hij)
  have hi := i.isLt
  have hj := j.isLt
  have hij' : (i : ℕ) < (j : ℕ) := hij
  rw [eStair, eStair]
  omega

/-- **Positivity of the degree**: a positive natural multiple of
`jtChar μ 1` is a positive natural. -/
theorem jtChar_one_pos_identity (μ : YoungDiagram) :
    ∃ N D : ℕ, 0 < N ∧ 0 < D ∧
      (D : ℂ) * jtChar μ 1 = (N : ℂ) := by
  classical
  refine ⟨μ.card.factorial *
      ∏ i : Fin μ.rowLens.length, ∏ j ∈ Finset.Ioi i,
        (eStair μ (Fin.revPerm j) - eStair μ (Fin.revPerm i)),
    ∏ i : Fin μ.rowLens.length, (eStair μ i).factorial,
    ?_, ?_, ?_⟩
  · refine Nat.mul_pos (Nat.factorial_pos _)
      (Finset.prod_pos fun i _ => Finset.prod_pos fun j hj => ?_)
    have hij : i < j := Finset.mem_Ioi.mp hj
    have hrev : Fin.revPerm j < Fin.revPerm i := by
      have hi := i.isLt
      have hj' := j.isLt
      have h1 : ((Fin.revPerm j : Fin _) : ℕ) =
          _ - ((j : ℕ) + 1) := Fin.val_rev j
      have h2 : ((Fin.revPerm i : Fin _) : ℕ) =
          _ - ((i : ℕ) + 1) := Fin.val_rev i
      have hij' : (i : ℕ) < (j : ℕ) := hij
      rw [Fin.lt_def, h1, h2]
      omega
    exact Nat.sub_pos_of_lt (eStair_strictAnti μ hrev)
  · exact Finset.prod_pos fun i _ => Nat.factorial_pos _
  · rw [jtChar_one_eq]
    have h2 := diagramSchur_delta_mul μ
    push_cast
    rw [show ((∏ i : Fin μ.rowLens.length,
        ((eStair μ i).factorial : ℂ))) *
        ((μ.card.factorial : ℂ) * diagramSchur μ deltaSeq) =
      (μ.card.factorial : ℂ) *
        (diagramSchur μ deltaSeq *
          ∏ i : Fin μ.rowLens.length,
            ((eStair μ i).factorial : ℂ)) from by ring]
    rw [h2]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    refine Finset.prod_congr rfl fun j hj => ?_
    have hij : i < j := Finset.mem_Ioi.mp hj
    have hrev : Fin.revPerm j < Fin.revPerm i := by
      have hi := i.isLt
      have hj' := j.isLt
      have h1 : ((Fin.revPerm j : Fin _) : ℕ) =
          _ - ((j : ℕ) + 1) := Fin.val_rev j
      have h2 : ((Fin.revPerm i : Fin _) : ℕ) =
          _ - ((i : ℕ) + 1) := Fin.val_rev i
      have hij' : (i : ℕ) < (j : ℕ) := hij
      rw [Fin.lt_def, h1, h2]
      omega
    rw [Nat.cast_sub (le_of_lt (eStair_strictAnti μ hrev))]

open scoped Classical in
/-- **The Jacobi–Trudi character is a native character.** -/
theorem jtChar_eq_nChar (μ : YoungDiagram) :
    ∃ S₀ : Submodule (MonoidAlgebra ℂ (Equiv.Perm (Fin μ.card)))
      (MonoidAlgebra ℂ (Equiv.Perm (Fin μ.card))),
      IsSimpleModule (MonoidAlgebra ℂ (Equiv.Perm (Fin μ.card)))
        S₀ ∧
      ∀ π, jtChar μ π = nChar S₀ π := by
  obtain ⟨S₀, hS₀, hpm⟩ := jtChar_pm_simple μ
  refine ⟨S₀, hS₀, ?_⟩
  rcases hpm with hpos | hneg
  · exact hpos
  · exfalso
    obtain ⟨N, D, hN, hD, hid⟩ := jtChar_one_pos_identity μ
    rw [hneg 1] at hid
    rw [show nChar S₀ 1 =
        ((Module.finrank ℂ (subCarrier S₀) : ℕ) : ℂ) from by
      rw [nChar, Representation.char_one]] at hid
    have hcast : ((D * Module.finrank ℂ (subCarrier S₀) + N :
        ℕ) : ℂ) = 0 := by
      push_cast
      linear_combination -hid
    have h0 : D * Module.finrank ℂ (subCarrier S₀) + N = 0 := by
      exact_mod_cast hcast
    omega

end RS
