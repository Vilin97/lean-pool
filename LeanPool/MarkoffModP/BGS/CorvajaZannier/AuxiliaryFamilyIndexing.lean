/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.DedekindLocalWronskian
import LeanPool.MarkoffModP.BGS.CorvajaZannier.FrobeniusWronskian
import LeanPool.MarkoffModP.BGS.CorvajaZannier.AuxiliaryFamily
import Mathlib.Tactic

namespace BGS.CorvajaZannier

noncomputable section

open scoped BigOperators

/-- The source auxiliary family has exactly `h*k+h+k` members. -/
theorem auxiliaryFamily_index_card (h k : ℕ) :
    Fintype.card (Sum (Fin k) (Fin (k + 1) × Fin h)) =
      h * k + h + k := by
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_prod]
  ring

/-- A fixed enumeration of the auxiliary family by consecutive derivative
orders. -/
def auxiliaryFamilyIndexEquiv (h k : ℕ) :
    Sum (Fin k) (Fin (k + 1) × Fin h) ≃ Fin (h * k + h + k) :=
  Fintype.equivFinOfCardEq (auxiliaryFamily_index_card h k)

/-- The derivative order assigned to an auxiliary-family row. -/
def auxiliaryFamilyDerivativeOrder (h k : ℕ) :
    Sum (Fin k) (Fin (k + 1) × Fin h) → ℕ :=
  fun i => (auxiliaryFamilyIndexEquiv h k i : ℕ)

theorem auxiliaryFamilyDerivativeOrder_injective (h k : ℕ) :
    Function.Injective (auxiliaryFamilyDerivativeOrder h k) := by
  intro i j hij
  apply (auxiliaryFamilyIndexEquiv h k).injective
  exact Fin.ext hij

theorem auxiliaryFamilyDerivativeOrder_le_pred
    (h k : ℕ) (hn : 0 < h * k + h + k)
    (i : Sum (Fin k) (Fin (k + 1) × Fin h)) :
    auxiliaryFamilyDerivativeOrder h k i ≤ h * k + h + k - 1 := by
  have hi := (auxiliaryFamilyIndexEquiv h k i).isLt
  change (auxiliaryFamilyIndexEquiv h k i : ℕ) ≤ h * k + h + k - 1
  omega

theorem auxiliaryFamilyDerivativeOrder_sum (h k : ℕ) :
    (∑ i, auxiliaryFamilyDerivativeOrder h k i) =
      (h * k + h + k).choose 2 := by
  let n := h * k + h + k
  let e := auxiliaryFamilyIndexEquiv h k
  calc
    (∑ i, auxiliaryFamilyDerivativeOrder h k i) =
        ∑ j : Fin n, (j : ℕ) := by
          simpa only [auxiliaryFamilyDerivativeOrder, e, n] using
            (Equiv.sum_comp e (fun j : Fin n => (j : ℕ)))
    _ = ∑ j ∈ Finset.range n, j := by
      simpa using (Fin.sum_univ_eq_sum_range (fun j : ℕ => j) n)
    _ = n * (n - 1) / 2 := Finset.sum_range_id n
    _ = n.choose 2 := by rw [Nat.choose_two_right]

theorem auxiliaryFamily_k_le_card (h k : ℕ) :
    k ≤ h * k + h + k := by omega

section IndexedWronskian

variable {C L : Type*} [Field C] [Field L] [Algebra C L]

/-- Reindexing both rows and columns identifies the indexed consecutive-order
Wronskian with the ordinary `Fin n` Wronskian. -/
theorem indexedAuxiliaryWronskian_det_eq_derivationWronskian_det
    (D : Derivation C L L) (h k : ℕ)
    (f : Sum (Fin k) (Fin (k + 1) × Fin h) → L) :
    (indexedDedekindLocalWronskian D
      (auxiliaryFamilyDerivativeOrder h k) f).det =
      (BGS.Algebra.derivationWronskian D
        (fun j : Fin (h * k + h + k) =>
          f ((auxiliaryFamilyIndexEquiv h k).symm j))).det := by
  let e := auxiliaryFamilyIndexEquiv h k
  let g : Fin (h * k + h + k) → L := fun j => f (e.symm j)
  have hmatrix :
      indexedDedekindLocalWronskian D
          (auxiliaryFamilyDerivativeOrder h k) f =
        Matrix.reindex e.symm e.symm
          (BGS.Algebra.derivationWronskian D g) := by
    ext i j
    simp [indexedDedekindLocalWronskian,
      auxiliaryFamilyDerivativeOrder, BGS.Algebra.derivationWronskian,
      Matrix.reindex_apply, Matrix.submatrix, g, e]
    exact (Module.End.pow_apply D.toLinearMap _ (f j)).symm
  rw [hmatrix, Matrix.det_reindex_self]

/-- Exact constants and linear independence make the indexed global
Wronskian nonzero. -/
theorem indexedAuxiliaryWronskian_det_ne_zero_of_linearIndependent
    (D : Derivation C L L)
    (hconstants : ∀ x : L, D x = 0 →
      ∃ c : C, algebraMap C L c = x)
    (h k : ℕ) (f : Sum (Fin k) (Fin (k + 1) × Fin h) → L)
    (hLI : LinearIndependent C f) :
    (indexedDedekindLocalWronskian D
      (auxiliaryFamilyDerivativeOrder h k) f).det ≠ 0 := by
  let e := auxiliaryFamilyIndexEquiv h k
  let g : Fin (h * k + h + k) → L := fun j => f (e.symm j)
  have hLIg : LinearIndependent C g := hLI.comp e.symm e.symm.injective
  rw [indexedAuxiliaryWronskian_det_eq_derivationWronskian_det]
  exact BGS.Algebra.derivationWronskian_det_ne_zero_of_linearIndependent
    D hconstants _ g hLIg

end IndexedWronskian

end

end BGS.CorvajaZannier
