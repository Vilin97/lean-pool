/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.InsertionAlgebra
import LeanPool.Feige.ChainInsertion
import LeanPool.Feige.ChainFromBoolean

/-!
# Statistic values on an inserted Boolean chain

This file connects the concrete inserted Boolean chain to the abstract
`A`/`B` statistic sequences used in the mass-transport proof of Theorem 2.1.
-/

namespace Feige

/-- The `Bᵣ` value at the lifted lower state `Cᵣ`, extended by zero after
the old chain's sentinel. -/
noncomputable def insertionLowerK {n : ℕ}
    (γ β : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin n)) (r : ℕ) : ℝ :=
  if hr : r < n + 1 then
    twoPointKFinset γ β
      (liftChainState (chainState σ ⟨r, hr⟩))
  else 0

/-- The `Aᵣ` value at the lifted upper state `Hᵣ`, extended by zero after
the old chain's sentinel. -/
noncomputable def insertionUpperK {n : ℕ}
    (γ β : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin n)) (r : ℕ) : ℝ :=
  if hr : r < n + 1 then
    twoPointKFinset γ β
      (insert (Fin.last n) (liftChainState (chainState σ ⟨r, hr⟩)))
  else 0

/-- The old `n`-coordinate statistic sequence `Fᵣ`, including its zero
sentinel. -/
noncomputable def insertionOldK {n : ℕ}
    (γ β : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin n)) (r : ℕ) : ℝ :=
  booleanChainK (fun i ↦ γ i.castSucc) (fun i ↦ β i.castSucc) σ r

/-- Band width `wᵣ = Bᵣ - Aᵣ`. -/
noncomputable def insertionWidth {n : ℕ}
    (γ β : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin n)) (r : ℕ) : ℝ :=
  insertionLowerK γ β σ r - insertionUpperK γ β σ r

/-- Conditional interpolation parameter
`θᵣ = (Fᵣ - Aᵣ) / (Bᵣ - Aᵣ)`. -/
noncomputable def insertionTheta {n : ℕ}
    (γ β : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin n)) (r : ℕ) : ℝ :=
  (insertionOldK γ β σ r - insertionUpperK γ β σ r) /
    insertionWidth γ β σ r

/-- Monotonicity of `K` makes every insertion band width nonnegative. -/
theorem insertionWidth_nonneg {n : ℕ}
    (γ β : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin n))
    (hγ : ∀ i, 0 ≤ γ i) (hβ : ∀ i, 0 ≤ β i) (r : ℕ) :
    0 ≤ insertionWidth γ β σ r := by
  unfold insertionWidth insertionLowerK insertionUpperK
  by_cases hr : r < n + 1
  · rw [dite_eq_left hr, dite_eq_left hr]
    exact sub_nonneg.mpr
      (twoPointKFinset_antitone hγ hβ (Finset.subset_insert _ _))
  · rw [dite_eq_right hr, dite_eq_right hr, sub_zero]

/-- The defining interpolation identity, whenever the band has positive
width (nonzero is algebraically sufficient). -/
theorem insertionOldK_eq_upper_add_theta_mul_width {n : ℕ}
    (γ β : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin n)) (r : ℕ)
    (hw : insertionWidth γ β σ r ≠ 0) :
    insertionOldK γ β σ r =
      insertionUpperK γ β σ r +
        insertionTheta γ β σ r * insertionWidth γ β σ r := by
  unfold insertionTheta
  field_simp [hw]
  ring

/-- The interpolation identity on the whole zero-extended sequence, given
nondegeneracy of every genuine insertion band. -/
theorem insertionOldK_eq_upper_add_theta_mul_width_all {n : ℕ}
    (γ β : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin n))
    (hw : ∀ r < n + 1, insertionWidth γ β σ r ≠ 0) (r : ℕ) :
    insertionOldK γ β σ r =
      insertionUpperK γ β σ r +
        insertionTheta γ β σ r * insertionWidth γ β σ r := by
  by_cases hr : r < n + 1
  · exact insertionOldK_eq_upper_add_theta_mul_width γ β σ r (hw r hr)
  · have hF : insertionOldK γ β σ r = 0 := by
      exact booleanChainK_of_not_lt _ _ _ hr
    have hA : insertionUpperK γ β σ r = 0 := by
      simp [insertionUpperK, hr]
    have hB : insertionLowerK γ β σ r = 0 := by
      simp [insertionLowerK, hr]
    rw [hF, hA]
    simp [insertionTheta, insertionWidth, hF, hA, hB]

@[simp]
theorem insertionTheta_sentinel {n : ℕ}
    (γ β : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin n)) :
    insertionTheta γ β σ (n + 1) = 0 := by
  unfold insertionTheta insertionOldK insertionWidth
    insertionLowerK insertionUpperK
  rw [booleanChainK_sentinel]
  simp

/-- The initial old and lower statistic values both equal one. -/
theorem insertionOldK_zero_eq_lowerK_zero {n : ℕ}
    (γ β : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin n))
    (hγ : ∀ i, 0 ≤ γ i) :
    insertionOldK γ β σ 0 = 1 ∧ insertionLowerK γ β σ 0 = 1 := by
  constructor
  · unfold insertionOldK
    exact booleanChainK_initial _ _ σ (fun i ↦ hγ i.castSucc)
  · unfold insertionLowerK
    rw [dite_eq_left (Nat.zero_lt_succ n)]
    have hs :
        chainState σ ⟨0, Nat.zero_lt_succ n⟩ = ∅ := by
      ext i
      simp
    rw [hs]
    simp only [liftChainState, Finset.map_empty]
    simpa [twoPointKFinset] using twoPointK_empty γ β hγ

/-- The initial interpolation parameter is one when its band is
nondegenerate. -/
theorem insertionTheta_zero {n : ℕ}
    (γ β : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin n))
    (hγ : ∀ i, 0 ≤ γ i)
    (hw : insertionWidth γ β σ 0 ≠ 0) :
    insertionTheta γ β σ 0 = 1 := by
  rcases insertionOldK_zero_eq_lowerK_zero γ β σ hγ with ⟨hF, hB⟩
  have hw' : 1 - insertionUpperK γ β σ 0 ≠ 0 := by
    simpa [insertionWidth, hB] using hw
  unfold insertionTheta insertionWidth
  rw [hF, hB]
  exact div_self hw'

/-- At every genuine level, the statistic along the inserted permutation is
exactly `Bᵣ` before insertion and `Aᵣ₋₁` afterwards. -/
theorem booleanChainK_insertChainPerm_eq {n : ℕ}
    (γ β : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin n))
    (J : Fin (n + 1)) (r : Fin (n + 2)) :
    booleanChainK γ β (insertChainPerm σ J) r.val =
      insertionStatisticSequence
        (insertionUpperK γ β σ) (insertionLowerK γ β σ) J.val r.val := by
  rw [booleanChainK_of_lt γ β (insertChainPerm σ J) r.isLt]
  rw [chainState_insertChainPerm_eq_insertedChainState]
  unfold insertionStatisticSequence insertedChainState
  split_ifs with h
  · unfold insertionLowerK
    rw [dite_eq_left (lt_of_le_of_lt h J.isLt)]
  · unfold insertionUpperK
    have hJr : J.val < r.val := Nat.lt_of_not_ge h
    have hrpos : 0 < r.val := lt_of_le_of_lt (Nat.zero_le _) hJr
    have hrlt : r.val - 1 < n + 1 := by omega
    rw [dite_eq_left hrlt]

/-- The preceding identity, including the zero sentinel and the zero
extension beyond it. -/
theorem booleanChainK_insertChainPerm_eq_nat {n : ℕ}
    (γ β : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin n))
    (J : Fin (n + 1)) (r : ℕ) :
    booleanChainK γ β (insertChainPerm σ J) r =
      insertionStatisticSequence
        (insertionUpperK γ β σ) (insertionLowerK γ β σ) J.val r := by
  by_cases hr : r < n + 2
  · let rf : Fin (n + 2) := ⟨r, hr⟩
    simpa only [rf] using booleanChainK_insertChainPerm_eq γ β σ J rf
  · rw [booleanChainK_of_not_lt γ β (insertChainPerm σ J) hr]
    unfold insertionStatisticSequence
    rw [ite_eq_right (by omega : ¬r ≤ J.val)]
    unfold insertionUpperK
    rw [dite_eq_right (by omega : ¬r - 1 < n + 1)]

/-- The actual chain mass at a present lower state `Cⱼ` is its lower rank
contribution. -/
theorem chainMass_booleanChainK_insert_lower {n : ℕ}
    (γ β : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin n))
    (J j : Fin (n + 1)) (hjJ : j ≤ J) :
    chainMass (booleanChainK γ β (insertChainPerm σ J)) j.val =
      lowerMassForInsertion (insertionLowerK γ β σ)
        (fun r ↦ insertionLowerK γ β σ r - insertionUpperK γ β σ r)
        J.val j.val := by
  unfold chainMass
  rw [booleanChainK_insertChainPerm_eq_nat,
    booleanChainK_insertChainPerm_eq_nat]
  simpa only [chainMass] using
    (chainMass_insertionStatisticSequence_lower
      (A := insertionUpperK γ β σ) (B := insertionLowerK γ β σ)
      (w := fun r ↦ insertionLowerK γ β σ r - insertionUpperK γ β σ r)
      hjJ rfl)

/-- The actual chain mass at a present upper state `Hⱼ` is its upper rank
contribution, including the terminal edge to the zero sentinel. -/
theorem chainMass_booleanChainK_insert_upper {n : ℕ}
    (γ β : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin n))
    (J j : Fin (n + 1)) (hJj : J ≤ j) :
    chainMass (booleanChainK γ β (insertChainPerm σ J)) (j.val + 1) =
      upperMassForInsertion (insertionUpperK γ β σ) J.val j.val := by
  unfold chainMass
  rw [booleanChainK_insertChainPerm_eq_nat,
    booleanChainK_insertChainPerm_eq_nat]
  simpa only [chainMass] using
    (chainMass_insertionStatisticSequence_upper
      (A := insertionUpperK γ β σ) (B := insertionLowerK γ β σ) hJj)

end Feige
