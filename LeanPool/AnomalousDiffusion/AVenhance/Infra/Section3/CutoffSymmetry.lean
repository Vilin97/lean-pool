/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.ShearFormula
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.TimeScaleArithmetic
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.ZetaProd
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.PsiM
public import LeanPool.AnomalousDiffusion.Homogenization.Ambient.Basic
public import Mathlib.Algebra.Order.Floor.Ring

/-! Translation identities at the large Section 3 time scale. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section3

open AVenhance Homogenization

/-- The number of small cells in a large cell is congruent to one modulo four. -/
theorem tauCellCount_mod_four (β : ℝ) (Λ m : ℕ) :
    Infra.Ingredients.tauCellCount β Λ m % 4 = 1 := by
  unfold Infra.Ingredients.tauCellCount
  let n := ⌈epsilon β Λ (m - 1) ^ (-delta β)⌉₊
  change (4 * n + 1) ^ 2 % 4 = 1
  have hsq : (4 * n + 1) ^ 2 = 4 * (4 * n ^ 2 + 2 * n) + 1 := by ring
  rw [hsq]
  omega

/-- Shifting the small integer index by two large cells advances the large cutoff index by exactly
    two. -/
theorem lIdx_add_twoCellCount {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) (k : ℤ) :
    lIdx β I.Λ m (k + 2 * (Infra.Ingredients.tauCellCount β I.Λ m : ℤ)) =
      lIdx β I.Λ m k + 2 := by
  let p := Infra.Ingredients.tauCellCount β I.Λ m
  have hτ := Infra.Ingredients.tau_pos (m := m)
    I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hratio := Infra.Ingredients.tauPP_eq_cellCount_mul_tau
    (β := β) (Λ := I.Λ) (m := m) hm
  have hp : 0 < (p : ℝ) := by
    dsimp [p, Infra.Ingredients.tauCellCount]
    positivity
  have hcountPos : 0 < (Infra.Ingredients.tauCellCount β I.Λ m : ℝ) := by
    simpa [p] using hp
  have hcountInv :
      (Infra.Ingredients.tauCellCount β I.Λ m : ℝ) *
        (Infra.Ingredients.tauCellCount β I.Λ m : ℝ)⁻¹ = 1 :=
    mul_inv_cancel₀ (ne_of_gt hcountPos)
  have hshift :
      (((k + 2 * (p : ℤ) : ℤ) : ℝ) * tau β I.Λ m +
          (1 / 2) * (tauPP β I.Λ m - tau β I.Λ m)) /
          tauPP β I.Λ m =
        (((k : ℝ) * tau β I.Λ m +
          (1 / 2) * (tauPP β I.Λ m - tau β I.Λ m)) /
          tauPP β I.Λ m) + (2 : ℤ) := by
    rw [hratio]
    simp only [p]
    push_cast
    field_simp [ne_of_gt hτ, ne_of_gt hp]
    ring_nf
  unfold lIdx
  rw [hshift, Int.floor_add_intCast]

/-- The product of the two time cutoffs is invariant when time and its small
index are shifted together by two large cells. -/
theorem zetaProd_add_twoCellCount {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) (k : ℤ) (t : ℝ) :
    I.zetaProd m (k + 2 * (Infra.Ingredients.tauCellCount β I.Λ m : ℤ))
        (t + 2 * tauPP β I.Λ m) = I.zetaProd m k t := by
  have hτ := Infra.Ingredients.tau_pos (m := m)
    I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hratio := Infra.Ingredients.tauPP_eq_cellCount_mul_tau
    (β := β) (Λ := I.Λ) (m := m) hm
  have hindex := lIdx_add_twoCellCount I hm k
  have hsmall :
      (t + 2 * tauPP β I.Λ m -
          (↑(k + 2 *
            (Infra.Ingredients.tauCellCount β I.Λ m : ℤ)) : ℝ) *
            tau β I.Λ m) /
          tau β I.Λ m = (t - (k : ℝ) * tau β I.Λ m) /
            tau β I.Λ m := by
    rw [hratio]
    push_cast
    field_simp [ne_of_gt hτ]
    ring
  have hlarge :
      t + 2 * tauPP β I.Λ m -
          (↑(lIdx β I.Λ m k + 2) : ℝ) * tauPP β I.Λ m =
        t - (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m := by
    push_cast
    ring
  change
    I.hatZetaML m (lIdx β I.Λ m
      (k + 2 * (Infra.Ingredients.tauCellCount β I.Λ m : ℤ)))
        (t + 2 * tauPP β I.Λ m) *
      I.zetaMK m (k + 2 * (Infra.Ingredients.tauCellCount β I.Λ m : ℤ))
        (t + 2 * tauPP β I.Λ m) =
    I.hatZetaML m (lIdx β I.Λ m k) t * I.zetaMK m k t
  rw [hindex]
  simp only [Ingredients.hatZetaML, shiftCutoff, Ingredients.zetaMK,
    scaledCutoff, hlarge, hsmall]

end AVenhance.Infra.Section3
