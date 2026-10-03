/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftJacobian.CellMean

/-!: the pulled cell flux `C⁰_k` of `normie3⁺` is the cell flux
`cellFluxCell` (whose fast mean is the flux, `cellFluxCell_mean`) composed with
the inverse flow `Y_{l_k}`. -/

@[expose] public section

noncomputable section

open Homogenization

namespace AVenhance.Infra.Section5.LeftJacobian

open AVenhance AVenhance.Infra.Section5

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- `C⁰_k(x) = cellFluxCell (Y_{l_k} x)`. -/
theorem cellFlux_eq_cellFluxCell_comp (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (k : ℤ)
    (t : ℝ) (x : Vec 2) :
    cellFlux I hΦ m κm k t x =
      cellFluxCell I m κm k t (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) := by
  simp [cellFlux, cellFluxCell, selCoeff, Ingredients.zetaProd, mul_assoc]

end AVenhance.Infra.Section5.LeftJacobian

end
