/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import Mathlib.Tactic
public import LeanPool.NandakumarRamanaRao.NRR.PowerDiagram.Defs

/-!
# `NRR.PowerDiagram.CellAlgebra` — exact half‑space description of power cells

Given `n` sites `s : Fin n → E2` and weights `w : Fin n → ℝ`, the power (Laguerre) cell of
site `i` is `{x | ∀ j, powerDist s w i x ≤ powerDist s w j x}` where
`powerDist s w i x = ‖x - sᵢ‖² - wᵢ`.

Expanding `‖x - a‖² = ‖x‖² - 2⟪x,a⟫ + ‖a‖²` and cancelling the shared `‖x‖²` term shows the
pairwise inequality `powerDist s w i x ≤ powerDist s w j x` is equivalent to membership in the
closed half‑space `{x | ⟪u, x⟫ ≤ c}` with **exact** normal / offset data

* `u = sepNormal s i j = 2 • (sⱼ - sᵢ)`,
* `c = sepOffset s w i j = ‖sⱼ‖² - ‖sᵢ‖² - wⱼ + wᵢ`.

When `i = j` the normal is `0` and the offset is `0`, so the half‑space is the whole plane,
matching the (always true) inequality `powerDist s w i x ≤ powerDist s w i x`.

This yields the exact intersection‑of‑half‑spaces representation of each power cell.
-/

@[expose] public section

open NRR
open scoped RealInnerProductSpace

namespace NRR.PowerDiagram

variable {n : ℕ}

/-- **Separating normal** for the pair `(i, j)`: the inner normal of the closed half‑space
whose boundary is the radical axis of sites `i` and `j`. Chosen as `2 • (sⱼ - sᵢ)` so that
`powerDist s w i x ≤ powerDist s w j x ↔ ⟪sepNormal s i j, x⟫ ≤ sepOffset s w i j`. -/
noncomputable def sepNormal (s : Fin n → E2) (i j : Fin n) : E2 :=
  (2 : ℝ) • (s j - s i)

/-- **Separating offset** for the pair `(i, j)`: the offset of the closed half‑space bounding
the power cell of `i` against `j`, equal to `‖sⱼ‖² - ‖sᵢ‖² - wⱼ + wᵢ`. -/
noncomputable def sepOffset (s : Fin n → E2) (w : Fin n → ℝ) (i j : Fin n) : ℝ :=
  ‖s j‖ ^ 2 - ‖s i‖ ^ 2 - w j + w i

/-- The pairwise power‑distance inequality is exactly membership in the closed half‑space with
normal `sepNormal s i j` and offset `sepOffset s w i j`. -/
theorem powerDist_le_iff_halfspace (s : Fin n → E2) (w : Fin n → ℝ)
    (i j : Fin n) (x : E2) :
    powerDist s w i x ≤ powerDist s w j x ↔
      x ∈ NRR.Halfspace.of (sepNormal s i j) (sepOffset s w i j) := by
  rw [NRR.Halfspace.mem_halfspace]
  unfold powerDist sepNormal sepOffset
  rw [norm_sub_sq_real x (s i), norm_sub_sq_real x (s j), real_inner_smul_left,
    inner_sub_left, real_inner_comm (s i) x, real_inner_comm (s j) x]
  constructor <;> intro h <;> nlinarith [h]

/-- Each power cell is the exact intersection over `j` of the closed half‑spaces
`Halfspace.of (sepNormal s i j) (sepOffset s w i j)`. -/
theorem cell_eq_iInter_halfspace (s : Fin n → E2) (w : Fin n → ℝ) (i : Fin n) :
    cell s w i = ⋂ j, NRR.Halfspace.of (sepNormal s i j) (sepOffset s w i j) := by
  ext x
  simp only [cell, Set.mem_ofPred_eq, Set.mem_iInter, powerDist_le_iff_halfspace]

end NRR.PowerDiagram
