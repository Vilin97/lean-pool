/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib
import LeanPool.NandakumarRamanaRao.NRR.PowerDiagram.Defs
import LeanPool.NandakumarRamanaRao.NRR.PowerDiagram.CellAlgebra
import LeanPool.NandakumarRamanaRao.NRR.HalfSpace

/-!
# Geometry of power cells

Proves convexity, closedness, and covering of the ambient space by power cells. The definitions are
in `NRR.PowerDiagram.Defs`, and the halfspace representation is in `CellAlgebra`.
-/

open NRR
open scoped RealInnerProductSpace

namespace NRR.PowerDiagram

variable {n : ℕ}

/-- Membership in a power cell: `x` lies in `cell s w i` iff `i` is (weakly) power‑closest to
`x` among all sites. -/
@[simp] theorem mem_cell (s : Fin n → E2) (w : Fin n → ℝ) (i : Fin n) (x : E2) :
    x ∈ cell s w i ↔ ∀ j, powerDist s w i x ≤ powerDist s w j x := Iff.rfl

/-- Every power cell is convex: it is an intersection of convex half‑spaces. -/
theorem cell_convex (s : Fin n → E2) (w : Fin n → ℝ) (i : Fin n) :
    Convex ℝ (cell s w i) := by
  rw [cell_eq_iInter_halfspace]
  exact convex_iInter (fun j => NRR.Halfspace.convex _ _)

/-- Every power cell is closed: it is an intersection of closed half‑spaces. -/
theorem cell_isClosed (s : Fin n → E2) (w : Fin n → ℝ) (i : Fin n) :
    IsClosed (cell s w i) := by
  rw [cell_eq_iInter_halfspace]
  exact isClosed_iInter (fun j => NRR.Halfspace.isClosed _ _)

/-- The power cells cover the whole plane. Requires at least one site (`[NeZero n]`): for each
`x`, pick an index `i` minimizing the finite family `j ↦ powerDist s w j x`. -/
theorem iUnion_cell [NeZero n] (s : Fin n → E2) (w : Fin n → ℝ) :
    ⋃ i, cell s w i = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨i, _, hi⟩ :=
    Finset.exists_min_image Finset.univ (fun k => powerDist s w k x)
      ⟨(⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ : Fin n), Finset.mem_univ _⟩
  simp only [Set.mem_iUnion, mem_cell]
  exact ⟨i, fun j => hi j (Finset.mem_univ j)⟩

end NRR.PowerDiagram
