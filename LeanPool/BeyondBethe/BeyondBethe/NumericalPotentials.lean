/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.NumericalTransfer
public import Mathlib.Tactic

/-! # Numerical Potentials -/

@[expose] public section

namespace BeyondBethe

/-!
# Explicit row and column potentials

Least-squares projection is unnecessary in the numerical argument.  Fixing
one row and one column gives an explicit rational recovery map.  Exact
row-plus-column matrices are recovered identically, while a coordinatewise
perturbation of size `delta` creates residual at most `4 * delta`.
-/

/-- Row potentials anchored at one column. -/
def anchoredRowPotential
    {ι κ : Type*} (G : Matrix ι κ ℝ) (j0 : κ) : ι → ℝ :=
  fun i ↦ G i j0

/-- Column potentials anchored at one row and normalized to vanish at the
anchor column. -/
def anchoredColumnPotential
    {ι κ : Type*} (G : Matrix ι κ ℝ) (i0 : ι) (j0 : κ) : κ → ℝ :=
  fun j ↦ G i0 j - G i0 j0

theorem anchoredPotentials_exact
    {ι κ : Type*} (r : ι → ℝ) (c : κ → ℝ)
    (i0 : ι) (j0 : κ) (i : ι) (j : κ) :
    anchoredRowPotential (fun a b ↦ r a + c b) j0 i +
        anchoredColumnPotential (fun a b ↦ r a + c b) i0 j0 j =
      r i + c j := by
  simp [anchoredRowPotential, anchoredColumnPotential]

theorem abs_sub_sub_add_le_four
    {a b c d δ : ℝ}
    (ha : abs a ≤ δ) (hb : abs b ≤ δ)
    (hc : abs c ≤ δ) (hd : abs d ≤ δ) :
    abs (a - b - c + d) ≤ 4 * δ := by
  calc
    abs (a - b - c + d) = abs ((a - b) + (d - c)) := by ring
    _ ≤ abs (a - b) + abs (d - c) := abs_add_le _ _
    _ ≤ (abs a + abs b) + (abs d + abs c) :=
      add_le_add (abs_sub a b) (abs_sub d c)
    _ ≤ 4 * δ := by linarith

/-- Anchored potentials turn coordinatewise proximity to a row-plus-column
matrix into a coordinatewise KKT residual. -/
theorem anchoredPotentials_residual_le
    {ι κ : Type*} {G Gstar : Matrix ι κ ℝ}
    {r : ι → ℝ} {c : κ → ℝ} {δ : ℝ}
    (hstar : ∀ i j, Gstar i j = r i + c j)
    (hclose : ∀ i j, abs (G i j - Gstar i j) ≤ δ)
    (i0 : ι) (j0 : κ) (i : ι) (j : κ) :
    abs (G i j -
      (anchoredRowPotential G j0 i +
        anchoredColumnPotential G i0 j0 j)) ≤ 4 * δ := by
  have hid : G i j -
        (anchoredRowPotential G j0 i +
          anchoredColumnPotential G i0 j0 j) =
      (G i j - Gstar i j) - (G i j0 - Gstar i j0) -
        (G i0 j - Gstar i0 j) + (G i0 j0 - Gstar i0 j0) := by
    simp only [anchoredRowPotential, anchoredColumnPotential]
    rw [hstar i j, hstar i j0, hstar i0 j, hstar i0 j0]
    ring
  rw [hid]
  exact abs_sub_sub_add_le_four
    (hclose i j) (hclose i j0) (hclose i0 j) (hclose i0 j0)

/-- If `Gtilde` is a rational approximation to a computable gradient `G`,
the same anchored potentials have residual `evaluationError + 4 * modelError`
for `G`.  The statement separates elementary-function evaluation error from
the optimization error that moves the gradient away from the exact KKT
subspace. -/
theorem anchoredPotentials_residual_of_evaluation
    {ι κ : Type*} {G Gtilde Gstar : Matrix ι κ ℝ}
    {r : ι → ℝ} {c : κ → ℝ} {modelError evaluationError : ℝ}
    (hstar : ∀ i j, Gstar i j = r i + c j)
    (hmodel : ∀ i j, abs (Gtilde i j - Gstar i j) ≤ modelError)
    (heval : ∀ i j, abs (G i j - Gtilde i j) ≤ evaluationError)
    (i0 : ι) (j0 : κ) (i : ι) (j : κ) :
    abs (G i j -
      (anchoredRowPotential Gtilde j0 i +
        anchoredColumnPotential Gtilde i0 j0 j)) ≤
      evaluationError + 4 * modelError := by
  have hres := anchoredPotentials_residual_le
    hstar hmodel i0 j0 i j
  have htriangle : abs (G i j -
        (anchoredRowPotential Gtilde j0 i +
          anchoredColumnPotential Gtilde i0 j0 j)) ≤
      abs (G i j - Gtilde i j) +
        abs (Gtilde i j -
          (anchoredRowPotential Gtilde j0 i +
            anchoredColumnPotential Gtilde i0 j0 j)) := by
    have hid : (G i j - Gtilde i j) +
          (Gtilde i j -
            (anchoredRowPotential Gtilde j0 i +
              anchoredColumnPotential Gtilde i0 j0 j)) =
        G i j -
          (anchoredRowPotential Gtilde j0 i +
            anchoredColumnPotential Gtilde i0 j0 j) := by ring
    rw [← hid]
    exact abs_add_le _ _
  exact htriangle.trans (add_le_add (heval i j) hres)

end BeyondBethe
