/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic
import LeanPool.NandakumarRamanaRao.NRR.PowerDiagram.BodyCells
import LeanPool.NandakumarRamanaRao.NRR.PowerDiagram.CellAlgebra
import LeanPool.NandakumarRamanaRao.NRR.Geometry.HalfspaceFiniteIntersectionAreaContinuity

/-!
# `NRR.PowerDiagram.CellAreaContinuityWeights`

Weight‑continuity of restricted power‑cell areas with **fixed sites**.

Fixing the sites `s : Fin n → Plane` and letting the weights `w : Fin n → ℝ` vary, the
restricted power cell of site `i` is a finite intersection of *fixed‑normal* halfspaces whose
offsets move **linearly** (hence continuously) with the weights:

* normal of the `j`‑th halfspace is `sepNormal s i j = 2 • (s j - s i)` — independent of `w`;
* offset of the `j`‑th halfspace is `sepOffset s w i j = ‖s j‖² - ‖s i‖² - w j + w i`.

Specializing the moving‑halfspace area‑continuity result of
`NRR/Geometry/HalfspaceFiniteIntersectionAreaContinuity.lean` then yields
continuity of `w ↦ bodyCellArea K s w i`.

## The distinct‑sites hypothesis is necessary

The main theorem carries `hs : ∀ j, j ≠ i → s j ≠ s i`. This nondegeneracy hypothesis is
**mathematically required**: if `s j = s i` for some `j ≠ i` then `sepNormal s i j = 0` and the
`j`‑th halfspace degenerates to `{x | 0 ≤ sepOffset s w i j} = {x | w i ≥ w j}`, i.e. the whole
plane when `w i ≥ w j` and the empty set when `w i < w j`. The restricted area then jumps
discontinuously (from a positive value to `0`) as `w i` crosses `w j`. So without distinct
sites the statement is genuinely false; the hypothesis is how the degenerate case is handled
rather than omitted.

Note the *diagonal* term `j = i` always has `sepNormal s i i = 0` and `sepOffset s w i i = 0`,
so its halfspace is the constant whole plane `{x | 0 ≤ 0}`; it contributes nothing and is
harmless, which is why the diagonal is exempted (only the off‑diagonal normals must be
nonzero).
-/

open NRR NRR.Geometry NRR.Geometry.ConvexBody MeasureTheory
open scoped RealInnerProductSpace

namespace NRR.PowerDiagram

variable {n : ℕ}

/-- **Restricted power cell as a fixed‑normal finite halfspace intersection.** With sites `s`
fixed, `bodyCellSet K s w i` is exactly the finite intersection of `K` with the fixed‑normal
halfspaces `sepNormal s i j` at the (weight‑dependent) offsets `sepOffset s w i j`. -/
theorem bodyCellSet_eq_finiteHalfspaceIntersection
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane) (w : Fin n → ℝ) (i : Fin n) :
    bodyCellSet K s w i =
      finiteHalfspaceIntersection K (fun j => sepNormal s i j)
        (fun j => sepOffset s w i j) := by
  rw [bodyCellSet_def, cell_eq_iInter_halfspace]
  rfl

/-- **Offsets move continuously with the weights.** For fixed sites `s`, the whole offset
vector `j ↦ sepOffset s w i j` depends continuously (indeed affinely) on the weights `w`. -/
theorem continuous_sepOffset_weights
    (s : Fin n → Plane) (i : Fin n) :
    Continuous fun w : Fin n → ℝ => fun j => sepOffset s w i j := by
  refine continuous_pi fun j => ?_
  unfold sepOffset
  fun_prop

/-
**Restricted power cell as an off‑diagonal fixed‑normal finite halfspace intersection.**
The diagonal (`j = i`) halfspace is the constant whole plane, so it can be dropped, leaving the
intersection over `j ≠ i`, whose normals are nonzero exactly under the distinct‑sites
hypothesis.
-/
theorem bodyCellSet_eq_finiteHalfspaceIntersection_offDiag
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane) (w : Fin n → ℝ) (i : Fin n) :
    bodyCellSet K s w i =
      finiteHalfspaceIntersection K
        (fun j : {j : Fin n // j ≠ i} => sepNormal s i j.1)
        (fun j : {j : Fin n // j ≠ i} => sepOffset s w i j.1) := by
  convert Set.ext _;
  intro x; simp +decide [ finiteHalfspaceIntersection ] ;
  intro hx; constructor <;> intro h <;> intro j <;> by_cases hj : j = i <;> simp_all +decide [ powerDist_le_iff_halfspace ] ;

/-- **Fixed‑site weight‑continuity of the restricted power‑cell area.** With sites `s` fixed and
pairwise distinct from `s i` (`hs`), the restricted cell area `w ↦ bodyCellArea K s w i` is
continuous. The hypothesis `hs` is necessary (see the module docstring). -/
theorem continuous_bodyCellArea_weights
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane) (i : Fin n)
    (hs : ∀ j, j ≠ i → s j ≠ s i) :
    Continuous fun w : Fin n → ℝ => bodyCellArea K s w i := by
  have hu : ∀ j : {j : Fin n // j ≠ i}, (fun j : {j : Fin n // j ≠ i} => sepNormal s i j.1) j ≠ 0 := by
    intro j
    simp only [sepNormal]
    have h : s j.1 - s i ≠ 0 := sub_ne_zero.mpr (hs j.1 j.2)
    exact smul_ne_zero (by norm_num) h
  have hc : Continuous fun w : Fin n → ℝ => fun j : {j : Fin n // j ≠ i} => sepOffset s w i j.1 := by
    refine continuous_pi fun j => ?_
    unfold sepOffset
    fun_prop
  have key : (fun w : Fin n → ℝ => bodyCellArea K s w i) =
      fun w : Fin n → ℝ => finiteHalfspaceIntersectionArea K
        (fun j : {j : Fin n // j ≠ i} => sepNormal s i j.1)
        (fun j : {j : Fin n // j ≠ i} => sepOffset s w i j.1) := by
    funext w
    rw [bodyCellArea, bodyCellSet_eq_finiteHalfspaceIntersection_offDiag,
      finiteHalfspaceIntersectionArea]
  rw [key]
  exact continuous_finiteHalfspaceIntersectionArea K
    (fun j : {j : Fin n // j ≠ i} => sepNormal s i j.1) hu
    (fun w j => sepOffset s w i j.1) hc

end NRR.PowerDiagram
