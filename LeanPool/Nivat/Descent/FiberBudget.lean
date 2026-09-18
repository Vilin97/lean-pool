/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boon Suan Ho
-/

import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Data.Set.Card

/-
Upstream: https://github.com/boonsuan/nivat
Commit: 84fe839635bdebb7d5e80c209b4f578a0c767fcf
Originally released under MIT; the upstream copyright and permission notice follow.

MIT License

Copyright (c) 2026 Boon Suan Ho

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/-!
# Counting differences within fibers

The finite-set argument at the end of Theorem 2.2 (`thm:descent`) in
`paper/nivat.tex`. A fiber with `k` inputs needs at most `k - 1` generators for
all of its differences. `finite_fiber_budget` sums that bound over the fibers.

The argument uses an arbitrary function between sets of vectors. The application
to a Laurent filter is in `Nivat.Descent.ExactDescent`.
-/

namespace Nivat.Descent

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Differences between members of one fiber.
This is the generating set in the counting step of Theorem 2.2 (`thm:descent`). -/
def fiberDifferences (F : V → W) (P : Set V) : Set V :=
  {d | ∃ x ∈ P, ∃ y ∈ P, F x = F y ∧ d = x - y}

/-- One chosen input for each occurring output, in the proof of Theorem 2.2 (`thm:descent`). -/
private noncomputable def fiberRepresentatives (F : V → W) (P : Set V) : Set V :=
  Function.invFunOn F P '' (F '' P)

/-- Subtract the chosen representative from each other input in its fiber.
These are the generators counted in the proof of Theorem 2.2 (`thm:descent`). -/
private noncomputable def representativeDifferences (F : V → W) (P : Set V) : Set V :=
  (fun x => x - Function.invFunOn F P (F x)) '' (P \ fiberRepresentatives F P)

/-- Chosen representatives are inputs, as required in Theorem 2.2 (`thm:descent`). -/
private theorem fiberRepresentatives_subset (F : V → W) (P : Set V) :
    fiberRepresentatives F P ⊆ P :=
  Function.invFunOn_image_image_subset F P

/-- There is one representative per output in the proof of Theorem 2.2 (`thm:descent`). -/
private theorem fiberRepresentatives_ncard (F : V → W) (P : Set V) :
    (fiberRepresentatives F P).ncard = (F '' P).ncard :=
  (Function.invFunOn_injOn_image F P).ncard_image

/-- Each representative difference lies in a fiber, in Theorem 2.2 (`thm:descent`). -/
private theorem representativeDifferences_subset (F : V → W) (P : Set V) :
    representativeDifferences F P ⊆ fiberDifferences F P := by
  rintro d ⟨x, hx, rfl⟩
  exact ⟨x, hx.1, Function.invFunOn F P (F x),
    Function.invFunOn_apply_mem hx.1,
    (Function.invFunOn_apply_eq hx.1).symm, rfl⟩

/-- An input minus its representative belongs to the chosen span, including when
it is zero. This is an auxiliary step in Theorem 2.2 (`thm:descent`). -/
private theorem representativeDifference_mem_span (F : V → W) (P : Set V)
    {x : V} (hx : x ∈ P) :
    x - Function.invFunOn F P (F x) ∈
      Submodule.span K (representativeDifferences F P) := by
  by_cases hr : x ∈ fiberRepresentatives F P
  · obtain ⟨y, hy, hxy⟩ := hr
    have hFy : F (Function.invFunOn F P y) = y := Function.invFunOn_eq hy
    have hxrep : x = Function.invFunOn F P (F x) := by
      rw [← hxy, hFy]
    rw [← hxrep, sub_self]
    exact Submodule.zero_mem _
  · exact Submodule.subset_span ⟨x, ⟨hx, hr⟩, rfl⟩

/-- The chosen representative differences span all same-fiber differences.
This is the spanning assertion in the proof of Theorem 2.2 (`thm:descent`). -/
private theorem span_fiberDifferences_eq (F : V → W) (P : Set V) :
    Submodule.span K (fiberDifferences F P) =
      Submodule.span K (representativeDifferences F P) := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro d ⟨x, hx, y, hy, hF, rfl⟩
    have h := Submodule.sub_mem (Submodule.span K (representativeDifferences F P))
      (representativeDifference_mem_span F P hx)
      (representativeDifference_mem_span F P hy)
    rw [hF] at h
    change x - y ∈ Submodule.span K (representativeDifferences F P)
    simpa only [sub_sub_sub_cancel_right] using h
  · exact Submodule.span_mono (representativeDifferences_subset F P)

/-- The number of generators is the number of inputs minus the number of outputs.
This is the counting identity in Theorem 2.2 (`thm:descent`), written additively. -/
private theorem representative_index_budget (F : V → W) {P : Set V} (hP : P.Finite) :
    (P \ fiberRepresentatives F P).ncard + (F '' P).ncard = P.ncard := by
  rw [← fiberRepresentatives_ncard F P]
  exact Set.ncard_sdiff_add_ncard_of_subset (fiberRepresentatives_subset F P) hP

/-- A finite input set yields a finite-dimensional space of same-fiber differences.
This is the finite-span step in Theorem 2.2 (`thm:descent`). -/
theorem finiteDimensional_fiberDifferences (F : V → W) {P : Set V} (hP : P.Finite) :
    FiniteDimensional K (Submodule.span K (fiberDifferences F P)) := by
  rw [span_fiberDifferences_eq]
  exact FiniteDimensional.span_of_finite K (hP.sdiff.image _)

/-- The fiber-counting inequality in Theorem 2.2 (`thm:descent`).
It holds for any function on a finite set of vectors; neither linearity nor a
finite-dimensional ambient space is needed. -/
theorem finite_fiber_budget (F : V → W) {P : Set V} (hP : P.Finite) :
    Module.finrank K (Submodule.span K (fiberDifferences F P)) +
      (F '' P).ncard ≤ P.ncard := by
  classical
  have hD : (representativeDifferences F P).Finite := hP.sdiff.image _
  let : Fintype (representativeDifferences F P) := hD.fintype
  have hdim : Module.finrank K (Submodule.span K (representativeDifferences F P)) ≤
      (representativeDifferences F P).ncard := by
    simpa only [Set.ncard_eq_toFinset_card'] using
      (finrank_span_le_card (R := K) (representativeDifferences F P))
  have hcard : (representativeDifferences F P).ncard ≤
      (P \ fiberRepresentatives F P).ncard := Set.ncard_image_le hP.sdiff
  rw [span_fiberDifferences_eq]
  exact (Nat.add_le_add_right (hdim.trans hcard) _).trans_eq
    (representative_index_budget F hP)

end Nivat.Descent
