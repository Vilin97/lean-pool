/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Algebra.Group.Basic

import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Union

/-!
# Choosing points with differences outside a finite set

Given finitely many infinite subsets `E i` of a commutative additive group and a finite set `D`,
one can pick one point from each `E i` so that no difference of two chosen points lies in `D`.
The points are chosen one at a time; at each step only finitely many values are excluded.
-/

universe u v

public section

/-- From finitely many infinite sets one can choose one point each with all pairwise differences
outside a given finite set. -/
theorem exists_forall_mem_forall_sub_notMem {α : Type u} [AddCommGroup α] {ι : Type v}
    (s : Finset ι) (E : ι → Set α) (hE : ∀ i, (E i).Infinite) (D : Finset α) :
    ∃ x : ι → α, (∀ i ∈ s, x i ∈ E i) ∧ ∀ i ∈ s, ∀ j ∈ s, i ≠ j → x i - x j ∉ D := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨fun i ↦ (hE i).nonempty.choose, fun i hi ↦ absurd hi (Finset.notMem_empty i),
        fun i hi ↦ absurd hi (Finset.notMem_empty i)⟩
  | insert a s ha ih =>
      obtain ⟨x, hxE, hxD⟩ := ih
      -- The values excluded for the new point: `x j + d` and `x j - d` for `j ∈ s`, `d ∈ D`.
      let F : Finset α := s.biUnion fun j ↦ D.image (fun d ↦ x j + d) ∪ D.image (fun d ↦ x j - d)
      obtain ⟨y, hyE, hyF⟩ := (hE a).exists_notMem_finset F
      refine ⟨Function.update x a y, fun i hi ↦ ?_, fun i hi j hj hij ↦ ?_⟩
      · rcases Finset.mem_insert.mp hi with hia | hi
        · rw [hia, Function.update_self]; exact hyE
        · rw [Function.update_of_ne (fun h ↦ ha (by rw [← h]; exact hi))]; exact hxE i hi
      · rcases Finset.mem_insert.mp hi with hia | hi
        · rcases Finset.mem_insert.mp hj with hja | hj
          · exact absurd (hia.trans hja.symm) hij
          · rw [hia, Function.update_self,
              Function.update_of_ne (fun h ↦ ha (by rw [← h]; exact hj))]
            intro hd
            apply hyF
            refine Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_union_left _ ?_⟩
            exact Finset.mem_image.mpr ⟨y - x j, hd, add_sub_cancel (x j) y⟩
        · rcases Finset.mem_insert.mp hj with hja | hj
          · rw [hja, Function.update_self,
              Function.update_of_ne (fun h ↦ ha (by rw [← h]; exact hi))]
            intro hd
            apply hyF
            refine Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_union_right _ ?_⟩
            exact Finset.mem_image.mpr ⟨x i - y, hd, sub_sub_cancel (x i) y⟩
          · rw [Function.update_of_ne (fun h ↦ ha (by rw [← h]; exact hi)),
              Function.update_of_ne (fun h ↦ ha (by rw [← h]; exact hj))]
            exact hxD i hi j hj hij

end
