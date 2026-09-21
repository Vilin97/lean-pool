/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Path

/-!
# First exit of a path from an open set

A path starting inside an open set and ending outside it has a positive first exit time. The
path is extended to real parameters using Mathlib’s `Path.extend`.

## Main results

* `Path.extend_exists_first_notMem`: First time a path starting in an open set leaves that set.
-/

public section

open Set

/-- First time a path starting in an open set leaves that set. -/
theorem Path.extend_exists_first_notMem {X : Type*} [TopologicalSpace X] {x y : X}
    (γ : Path x y) {A : Set X} (hA : IsOpen A)
    (hx : γ.extend 0 ∈ A) (hy : γ.extend 1 ∉ A) :
    ∃ t, t ∈ Icc (0 : ℝ) 1 ∧ γ.extend t ∉ A ∧ 0 < t ∧
      ∀ s, 0 ≤ s → s < t → γ.extend s ∈ A := by
  set S : Set ℝ := Icc (0 : ℝ) 1 ∩ γ.extend ⁻¹' Aᶜ
  have hSc : IsClosed S := isClosed_Icc.inter (hA.isClosed_compl.preimage γ.continuous_extend)
  have hSne : S.Nonempty := ⟨1, ⟨zero_le_one, le_rfl⟩, hy⟩
  have hSbdd : BddBelow S := ⟨0, fun t ht => ht.1.1⟩
  have hsS : sInf S ∈ S := hSc.csInf_mem hSne hSbdd
  have hs01 : sInf S ∈ Icc (0 : ℝ) 1 := hsS.1
  have h0S : (0 : ℝ) ∉ S := fun h => h.2 hx
  have hs0 : 0 < sInf S := lt_of_le_of_ne hs01.1 fun h => h0S (h ▸ hsS)
  refine ⟨sInf S, hs01, hsS.2, hs0, fun s hs0' hst => ?_⟩
  by_contra h
  exact notMem_of_lt_csInf hst hSbdd ⟨⟨hs0', hst.le.trans hs01.2⟩, h⟩

end

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
