/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import LeanPool.Sensitivity.Defs
import Archive.Sensitivity
import Mathlib.Data.Fintype.Pi

/-!
# Bridge to Mathlib's Huang Theorem

Repackages Mathlib's `Sensitivity.huang_degree_theorem` (the Huang hypercube
lemma) in a form that uses `Finset (Fin (m+1) → Bool)` and the `flipBit`
predicate from `LeanPool.Sensitivity.Defs`, ready to feed into the
sensitivity-conjecture argument.

The Mathlib formalisation in `Archive.Sensitivity` originated in the
[lean-sensitivity](https://github.com/leanprover-community/lean-sensitivity)
project, a community formalisation of Huang's proof carried out shortly after
the original paper appeared in 2019.
-/

namespace LeanPoolSensitivity

/-- A finset-flavoured restatement of Mathlib's
`Sensitivity.huang_degree_theorem`: any subset `H` of the hypercube of size
at least `2^m + 1` contains a vertex `q` with at least `√(m+1)` neighbours
in `H`, where neighbours are bit-flip images `flipBit q i`. -/
theorem huang_finset {m : ℕ} (H : Finset (Fin (m + 1) → Bool))
    (hH : 2 ^ m + 1 ≤ H.card) :
    ∃ q ∈ H, Real.sqrt (↑m + 1) ≤
      ↑(H.filter (fun p => ∃ i, p = flipBit q i)).card := by
  classical
  let e : Sensitivity.Q m.succ ≃ (Fin (m + 1) → Bool) :=
    { toFun := fun x => (show Fin (m + 1) → Bool from x)
      invFun := fun x => (show Sensitivity.Q m.succ from x)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let HQ : Set (Sensitivity.Q m.succ) := {x | e x ∈ H}
  let : DecidablePred (fun a : Sensitivity.Q m.succ => a ∈ HQ) :=
    Classical.decPred _
  have hmap : HQ.toFinset.map e.toEmbedding = H := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_map.mp hx with ⟨y, hy, hxy⟩
      have hyHQ : y ∈ HQ := Set.mem_toFinset.mp hy
      change e y ∈ H at hyHQ
      rw [← hxy]
      exact hyHQ
    · intro hx
      apply Finset.mem_map.mpr
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      apply Set.mem_toFinset.mpr
      change e (e.symm x) ∈ H
      simpa only [Equiv.apply_symm_apply] using hx
  have hHQcard : HQ.toFinset.card = H.card := by rw [← hmap]
                                                 simp
  have hHQ : HQ.toFinset.card ≥ 2 ^ m + 1 := by
    omega
  obtain ⟨q, hqH, hbound⟩ := Sensitivity.huang_degree_theorem HQ hHQ
  have hqH' : e q ∈ H := by
    change q ∈ HQ at hqH
    change e q ∈ H at hqH
    exact hqH
  refine ⟨e q, hqH', le_trans hbound ?_⟩
  push_cast [Nat.cast_le]
  apply Finset.card_le_card
  intro p hp
  simp only [Set.mem_toFinset, Set.mem_inter_iff] at hp
  rw [Finset.mem_filter]
  refine ⟨hp.1, ?_⟩
  simp only [Sensitivity.Q.adjacent, Set.mem_ofPred_eq] at hp
  obtain ⟨i, hne, huniq⟩ := hp.2
  have e_apply (x : Sensitivity.Q m.succ) (j : Fin m.succ) : e x j = x j := rfl
  exact ⟨i, funext fun j => by
    by_cases hji : j = i
    · subst hji; simp only [flipBit_apply_same, e_apply]
      revert hne; cases q j <;> cases p j <;> simp
    · rw [flipBit_apply_ne _ _ hji, e_apply]
      have hne' : ¬¬ q j = p j := mt (huniq j) hji
      exact (Classical.not_not.mp hne').symm⟩

end LeanPoolSensitivity
