/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

import LeanPool.PoincareGeometry.BonnetMyers.Statement

/-!
# Finite reindexing lemmas

The coordinate calculations in the transport layer use four nested finite
sums.  These lemmas expose the two index permutations needed for the metric
compatibility cancellation without hiding a reindexing step in automation.
-/

noncomputable section

open scoped BigOperators

namespace BonnetMyersEntry

lemma sum_swap_first_third {n : ℕ}
    (F : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, ∑ l, ∑ k, F l j i k) =
      ∑ i, ∑ j, ∑ l, ∑ k, F i j l k := by
  let e : (Fin n × (Fin n × (Fin n × Fin n))) ≃
      (Fin n × (Fin n × (Fin n × Fin n))) :=
    { toFun := fun q ↦ (q.2.2.1, (q.2.1, (q.1, q.2.2.2)))
      invFun := fun q ↦ (q.2.2.1, (q.2.1, (q.1, q.2.2.2)))
      left_inv := by
        intro q
        rcases q with ⟨i, j, l, k⟩
        rfl
      right_inv := by
        intro q
        rcases q with ⟨i, j, l, k⟩
        rfl }
  let f : Fin n × (Fin n × (Fin n × Fin n)) → ℝ :=
    fun q ↦ F q.1 q.2.1 q.2.2.1 q.2.2.2
  have h := Equiv.sum_comp e f
  have expand (g : Fin n × (Fin n × (Fin n × Fin n)) → ℝ) :
      (∑ q, g q) = ∑ i, ∑ j, ∑ l, ∑ k, g (i, (j, (l, k))) := by
    calc
      (∑ q, g q) = ∑ i, ∑ r, g (i, r) := by
        simpa using (Fintype.sum_prod_type' (fun i r ↦ g (i, r)))
      _ = ∑ i, ∑ j, ∑ s, g (i, (j, s)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Fintype.sum_prod_type' (fun j s ↦ g (i, (j, s)))]
      _ = ∑ i, ∑ j, ∑ l, ∑ k, g (i, (j, (l, k))) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [Fintype.sum_prod_type' (fun l k ↦ g (i, (j, (l, k))))]
  have h' := h
  rw [expand (fun q ↦ f (e q)), expand f] at h'
  simpa [f, e] using h'

lemma sum_swap_second_third {n : ℕ}
    (F : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, ∑ l, ∑ k, F i l j k) =
      ∑ i, ∑ j, ∑ l, ∑ k, F i j l k := by
  let e : (Fin n × (Fin n × (Fin n × Fin n))) ≃
      (Fin n × (Fin n × (Fin n × Fin n))) :=
    { toFun := fun q ↦ (q.1, (q.2.2.1, (q.2.1, q.2.2.2)))
      invFun := fun q ↦ (q.1, (q.2.2.1, (q.2.1, q.2.2.2)))
      left_inv := by
        intro q
        rcases q with ⟨i, j, l, k⟩
        rfl
      right_inv := by
        intro q
        rcases q with ⟨i, j, l, k⟩
        rfl }
  let f : Fin n × (Fin n × (Fin n × Fin n)) → ℝ :=
    fun q ↦ F q.1 q.2.1 q.2.2.1 q.2.2.2
  have h := Equiv.sum_comp e f
  have expand (g : Fin n × (Fin n × (Fin n × Fin n)) → ℝ) :
      (∑ q, g q) = ∑ i, ∑ j, ∑ l, ∑ k, g (i, (j, (l, k))) := by
    calc
      (∑ q, g q) = ∑ i, ∑ r, g (i, r) := by
        simpa using (Fintype.sum_prod_type' (fun i r ↦ g (i, r)))
      _ = ∑ i, ∑ j, ∑ s, g (i, (j, s)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Fintype.sum_prod_type' (fun j s ↦ g (i, (j, s)))]
      _ = ∑ i, ∑ j, ∑ l, ∑ k, g (i, (j, (l, k))) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [Fintype.sum_prod_type' (fun l k ↦ g (i, (j, (l, k))))]
  have h' := h
  rw [expand (fun q ↦ f (e q)), expand f] at h'
  simpa [f, e] using h'

end BonnetMyersEntry
