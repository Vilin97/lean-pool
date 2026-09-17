/-
Copyright (c) 2026 Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao
-/
import LeanPool.LanguageGeneration.FiniteWitness.Width.Anchored
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Tactic.Push

/-!
# Counting lower bounds for anchored witness assignments
-/

namespace GenLimit.FiniteWitness.Anchored

theorem anchor_cover {k q : ℕ} {T : Set Point → Finset Point}
    (hT : Valid (family k) T) (hb : ∀ L ∈ family k, (T L).card ≤ q) :
    ∃ D : Set ℕ, ∃ R : Fin k → Finset (Fin k),
      (∀ j, (R j).card ≤ q) ∧
      ∀ i j : Fin k, Sum.inl j.val ∈ T (leftTarget i D) ∨ i ∈ R j := by
  classical
  let E : ℕ → Set ℕ := fun n => ↑(Finset.range n)
  let pat : ℕ → (Fin k → Finset (Fin k)) :=
    fun n j => rightAnchors k (T (rightTarget j (E n)))
  obtain ⟨R, hR⟩ := Finite.exists_infinite_fiber pat
  have hI : {n | pat n = R}.Infinite := Set.infinite_coe_iff.mp hR
  let e := hI.natEmbedding {n | pat n = R}
  let f : ℕ → ℕ := fun n => (e n).val
  have hfinj : Function.Injective f := Subtype.val_injective.comp e.injective
  have hpat (n j) : rightAnchors k (T (rightTarget j (E (f n)))) = R j :=
    congrFun (e n).property j
  have hRb (j) : (R j).card ≤ q := by
    rw [← hpat 0 j]
    exact (card_rightAnchors_le _ _).trans (hb _ (right_mem_family _ _))
  let U : ℕ → Finset ℕ := fun n => Finset.univ.biUnion
    (fun j : Fin k => rightTail k (T (rightTarget j (E (f n)))))
  have hUb (n) : (U n).card ≤ k * q := by
    have h := Finset.card_biUnion_le_card_mul (Finset.univ : Finset (Fin k))
      (fun j => rightTail k (T (rightTarget j (E (f n))))) q
      (fun j _ => (card_rightTail_le _ _).trans (hb _ (right_mem_family _ _)))
    simpa [U] using h
  obtain ⟨D, hcap, havoid⟩ := bounded_capture_indexed (k * q) U hUb
    (fun p : Fin k × Finset Point => leftCore T p.1 p.2)
  refine ⟨D, R, hRb, ?_⟩
  intro i j
  by_contra hn
  push Not at hn
  obtain ⟨hja, hir⟩ := hn
  let L := leftTarget i D
  let b := (T L).sup (Sum.elim id id)
  obtain ⟨v, ⟨n, hncap, rfl⟩, hv⟩ := (hcap.image hfinj.injOn).exists_gt b
  let K := rightTarget j (E (f n))
  have hLK : (↑(T L) : Set Point) ⊆ K := by
    rintro (m | m) hm
    · have hmb : m ≤ b := Finset.le_sup (f := Sum.elim id id) hm
      by_cases hmk : m < k
      · have hne : m ≠ j.val := by
          intro he
          subst m
          exact hja hm
        simpa [K, hmk] using hne
      · have hlt : m - k < f n := by omega
        simpa [K, hmk, E] using hlt
    · trivial
  have hKL : (↑(T K) : Set Point) ⊆ L := by
    rintro (m | m) hm
    · trivial
    · by_cases hmk : m < k
      · have hne : m ≠ i.val := by
          intro he
          subst m
          apply hir
          rw [← hpat n j]
          exact (mem_rightAnchors _ i).mpr hm
        simpa [L, hmk] using hne
      · have htail : m - k ∈ rightTail k (T K) := by
          apply (mem_rightTail k (T K) _).mpr
          simpa [Nat.add_sub_of_le (by omega : k ≤ m)] using hm
        have hmU : m - k ∈ U n := Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, htail⟩
        have hmD := hncap hmU
        simpa [L, hmk] using hmD
  let S := T L ∪ T K
  have hLa : L ∈ active (family k) T S := by
    refine ⟨left_mem_family i D, Finset.subset_union_left, ?_⟩
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hT.1 L (left_mem_family i D) hx
    · exact hKL hx
  have hKa : K ∈ active (family k) T S := by
    refine ⟨right_mem_family j _, Finset.subset_union_right, ?_⟩
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hLK hx
    · exact hT.1 K (right_mem_family j _) hx
  have hcore : (leftCore T i S).Infinite :=
    leftCore_infinite_of_active_right hT ⟨L, hLa⟩ i j (Finset.finite_toSet _) hKa
  exact havoid (i, S) hcore (fun x hx => hx D hLa)

theorem lower_incidence {k q : ℕ} {T : Set Point → Finset Point}
    (hT : Valid (family k) T) (hb : ∀ L ∈ family k, (T L).card ≤ q) :
    k * k ≤ 2 * k * q := by
  classical
  obtain ⟨D, R, hRb, hcover⟩ := anchor_cover hT hb
  let A : Fin k → Finset (Fin k) := fun i => leftAnchors k (T (leftTarget i D))
  have hAb (i) : (A i).card ≤ q :=
    (card_leftAnchors_le _ _).trans (hb _ (left_mem_family _ _))
  let rows : Finset (Fin k × Fin k) := Finset.univ.biUnion (fun i => {i} ×ˢ A i)
  let cols : Finset (Fin k × Fin k) := Finset.univ.biUnion (fun j => R j ×ˢ {j})
  have hsub : (Finset.univ : Finset (Fin k × Fin k)) ⊆ rows ∪ cols := by
    rintro ⟨i, j⟩ _
    rcases hcover i j with h | h
    · apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      exact ⟨i, Finset.mem_univ _, by simpa [A] using h⟩
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      exact ⟨j, Finset.mem_univ _, by simpa using h⟩
  have hrows : rows.card ≤ k * q := by
    have h := Finset.card_biUnion_le_card_mul (Finset.univ : Finset (Fin k))
      (fun i => {i} ×ˢ A i) q (fun i _ => by simpa using hAb i)
    simpa [rows] using h
  have hcols : cols.card ≤ k * q := by
    have h := Finset.card_biUnion_le_card_mul (Finset.univ : Finset (Fin k))
      (fun j => R j ×ˢ {j}) q (fun j _ => by simpa using hRb j)
    simpa [cols] using h
  have hcard : k * k ≤ (rows ∪ cols).card := by simpa using Finset.card_le_card hsub
  have hu := Finset.card_union_le rows cols
  calc
    k * k ≤ rows.card + cols.card := hcard.trans hu
    _ ≤ k * q + k * q := Nat.add_le_add hrows hcols
    _ = 2 * k * q := by rw [Nat.two_mul, Nat.add_mul]

theorem lower_bound {k q : ℕ} (h : HasBoundedWitnesses (family k) q) : (k + 1) / 2 ≤ q := by
  obtain ⟨T, hT, hb⟩ := h
  have hi := lower_incidence hT hb
  by_cases hk : k = 0
  · simp [hk]
  · have hkq : k ≤ 2 * q := Nat.le_of_mul_le_mul_left
      (by simpa only [Nat.mul_left_comm, Nat.mul_assoc] using hi) (Nat.pos_of_ne_zero hk)
    omega

end GenLimit.FiniteWitness.Anchored
