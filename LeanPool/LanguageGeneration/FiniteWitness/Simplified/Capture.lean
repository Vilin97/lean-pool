/-
Copyright (c) 2026 Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao
-/
import LeanPool.LanguageGeneration.FiniteWitness.Width.Foundation
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Choose

/-! Direct diagonal bounded capture, without a sunflower extraction. -/
namespace GenLimit.FiniteWitness.Simplified
variable {α : Type*}

private theorem omitted_infinitely (d : ℕ) (U : ℕ → Finset α)
    (hU : ∀ n, (U n).card ≤ d) {I : Set ℕ} (hI : I.Infinite)
    {C : Set α} (hC : C.Infinite) (B : Finset α) :
    ∃ x ∈ C, x ∉ B ∧ {n | n ∈ I ∧ x ∉ U n}.Infinite := by
  classical
  obtain ⟨V, hVC, hcard⟩ := (hC.sdiff B.finite_toSet).exists_subset_card_eq (d + 1)
  by_contra hn
  have hfin : ∀ x : {x // x ∈ V}, {n | n ∈ I ∧ x.val ∉ U n}.Finite := by
    intro x
    have hx := hVC x.property
    by_contra hh
    exact hn ⟨x.val, hx.1, hx.2, hh⟩
  let bad := V.attach.biUnion (fun x => (hfin x).toFinset)
  obtain ⟨n, hnI, hnbad⟩ := hI.exists_notMem_finset bad
  have hvu : V ⊆ U n := by
    intro x hx
    by_contra hxU
    apply hnbad
    exact Finset.mem_biUnion.mpr ⟨⟨x, hx⟩, Finset.mem_attach _ _,
      (hfin ⟨x, hx⟩).mem_toFinset.mpr ⟨hnI, hxU⟩⟩
  have hc := Finset.card_le_card hvu
  have hu := hU n
  omega

private structure DiagonalState (U : ℕ → Finset α) where
  indices : Finset ℕ
  forbidden : Finset α
  pool : Set ℕ
  infinite_pool : pool.Infinite
  safe : ∀ i ∈ indices, ∀ x ∈ forbidden, x ∉ U i
  pool_safe : ∀ i ∈ pool, ∀ x ∈ forbidden, x ∉ U i

private theorem diagonal_step (d : ℕ) (U : ℕ → Finset α)
    (hU : ∀ n, (U n).card ≤ d) (C : ℕ → Set α)
    (m : ℕ) (s : DiagonalState U) :
    ∃ t : DiagonalState U, s.indices ⊆ t.indices ∧ s.forbidden ⊆ t.forbidden ∧
      (∃ i ∈ t.indices, m < i) ∧
      ((C m).Infinite → ∃ x ∈ C m, x ∈ t.forbidden) := by
  classical
  by_cases hm : (C m).Infinite
  · obtain ⟨x, hxC, hxB, hpool⟩ := omitted_infinitely d U hU s.infinite_pool hm
      (s.indices.biUnion U)
    obtain ⟨i, hi, hmi⟩ := hpool.exists_gt m
    let t : DiagonalState U := {
      indices := insert i s.indices
      forbidden := insert x s.forbidden
      pool := {n | n ∈ s.pool ∧ x ∉ U n}
      infinite_pool := hpool
      safe := by
        intro j hj y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · rcases Finset.mem_insert.mp hj with rfl | hj
          · exact hi.2
          · intro hxj
            exact hxB (Finset.mem_biUnion.mpr ⟨j, hj, hxj⟩)
        · rcases Finset.mem_insert.mp hj with rfl | hj
          · exact s.pool_safe _ hi.1 y hy
          · exact s.safe j hj y hy
      pool_safe := by
        intro j hj y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hj.2
        · exact s.pool_safe j hj.1 y hy }
    exact ⟨t, Finset.subset_insert _ _, Finset.subset_insert _ _,
      ⟨i, Finset.mem_insert_self _ _, hmi⟩,
      fun _ => ⟨x, hxC, Finset.mem_insert_self _ _⟩⟩
  · obtain ⟨i, hi, hmi⟩ := s.infinite_pool.exists_gt m
    let t : DiagonalState U := { s with
      indices := insert i s.indices
      safe := by
        intro j hj x hx
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact s.pool_safe _ hi x hx
        · exact s.safe j hj x hx }
    exact ⟨t, Finset.subset_insert _ _, (fun _ h => h),
      ⟨i, Finset.mem_insert_self _ _, hmi⟩, fun h => (hm h).elim⟩

/-- Exact bounded-capture statement, proved by direct diagonal selection. -/
theorem bounded_capture (d : ℕ) (U : ℕ → Finset α)
    (hU : ∀ n, (U n).card ≤ d) (C : ℕ → Set α) :
    ∃ D : Set α, {n | (↑(U n) : Set α) ⊆ D}.Infinite ∧
      ∀ m, (C m).Infinite → ¬ C m ⊆ D := by
  classical
  choose next hi hf hl hc using diagonal_step d U hU C
  let start : DiagonalState U := ⟨∅, ∅, Set.univ, Set.infinite_univ, by simp, by simp⟩
  let state : ℕ → DiagonalState U := Nat.rec start (fun n s => next n s)
  have hI : Monotone (fun n => (state n).indices) :=
    monotone_nat_of_le_succ (fun n => hi n (state n))
  have hF : Monotone (fun n => (state n).forbidden) :=
    monotone_nat_of_le_succ (fun n => hf n (state n))
  let D : Set α := {x | ∃ n, ∃ i ∈ (state n).indices, x ∈ U i}
  have hcap (n i) (hi : i ∈ (state n).indices) : (↑(U i) : Set α) ⊆ D :=
    fun x hx => ⟨n, i, hi, hx⟩
  refine ⟨D, ?_, ?_⟩
  · intro hfinite
    let N := hfinite.toFinset.sup id
    obtain ⟨i, himem, hNi⟩ := hl N (state N)
    have hmem : i ∈ hfinite.toFinset := hfinite.mem_toFinset.mpr (hcap (N + 1) i himem)
    have hle : i ≤ N := Finset.le_sup (f := id) hmem
    omega
  · intro m hm hsub
    obtain ⟨x, hxC, hxF⟩ := hc m (state m) hm
    obtain ⟨n, i, hiI, hxi⟩ := hsub hxC
    exact (state (max n (m + 1))).safe i
      (hI (le_max_left _ _) hiI) x (hF (le_max_right _ _) hxF) hxi

theorem bounded_capture_indexed {ι : Type*} [Countable ι]
    (d : ℕ) (U : ℕ → Finset α) (hU : ∀ n, (U n).card ≤ d) (C : ι → Set α) :
    ∃ D : Set α, {n | (↑(U n) : Set α) ⊆ D}.Infinite ∧
      ∀ i, (C i).Infinite → ¬ C i ⊆ D := by
  classical
  let : Encodable ι := Encodable.ofCountable ι
  let C' : ℕ → Set α := fun n => ((Encodable.decode (α := ι) n).map C).getD ∅
  obtain ⟨D, hD, hC⟩ := bounded_capture d U hU C'
  refine ⟨D, hD, ?_⟩
  intro i
  simpa [C'] using hC (Encodable.encode i)

end GenLimit.FiniteWitness.Simplified
