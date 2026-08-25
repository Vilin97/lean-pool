/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos132ThreeChain.FivePoints
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod

/-!
# From five labelled points to five-element sets

`no_five_chain_points` is stated for five named points with a named shortest edge.  This file
removes both conveniences: `no_five_chain_finset` takes any five-element set of plane points
whose pairwise squared distances lie in a geometric 3-chain, selects a shortest edge inside it,
and rescales the chain so that the shortest edge has squared length exactly the new base.
-/

namespace Erdos132ThreeChain

open Finset

theorem isChainValue_of_le {a c x : ℝ} (ha : 0 < a) {j₀ j : ℕ} (hc : c = a * 3 ^ j₀)
    (hx : x = a * 3 ^ j) (hle : c ≤ x) : IsChainValue c x := by
  have hj : j₀ ≤ j := by
    by_contra hlt
    have hlt' : j < j₀ := by omega
    have : (3 : ℝ) ^ j < 3 ^ j₀ := by
      exact pow_lt_pow_right₀ (by norm_num) hlt'
    rw [hc, hx] at hle
    nlinarith
  refine ⟨j - j₀, ?_⟩
  rw [hx, hc, mul_assoc, ← pow_add]
  congr 2
  omega

/-- Inside a set whose pairwise squared distances lie in a geometric 3-chain, a shortest edge
rescales the chain: every squared distance is the shortest one times a power of three. -/
theorem exists_min_edge {S : Finset Point} {a : ℝ} (ha : 0 < a) (hcard : 2 ≤ S.card)
    (hch : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → ∃ j : ℕ, sqDist p q = a * 3 ^ j) :
    ∃ A ∈ S, ∃ B ∈ S, A ≠ B ∧
      ∀ p ∈ S, ∀ q ∈ S, p ≠ q → IsChainValue (sqDist A B) (sqDist p q) := by
  classical
  set U : Finset (Point × Point) := (S ×ˢ S).filter fun x => x.1 ≠ x.2 with hU
  have hUne : U.Nonempty := by
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
    exact ⟨(u, v), by simp [hU, Finset.mem_filter, Finset.mem_product, hu, hv, huv]⟩
  obtain ⟨⟨A, B⟩, hABmem, hmin⟩ := Finset.exists_min_image U (fun x => sqDist x.1 x.2) hUne
  have hAB : A ∈ S ∧ B ∈ S ∧ A ≠ B := by
    have hf := Finset.mem_filter.mp hABmem
    exact ⟨(Finset.mem_product.mp hf.1).1, (Finset.mem_product.mp hf.1).2, hf.2⟩
  obtain ⟨j₀, hj₀⟩ := hch A hAB.1 B hAB.2.1 hAB.2.2
  refine ⟨A, hAB.1, B, hAB.2.1, hAB.2.2, fun p hp q hq hpq => ?_⟩
  obtain ⟨j, hj⟩ := hch p hp q hq hpq
  exact isChainValue_of_le ha hj₀ hj
    (hmin (p, q) (by simp [hU, Finset.mem_filter, Finset.mem_product, hp, hq, hpq]))

/-- **The chain-quadruple theorem.**  No planar chain quadruple spans two chain steps: if the
six pairwise squared distances of a four-element set of plane points lie in a geometric 3-chain
with positive base, then they all lie in a single adjacent pair `{r, 3 * r}` of that chain, and
`r` is itself a member of the chain. -/
theorem four_chain_adjacent {S : Finset Point} {a : ℝ} (ha : 0 < a) (hcard : S.card = 4)
    (hch : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → ∃ j : ℕ, sqDist p q = a * 3 ^ j) :
    ∃ r : ℝ, 0 < r ∧ (∃ j : ℕ, r = a * 3 ^ j) ∧
      ∀ p ∈ S, ∀ q ∈ S, p ≠ q → sqDist p q = r ∨ sqDist p q = 3 * r := by
  classical
  obtain ⟨A, hA, B, hB, hAB, hchain⟩ := exists_min_edge ha (by omega) hch
  obtain ⟨jbase, hjbase⟩ := hch A hA B hB hAB
  set c : ℝ := sqDist A B with hcdef
  have hc : 0 < c := sqDist_pos hAB
  have hsub : ({A, B} : Finset Point) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hA
    · exact hB
  have hrest : (S \ {A, B}).card = 2 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, hcard,
      Finset.card_insert_of_notMem (by simpa using hAB), Finset.card_singleton]
  obtain ⟨C, D, hCD, hset⟩ := Finset.card_eq_two.mp hrest
  have hmemC : C ∈ S \ {A, B} := by rw [hset]; simp
  have hmemD : D ∈ S \ {A, B} := by rw [hset]; simp
  have hCS : C ∈ S := (Finset.mem_sdiff.mp hmemC).1
  have hDS : D ∈ S := (Finset.mem_sdiff.mp hmemD).1
  have hCA : A ≠ C := fun h => (Finset.mem_sdiff.mp hmemC).2 (by rw [← h]; simp)
  have hCB : B ≠ C := fun h => (Finset.mem_sdiff.mp hmemC).2 (by rw [← h]; simp)
  have hDA : A ≠ D := fun h => (Finset.mem_sdiff.mp hmemD).2 (by rw [← h]; simp)
  have hDB : B ≠ D := fun h => (Finset.mem_sdiff.mp hmemD).2 (by rw [← h]; simp)
  have quad := pair_classification hc rfl (hchain A hA C hCS hCA)
    (hchain B hB C hCS hCB) (hchain A hA D hDS hDA) (hchain B hB D hDS hDB)
    (hchain C hCS D hDS hCD)
  have posC := quad.posC
  have posD := quad.posD
  have hmem : ∀ p ∈ S, p = A ∨ p = B ∨ p = C ∨ p = D := by
    intro p hp
    by_cases hpm : p ∈ ({A, B} : Finset Point)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpm; tauto
    · have : p ∈ S \ {A, B} := Finset.mem_sdiff.mpr ⟨hp, hpm⟩
      rw [hset] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      tauto
  refine ⟨c, hc, ⟨jbase, hjbase⟩, fun p hp q hq hpq => ?_⟩
  have eAB : sqDist A B = c ∨ sqDist A B = 3 * c := Or.inl rfl
  have eBA : sqDist B A = c ∨ sqDist B A = 3 * c := by rw [sqDist_comm B A]; exact eAB
  have eAC : sqDist A C = c ∨ sqDist A C = 3 * c := posC.fromLeft
  have eCA : sqDist C A = c ∨ sqDist C A = 3 * c := by rw [sqDist_comm C A]; exact eAC
  have eBC : sqDist B C = c ∨ sqDist B C = 3 * c := posC.fromRight
  have eCB : sqDist C B = c ∨ sqDist C B = 3 * c := by rw [sqDist_comm C B]; exact eBC
  have eAD : sqDist A D = c ∨ sqDist A D = 3 * c := posD.fromLeft
  have eDA : sqDist D A = c ∨ sqDist D A = 3 * c := by rw [sqDist_comm D A]; exact eAD
  have eBD : sqDist B D = c ∨ sqDist B D = 3 * c := posD.fromRight
  have eDB : sqDist D B = c ∨ sqDist D B = 3 * c := by rw [sqDist_comm D B]; exact eBD
  have eCD : sqDist C D = c ∨ sqDist C D = 3 * c := quad.distCD
  have eDC : sqDist D C = c ∨ sqDist D C = 3 * c := by rw [sqDist_comm D C]; exact eCD
  rcases hmem p hp with rfl | rfl | rfl | rfl <;> rcases hmem q hq with rfl | rfl | rfl | rfl <;>
    first
      | exact absurd rfl hpq
      | assumption

/-- **The five-point obstruction for five-element sets.**  No five-element set of plane points
has all ten of its pairwise squared distances inside a geometric 3-chain with positive base. -/
theorem no_five_chain_finset {S : Finset Point} {a : ℝ} (ha : 0 < a) (hcard : S.card = 5)
    (hch : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → ∃ j : ℕ, sqDist p q = a * 3 ^ j) : False := by
  classical
  obtain ⟨A, hA, B, hB, hAB, hchain⟩ := exists_min_edge ha (by omega) hch
  have hc : 0 < sqDist A B := sqDist_pos hAB
  have hsub : ({A, B} : Finset Point) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hA
    · exact hB
  have hrest : (S \ {A, B}).card = 3 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, hcard,
      Finset.card_insert_of_notMem (by simpa using hAB), Finset.card_singleton]
  obtain ⟨C, D, E, hCD, hCE, hDE, hset⟩ := Finset.card_eq_three.mp hrest
  have hmemC : C ∈ S \ {A, B} := by rw [hset]; simp
  have hmemD : D ∈ S \ {A, B} := by rw [hset]; simp
  have hmemE : E ∈ S \ {A, B} := by rw [hset]; simp
  have hCS : C ∈ S := (Finset.mem_sdiff.mp hmemC).1
  have hDS : D ∈ S := (Finset.mem_sdiff.mp hmemD).1
  have hES : E ∈ S := (Finset.mem_sdiff.mp hmemE).1
  have hCA : A ≠ C := fun h => (Finset.mem_sdiff.mp hmemC).2 (by rw [← h]; simp)
  have hCB : B ≠ C := fun h => (Finset.mem_sdiff.mp hmemC).2 (by rw [← h]; simp)
  have hDA : A ≠ D := fun h => (Finset.mem_sdiff.mp hmemD).2 (by rw [← h]; simp)
  have hDB : B ≠ D := fun h => (Finset.mem_sdiff.mp hmemD).2 (by rw [← h]; simp)
  have hEA : A ≠ E := fun h => (Finset.mem_sdiff.mp hmemE).2 (by rw [← h]; simp)
  have hEB : B ≠ E := fun h => (Finset.mem_sdiff.mp hmemE).2 (by rw [← h]; simp)
  exact no_five_chain_points hc rfl (hchain A hA C hCS hCA) (hchain A hA D hDS hDA)
    (hchain A hA E hES hEA) (hchain B hB C hCS hCB) (hchain B hB D hDS hDB)
    (hchain B hB E hES hEB) (hchain C hCS D hDS hCD) (hchain C hCS E hES hCE)
    (hchain D hDS E hES hDE)

end Erdos132ThreeChain
