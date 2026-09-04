/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.InsertionExpectation
import LeanPool.Feige.TwoPointInduction

/-!
# Splitting a finite product law at its last coordinate

These identities are the finite-sum/Tonelli layer used in the two-point
induction for Theorem 2.1.  Every high set on `Fin (n + 1)` is uniquely a
lifted old high set, with or without the last coordinate.
-/

open Finset

namespace Feige

theorem univ_eq_insert_last_lift_univ {n : ℕ} :
    (Finset.univ : Finset (Fin (n + 1))) =
      insert (Fin.last n) (liftChainState (Finset.univ : Finset (Fin n))) := by
  ext i
  by_cases hi : i = Fin.last n
  · simp [hi]
  · obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hi
    simp

/-- Product mass of a high set not containing the last coordinate. -/
theorem highSetMass_lift {n : ℕ}
    (p : Fin (n + 1) → ℝ) (S : Finset (Fin n)) :
    highSetMass p (liftChainState S) =
      (1 - p (Fin.last n)) *
        highSetMass (fun i ↦ p i.castSucc) S := by
  classical
  have hcomp :
      (Finset.univ : Finset (Fin (n + 1))) \ liftChainState S =
        insert (Fin.last n)
          (liftChainState ((Finset.univ : Finset (Fin n)) \ S)) := by
    ext i
    by_cases hi : i = Fin.last n
    · simp [hi]
    · obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hi
      simp
  unfold highSetMass
  rw [hcomp, Finset.prod_insert (last_not_mem_liftChainState _)]
  simp only [liftChainState, prod_map]
  change
    (∏ i ∈ S, p i.castSucc) *
        ((1 - p (Fin.last n)) *
          ∏ i ∈ (Finset.univ : Finset (Fin n)) \ S, (1 - p i.castSucc)) =
      (1 - p (Fin.last n)) *
        ((∏ i ∈ S, p i.castSucc) *
          ∏ i ∈ (Finset.univ : Finset (Fin n)) \ S, (1 - p i.castSucc))
  ring

/-- Product mass of the corresponding high set containing the last
coordinate. -/
theorem highSetMass_insert_last {n : ℕ}
    (p : Fin (n + 1) → ℝ) (S : Finset (Fin n)) :
    highSetMass p (insert (Fin.last n) (liftChainState S)) =
      p (Fin.last n) * highSetMass (fun i ↦ p i.castSucc) S := by
  classical
  have hcomp :
      (Finset.univ : Finset (Fin (n + 1))) \
          insert (Fin.last n) (liftChainState S) =
        liftChainState ((Finset.univ : Finset (Fin n)) \ S) := by
    ext i
    by_cases hi : i = Fin.last n
    · simp [hi]
    · obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hi
      simp
  unfold highSetMass
  rw [Finset.prod_insert (last_not_mem_liftChainState _), hcomp]
  simp only [liftChainState, prod_map]
  change
    (p (Fin.last n) * ∏ i ∈ S, p i.castSucc) *
        (∏ i ∈ (Finset.univ : Finset (Fin n)) \ S, (1 - p i.castSucc)) =
      p (Fin.last n) *
        ((∏ i ∈ S, p i.castSucc) *
          ∏ i ∈ (Finset.univ : Finset (Fin n)) \ S, (1 - p i.castSucc))
  ring

private theorem sum_powerset_lift {n : ℕ}
    (f : Finset (Fin (n + 1)) → ℝ) :
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        f (liftChainState S)) =
      ∑ U ∈ (liftChainState (Finset.univ : Finset (Fin n))).powerset,
        f U := by
  classical
  apply Finset.sum_bij (fun S hS ↦ liftChainState S)
  · intro S hS
    rw [Finset.mem_powerset] at hS ⊢
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
    simp
  · intro S₁ h₁ S₂ h₂ hEq
    simpa [liftChainState] using hEq
  · intro U hU
    rw [Finset.mem_powerset] at hU
    let S : Finset (Fin n) :=
      Finset.univ.filter fun i ↦ i.castSucc ∈ U
    have hS : S ∈ (Finset.univ : Finset (Fin n)).powerset := by
      simp [S]
    refine ⟨S, hS, ?_⟩
    ext i
    by_cases hi : i = Fin.last n
    · subst i
      have hnot : Fin.last n ∉ U := by
        intro hlast
        have := hU hlast
        exact last_not_mem_liftChainState _ this
      simp [hnot]
    · obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hi
      simp [S]
  · intro S hS
    rfl

/-- Reindexing all subsets of `Fin (n + 1)` by an old subset and a last
coordinate bit. -/
theorem sum_powerset_succ {n : ℕ}
    (f : Finset (Fin (n + 1)) → ℝ) :
    (∑ S ∈ (Finset.univ : Finset (Fin (n + 1))).powerset, f S) =
      ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
        (f (liftChainState T) +
          f (insert (Fin.last n) (liftChainState T))) := by
  classical
  let L := liftChainState (Finset.univ : Finset (Fin n))
  have huniv :
      (Finset.univ : Finset (Fin (n + 1))) = insert (Fin.last n) L :=
    univ_eq_insert_last_lift_univ
  have hlastL : Fin.last n ∉ L := last_not_mem_liftChainState _
  have hdis :
      Disjoint L.powerset (L.powerset.image (insert (Fin.last n))) := by
    rw [Finset.disjoint_left]
    intro S hSL hSI
    obtain ⟨T, hTL, rfl⟩ := Finset.mem_image.mp hSI
    have hlastInsert : Fin.last n ∈ insert (Fin.last n) T := by simp
    exact hlastL ((Finset.mem_powerset.mp hSL) hlastInsert)
  rw [huniv, Finset.powerset_insert, Finset.sum_union hdis]
  have himage :
      (∑ S ∈ L.powerset.image (insert (Fin.last n)), f S) =
        ∑ S ∈ L.powerset, f (insert (Fin.last n) S) := by
    rw [Finset.sum_image]
    intro A hA B hB hEq
    have hlastA : Fin.last n ∉ A := by
      intro hlast
      exact hlastL ((Finset.mem_powerset.mp hA) hlast)
    have hlastB : Fin.last n ∉ B := by
      intro hlast
      exact hlastL ((Finset.mem_powerset.mp hB) hlast)
    have herase := congrArg (fun S ↦ S.erase (Fin.last n)) hEq
    simpa [hlastA, hlastB] using herase
  rw [himage, ← sum_powerset_lift f,
    ← sum_powerset_lift (fun S ↦ f (insert (Fin.last n) S))]
  rw [Finset.sum_add_distrib]

/-- Product expectation recursion at the last coordinate. -/
theorem productHighSetExpectation_succ {n : ℕ}
    (p : Fin (n + 1) → ℝ) (g : Finset (Fin (n + 1)) → ℝ) :
    productHighSetExpectation p g =
      productHighSetExpectation (fun i ↦ p i.castSucc)
        (revealedLastPayoff (p (Fin.last n)) g) := by
  classical
  unfold productHighSetExpectation revealedLastPayoff
  rw [sum_powerset_succ
    (fun S ↦ highSetMass p S * g S)]
  apply Finset.sum_congr rfl
  intro T hT
  rw [highSetMass_lift, highSetMass_insert_last]
  ring

end Feige
