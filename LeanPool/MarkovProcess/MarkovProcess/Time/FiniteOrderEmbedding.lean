/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.Fin.Basic


/-!
# Factoring finite order embeddings through one deletion

This file records the elementary finite-order factorization obtained by deleting a point outside
the range of an order embedding. It is ordinary combinatorial infrastructure and makes no
probability-law or stochastic-process claim.
-/

@[expose] public section

namespace MarkovProcess

/-- An order embedding `Fin m ↪ Fin (n + 1)` with `m ≤ n` factors through deletion of a
single point. -/
theorem exists_factor_succAboveOrderEmb {m n : ℕ} (e : Fin m ↪o Fin (n + 1)) (h : m ≤ n) :
    ∃ (p : Fin (n + 1)) (d : Fin m ↪o Fin n), d.trans (Fin.succAboveOrderEmb p) = e := by
  classical
  have hns : ¬ Function.Surjective e := by
    intro he
    have hcard := Fintype.card_le_of_surjective e he
    simp only [Fintype.card_fin] at hcard
    exact (Nat.not_succ_le_self n) (hcard.trans h)
  rw [Function.Surjective] at hns
  push Not at hns
  obtain ⟨p, hp⟩ := hns
  by_cases plast : p = Fin.last n
  · have hlast : ∀ i, e i ≠ Fin.last n := by
      intro i
      simpa only [plast] using hp i
    let d : Fin m ↪o Fin n :=
      OrderEmbedding.ofStrictMono
        (fun i ↦ (e i).castPred (hlast i))
        (Fin.strictMono_castPred_comp hlast e.strictMono)
    refine ⟨p, d, ?_⟩
    apply DFunLike.ext _ _
    intro i
    change Fin.succAbove p ((e i).castPred (hlast i)) = e i
    rw [plast, Fin.succAbove_last_apply, Fin.castSucc_castPred]
  · let q : Fin n := p.castPred plast
    have hqp : q.castSucc = p := Fin.castSucc_castPred p plast
    have havoid : ∀ i, e i ≠ q.castSucc := by
      intro i
      rw [hqp]
      exact hp i
    have hmono : StrictMono (fun i ↦ q.predAbove (e i)) := by
      intro i j hij
      rw [← (Fin.succAboveOrderEmb p).lt_iff_lt]
      simpa only [Fin.succAboveOrderEmb_apply, ← hqp,
        Fin.succAbove_predAbove (havoid i), Fin.succAbove_predAbove (havoid j)] using
        e.strictMono hij
    let d : Fin m ↪o Fin n :=
      OrderEmbedding.ofStrictMono (fun i ↦ q.predAbove (e i)) hmono
    refine ⟨p, d, ?_⟩
    apply DFunLike.ext _ _
    intro i
    change Fin.succAbove p (q.predAbove (e i)) = e i
    rw [← hqp, Fin.succAbove_predAbove (havoid i)]

end MarkovProcess
