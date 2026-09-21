/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.Basic

open scoped BigOperators

namespace EGZ.HasBoundedRepresentative

theorem zero (p K : ℕ) : HasBoundedRepresentative p K 0 := ⟨0, by simp, by simp⟩

theorem mono {p K L : ℕ} {a : ZMod p} (ha : HasBoundedRepresentative p K a)
    (hKL : K ≤ L) : HasBoundedRepresentative p L a := by
  obtain ⟨z, hz, rfl⟩ := ha
  exact ⟨z, hz.trans hKL, rfl⟩

theorem neg {p K : ℕ} {a : ZMod p} (ha : HasBoundedRepresentative p K a) :
    HasBoundedRepresentative p K (-a) := by
  obtain ⟨z, hz, rfl⟩ := ha
  exact ⟨-z, by simpa using hz, by simp⟩

theorem add {p K L : ℕ} {a b : ZMod p}
    (ha : HasBoundedRepresentative p K a) (hb : HasBoundedRepresentative p L b) :
    HasBoundedRepresentative p (K + L) (a + b) := by
  obtain ⟨z, hz, rfl⟩ := ha
  obtain ⟨w, hw, rfl⟩ := hb
  exact ⟨z + w, (Int.natAbs_add_le z w).trans (Nat.add_le_add hz hw), by simp⟩

theorem sub {p K L : ℕ} {a b : ZMod p}
    (ha : HasBoundedRepresentative p K a) (hb : HasBoundedRepresentative p L b) :
    HasBoundedRepresentative p (K + L) (a - b) := by
  simpa only [sub_eq_add_neg] using ha.add hb.neg

theorem int_mul {p K : ℕ} {a : ZMod p} (ha : HasBoundedRepresentative p K a) (n : ℤ) :
    HasBoundedRepresentative p (n.natAbs * K) ((n : ZMod p) * a) := by
  obtain ⟨z, hz, rfl⟩ := ha
  exact ⟨n * z, by rw [Int.natAbs_mul]; exact Nat.mul_le_mul_left _ hz, by simp⟩

theorem sum {p : ℕ} {I : Type*} (s : Finset I) (K : I → ℕ) (a : I → ZMod p)
    (h : ∀ i ∈ s, HasBoundedRepresentative p (K i) (a i)) :
    HasBoundedRepresentative p (∑ i ∈ s, K i) (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero p 0
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i (by simp)).add (ih (fun j hj ↦ h j (by simp [hj])))

end EGZ.HasBoundedRepresentative
