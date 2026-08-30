/-
Copyright (c) 2026 Elan Roth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elan Roth
-/

import Mathlib.Data.ENat.Lattice
import Mathlib.Tactic.Cases
import LeanPool.UlmsTheorem.PGroups.UlmSubgroups

/-!
# Reducedness and height theory

This file contains the reducedness predicate used in the project and the
basic finite `p`-height calculus.
-/

namespace UlmsTheorem

variable (p : ℕ)

/-! ### Primary, reduced, and separable groups -/

/-- `G` is `p`-primary if every element is killed by some power of `p`.

This hypothesis is logically independent from reducedness.  In particular, torsion-free
groups such as `ℤ` must not enter Ulm's classification theorem merely because their
`p`-socle is trivial. -/
def IsPrimaryPGroup (G : Type*) [AddCommGroup G] : Prop :=
  ∀ x : G, ∃ n : ℕ, p ^ n • x = 0

/-- The `p`-Ulm filtration of `G` is reduced if it eventually reaches zero.

For the countable `p`-primary groups classified below, this is equivalent to saying that
`G` has no nontrivial divisible subgroup: the eventual stable Ulm subgroup is the maximal
divisible subgroup.  Crucially, this does *not* require `G_ω = 0`; reduced groups may
contain elements of infinite height and have arbitrary countable Ulm length. -/
def IsPReduced (G : Type*) [AddCommGroup G] : Prop :=
  ∃ α : Ordinal.{0}, ulmSubgroup p α (G := G) = ⊥

/-- A reduced abelian `p`-group: primary, with zero divisible part. -/
structure IsReducedPGroup (G : Type*) [AddCommGroup G] : Prop where
  primary : IsPrimaryPGroup p G
  reduced : IsPReduced p G

/-- `G` is `p`-separable if it has no nonzero element of infinite `p`-height.

This was formerly (and incorrectly) called `IsReducedPGroup`.  It is strictly stronger
than reducedness: it says `G_ω = 0`. -/
def IsPSeparable (G : Type*) [AddCommGroup G] : Prop :=
  ∀ x : G, (∀ n : ℕ, ∃ y : G, p ^ n • y = x) → x = 0

section ReducedLemmas

variable {G : Type*} [AddCommGroup G]

/-- `G` is `p`-separable iff `⋂_n p^n·G = 0`. -/
lemma isPSeparable_iff_iInf :
    IsPSeparable p G ↔ (⨅ n : ℕ, pPow p (G := G) n) = ⊥ := by
  constructor
  · intro hred
    ext x
    simp only [AddSubgroup.mem_iInf, AddSubgroup.mem_bot]
    exact ⟨fun h ↦ hred x (fun n ↦ (pPow_mem_iff p x n).mp (h n)),
      fun h n ↦ h ▸ (pPow p (G := G) n).zero_mem⟩
  · intro h x hx
    have hmem : x ∈ ⨅ n : ℕ, pPow p (G := G) n := by
      simp only [AddSubgroup.mem_iInf]
      intro n
      exact (pPow_mem_iff p x n).mpr (hx n)
    rw [h] at hmem
    exact AddSubgroup.mem_bot.mp hmem

end ReducedLemmas

/-! ### `p`-height -/

/-- The `p`-height of `x`: `⊤` if `x = 0`, otherwise the supremum of
the natural numbers `n` such that `x ∈ p^n·G`. -/
noncomputable def pHeight {G : Type*} [AddCommGroup G] (x : G) : ℕ∞ :=
  letI : Decidable (x = 0) := Classical.propDecidable _
  if x = 0 then ⊤ else sSup (WithTop.some '' {n : ℕ | ∃ y : G, p ^ n • y = x})

section HeightLemmas

variable {G : Type*} [AddCommGroup G]

@[simp] lemma pHeight_zero : pHeight p (0 : G) = ⊤ := by
  simp only [pHeight, ite_true]

lemma pHeight_ge_iff (x : G) (n : ℕ) :
    (n : ℕ∞) ≤ pHeight p x ↔ ∃ y : G, p ^ n • y = x := by
  by_cases hx : x = 0
  · subst hx
    simp only [pHeight_zero, le_top, true_iff]
    exact ⟨0, smul_zero _⟩
  · simp only [pHeight, ite_eq_right hx]
    constructor
    · intro h
      contrapose! h
      refine lt_of_le_of_lt (csSup_le (a := (↑(n - 1) : ℕ∞)) ?_ ?_) ?_
      · exact ⟨_, ⟨0, ⟨x, by simp +decide⟩, rfl⟩⟩
      · rintro _ ⟨m, ⟨y, hy⟩, rfl⟩
        exact WithTop.coe_le_coe.mpr (Nat.le_sub_one_of_lt (lt_of_not_ge fun hnm ↦
          h (p ^ (m - n) • y) <| by rw [← mul_smul, ← pow_add, Nat.add_sub_of_le hnm, hy]))
      · rcases n with _ | n
        · exact (h x (by simp)).elim
        · simp_all +decide only [add_tsub_cancel_right, Nat.cast_add, Nat.cast_one]
          exact WithTop.coe_lt_coe.mpr (Nat.lt_succ_self _)
    · intro ⟨y, hy⟩
      apply le_sSup
      exact ⟨n, ⟨y, hy⟩, rfl⟩

lemma pHeight_ge_iff_mem (x : G) (n : ℕ) :
    (n : ℕ∞) ≤ pHeight p x ↔ x ∈ pPow p n := by
  rw [pHeight_ge_iff, pPow_mem_iff]

lemma pHeight_add_ge (x y : G) (n : ℕ)
    (hx : (n : ℕ∞) ≤ pHeight p x) (hy : (n : ℕ∞) ≤ pHeight p y) :
    (n : ℕ∞) ≤ pHeight p (x + y) := by
  rw [pHeight_ge_iff] at *
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  exact ⟨a + b, by rw [smul_add, ha, hb]⟩

lemma pHeight_add_ge_min (x y : G) :
    min (pHeight p x) (pHeight p y) ≤ pHeight p (x + y) := by
  by_cases hxy : pHeight p x ≥ pHeight p y
  · have hxy_in_pnG : ∀ n : ℕ, (n : ℕ∞) ≤ pHeight p y → ∃ z : G, p ^ n • z = x + y := by
      intro n hn
      obtain ⟨zx, hzx⟩ := (pHeight_ge_iff p x n).1 (le_trans hn hxy)
      obtain ⟨zy, hzy⟩ := (pHeight_ge_iff p y n).1 hn
      exact ⟨zx + zy, by rw [smul_add, hzx, hzy]⟩
    contrapose! hxy_in_pnG with hxy_not_in_pnG
    rw [min_eq_right hxy] at hxy_not_in_pnG
    obtain ⟨n, hn₁, hn₂⟩ : ∃ n : ℕ, (n : ℕ∞) ≤ pHeight p y ∧ (n : ℕ∞) > pHeight p (x + y) := by
      obtain ⟨n, hn, hnlt⟩ := WithTop.lt_iff_exists_coe.mp hxy_not_in_pnG
      refine ⟨n + 1, ENat.natCast_add_one_le_iff.mpr hnlt, ?_⟩
      rw [hn]
      exact ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self n)
    exact ⟨n, hn₁,
      fun z hz ↦ (not_le.mpr hn₂) ((pHeight_ge_iff p (x + y) n).2 ⟨z, hz⟩)⟩
  · have h_subadd : ∀ n : ℕ, (n : ℕ∞) ≤ pHeight p x → (n : ℕ∞) ≤ pHeight p (x + y) := fun n hn ↦
      pHeight_add_ge p x y n hn (le_trans hn (le_of_not_ge hxy))
    cases h : pHeight p x <;> aesop

lemma pHeight_add_eq_min_of_ne (x y : G) (h : pHeight p x ≠ pHeight p y) :
    pHeight p (x + y) = min (pHeight p x) (pHeight p y) := by
  wlog hx_lt_hy : pHeight p x < pHeight p y generalizing x y
  · rw [add_comm, this y x h.symm (lt_of_le_of_ne (le_of_not_gt hx_lt_hy) h.symm)]
    exact min_comm _ _
  have hle : pHeight p (x + y) ≤ pHeight p x := by
    by_contra hlt
    push Not at hlt
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℕ∞) = pHeight p x :=
      WithTop.ne_top_iff_exists.mp (ne_top_of_lt hx_lt_hy)
    have hk_lt_y  : (k : ℕ∞) < pHeight p y       := by rw [hk]; exact hx_lt_hy
    have hk_lt_xy : (k : ℕ∞) < pHeight p (x + y) := by rw [hk]; exact hlt
    have succ_le : ∀ a : ℕ∞, (k : ℕ∞) < a → (↑(k + 1) : ℕ∞) ≤ a := fun a ha ↦ by
      rcases a with (_ | m)
      · exact le_top
      · exact WithTop.coe_le_coe.mpr (Nat.succ_le_of_lt (WithTop.coe_lt_coe.mp ha))
    obtain ⟨zy, hzy⟩ := (pHeight_ge_iff p y (k + 1)).mp (succ_le _ hk_lt_y)
    obtain ⟨zxy, hzxy⟩ := (pHeight_ge_iff p (x + y) (k + 1)).mp (succ_le _ hk_lt_xy)
    have hx_mem : (↑(k + 1) : ℕ∞) ≤ pHeight p x :=
      (pHeight_ge_iff p x (k + 1)).mpr
        ⟨zxy - zy, by rw [smul_sub, hzxy, hzy, add_sub_cancel_right]⟩
    rw [← hk] at hx_mem
    exact absurd (WithTop.coe_le_coe.mp hx_mem) (by omega)
  exact le_antisymm (le_min hle (le_trans hle hx_lt_hy.le)) (pHeight_add_ge_min p x y)

end HeightLemmas

end UlmsTheorem
