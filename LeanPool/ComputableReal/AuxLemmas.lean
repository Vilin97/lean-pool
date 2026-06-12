/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Auxiliary lemmas

Small helper lemmas about `CauSeq` suprema/infima and about Cauchy sequences
converging to a real number, used in the construction of computable reals.
-/

theorem abs_ite_le [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] (x : α) :
    abs x = if 0 ≤ x then x else -x := by
  split_ifs <;> simp_all only [abs_eq_self, not_le, abs_eq_neg_self]
  next h =>
    exact LT.lt.le h

namespace CauSeq

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a b : CauSeq α abs}

theorem sup_equiv_of_equivs (ha : a ≈ c) (hb : b ≈ c) : a ⊔ b ≈ c := by
  intro n hn
  obtain ⟨i₁, hi₁⟩ := ha n hn
  obtain ⟨i₂, hi₂⟩ := hb n hn
  use max i₁ i₂
  intro j hj
  replace hi₁ := hi₁ j (Nat.max_le.mp hj).1
  replace hi₂ := hi₂ j (Nat.max_le.mp hj).2
  dsimp at hi₁ hi₂ ⊢
  rw [max_def]
  rw [abs_ite_le] at hi₁ hi₂ ⊢
  split_ifs at hi₁ hi₂ ⊢
  all_goals linarith

theorem equiv_sup_of_equivs (ha : c ≈ a) (hb : c ≈ b) : c ≈ a ⊔ b :=
  Setoid.symm (sup_equiv_of_equivs (Setoid.symm ha) (Setoid.symm hb))

theorem inf_equiv_of_equivs (ha : a ≈ c) (hb : b ≈ c) : a ⊓ b ≈ c := by
  --if we had a version of `neg_inf` for CauSeq this could be easily
  --reduced to `sup_equiv_of_equivs`.
  intro n hn
  obtain ⟨i₁, hi₁⟩ := ha n hn
  obtain ⟨i₂, hi₂⟩ := hb n hn
  use max i₁ i₂
  intro j hj
  replace hi₁ := hi₁ j (Nat.max_le.mp hj).1
  replace hi₂ := hi₂ j (Nat.max_le.mp hj).2
  dsimp at hi₁ hi₂ ⊢
  rw [min_def]
  rw [abs_ite_le] at hi₁ hi₂ ⊢
  split_ifs at hi₁ hi₂ ⊢
  all_goals linarith

/-- Dropping the first n terms of a Cauchy sequence to get a new sequence. -/
def drop (a : CauSeq α abs) (n : ℕ) : CauSeq α abs :=
  ⟨fun k ↦ a.val (n+k), fun _ hq ↦ Exists.casesOn (cauchy₂ a hq)
    fun i hi ↦ ⟨i,
      fun _ hj ↦ hi _ (le_add_of_le_right hj) _ (Nat.le_add_left i n)⟩⟩

/-- Dropping elements from a Cauchy sequence gives an equivalent one. -/
theorem drop_equiv_self (a : CauSeq α abs) (n : ℕ) : a.drop n ≈ a :=
  fun _ hq ↦ Exists.casesOn (cauchy₂ a hq)
    fun i hi ↦ ⟨i, fun _ hj ↦ hi _ (le_add_of_le_right hj) _ hj⟩

end CauSeq

namespace Real

/-- Every real number has some Caucy sequence converging to it. -/
theorem exists_CauSeq (x : ℝ) : ∃ s, Real.mk s = x :=
  let ⟨y,hy⟩ := Quot.exists_rep x.cauchy
  ⟨y, by rwa [Real.mk, CauSeq.Completion.mk, Quotient.mk'', Real.ofCauchy.injEq]⟩

end Real

theorem cauchy_real_mk (x : CauSeq ℚ abs) : ∀ ε > 0, ∃ i, ∀ j ≥ i, |x j - Real.mk x| < ε := by
  intro ε hε
  obtain ⟨q, hq, hq'⟩ := exists_rat_btwn hε
  obtain ⟨i, hi⟩ := x.2.cauchy₂ (by simpa using hq)
  simp_rw [abs_sub_comm]
  refine ⟨i, fun j hj ↦ lt_of_le_of_lt (Real.mk_near_of_forall_near ⟨i, fun k hk ↦ ?_⟩) hq'⟩
  exact_mod_cast (hi k hk j hj).le

--end silly lemmas
--================
