/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.MixedPartition

/-!
# The standard orthosymplectic super vector space

The concrete model of §5.1 of the accompanying paper: the super
vector space with even part `Fin k → ℂ` and odd part
`Fin (2ℓ) → ℂ`, carrying the pinned Regts–Sevenster form —
orthonormal on the even part, and on the odd part the
antisymmetric form with
`b (f m) (f (m + ℓ)) = 1 = −b (f (m + ℓ)) (f m)`.  The dual
vectors `g i` and the partner index calculus reuse `oddPartner`
and `oddPartnerSign` from the Definition 5 machinery, so the two
sides of the Contraction–Expansion Lemma speak the same language.

The odd basis is named as in Regts–Sevenster, `f i` and `g i`;
the accompanying paper writes `ξ i` and `η i` for the same
vectors, `f` being reserved there for the graph parameter.
-/

namespace RS

open scoped BigOperators

/-- The standard super vector space with even dimension `k` and
odd dimension `2ℓ`. -/
noncomputable def stdSuperPair (k ℓ : ℕ) : SuperVect where
  even := Fin k → ℂ
  odd := Fin (2 * ℓ) → ℂ

/-- The standard even basis vectors `e i`. -/
noncomputable def stdE (k : ℕ) (i : Fin k) : Fin k → ℂ :=
  Pi.single i 1

/-- The standard odd basis vectors `f i`. -/
noncomputable def stdF (ℓ : ℕ) (i : Fin (2 * ℓ)) : Fin (2 * ℓ) → ℂ :=
  Pi.single i 1

/-- The even part of the standard form: the orthonormal pairing. -/
noncomputable def stdFormEven (k : ℕ) (x y : Fin k → ℂ) : ℂ :=
  ∑ i, x i * y i

/-- The odd part of the standard form: the antisymmetric pairing
with `b (f m) (f (m + ℓ)) = 1` for `m ≤ ℓ` and all other basis
values forced by antisymmetry. -/
noncomputable def stdFormOdd (ℓ : ℕ) (x y : Fin (2 * ℓ) → ℂ) : ℂ :=
  ∑ i, -(oddPartnerSign ℓ i : ℂ) * x i * y (oddPartner ℓ i)

/-- The Regts–Sevenster dual odd vectors: `g i = −f (i + ℓ)` for
`i < ℓ` and `g i = f (i − ℓ)` otherwise. -/
noncomputable def stdG (ℓ : ℕ) (i : Fin (2 * ℓ)) : Fin (2 * ℓ) → ℂ :=
  (oddPartnerSign ℓ i : ℂ) • stdF ℓ (oddPartner ℓ i)

/-- The even form is orthonormal on the standard basis. -/
theorem stdFormEven_stdE (k : ℕ) (i j : Fin k) :
    stdFormEven k (stdE k i) (stdE k j) = if i = j then 1 else 0 := by
  unfold stdFormEven stdE
  rw [Finset.sum_eq_single i]
  · by_cases h : i = j
    · subst h; simp
    · rw [Pi.single_eq_same, one_mul, Pi.single_eq_of_ne h, ite_eq_right h]
  · intro m _ hm
    rw [Pi.single_eq_of_ne hm, zero_mul]
  · intro hmem
    exact absurd (Finset.mem_univ i) hmem

/-- The odd form on the standard basis: `−oddPartnerSign` at the
partner index and zero elsewhere. -/
theorem stdFormOdd_stdF (ℓ : ℕ) (i j : Fin (2 * ℓ)) :
    stdFormOdd ℓ (stdF ℓ i) (stdF ℓ j) =
      if j = oddPartner ℓ i then -(oddPartnerSign ℓ i : ℂ) else 0 := by
  unfold stdFormOdd stdF
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, mul_one]
    by_cases h : j = oddPartner ℓ i
    · subst h; rw [Pi.single_eq_same, ite_eq_left rfl, mul_one]
    · rw [Pi.single_eq_of_ne (fun hh => h hh.symm), ite_eq_right h,
        mul_zero]
  · intro m _ hm
    rw [Pi.single_eq_of_ne hm, mul_zero, zero_mul]
  · intro hmem
    exact absurd (Finset.mem_univ i) hmem

/-- The odd form is antisymmetric. -/
theorem stdFormOdd_antisymm (ℓ : ℕ) (x y : Fin (2 * ℓ) → ℂ) :
    stdFormOdd ℓ x y = -stdFormOdd ℓ y x := by
  unfold stdFormOdd
  rw [← Finset.sum_neg_distrib]
  refine Fintype.sum_equiv
    ⟨oddPartner ℓ, oddPartner ℓ, oddPartner_invol ℓ, oddPartner_invol ℓ⟩
    _ _ (fun i => ?_)
  change -(oddPartnerSign ℓ i : ℂ) * x i * y (oddPartner ℓ i) =
    -(-(oddPartnerSign ℓ (oddPartner ℓ i) : ℂ) * y (oddPartner ℓ i) *
      x (oddPartner ℓ (oddPartner ℓ i)))
  rw [oddPartner_invol, oddPartnerSign_oddPartner]
  push_cast
  ring

/-- The companion pairing identity: `b (f i) (g j) = −δ_{ij}`. -/
theorem stdFormOdd_stdF_stdG (ℓ : ℕ) (i j : Fin (2 * ℓ)) :
    stdFormOdd ℓ (stdF ℓ i) (stdG ℓ j) = if i = j then -1 else 0 := by
  unfold stdG stdFormOdd
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [show (∑ m, -(oddPartnerSign ℓ m : ℂ) * stdF ℓ i m *
        ((oddPartnerSign ℓ j : ℂ) * stdF ℓ (oddPartner ℓ j)
          (oddPartner ℓ m))) =
      (oddPartnerSign ℓ j : ℂ) *
        ∑ m, -(oddPartnerSign ℓ m : ℂ) * stdF ℓ i m *
          stdF ℓ (oddPartner ℓ j) (oddPartner ℓ m) from by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun m _ => by ring),
    show (∑ m, -(oddPartnerSign ℓ m : ℂ) * stdF ℓ i m *
        stdF ℓ (oddPartner ℓ j) (oddPartner ℓ m)) =
      stdFormOdd ℓ (stdF ℓ i) (stdF ℓ (oddPartner ℓ j)) from rfl,
    stdFormOdd_stdF]
  by_cases h : i = j
  · subst h
    rw [ite_eq_left rfl, ite_eq_left rfl, mul_neg, ← Int.cast_mul,
      oddPartnerSign_mul_self, Int.cast_one]
  · rw [ite_eq_right (fun hh : oddPartner ℓ j = oddPartner ℓ i =>
      h (by
        have := congrArg (oddPartner ℓ) hh
        rwa [oddPartner_invol, oddPartner_invol, eq_comm] at this)),
      mul_zero, ite_eq_right h]

/-- The even trace of the copairing: `Σ_i b(e_i, e_i) = k`. -/
theorem sum_stdFormEven_diag (k : ℕ) :
    (∑ i, stdFormEven k (stdE k i) (stdE k i)) = (k : ℂ) := by
  rw [Finset.sum_congr rfl
    (fun i _ => (stdFormEven_stdE k i i).trans (ite_eq_left rfl))]
  simp

/-- The odd trace of the copairing: `Σ_i b(f_i, g_i) = −2ℓ`;
together with the even part this is `b(C) = k − 2ℓ`, the value of
a free circle. -/
theorem sum_stdFormOdd_diag (ℓ : ℕ) :
    (∑ i, stdFormOdd ℓ (stdF ℓ i) (stdG ℓ i)) = -(2 * ℓ : ℂ) := by
  rw [Finset.sum_congr rfl
    (fun i _ => (stdFormOdd_stdF_stdG ℓ i i).trans (ite_eq_left rfl))]
  simp

/-- The even form against a basis vector reads off the
coordinate. -/
theorem stdFormEven_stdE_left (k : ℕ) (j : Fin k) (x : Fin k → ℂ) :
    stdFormEven k (stdE k j) x = x j := by
  unfold stdFormEven stdE
  rw [Finset.sum_eq_single j]
  · rw [Pi.single_eq_same, one_mul]
  · intro m _ hm
    rw [Pi.single_eq_of_ne hm, zero_mul]
  · intro hmem
    exact absurd (Finset.mem_univ j) hmem

/-- The odd form against a dual basis vector reads off the
coordinate. -/
theorem stdFormOdd_stdG_left (ℓ : ℕ) (j : Fin (2 * ℓ))
    (x : Fin (2 * ℓ) → ℂ) :
    stdFormOdd ℓ (stdG ℓ j) x = x j := by
  unfold stdFormOdd stdG stdF
  rw [Finset.sum_eq_single (oddPartner ℓ j)]
  · rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one,
      oddPartnerSign_oddPartner, oddPartner_invol]
    push_cast
    rw [show -(-(oddPartnerSign ℓ j : ℂ)) * (oddPartnerSign ℓ j : ℂ) *
        x j = ((oddPartnerSign ℓ j * oddPartnerSign ℓ j : ℤ) : ℂ) *
        x j from by push_cast; ring,
      oddPartnerSign_mul_self, Int.cast_one, one_mul]
  · intro m _ hm
    rw [Pi.smul_apply, Pi.single_eq_of_ne (fun hh : m = oddPartner ℓ j =>
        hm hh), smul_zero, mul_zero, zero_mul]
  · intro hmem
    exact absurd (Finset.mem_univ (oddPartner ℓ j)) hmem

/-- **The even contraction identity** (accompanying paper,
§5.2): contracting the even copairing through the form is the identity. -/
theorem sum_stdFormEven_smul (k : ℕ) (x : Fin k → ℂ) :
    (∑ i, stdFormEven k (stdE k i) x • stdE k i) = x := by
  funext j
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single j]
  · rw [Pi.smul_apply, stdFormEven_stdE_left]
    unfold stdE
    rw [Pi.single_eq_same, smul_eq_mul, mul_one]
  · intro m _ hm
    rw [Pi.smul_apply, smul_eq_mul]
    unfold stdE
    rw [Pi.single_eq_of_ne (fun hh : j = m => hm hh.symm), mul_zero]
  · intro hmem
    exact absurd (Finset.mem_univ j) hmem

end RS
