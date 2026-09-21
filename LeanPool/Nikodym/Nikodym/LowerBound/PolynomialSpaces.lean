/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import Mathlib

/-!
# Degree-bounded polynomial spaces

This file implements blueprint node **F01** of the lower-bound side of the sharp finite-field
Nikodym exponent.

For a field `K` and `d : ℕ`, the polynomial ring `P_d = K[X_1, …, X_d]` is
`MvPolynomial (Fin d) K`, and the space `P_{d,≤t}` of polynomials of total degree at most `t` is
Mathlib's `MvPolynomial.restrictTotalDegree (Fin d) K t`. We collect the basic API used by the
rest of the development:

* `Nikodym.LowerBound.exponentsLE d t`: the finset of exponent vectors `α : Fin d →₀ ℕ` with
  `α.degree ≤ t`, and `Nikodym.LowerBound.card_exponentsLE : #(exponentsLE d t) = (t + d).choose d`;
* `Nikodym.LowerBound.finrank_restrictTotalDegree :
    Module.finrank K (restrictTotalDegree (Fin d) K t) = (t + d).choose d`;
* membership lemmas (`mem_restrictTotalDegree_iff`, `C_mem_restrictTotalDegree`,
  `X_mem_restrictTotalDegree`, `monomial_mem_restrictTotalDegree`), monotonicity in `t`
  (`restrictTotalDegree_mono`), and the multiplication rule `mul_mem_restrictTotalDegree`.

Finite-dimensionality of `restrictTotalDegree (Fin d) K t` is already a Mathlib instance; we
restate it as `Nikodym.LowerBound.instModuleFiniteRestrictTotalDegree` for discoverability.
-/

namespace Nikodym.LowerBound

open MvPolynomial Finset

variable {K : Type*} [Field K] {d : ℕ}

/-! ### Counting exponent vectors -/

section Counting

/-- Blueprint F01: the finset of exponent vectors `α : Fin d →₀ ℕ` of total degree
`α.degree = ∑ i, α i` at most `t`, i.e. the exponents of the monomials spanning `P_{d,≤t}`. -/
def exponentsLE (d t : ℕ) : Finset (Fin d →₀ ℕ) :=
  (range (t + 1)).biUnion fun k ↦ (univ : Finset (Fin d)).finsuppAntidiag k

/-- Blueprint F01: membership in `exponentsLE d t`. -/
theorem mem_exponentsLE {t : ℕ} {α : Fin d →₀ ℕ} : α ∈ exponentsLE d t ↔ α.degree ≤ t := by
  simp only [exponentsLE, mem_biUnion, mem_range, mem_finsuppAntidiag, subset_univ, and_true,
    Nat.lt_succ_iff, Finsupp.degree_eq_sum]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact hk
  · intro h
    exact ⟨_, h, rfl⟩

/-- Blueprint F01: the elementary identity `∑_{k ≤ t} multichoose d k = multichoose (d+1) t`,
i.e. the number of monomials of degree at most `t` in `d` variables equals the number of monomials
of degree exactly `t` in `d + 1` variables. -/
theorem sum_range_multichoose (d t : ℕ) :
    ∑ k ∈ range (t + 1), d.multichoose k = (d + 1).multichoose t := by
  induction t with
  | zero => simp [Nat.multichoose_zero_right]
  | succ t ih => rw [sum_range_succ, ih, Nat.multichoose_succ_succ, add_comm]

/-- Blueprint F01: there are exactly `(t + d).choose d` exponent vectors of degree at most `t`
in `d` variables. -/
theorem card_exponentsLE (d t : ℕ) : #(exponentsLE d t) = (t + d).choose d := by
  rw [exponentsLE, card_biUnion]
  · simp_rw [card_finsuppAntidiag_nat_eq_multichoose, card_univ, Fintype.card_fin]
    rw [sum_range_multichoose, Nat.multichoose_eq]
    have h : d + 1 + t - 1 = t + d := by omega
    rw [h, Nat.choose_symm_add]
  · intro i _ j _ hij
    refine Finset.disjoint_left.mpr fun α hi hj ↦ ?_
    rw [mem_finsuppAntidiag] at hi hj
    exact hij (hi.1.symm.trans hj.1)

end Counting

/-! ### The spaces `P_{d,≤t}` -/

section RestrictTotalDegree

/-- Blueprint F01: `f ∈ P_{d,≤t}` iff `f.totalDegree ≤ t`. -/
theorem mem_restrictTotalDegree_iff {t : ℕ} {f : MvPolynomial (Fin d) K} :
    f ∈ restrictTotalDegree (Fin d) K t ↔ f.totalDegree ≤ t :=
  mem_restrictTotalDegree _ _ _

/-- Blueprint F01: `f ∈ P_{d,≤t}` iff every exponent vector in the support of `f` has degree
at most `t`. -/
theorem mem_restrictTotalDegree_iff_forall_support {t : ℕ} {f : MvPolynomial (Fin d) K} :
    f ∈ restrictTotalDegree (Fin d) K t ↔ ∀ α ∈ f.support, α.degree ≤ t := by
  rw [mem_restrictTotalDegree_iff, totalDegree, Finset.sup_le_iff]
  rfl

/-- Blueprint F01: `P_{d,≤t}` is the span of the monomials with exponents in `exponentsLE d t`. -/
theorem restrictTotalDegree_eq_restrictSupport (t : ℕ) :
    restrictTotalDegree (Fin d) K t =
      restrictSupport K (↑(exponentsLE d t) : Set (Fin d →₀ ℕ)) := by
  rw [restrictTotalDegree]
  congr 1
  ext α
  simp only [Set.mem_setOf_eq, Finset.mem_coe, mem_exponentsLE]
  rfl

/-- Blueprint F01: `P_{d,≤t}` is a finite-dimensional `K`-vector space (this is a Mathlib
instance, restated here for discoverability). -/
instance instModuleFiniteRestrictTotalDegree (t : ℕ) :
    Module.Finite K (restrictTotalDegree (Fin d) K t) :=
  inferInstance

/-- Blueprint F01: `dim_K P_{d,≤t} = (t + d).choose d`. -/
theorem finrank_restrictTotalDegree (t : ℕ) :
    Module.finrank K (restrictTotalDegree (Fin d) K t) = (t + d).choose d := by
  rw [restrictTotalDegree_eq_restrictSupport,
    Module.finrank_eq_nat_card_basis (basisRestrictSupport K _), Nat.card_coe_set_eq,
    Set.ncard_coe_finset, card_exponentsLE]

/-- Blueprint F01: the spaces `P_{d,≤t}` increase with `t`. -/
theorem restrictTotalDegree_mono {s t : ℕ} (h : s ≤ t) :
    restrictTotalDegree (Fin d) K s ≤ restrictTotalDegree (Fin d) K t := fun _ hf ↦
  mem_restrictTotalDegree_iff.mpr ((mem_restrictTotalDegree_iff.mp hf).trans h)

/-- Blueprint F01: multiplication by a polynomial of degree at most `e` maps `P_{d,≤t}` into
`P_{d,≤t+e}`. -/
theorem mul_mem_restrictTotalDegree {t e : ℕ} {f g : MvPolynomial (Fin d) K}
    (hf : f ∈ restrictTotalDegree (Fin d) K t) (hg : g.totalDegree ≤ e) :
    g * f ∈ restrictTotalDegree (Fin d) K (t + e) := by
  rw [mem_restrictTotalDegree_iff] at hf ⊢
  have := totalDegree_mul g f
  omega

/-- Blueprint F01: multiplication by a polynomial of degree at most `e` maps `P_{d,≤t}` into
`P_{d,≤t+e}` (right multiplication version). -/
theorem mul_mem_restrictTotalDegree' {t e : ℕ} {f g : MvPolynomial (Fin d) K}
    (hf : f ∈ restrictTotalDegree (Fin d) K t) (hg : g.totalDegree ≤ e) :
    f * g ∈ restrictTotalDegree (Fin d) K (t + e) := by
  rw [mul_comm]
  exact mul_mem_restrictTotalDegree hf hg

/-- Blueprint F01: constants lie in every `P_{d,≤t}`. -/
theorem C_mem_restrictTotalDegree (t : ℕ) (a : K) :
    (C a : MvPolynomial (Fin d) K) ∈ restrictTotalDegree (Fin d) K t := by
  rw [mem_restrictTotalDegree_iff, totalDegree_C]
  exact Nat.zero_le _

/-- Blueprint F01: `1 ∈ P_{d,≤t}`. -/
theorem one_mem_restrictTotalDegree (t : ℕ) :
    (1 : MvPolynomial (Fin d) K) ∈ restrictTotalDegree (Fin d) K t := by
  simpa using C_mem_restrictTotalDegree (K := K) (d := d) t 1

/-- Blueprint F01: the variables lie in `P_{d,≤t}` as soon as `1 ≤ t`. -/
theorem X_mem_restrictTotalDegree {t : ℕ} (ht : 1 ≤ t) (i : Fin d) :
    (X i : MvPolynomial (Fin d) K) ∈ restrictTotalDegree (Fin d) K t := by
  rw [mem_restrictTotalDegree_iff, totalDegree_X]
  exact ht

/-- Blueprint F01: a monomial with exponent vector of degree at most `t` lies in `P_{d,≤t}`. -/
theorem monomial_mem_restrictTotalDegree {t : ℕ} {α : Fin d →₀ ℕ} (hα : α.degree ≤ t) (a : K) :
    (monomial α a : MvPolynomial (Fin d) K) ∈ restrictTotalDegree (Fin d) K t := by
  rw [mem_restrictTotalDegree_iff]
  exact (totalDegree_monomial_le α a).trans hα

/-- Blueprint F01: a monomial with nonzero coefficient lies in `P_{d,≤t}` iff its exponent
vector has degree at most `t`. -/
theorem monomial_mem_restrictTotalDegree_iff {t : ℕ} {α : Fin d →₀ ℕ} {a : K} (ha : a ≠ 0) :
    (monomial α a : MvPolynomial (Fin d) K) ∈ restrictTotalDegree (Fin d) K t ↔ α.degree ≤ t := by
  rw [mem_restrictTotalDegree_iff, totalDegree_monomial α ha]
  rfl

end RestrictTotalDegree

end Nikodym.LowerBound

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
