/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module


public import LeanPool.Nikodym.Nikodym.LowerBound.Hilbert.StandardMonomials

/-!
# Normalized cumulative Hilbert inequality

This file implements blueprint node **H03** of the lower-bound side of the sharp finite-field
Nikodym exponent: for every ideal `I` of `P_d = MvPolynomial (Fin d) K` and all `t ≤ u`,

  `H_I(u) * (t + d).choose d ≤ H_I(t) * (u + d).choose d`,

a natural-number inequality with no divisions and no primality or homogeneity assumption on `I`.

The combinatorial core is stated for an arbitrary divisor-closed set `S : Set (Fin d → ℕ)`:

* `Nikodym.LowerBound.cum S t`: the number of elements of `S` of total degree at most `t`, as the
  sum of the layer counts of node H02;
* `Nikodym.LowerBound.lift S`: the slack-variable lift of `S` to `d + 1` variables (the first `d`
  coordinates lie in `S`, the last one is unconstrained), which is again divisor-closed
  (`lift_downClosed`);
* `layerCard_lift_eq_cum`: the degree-`t` layer of `lift S` is in bijection with the elements of
  `S` of degree at most `t`, via `α ↦ Fin.snoc α (t - |α|)`;
* `cum_succ_mul_le`, `cum_succ_mul_choose_le`: the weighted shadow inequality (node H02) applied to
  `lift S` gives `(t + 1) cum(t + 1) ≤ (t + d + 1) cum(t)`, i.e. the adjacent-degree inequality
  `cum(t + 1) * (t + d).choose d ≤ cum(t) * (t + 1 + d).choose d`;
* `cum_mul_choose_le`: iterating the adjacent inequality along `t ≤ u`.

The main theorem `hilbert_mul_choose_le` then follows from `hilbert_eq_sum_layerCard` (node H01)
with `S = standardSet I`.
-/

@[expose] public section

namespace Nikodym.LowerBound

open Finset

variable {K : Type*} [Field K] {d : ℕ}

/-! ### The cumulative count -/

/-- Blueprint H03: the number of elements of `S` of total degree at most `t`, written as the sum
of the layer counts `layerCard S s`, `s ≤ t`. -/
noncomputable def cum (S : Set (Fin d → ℕ)) (t : ℕ) : ℕ :=
  ∑ s ∈ range (t + 1), layerCard S s

/-- Blueprint H03: `cum S 0 = layerCard S 0`. -/
theorem cum_zero (S : Set (Fin d → ℕ)) : cum S 0 = layerCard S 0 := by
  simp [cum]

/-- Blueprint H03: the recursion `cum S (t + 1) = cum S t + layerCard S (t + 1)`. -/
theorem cum_succ (S : Set (Fin d → ℕ)) (t : ℕ) :
    cum S (t + 1) = cum S t + layerCard S (t + 1) := by
  rw [cum, cum, sum_range_succ]

/-! ### The slack-variable lift -/

/-- Blueprint H03: the slack-variable lift of `S`: exponent vectors in `d + 1` variables whose
first `d` coordinates form an element of `S`; the last (slack) coordinate is unconstrained. -/
def lift (S : Set (Fin d → ℕ)) : Set (Fin (d + 1) → ℕ) :=
  {β | Fin.init β ∈ S}

/-- Blueprint H03: membership in `lift S`. -/
theorem mem_lift {S : Set (Fin d → ℕ)} {β : Fin (d + 1) → ℕ} : β ∈ lift S ↔ Fin.init β ∈ S :=
  Iff.rfl

/-- Blueprint H03: the slack-variable lift of a divisor-closed set is divisor-closed. -/
theorem lift_downClosed (S : Set (Fin d → ℕ))
    (hS : ∀ α ∈ S, ∀ β : Fin d → ℕ, (∀ i, β i ≤ α i) → β ∈ S) :
    ∀ β ∈ lift S, ∀ γ : Fin (d + 1) → ℕ, (∀ i, γ i ≤ β i) → γ ∈ lift S := by
  intro β hβ γ hγ
  exact hS _ hβ _ fun i ↦ hγ (Fin.castSucc i)

/-- Blueprint H03: the degree-`t` layer of `lift S` counts the elements of `S` of total degree at
most `t`, via the bijection `α ↦ Fin.snoc α (t - |α|)`. -/
theorem layerCard_lift_eq_cum (S : Set (Fin d → ℕ)) (t : ℕ) :
    layerCard (lift S) t = cum S t := by
  classical
  have hmaps : ∀ β ∈ layer (lift S) t, (∑ i, Fin.init β i) ∈ range (t + 1) := by
    intro β hβ
    rw [mem_range, Nat.lt_succ_iff, ← (mem_layer.mp hβ).1, Fin.sum_univ_castSucc]
    exact Nat.le_add_right _ _
  rw [layerCard, cum, card_eq_sum_card_fiberwise hmaps]
  refine sum_congr rfl fun s hs ↦ ?_
  have hst : s ≤ t := Nat.lt_succ_iff.mp (mem_range.mp hs)
  rw [layerCard]
  refine card_bij' (fun β _ ↦ Fin.init β) (fun α _ ↦ Fin.snoc α (t - s)) ?_ ?_ ?_ ?_
  · intro β hβ
    rw [mem_filter] at hβ
    exact mem_layer.mpr ⟨hβ.2, (mem_layer.mp hβ.1).2⟩
  · intro α hα
    obtain ⟨hαs, hαS⟩ := mem_layer.mp hα
    rw [mem_filter, mem_layer, mem_lift, Fin.init_snoc]
    refine ⟨⟨?_, hαS⟩, hαs⟩
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rw [hαs, Nat.add_sub_cancel' hst]
  · intro β hβ
    rw [mem_filter] at hβ
    have hsum := (mem_layer.mp hβ.1).1
    rw [Fin.sum_univ_castSucc] at hsum
    change ∑ i, Fin.init β i + β (Fin.last d) = t at hsum
    rw [hβ.2] at hsum
    rw [← Nat.eq_sub_of_add_eq' hsum]
    exact Fin.snoc_init_self β
  · intro α _
    exact Fin.init_snoc _ _

/-! ### The adjacent-degree inequality -/

/-- Blueprint H03: the weighted shadow inequality for the cumulative count,
`(t + 1) cum(t + 1) ≤ (t + d + 1) cum(t)`, obtained from node H02 for the slack-variable lift. -/
theorem cum_succ_mul_le (S : Set (Fin d → ℕ))
    (hS : ∀ α ∈ S, ∀ β : Fin d → ℕ, (∀ i, β i ≤ α i) → β ∈ S) (t : ℕ) :
    (t + 1) * cum S (t + 1) ≤ (t + d + 1) * cum S t := by
  have := weighted_shadow (lift S) (lift_downClosed S hS) t
  rwa [layerCard_lift_eq_cum, layerCard_lift_eq_cum, ← Nat.add_assoc] at this

/-- Blueprint H03 (auxiliary): `(t + 1 + d).choose d * (t + 1) = (t + d).choose d * (t + d + 1)`. -/
private lemma choose_succ_mul (t d : ℕ) :
    (t + 1 + d).choose d * (t + 1) = (t + d).choose d * (t + d + 1) := by
  rw [← Nat.choose_symm_add (a := t + 1) (b := d), show t + 1 + d = t + d + 1 by ring,
    ← Nat.add_one_mul_choose_eq, Nat.choose_symm_add, Nat.mul_comm]

/-- Blueprint H03: the adjacent-degree normalized inequality
`cum(t + 1) * (t + d).choose d ≤ cum(t) * (t + 1 + d).choose d`. -/
theorem cum_succ_mul_choose_le (S : Set (Fin d → ℕ))
    (hS : ∀ α ∈ S, ∀ β : Fin d → ℕ, (∀ i, β i ≤ α i) → β ∈ S) (t : ℕ) :
    cum S (t + 1) * (t + d).choose d ≤ cum S t * (t + 1 + d).choose d := by
  refine Nat.le_of_mul_le_mul_right ?_ (Nat.succ_pos t)
  calc cum S (t + 1) * (t + d).choose d * (t + 1)
      = (t + d).choose d * ((t + 1) * cum S (t + 1)) := by ring
    _ ≤ (t + d).choose d * ((t + d + 1) * cum S t) :=
      Nat.mul_le_mul_left _ (cum_succ_mul_le S hS t)
    _ = cum S t * ((t + d).choose d * (t + d + 1)) := by ring
    _ = cum S t * (t + 1 + d).choose d * (t + 1) := by rw [← choose_succ_mul, Nat.mul_assoc]

/-! ### Iteration -/

/-- Blueprint H03: the normalized cumulative inequality for a divisor-closed set,
`cum(u) * (t + d).choose d ≤ cum(t) * (u + d).choose d` for `t ≤ u`. -/
theorem cum_mul_choose_le (S : Set (Fin d → ℕ))
    (hS : ∀ α ∈ S, ∀ β : Fin d → ℕ, (∀ i, β i ≤ α i) → β ∈ S) {t u : ℕ} (htu : t ≤ u) :
    cum S u * (t + d).choose d ≤ cum S t * (u + d).choose d := by
  induction u, htu using Nat.le_induction with
  | base => exact le_rfl
  | succ u htu ih =>
    have hadj := cum_succ_mul_choose_le S hS u
    refine Nat.le_of_mul_le_mul_right ?_ (Nat.choose_pos (Nat.le_add_left d u))
    calc cum S (u + 1) * (t + d).choose d * (u + d).choose d
        = cum S (u + 1) * (u + d).choose d * (t + d).choose d := by ring
      _ ≤ cum S u * (u + 1 + d).choose d * (t + d).choose d := Nat.mul_le_mul_right _ hadj
      _ = cum S u * (t + d).choose d * (u + 1 + d).choose d := by ring
      _ ≤ cum S t * (u + d).choose d * (u + 1 + d).choose d := Nat.mul_le_mul_right _ ih
      _ = cum S t * (u + 1 + d).choose d * (u + d).choose d := by ring

/-! ### The Hilbert function -/

/-- Blueprint H03: the Hilbert function as the cumulative count of the standard exponents. -/
theorem hilbert_eq_cum (I : Ideal (MvPolynomial (Fin d) K)) (t : ℕ) :
    hilbert I t = cum (standardSet I) t :=
  hilbert_eq_sum_layerCard I t

/-- Blueprint H03: the normalized cumulative Hilbert inequality
`H_I(u) * (t + d).choose d ≤ H_I(t) * (u + d).choose d` for `t ≤ u`, for every ideal `I` (no
primality or homogeneity assumption), as a natural-number inequality. -/
theorem hilbert_mul_choose_le {I : Ideal (MvPolynomial (Fin d) K)} {t u : ℕ} (htu : t ≤ u) :
    hilbert I u * (t + d).choose d ≤ hilbert I t * (u + d).choose d := by
  rw [hilbert_eq_cum, hilbert_eq_cum]
  exact cum_mul_choose_le (standardSet I) (standardSet_downClosed I) htu

end Nikodym.LowerBound

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
