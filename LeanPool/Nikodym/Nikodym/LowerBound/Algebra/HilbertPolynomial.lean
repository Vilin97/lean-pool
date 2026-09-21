/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import LeanPool.Nikodym.Nikodym.LowerBound.Hilbert.Normalized
import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.Interface

/-!
# Eventual polynomiality of the affine Hilbert function

This file implements blueprint node **A03** of the algebra backend: for every ideal `I` of
`P_d = MvPolynomial (Fin d) K` (over any field, with no primality or homogeneity assumption) the
affine Hilbert function `t ↦ hilbert I t` agrees for all large `t` with a polynomial with rational
coefficients, namely `affineHilbertPoly I`.

The proof is purely combinatorial. By `hilbert_eq_sum_layerCard` (node H01), `hilbert I t` is the
number of standard exponents of degree at most `t`, i.e. the partial sum of the layer counts
`layerCard (standardSet I) s` of a divisor-closed set of exponent vectors. We show:

* `Nikodym.LowerBound.EventuallyPoly h`: the predicate "`h : ℕ → ℚ` agrees with a polynomial at
  all large arguments", with closure lemmas `EventuallyPoly.add`, `EventuallyPoly.sum`,
  `EventuallyPoly.const`, `EventuallyPoly.congr`, `EventuallyPoly.shift` (`t ↦ h (t - e)`) and
  `EventuallyPoly.partialSum` (`t ↦ ∑_{u ≤ t} h u`, via Faulhaber's formula `sum_range_pow`);
* `layerCard_eventually_polynomial`: the layer counts of a divisor-closed
  `S : Set (Fin N → ℕ)` are eventually polynomial. Induction on `N`: the slices
  `slice S j = {a | Fin.snoc a j ∈ S}` along the last coordinate form an antitone chain of
  divisor-closed sets, which stabilizes by Dickson's lemma (`Fin N → ℕ` is well-quasi-ordered,
  `Pi.wellQuasiOrderedLE`); after the stabilization index the layer count is a finite sum of
  shifted slice counts plus a shifted partial sum of the stable slice count;
* `hilbert_eventually_polynomial` and `hilbert_eventually_eq_affineHilbertPoly`: the affine
  Hilbert function of any ideal is eventually polynomial, and `affineHilbertPoly I` is that
  polynomial.
-/

namespace Nikodym.LowerBound

open Finset Polynomial Filter

/-! ### Eventually polynomial functions -/

/-- Blueprint A03: `h : ℕ → ℚ` agrees with a rational polynomial at all sufficiently large
natural numbers. -/
def EventuallyPoly (h : ℕ → ℚ) : Prop :=
  ∃ p : Polynomial ℚ, ∀ᶠ t : ℕ in atTop, h t = p.eval (t : ℚ)

namespace EventuallyPoly

/-- Blueprint A03: a function eventually equal to an eventually polynomial function is eventually
polynomial. -/
theorem congr {h h' : ℕ → ℚ} (hh : EventuallyPoly h) (heq : ∀ᶠ t : ℕ in atTop, h t = h' t) :
    EventuallyPoly h' := by
  obtain ⟨p, hp⟩ := hh
  exact ⟨p, (heq.and hp).mono fun t ht ↦ ht.1.symm.trans ht.2⟩

/-- Blueprint A03: constant functions are eventually polynomial. -/
theorem const (c : ℚ) : EventuallyPoly (fun _ ↦ c) :=
  ⟨C c, Eventually.of_forall fun _ ↦ (eval_C).symm⟩

/-- Blueprint A03: eventually polynomial functions are closed under addition. -/
theorem add {f g : ℕ → ℚ} (hf : EventuallyPoly f) (hg : EventuallyPoly g) :
    EventuallyPoly (fun t ↦ f t + g t) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p + q, (hp.and hq).mono fun t ht ↦ by
    change f t + g t = _
    rw [eval_add, ht.1, ht.2]⟩

/-- Blueprint A03: eventually polynomial functions are closed under finite sums. -/
theorem sum {ι : Type*} (s : Finset ι) {f : ι → ℕ → ℚ} (hf : ∀ i ∈ s, EventuallyPoly (f i)) :
    EventuallyPoly (fun t ↦ ∑ i ∈ s, f i t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const 0
  | insert a s ha ih =>
    simp only [sum_insert ha]
    exact (hf a (mem_insert_self _ _)).add (ih fun i hi ↦ hf i (mem_insert_of_mem hi))

/-- Blueprint A03: eventually polynomial functions are closed under the shift `t ↦ h (t - e)`
(truncated subtraction is harmless since eventually `t ≥ e`). -/
theorem shift {h : ℕ → ℚ} (hh : EventuallyPoly h) (e : ℕ) :
    EventuallyPoly (fun t ↦ h (t - e)) := by
  obtain ⟨p, hp⟩ := hh
  obtain ⟨N, hN⟩ := eventually_atTop.mp hp
  refine ⟨p.comp (X - C (e : ℚ)), ?_⟩
  filter_upwards [eventually_ge_atTop (N + e)] with t ht
  rw [eval_comp, eval_sub, eval_X, eval_C, ← Nat.cast_sub (by omega), hN _ (by omega)]

/-- Blueprint A03 (auxiliary): the partial sums `t ↦ ∑_{u ≤ t} p(u)` of a polynomial are given
by a polynomial, by Faulhaber's formula for the sums of powers. -/
private lemma exists_poly_sum_range (p : Polynomial ℚ) :
    ∃ q : Polynomial ℚ, ∀ t : ℕ, ∑ u ∈ range (t + 1), p.eval (u : ℚ) = q.eval (t : ℚ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨P, hP⟩ := hp
    obtain ⟨Q, hQ⟩ := hq
    exact ⟨P + Q, fun t ↦ by simp only [eval_add, sum_add_distrib, hP, hQ]⟩
  | monomial n c =>
    refine ⟨C c * (∑ i ∈ range (n + 1),
      C (_root_.bernoulli i * ((n + 1).choose i : ℚ) / (n + 1)) * X ^ (n + 1 - i)).comp (X + 1),
      fun t ↦ ?_⟩
    simp only [eval_monomial, ← mul_sum, eval_mul, eval_C, eval_comp, eval_add, eval_X, eval_one,
      eval_finsetSum, eval_pow]
    congr 1
    have h := sum_range_pow (t + 1) n
    push_cast at h
    rw [h]
    exact sum_congr rfl fun i _ ↦ by ring

/-- Blueprint A03: eventually polynomial functions are closed under partial sums
`t ↦ ∑_{u ≤ t} h u`: the initial non-polynomial segment contributes a constant. -/
theorem partialSum {h : ℕ → ℚ} (hh : EventuallyPoly h) :
    EventuallyPoly (fun t ↦ ∑ u ∈ range (t + 1), h u) := by
  obtain ⟨p, hp⟩ := hh
  obtain ⟨N, hN⟩ := eventually_atTop.mp hp
  obtain ⟨q, hq⟩ := exists_poly_sum_range p
  refine ⟨q + C (∑ u ∈ range N, (h u - p.eval (u : ℚ))), ?_⟩
  filter_upwards [eventually_ge_atTop N] with t ht
  rw [eval_add, eval_C, ← hq]
  have hsum : ∑ u ∈ range N, (h u - p.eval (u : ℚ)) =
      ∑ u ∈ range (t + 1), (h u - p.eval (u : ℚ)) := by
    have hsub : range N ⊆ range (t + 1) := by
      intro u hu
      rw [mem_range] at hu ⊢
      omega
    apply sum_subset hsub
    intro u _ hu
    rw [mem_range, not_lt] at hu
    rw [hN u hu, sub_self]
  rw [hsum, sum_sub_distrib]
  ring

end EventuallyPoly

/-! ### Slices of a set of exponent vectors along the last coordinate -/

variable {N : ℕ}

/-- Blueprint A03: the slice of `S ⊆ ℕ^{N+1}` at last coordinate `j`, as a subset of `ℕ^N`. -/
def slice (S : Set (Fin (N + 1) → ℕ)) (j : ℕ) : Set (Fin N → ℕ) :=
  {a | Fin.snoc a j ∈ S}

/-- Blueprint A03: membership in a slice. -/
theorem mem_slice {S : Set (Fin (N + 1) → ℕ)} {j : ℕ} {a : Fin N → ℕ} :
    a ∈ slice S j ↔ Fin.snoc a j ∈ S :=
  Iff.rfl

/-- Blueprint A03: slices of a divisor-closed set are divisor-closed. -/
theorem slice_downClosed {S : Set (Fin (N + 1) → ℕ)}
    (hS : ∀ α ∈ S, ∀ β : Fin (N + 1) → ℕ, (∀ i, β i ≤ α i) → β ∈ S) (j : ℕ) :
    ∀ a ∈ slice S j, ∀ b : Fin N → ℕ, (∀ i, b i ≤ a i) → b ∈ slice S j := by
  intro a ha b hb
  refine hS _ ha _ fun i ↦ ?_
  refine Fin.lastCases ?_ (fun i ↦ ?_) i
  · simp only [Fin.snoc_last, le_refl]
  · simpa only [Fin.snoc_castSucc] using hb i

/-- Blueprint A03: the slices of a divisor-closed set form an antitone chain. -/
theorem slice_anti {S : Set (Fin (N + 1) → ℕ)}
    (hS : ∀ α ∈ S, ∀ β : Fin (N + 1) → ℕ, (∀ i, β i ≤ α i) → β ∈ S) {j j' : ℕ} (h : j ≤ j') :
    slice S j' ⊆ slice S j := by
  intro a ha
  refine hS _ ha _ fun i ↦ ?_
  refine Fin.lastCases ?_ (fun i ↦ ?_) i
  · simpa only [Fin.snoc_last] using h
  · simp only [Fin.snoc_castSucc, le_refl]

/-- Blueprint A03: the degree-`t` layer of `S ⊆ ℕ^{N+1}` decomposes along the last coordinate
`j ≤ t` into the degree-`(t - j)` layers of the slices. -/
theorem layerCard_eq_sum_slice (S : Set (Fin (N + 1) → ℕ)) (t : ℕ) :
    layerCard S t = ∑ j ∈ range (t + 1), layerCard (slice S j) (t - j) := by
  classical
  have hmaps : ∀ β ∈ layer S t, β (Fin.last N) ∈ range (t + 1) := by
    intro β hβ
    rw [mem_range, Nat.lt_succ_iff, ← (mem_layer.mp hβ).1]
    exact single_le_sum (fun _ _ ↦ Nat.zero_le _) (mem_univ _)
  rw [layerCard, card_eq_sum_card_fiberwise hmaps]
  refine sum_congr rfl fun j hj ↦ ?_
  have hjt : j ≤ t := Nat.lt_succ_iff.mp (mem_range.mp hj)
  rw [layerCard]
  refine card_bij' (fun β _ ↦ Fin.init β) (fun a _ ↦ Fin.snoc a j) ?_ ?_ ?_ ?_
  · intro β hβ
    rw [mem_filter] at hβ
    obtain ⟨hsum, hβS⟩ := mem_layer.mp hβ.1
    refine mem_layer.mpr ⟨?_, ?_⟩
    · rw [Fin.sum_univ_castSucc] at hsum
      change ∑ i, Fin.init β i + β (Fin.last N) = t at hsum
      omega
    · rw [mem_slice, ← hβ.2, Fin.snoc_init_self]
      exact hβS
  · intro a ha
    obtain ⟨hsum, haS⟩ := mem_layer.mp ha
    rw [mem_filter, mem_layer, Fin.snoc_last]
    refine ⟨⟨?_, haS⟩, rfl⟩
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    omega
  · intro β hβ
    rw [mem_filter] at hβ
    rw [← hβ.2]
    exact Fin.snoc_init_self β
  · intro a _
    exact Fin.init_snoc _ _

/-- Blueprint A03: the antitone chain of slices of a divisor-closed set stabilizes (Dickson's
lemma: `Fin N → ℕ` is well-quasi-ordered). -/
theorem exists_slice_stable {S : Set (Fin (N + 1) → ℕ)}
    (hS : ∀ α ∈ S, ∀ β : Fin (N + 1) → ℕ, (∀ i, β i ≤ α i) → β ∈ S) :
    ∃ J : ℕ, ∀ j, J ≤ j → slice S j = slice S J := by
  by_contra! hcon
  choose f hf using hcon
  have hlt : ∀ J, J < f J := fun J ↦
    lt_of_le_of_ne (hf J).1 fun h ↦ (hf J).2 (by rw [← h])
  have hx : ∀ J, ∃ x, x ∈ slice S J ∧ x ∉ slice S (f J) := by
    intro J
    by_contra! h
    exact (hf J).2 (Set.Subset.antisymm (slice_anti hS (hf J).1) h)
  choose x hx using hx
  let g : ℕ → ℕ := fun n ↦ f^[n] 0
  have hg_succ : ∀ n, g (n + 1) = f (g n) := fun n ↦ Function.iterate_succ_apply' f n 0
  have hg : StrictMono g := strictMono_nat_of_lt_succ fun n ↦ by
    rw [hg_succ]
    exact hlt _
  obtain ⟨m, n, hmn, hle⟩ := wellQuasiOrdered_le (α := Fin N → ℕ) fun n ↦ x (g n)
  have h1 : x (g n) ∈ slice S (f (g m)) := by
    refine slice_anti hS ?_ (hx (g n)).1
    rw [← hg_succ]
    exact hg.monotone hmn
  exact (hx (g m)).2 (slice_downClosed hS _ _ h1 _ hle)

/-! ### Eventual polynomiality of the layer counts -/

/-- Blueprint A03 (combinatorial core): the layer counts `t ↦ layerCard S t` of a divisor-closed
set `S ⊆ ℕ^N` are eventually polynomial. Induction on `N` via the slices along the last
coordinate. -/
theorem layerCard_eventually_polynomial {N : ℕ} (S : Set (Fin N → ℕ))
    (hS : ∀ α ∈ S, ∀ β : Fin N → ℕ, (∀ i, β i ≤ α i) → β ∈ S) :
    EventuallyPoly (fun t ↦ (layerCard S t : ℚ)) := by
  induction N with
  | zero =>
    refine ⟨0, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with t ht
    rw [eval_zero, Nat.cast_eq_zero, layerCard, card_eq_zero, eq_empty_iff_forall_notMem]
    intro β hβ
    have h := (mem_layer.mp hβ).1
    rw [Fin.sum_univ_zero] at h
    omega
  | succ N ih =>
    obtain ⟨J, hJ⟩ := exists_slice_stable hS
    have hsl : ∀ j, EventuallyPoly (fun t ↦ (layerCard (slice S j) t : ℚ)) := fun j ↦
      ih _ (slice_downClosed hS j)
    have key : EventuallyPoly (fun t ↦ ∑ j ∈ range J, (layerCard (slice S j) (t - j) : ℚ) +
        ∑ u ∈ range (t - J + 1), (layerCard (slice S J) u : ℚ)) :=
      (EventuallyPoly.sum (range J) fun j _ ↦ (hsl j).shift j).add ((hsl J).partialSum.shift J)
    refine key.congr ?_
    filter_upwards [eventually_ge_atTop J] with t ht
    rw [layerCard_eq_sum_slice, Nat.cast_sum,
      ← sum_range_add_sum_Ico _ (by omega : J ≤ t + 1)]
    congr 1
    have hst : ∑ j ∈ Ico J (t + 1), (layerCard (slice S j) (t - j) : ℚ) =
        ∑ j ∈ Ico J (t + 1), (layerCard (slice S J) (t - j) : ℚ) :=
      sum_congr rfl fun j hj ↦ by rw [hJ j (mem_Ico.mp hj).1]
    rw [hst, sum_Ico_eq_sum_range, show t + 1 - J = t - J + 1 by omega]
    refine (sum_range_reflect (fun u ↦ (layerCard (slice S J) u : ℚ)) (t - J + 1)).symm.trans
      (sum_congr rfl fun k hk ↦ ?_)
    have hk := mem_range.mp hk
    rw [show t - J + 1 - 1 - k = t - (J + k) by omega]

/-! ### The affine Hilbert function -/

variable {K : Type*} [Field K] {d : ℕ}

/-- Blueprint A03: the affine Hilbert function of any ideal `I ⊆ P_d` is eventually polynomial. -/
theorem hilbert_eventually_polynomial (I : Ideal (MvPolynomial (Fin d) K)) :
    ∃ p : Polynomial ℚ, ∀ᶠ t : ℕ in atTop, (hilbert I t : ℚ) = p.eval (t : ℚ) := by
  have h := (layerCard_eventually_polynomial (standardSet I) (standardSet_downClosed I)).partialSum
  refine h.congr (Eventually.of_forall fun t ↦ ?_)
  rw [hilbert_eq_sum_layerCard, Nat.cast_sum]

/-- Blueprint A03: `affineHilbertPoly I` is the eventual polynomial of the affine Hilbert function
of `I`, for every ideal `I ⊆ P_d`. -/
theorem hilbert_eventually_eq_affineHilbertPoly (I : Ideal (MvPolynomial (Fin d) K)) :
    ∀ᶠ t : ℕ in atTop, (hilbert I t : ℚ) = (affineHilbertPoly I).eval (t : ℚ) :=
  affineHilbertPoly_spec I (hilbert_eventually_polynomial I)

end Nikodym.LowerBound

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
