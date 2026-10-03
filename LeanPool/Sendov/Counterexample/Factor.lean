/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Complex.Basic

/-!
# The two factorizations

A polynomial `p` of degree `n` over `ℂ` splits, so it factors over its roots, and so does `p'`.
The blog post writes these as

  `p(z) = (z-a) ∏ⱼ (z - zⱼ)`,   `p'(z) = n ∏ⱼ (z - a + 1/qⱼ)`,

where `a` is the distinguished root, the `zⱼ` are the others, and the critical points are
written as `a - 1/qⱼ` — possible exactly because each lies at distance at least `1` from `a`,
which puts each `qⱼ` in the closed unit disk.

Everything here is deliberately **hypothesis-light**.  Nothing is assumed about `a` beyond its
being a root: not that it is real, not that `|a| < 1`, not that `a ≠ 0`.  The boundary case
`|a| = 1` of Rubinstein's theorem needs these same two factorizations, and would not be able
to use them if `|a| < 1` were baked in here.  The stronger hypotheses enter one layer up.

Roots are kept as **multisets** throughout, which is how Mathlib produces them and what allows
repeated roots without comment.

A note on the proofs: the root multisets are extracted with `obtain ⟨z, hz⟩ : ∃ z, … := ⟨_, rfl⟩`
rather than named with `set`.  Rewriting `p = C p.leadingCoeff * (p.roots.map …).prod` into a
goal that still mentions `p.roots` otherwise loops, and `set` leaves a local definition that
rewriting unfolds again.  An opaque local is what is wanted.

## Main statements

* `Sendov.exists_root_multiset`: the factorization of `p` over `a` and the other roots;
* `Sendov.exists_crit_multiset`: the factorization of `p'` over the reciprocal coordinates `q`.
-/

public section

namespace Sendov

open Polynomial

/-- The factorization of `p` over its roots, with the distinguished root `a` split off. -/
theorem exists_root_multiset {n : ℕ} (hn : 1 ≤ n) {p : ℂ[X]} (hdeg : p.natDegree = n)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) {a : ℂ} (hpa : p.eval a = 0) :
    ∃ z : Multiset ℂ, z.card = n - 1 ∧ (∀ w ∈ z, ‖w‖ ≤ 1) ∧
      p = C p.leadingCoeff * ((X - C a) * (z.map (fun w => X - C w)).prod) := by
  have hp0 : p ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  have hsplit : p.Splits := IsAlgClosed.splits p
  have hcard : p.roots.card = n := by
    rw [← hdeg]
    exact hsplit.natDegree_eq_card_roots.symm
  have hmem : a ∈ p.roots := by
    rw [mem_roots hp0]
    exact hpa
  obtain ⟨z, hz⟩ : ∃ z : Multiset ℂ, p.roots = a ::ₘ z :=
    ⟨p.roots.erase a, (Multiset.cons_erase hmem).symm⟩
  have hfac := hsplit.eq_prod_roots
  rw [hz] at hfac hcard
  refine ⟨z, ?_, ?_, ?_⟩
  · simp only [Multiset.card_cons] at hcard
    omega
  · intro w hw
    exact hroots w (by rw [hz]; exact Multiset.mem_cons_of_mem hw)
  · rwa [Multiset.map_cons, Multiset.prod_cons] at hfac

/-- The factorization of `p'`.  Each critical point `w` lies at distance at least `1` from `a`,
so `(a - w)⁻¹` lies in the closed unit disk and `w = a - ((a-w)⁻¹)⁻¹`. -/
theorem exists_crit_multiset {n : ℕ} (hn : 2 ≤ n) {p : ℂ[X]} (hdeg : p.natDegree = n) {a : ℂ}
    (hcrit : ∀ w : ℂ, (derivative p).eval w = 0 → 1 ≤ ‖w - a‖) :
    ∃ q : Multiset ℂ, q.card = n - 1 ∧ (∀ v ∈ q, ‖v‖ ≤ 1) ∧ (∀ v ∈ q, v ≠ 0) ∧
      derivative p = C ((n : ℂ) * p.leadingCoeff)
        * (q.map (fun v => X - C (a - v⁻¹))).prod := by
  have hp0 : p ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  have hdd : (derivative p).natDegree = n - 1 := by
    rw [natDegree_derivative p, hdeg]
  have hd0 : derivative p ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdd
    omega
  -- Mathlib already knows the leading coefficient of a derivative
  have hlc : (derivative p).leadingCoeff = (n : ℂ) * p.leadingCoeff := by
    rw [leadingCoeff_derivative, hdeg, mul_comm]
  have hsplit : (derivative p).Splits := IsAlgClosed.splits _
  have hcard : (derivative p).roots.card = n - 1 := by
    rw [← hdd]
    exact hsplit.natDegree_eq_card_roots.symm
  have hfac := hsplit.eq_prod_roots
  -- make the root multiset opaque before rewriting anything into `hfac`
  obtain ⟨W, hW⟩ : ∃ W : Multiset ℂ, (derivative p).roots = W := ⟨_, rfl⟩
  rw [hW] at hfac hcard
  have hcrit' : ∀ w ∈ W, 1 ≤ ‖w - a‖ := by
    intro w hw
    exact hcrit w (isRoot_of_mem_roots (by rw [hW]; exact hw))
  have hne : ∀ w ∈ W, a - w ≠ 0 := by
    intro w hw h
    have h1 := hcrit' w hw
    rw [sub_eq_zero] at h
    rw [← h, sub_self, norm_zero] at h1
    linarith
  obtain ⟨q, hq⟩ : ∃ q : Multiset ℂ, q = W.map (fun w => (a - w)⁻¹) := ⟨_, rfl⟩
  have hback : q.map (fun v => a - v⁻¹) = W := by
    rw [hq, Multiset.map_map]
    have hid : ∀ w ∈ W, ((fun v => a - v⁻¹) ∘ (fun w => (a - w)⁻¹)) w = w := by
      intro w hw
      simp only [Function.comp_apply, inv_inv]
      ring
    rw [Multiset.map_congr rfl hid, Multiset.map_id']
  refine ⟨q, ?_, ?_, ?_, ?_⟩
  · rw [hq, Multiset.card_map, hcard]
  · intro v hv
    rw [hq] at hv
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.1 hv
    rw [norm_inv, inv_le_one_iff₀]
    right
    rw [norm_sub_rev]
    exact hcrit' w hw
  · intro v hv
    rw [hq] at hv
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.1 hv
    exact inv_ne_zero (hne w hw)
  · rw [← hback, hlc] at hfac
    rwa [Multiset.map_map] at hfac

end Sendov
