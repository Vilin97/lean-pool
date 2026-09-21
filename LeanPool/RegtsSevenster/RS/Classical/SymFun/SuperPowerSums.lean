/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SymFun.PowerSums

/-!
# Super power sums

The central symmetric-function lemmas for the Regts–Sevenster
development.  Given a sequence `t : ℕ → ℂ` whose Schur specialization
vanishes outside a hook, `t` decomposes as a difference of power sums
of two disjoint multisets of nonzero complex numbers (Lemma A.9 of
the accompanying paper); if `t` is eventually zero, then `t` is
identically zero from degree 1 onward (Lemma A.10 there).

The key technical ingredient is the identity `derivative H = T * H`
where `H` is the generating power series of `newtonH t` and `T` is
the shifted power-sum series; this is immediate from the Newton
recursion that defines `newtonH`.
-/

namespace RS

open Finset PowerSeries

/-! ### The generating series and its derivative -/

/-- The generating power series of the complete homogeneous sequence:
`H = PowerSeries.mk (newtonH t)`. -/
noncomputable def newtonHSeries (t : ℕ → ℂ) : ℂ⟦X⟧ :=
  PowerSeries.mk (newtonH t)

/-- The shifted power-sum series: coefficient `n` is `t (n + 1)`. -/
noncomputable def powerSumSeries (t : ℕ → ℂ) : ℂ⟦X⟧ :=
  PowerSeries.mk (fun n => t (n + 1))

/-- The Newton recursion at coefficient level:
`newtonH t (n + 1) * (n + 1) =
∑ i ∈ range (n + 1), t (i + 1) * newtonH t (n − i)`. -/
private theorem newtonH_coeff_identity (t : ℕ → ℂ) (n : ℕ) :
    newtonH t (n + 1) * (↑(n + 1) : ℂ) =
      ∑ i ∈ Finset.range (n + 1), t (i + 1) * newtonH t (n - i) := by
  simp only [newtonH]
  rw [show (↑n : ℂ) + 1 = (↑(n + 1) : ℂ) from by push_cast; ring]
  have hne : (↑(n + 1) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  field_simp

/-- **The derivative identity for the Newton generating series.**
`d⁄dX (newtonHSeries t) = powerSumSeries t * newtonHSeries t`,
i.e. `H' = T · H` where `H = ∑ h_n X^n` and `T = ∑ t_{n+1} X^n`.
This is a direct restatement of the Newton recursion at the level of
formal power series. -/
theorem newtonH_derivative (t : ℕ → ℂ) :
    d⁄dX (newtonHSeries t) = powerSumSeries t * newtonHSeries t := by
  ext n
  rw [coeff_derivative]
  rw [coeff_mul]
  simp only [newtonHSeries, coeff_mk, powerSumSeries]
  rw [Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [show (↑n : ℂ) + 1 = (↑(n + 1) : ℂ) from by push_cast; ring]
  exact newtonH_coeff_identity t n

/-- The constant coefficient of `newtonHSeries t` is `1`. -/
@[simp]
theorem newtonH_series_constantCoeff (t : ℕ → ℂ) :
    constantCoeff (newtonHSeries t) = 1 := by
  simp [newtonHSeries, ← coeff_zero_eq_constantCoeff_apply, coeff_mk]

/-! ### Power series eventually zero implies polynomial coercion -/

/-- A power series whose coefficients vanish from degree `N` onward
equals the coercion of its truncation to a polynomial. -/
theorem powerSeries_eq_coe_trunc_of_eventually_zero {R : Type*} [CommSemiring R]
    (f : PowerSeries R) (N : ℕ) (hf : ∀ m, N ≤ m → coeff m f = 0) :
    f = ↑(PowerSeries.trunc N f) := by
  ext m
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  split
  · rfl
  · rename_i h; simp only [not_lt] at h; exact hf m h

/-! ### Lemma A.10: eventually zero power sums vanish -/

/-- A weighted exponential sum over `Fin n` that vanishes at sufficiently many
consecutive exponents must have all weights zero, by the Vandermonde
argument. -/
private theorem vanishing_exponential_sum
    {n : ℕ} {γ : Fin n → ℂ} (hγ : Function.Injective γ)
    {w : Fin n → ℂ} {M : ℕ}
    (hγnz : ∀ j, γ j ≠ 0)
    (hvan : ∀ i : Fin n, ∑ j : Fin n, w j * γ j ^ (M + (i : ℕ)) = 0) :
    w = 0 := by
  have hvan' : ∀ i : Fin n,
      ∑ j : Fin n, (w j * γ j ^ M) * γ j ^ (i : ℕ) = 0 := by
    intro i
    have := hvan i
    simp only [pow_add] at this
    convert this using 1
    congr 1; ext j; ring
  have hv := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hγ hvan'
  ext j
  have := congr_fun hv j
  simp only [Pi.zero_apply] at this
  exact (mul_eq_zero.mp this).resolve_right (pow_ne_zero M (hγnz j))

/-- The sum of a multiset mapped by `f` equals the finset sum with counts. -/
private theorem multiset_map_sum_eq
    (s : Multiset ℂ) (f : ℂ → ℂ) :
    (s.map f).sum = ∑ a ∈ s.toFinset, (s.count a : ℂ) * f a := by
  rw [Finset.sum_multiset_map_count]
  congr 1; ext a
  rw [nsmul_eq_mul]

/-- Extension of a multiset-weighted sum to a superset. -/
private theorem multiset_sum_eq_finset_sum
    (s : Multiset ℂ) (S : Finset ℂ) (hsS : s.toFinset ⊆ S) (f : ℂ → ℂ) :
    (s.map f).sum = ∑ a ∈ S, (s.count a : ℂ) * f a := by
  rw [multiset_map_sum_eq]
  exact Finset.sum_subset hsS (fun x _ hx => by
    rw [Multiset.count_eq_zero.mpr (Multiset.mem_toFinset.not.mp hx),
        Nat.cast_zero, zero_mul])

/-- **Lemma A.10 of the accompanying paper.**
If `t m = ∑ αᵢ^m − ∑ βⱼ^m` for all `m ≥ 1` with `α` and `β`
multisets of nonzero complex numbers having disjoint supports, and
`t` is eventually zero, then `t m = 0` for all `m ≥ 1`.

The proof is direct: the power-sum difference is rewritten as a
single weighted exponential sum over the union of supports;
vanishing at sufficiently many consecutive exponents forces all
weights to be zero by a Vandermonde argument; but disjointness
makes every weight nonzero, so the support set must be empty. -/
theorem powerSums_zero_of_eventually_zero
    {t : ℕ → ℂ} {α β : Multiset ℂ}
    (hα : ∀ x ∈ α, x ≠ (0 : ℂ))
    (hβ : ∀ x ∈ β, x ≠ (0 : ℂ))
    (hdisj : ∀ x ∈ α, x ∉ β)
    (hps : ∀ m, 1 ≤ m → t m = (α.map (· ^ m)).sum - (β.map (· ^ m)).sum)
    (hev : ∃ N₀ : ℕ, ∀ m, N₀ ≤ m → t m = 0) :
    ∀ m, 1 ≤ m → t m = 0 := by
  classical
  obtain ⟨N₀, hN₀⟩ := hev
  -- ═══════ STAGE 1: rewrite as a single weighted sum ═══════
  set S := α.toFinset ∪ β.toFinset
  set c : ℂ → ℂ := fun a => (α.count a : ℂ) - (β.count a : ℂ)
  have htS : ∀ m, 1 ≤ m →
      t m = ∑ a ∈ S, c a * a ^ m := by
    intro m hm
    rw [hps m hm,
        multiset_sum_eq_finset_sum α S Finset.subset_union_left,
        multiset_sum_eq_finset_sum β S Finset.subset_union_right]
    simp only [c, sub_mul, Finset.sum_sub_distrib]
  -- ═══════ STAGE 2: S must be empty ═══════
  suffices hSe : S = ∅ by
    intro m hm
    rw [htS m hm, hSe, Finset.sum_empty]
  by_contra hSne
  have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSne
  -- Biject S with Fin n using noncomputable equivFin
  set n := S.card
  have hn : 0 < n := Finset.card_pos.mpr hSne
  -- γ : Fin n → ℂ via the equivalence
  set e := S.equivFin with he_def
  set γ : Fin n → ℂ := fun i => (e.symm i : ℂ) with hγ_def
  have hγ_mem : ∀ i, γ i ∈ S := fun i => (e.symm i).prop
  have hγ_inj : Function.Injective γ := by
    intro i j hij
    exact e.symm.injective (Subtype.val_injective hij)
  -- All γ values are nonzero
  have hγnz : ∀ i, γ i ≠ 0 := by
    intro i
    have hi := hγ_mem i
    rcases Finset.mem_union.mp hi with h | h
    · exact hα _ (Multiset.mem_toFinset.mp h)
    · exact hβ _ (Multiset.mem_toFinset.mp h)
  -- c (γ i) ≠ 0 for all i (by disjointness)
  have hc_ne : ∀ i, c (γ i) ≠ 0 := by
    intro i
    have hi := hγ_mem i
    rcases Finset.mem_union.mp hi with h | h
    · have hmem := Multiset.mem_toFinset.mp h
      have hni := hdisj _ hmem
      simp only [c, Multiset.count_eq_zero.mpr hni, Nat.cast_zero, sub_zero]
      exact Nat.cast_ne_zero.mpr (Multiset.count_ne_zero.mpr hmem)
    · have hmem := Multiset.mem_toFinset.mp h
      have hni : γ i ∉ α := fun hmem' => hdisj _ hmem' hmem
      simp only [c, Multiset.count_eq_zero.mpr hni, Nat.cast_zero,
        zero_sub, neg_ne_zero]
      exact Nat.cast_ne_zero.mpr (Multiset.count_ne_zero.mpr hmem)
  -- Convert finset sum to Fin n sum
  have hsum_conv : ∀ (f : ℂ → ℂ), ∑ a ∈ S, f a = ∑ i : Fin n, f (γ i) := by
    intro f
    conv_lhs => rw [← S.sum_coe_sort f]
    exact Fintype.sum_equiv e (fun x => f ↑x) (fun i => f (γ i))
      (fun x => by simp [hγ_def])
  -- ═══════ STAGE 3: Vandermonde contradiction ═══════
  set M := max N₀ 1
  set w : Fin n → ℂ := fun i => c (γ i)
  have hvan_all : ∀ m, M ≤ m → ∑ i : Fin n, w i * γ i ^ m = 0 := by
    intro m hm
    show ∑ i : Fin n, c (γ i) * γ i ^ m = 0
    rw [← hsum_conv (fun a => c a * a ^ m)]
    have : t m = 0 := hN₀ m (le_trans (le_max_left _ _) hm)
    rw [htS m (le_trans (le_max_right _ _) hm)] at this
    exact this
  have hvan_fin : ∀ i : Fin n, ∑ j : Fin n, w j * γ j ^ (M + (i : ℕ)) = 0 :=
    fun i => hvan_all _ (Nat.le_add_right M _)
  have hw := vanishing_exponential_sum hγ_inj hγnz hvan_fin
  exact hc_ne ⟨0, hn⟩ (congr_fun hw ⟨0, hn⟩)

end RS
