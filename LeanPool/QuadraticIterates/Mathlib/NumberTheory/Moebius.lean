/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Sums of the Möbius function over divisors

Restricted Möbius sums over divisors and divisor antidiagonals, and the equal-size
sign partition of the divisors of a squarefree number.

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-- Rewrites the antidiagonal Möbius product `∏_{ed = n} F d ^ μ e` as a product over the divisors
of the radical `n' = rad n`: `∏_{t ∣ n'} F (k t) ^ μ (n'/t)`, where `k = n / n'`. -/
theorem beta_radical (n k n' : ℕ) (hn : 1 ≤ n)
    (hn' : n' = UniqueFactorizationMonoid.radical n) (hk : n = k * n') (F : ℕ → ℚ) :
    ∏ x ∈ n.divisorsAntidiagonal, F x.2 ^ (μ x.1)
      = ∏ t ∈ n'.divisors, F (k * t) ^ (μ (n' / t)) := by
  have hn0 : n ≠ 0 := by lia
  have hn'0 : n' ≠ 0 := hn' ▸ (Nat.radical_pos n).ne'
  rw [Nat.prod_divisorsAntidiagonal (fun a b ↦ F b ^ (μ a))]
  have hdvd_n' : n' ∣ n := by simp [hk]
  rw [← Finset.prod_subset (Nat.divisors_subset_of_dvd hn0 hdvd_n')]
  · rw [← Nat.prod_div_divisors n' (fun x ↦ F (k * x) ^ (μ (n' / x)))]
    refine Finset.prod_congr rfl fun i hi ↦ ?_
    have hidvd : i ∣ n' := Nat.dvd_of_mem_divisors hi
    simp only [← Nat.mul_div_assoc k hidvd, hk, Nat.div_div_self hidvd hn'0]
  · intro i hiin hinotin
    simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree fun hsqfree ↦
      hinotin (Nat.mem_divisors.mpr
        ⟨hn' ▸ (UniqueFactorizationMonoid.dvd_radical_iff hsqfree.isRadical hn0).mpr
          (Nat.dvd_of_mem_divisors hiin), hn'0⟩)]

/-- `∑_{ed = n} μ e = 0` for `n ≥ 2`: the Möbius function is the Dirichlet inverse of `ζ`. -/
theorem moebius_antidiag_sum_zero (n : ℕ) (hn : 2 ≤ n) :
    ∑ x ∈ n.divisorsAntidiagonal, (μ x.1) = 0 := by
  have : (∑ x ∈ n.divisorsAntidiagonal, μ x.1) = (μ * (ζ : ArithmeticFunction ℤ)) n :=
    (Finset.sum_congr rfl fun x hx ↦ by
      simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply,
        Nat.right_ne_zero_of_mem_divisorsAntidiagonal hx]).trans
      (ArithmeticFunction.mul_apply ..).symm
  rw [this, ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply,
    ite_eq_right (by lia)]

/-- For squarefree `n' > 1`, the divisors of `n'` split into two halves of equal size according
to the sign of `μ(n'/t)`. -/
theorem moebius_sign_partition (n' : ℕ) (hn'1 : 1 < n') (hsf : Squarefree n') :
    ∃ Sp Sm : Finset ℕ, Disjoint Sp Sm ∧ Sp ∪ Sm = n'.divisors ∧ Sp.card = Sm.card ∧
      (∀ t ∈ Sp, μ (n' / t) = 1) ∧ (∀ t ∈ Sm, μ (n' / t) = -1) := by
  have hmu_pm : ∀ t ∈ n'.divisors, μ (n' / t) = 1 ∨ μ (n' / t) = -1 := by
    intro t ht
    rw [Nat.mem_divisors] at ht
    have hsf' : Squarefree (n' / t) := hsf.squarefree_of_dvd (Nat.div_dvd_of_dvd ht.1)
    exact mul_self_eq_one_iff.mp (by
      rw [← sq]; exact ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsf')
  set Sp := n'.divisors.filter (fun t ↦ μ (n' / t) = 1) with hSp
  set Sm := n'.divisors.filter (fun t ↦ μ (n' / t) = -1) with hSm
  have hdisj : Disjoint Sp Sm := by
    rw [Finset.disjoint_left]
    intro t htp htm
    rw [hSp, Finset.mem_filter] at htp
    rw [hSm, Finset.mem_filter] at htm
    rw [htp.2] at htm
    exact absurd htm.2 (by decide)
  have hunion : Sp ∪ Sm = n'.divisors := by
    rw [hSp, hSm, ← Finset.filter_or]
    exact Finset.filter_true_of_mem (fun t ht ↦ hmu_pm t ht)
  have hsum0 : ∑ t ∈ n'.divisors, μ (n' / t) = 0 := by
    rw [← Nat.sum_divisorsAntidiagonal' (f := fun e _ ↦ μ e)]
    exact moebius_antidiag_sum_zero n' hn'1
  refine ⟨Sp, Sm, hdisj, hunion, ?_, fun t ht ↦ (Finset.mem_filter.mp ht).2,
    fun t ht ↦ (Finset.mem_filter.mp ht).2⟩
  have hsplit : ∑ t ∈ n'.divisors, μ (n' / t) = ∑ t ∈ Sp, μ (n' / t) + ∑ t ∈ Sm, μ (n' / t) := by
    rw [← hunion, Finset.sum_union hdisj]
  have hSpsum : ∑ t ∈ Sp, μ (n' / t) = (Sp.card : ℤ) := by
    rw [Finset.sum_congr rfl (fun t ht ↦ (Finset.mem_filter.mp ht).2), Finset.sum_const,
      nsmul_eq_mul, mul_one]
  have hSmsum : ∑ t ∈ Sm, μ (n' / t) = -(Sm.card : ℤ) := by
    rw [Finset.sum_congr rfl (fun t ht ↦ (Finset.mem_filter.mp ht).2), Finset.sum_const,
      nsmul_eq_mul, mul_neg_one]
  rw [hSpsum, hSmsum, hsum0] at hsplit
  lia

/-- Under a sign partition `(Sp, Sm)` of the divisors of `n' = rad n` (as produced by
`moebius_sign_partition`), the antidiagonal Möbius product `∏_{ed = n} F d ^ μ e` splits as the
quotient `(∏_{t ∈ Sp} F (k t)) / (∏_{t ∈ Sm} F (k t))`, where `k = n / n'`. -/
theorem prod_pow_moebius_eq_div (n k n' : ℕ) (hn : 1 ≤ n)
    (hn' : n' = UniqueFactorizationMonoid.radical n) (hk : n = k * n') (F : ℕ → ℚ)
    {Sp Sm : Finset ℕ} (hdisj : Disjoint Sp Sm) (hunion : Sp ∪ Sm = n'.divisors)
    (hSp : ∀ t ∈ Sp, μ (n' / t) = 1) (hSm : ∀ t ∈ Sm, μ (n' / t) = -1) :
    ∏ x ∈ n.divisorsAntidiagonal, F x.2 ^ (μ x.1)
      = (∏ t ∈ Sp, F (k * t)) / (∏ t ∈ Sm, F (k * t)) := by
  rw [beta_radical n k n' hn hn' hk F, ← hunion, Finset.prod_union hdisj,
    show (∏ t ∈ Sp, F (k * t) ^ (μ (n' / t))) = ∏ t ∈ Sp, F (k * t) from
      Finset.prod_congr rfl fun t ht ↦ by rw [hSp t ht, zpow_one],
    show (∏ t ∈ Sm, F (k * t) ^ (μ (n' / t))) = (∏ t ∈ Sm, F (k * t))⁻¹ from
      (Finset.prod_congr rfl fun t ht ↦ by rw [hSm t ht, zpow_neg_one]).trans
        (Finset.prod_inv_distrib fun t ↦ F (k * t)),
    div_eq_mul_inv]

/-- The Möbius sum over antidiagonal pairs `(e, d)` with `m ∣ d` is `1` if `n = m` and `0`
otherwise (assuming `m ∣ n`, `m, n ≥ 1`). -/
theorem moebius_restricted_sum (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : m ∣ n) :
    ∑ x ∈ n.divisorsAntidiagonal with m ∣ x.2, (μ x.1 : ℤ) = if n = m then 1 else 0 := by
  have hm_pos : 0 < m := by lia
  have classic : ∀ N ≥ 1, ∑ i ∈ N.divisors, (μ i : ℤ) = if N = 1 then 1 else 0 := by
    intro N hN
    simpa [ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply] using
      (ArithmeticFunction.coe_mul_zeta_apply (f := μ) (x := N)).symm
  obtain ⟨N, rfl⟩ := hmn
  have hN0 : 1 ≤ N := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  have hbij : ∑ x ∈ (m * N).divisorsAntidiagonal with m ∣ x.2, (μ x.1 : ℤ)
      = ∑ y ∈ N.divisorsAntidiagonal, (μ y.1 : ℤ) := by
    apply Finset.sum_nbij' (fun x ↦ (x.1, x.2 / m)) (fun y ↦ (y.1, y.2 * m))
    · rintro ⟨e, d⟩ hx
      simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hx ⊢
      obtain ⟨⟨hed, hne⟩, ⟨d', rfl⟩⟩ := hx
      rw [Nat.mul_div_cancel_left _ hm_pos]
      exact ⟨Nat.eq_of_mul_eq_mul_left hm_pos (by nlinarith), by rintro rfl; simp at hne⟩
    · rintro ⟨e, d'⟩ hy
      simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hy ⊢
      obtain ⟨hed, hne⟩ := hy
      exact ⟨⟨by rw [← hed]; ring, by positivity⟩, ⟨d', by ring⟩⟩
    · rintro ⟨e, d⟩ hx
      simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hx
      obtain ⟨⟨hed, hne⟩, ⟨d', rfl⟩⟩ := hx
      simp [Nat.mul_div_cancel_left _ hm_pos, mul_comm]
    · rintro ⟨e, d'⟩ hy
      simp [Nat.mul_div_cancel _ hm_pos]
    · rintro ⟨e, d⟩ hx
      rfl
  rw [hbij, Nat.sum_divisorsAntidiagonal (fun i j ↦ (μ i : ℤ)), classic N hN0]
  simp only [show (m * N = m) ↔ (N = 1) from
    ⟨fun h ↦ Nat.eq_of_mul_eq_mul_left hm_pos (h.trans (by ring)), fun h ↦ by rw [h, mul_one]⟩]

/-- For a level set `{d : k ≤ g d}` of a `gcd`-`min` function `g`, the antidiagonal Möbius transform
of its indicator (in the second coordinate) over `n` is `0` or `1`; in particular nonnegative. -/
theorem indicator_moebius_nonneg (g : ℕ → ℕ)
    (hmin : ∀ x ≥ 1, ∀ y ≥ 1, g (x.gcd y) = min (g x) (g y)) (n : ℕ) (hn : 1 ≤ n) (k : ℕ) :
    0 ≤ ∑ x ∈ n.divisorsAntidiagonal, (μ x.1 : ℤ) * (if k ≤ g x.2 then 1 else 0) := by
  have hmem (x : ℕ × ℕ) (hx : x ∈ n.divisorsAntidiagonal) : x.2 ∈ n.divisors :=
    Nat.snd_mem_divisors_of_mem_antidiagonal hx
  have hconv : ∑ x ∈ n.divisorsAntidiagonal, (μ x.1 : ℤ) * (if k ≤ g x.2 then 1 else 0)
      = ∑ x ∈ n.divisorsAntidiagonal with k ≤ g x.2, (μ x.1 : ℤ) := by
    rw [Finset.sum_filter]; exact Finset.sum_congr rfl fun x _ ↦ by rw [mul_ite, mul_one, mul_zero]
  rw [hconv]
  rcases (n.divisors.filter (fun d ↦ k ≤ g d)).eq_empty_or_nonempty with he | hne
  · rw [Finset.filter_false_of_mem fun x hx hkx ↦ by
      have hx2 : x.2 ∈ n.divisors.filter (fun d ↦ k ≤ g d) :=
        Finset.mem_filter.mpr ⟨hmem x hx, hkx⟩
      rw [he] at hx2; simp at hx2, Finset.sum_empty]
  · set S := n.divisors.filter (fun d ↦ k ≤ g d) with hS
    set m := S.min' hne
    have hmS : m ∈ S := S.min'_mem hne
    have hmn : m ∣ n := Nat.dvd_of_mem_divisors (Finset.mem_of_mem_filter m hmS)
    have hmk : k ≤ g m := (Finset.mem_filter.mp hmS).2
    have hm1 : 1 ≤ m := Nat.pos_of_dvd_of_pos hmn (by lia)
    have hpred (d : ℕ) (hd : d ∈ n.divisors) : (k ≤ g d) ↔ m ∣ d := by
      have hdn := Nat.dvd_of_mem_divisors hd
      have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
      constructor
      · intro hkd
        have hgcdmem : m.gcd d ∈ S := Finset.mem_filter.mpr
          ⟨Nat.mem_divisors.mpr ⟨(Nat.gcd_dvd_right m d).trans hdn, by lia⟩, by
            rw [hmin m hm1 d hd1]; exact le_min hmk hkd⟩
        have heq : m.gcd d = m :=
          le_antisymm (Nat.gcd_le_left d (by lia)) (S.min'_le _ hgcdmem)
        rw [← heq]; exact Nat.gcd_dvd_right m d
      · intro hmd
        have hgd := hmin m hm1 d hd1
        rw [Nat.gcd_eq_left hmd] at hgd
        exact le_trans hmk (by rw [hgd]; exact min_le_right _ _)
    rw [Finset.filter_congr fun x hx ↦ by rw [hpred x.2 (hmem x hx)],
      moebius_restricted_sum m n hm1 hn hmn]
    split <;> norm_num

/-- **Nonnegativity of the Möbius transform of a `gcd`-`min` function.** If `g` satisfies
`g (gcd x y) = min (g x) (g y)`, then `∑_{ed = n} μ e · g d ≥ 0`. This is the arithmetic core of the
integrality of the Möbius factors of a strong divisibility sequence. -/
theorem moebius_transform_nonneg (g : ℕ → ℕ)
    (hmin : ∀ x ≥ 1, ∀ y ≥ 1, g (x.gcd y) = min (g x) (g y)) (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ ∑ x ∈ n.divisorsAntidiagonal, (μ x.1 : ℤ) * (g x.2 : ℤ) := by
  have hmono (x : ℕ × ℕ) (hx : x ∈ n.divisorsAntidiagonal) : g x.2 ≤ g n := by
    have hx2 : x.2 ∈ n.divisors := Nat.snd_mem_divisors_of_mem_antidiagonal hx
    have h := hmin x.2 (Nat.pos_of_mem_divisors hx2) n (by lia)
    rw [Nat.gcd_eq_left (Nat.dvd_of_mem_divisors hx2)] at h
    omega
  have hcard (a : ℕ) (ha : a ≤ g n) :
      (a : ℤ) = ∑ k ∈ Finset.Icc 1 (g n), if k ≤ a then (1 : ℤ) else 0 := by
    rw [Finset.sum_boole, show (Finset.Icc 1 (g n)).filter (· ≤ a) = Finset.Icc 1 a from by
      ext k; simp only [Finset.mem_filter, Finset.mem_Icc]; omega, Nat.card_Icc]
    simp
  rw [Finset.sum_congr rfl fun x hx ↦ by rw [hcard (g x.2) (hmono x hx), Finset.mul_sum],
    Finset.sum_comm]
  exact Finset.sum_nonneg fun k _ ↦ indicator_moebius_nonneg g hmin n hn k
