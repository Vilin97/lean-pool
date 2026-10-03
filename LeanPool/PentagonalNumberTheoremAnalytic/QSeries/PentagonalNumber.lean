/-
Copyright (c) 2026 Jonathan Conrad, Paula Muermann, Maryna Viazovska. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Conrad, Paula Muermann, Maryna Viazovska
-/
module

public import LeanPool.PentagonalNumberTheoremAnalytic.QSeries.JacobiTripleProduct

/-!
# Euler's pentagonal number theorem

**Euler's pentagonal number theorem** states that for $\|q\| < 1$:
$$\prod_{n=1}^{\infty} (1 - q^n) = \sum_{k \in \mathbb{Z}} (-1)^k q^{k(3k-1)/2}$$

This follows from the Jacobi triple product by the substitution
$q \to q^3$, $z \to q$, using the index partition
$\{3n\} \cup \{3n-2\} \cup \{3n-1\} = \mathbb{Z}_{\geq 1}$.

## Main definitions

* `QSeries.pentagonal` — the generalized pentagonal number $\omega(k) = k(3k-1)/2$.

## Main results

* `QSeries.euler_pentagonal_number` — the pentagonal number theorem.
-/

public section

open Finset Filter
open scoped Topology

namespace QSeries

noncomputable section

/-- The $k$-th generalized pentagonal number $\omega(k) = k(3k-1)/2$,
well-defined for $k \in \mathbb{Z}$ (the product $k(3k-1)$ is always even). -/
def pentagonal (k : ℤ) : ℕ :=
  (k * (3 * k - 1) / 2).toNat

/-- At a nonnegative index, $\omega(k) = k + 3\binom{k}{2}$. -/
private theorem pentagonal_natCast (k : ℕ) : pentagonal (k : ℤ) = k + k.choose 2 * 3 := by
  have key : (k : ℤ) * (3 * (k : ℤ) - 1) = 2 * ((k + k.choose 2 * 3 : ℕ) : ℤ) := by
    induction k with
    | zero => norm_num
    | succ n ih =>
      simp only [Nat.cast_succ, Nat.choose_succ_succ, Nat.choose_one_right] at *
      push_cast at *
      linarith
  unfold pentagonal
  rw [key]
  omega

/-- At a negative index, $\omega(-(m+1)) + (m+1) = 3\binom{m+2}{2}$. -/
private theorem pentagonal_neg_succ_add (m : ℕ) :
    pentagonal (-(m + 1) : ℤ) + (m + 1) = (m + 2).choose 2 * 3 := by
  have key : (-((m : ℤ) + 1)) * (3 * (-((m : ℤ) + 1)) - 1) =
      2 * (((m + 2).choose 2 * 3 : ℤ) - ((m : ℤ) + 1)) := by
    induction m with
    | zero => norm_num
    | succ n ih =>
      simp only [Nat.cast_succ, Nat.choose_succ_succ, Nat.choose_one_right,
        Nat.choose_zero_right] at *
      push_cast at *
      linarith
  have hle : (m : ℤ) + 1 ≤ ((m + 2).choose 2 * 3 : ℤ) := by
    have h : (m + 2).choose 2 = (m + 1) + (m + 1).choose 2 := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
    have : (m + 1 : ℕ) ≤ (m + 2).choose 2 * 3 := by omega
    exact_mod_cast this
  unfold pentagonal
  rw [key]
  omega

/-- $\omega(-(m+1)) \neq 0$: the negative pentagonal numbers are all positive. -/
private theorem pentagonal_neg_succ_ne_zero (m : ℕ) : pentagonal (-(m + 1) : ℤ) ≠ 0 := by
  have hp := pentagonal_neg_succ_add m
  have h : (m + 2).choose 2 = (m + 1) + (m + 1).choose 2 := by
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
  omega

/-- Partial products of an absolutely convergent product converge to the product. -/
private theorem tendsto_prod_one_add {f : ℕ → ℂ} (hf : Summable fun k => ‖f k‖) :
    Tendsto (fun n => ∏ k ∈ Finset.range n, (1 + f k)) atTop (𝓝 (∏' k : ℕ, (1 + f k))) :=
  (multipliable_one_add_of_summable hf).hasProd.tendsto_prod_nat

/-- An absolutely convergent product over `ℕ` splits into its three residue classes mod `3`. -/
private theorem tprod_one_add_eq_mul_mul {f : ℕ → ℂ} (hf : Summable fun k => ‖f k‖) :
    ∏' k : ℕ, (1 + f k) = (∏' k : ℕ, (1 + f (3 * k))) * (∏' k : ℕ, (1 + f (3 * k + 1))) *
      ∏' k : ℕ, (1 + f (3 * k + 2)) := by
  have hpart : ∀ n : ℕ, ∏ k ∈ Finset.range (3 * n), (1 + f k) =
      (∏ k ∈ Finset.range n, (1 + f (3 * k))) * (∏ k ∈ Finset.range n, (1 + f (3 * k + 1))) *
        ∏ k ∈ Finset.range n, (1 + f (3 * k + 2)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => simp only [Nat.mul_succ, Finset.prod_range_succ] at *; rw [ih]; ring
  have hL : Tendsto (fun n => ∏ k ∈ Finset.range (3 * n), (1 + f k)) atTop
      (𝓝 (∏' k : ℕ, (1 + f k))) := by
    simpa [Function.comp_def] using
      (tendsto_prod_one_add hf).comp (tendsto_id.nsmul_atTop (three_pos (α := ℕ)))
  have hR := ((tendsto_prod_one_add (f := fun k => f (3 * k))
      (hf.comp_injective fun a b h => by omega)).mul
    (tendsto_prod_one_add (f := fun k => f (3 * k + 1))
      (hf.comp_injective fun a b h => by omega))).mul
    (tendsto_prod_one_add (f := fun k => f (3 * k + 2))
      (hf.comp_injective fun a b h => by omega))
  exact tendsto_nhds_unique hL (hR.congr fun n => (hpart n).symm)

/-- **Euler's pentagonal number theorem**: for $\|q\| < 1$, the infinite product $(q;q)_\infty$
equals the bilateral series $\sum_{k \in \mathbb{Z}} (-1)^k q^{\omega(k)}$ over generalized
pentagonal numbers $\omega(k) = k(3k-1)/2$, written as two one-sided sums. -/
theorem euler_pentagonal_number {q : ℂ} (hq : ‖q‖ < 1) :
    qPochhammerInf q q =
      (∑' k : ℕ, (-1 : ℂ) ^ k * q ^ pentagonal k)
      + ∑' k : ℕ, (-1 : ℂ) ^ (k + 1) * q ^ pentagonal (-(↑k + 1)) := by
  by_cases hq0 : q = 0
  · subst hq0
    have h1 : ∀ k : ℕ, k ≠ 0 → (-1 : ℂ) ^ k * (0 : ℂ) ^ pentagonal (k : ℤ) = 0 := fun k hk => by
      rw [pentagonal_natCast, zero_pow (by omega), mul_zero]
    have h2 : ∀ k : ℕ, (-1 : ℂ) ^ (k + 1) * (0 : ℂ) ^ pentagonal (-(↑k + 1)) = 0 := fun k => by
      rw [zero_pow (pentagonal_neg_succ_ne_zero k), mul_zero]
    rw [tsum_eq_single 0 h1]
    simp only [h2, tsum_zero, add_zero]
    simp [qPochhammerInf, pentagonal]
  · have h3 : ‖q ^ 3‖ < 1 := by simpa using pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
    have hzq : ‖q ^ 3‖ < ‖-q‖ := by
      simpa using pow_lt_self_of_lt_one₀ (norm_pos_iff.mpr hq0) hq (by norm_num : (1 : ℕ) < 3)
    have hf : Summable fun k : ℕ => ‖-q ^ (k + 1)‖ := by
      simpa using (summable_nat_add_iff 1).2 (summable_geometric_of_lt_one (norm_nonneg q) hq)
    have hprod : qPochhammerInf q q = qPochhammerInf (q ^ 3) (q ^ 3) *
        qPochhammerInf (-(-q)) (q ^ 3) * qPochhammerInf (-(q ^ 3) / -q) (q ^ 3) := by
      have hd : (-(q ^ 3) / -q : ℂ) = q ^ 2 := by field_simp
      have e0 : qPochhammerInf q q = ∏' k : ℕ, (1 + -q ^ (k + 1)) :=
        tprod_congr fun k => by ring
      have e1 : qPochhammerInf (-(-q)) (q ^ 3) = ∏' k : ℕ, (1 + -q ^ (3 * k + 1)) :=
        tprod_congr fun k => by rw [neg_neg]; ring
      have e2 : qPochhammerInf (q ^ 2) (q ^ 3) = ∏' k : ℕ, (1 + -q ^ (3 * k + 2)) :=
        tprod_congr fun k => by ring
      have e3 : qPochhammerInf (q ^ 3) (q ^ 3) = ∏' k : ℕ, (1 + -q ^ (3 * k + 3)) :=
        tprod_congr fun k => by ring
      rw [hd, e0, e1, e2, e3, tprod_one_add_eq_mul_mul hf]
      ring
    have hsum1 : ∑' k : ℕ, (-1 : ℂ) ^ k * q ^ pentagonal (k : ℤ) =
        ∑' k : ℕ, (-q) ^ k * (q ^ 3) ^ k.choose 2 :=
      tsum_congr fun k => by rw [pentagonal_natCast, neg_pow]; ring
    have hsum2 : ∑' k : ℕ, (-1 : ℂ) ^ (k + 1) * q ^ pentagonal (-(↑k + 1)) =
        ∑' m : ℕ, (-q : ℂ)⁻¹ ^ (m + 1) * (q ^ 3) ^ (m + 2).choose 2 := by
      refine tsum_congr fun m => ?_
      have hp := pentagonal_neg_succ_add m
      have key : (q ^ 3) ^ (m + 2).choose 2 = q ^ pentagonal (-(↑m + 1)) * q ^ (m + 1) := by
        rw [← pow_mul, ← pow_add]
        congr 1
        omega
      rw [key, show (-q : ℂ)⁻¹ ^ (m + 1) * (q ^ pentagonal (-(↑m + 1)) * q ^ (m + 1)) =
        ((-q : ℂ)⁻¹ * q) ^ (m + 1) * q ^ pentagonal (-(↑m + 1)) from by rw [mul_pow]; ring,
        show ((-q : ℂ)⁻¹ * q) = -1 from by field_simp]
    rw [hprod, hsum1, hsum2]
    exact jacobiTripleProduct_annulus h3 hzq (by simpa using hq) (neg_ne_zero.mpr hq0)

end

end QSeries
