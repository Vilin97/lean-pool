/-
Copyright (c) 2026 Jue Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jue Xu
-/

module

public import LeanPool.LowWeightPauliDynamics.Constants.ChainWeights
public import LeanPool.LowWeightPauliDynamics.Constants.Total
public import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The product estimate and the quantitative `D`-sector assembly

This file completes the scalar part of the proof of `apd:eq:total_high_weight_norm`. It bounds
the rung product by a factorial times a power, sums the slot polynomial over the sectors of
chains with `D = m - K` fewer jumps than the all-ones chain, and assembles the result into the
`c₀` form of `apd:eq:c0`.

## The product estimate

By `prod_rungW_eq` the rung product is `∏_{j=2}^{n+1} w_j = (k_h-1)^n ∏_{i=1}^{n} (i+c)`, and
`prod_add_one_le_factorial_exp_rpow` bounds `∏_{i=1}^{n} (i+c)` by `n! (e n)^c`. The shifted
product `∏_{j=2}^{n+1} (j+c)` dominates it termwise (`prod_shift_le`), and
`prod_shifted_le_factorial_exp_rpow` proves the corresponding estimate `(n+1)! (e(n+1))^c` for
the shifted product as well, so the estimate is available in either indexing.

## The assembly

`total_truncation_error_product_bound` composes `total_truncation_error` with the product
estimate and retains its hypothesis `hstep` explicitly. The later theorems prove the
factorial/exponential sector estimate, combine it with the reset/local-inflow lemmas of
`Lean4LPD/Ladder/ChainBound.lean`, and use `Lean4LPD/Constants/ChainWeights.lean` to discharge
the concrete jump and entry bounds. The final theorem `MultiLadder.sum_block_epsJump_le_cZero`
concludes the `c₀`-form scalar bound, which is the shape of `hstep`, from reset and local layer
inflow. It is a statement about an abstract `MultiLadder`; the Pauli trajectory, its reset and
its layer inflow are supplied in `Lean4LPD/Pauli/LayerError.lean`.

## Main results

* `prod_add_one_le_factorial_exp_rpow`, `prod_shifted_le_factorial_exp_rpow`: the product
  estimate in the two indexings.
* `total_truncation_error_product_bound`: `total_truncation_error` with the product estimate
  applied.
* `sum_factorial_sectors_le_exp`, `slot_polynomial_le_exp`: the `D`-sector sum is bounded by an
  exponential.
* `chain_slot_sum_le_exp`, `MultiLadder.sum_block_inflow_le_exp`: the sector estimate combined
  with the composition count and with the block-inflow bound.
* `cZero_pow_nat`, `sector_bound_le_cZero`: the passage to the `c₀` form.
* `MultiLadder.sum_block_epsJump_le_cZero`: the `c₀`-form bound for the concrete jump norms.
-/

public section

namespace Lean4LPD

open Finset

/-- The product estimate for `apd:eq:total_high_weight_norm`: for `c ≥ 0` and `n ≥ 1`,
`∏_{i=1}^n (i+c) ≤ n! (e n)^c`. By `prod_rungW_eq` the left-hand side is the rung product
`∏_{j=2}^{n+1} w_j` up to the factor `(k_h-1)^n`. The proof writes the product as
`n! ∏_{i=1}^n (1 + c/i)`, bounds it by `n! exp(c H_n)`, and uses `H_n ≤ 1 + log n`.

The hypothesis `n ≥ 1` cannot be dropped: at `n = 0` the empty product is `1`, while
`(e · 0)^c = 0` for every `c > 0`. -/
theorem prod_add_one_le_factorial_exp_rpow {c : ℝ} (hc : 0 ≤ c) (n : ℕ) (hn : 1 ≤ n) :
    ∏ i ∈ range n, ((i : ℝ) + 1 + c) ≤
      (Nat.factorial n : ℝ) * (Real.exp 1 * (n : ℝ)) ^ c := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hfactor : ∏ i ∈ range n, ((i : ℝ) + 1 + c) =
      (Nat.factorial n : ℝ) * ∏ i ∈ range n, (1 + c / ((i : ℝ) + 1)) := by
    rw [← prod_range_add_one_cast, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hi : (i : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  have hsum : (∑ i ∈ range n, c / ((i : ℝ) + 1)) = c * (harmonic n : ℝ) := by
    simp [harmonic, Finset.mul_sum, div_eq_mul_inv]
  have hexp : Real.exp (c * (1 + Real.log (n : ℝ))) =
      (Real.exp 1 * (n : ℝ)) ^ c := by
    rw [Real.rpow_def_of_pos (by positivity),
      Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hnpos), Real.log_exp]
    congr 1
    ring
  calc
    ∏ i ∈ range n, ((i : ℝ) + 1 + c) =
        (Nat.factorial n : ℝ) * ∏ i ∈ range n, (1 + c / ((i : ℝ) + 1)) := hfactor
    _ ≤ (Nat.factorial n : ℝ) * Real.exp (∑ i ∈ range n, c / ((i : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left
        (Real.prod_one_add_le_exp_sum _ fun i => div_nonneg hc (by positivity))
        (Nat.cast_nonneg _)
    _ ≤ (Nat.factorial n : ℝ) * Real.exp (c * (1 + Real.log (n : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Real.exp_le_exp.mpr
      rw [hsum]
      exact mul_le_mul_of_nonneg_left (harmonic_le_one_add_log n) hc
    _ = (Nat.factorial n : ℝ) * (Real.exp 1 * (n : ℝ)) ^ c := by rw [hexp]

/-- The product estimate for `apd:eq:total_high_weight_norm` in shifted indexing:
`∏_{j=2}^{n+1} (j+c) ≤ (n+1)! (e(n+1))^c` for `c ≥ 0` and every `n`. Since `1 + c ≥ 1`, the
shifted product over `n` factors is at most the unshifted product over `n + 1` factors, so this
follows from `prod_add_one_le_factorial_exp_rpow` at `n + 1`. -/
theorem prod_shifted_le_factorial_exp_rpow {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    ∏ i ∈ range n, ((i : ℝ) + 2 + c) ≤
      (Nat.factorial (n + 1) : ℝ) * (Real.exp 1 * ((n : ℝ) + 1)) ^ c := by
  have hnonneg : 0 ≤ ∏ i ∈ range n, ((i : ℝ) + 2 + c) := by
    apply Finset.prod_nonneg
    intro i _
    positivity
  have hsplit : ∏ i ∈ range (n + 1), ((i : ℝ) + 1 + c) =
      (1 + c) * ∏ i ∈ range n, ((i : ℝ) + 2 + c) := by
    rw [Finset.prod_range_succ']
    simp_rw [Nat.cast_add, Nat.cast_one,
      show ∀ i : ℕ, (i : ℝ) + 1 + 1 + c = (i : ℝ) + 2 + c from fun i => by ring]
    simp [mul_comm]
  have hle : ∏ i ∈ range n, ((i : ℝ) + 2 + c) ≤
      ∏ i ∈ range (n + 1), ((i : ℝ) + 1 + c) := by
    rw [hsplit]
    nlinarith [mul_nonneg hc hnonneg]
  exact hle.trans (by
    simpa only [Nat.cast_add, Nat.cast_one] using
      prod_add_one_le_factorial_exp_rpow hc (n + 1) (by omega))

/-- `total_truncation_error` composed with the product estimate
`prod_add_one_le_factorial_exp_rpow`: the summed truncation error is at most
`(t/t₀)^{m+1} (e(m+1))^c ‖O‖` with `t/t₀ = decayBase Γ k_h a t`. Only the product estimate is
added here; the hypothesis `hstep` of `total_truncation_error` is retained unchanged, and is
proved from reset and layer inflow in `MultiLadder.sum_block_epsJump_le_cZero` below. -/
theorem total_truncation_error_product_bound {S M t a G kh1 c B : ℝ} {m r : ℕ}
    (hstep : S ≤ (cZero (r : ℝ) (m : ℝ) G B * G * a * t) ^ (m + 1)
              * (∏ j ∈ range (m + 1), rungW kh1 c (j + 2))
              / (Nat.factorial (m + 1) : ℝ) * M)
    (hadm : Admissible (r : ℝ) (m : ℝ) G) (hm1 : 1 ≤ (m : ℝ)) (hr5 : 5 ≤ (r : ℝ))
    (hB0 : 0 ≤ B) (hB1 : B ≤ 1) (hkh1 : 0 < kh1) (hc : 0 ≤ c)
    (ha : 0 < a) (ht : 0 ≤ t) (hM : 0 ≤ M) :
    S ≤ decayBase G (kh1 + 1) a t ^ (m + 1) *
      (Real.exp 1 * ((m : ℝ) + 1)) ^ c * M := by
  have htotal := total_truncation_error hstep hadm hm1 hr5 hB0 hB1 hkh1 hc ha ht hM
  have hfac : (0 : ℝ) < (Nat.factorial (m + 1) : ℝ) := by positivity
  have hprod : (∏ i ∈ range (m + 1), ((i : ℝ) + 1 + c)) /
      (Nat.factorial (m + 1) : ℝ) ≤ (Real.exp 1 * ((m : ℝ) + 1)) ^ c := by
    apply (div_le_iff₀ hfac).mpr
    simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using
      prod_add_one_le_factorial_exp_rpow hc (m + 1) (by omega)
  obtain ⟨_, _, hG, _, _⟩ := hadm
  have hbase : 0 ≤ decayBase G (kh1 + 1) a t ^ (m + 1) :=
    pow_nonneg (decayBase_nonneg hG (by linarith) ha ht) _
  calc
    S ≤ decayBase G (kh1 + 1) a t ^ (m + 1) *
        (∏ i ∈ range (m + 1), ((i : ℝ) + 1 + c)) /
        (Nat.factorial (m + 1) : ℝ) * M := htotal
    _ = (decayBase G (kh1 + 1) a t ^ (m + 1) *
        ((∏ i ∈ range (m + 1), ((i : ℝ) + 1 + c)) /
          (Nat.factorial (m + 1) : ℝ))) * M := by ring
    _ ≤ decayBase G (kh1 + 1) a t ^ (m + 1) *
        (Real.exp 1 * ((m : ℝ) + 1)) ^ c * M :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod hbase) hM

/-- The factorial-ratio estimate `m!/(m-D)! ≤ m^D` used in `apd:eq:total_high_weight_norm`,
proved through the falling factorial. -/
lemma factorial_ratio_le_pow {m D : ℕ} (hD : D ≤ m) :
    (Nat.factorial m : ℝ) / (Nat.factorial (m - D) : ℝ) ≤ (m : ℝ) ^ D := by
  have h : Nat.factorial m ≤ m ^ D * Nat.factorial (m - D) := by
    calc
      Nat.factorial m = Nat.factorial (m - D) * m.descFactorial D :=
        (Nat.factorial_mul_descFactorial hD).symm
      _ ≤ Nat.factorial (m - D) * m ^ D :=
        Nat.mul_le_mul_left _ (Nat.descFactorial_le_pow m D)
      _ = m ^ D * Nat.factorial (m - D) := Nat.mul_comm _ _
  apply (div_le_iff₀ (by positivity)).mpr
  exact_mod_cast h

/-- The factorial and composition-count factors in `apd:eq:total_high_weight_norm` are bounded
by the exponential series, for every `m` at once:
`∑_{D<m} C(m-1, D) · m!/(m-D)! · y^D ≤ exp(m² y)` for `y ≥ 0`. -/
theorem sum_factorial_sectors_le_exp (m : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    (∑ D ∈ range m, ((m - 1).choose D : ℝ) *
      ((Nat.factorial m : ℝ) / (Nat.factorial (m - D) : ℝ)) * y ^ D) ≤
      Real.exp ((m : ℝ) ^ 2 * y) := by
  refine le_trans (Finset.sum_le_sum fun D hD => ?_)
    (Real.sum_le_exp_of_nonneg (by positivity) m)
  have hD' : D ≤ m := (Finset.mem_range.mp hD).le
  have hchoose : ((m - 1).choose D : ℝ) ≤
      (m : ℝ) ^ D / (Nat.factorial D : ℝ) := by
    refine le_trans (Nat.choose_le_pow_div (α := ℝ) D (m - 1)) ?_
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply pow_le_pow_left₀ (Nat.cast_nonneg _)
    exact_mod_cast Nat.sub_le m 1
  have hprod := mul_le_mul hchoose (factorial_ratio_le_pow hD')
    (by positivity) (by positivity)
  refine le_trans (mul_le_mul_of_nonneg_right hprod (pow_nonneg hy D)) ?_
  simp only [sq, mul_pow]
  exact le_of_eq (by ring)

/-- Exact reindexing by `D=m-K` in `apd:eq:total_high_weight_norm`, keeping
the all-ones prefactor `X^m/m!` explicit. Only the positive slot count `X` is divided out. -/
theorem slot_polynomial_eq_sectors {m : ℕ} (hm : 1 ≤ m) {X R : ℝ} (hX : 0 < X) :
    (∑ k ∈ range m, X ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) *
      R ^ (m - (k + 1)) * ((m - 1).choose k : ℝ)) =
      X ^ m / (Nat.factorial m : ℝ) *
        ∑ D ∈ range m, ((m - 1).choose D : ℝ) *
          ((Nat.factorial m : ℝ) / (Nat.factorial (m - D) : ℝ)) * (R / X) ^ D := by
  rw [← Finset.sum_range_reflect
    (fun k => X ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) *
      R ^ (m - (k + 1)) * ((m - 1).choose k : ℝ)) m, Finset.mul_sum]
  refine Finset.sum_congr rfl fun D hD => ?_
  have hD' : D < m := Finset.mem_range.mp hD
  have hk : m - 1 - D + 1 = m - D := by omega
  have hsub : m - (m - D) = D := by omega
  rw [hk, hsub, Nat.choose_symm (by omega)]
  have hp : X ^ m = X ^ (m - D) * X ^ D := by
    rw [← pow_add, Nat.sub_add_cancel hD'.le]
  rw [div_pow, hp]
  field_simp

/-- The complete factorial/slot `D`-sector estimate in `apd:eq:total_high_weight_norm`,
generalized from `9/4` to any nonnegative part-ratio bound `R`. -/
theorem slot_polynomial_le_exp {m : ℕ} (hm : 1 ≤ m) {X R : ℝ} (hX : 0 < X) (hR : 0 ≤ R) :
    (∑ k ∈ range m, X ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) *
      R ^ (m - (k + 1)) * ((m - 1).choose k : ℝ)) ≤
      X ^ m / (Nat.factorial m : ℝ) * Real.exp (R * (m : ℝ) ^ 2 / X) := by
  rw [slot_polynomial_eq_sectors hm hX]
  have h := mul_le_mul_of_nonneg_left
    (sum_factorial_sectors_le_exp m (div_nonneg hR hX.le))
    (show 0 ≤ X ^ m / (Nat.factorial m : ℝ) by positivity)
  simpa only [show (m : ℝ) ^ 2 * (R / X) = R * (m : ℝ) ^ 2 / X from by ring] using h

/-- Combine the proved local-ratio chain bound with the full `D`-sector estimate of
`apd:eq:total_high_weight_norm`. The entry inflation `C` is charged exactly once;
the desired chain sum is a conclusion, not one of the local coefficient hypotheses. -/
theorem chain_slot_sum_le_exp {eps : ℕ → ℕ → ℝ} {E W : ℕ → ℝ} {C R X : ℝ}
    {m : ℕ} (hm : 1 ≤ m) (heps : ∀ j m, 0 ≤ eps j m) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hW : 0 ≤ W m) (hX : 0 < X)
    (hentry : ∀ m, 1 ≤ m → E m ≤ C * R ^ (m - 1) * W m)
    (hjump : ∀ j m, 1 ≤ j → j < m →
      eps j m * W (m - j) ≤ R ^ (j - 1) * W m) :
    (∑ k ∈ range m, X ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) *
      chain eps E (k + 1) m) ≤
      C * W m * X ^ m / (Nat.factorial m : ℝ) * Real.exp (R * (m : ℝ) ^ 2 / X) := by
  calc
    (∑ k ∈ range m, X ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) *
        chain eps E (k + 1) m) ≤
        ∑ k ∈ range m, X ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) *
          (C * R ^ (m - (k + 1)) * W m * ((m - 1).choose k : ℝ)) := by
      refine Finset.sum_le_sum fun k _ => ?_
      exact mul_le_mul_of_nonneg_left
        (chain_le_weighted_choose heps hC hR hentry hjump k m hm) (by positivity)
    _ = C * W m * ∑ k ∈ range m, X ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) *
        R ^ (m - (k + 1)) * ((m - 1).choose k : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    _ ≤ C * W m * (X ^ m / (Nat.factorial m : ℝ) * Real.exp (R * (m : ℝ) ^ 2 / X)) :=
      mul_le_mul_of_nonneg_left (slot_polynomial_le_exp hm hX hR) (mul_nonneg hC hW)
    _ = C * W m * X ^ m / (Nat.factorial m : ℝ) * Real.exp (R * (m : ℝ) ^ 2 / X) := by ring

/-- The abstract reset/local-inflow route through the entire quantitative sector sum of
`apd:eq:total_high_weight_norm`. It still requires a concrete model to supply the
local inflow and local coefficient ratios; no final discarded-mass bound is assumed. -/
theorem MultiLadder.sum_block_inflow_le_exp {eps : ℕ → ℕ → ℝ} {E W : ℕ → ℝ}
    {M C R : ℝ} (L : MultiLadder eps E M)
    (heps : ∀ j m, 0 ≤ eps j m) (hE : ∀ m, 0 ≤ E m) (hM : 0 ≤ M)
    (hC : 0 ≤ C) (hR : 0 ≤ R) {m G : ℕ} (hm : 1 ≤ m) (hG : 1 ≤ G) (hW : 0 ≤ W m)
    (r : ℕ) (x : ℕ → ℕ → ℝ)
    (hreset : ∀ d, d < r → x d 0 = 0)
    (hinflow : ∀ d, d < r → ∀ i, i < G → x d (i + 1) ≤ x d i +
      (∑ j ∈ Ico 1 m, eps j m * L.N (m - j) (d * G + i)) + E m * M)
    (hentry : ∀ m, 1 ≤ m → E m ≤ C * R ^ (m - 1) * W m)
    (hjump : ∀ j m, 1 ≤ j → j < m →
      eps j m * W (m - j) ≤ R ^ (j - 1) * W m) :
    (∑ d ∈ range r, x d G) ≤
      M * (C * W m * (((r : ℝ) + 1) * G) ^ m / (Nat.factorial m : ℝ) *
        Real.exp (R * (m : ℝ) ^ 2 / (((r : ℝ) + 1) * G))) := by
  have hGpos : (0 : ℝ) < G := by exact_mod_cast hG
  refine (MultiLadder.sum_block_inflow_le L heps hE hM hm hG r x hreset hinflow).trans ?_
  exact mul_le_mul_of_nonneg_left
    (chain_slot_sum_le_exp hm heps hC hR hW (by positivity) hentry hjump) hM

/-- Raising `c₀` to the power `m + 1` recovers the correction factors of `apd:eq:c0` exactly:
`c₀^{m+1} = ((r+1)/r)^{m+1} · exp(9(m+1)²/(4rΓ)) · (1+B)`. This is an identity, valid for every
natural `m` including `m = 0`; it does not use the bound `c₀ ≤ 2` of `cZero_le_two`, which
requires `m ≥ 1` (see `two_lt_cZero_of_m_zero`). -/
lemma cZero_pow_nat {r G B : ℝ} (hB : 0 ≤ B) (m : ℕ) :
    cZero r (m : ℝ) G B ^ (m + 1) =
      ((r + 1) / r) ^ (m + 1) *
        Real.exp (9 / 4 * ((m : ℝ) + 1) ^ 2 / (r * G)) * (1 + B) := by
  have hroot : ((1 + B) ^ ((1 : ℝ) / ((m : ℝ) + 1))) ^ (m + 1) = 1 + B := by
    simpa only [Nat.cast_add, Nat.cast_one, one_div] using
      Real.rpow_inv_natCast_pow (x := 1 + B) (n := m + 1) (by positivity) (by omega)
  have he : (Real.exp (9 / 4 * ((m : ℝ) + 1) / (r * G))) ^ (m + 1) =
      Real.exp (9 / 4 * ((m : ℝ) + 1) ^ 2 / (r * G)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [cZero, mul_pow, mul_pow, hroot, he]

/-- The scalar passage from the sharper sector denominator `(r+1)Γ` to the `c₀` shape of
`apd:eq:total_high_weight_norm` and `apd:eq:c0`. `A` stands for the paper's product `αt`; only
the angle bound `a ≤ A/r` is used. -/
theorem sector_bound_le_cZero {r G B a A P M : ℝ}
    (hr : 0 < r) (hG : 0 < G) (hB : 0 ≤ B) (ha0 : 0 ≤ a) (hA : 0 ≤ A)
    (ha : a ≤ A / r) (hP : 0 ≤ P) (hM : 0 ≤ M) (m : ℕ) :
    M * ((1 + B) * (a ^ (m + 1) * P) * ((r + 1) * G) ^ (m + 1) /
      (Nat.factorial (m + 1) : ℝ) *
      Real.exp (9 / 4 * ((m : ℝ) + 1) ^ 2 / ((r + 1) * G))) ≤
      (cZero r (m : ℝ) G B * G * A) ^ (m + 1) * P /
        (Nat.factorial (m + 1) : ℝ) * M := by
  have hX : 0 < (r + 1) * G := by positivity
  have hbase : a * ((r + 1) * G) ≤ ((r + 1) / r) * G * A := by
    calc
      a * ((r + 1) * G) ≤ (A / r) * ((r + 1) * G) :=
        mul_le_mul_of_nonneg_right ha hX.le
      _ = ((r + 1) / r) * G * A := by ring
  have hp := pow_le_pow_left₀ (mul_nonneg ha0 hX.le) hbase (m + 1)
  have hfrac : 9 / 4 * ((m : ℝ) + 1) ^ 2 / ((r + 1) * G) ≤
      9 / 4 * ((m : ℝ) + 1) ^ 2 / (r * G) := by
    apply (div_le_div_iff₀ hX (mul_pos hr hG)).mpr
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith
  have he := Real.exp_le_exp.mpr hfrac
  have hpair := mul_le_mul hp he (Real.exp_pos _).le (by positivity)
  have hcoef : 0 ≤ (1 + B) * P / (Nat.factorial (m + 1) : ℝ) * M := by positivity
  have hmul := mul_le_mul_of_nonneg_right hpair hcoef
  calc
    M * ((1 + B) * (a ^ (m + 1) * P) * ((r + 1) * G) ^ (m + 1) /
        (Nat.factorial (m + 1) : ℝ) *
        Real.exp (9 / 4 * ((m : ℝ) + 1) ^ 2 / ((r + 1) * G))) =
        (a * ((r + 1) * G)) ^ (m + 1) *
          Real.exp (9 / 4 * ((m : ℝ) + 1) ^ 2 / ((r + 1) * G)) *
          ((1 + B) * P / (Nat.factorial (m + 1) : ℝ) * M) := by
      simp only [mul_pow]
      ring
    _ ≤ ((r + 1) / r * G * A) ^ (m + 1) *
        Real.exp (9 / 4 * ((m : ℝ) + 1) ^ 2 / (r * G)) *
        ((1 + B) * P / (Nat.factorial (m + 1) : ℝ) * M) := hmul
    _ = (cZero r (m : ℝ) G B * G * A) ^ (m + 1) * P /
        (Nat.factorial (m + 1) : ℝ) * M := by
      simp only [mul_pow]
      rw [cZero_pow_nat hB]
      ring

/-- The concrete `epsJump`/`entryFactor` specialization of `apd:eq:total_high_weight_norm`,
with the paper's entry constant `1 + 4eβ`. All local coefficient and entry premises are
discharged by `ChainWeights`; only the model's reset and layer-inflow recurrence remain inputs. -/
theorem MultiLadder.sum_block_epsJump_le_exp_source {kh1 c a M : ℝ}
    (L : MultiLadder (epsJump kh1 c a) (entryFactor kh1 c a) M)
    (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a) (hb : betaOf kh1 c a ≤ 1 / 2)
    (hM : 0 ≤ M) {m G : ℕ} (hm : 1 ≤ m) (hG : 1 ≤ G)
    (r : ℕ) (x : ℕ → ℕ → ℝ)
    (hreset : ∀ d, d < r → x d 0 = 0)
    (hinflow : ∀ d, d < r → ∀ i, i < G → x d (i + 1) ≤ x d i +
      (∑ j ∈ Ico 1 m, epsJump kh1 c a j m * L.N (m - j) (d * G + i)) +
        entryFactor kh1 c a m * M) :
    (∑ d ∈ range r, x d G) ≤
      M * ((1 + 4 * Real.exp 1 * betaOf kh1 c a) * chainWeight kh1 c a m *
        (((r : ℝ) + 1) * G) ^ m / (Nat.factorial m : ℝ) *
          Real.exp (9 / 4 * (m : ℝ) ^ 2 / (((r : ℝ) + 1) * G))) := by
  have hE (m : ℕ) : 0 ≤ entryFactor kh1 c a m := by
    unfold entryFactor
    exact tsum_nonneg fun i => epsJump_nonneg_for_chain hkh hc ha (m + i) m
  have hC : 0 ≤ 1 + 4 * Real.exp 1 * betaOf kh1 c a := by
    have hb0 := betaOf_nonneg_for_chain hkh hc ha
    positivity
  exact MultiLadder.sum_block_inflow_le_exp L (epsJump_nonneg_for_chain hkh hc ha)
    hE hM hC (by norm_num) hm hG (chainWeight_nonneg hkh hc ha m) r x hreset hinflow
    (fun _ hm => entryFactor_le_chainWeight_source hkh hc ha hb hm)
    (fun _ _ hj hjm => epsJump_mul_chainWeight_le hkh hc ha hj hjm.le)

/-- **The quantitative `hstep` shape is a conclusion, not a hypothesis.**
This proves the scalar assembly in `apd:eq:total_high_weight_norm` / `apd:eq:c0` for reset
blocks obeying the concrete multi-jump layer recurrence. A Pauli model must still instantiate
`L`, `x`, their reset, and their local inflow, which `Lean4LPD/Pauli/LayerError.lean` does; no
equality with a post-cut retained mass is assumed. `A = αt` yields the exact input shape of
`total_truncation_error`. -/
theorem MultiLadder.sum_block_epsJump_le_cZero {kh1 c a A M : ℝ}
    (L : MultiLadder (epsJump kh1 c a) (entryFactor kh1 c a) M)
    (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a) (hb : betaOf kh1 c a ≤ 1 / 2)
    (hA : 0 ≤ A) (hM : 0 ≤ M) {G r : ℕ} (hG : 1 ≤ G) (hr : 1 ≤ r)
    (haA : a ≤ A / (r : ℝ)) (m : ℕ) (x : ℕ → ℕ → ℝ)
    (hreset : ∀ d, d < r → x d 0 = 0)
    (hinflow : ∀ d, d < r → ∀ i, i < G → x d (i + 1) ≤ x d i +
      (∑ j ∈ Ico 1 (m + 1), epsJump kh1 c a j (m + 1) * L.N (m + 1 - j) (d * G + i)) +
        entryFactor kh1 c a (m + 1) * M) :
    (∑ d ∈ range r, x d G) ≤
      (cZero (r : ℝ) (m : ℝ) (G : ℝ) (4 * Real.exp 1 * betaOf kh1 c a) * G * A) ^ (m + 1) *
        (∏ j ∈ range (m + 1), rungW kh1 c (j + 2)) /
          (Nat.factorial (m + 1) : ℝ) * M := by
  have hfirst := MultiLadder.sum_block_epsJump_le_exp_source L hkh hc ha hb hM
    (m := m + 1) (by omega) hG r x hreset hinflow
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hGpos : (0 : ℝ) < G := by exact_mod_cast hG
  have hB : 0 ≤ 4 * Real.exp 1 * betaOf kh1 c a := by
    have hb0 := betaOf_nonneg_for_chain hkh hc ha
    positivity
  have hP : 0 ≤ ∏ j ∈ range (m + 1), rungW kh1 c (j + 2) := by
    exact Finset.prod_nonneg fun j _ => rungW_nonneg hkh hc (by omega)
  refine hfirst.trans ?_
  simpa only [chainWeight, Nat.cast_add, Nat.cast_one] using
    sector_bound_le_cZero hrpos hGpos hB ha hA haA hP hM m

end Lean4LPD
