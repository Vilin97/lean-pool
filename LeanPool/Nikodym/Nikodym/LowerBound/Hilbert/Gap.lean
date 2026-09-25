/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module


public import LeanPool.Nikodym.Nikodym.LowerBound.Hilbert.Normalized
public import LeanPool.Nikodym.Nikodym.LowerBound.Arithmetic.BinomialGap
public import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.Interface

/-!
# Hilbert gap with all denominators cleared

This file implements blueprint node **C03** of the lower-bound side of the sharp finite-field
Nikodym exponent.

Let `I` be a prime ideal of `P_d = MvPolynomial (Fin d) K` of quotient dimension `k = quotDim I`
and degree `Δ = degree I`, and let `2 ≤ d`, `1 ≤ k`, `2 ≤ q`, `8 d² ≤ r ≤ q`. With
`T = r (q - 1) - 1` and `U = q (r - 1) + d (q - 1)` the main theorem `hilbert_gap` states

  `r * H_I(U) ≤ r * H_I(T) + 4 d² * (Δ q^k) * (r + k - 1).choose k`,

an additive natural-number inequality. It combines the normalized cumulative Hilbert inequality
(node H03, `hilbert_mul_choose_le`), the integer binomial-ratio estimate (node C02,
`r_mul_choose_le`, `choose_T_le`) and the uniform Hilbert upper bound A08 supplied by
`AlgebraInterface.hilbert_le_degree_mul_choose`.

The intermediate step `hilbert_gap_aux`, `r * H_I(U) ≤ r * H_I(T) + 4 d² * H_I(T)`, holds for
every ideal `I` and needs no algebraic input.
-/

@[expose] public section

namespace Nikodym.LowerBound

variable {K : Type*} [Field K] {d : ℕ}

/-- Blueprint C03 (first step): for every ideal `I`, with `T = r (q - 1) - 1` and
`U = q (r - 1) + d (q - 1)`, one has `r * H_I(U) ≤ r * H_I(T) + 4 d² * H_I(T)`. This follows from
the normalized cumulative inequality H03 and the binomial-ratio estimate C02 after cancelling the
positive factor `(T + d).choose d`. -/
theorem hilbert_gap_aux (I : Ideal (MvPolynomial (Fin d) K)) (hd : 2 ≤ d) {q r : ℕ} (hq : 2 ≤ q)
    (hr : 8 * d ^ 2 ≤ r) (hrq : r ≤ q) :
    r * hilbert I (q * (r - 1) + d * (q - 1)) ≤
      r * hilbert I (r * (q - 1) - 1) + 4 * d ^ 2 * hilbert I (r * (q - 1) - 1) := by
  have hTU : r * (q - 1) - 1 ≤ q * (r - 1) + d * (q - 1) := T_le_U hd hq hr
  have hc₀ : 0 < (r * (q - 1) - 1 + d).choose d := Nat.choose_pos (Nat.le_add_left d _)
  have hH03 := hilbert_mul_choose_le (I := I) hTU
  have hC02 := r_mul_choose_le hd hq hr hrq
  set T := r * (q - 1) - 1
  set U := q * (r - 1) + d * (q - 1)
  refine Nat.le_of_mul_le_mul_right ?_ hc₀
  calc r * hilbert I U * (T + d).choose d
      = r * (hilbert I U * (T + d).choose d) := by ring
    _ ≤ r * (hilbert I T * (U + d).choose d) := Nat.mul_le_mul_left _ hH03
    _ = hilbert I T * (r * (U + d).choose d) := by ring
    _ ≤ hilbert I T * ((r + 4 * d ^ 2) * (T + d).choose d) := Nat.mul_le_mul_left _ hC02
    _ = (r * hilbert I T + 4 * d ^ 2 * hilbert I T) * (T + d).choose d := by ring

/-- Blueprint C03: the Hilbert gap with all denominators cleared. For a prime `I` of quotient
dimension `k = quotDim I ≥ 1` and degree `Δ = degree I`, with `2 ≤ d`, `2 ≤ q`, `8 d² ≤ r ≤ q`,
`T = r (q - 1) - 1` and `U = q (r - 1) + d (q - 1)`,

  `r * H_I(U) ≤ r * H_I(T) + 4 d² * (Δ q^k) * (r + k - 1).choose k`.

The blueprint hypothesis `k ≤ d` is automatic (`quotDim_le`) and is therefore not assumed. -/
theorem hilbert_gap (H : AlgebraInterface K d) {I : Ideal (MvPolynomial (Fin d) K)}
    (hI : I.IsPrime) (hd : 2 ≤ d) (hk : 1 ≤ quotDim I) {q r : ℕ} (hq : 2 ≤ q)
    (hr : 8 * d ^ 2 ≤ r) (hrq : r ≤ q) :
    r * hilbert I (q * (r - 1) + d * (q - 1)) ≤
      r * hilbert I (r * (q - 1) - 1) +
        4 * d ^ 2 * (degree I * q ^ quotDim I) * (r + quotDim I - 1).choose (quotDim I) := by
  have h1 := hilbert_gap_aux I hd hq hr hrq
  have hA08 := H.hilbert_le_degree_mul_choose I hI (r * (q - 1) - 1)
  have hC02 := choose_T_le hd hq hr hrq hk (quotDim_le I)
  set T := r * (q - 1) - 1
  set U := q * (r - 1) + d * (q - 1)
  set k := quotDim I
  set Δ := degree I
  have h2 : hilbert I T ≤ Δ * q ^ k * (r + k - 1).choose k :=
    calc hilbert I T ≤ Δ * (T + k).choose k := hA08
      _ ≤ Δ * (q ^ k * (r + k - 1).choose k) := Nat.mul_le_mul_left _ hC02
      _ = Δ * q ^ k * (r + k - 1).choose k := by ring
  calc r * hilbert I U ≤ r * hilbert I T + 4 * d ^ 2 * hilbert I T := h1
    _ ≤ r * hilbert I T + 4 * d ^ 2 * (Δ * q ^ k * (r + k - 1).choose k) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ h2) _
    _ = r * hilbert I T + 4 * d ^ 2 * (Δ * q ^ k) * (r + k - 1).choose k := by ring

end Nikodym.LowerBound

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
