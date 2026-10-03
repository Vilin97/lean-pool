/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import Mathlib.NumberTheory.Bernoulli

/-! # The Hankel determinant construction of the paper "ζ(5) is irrational"

This file *defines* (in Lean) the objects of Section 2.1 of the paper
"ζ(5) is irrational" (A. Fauzan, 17 September 2026):

* the polynomials `D_m(t) = ∏_{j=1}^m (t + j²)`;
* the `ℚ`-linear functional `μ_X`, given on monomials by (2.2) and on the simple poles
  `1/(t + j²)` by
(2.3), extended to `P / D_K` by polynomial division and partial fractions;
* the Hankel matrix `G_K(X)` of (2.4), its determinant `Δ_K(X)`, the scalar `S_K` of (2.5)
  and `F_K = S_K Δ_K`.

Throughout, `K = 40 n`, `N = 3 n`, `h = 37 n` as in (2.1).

**Convention.** Two polynomial rings `ℚ[X]` occur: the paper's variable `t` (the argument of the
rational functions the functional is applied to) and the paper's indeterminate `X` (the
value of the functional is affine in `X`). Both are represented by `Polynomial ℚ`; the
docstrings say which is which.

Nothing is proved about these objects here; see `Zeta5Irrational.MainEstimate` for the main
estimate.
-/

public section

open Polynomial Finset

namespace Zeta5Irrational

/-- `D_m(t) = ∏_{j=1}^m (t + j²)`, a monic polynomial in `t`. -/
@[expose] noncomputable def D (m : ℕ) : ℚ[X] :=
  ∏ j ∈ Icc 1 m, (X + C ((j : ℚ) ^ 2))

/-- The polynomial moments (2.2): `μ(t^e) = (-1)^e B_{2e+2} (2e+3)(2e+4)(2e+5) / 24`.
Mathlib's `bernoulli` uses the convention `B₁ = -1/2`, as does the paper. -/
@[expose] def μmono (e : ℕ) : ℚ :=
  (-1) ^ e * _root_.bernoulli (2 * e + 2) * ((2 * e + 3) * (2 * e + 4) * (2 * e + 5)) / 24

/-- `μ` on polynomials in `t`, extended `ℚ`-linearly from the monomials. -/
@[expose] noncomputable def μpoly (P : ℚ[X]) : ℚ :=
  P.sum fun e c => c * μmono e

/-- The generalized harmonic number `H_j^{(5)} = ∑_{v=1}^j v⁻⁵`. -/
@[expose] def H5 (j : ℕ) : ℚ :=
  ∑ v ∈ Icc 1 j, 1 / (v : ℚ) ^ 5

/-- The pole values (2.3), as polynomials in the indeterminate `X`:
`μ_X(1/(t + j²)) = j⁴ (X - H_j^{(5)}) - 1/4 + 1/(2j)`. -/
@[expose] noncomputable def poleValue (j : ℕ) : ℚ[X] :=
  C ((j : ℚ) ^ 4) * (X - C (H5 j)) - C (1 / 4) + C (1 / (2 * (j : ℚ)))

/-- `μ_X(P(t) / D_K(t))` for a polynomial `P` in `t`, as a polynomial in `X`.
Since `D_K` is monic with the simple roots `t = -j²` (`1 ≤ j ≤ K`),
`P / D_K = (P /ₘ D_K) + ∑_j (P(-j²) / D_K'(-j²)) / (t + j²)`, and `μ_X` is applied termwise. -/
@[expose] noncomputable def μX (K : ℕ) (P : ℚ[X]) : ℚ[X] :=
  C (μpoly (P /ₘ D K)) +
    ∑ j ∈ Icc 1 K,
      C (P.eval (-(j : ℚ) ^ 2) / (derivative (D K)).eval (-(j : ℚ) ^ 2)) * poleValue j

/-- The `h × h` Hankel matrix `G_K(X)` of (2.4), whose `(i, j)` entry is
`μ_X (D_N(t)^6 t^(i+j) / D_K(t))`, with `K = 40 n`, `N = 3 n`, `h = 37 n`. -/
@[expose] noncomputable def G (n : ℕ) : Matrix (Fin (37 * n)) (Fin (37 * n)) ℚ[X] := fun i j =>
  μX (40 * n) (D (3 * n) ^ 6 * X ^ ((i : ℕ) + (j : ℕ)))

/-- `Δ_K(X) = det G_K(X)`, a polynomial in `X` (of degree `h`, by (2.9)). -/
@[expose] noncomputable def Δ (n : ℕ) : ℚ[X] :=
  (G n).det

/-- The scalar `S_K` of (2.5). -/
@[expose] noncomputable def S (n : ℕ) : ℚ :=
  ((40 * n).factorial : ℚ) ^ (2 * (37 * n)) * 4 ^ (37 * n - 1) /
    (((3 * n).factorial : ℚ) ^ (12 * (37 * n)) *
      ∏ i ∈ Icc 1 (37 * n - 1), ((2 * i).factorial : ℚ) ^ 2)

/-- `F_K = S_K Δ_K` of (2.5). -/
@[expose] noncomputable def F (n : ℕ) : ℚ[X] :=
  C (S n) * Δ n

end Zeta5Irrational
