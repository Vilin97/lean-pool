/-
Copyright (c) 2026 Xuanji Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuanji Li
-/

import LeanPool.Chudnovsky.SingularModuli.QuadraticPoints
import LeanPool.Chudnovsky.SingularModuli.FormReduction

/-!
# The CM relations at `τ₁₆₃`: explicit isogeny matrices (Phase C, Track 3)

This file provides the **input-side** data of `PhaseC-PLAN.md` (B8)/(C2): for each
`m ∈ {41, 43, 61}` an explicit integer matrix of determinant `m` fixing `τ₁₆₃` as a Möbius
transformation.  These are the `m`-isogenies of the CM lattice with itself; downstream
(`CMRelations`/`Rationality` in the plan) they witness `Φ_m(j₀, j₀) = 0` and, via
`FormReduction.disc_of_three_relations`, pin the discriminant `D₀ = −163`.

The matrix is `M_n = ![![n+1, −41],![1, n]]` (in the `(a,b,c,d)` convention `M • τ =
(aτ+b)/(cτ+d)`), fixing `τ₁₆₃` because `τ² = τ − 41` (from `41 − τ + τ² = 0`):

* `det M_n = n² + n + 41` — the norm form `x² + xy + 41 y²` at `(x,y) = (n, 1)`;
* `tr M_n = 2n + 1`, and `tr² − 4·det = −163` (the multiplier `λ = 1` throughout);
* the instances `n = 0, 1, 4` give determinants `41, 43, 61` — the minimal working triple
  (§6.6: `{41,43,47}` fails, `−43` survives).

Only elementary Möbius algebra is used; nothing here touches the modular polynomial `Φ_m`
itself (that is `ModularPolynomialQ`, another track).
-/

noncomputable section

namespace Chudnovsky

open UpperHalfPlane Chudnovsky.QF

/-- The CM relation at `τ₁₆₃` in the form `τ² = τ − 41`, recovered from
`FormReduction.isRoot_τ₁₆₃` (`τ₁₆₃` is the root of the reduced form `(1, −1, 41)`). -/
theorem τ₁₆₃_sq : (τ₁₆₃ : ℂ) ^ 2 = (τ₁₆₃ : ℂ) - 41 := by
  have h := QF.isRoot_τ₁₆₃
  simp only [QF.IsRoot] at h
  push_cast at h
  linear_combination h

/-! ## The explicit fixing matrices `M_n = ![![n+1, −41],![1, n]]` -/

/-- **`M_n` fixes `τ₁₆₃`.** `(n+1)τ − 41 = τ·(τ + n)` using `τ² = τ − 41`. -/
theorem cmMatrix_fixes (n : ℤ) : QF.Fixes (n + 1) (-41) 1 n τ₁₆₃ := by
  simp only [QF.Fixes]
  push_cast
  linear_combination -τ₁₆₃_sq

/-- The determinant of `M_n` is the norm-form value `n² + n + 41`. -/
theorem cmMatrix_det (n : ℤ) : (n + 1) * n - (-41) * 1 = n ^ 2 + n + 41 := by ring

/-- The trace of `M_n` is `2n + 1`. -/
theorem cmMatrix_trace (n : ℤ) : (n + 1) + n = 2 * n + 1 := by ring

/-- The characteristic relation `tr² − 4·det = −163`, i.e. every `M_n` has multiplier
`λ = 1` over the discriminant-`−163` order. -/
theorem cmMatrix_disc (n : ℤ) : (2 * n + 1) ^ 2 - 4 * (n ^ 2 + n + 41) = -163 := by ring

/-- Consistency with `QuadraticPoints.det_of_fixes` (the `ℚ[Λ]`-norm-form): the classified
multiplier for `M_n` is `k = 1`, and the determinant equals
`p² + b·p·k + a·c·k²` at `(a,b,c) = (1,−1,41)`, `p = n+1`, `k = 1`. -/
theorem cmMatrix_det_eq_normForm (n : ℤ) :
    (n + 1) * n - (-41) * 1
      = (n + 1) ^ 2 + (-1) * (n + 1) * 1 + 1 * 41 * 1 ^ 2 := by ring

/-! ## The three primes `41, 43, 61` -/

/-- `M_0` fixes `τ₁₆₃` with determinant `41`. -/
theorem cm_41 : QF.Fixes (0 + 1) (-41) 1 0 τ₁₆₃ ∧ (0 + 1) * 0 - (-41) * 1 = 41 :=
  ⟨cmMatrix_fixes 0, by ring⟩

/-- `M_1` fixes `τ₁₆₃` with determinant `43`. -/
theorem cm_43 : QF.Fixes (1 + 1) (-41) 1 1 τ₁₆₃ ∧ (1 + 1) * 1 - (-41) * 1 = 43 :=
  ⟨cmMatrix_fixes 1, by ring⟩

/-- `M_4` fixes `τ₁₆₃` with determinant `61`. -/
theorem cm_61 : QF.Fixes (4 + 1) (-41) 1 4 τ₁₆₃ ∧ (4 + 1) * 4 - (-41) * 1 = 61 :=
  ⟨cmMatrix_fixes 4, by ring⟩

/-- The three determinants are represented by the norm form `x² + xy + 41 y²` at
`(x, y) = (0,1), (1,1), (4,1)` — the arithmetic reason the isogenies exist (`m` splits in
the order `ℤ[τ₁₆₃]`). -/
theorem normForm_represents :
    (0 : ℤ) ^ 2 + 0 * 1 + 41 * 1 ^ 2 = 41 ∧
    (1 : ℤ) ^ 2 + 1 * 1 + 41 * 1 ^ 2 = 43 ∧
    (4 : ℤ) ^ 2 + 4 * 1 + 41 * 1 ^ 2 = 61 := by
  refine ⟨by ring, by ring, by ring⟩

/-- **The three-prime input, packaged for the rationality argument.** The traces
`t = 2n+1` for `n = 0, 1, 4` and multiplier `λ = 1` satisfy the discriminant relations
`t² − 4m = (−163)·λ²` at `m = 41, 43, 61`; feeding these to
`FormReduction.disc_of_three_relations` re-derives `D₀ = −163`.  (Here it is a tautological
consistency check, since `D₀ = −163` is the discriminant of `τ₁₆₃`; downstream the same
shape is applied to an *a priori unknown* common CM point.) -/
theorem three_prime_relations :
    ((2 * 0 + 1 : ℤ) ^ 2 - 4 * 41 = -163 * 1 ^ 2) ∧
    ((2 * 1 + 1 : ℤ) ^ 2 - 4 * 43 = -163 * 1 ^ 2) ∧
    ((2 * 4 + 1 : ℤ) ^ 2 - 4 * 61 = -163 * 1 ^ 2) := by
  refine ⟨by ring, by ring, by ring⟩

example : (-163 : ℤ) = -163 :=
  QF.disc_of_three_relations (by norm_num) (l1 := 1) (l2 := 1) (l3 := 1)
    (by norm_num) (by norm_num) (by norm_num)
    (three_prime_relations.1) (three_prime_relations.2.1) (three_prime_relations.2.2)

end Chudnovsky
