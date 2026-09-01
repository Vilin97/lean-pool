/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
import LeanPool.CompositionAlgebras.Octonions

/-!
# The octonionic trace form

The real part `re : 𝕆 → ℝ` is the normalized trace of left multiplication.  Although `𝕆`
itself is neither commutative nor associative -- `Octonions.non_associative` exhibits a
counterexample -- the *trace* of a product is both symmetric and associative:

* `re_mul_comm`  -- `re (x * y) = re (y * x)`
* `re_mul_assoc` -- `re ((x * y) * z) = re (x * (y * z))`

Equivalently: every commutator lies in `ker re`, and every associator lies in `ker re`.
This is the standard fact that a composition algebra's trace form `⟨x, y⟩ = re (x * conj y)` is
an *associative* symmetric bilinear form, and it is what makes the trace form on
`h₃(𝕆)` Euclidean rather than merely symmetric.

## Why these two

They are the entry-level input to the trace form on the Albert algebra `h₃(𝕆)`.  The
Euclidean hypothesis carried by the order-unit-space construction of the `EJA` layer,

```
hassoc : ⟪m x y, z⟫ = ⟪y, m x z⟫
```

reduces, on hermitian `3 × 3` octonionic matrices, to exactly these two identities on the
octonionic entries (plus positive-definiteness, `re_mul_conj_self` below, which is
`Octonion.mul_conj` read at coordinate `0`).

## Proofs

`re a` is `a.coords 0`, so each statement here is a *single* polynomial identity rather
than an eight-component coordinate expansion: degree 2 in 16 variables for `re_mul_comm`,
degree 3 in 24 variables for
`re_mul_assoc`.  Both are inside the default heartbeat budget; no `set_option
maxHeartbeats` is needed anywhere in this file.

## Downstream

`OctonionModule.lean` reads these two identities in `octIp` vocabulary as
`octIp_conj_cyc` and `octIp_conj_cyc'`, which is the form the trace form on hermitian
octonionic matrices is built over.
-/

namespace Octonion

/-- The `Mul` instance is the explicit `Octonion.mul`.  Bridges the `*`-notation
statements below to the `mul`-form ones used throughout `Octonions.lean`. -/
theorem mul_def (x y : Octonion) : x * y = mul x y := rfl

/-- The trace form is symmetric: the real part of a product does not see the order of the
factors, even though `𝕆` is not commutative.  Equivalently, `re` kills every commutator. -/
theorem re_mul_comm (x y : Octonion) : re (mul x y) = re (mul y x) := by
  simp only [re, mul, Fin.isValue]; norm_num; ring

/-- The trace form is **associative**: the real part of a triple product does not see the
bracketing, even though `𝕆` is not associative (`Octonion.non_associative`).
Equivalently, `re` kills every associator. -/
theorem re_mul_assoc (x y z : Octonion) :
    re (mul (mul x y) z) = re (mul x (mul y z)) := by
  simp only [re, mul, Fin.isValue]; norm_num; ring

/-- `re_mul_comm` in `*` notation. -/
theorem re_hmul_comm (x y : Octonion) : re (x * y) = re (y * x) := re_mul_comm x y

/-- `re_mul_assoc` in `*` notation. -/
theorem re_hmul_assoc (x y z : Octonion) : re ((x * y) * z) = re (x * (y * z)) :=
  re_mul_assoc x y z

/-- Conjugation fixes the real part. -/
@[simp] theorem re_conj (x : Octonion) : re (conj x) = re x := by
  simp only [re, conj]; norm_num

/-- Symmetry of the trace form `⟨x, y⟩ = re (x * conj y)`, in the conjugated shape the Albert
inner product actually uses.  Derived from `conj_mul` and `conj_conj` rather than
recomputed. -/
theorem re_mul_conj_comm (x y : Octonion) :
    re (mul x (conj y)) = re (mul y (conj x)) := by
  rw [← re_conj (mul x (conj y)), conj_mul, conj_conj]

/-- Positive-definiteness of the trace form: `⟨x, x⟩ = N(x)`.  This is `Octonion.mul_conj`
read at coordinate `0`. -/
theorem re_mul_conj_self (x : Octonion) : re (mul x (conj x)) = normSq x := by
  rw [mul_conj]; simp only [re, one, HSMul.hSMul, SMul.smul]; norm_num

end Octonion
