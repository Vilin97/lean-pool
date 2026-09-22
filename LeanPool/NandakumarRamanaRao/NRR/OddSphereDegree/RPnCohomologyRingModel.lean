/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# The algebraic target ring `F₂[α] / (αⁿ⁺¹)` of the `RPⁿ` mod-two cohomology computation

The classical computation of the mod-two cohomology ring of real projective space
is the ring isomorphism

```text
H^*(RPⁿ; F₂) ≅ F₂[α] / (αⁿ⁺¹), deg α = 1.
```

This file builds the **right-hand side** — the *algebraic model* — as a genuine,
formalized Lean object together with the structural facts the final theorem
consumes, namely (on the model side):

* `αⁿ⁺¹ = 0` (the defining relation, the truncation);
* `αⁿ ≠ 0` (the top power is nonzero — the "top class" survives);
* more generally `αᵏ = 0 ↔ n+1 ≤ k` (exactly the powers below the truncation
 bound are nonzero), and the total `F₂`-dimension is `n+1`
 (`= Σₖ dim Hᵏ(RPⁿ; F₂)`).

Here the model ring is the genuine quotient polynomial ring

```text
RPnCohomologyRingModel n := (ZMod 2)[X] ⧸ (X^(n+1)),
```

and `modelAlpha n` is the residue class of `X` (the model of the degree-one
generator `α`). ** The bridge `H^*(RPⁿ; F₂) ≅ RPnCohomologyRingModel n`
remains genuinely open (it needs singular cohomology with a cup product that
descends to a graded ring, the degree-one universal coefficient class `α`, and
the cellular/inductive nonvanishing input — none of which exist in pinned
Mathlib; see

These model facts are nonetheless the precise *consequences* requested for the
final theorem (`αⁿ ≠ 0`, `αⁿ` is the top class, `αⁿ⁺¹ = 0`): under the ring isomorphism, they transport to
`H^*(RPⁿ; F₂)`.
-/

open Polynomial

namespace SphereOddDegree

/-- The **algebraic model** `F₂[α] / (αⁿ⁺¹)` of the mod-two cohomology ring of
`RPⁿ`, realized as the genuine quotient polynomial ring `(ZMod 2)[X] ⧸ (X^(n+1))`.

This is the right-hand side of the classical isomorphism
`H^*(RPⁿ; F₂) ≅ F₂[α]/(αⁿ⁺¹)`. The isomorphism itself to topological cohomology
is *not* asserted here (it remains open); only the model and its internal
structure are built. -/
noncomputable def RPnCohomologyRingModel (n : ℕ) : Type :=
  (ZMod 2)[X] ⧸ (Ideal.span {(X : (ZMod 2)[X]) ^ (n + 1)})

noncomputable instance (n : ℕ) : CommRing (RPnCohomologyRingModel n) := by
  unfold RPnCohomologyRingModel; infer_instance

noncomputable instance (n : ℕ) : Algebra (ZMod 2) (RPnCohomologyRingModel n) := by
  unfold RPnCohomologyRingModel; infer_instance

/-- The model of the **degree-one generator** `α`: the residue class of the
indeterminate `X` in `RPnCohomologyRingModel n = (ZMod 2)[X] ⧸ (X^(n+1))`. -/
noncomputable def modelAlpha (n : ℕ) : RPnCohomologyRingModel n :=
  Ideal.Quotient.mk _ X

/-- **Power-vanishing characterization.** In the model ring `F₂[α]/(αⁿ⁺¹)`, the
power `αᵏ` vanishes exactly when `k` reaches the truncation bound, i.e.
`αᵏ = 0 ↔ n + 1 ≤ k`. Equivalently, `αᵏ ≠ 0` for all `k ≤ n` and `αᵏ = 0` for all
`k ≥ n + 1`. -/
theorem modelAlpha_pow_eq_zero_iff (n k : ℕ) :
    (modelAlpha n) ^ k = 0 ↔ n + 1 ≤ k := by
  unfold modelAlpha RPnCohomologyRingModel
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    rw [Polynomial.X_pow_dvd_iff] at h
    have := h k (by omega)
    rw [Polynomial.coeff_X_pow, ite_eq_left rfl] at this
    exact one_ne_zero this
  · intro h
    exact pow_dvd_pow X h

/-- **The truncation relation.** `αⁿ⁺¹ = 0` in the model ring — this is the
defining relation of `F₂[α]/(αⁿ⁺¹)`. -/
@[simp] theorem modelAlpha_pow_succ_eq_zero (n : ℕ) :
    (modelAlpha n) ^ (n + 1) = 0 := by
  rw [modelAlpha_pow_eq_zero_iff]

/-- **Sub-truncation nonvanishing.** `αᵏ ≠ 0` for every `k ≤ n`: every power
strictly below the truncation bound is nonzero in the model ring. -/
theorem modelAlpha_pow_ne_zero (n k : ℕ) (hk : k ≤ n) :
    (modelAlpha n) ^ k ≠ 0 := by
  rw [Ne, modelAlpha_pow_eq_zero_iff]
  omega

/-- **The top power is nonzero.** `αⁿ ≠ 0` in the model ring — the model-side
form of "`αⁿ ≠ 0`", i.e. the top class survives. -/
theorem modelAlpha_pow_top_ne_zero (n : ℕ) :
    (modelAlpha n) ^ n ≠ 0 :=
  modelAlpha_pow_ne_zero n n le_rfl

/-- `α` is nilpotent in the model ring (with `αⁿ⁺¹ = 0`). -/
theorem modelAlpha_isNilpotent (n : ℕ) : IsNilpotent (modelAlpha n) :=
  ⟨n + 1, modelAlpha_pow_succ_eq_zero n⟩

/-- **Total dimension.** The model ring `F₂[α]/(αⁿ⁺¹)` is a free `F₂`-module of
rank `n + 1`, matching `Σₖ dim_{F₂} Hᵏ(RPⁿ; F₂) = n + 1` (one class in each degree
`0, 1, …, n`). -/
theorem modelAlpha_finrank (n : ℕ) :
    Module.finrank (ZMod 2) (RPnCohomologyRingModel n) = n + 1 := by
  -- `RPnCohomologyRingModel n` is definitionally `AdjoinRoot (X^(n+1))`, whose monic
  -- power basis `1, root, …, root^n` has dimension `natDegree (X^(n+1)) = n+1`.
  have hmonic : (((X : (ZMod 2)[X]) ^ (n + 1))).Monic := monic_X_pow _
  have h := (AdjoinRoot.powerBasis' hmonic).finrank
  rw [AdjoinRoot.powerBasis'_dim, natDegree_X_pow] at h
  exact h

end SphereOddDegree
