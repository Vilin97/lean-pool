/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
module

public import LeanPool.EuclideanJordan.EuclideanJordan.PeirceMul



/-!
# Orthogonal idempotents, and the simultaneous-diagonalisation field

This file derives, at the generality of an arbitrary idempotent, the Faraut–Korányi
simultaneous-diagonalisation fact:

> an element **scalar on `range q`** and an element of **`J₂(q)`** operator-commute.

Here `q` is any idempotent `c`, "scalar on `range c`" is `a = μ • c + a₀` with `a₀ ∈ J₀(c)`,
and `J₂(c)` is `J₁(c)` in the eigenvalue naming of `EuclideanJordan/Peirce.lean`. The proof is four
lines, because `EuclideanJordan/PeirceMul.lean` already did the work: `L_c` commutes with `L_b` for
`b ∈ J₁(c)`, and `L_{a₀}` commutes with `L_b` for `a₀ ∈ J₀(c)`, so `L_a = μ L_c + L_{a₀}`
commutes with `L_b` by linearity.

The interface's `q` is a *rank-two* idempotent `pᵢ + pⱼ` built from a Jordan frame, so
`add_idem_of_orthogonal` below supplies the shape: a sum of two orthogonal idempotents is an
idempotent, and then the general result applies.

## Scope

The frame-level version of the statement quantifies over a rank-two `q = pᵢ + pⱼ` built from a
Jordan frame; `add_idem_of_orthogonal` below supplies the shape that reduces it to the general
result — a sum of two orthogonal idempotents is an idempotent —
and `EuclideanJordan/Frame.lean` assembles it (`opCommute_scalarOn_frame`).

## References

* Faraut and Korányi, *Analysis on Symmetric Cones*, Ch. IV.
-/

@[expose] public section

namespace EuclideanJordan

section Orthogonal

variable {J : Type*} [NonUnitalNonAssocCommRing J] [IsCommJordan J] [Module ℝ J]

omit [IsCommJordan J] [Module ℝ J] in
/-- **A sum of two orthogonal idempotents is an idempotent.** Pure expansion — this needs
only commutativity and distributivity, not the Jordan identity. -/
theorem add_idem_of_orthogonal {p q : J} (hp : p * p = p) (hq : q * q = q) (hpq : p * q = 0) :
    (p + q) * (p + q) = p + q := by
  have hqp : q * p = 0 := by rw [mul_comm]; exact hpq
  rw [add_mul, mul_add, mul_add, hp, hq, hpq, hqp]
  abel

/-- **Orthogonal idempotents operator-commute.** Not merely `p ∘ q = 0`: the multiplication
operators themselves commute, which is what every simultaneous-diagonalisation argument
needs. Immediate from `opCommute_eigen_one_zero`, since `p ∈ J₁(p)` and `q ∈ J₀(p)`. -/
theorem opCommute_of_orthogonal {p q : J} (hp : p * p = p) (hpq : p * q = 0) (w : J) :
    p * (q * w) = q * (p * w) :=
  opCommute_eigen_one_zero hp hp hpq w

section ScalarTower

variable [IsScalarTower ℝ J J]

/-- **Faraut–Korányi simultaneous diagonalisation, at single-idempotent generality.**

If `a` is scalar on `range c` — that is, `a = μ • c + a₀` with `a₀` in the `0`-Peirce
component — and `b` lies in the `1`-Peirce component `J₂(c)`, then `L_a` and `L_b` commute.

It is a consequence of the Jordan identity alone. -/
theorem opCommute_scalarOn {c a a₀ b : J} {μ : ℝ} (hc : c * c = c)
    (ha : a = μ • c + a₀) (ha₀ : c * a₀ = 0) (hb : c * b = b) (w : J) :
    a * (b * w) = b * (a * w) := by
  have hcb : c * (b * w) = b * (c * w) := mul_comm_of_eigen_one hc hb w
  have h0 : a₀ * (b * w) = b * (a₀ * w) := (opCommute_eigen_one_zero hc hb ha₀ w).symm
  subst ha
  rw [add_mul, add_mul, mul_add, smul_mul_assoc, smul_mul_assoc, hcb, h0, mul_smul_comm']

/-- The interface's actual shape: `c` is the rank-two idempotent `p + q` built from two
orthogonal idempotents of a Jordan frame. -/
theorem opCommute_scalarOn_pair {p q a a₀ b : J} {μ : ℝ} (hp : p * p = p) (hq : q * q = q)
    (hpq : p * q = 0) (ha : a = μ • (p + q) + a₀) (ha₀ : (p + q) * a₀ = 0)
    (hb : (p + q) * b = b) (w : J) : a * (b * w) = b * (a * w) :=
  opCommute_scalarOn (add_idem_of_orthogonal hp hq hpq) ha ha₀ hb w

end ScalarTower

end Orthogonal

end EuclideanJordan
