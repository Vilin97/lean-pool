/-
Copyright (c) 2026 Dillon Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dillon Ryan
-/

import LeanPool.LehmerE10.Defs
import LeanPool.LehmerE10.Mahler
import Mathlib.GroupTheory.OrderOfElement

/-!
# the finite contrast: the E₈ Coxeter element has order 30.
The E-series Coxeter elements cross a phase boundary at rank 10.  For the *finite* root
system E₈ the Coxeter element is torsion — its order is the Coxeter number `h = 30`, and
its spectrum consists of the primitive 30th roots of unity (the exponents of E₈ are
exactly the totatives of 30).  Two ranks later, at the hyperbolic E₁₀, the Coxeter
element is a Salem matrix of infinite order (`coxeterE10_infinite_order`) whose spectral
radius is Lehmer's number.
This file pins the finite side by kernel computation, in the same simple-reflection
convention as `Defs.lean`:
* `coxeterE8_pow_thirty` : `coxeterE8 ^ 30 = 1`;
* `orderOf_coxeterE8` : the order is exactly `30` (no proper power at `30/2, 30/3, 30/5`
  is the identity).
So the pair (E₈, E₁₀) realizes both sides of Kronecker's dichotomy for integer matrices:
spectrum on the unit circle ⟹ roots of unity ⟹ finite order, versus one eigenvalue off
the circle ⟹ infinite order — with Lehmer's number as the first exit.
-/

open Matrix

namespace LehmerE10

/-- The Cartan matrix of **E₈**: nodes `0–6` form an A₇ chain and node `7` is attached to
node `2` — the same labelling convention as `cartanE10`, truncated to the finite diagram
(arm lengths `2, 1, 4` off the branch node `2`). -/
def cartanE8 : Matrix (Fin 8) (Fin 8) ℤ :=
  !![ 2, -1,  0,  0,  0,  0,  0,  0;
     -1,  2, -1,  0,  0,  0,  0,  0;
      0, -1,  2, -1,  0,  0,  0, -1;
      0,  0, -1,  2, -1,  0,  0,  0;
      0,  0,  0, -1,  2, -1,  0,  0;
      0,  0,  0,  0, -1,  2, -1,  0;
      0,  0,  0,  0,  0, -1,  2,  0;
      0,  0, -1,  0,  0,  0,  0,  2]

/-- The simple reflection `sᵢ` of the E₈ Weyl group on the root lattice:
`(sᵢ)ⱼₖ = δⱼₖ − δⱼᵢ aᵢₖ`. -/
def simpleReflectionE8 (i : Fin 8) : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun j k => (if j = k then 1 else 0) - (if j = i then cartanE8 i k else 0)

/-- A Coxeter element of the E₈ Weyl group: the product `s₀ s₁ ⋯ s₇`. -/
def coxeterE8 : Matrix (Fin 8) (Fin 8) ℤ :=
  ((List.finRange 8).map simpleReflectionE8).prod

/-- The Coxeter element `s₀ s₁ ⋯ s₇`, evaluated (kernel computation below). -/
def coxeterE8Mat : Matrix (Fin 8) (Fin 8) ℤ :=
  !![ 0, 0, 1, 0, 0, 0, -1, -1;
      1, 0, 1, 0, 0, 0, -1, -1;
      0, 1, 1, 0, 0, 0, -1, -1;
      0, 0, 1, 0, 0, 0, -1,  0;
      0, 0, 0, 1, 0, 0, -1,  0;
      0, 0, 0, 0, 1, 0, -1,  0;
      0, 0, 0, 0, 0, 1, -1,  0;
      0, 0, 1, 0, 0, 0,  0, -1]

theorem coxeterE8_eq : coxeterE8 = coxeterE8Mat := by decide

/-- `coxeterE8 ^ 30 = 1`: the E₈ Coxeter element is torsion, of order dividing the
Coxeter number `h = 30`.  Kernel computation, staged as `((c⁵)³)²`. -/
theorem coxeterE8_pow_thirty : coxeterE8 ^ 30 = 1 := by
  rw [coxeterE8_eq, show (30 : ℕ) = 5 * 3 * 2 from by norm_num, pow_mul, pow_mul]
  decide

/-- **The order of the E₈ Coxeter element is exactly the Coxeter number 30**: the powers
`30/2 = 15`, `30/3 = 10`, `30/5 = 6` are not the identity (kernel computations), so no
proper divisor of `30` kills it. -/
theorem orderOf_coxeterE8 : orderOf coxeterE8 = 30 := by
  refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) coxeterE8_pow_thirty ?_
  intro p hp hdvd
  have h2p : 2 ≤ p := hp.two_le
  have hle : p ≤ 30 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases p <;>
    first
      | (rw [coxeterE8_eq, show (30 : ℕ) / 2 = 5 * 3 from by norm_num, pow_mul]; decide)
      | (rw [coxeterE8_eq, show (30 : ℕ) / 3 = 5 * 2 from by norm_num, pow_mul]; decide)
      | (rw [coxeterE8_eq, show (30 : ℕ) / 5 = 3 * 2 from by norm_num, pow_mul]; decide)
      | exact absurd hdvd (by decide)
      | exact absurd hp (by decide)

end LehmerE10

#print axioms LehmerE10.coxeterE8_pow_thirty
#print axioms LehmerE10.orderOf_coxeterE8
