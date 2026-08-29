/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
import LeanPool.CompositionAlgebras.Composition.Defs


/-!
# The Cayley–Dickson doubling, internally

Let `C` be a Euclidean composition algebra, `A ⊆ C` a **composition subalgebra** (a submodule
containing `1` and closed under multiplication and conjugation), and `u ⊥ A` a unit vector.
This file proves the three multiplication rules that make `A ⊕ A u` the Cayley–Dickson double
of `A`:

* `mul_mul_unit` — `a (b u) = (b a) u`
* `unit_mul_mul` — `(a u) b = (a b*) u`
* `unit_mul_unit` — `(a u)(b u) = -(b* a)`

together with the orthogonality `ip_mul_unit` (`⟪a u, b⟫ = 0`) that makes the sum direct.

## Why this file is not the plan's `Composition/CayleyDickson.lean`

The build plan proposed constructing `CD C := C × C` as a *new* algebra and then transporting
it into `C`. That is not what Hurwitz's argument needs and it is the expensive half: it means
building a second `NonAssocRing` instance, a second form, and an isomorphism onto a subalgebra.
Everything downstream instead needs the doubling *inside* `C`, where the composition law is
already available and where `A ⊕ A u` is a submodule rather than a new type. So the doubling
is done internally, and no `CD` type former is built.

★ **The rules need no associativity of `A`.** The plan's §6 flagged the termination step
("the doubling stops at dimension 8 because `CD D` composes only when `D` is associative") as
the one it had not written out to the level where a Lean gap would show. It was right to flag
it, and the shape of the gap is this: the three rules above hold for *any* composition
subalgebra `A`, associative or not, so **closure of `A ⊕ A u` is not where the dimension bound
comes from**. What associativity actually gates is the *norm* on `A ⊕ A u`, and inside `C` the
norm is multiplicative for free. The bound therefore arrives as a contrapositive — if `A` is
not associative there is no unit vector orthogonal to it at all — which is
`Composition/Hurwitz.lean`, not this file.

## Main statements

The named results are the four listed above plus their inputs: `cstar_mul_mul`
(`x* (x y) = N x • y`) and `mul_mul_cstar` (`(y x) x* = N x • y`) with their polarisations
`cstar_mul_mul_polar` / `mul_mul_cstar_polar`, and the two commutation rules
`unit_comm` (`a u = u a*`) and `unit_mul_left` (`u (a* y) = a (u y)`).

## Scope

Substrate for the two Hurwitz theorems. It states neither of them.
-/

namespace CompositionAlgebra

universe u

variable {C : Type u} [NonAssocRing C] [Module ℝ C]
  [IsScalarTower ℝ C C] [SMulCommClass ℝ C C] [CompositionAlgebra C] [Nontrivial C]

/-! ### The two Kirmse identities and their polarisations -/

omit [Nontrivial C] in
/-- `x* (x y) = N x • y`. Immediate from left alternativity and `sq_eq`. -/
theorem cstar_mul_mul (x y : C) : cstar x * (x * y) = (nf x) • y := by
  have h : cstar x * (x * y) = (2 * ip x 1) • (x * y) - x * (x * y) := by
    simp [cstar_apply, sub_mul, smul_mul_assoc]
  rw [h, left_alternative, sq_eq x]
  simp only [sub_mul, smul_mul_assoc, one_mul]
  module

omit [Nontrivial C] in
/-- `(y x) x* = N x • y`. Immediate from right alternativity and `sq_eq`. -/
theorem mul_mul_cstar (x y : C) : (y * x) * cstar x = (nf x) • y := by
  have h : (y * x) * cstar x = (2 * ip x 1) • (y * x) - (y * x) * x := by
    simp [cstar_apply, mul_sub, mul_smul_comm]
  rw [h, right_alternative, sq_eq x]
  simp only [mul_sub, mul_smul_comm, mul_one]
  module

omit [Nontrivial C] in
/-- Polarisation of `cstar_mul_mul`: `x* (w y) + w* (x y) = 2⟪x,w⟫ • y`. -/
theorem cstar_mul_mul_polar (x w y : C) :
    cstar x * (w * y) + cstar w * (x * y) = (2 * ip x w) • y := by
  have h := cstar_mul_mul (x + w) y
  simp only [cstar_add, add_mul, mul_add, nf_add] at h
  have h1 := cstar_mul_mul x y
  have h2 := cstar_mul_mul w y
  rw [h1, h2] at h
  linear_combination (norm := module) h

omit [Nontrivial C] in
/-- Polarisation of `mul_mul_cstar`: `(y x) w* + (y w) x* = 2⟪x,w⟫ • y`. -/
theorem mul_mul_cstar_polar (x w y : C) :
    (y * x) * cstar w + (y * w) * cstar x = (2 * ip x w) • y := by
  have h := mul_mul_cstar (x + w) y
  simp only [cstar_add, mul_add, add_mul, nf_add] at h
  have h1 := mul_mul_cstar x y
  have h2 := mul_mul_cstar w y
  rw [h1, h2] at h
  linear_combination (norm := module) h

/-! ### Composition subalgebras -/

/-- A **composition subalgebra**: a submodule containing the unit and closed under the product
and the conjugation. Its own composition law is inherited from `C`. -/
structure IsCompSubalgebra (A : Submodule ℝ C) : Prop where
  /-- The subalgebra contains the unit. -/
  one_mem : (1 : C) ∈ A
  /-- The subalgebra is closed under multiplication. -/
  mul_mem : ∀ ⦃a : C⦄, a ∈ A → ∀ ⦃b : C⦄, b ∈ A → a * b ∈ A
  /-- The subalgebra is closed under conjugation. -/
  cstar_mem : ∀ ⦃a : C⦄, a ∈ A → cstar a ∈ A

namespace IsCompSubalgebra

variable {A : Submodule ℝ C} (hA : IsCompSubalgebra A) {u : C}
  (hu : ∀ a ∈ A, ip u a = 0) (hnu : nf u = 1)

include hA hu

omit [Nontrivial C] in
/-- The doubling vector is imaginary: it is orthogonal to `1 ∈ A`. -/
theorem isPure_unit : IsPure u := by
  have := hu 1 hA.one_mem
  simpa [IsPure, ip_symm u 1] using this

include hnu

omit [Nontrivial C] in
/-- `u * u = -1`. -/
theorem unit_sq : u * u = -(1 : C) := by
  have := sq_of_pure (hA.isPure_unit hu)
  rw [hnu] at this
  simpa using this

omit hnu

omit [Nontrivial C] in
/-- `A ⊥ A u`: the doubled part is orthogonal to the original. This is what makes the sum
`A ⊕ A u` direct. -/
theorem ip_mul_unit {a : C} (ha : a ∈ A) {b : C} (hb : b ∈ A) : ip (a * u) b = 0 := by
  rw [ip_mul_adj_left]
  exact hu _ (hA.mul_mem (hA.cstar_mem ha) hb)

omit [Nontrivial C] in
/-- Every element of `A u` is imaginary. -/
theorem isPure_mul_unit {a : C} (ha : a ∈ A) : IsPure (a * u) :=
  hA.ip_mul_unit hu ha hA.one_mem

omit [Nontrivial C] in
/-- `a u = u a*` for `a ∈ A`: the doubling vector conjugates `A`. -/
theorem unit_comm {a : C} (ha : a ∈ A) : a * u = u * cstar a := by
  have h := mul_mul_cstar_polar (C := C) u a 1
  rw [one_mul, one_mul, hu a ha] at h
  rw [cstar_of_pure (hA.isPure_unit hu)] at h
  simp only [mul_neg] at h
  linear_combination (norm := module) -h

/-- `u (a* y) = a (u y)` for `a ∈ A`: moving `A` across the doubling vector on the left. -/
theorem unit_mul_left {a : C} (ha : a ∈ A) (y : C) :
    u * (cstar a * y) = a * (u * y) := by
  have h := cstar_mul_mul_polar (C := C) u (cstar a) y
  rw [hu _ (hA.cstar_mem ha), cstar_cstar] at h
  rw [cstar_of_pure (hA.isPure_unit hu)] at h
  simp only [neg_mul] at h
  linear_combination (norm := module) -h

/-- **First Cayley–Dickson rule**: `a (b u) = (b a) u`. -/
theorem mul_mul_unit {a : C} (ha : a ∈ A) {b : C} (hb : b ∈ A) :
    a * (b * u) = (b * a) * u := by
  rw [hA.unit_comm hu hb, ← hA.unit_mul_left hu ha (cstar b), ← cstar_mul,
    ← hA.unit_comm hu (hA.mul_mem hb ha)]

/-- **Second Cayley–Dickson rule**: `(a u) b = (a b*) u`. Note `a` is arbitrary: only
`b ∈ A` is used. -/
theorem unit_mul_mul (a : C) {b : C} (hb : b ∈ A) :
    (a * u) * b = (a * cstar b) * u := by
  have h := mul_mul_cstar_polar (C := C) u (cstar b) a
  rw [hu _ (hA.cstar_mem hb), cstar_cstar] at h
  rw [cstar_of_pure (hA.isPure_unit hu)] at h
  simp only [mul_neg] at h
  linear_combination (norm := module) h

include hnu

omit [Nontrivial C] hA hu in
/-- `⟪u, b u⟫ = ⟪1, b⟫`. -/
theorem ip_unit_mul_unit (b : C) : ip u (b * u) = ip 1 b := by
  have h := ip_exchange (C := C) 1 u b u
  simp only [one_mul] at h
  rw [ip_symm (b * u) u, ← nf_eq_ip, hnu] at h
  linarith

/-- **Third Cayley–Dickson rule**: `(a u)(b u) = -(b* a)`. -/
theorem unit_mul_unit {a : C} (ha : a ∈ A) {b : C} (hb : b ∈ A) :
    (a * u) * (b * u) = -(cstar b * a) := by
  have h := mul_mul_cstar_polar (C := C) u (b * u) a
  rw [ip_unit_mul_unit hnu b, cstar_of_pure (hA.isPure_mul_unit hu hb),
    cstar_of_pure (hA.isPure_unit hu), hA.mul_mul_unit hu ha hb] at h
  have hsq : ((b * a) * u) * u = -(b * a) := by
    rw [right_alternative, hA.unit_sq hu hnu]
    simp
  rw [mul_neg, mul_neg, hsq] at h
  have hb' : cstar b * a = (2 * ip b 1) • a - b * a := by
    simp [cstar_apply, sub_mul, smul_mul_assoc]
  rw [hb', ip_symm b 1]
  linear_combination (norm := module) -h

end IsCompSubalgebra

end CompositionAlgebra
