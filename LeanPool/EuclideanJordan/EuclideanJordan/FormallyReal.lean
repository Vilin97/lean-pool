/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
module

public import LeanPool.EuclideanJordan.EuclideanJordan.PowerAssoc



/-!
# Formal reality, and the absence of nilpotents

A Euclidean Jordan algebra is a finite-dimensional real Jordan algebra that is **formally
real**: a sum of squares vanishes only if every summand does. This file adds that hypothesis
as a mixin and draws the consequence the spectral theorem needs first —
**`nilpotent ⟹ zero`**.

The nilpotence result is the first place in this development where **Albert's theorem does
real work**: `x^{k+1} ∘ x^{k+1} = x^{2k+2}` is a *product* identity, so without
`jpow_mul_jpow` there is no way to turn "some power vanishes" into "a square vanishes",
which is the only thing formal reality can see.

## What is here

* `IsFormallyReal` — the mixin, stated over a `Finset` sum so that it is the usual
  many-summand condition rather than the two-summand special case.
* `eq_zero_of_mul_self_eq_zero` — the one-summand case: `x ∘ x = 0 ⟹ x = 0`.
* `eq_zero_of_jpow_eq_zero` — **no nilpotents**: if any power of `x` vanishes, `x = 0`.

## What is not

No trace form, no inner product, no finite-dimensionality, and **no spectral theorem**. The
spectral theorem additionally needs `ℝ[x]` to be finite-dimensional and reduced, and then the
classification of finite-dimensional reduced commutative `ℝ`-algebras. Formal reality is what
supplies "reduced"; the rest is not built.

★ **The hypothesis has a carrier.**  `EuclideanJordan/Witness.lean` carries
`instIsFormallyReal : IsFormallyReal (HermitianMat d 𝕜)`, so both theorems below are live on
`H_d(𝕜)` (`hermitian_eq_zero_of_jpow_eq_zero`); neither is conditional on a premise nothing
satisfies.

★ The proof needed nothing new — `inner_self_nonneg` and `InnerProductCore.definite` are
vendored and `symmMul_self` says the Jordan square *is* the matrix square. What was missing was
the application, which is the third time in this arc that a residue named a hypothesis and a
conclusion whose connecting lemma was already in the tree (after row 35 and the FK fields).
**When a file's own docstring declares an exposure, try to close it before writing the sentence
that documents it.**
-/

@[expose] public section

namespace EuclideanJordan

open Finset

/-- **Formal reality.** A sum of squares vanishes only if every summand does. Stated over an
arbitrary `Finset` index rather than for two elements: the two-summand version does not
obviously imply the general one in a non-associative setting, because `x ∘ x + y ∘ y` need
not itself be a square. -/
class IsFormallyReal (J : Type*) [Mul J] [AddCommMonoid J] : Prop where
  /-- A vanishing sum of squares has vanishing summands. -/
  eq_zero_of_sum_mul_self : ∀ {ι : Type} (s : Finset ι) (f : ι → J),
    ∑ i ∈ s, f i * f i = 0 → ∀ i ∈ s, f i = 0

section Basic

variable {J : Type*} [NonUnitalNonAssocCommRing J] [IsFormallyReal J]

/-- The one-summand case: an element whose square vanishes is zero. -/
theorem eq_zero_of_mul_self_eq_zero {x : J} (h : x * x = 0) : x = 0 := by
  have := IsFormallyReal.eq_zero_of_sum_mul_self ({0} : Finset ℕ) (fun _ => x) (by simpa using h)
  exact this 0 (Finset.mem_singleton_self 0)

end Basic

section Nilpotent

variable {J : Type*} [NonUnitalNonAssocCommRing J] [IsCommJordan J] [Module ℝ J]
  [IsFormallyReal J]

omit [IsFormallyReal J] in
/-- If one power vanishes, every higher power does. Uses Albert's theorem to split
`x^{m+1} = x^{n+1} ∘ x^{m−n}`. -/
theorem jpow_eq_zero_of_le {x : J} {n : ℕ} (h : jpow x n = 0) {m : ℕ} (hm : n ≤ m) :
    jpow x m = 0 := by
  rcases Nat.eq_or_lt_of_le hm with rfl | hlt
  · exact h
  · have hsplit : jpow x n * jpow x (m - n - 1) = jpow x m := by
      rw [jpow_mul_jpow]
      congr 1
      omega
    rw [← hsplit, h, zero_mul]

/-- **A formally real Jordan algebra has no nilpotents.** If any power of `x` vanishes then
`x = 0`.

★ This is where Albert's theorem earns its place. Formal reality can only see *squares*, and
turning "some power vanishes" into "a square vanishes" is exactly the product identity
`jpow_mul_jpow` supplies. In this file's indexing (`jpow x n = x^{n+1}`) the descent from
`jpow x (k+1) = 0` runs: `jpow x (k+k+1) = 0` by `jpow_eq_zero_of_le`, that element **is**
`jpow x k * jpow x k`, so formal reality gives `jpow x k = 0`, and the index has strictly
dropped. -/
theorem eq_zero_of_jpow_eq_zero {x : J} : ∀ (n : ℕ), jpow x n = 0 → x = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro h
      match n with
      | 0 => simpa using h
      | (k + 1) =>
          have hsq : jpow x k * jpow x k = 0 := by
            rw [jpow_mul_jpow]
            exact jpow_eq_zero_of_le h (by omega)
          exact ih k (by omega) (eq_zero_of_mul_self_eq_zero hsq)

end Nilpotent

end EuclideanJordan
