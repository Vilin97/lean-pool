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
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import LeanPool.EuclideanJordan.EuclideanJordan.OrderAuto


/-!
# Solution: Koecher / Alfsen–Shultz, a unital linear order isomorphism is a Jordan automorphism

Let `J` be a finite-dimensional formally real (Euclidean) Jordan algebra with unit `e`, ordered by
its cone of sums of squares.  If a linear bijection `Φ : J ≃ₗ[ℝ] J` fixes `e` and preserves that
cone **in both directions**, then `Φ` preserves the Jordan product.  This is the classical theorem
of Koecher; see Alfsen–Shultz, *Geometry of State Spaces*, Theorem 2.80.

The content is that a Euclidean Jordan algebra's *order* determines its *multiplication*: the
order-automorphism group of the cone that fix the unit is exactly the Jordan-automorphism group.
It is the algebraic core of the Koecher–Vinberg circle of ideas, and the step by which
order-theoretic hypotheses in quantum foundations become algebraic ones.

## The vocabulary used here

Everything the statement mentions is defined below from Mathlib alone.  In particular **no Jordan
ring instance is used**: the multiplication is a bundled `ℝ`-bilinear map `m : J →ₗ[ℝ] J →ₗ[ℝ] J`,
and commutativity, the Jordan identity, formal reality and unitality are ordinary hypotheses
stated in terms of `m`.  Likewise **no order instance is used**: the cone is the predicate `IsSoS`
defined below, and `Φ`'s order-compatibility is the biconditional `horder`.

Consequently the statement elaborates against a bare `NormedAddCommGroup`/`Module ℝ`/`Module.Finite`
carrier, and a reader can check that it says what it should without consulting any library.

## What is and is not assumed

Assumed: `m` is `ℝ`-bilinear (by type), commutative (`hcomm`), satisfies the Jordan identity
`(a ∘ b) ∘ (a ∘ a) = a ∘ (b ∘ (a ∘ a))` (`hjordan`), is formally real in the finite-sum sense
(`hfr`: a finite sum of squares vanishes only if every summand's argument is `0`), and has `e` as a
two-sided unit (`he`, which is one-sided only because `m` is commutative).  `J` is finitely
generated as an `ℝ`-module.  `Φ` is `ℝ`-linear and bijective **by type**, fixes `e`, and satisfies
`IsSoS m x ↔ IsSoS m (Φ x)` for every `x`.

★ The **biconditional** in `horder` is load-bearing and is not a convenience.  The order-theoretic
characterisation of idempotents used in the proof (`c` is idempotent iff `0 ≤ c ≤ e` and no nonzero
cone element lies below both `c` and `e - c`) contains a universal quantifier over the cone, and
transporting that clause along `Φ⁻¹` consumes the reflecting direction.  A one-directional
hypothesis `IsSoS m x → IsSoS m (Φ x)` is genuinely weaker.

Not assumed: no inner product, no trace form, no continuity or boundedness of `Φ`, no associativity
or power-associativity as a hypothesis, no positive-definiteness beyond `hfr`, no `OrderedSpace`
structure, no simplicity, no classification, and no identification of `J` with a matrix algebra.

★ **The norm is never used.**  `[NormedAddCommGroup J]` appears only so that this statement matches
the one proved in the reference library, whose finite-dimensionality plumbing is set up over a
normed carrier; it is an extra hypothesis, so it makes the theorem below weaker rather than
stronger, and the argument does not touch it.

★ This is **not** the van Imhoff–Roelands theorem (arXiv:1904.09278), which works in JB-generality
and *concludes* linearity from order-isomorphy.  Here `Φ` is linear by type, and that is the whole
difference.

## This file

Repeats the definition and the theorem statement of `KoecherChallenge.lean` verbatim, imports the
reference library, and discharges the theorem from `EuclideanJordan.orderIso_preservesJordan`.  The
local `IsSoS` is the same existential as `EuclideanJordan.IsSoS`, so the bridge is definitional.
-/

namespace KoecherAlfsenShultz

open Finset

/-- **The positive cone**: `z` is a finite sum of squares of the bilinear product `m`.

The sums-of-squares reading, rather than the single-square reading, is what makes this usable as a
*definition*: closure under addition is a concatenation of index sets, whereas closure of the
single-square set under addition is a theorem requiring the spectral decomposition.  Over a
Euclidean Jordan algebra the two predicates coincide, but that is a result, not a convention.

The empty sum is allowed (`k = 0`), so `0` lies in the cone. -/
def IsSoS {J : Type*} [AddCommGroup J] [Module ℝ J] (m : J →ₗ[ℝ] J →ₗ[ℝ] J) (z : J) : Prop :=
  ∃ (k : ℕ) (f : Fin k → J), z = ∑ i, m (f i) (f i)

variable {J : Type*} [NormedAddCommGroup J] [Module ℝ J] [Module.Finite ℝ J]

/-- **Koecher / Alfsen–Shultz.**  On a finite-dimensional formally real Jordan algebra, a linear
bijection that fixes the unit and preserves the cone of sums of squares in both directions
preserves the Jordan product — that is, it is a Jordan automorphism.

The hypotheses, in order: `hcomm` and `hjordan` make the bilinear map `m` a Jordan multiplication;
`hfr` is formal reality (`∑ᵢ m (f i) (f i) = 0 → ∀ i, f i = 0`), which together with finite
dimensionality makes `J` Euclidean; `he` says `e` is the unit; `hunital` and `horder` say `Φ` is a
unital order isomorphism for the cone `IsSoS m`.  The conclusion `Φ (m x y) = m (Φ x) (Φ y)` holds
for all `x y : J`.

Reference: M. Koecher; see also E. M. Alfsen and F. W. Shultz, *Geometry of State Spaces of
Operator Algebras*, Birkhäuser 2003, Theorem 2.80.

For what is and is not assumed — in particular why the biconditional in `horder` cannot be weakened
to an implication, and why the norm on `J` is inert — see the module docstring above. -/
theorem orderIso_preservesJordan (m : J →ₗ[ℝ] J →ₗ[ℝ] J)
    (hcomm : ∀ x y : J, m x y = m y x)
    (hjordan : ∀ a b : J, m (m a b) (m a a) = m a (m b (m a a)))
    (hfr : ∀ (k : ℕ) (f : Fin k → J), (∑ i, m (f i) (f i)) = 0 → ∀ i, f i = 0)
    (e : J) (he : ∀ y : J, m e y = y)
    (Φ : J ≃ₗ[ℝ] J) (hunital : Φ e = e)
    (horder : ∀ x : J, IsSoS m x ↔ IsSoS m (Φ x)) (x y : J) :
    Φ (m x y) = m (Φ x) (Φ y) :=
  EuclideanJordan.orderIso_preservesJordan m hcomm hjordan hfr e he Φ hunital horder x y

end KoecherAlfsenShultz
