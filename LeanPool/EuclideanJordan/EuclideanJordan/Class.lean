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
import LeanPool.EuclideanJordan.EuclideanJordan.Order
import LeanPool.EuclideanJordan.EuclideanJordan.Pattern


/-!
# The Euclidean Jordan algebra class

The abstract modules of this library built before this one — `Peirce`, `PeirceMul`,
`Orthogonal`, `Frame`, `Power`, `PowerAssoc`, `FormallyReal`, `Subalgebra`, `Block`, `Pattern`
and `Spectral` — state their hypotheses as a *tuple* drawn from
`[NonUnitalNonAssocCommRing J] [IsCommJordan J] [Module ℝ J] [IsScalarTower ℝ J J]
[IsFormallyReal J] [Module.Finite ℝ J]`, each module taking the sub-tuple it needs; or — on the
Euclidean side of `EuclideanJordan/Order.lean` and in `Spectral`'s interface section — as a
    bilinear map
`m : J →ₗ[ℝ] J →ₗ[ℝ] J` carrying `hcomm`/`hjordan`/`hassoc` as ordinary hypotheses.  (`Witness`
and `Spectral`'s concrete section state theirs over `HermitianMat` instead.)  Both abstract
vocabularies are correct and neither is a *class*, so a theorem about a Euclidean Jordan
algebra cannot be stated by naming one.

This file names one.  `EuclideanJordanAlgebra J` is a real inner-product space with a
commutative bilinear product with unit, satisfying the Jordan identity and the associativity of
the inner product — Faraut–Korányi's definition (FK III.1).

★ **Hypothesis direction.**  The class is *weaker* than the textbook definition in two
respects, which is the correct direction for an import — a theorem proved over this class
applies to the textbook setting, not the other way round.  First, finite-dimensionality is
folded into the textbook definition and is carried here as a separate `[FiniteDimensional ℝ J]`
argument.  Second, a common presentation fixes the inner product to be the trace form
`⟪x, y⟫ = tr(x ∘ y)` for the Jordan trace, whereas the class asks only that *some*
positive-definite associative inner product exist.  `inner_mul_one` below shows the gap is
smaller than it looks: any associative inner product satisfies `⟪x ∘ y, 1⟫ = ⟪x, y⟫`, so it *is*
the trace form of the linear functional `z ↦ ⟪z, 1⟫`.  It need not be the form of the *Jordan*
trace — rescaling an associative inner product by a positive constant keeps it associative —
and nothing here claims otherwise.

## The shape, and the diamond it dodges

★ The product is placed **on top of** the additive group of the inner-product space, never
alongside a second one.  Assuming `[NormedAddCommGroup J]` and `[NonUnitalNonAssocCommRing J]`
simultaneously produces two `AddCommGroup J` instances and `Module ℝ J` then fails to
synthesise; `EuclideanJordan/Bridge.lean` records that diamond and `ringOfBilinear` dodges it by
    building
the multiplicative structure on the *ambient* additive group.  This class is that dodge
promoted from a `def` to a `class`: it `extends Mul J, One J` over
`[NormedAddCommGroup J] [InnerProductSpace ℝ J]`, so only one `AddCommGroup J` is ever in play
and `instNonUnitalNonAssocCommRing` below is built from `inferInstance` on the nose.

Consequently `ringOfBilinear (jmulₗ J) mul_comm = instNonUnitalNonAssocCommRing` holds by `rfl`
(`ringOfBilinear_jmulₗ`), which is the statement that the class and the bilinear vocabulary of
`EuclideanJordan/Order.lean` are the same structure and not merely isomorphic ones.

## What finite-dimensionality is, and is not, needed for

`FiniteDimensional ℝ J` is deliberately **not** a field of the class.  It is genuinely required
downstream: `EuclideanJordan/Spectral.lean` records that its `spectral_resolution_bilinear` —
    which is
`spectral_resolution_complete` in bilinear vocabulary, and carries the same hypotheses minus the
inner product — is false without it, `ℝ[X]` satisfying every other hypothesis with no nonconstant
resolution.  So the dimension is carried as a separate instance argument at exactly the theorems
that need it, and `spectral_resolution_complete'` below is one of them.

★ It is *not* needed for formal reality.  `instIsFormallyReal` below is unconditional: pairing a
vanishing sum of squares against the unit turns `∑ᵢ ⟪xᵢ ∘ xᵢ, 1⟫` into `∑ᵢ ⟪xᵢ, xᵢ⟫` by one
application of `inner_assoc`, and a vanishing sum of nonnegative reals has vanishing terms.

This corrects the build plan on two points.  The plan derived the instance from
`EuclideanJordan/Spectral.lean`'s `isFormallyReal_of_fin` under `[FiniteDimensional ℝ J]`.  That
    lemma
cannot supply it: `isFormallyReal_of_fin` *takes formal reality as a hypothesis*, in `Fin k`
form, and does nothing but reindex it to the `Finset` form the class `IsFormallyReal` carries.
The derivation had to come from the inner product instead — and once it does, the dimension
hypothesis turns out to be unused.

## Scope

Almost all of this file is repackaging: the two restatements at the end
    (`spectral_resolution_complete'`, `peirce_add_add'`) discharge the claim
that the existing layer is reachable from the class, and are not new results.

★ Two declarations are *not* repackaging, and the file should not be described as if they were.
`inner_mul_one`, and `instIsFormallyReal` resting on it, derive formal reality from the
associative inner product, and the existing layer does not contain that derivation anywhere: it
takes formal reality as a hypothesis at every abstract site (`EuclideanJordan/Spectral.lean`'s
`isFormallyReal_of_fin` *receives* it and does nothing but reindex; `EuclideanJordan/Order.lean`'s
`orderUnitSpaceOfBilinear` receives it as `[IsFormallyReal J]`), and derives it only on the
concrete carrier, in `EuclideanJordan/Witness.lean`'s `instIsFormallyReal` for `HermitianMat d
    𝕜`.  Both new
declarations are short; the point is only that "this file contains no new mathematics" would be
false.

★ One hazard to record for later modules.  `instNonUnitalNonAssocCommRing` fires on any type
carrying `EuclideanJordanAlgebra`, and `HermitianMat d 𝕜` already carries a `Mul` — from
`EuclideanJordan/Vendor/HermitianMat/Jordan.lean`'s `scoped instance : CommMagma
(HermitianMat d 𝕜)`, whose product is `HermitianMat.symmMul`.  Nothing declares
`EuclideanJordanAlgebra (HermitianMat d 𝕜)` today, and until something does the two never meet;
if one is ever declared, that scoped instance and this class's `toMul` will both be in scope
inside `open HermMul` sections and one of them has to give way.
-/

noncomputable section

namespace EuclideanJordan

/-- A **Euclidean Jordan algebra**: a real inner-product space carrying a commutative bilinear
product with unit, satisfying the Jordan identity and the associativity of the inner product.

This is Faraut–Korányi's definition (FK III.1), weakened in the two ways the module docstring
records: finite-dimensionality is *not* a field, and the inner product is an arbitrary
associative one rather than the Jordan trace form.  Both weakenings run in the import-safe
direction. -/
class EuclideanJordanAlgebra (J : Type*) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    extends Mul J, One J where
  /-- The Jordan product is commutative. -/
  mul_comm : ∀ x y : J, x * y = y * x
  /-- The Jordan product is additive in its left argument. -/
  add_mul : ∀ x y z : J, (x + y) * z = x * z + y * z
  /-- The Jordan product is homogeneous in its left argument. -/
  smul_mul : ∀ (r : ℝ) (x y : J), (r • x) * y = r • (x * y)
  /-- `1` is a unit for the Jordan product. -/
  one_mul : ∀ x : J, (1 : J) * x = x
  /-- The Jordan identity, `x ∘ (x² ∘ y) = x² ∘ (x ∘ y)`. -/
  jordan : ∀ x y : J, x * ((x * x) * y) = (x * x) * (x * y)
  /-- The inner product is associative: `⟪x ∘ y, z⟫ = ⟪y, x ∘ z⟫`.  This is what "Euclidean"
  adds to "formally real"; `EuclideanJordan/Order.lean` carries the same condition as the hypothesis
  `hassoc`. -/
  inner_assoc : ∀ x y z : J, inner ℝ (x * y) z = inner ℝ y (x * z)

namespace EuclideanJordanAlgebra

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J] [EuclideanJordanAlgebra J]

/-- Left multiplication by `0` is `0` — the one ring axiom the class does not state, obtained
from additivity at `(0, 0, a)`. -/
theorem zero_mul' (a : J) : (0 : J) * a = 0 := by
  have h : (0 : J) * a + (0 : J) * a = (0 : J) * a + 0 := by
    rw [add_zero, ← add_mul, add_zero]
  exact add_left_cancel h

/-- The ring structure, built on the **ambient** additive group. -/
instance instNonUnitalNonAssocCommRing : NonUnitalNonAssocCommRing J :=
  { (inferInstance : AddCommGroup J), (inferInstance : Mul J) with
    left_distrib := fun a b c => by
      rw [mul_comm a (b + c), add_mul, mul_comm b a, mul_comm c a]
    right_distrib := add_mul
    zero_mul := zero_mul'
    mul_zero := fun a => by rw [mul_comm, zero_mul']
    mul_comm := mul_comm }

/-- Mathlib's Jordan class.  Its field `lmul_comm_rmul_rmul` is oriented
`a ∘ b ∘ (a ∘ a) = a ∘ (b ∘ (a ∘ a))`, which is the class's `jordan` field read through
commutativity twice. -/
instance instIsCommJordan : IsCommJordan J :=
  ⟨fun a b => by rw [mul_comm (a * b) (a * a), ← jordan a b, mul_comm (a * a) b]⟩

instance instIsScalarTower : IsScalarTower ℝ J J := ⟨smul_mul⟩

/-- Required by `Submodule`-valued and `NonUnitalSubalgebra`-valued subobject constructions
downstream; do not remove because nothing in this file uses it. -/
instance instSMulCommClass : SMulCommClass ℝ J J :=
  ⟨fun r x y => by
    change r • (x * y) = x * (r • y)
    rw [mul_comm x (r • y), smul_mul, mul_comm y x]⟩

theorem mul_one' (x : J) : x * (1 : J) = x := by rw [mul_comm, one_mul]

/-- **The inner product is a trace form.**  `⟪x ∘ y, 1⟫ = ⟪x, y⟫`: one application of
`inner_assoc` against the unit.  So the linear functional `z ↦ ⟪z, 1⟫` plays the role the
article's `tr` plays, and the inner product's positive-definiteness is available as
positive-definiteness of that form on products.  It is *not* claimed that this functional is the
Jordan trace — see the module docstring. -/
theorem inner_mul_one (x y : J) : (inner ℝ (x * y) (1 : J) : ℝ) = inner ℝ x y := by
  rw [inner_assoc x y 1, mul_one' x, real_inner_comm]

/-- **Formal reality, from the inner product.**  Unconditional on the dimension — see the
module docstring. -/
instance instIsFormallyReal : IsFormallyReal J := by
  refine ⟨fun {ι} s f hsum i hi => ?_⟩
  have hz : (∑ j ∈ s, (inner ℝ (f j) (f j) : ℝ)) = 0 := by
    have h0 : (inner ℝ (∑ j ∈ s, f j * f j) (1 : J) : ℝ) = 0 := by rw [hsum, inner_zero_left]
    rw [sum_inner] at h0
    simpa only [fun x : J => inner_mul_one x x] using h0
  have hnn : ∀ j ∈ s, (0 : ℝ) ≤ inner ℝ (f j) (f j) := fun _ _ => real_inner_self_nonneg
  exact inner_self_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg hnn).mp hz i hi)

/-- The associativity of the inner product in its other orientation, `⟪x ∘ y, z⟫ = ⟪x, y ∘ z⟫`,
obtained from the field by commuting the product. -/
theorem inner_assoc' (x y z : J) : (inner ℝ (x * y) z : ℝ) = inner ℝ x (y * z) := by
  rw [mul_comm x y, inner_assoc y x z]

end EuclideanJordanAlgebra

/-! ## The bridge to the bilinear-map vocabulary

`EuclideanJordan/Order.lean`'s Euclidean section and `EuclideanJordan/Spectral.lean`'s interface
    section state
everything over a bundled `m : J →ₗ[ℝ] J →ₗ[ℝ] J` carrying `hcomm`, `hjordan`, `hassoc` and a
`Fin k`-indexed formal-reality hypothesis.  `jmulₗ` is the class's product in that vocabulary
and the five lemmas after it are exactly that hypothesis tuple, so a consumer of
`orderUnitSpaceOfBilinear`, `inner_left_coeff`, `isArchimedean_ofBilinear`,
`isSoS_iff_exists_sq` or `spectral_resolution_bilinear` supplies them by name rather than
rebuilding them. -/

/-- The Jordan product of a `EuclideanJordanAlgebra` as a bundled bilinear map. -/
def jmulₗ (J : Type*) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [EuclideanJordanAlgebra J] : J →ₗ[ℝ] J →ₗ[ℝ] J :=
  LinearMap.mk₂ ℝ (· * ·) EuclideanJordanAlgebra.add_mul EuclideanJordanAlgebra.smul_mul
    (fun x y z => mul_add x y z) (fun r x y => mul_smul_comm r x y)

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J] [EuclideanJordanAlgebra J]

@[simp] theorem jmulₗ_apply (x y : J) : jmulₗ J x y = x * y := rfl

/-- ★ The class and `EuclideanJordan/Bridge.lean`'s `ringOfBilinear` produce the **same** ring
structure,
definitionally.  This is the precise sense in which the class does not introduce a second
multiplicative structure alongside the one the existing layer runs on. -/
theorem ringOfBilinear_jmulₗ :
    ringOfBilinear (jmulₗ J) EuclideanJordanAlgebra.mul_comm =
      EuclideanJordanAlgebra.instNonUnitalNonAssocCommRing (J := J) := rfl

theorem jmulₗ_comm (x y : J) : jmulₗ J x y = jmulₗ J y x := EuclideanJordanAlgebra.mul_comm x y

theorem jmulₗ_jordan (a b : J) :
    jmulₗ J (jmulₗ J a b) (jmulₗ J a a) = jmulₗ J a (jmulₗ J b (jmulₗ J a a)) :=
  IsCommJordan.lmul_comm_rmul_rmul a b

theorem jmulₗ_inner_assoc (x y z : J) :
    (inner ℝ (jmulₗ J x y) z : ℝ) = inner ℝ y (jmulₗ J x z) :=
  EuclideanJordanAlgebra.inner_assoc x y z

theorem jmulₗ_one_mul (y : J) : jmulₗ J 1 y = y := EuclideanJordanAlgebra.one_mul y

/-- Formal reality in the `Fin k` form `spectral_resolution_bilinear` and
`isFormallyReal_of_fin` take. -/
theorem jmulₗ_formallyReal (k : ℕ) (f : Fin k → J) (h : (∑ i, jmulₗ J (f i) (f i)) = 0)
    (i : Fin k) : f i = 0 :=
  IsFormallyReal.eq_zero_of_sum_mul_self Finset.univ f h i (Finset.mem_univ i)

/-! ## The existing layer, restated over the class -/

/-- **The spectral theorem with completeness, over the class.**  `EuclideanJordan/Spectral.lean`'s
`spectral_resolution_complete` carries the unit as an explicit hypothesis `he : ∀ y, e ∘ y = y`
because it has no `One`; the class supplies it. -/
theorem spectral_resolution_complete' [FiniteDimensional ℝ J] (x : J) :
    ∃ (n : ℕ) (c : Fin n → J) (lam : Fin n → ℝ),
      IsOrthIdemFamily c ∧ (∑ i, c i) = 1 ∧ x = ∑ i, lam i • c i :=
  spectral_resolution_complete 1 EuclideanJordanAlgebra.one_mul x

/-- **The Peirce decomposition at a single idempotent, over the class.**
`EuclideanJordan/Peirce.lean`'s
`peirce_add_add` needs no idempotency hypothesis: the three projections sum to the identity for
every `c`. -/
theorem peirce_add_add' (c y : J) : peirceOne c y + peirceHalf c y + peirceZero c y = y :=
  peirce_add_add c y

end EuclideanJordan
