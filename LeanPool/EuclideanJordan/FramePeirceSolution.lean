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

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Data.Sym.Sym2
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import LeanPool.EuclideanJordan.EuclideanJordan.FramePeirceMul



/-!
# The Peirce decomposition of a Euclidean Jordan algebra relative to a Jordan frame

A **Euclidean Jordan algebra** is a real inner-product space `J` carrying a commutative bilinear
product `∘` with unit `1`, satisfying the Jordan identity `x ∘ (x² ∘ y) = x² ∘ (x ∘ y)` and the
associativity of the inner product `⟪x ∘ y, z⟫ = ⟪y, x ∘ z⟫` (Faraut–Korányi, *Analysis on
Symmetric Cones*, Definition III.1.1).  `EuclideanJordanAlgebra` below is exactly that, written
as a class.

An idempotent `c` (`c ∘ c = c`) is **primitive** when it is nonzero and cannot be split: the only
idempotents `d` of the Peirce subalgebra `J₂(c) = {x | c ∘ x = x}` are `0` and `c`.  A **Jordan
frame** is a family `p₁, …, pₙ` of pairwise-orthogonal (`pᵢ ∘ pⱼ = 0` for `i ≠ j`) primitive
idempotents that is complete (`∑ᵢ pᵢ = 1`).

Left multiplication `L_c : x ↦ c ∘ x` by an idempotent is diagonalisable with eigenvalues `1`,
`½` and `0`; that is the Peirce decomposition at a single idempotent.  For a Jordan frame the
operators `L_{p₁}, …, L_{pₙ}` are simultaneously diagonalisable, and the surviving joint
eigenspaces — the **blocks** — are indexed by *unordered pairs* of indices:

* `V_{ii} := {x | pᵢ ∘ x = x}`, the `1`-eigenspace of `L_{pᵢ}`;
* `V_{ij} := {x | pᵢ ∘ x = ½ • x ∧ pⱼ ∘ x = ½ • x}` for `i ≠ j`, the joint `½`-eigenspace of
  `L_{pᵢ}` and `L_{pⱼ}`.

This file states the two theorems that turn that list of subspaces into a decomposition of `J`:

1. **`frameBlock_isInternal`** — the blocks are an internal direct sum, `J = ⨁_{i ≤ j} V_{ij}`.
   Equivalently: they are independent and they span.
2. **`finrank_frameBlock_diag`** — each diagonal block is a line, `dim_ℝ V_{ii} = 1`.  (It is in
   fact `ℝ ∙ pᵢ`, but the dimension is the form the coordinatization consumes.)

Together these are Faraut–Korányi Theorem IV.2.1.  They are the starting point of the
Jordan–von Neumann–Wigner classification: once `J = ⨁_{i ≤ j} V_{ij}` with one-dimensional
diagonal, the off-diagonal blocks `V_{ij}` all carry a common composition algebra structure and
`J` is recognised as a matrix algebra `H_n(K)`.  The multiplication table of the blocks
(`V_{ij} ∘ V_{jk} ⊆ V_{ik}`, `V_{ij} ∘ V_{kl} = 0` for disjoint index pairs, and so on) is the
next step and is *not* stated here.

## Why the blocks are indexed by `Sym2 (Fin n)`

`V_{ij}` and `V_{ji}` are literally the same subspace — the defining conditions are a conjunction
that is symmetric in `i` and `j`, and the eigenvalue `blockCoef i j` is symmetric too.  So the
honest index set for the family is the type of *unordered* pairs `Sym2 (Fin n)`, and the direct
sum runs over it with no double counting.  That is what "`⨁_{i ≤ j}`" means in the informal
statement, and using `Sym2` rather than `{q : Fin n × Fin n // q.1 ≤ q.2}` avoids having to
choose a representative.  `frameBlockRaw` is the ordered-pair family, `frameBlockRaw_comm` is its
symmetry, and `frameBlock` is the descent of the former along the latter; `frameBlock_mk`
(`frameBlock F s(i, j) = frameBlockRaw F i j`, by `rfl`) is the bridge a reader should use to see
what the statement says at a concrete pair of indices.

`DirectSum.IsInternal (frameBlock F)` is Mathlib's predicate saying that the canonical map
`⨁_{s : Sym2 (Fin n)} V_s → J` is bijective — that is, independence *and* spanning, which is the
full strength of the decomposition and not merely the spanning half.

## What is and is not assumed

Assumed for both theorems: `J` is a real inner-product space (`NormedAddCommGroup` plus
`InnerProductSpace ℝ`) carrying `EuclideanJordanAlgebra`, and `F : JordanFrame J n` is a Jordan
frame of some cardinality `n`, carried as **data**.

★ **Finite-dimensionality is assumed only for the second theorem.**  `frameBlock_isInternal`
holds with no dimension hypothesis at all; `finrank_frameBlock_diag` takes
`[FiniteDimensional ℝ J]`, because the proof that a primitive idempotent's Peirce subalgebra is a
line runs the spectral theorem inside that subalgebra, and the spectral theorem is false without
the dimension hypothesis (`ℝ[X]` satisfies every other hypothesis with no nonconstant
resolution).

★ **The inner product is an arbitrary associative one, not the trace form.**  Faraut–Korányi fix
`⟪x, y⟫ = tr(x ∘ y)`; the class below asks only that *some* positive-definite associative inner
product exist.  That is the weaker hypothesis, so the theorems below are the stronger statements.
Positive-definiteness is not stated as a field: it is already part of `InnerProductSpace ℝ J`.
Formal reality is not a hypothesis either — it follows from the associativity of the inner
product, by pairing a vanishing sum of squares against `1`.

★ **Primitivity is a formal hypothesis of both theorems; only the second one spends it.**
`JordanFrame` carries primitivity, so `frameBlock_isInternal` assumes it formally even though its
proof never uses it.  The stronger statement — that the blocks of a merely orthogonal complete
idempotent family already decompose `J` — is **not formalized here**.  It is
`dim V_{ii} = 1` that cashes primitivity out, and that is why the two theorems are stated
together: the decomposition is useless for classification without the one-dimensionality.

★ **No claim is made about the rank of `J`.**  A frame is carried as data of a given cardinality
`n`; that `n` equals the rank of `J`, or that all frames have the same cardinality
(Faraut–Korányi IV.2.5, conjugacy of frames), is neither assumed nor concluded here.  Do not read
`frameBlock_isInternal` as a statement about `rank J`.

Not assumed: no associativity or power-associativity as a hypothesis, no simplicity, no
classification, no identification of `J` with a matrix algebra, no ordered-space structure, no
continuity beyond what the norm gives for free, and no `n ≥ 3`.

## The vocabulary used here

Everything the two statements mention is defined below from Mathlib alone: the class
`EuclideanJordanAlgebra`, the predicates `IsOrthIdemFamily` and `IsPrimitive`, the structure
`JordanFrame`, the eigenspace `eigSub`, the eigenvalue `blockCoef`, and the block families
`frameBlockRaw` and `frameBlock`.  Nothing else is imported beyond core Mathlib.

## This file

Repeats the definitions and the two theorem statements of `FramePeirceChallenge.lean` verbatim,
imports the reference library, and discharges them from `EuclideanJordan.frameBlock_isInternal`
(`EuclideanJordan/FramePeirce.lean`) and `EuclideanJordan.finrank_frameBlock_diag`
(`EuclideanJordan/FramePeirceMul.lean`).

The bridge is short by construction.  The local class `EuclideanJordanAlgebra` carries the same
fields as `EuclideanJordan.EuclideanJordanAlgebra`, so an instance of the library's class is
assembled from ours field by field, with `toMul` and `toOne` taken from ours — which is what
makes the two `*` and the two `1` the *same* operations rather than merely isomorphic ones.  The
local `IsOrthIdemFamily`, `IsPrimitive`, `JordanFrame`, `eigSub`, `blockCoef`, `frameBlockRaw`
and `frameBlock` are then definitionally the library's, so each proof is a single `exact` once
the instance and the frame have been transported.

★ The library instance is introduced *inside* the proof bodies with `let`, never at the top
level of this file.  That is deliberate.  An ambient `EuclideanJordan.EuclideanJordanAlgebra J`
brings its derived `NonUnitalNonAssocCommRing J` into scope, and `Submodule ℝ J` would then
elaborate its `AddCommMonoid J` argument through the ring rather than through the norm; the
resulting type is definitionally equal to, but not syntactically the same as, the one the
challenge file states.  The contract here is that the two files' declaration types agree on the
nose, so the extra instance is kept out of every statement.
-/

@[expose] public section

noncomputable section

namespace JordanFramePeirce

/-- A **Euclidean Jordan algebra**: a real inner-product space carrying a commutative bilinear
product with unit, satisfying the Jordan identity and the associativity of the inner product.

This is Faraut–Korányi's definition (FK III.1.1) with two deliberate weakenings, both of which
make the theorems below *stronger*: finite-dimensionality is not a field (it is carried as a
separate `[FiniteDimensional ℝ J]` argument exactly where it is needed), and the inner product is
an arbitrary associative one rather than the Jordan trace form.

Distributivity and homogeneity are stated on the left only; commutativity supplies the right-hand
versions. -/
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
  adds to "formally real". -/
  inner_assoc : ∀ x y z : J, inner ℝ (x * y) z = inner ℝ y (x * z)

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J] [EuclideanJordanAlgebra J]

namespace EuclideanJordanAlgebra

/-- Left multiplication by `0` is `0` — the one ring axiom the class does not state, obtained
from additivity at `(0, 0, a)`. -/
theorem zero_mul' (a : J) : (0 : J) * a = 0 := by
  have h : (0 : J) * a + (0 : J) * a = (0 : J) * a + 0 := by
    rw [add_zero, ← add_mul, add_zero]
  exact add_left_cancel h

theorem mul_zero' (a : J) : a * (0 : J) = 0 := by rw [mul_comm, zero_mul']

theorem mul_add' (a x y : J) : a * (x + y) = a * x + a * y := by
  rw [mul_comm a (x + y), add_mul, mul_comm x a, mul_comm y a]

theorem mul_smul' (r : ℝ) (a x : J) : a * (r • x) = r • (a * x) := by
  rw [mul_comm a (r • x), smul_mul, mul_comm x a]

end EuclideanJordanAlgebra

/-! ## Orthogonal idempotent families, primitivity, and Jordan frames -/

/-- A family of pairwise-orthogonal idempotents.  Completeness is deliberately *not* part of this
predicate; it is a separate field of `JordanFrame`. -/
structure IsOrthIdemFamily {n : ℕ} (p : Fin n → J) : Prop where
  /-- Each member is idempotent. -/
  idem : ∀ i, p i * p i = p i
  /-- Distinct members are orthogonal. -/
  orth : ∀ i j, i ≠ j → p i * p j = 0

/-- A **primitive idempotent**: a nonzero idempotent that cannot be split, i.e. the only
idempotents of the Peirce subalgebra `J₂(c) = {x | c ∘ x = x}` are `0` and `c` itself.

The third clause is stated in the ambient algebra — `d` idempotent with `c ∘ d = d`, which is
membership in `J₂(c)` — rather than over a subtype, so that it can be checked without first
producing the subalgebra. -/
def IsPrimitive (c : J) : Prop :=
  c * c = c ∧ c ≠ 0 ∧ ∀ d : J, d * d = d → c * d = d → d = 0 ∨ d = c

/-- A **Jordan frame**: a complete family of pairwise-orthogonal primitive idempotents.

Carried as data, indexed by `Fin n`, so that its cardinality is available without any
well-definedness theorem.  In particular `n` is *not* asserted to be the rank of `J`. -/
structure JordanFrame (J : Type*) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [EuclideanJordanAlgebra J] (n : ℕ) where
  /-- The idempotents. -/
  p : Fin n → J
  /-- They are idempotent and pairwise orthogonal. -/
  orthIdem : IsOrthIdemFamily p
  /-- Each is primitive. -/
  primitive : ∀ i, IsPrimitive (p i)
  /-- They sum to the unit. -/
  complete : ∑ i, p i = 1

/-! ## The blocks -/

/-- The `r`-eigenspace of `L_a : x ↦ a ∘ x`, as a submodule. -/
def eigSub (a : J) (r : ℝ) : Submodule ℝ J where
  carrier := {x : J | a * x = r • x}
  add_mem' := fun {u v} hu hv => by
    change a * (u + v) = r • (u + v)
    rw [EuclideanJordanAlgebra.mul_add', hu, hv, smul_add]
  zero_mem' := by
    change a * 0 = r • (0 : J)
    rw [EuclideanJordanAlgebra.mul_zero', smul_zero]
  smul_mem' := fun t x hx => by
    change a * (t • x) = r • (t • x)
    rw [EuclideanJordanAlgebra.mul_smul', hx, smul_comm]

@[simp] theorem mem_eigSub {a : J} {r : ℝ} {x : J} : x ∈ eigSub a r ↔ a * x = r • x := Iff.rfl

variable {n : ℕ}

/-- The eigenvalue attached to the pair `(i, j)`: `1` on the diagonal, `½` off it. -/
def blockCoef (i j : Fin n) : ℝ := if i = j then 1 else (2 : ℝ)⁻¹

theorem blockCoef_comm (i j : Fin n) : blockCoef i j = blockCoef j i := by
  unfold blockCoef
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

/-- `V_{ij}` before it is pushed through `Sym2`: the joint `blockCoef i j`-eigenspace of `L_{pᵢ}`
and `L_{pⱼ}`.  On the diagonal this is `J₂(pᵢ) = {x | pᵢ ∘ x = x}`; off it, the joint
`½`-eigenspace. -/
def frameBlockRaw (F : JordanFrame J n) (i j : Fin n) : Submodule ℝ J :=
  eigSub (F.p i) (blockCoef i j) ⊓ eigSub (F.p j) (blockCoef i j)

theorem frameBlockRaw_comm (F : JordanFrame J n) (i j : Fin n) :
    frameBlockRaw F i j = frameBlockRaw F j i := by
  unfold frameBlockRaw
  rw [blockCoef_comm i j, inf_comm]

/-- **`V_{ij}`**, indexed by unordered pairs.  For `i ≠ j` the joint `½`-eigenspace of `L_{pᵢ}`
and `L_{pⱼ}`; on the diagonal, `J₂(pᵢ)`. -/
def frameBlock (F : JordanFrame J n) : Sym2 (Fin n) → Submodule ℝ J :=
  Sym2.lift ⟨frameBlockRaw F, frameBlockRaw_comm F⟩

@[simp] theorem frameBlock_mk (F : JordanFrame J n) (i j : Fin n) :
    frameBlock F s(i, j) = frameBlockRaw F i j := rfl

theorem mem_frameBlock_diag {F : JordanFrame J n} {i : Fin n} {x : J} :
    x ∈ frameBlock F s(i, i) ↔ F.p i * x = x := by
  simp [frameBlockRaw, blockCoef]

theorem mem_frameBlock_off {F : JordanFrame J n} {i j : Fin n} (hij : i ≠ j) {x : J} :
    x ∈ frameBlock F s(i, j) ↔ F.p i * x = (2 : ℝ)⁻¹ • x ∧ F.p j * x = (2 : ℝ)⁻¹ • x := by
  simp [frameBlockRaw, blockCoef, hij]

/-! ## The two theorems -/

/-- **The frame Peirce decomposition: `J = ⨁_{i ≤ j} V_{ij}`.**

For a Jordan frame `p₁, …, pₙ` of a Euclidean Jordan algebra `J`, the blocks `V_{ij}` — indexed
by unordered pairs, so that `V_{ij}` and `V_{ji}` are counted once — form an internal direct sum
decomposition of `J`: the canonical map `⨁_{s : Sym2 (Fin n)} V_s → J` is bijective.  That is
independence *and* spanning.

Reference: J. Faraut and A. Korányi, *Analysis on Symmetric Cones*, Oxford 1994, Theorem IV.2.1.

No dimension hypothesis is needed.  Primitivity remains a *formal hypothesis* of this statement —
it is carried by `JordanFrame` — but the proof does not spend it: see the module docstring. -/
theorem frameBlock_isInternal (F : JordanFrame J n) : DirectSum.IsInternal (frameBlock F) := by
  let _lib : EuclideanJordan.EuclideanJordanAlgebra J :=
    { toMul := inferInstance
      toOne := inferInstance
      mul_comm := EuclideanJordanAlgebra.mul_comm
      add_mul := EuclideanJordanAlgebra.add_mul
      smul_mul := EuclideanJordanAlgebra.smul_mul
      one_mul := EuclideanJordanAlgebra.one_mul
      jordan := EuclideanJordanAlgebra.jordan
      inner_assoc := EuclideanJordanAlgebra.inner_assoc }
  exact EuclideanJordan.frameBlock_isInternal
    { p := F.p
      orthIdem := ⟨F.orthIdem.idem, F.orthIdem.orth⟩
      primitive := F.primitive
      complete := F.complete }

/-- **The diagonal blocks are lines: `dim V_{ii} = 1`.**

This is where primitivity of the frame's members is spent, and where finite-dimensionality is
needed.  `V_{ii}` is the Peirce subalgebra `J₂(pᵢ)`, which is itself a Euclidean Jordan algebra
with unit `pᵢ`; the spectral theorem inside it writes every element as a real combination of
idempotents of `J₂(pᵢ)`, and primitivity says each of those is `0` or `pᵢ`.  So
`V_{ii} = ℝ ∙ pᵢ`, and `pᵢ ≠ 0`.

Reference: J. Faraut and A. Korányi, *Analysis on Symmetric Cones*, Oxford 1994, Theorem IV.2.1.

★ This is a statement about one block of a frame carried as data.  It is *not* a statement about
`rank J`, and nothing here converts it into one. -/
theorem finrank_frameBlock_diag [FiniteDimensional ℝ J] (F : JordanFrame J n) (i : Fin n) :
    Module.finrank ℝ ↥(frameBlock F s(i, i)) = 1 := by
  let _lib : EuclideanJordan.EuclideanJordanAlgebra J :=
    { toMul := inferInstance
      toOne := inferInstance
      mul_comm := EuclideanJordanAlgebra.mul_comm
      add_mul := EuclideanJordanAlgebra.add_mul
      smul_mul := EuclideanJordanAlgebra.smul_mul
      one_mul := EuclideanJordanAlgebra.one_mul
      jordan := EuclideanJordanAlgebra.jordan
      inner_assoc := EuclideanJordanAlgebra.inner_assoc }
  exact EuclideanJordan.finrank_frameBlock_diag
    { p := F.p
      orthIdem := ⟨F.orthIdem.idem, F.orthIdem.orth⟩
      primitive := F.primitive
      complete := F.complete } i

end JordanFramePeirce
