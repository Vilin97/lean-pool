/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
module

public import LeanPool.EuclideanJordan.TraceFormSolution
public import LeanPool.EuclideanJordan.FramePeirceSolution

/-!
# Combined trace-form and frame Peirce interface

The public names in `EuclideanJordan.StructureSolution` reuse the standalone
`JordanTraceForm` and `JordanFramePeirce` implementations. The algebra, orthogonal-family and
frame records are retained as compatibility boundaries, including their constructors and
projections. Named adapters preserve the multiplication, unit and frame data when passing to
the shared interface; they introduce no ambient library algebra instance into theorem headers.
-/

public section

namespace EuclideanJordan.StructureSolution

namespace JordanTraceForm

variable {J : Type*} [NonUnitalNonAssocCommRing J] [Module ℝ J] [IsScalarTower ℝ J J]

/-- In a *commutative* algebra the scalar-tower rule `(r • a) * b = r • (a * b)` already gives
the `SMulCommClass` rule on the other side, so only `IsScalarTower ℝ J J` has to be assumed. -/
theorem mul_smul_comm' (r : ℝ) (a b : J) : a * (r • b) = r • (a * b) :=
  _root_.JordanTraceForm.mul_smul_comm' r a b

/-- **The Jordan multiplication operator** `L_c : y ↦ c * y`, as an `ℝ`-linear map. Its
`ℝ`-linearity is exactly what the scalar tower buys, and it is what makes `L_c` traceable. -/
@[expose] def mulL (c : J) : J →ₗ[ℝ] J :=
  _root_.JordanTraceForm.mulL c

@[simp] theorem mulL_apply (c y : J) : mulL c y = c * y := rfl

/-- `L_·` bundled as a linear map in the multiplier, which is what makes `jtr` linear. -/
@[expose] def mulLₗ : J →ₗ[ℝ] J →ₗ[ℝ] J :=
  _root_.JordanTraceForm.mulLₗ

@[simp] theorem mulLₗ_apply (a : J) : mulLₗ a = mulL a := rfl

/-- **The Jordan trace functional** `x ↦ tr(L_x)`, as an `ℝ`-linear form. Not normalised: see
the module docstring. -/
@[expose] noncomputable def jtr : J →ₗ[ℝ] ℝ :=
  _root_.JordanTraceForm.jtr

@[simp] theorem jtr_apply (x : J) : jtr x = LinearMap.trace ℝ J (mulL x) := rfl

/-- **The Jordan trace form** `τ(x, y) = tr(L_{x * y})`, bundled as an `ℝ`-bilinear form.

Bilinearity is part of the type. This compatibility definition reuses the standalone
trace-form construction with the same multiplication operator. -/
@[expose] noncomputable def traceForm : J →ₗ[ℝ] J →ₗ[ℝ] ℝ :=
  _root_.JordanTraceForm.traceForm

@[simp] theorem traceForm_apply (x y : J) : traceForm x y = jtr (x * y) := rfl

/-- **The trace form is symmetric**: `τ(x, y) = τ(y, x)`.

No Jordan identity, no finite dimension, no formal reality: this is commutativity of the product
underneath `jtr`, and it is registered at that generality deliberately. -/
theorem traceForm_comm (x y : J) : traceForm x y = traceForm y x :=
  _root_.JordanTraceForm.traceForm_comm x y

/-- **The trace form is associative**: `τ(x * y, z) = τ(y, x * z)`.

This is the compatibility that the standard presentation of a Euclidean Jordan algebra *assumes*
of its inner product, here proved of a form manufactured from the multiplication alone. It is the
main theorem of this file.

Note the hypotheses, which are weaker than one expects. Beyond the commutative product and the
`ℝ`-module structure only `IsCommJordan` — the Jordan identity — is assumed: **no finite
dimension, no formal reality, no unit, no positivity, no idempotents, no spectral theory.**
`LinearMap.trace` is total, so the statement is meaningful (and true) even when `J` has no finite
basis and every trace in sight is `0`. -/
theorem traceForm_assoc [IsCommJordan J] (x y z : J) :
    traceForm (x * y) z = traceForm y (x * z) :=
  _root_.JordanTraceForm.traceForm_assoc x y z

/-- **The trace form is positive semidefinite**: `τ(x, x) ≥ 0`.

`hfr` is formal reality: a vanishing sum of squares has vanishing summands. With
`Module.Finite ℝ J` it yields a spectral resolution `x = ∑ᵢ λᵢ qᵢ` into orthogonal idempotents,
whence `x * x = ∑ᵢ λᵢ² qᵢ` and `τ(x, x) = ∑ᵢ λᵢ² tr(L_{qᵢ})`; and for an idempotent `c` the Peirce
split `L_c = P₁(c) + ½ P_{1/2}(c)` writes `tr(L_c)` as a nonnegative combination of traces of
idempotent endomorphisms, which are the ranks of their ranges.

Formal reality is essential: `ℂ` over `ℝ` is a finite-dimensional commutative associative Jordan
algebra with `τ(i, i) = -2`. See the module docstring, which is also honest about the weaker
role `Module.Finite ℝ J` plays in this particular statement. -/
theorem traceForm_self_nonneg [IsCommJordan J] [Module.Finite ℝ J]
    (hfr : ∀ (k : ℕ) (f : Fin k → J), (∑ i, f i * f i) = 0 → ∀ i, f i = 0) (x : J) :
    0 ≤ traceForm x x :=
  _root_.JordanTraceForm.traceForm_self_nonneg hfr x

/-- **The trace form is definite**: `τ(x, x) = 0 ↔ x = 0`.

Together with `traceForm_comm`, `traceForm_assoc` and `traceForm_self_nonneg` this is the whole
of the assertion that `τ` is a symmetric associative positive definite bilinear form — the
Euclidean form supplied by the multiplication itself. It is only the form: unitality, which a
Euclidean Jordan algebra also requires, is neither assumed nor concluded here.

The nontrivial direction is `→`. It rests on a sharpening of the estimate behind
`traceForm_self_nonneg`: for a **nonzero** idempotent `c` one has `tr(L_c) ≥ 1`, because
`P₁(c) c = c` makes the range of the Peirce projection `P₁(c)` nonzero, hence of rank at least
one. So a vanishing `∑ᵢ λᵢ² tr(L_{qᵢ})` kills every `λᵢ` whose idempotent is nonzero, and the
terms with `qᵢ = 0` contribute nothing to `x` anyway. -/
theorem traceForm_self_eq_zero_iff [IsCommJordan J] [Module.Finite ℝ J]
    (hfr : ∀ (k : ℕ) (f : Fin k → J), (∑ i, f i * f i) = 0 → ∀ i, f i = 0) (x : J) :
    traceForm x x = 0 ↔ x = 0 :=
  _root_.JordanTraceForm.traceForm_self_eq_zero_iff hfr x

end JordanTraceForm

/-! ## Frame Peirce compatibility interface

The two endpoints retain the same supplied-frame and dimension hypotheses as the standalone
solution. In particular, internality does not assume finite dimension, while the diagonal
finrank theorem does. The record vocabulary below preserves the combined interface's API.
-/

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

/-- The standalone frame algebra with exactly the same multiplication and unit. -/
@[instance_reducible] def toFramePeirce : _root_.JordanFramePeirce.EuclideanJordanAlgebra J where
  toMul := inferInstance
  toOne := inferInstance
  mul_comm := EuclideanJordanAlgebra.mul_comm
  add_mul := EuclideanJordanAlgebra.add_mul
  smul_mul := EuclideanJordanAlgebra.smul_mul
  one_mul := EuclideanJordanAlgebra.one_mul
  jordan := EuclideanJordanAlgebra.jordan
  inner_assoc := EuclideanJordanAlgebra.inner_assoc

/-- Left multiplication by `0` is `0` — the one ring axiom the class does not state, obtained
from additivity at `(0, 0, a)`. -/
theorem zero_mul' (a : J) : (0 : J) * a = 0 := by
  let := EuclideanJordanAlgebra.toFramePeirce (J := J)
  exact _root_.JordanFramePeirce.EuclideanJordanAlgebra.zero_mul' a

theorem mul_zero' (a : J) : a * (0 : J) = 0 := by
  let := EuclideanJordanAlgebra.toFramePeirce (J := J)
  exact _root_.JordanFramePeirce.EuclideanJordanAlgebra.mul_zero' a

theorem mul_add' (a x y : J) : a * (x + y) = a * x + a * y := by
  let := EuclideanJordanAlgebra.toFramePeirce (J := J)
  exact _root_.JordanFramePeirce.EuclideanJordanAlgebra.mul_add' a x y

theorem mul_smul' (r : ℝ) (a x : J) : a * (r • x) = r • (a * x) := by
  let := EuclideanJordanAlgebra.toFramePeirce (J := J)
  exact _root_.JordanFramePeirce.EuclideanJordanAlgebra.mul_smul' r a x

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
  letI := EuclideanJordanAlgebra.toFramePeirce (J := J)
  _root_.JordanFramePeirce.IsPrimitive c

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

/-- The standalone frame with the same indexed idempotents and completeness witness. -/
def JordanFrame.toFramePeirce {n : ℕ} (F : JordanFrame J n) :
    letI := EuclideanJordanAlgebra.toFramePeirce (J := J)
    _root_.JordanFramePeirce.JordanFrame J n :=
  letI := EuclideanJordanAlgebra.toFramePeirce (J := J)
  { p := F.p
    orthIdem := ⟨F.orthIdem.idem, F.orthIdem.orth⟩
    primitive := F.primitive
    complete := F.complete }

/-! ## The blocks -/

/-- The `r`-eigenspace of `L_a : x ↦ a ∘ x`, as a submodule. -/
@[expose] def eigSub (a : J) (r : ℝ) : Submodule ℝ J :=
  letI := EuclideanJordanAlgebra.toFramePeirce (J := J)
  _root_.JordanFramePeirce.eigSub a r

@[simp] theorem mem_eigSub {a : J} {r : ℝ} {x : J} : x ∈ eigSub a r ↔ a * x = r • x := Iff.rfl

variable {n : ℕ}

/-- The eigenvalue attached to the pair `(i, j)`: `1` on the diagonal, `½` off it. -/
def blockCoef (i j : Fin n) : ℝ :=
  _root_.JordanFramePeirce.blockCoef i j

theorem blockCoef_comm (i j : Fin n) : blockCoef i j = blockCoef j i :=
  _root_.JordanFramePeirce.blockCoef_comm i j

/-- `V_{ij}` before it is pushed through `Sym2`: the joint `blockCoef i j`-eigenspace of `L_{pᵢ}`
and `L_{pⱼ}`.  On the diagonal this is `J₂(pᵢ) = {x | pᵢ ∘ x = x}`; off it, the joint
`½`-eigenspace. -/
@[expose] def frameBlockRaw (F : JordanFrame J n) (i j : Fin n) : Submodule ℝ J :=
  letI := EuclideanJordanAlgebra.toFramePeirce (J := J)
  _root_.JordanFramePeirce.frameBlockRaw F.toFramePeirce i j

theorem frameBlockRaw_comm (F : JordanFrame J n) (i j : Fin n) :
    frameBlockRaw F i j = frameBlockRaw F j i := by
  let := EuclideanJordanAlgebra.toFramePeirce (J := J)
  exact _root_.JordanFramePeirce.frameBlockRaw_comm F.toFramePeirce i j

/-- **`V_{ij}`**, indexed by unordered pairs.  For `i ≠ j` the joint `½`-eigenspace of `L_{pᵢ}`
and `L_{pⱼ}`; on the diagonal, `J₂(pᵢ)`. -/
@[expose] def frameBlock (F : JordanFrame J n) : Sym2 (Fin n) → Submodule ℝ J :=
  letI := EuclideanJordanAlgebra.toFramePeirce (J := J)
  _root_.JordanFramePeirce.frameBlock F.toFramePeirce

@[simp] theorem frameBlock_mk (F : JordanFrame J n) (i j : Fin n) :
    frameBlock F s(i, j) = frameBlockRaw F i j := rfl

theorem mem_frameBlock_diag {F : JordanFrame J n} {i : Fin n} {x : J} :
    x ∈ frameBlock F s(i, i) ↔ F.p i * x = x := by
  let := EuclideanJordanAlgebra.toFramePeirce (J := J)
  exact _root_.JordanFramePeirce.mem_frameBlock_diag (F := F.toFramePeirce)

theorem mem_frameBlock_off {F : JordanFrame J n} {i j : Fin n} (hij : i ≠ j) {x : J} :
    x ∈ frameBlock F s(i, j) ↔ F.p i * x = (2 : ℝ)⁻¹ • x ∧ F.p j * x = (2 : ℝ)⁻¹ • x := by
  let := EuclideanJordanAlgebra.toFramePeirce (J := J)
  exact _root_.JordanFramePeirce.mem_frameBlock_off (F := F.toFramePeirce) hij

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
  let := EuclideanJordanAlgebra.toFramePeirce (J := J)
  exact _root_.JordanFramePeirce.frameBlock_isInternal F.toFramePeirce

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
  let := EuclideanJordanAlgebra.toFramePeirce (J := J)
  exact _root_.JordanFramePeirce.finrank_frameBlock_diag F.toFramePeirce i

end JordanFramePeirce

end

end EuclideanJordan.StructureSolution
