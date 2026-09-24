/-
Copyright (c) 2026 Jue Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jue Xu
-/

module

public import LeanPool.LowWeightPauliDynamics.SchurCore

/-!
# The ℓ² operator norm of a block of a matrix

A block of a matrix has ℓ² operator norm at most that of the matrix; in particular every block of
a unitary matrix, or of a real orthogonal matrix, has ℓ² operator norm at most one. The proof of
`apd:thm:local_flow_k_local` uses this for the orthogonal matrix `A` by which a Pauli rotation
acts on the vector of Pauli coefficients: the block `A_RR` of `A` on the high-weight coordinates
`R` satisfies `‖A_RR‖ ≤ ‖A‖ = 1`. That is the first of the two estimates the damped flow
recursion rests on.

The statement is proved in more generality than this application needs: for any pair of injective
index maps, over any `RCLike` field, and with no nonemptiness hypothesis. Nothing here is specific
to Pauli strings. `Pauli/Flow` does not go through this file: it never builds the matrix `A`, and
proves the same estimate directly on coefficient vectors. This file is the matrix form of the
statement, and its `clm` is how `Schur` and the layer inflow bounds speak about the ℓ² operator
norm of a rectangular matrix.

## Main definitions

* `restrictCLM`: restriction of coordinates along an index map, as a continuous linear map of
  Euclidean spaces.
* `clm`: the continuous linear map of Euclidean spaces attached to a rectangular matrix; its
  operator norm is the ℓ² operator norm of the matrix.

## Main results

* `l2_opNorm_submatrix_le`: `‖A.submatrix f g‖ ≤ ‖A‖` for injective `f` and `g`.
* `l2_opNorm_toBlock_le`: the same for `Matrix.toBlock`.
* `l2_opNorm_submatrix_le_one_of_mem_unitary`, `l2_opNorm_toBlock_le_one_of_mem_unitary`: a block
  of a unitary matrix has ℓ² operator norm at most one.
* `l2_opNorm_submatrix_le_one_of_mem_orthogonalGroup`,
  `l2_opNorm_toBlock_le_one_of_mem_orthogonalGroup`: the real orthogonal case.

## Method

`Matrix.l2_opNorm_def` says that the rectangular ℓ² operator norm **is** the operator norm of a
continuous linear map, by `rfl`. Selecting rows then factors definitionally,

  `clm (A.submatrix f id) = restrictCLM 𝕜 f ∘L clm A`   — also `rfl`,

so `ContinuousLinearMap.opNorm_comp_le` does the work once coordinate restriction is shown to be a
contraction. Columns come from conjugate-transposing rather than from a second map. No singular
values and no spectral theory are needed.

## Injectivity is needed

Both index maps must be injective. Repeating the single row of the `1 × 1` identity gives a `2 × 1`
block of norm `√2 > 1 = ‖1‖`; that witness is `example`-checked at the end of the file.
-/

open scoped Matrix.Norms.L2Operator

open Matrix Finset WithLp

@[expose] public section

namespace Lean4LPD

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### The coordinate-restriction continuous linear map -/

/-- Restriction of coordinates along `f : p → m`, as a continuous linear map of Euclidean
spaces: `x ↦ x ∘ f`. Mathlib's `EuclideanSpace.restrict₂` covers only the inclusion of one
`Finset` in another and comes with no norm lemma. -/
noncomputable def restrictCLM (𝕜 : Type*) [RCLike 𝕜] {p m : Type*}
    (f : p → m) : EuclideanSpace 𝕜 m →L[𝕜] EuclideanSpace 𝕜 p where
  toFun x := toLp 2 (fun i => ofLp x (f i))
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp

@[simp] lemma restrictCLM_apply {p m : Type*} (f : p → m)
    (x : EuclideanSpace 𝕜 m) (i : p) : restrictCLM 𝕜 f x i = x (f i) := rfl

section Restrict

variable {m p : Type*} [Fintype m] [Fintype p]

/-- Dropping coordinates (along an injective map) does not increase the ℓ² norm. -/
lemma norm_restrictCLM_apply_le {f : p → m} (hf : Function.Injective f)
    (x : EuclideanSpace 𝕜 m) : ‖restrictCLM 𝕜 f x‖ ≤ ‖x‖ := by
  classical
  have hsq : ‖restrictCLM 𝕜 f x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    refine Finset.sum_le_sum_of_injOn f hf.injOn (by simp) (fun i _ => ?_) (fun a _ _ => ?_)
    · simp
    · positivity
  have := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at this

/-- Coordinate restriction along an injective map is a contraction. -/
lemma norm_restrictCLM_le_one {f : p → m} (hf : Function.Injective f) :
    ‖restrictCLM 𝕜 f‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    simpa using norm_restrictCLM_apply_le hf x

end Restrict

variable {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
  [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]

/-! ### Selecting rows, then columns -/

omit [DecidableEq m] [DecidableEq p] in
/-- Selecting a subfamily of rows factors, **definitionally**, through coordinate restriction:
`clm (A.submatrix f id) = restrictCLM 𝕜 f ∘L clm A`. -/
lemma clm_submatrix_id (A : Matrix m n 𝕜) (f : p → m) :
    clm (A.submatrix f (id : n → n)) = (restrictCLM 𝕜 f).comp (clm A) := rfl

omit [DecidableEq m] [DecidableEq p] in
/-- **Row selection does not increase the ℓ² operator norm.** -/
lemma l2_opNorm_submatrix_id_le (A : Matrix m n 𝕜) {f : p → m} (hf : Function.Injective f) :
    ‖A.submatrix f (id : n → n)‖ ≤ ‖A‖ := by
  rw [Matrix.l2_opNorm_def, Matrix.l2_opNorm_def (A := A)]
  calc ‖clm (A.submatrix f (id : n → n))‖
      = ‖(restrictCLM 𝕜 f).comp (clm A)‖ := by rw [clm_submatrix_id]
    _ ≤ ‖restrictCLM 𝕜 f‖ * ‖clm A‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖clm A‖ := mul_le_of_le_one_left (norm_nonneg _) (norm_restrictCLM_le_one hf)

omit [DecidableEq m] [DecidableEq p] in
/-- **A block of a matrix has ℓ² operator norm at most that of the matrix.**

`A.submatrix f g` selects the rows indexed by `f` and the columns indexed by `g`. Both index maps
are required to be injective, and that hypothesis cannot be dropped: repeating the single row of
the `1 × 1` identity gives a matrix of norm `√2` (see the last `example` of this file).

The proof selects rows with `l2_opNorm_submatrix_id_le`, conjugate-transposes, and selects rows
again. -/
theorem l2_opNorm_submatrix_le (A : Matrix m n 𝕜) {f : p → m} {g : q → n}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ‖A.submatrix f g‖ ≤ ‖A‖ := by
  classical
  have h1 : A.submatrix f g
      = ((A.submatrix f (id : n → n))ᴴ.submatrix g (id : p → p))ᴴ := by
    ext i j; simp
  rw [h1, Matrix.l2_opNorm_conjTranspose]
  calc ‖(A.submatrix f (id : n → n))ᴴ.submatrix g (id : p → p)‖
      ≤ ‖(A.submatrix f (id : n → n))ᴴ‖ := l2_opNorm_submatrix_id_le _ hg
    _ = ‖A.submatrix f (id : n → n)‖ := Matrix.l2_opNorm_conjTranspose _
    _ ≤ ‖A‖ := l2_opNorm_submatrix_id_le A hf

omit [DecidableEq m] in
/-- `Matrix.toBlock` form of `l2_opNorm_submatrix_le`. -/
theorem l2_opNorm_toBlock_le (A : Matrix m n 𝕜) (P : m → Prop) (Q : n → Prop)
    [DecidablePred P] [DecidablePred Q] : ‖A.toBlock P Q‖ ≤ ‖A‖ :=
  l2_opNorm_submatrix_le A Subtype.val_injective Subtype.val_injective

/-! ### Unitary and orthogonal matrices -/

/-- `‖U‖ ≤ 1` for a unitary `U`, with **no nonemptiness hypothesis**.
`CStarRing.norm_of_mem_unitary` would need `[Nontrivial (Matrix n n 𝕜)]`, hence `[Nonempty n]`, but
`CStarRing.norm_mul_mem_unitary` needs none, and `‖(1 : Matrix n n 𝕜)‖ ≤ 1` holds even when `n` is
empty (the matrix ring is then trivial, so `1 = 0` and `‖1‖ = 0`). -/
lemma l2_opNorm_le_one_of_mem_unitary {U : Matrix n n 𝕜} (hU : U ∈ unitary (Matrix n n 𝕜)) :
    ‖U‖ ≤ 1 := by
  have h1 : ‖U‖ = ‖(1 : Matrix n n 𝕜)‖ := by
    rw [← CStarRing.norm_mul_mem_unitary (1 : Matrix n n 𝕜) hU, Matrix.one_mul]
  rw [h1, Matrix.cstar_norm_def, map_one]
  exact ContinuousLinearMap.norm_id_le

omit [DecidableEq m] [DecidableEq p] in
/-- **A block of a unitary matrix has ℓ² operator norm at most `1`.**

`f` and `g` are injective index maps, e.g. `Subtype.val` out of the two index subtypes cutting the
block out. No nonemptiness hypothesis on any of `n`, `p`, `q`. -/
theorem l2_opNorm_submatrix_le_one_of_mem_unitary {U : Matrix n n 𝕜}
    (hU : U ∈ unitary (Matrix n n 𝕜)) {f : p → n} {g : q → n}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ‖U.submatrix f g‖ ≤ 1 :=
  (l2_opNorm_submatrix_le U hf hg).trans (l2_opNorm_le_one_of_mem_unitary hU)

omit [DecidableEq m] [DecidableEq p] in
/-- `Matrix.unitaryGroup` spelling. -/
theorem l2_opNorm_submatrix_le_one_of_mem_unitaryGroup {U : Matrix n n 𝕜}
    (hU : U ∈ Matrix.unitaryGroup n 𝕜) {f : p → n} {g : q → n}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ‖U.submatrix f g‖ ≤ 1 :=
  l2_opNorm_submatrix_le_one_of_mem_unitary hU hf hg

omit [DecidableEq m] in
/-- `Matrix.toBlock` form: the `(P, Q)` block of a unitary has ℓ² operator norm at most `1`. -/
theorem l2_opNorm_toBlock_le_one_of_mem_unitary {U : Matrix n n 𝕜}
    (hU : U ∈ unitary (Matrix n n 𝕜)) (P Q : n → Prop) [DecidablePred P] [DecidablePred Q] :
    ‖U.toBlock P Q‖ ≤ 1 :=
  (l2_opNorm_toBlock_le U P Q).trans (l2_opNorm_le_one_of_mem_unitary hU)

omit [DecidableEq m] [DecidableEq p] in
/-- **Real orthogonal case**, the `𝕜 = ℝ` specialization: a block of an orthogonal matrix has ℓ²
operator norm at most `1`.  `Matrix.orthogonalGroup n ℝ` is by definition `unitary (Matrix n n ℝ)`
with the trivial star, so this is literally the unitary statement at `𝕜 = ℝ`. -/
theorem l2_opNorm_submatrix_le_one_of_mem_orthogonalGroup {O : Matrix n n ℝ}
    (hO : O ∈ Matrix.orthogonalGroup n ℝ) {f : p → n} {g : q → n}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ‖O.submatrix f g‖ ≤ 1 :=
  l2_opNorm_submatrix_le_one_of_mem_unitary hO hf hg

omit [DecidableEq m] in
/-- `Matrix.toBlock` form of the orthogonal case. -/
theorem l2_opNorm_toBlock_le_one_of_mem_orthogonalGroup {O : Matrix n n ℝ}
    (hO : O ∈ Matrix.orthogonalGroup n ℝ) (P Q : n → Prop) [DecidablePred P] [DecidablePred Q] :
    ‖O.toBlock P Q‖ ≤ 1 :=
  l2_opNorm_toBlock_le_one_of_mem_unitary hO P Q

/-! ### Sanity checks -/

section Checks

/-- The shape arising for Pauli coefficients: the block of a unitary matrix with rows of weight
at least `a` and columns of weight below `b`, for an arbitrary weight function `w`. -/
example {n : Type*} [Fintype n] [DecidableEq n] (U : Matrix n n ℂ)
    (hU : U ∈ unitary (Matrix n n ℂ)) (w : n → ℕ) (a b : ℕ) :
    ‖U.toBlock (fun s => a ≤ w s) (fun s => w s < b)‖ ≤ 1 :=
  l2_opNorm_toBlock_le_one_of_mem_unitary hU _ _

/-- Injectivity of the index maps cannot be dropped: repeating the single row of the `1 × 1`
identity gives a `2 × 1` matrix that maps a unit vector to a vector of squared norm `2`, so its
ℓ² operator norm exceeds `1 = ‖1‖`. -/
example : ¬ ‖(1 : Matrix (Fin 1) (Fin 1) ℝ).submatrix (fun _ : Fin 2 => 0) (id : Fin 1 → Fin 1)‖
    ≤ 1 := by
  set A : Matrix (Fin 2) (Fin 1) ℝ :=
    (1 : Matrix (Fin 1) (Fin 1) ℝ).submatrix (fun _ : Fin 2 => 0) (id : Fin 1 → Fin 1) with hA
  set x : EuclideanSpace ℝ (Fin 1) := toLp 2 ![1] with hx
  have hxn : ‖x‖ = 1 := by
    rw [← Real.sqrt_one, EuclideanSpace.norm_eq]
    norm_num [hx]
  have hcoord : ∀ i : Fin 2, (clm A x) i = 1 := by
    intro i
    change (A *ᵥ ofLp x) i = 1
    simp [hA, hx, Matrix.mulVec, dotProduct, Matrix.one_apply]
  have hAx : ‖clm A x‖ ^ 2 = 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, hcoord 0, hcoord 1]
    norm_num
  intro hle
  have h1 : ‖clm A x‖ ≤ ‖A‖ * ‖x‖ :=
    (Matrix.l2_opNorm_def A) ▸ ContinuousLinearMap.le_opNorm _ _
  rw [hxn, mul_one] at h1
  nlinarith [norm_nonneg (clm A x), norm_nonneg A]

end Checks

end Lean4LPD
