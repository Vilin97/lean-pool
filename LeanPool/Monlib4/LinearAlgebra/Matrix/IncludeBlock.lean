/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basis
import LeanPool.Monlib4.Preq.Dite
import Mathlib.LinearAlgebra.Matrix.Hermitian
import LeanPool.Monlib4.LinearAlgebra.TensorProduct.BasicLemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import LeanPool.Monlib4.LinearAlgebra.ToMatrixOfEquiv
import LeanPool.Monlib4.LinearAlgebra.Matrix.PiMat

/-!

# Include block

 This file defines `matrix.includeBlock`, which imitates `direct_sum.component_of`
 for `pi` instead of `direct_sum` :TODO:

 The direct sum in these files are sort of misleading.

-/


open scoped BigOperators

theorem Finset.sum_sigma_univ {β α : Type _} [AddCommMonoid β] [Fintype α] {σ : α → Type _}
    [∀ i, Fintype (σ i)] (f : (Σ i, σ i) → β) :
    ∑ x : Σ i : α, σ i, f x = ∑ a : α, ∑ s : σ a, f (⟨a, s⟩ : Σ i, σ i) :=
  Finset.sum_sigma _ _ _

namespace Matrix

/-- The algebra homomorphism from block-indexed matrices to their block diagonal matrix. -/
def blockDiagonal'AlgHom {o : Type _} {m' : o → Type _} {α : Type _} [Fintype o] [DecidableEq o]
    [∀ i, Fintype (m' i)] [∀ i, DecidableEq (m' i)] [CommSemiring α] :
    PiMat α o m' →ₐ[α] Matrix (Σ i : o, m' i) (Σ i : o, m' i) α
    where
  toFun a := blockDiagonal' a
  map_one' := blockDiagonal'_one
  map_mul' a b := blockDiagonal'_mul _ _
  map_zero' := blockDiagonal'_zero
  map_add' a b := blockDiagonal'_add _ _
  commutes' a := by
    simp_rw [Algebra.algebraMap_eq_smul_one, blockDiagonal'_smul, blockDiagonal'_one]

theorem blockDiagonal'AlgHom_apply {o : Type _} {m' : o → Type _} {α : Type _} [Fintype o]
    [DecidableEq o] [∀ i, Fintype (m' i)] [∀ i, DecidableEq (m' i)] [CommSemiring α]
    (x : PiMat α o m') : Matrix.blockDiagonal'AlgHom x = blockDiagonal' x :=
  rfl

/-- The linear map sending a matrix to the family of its diagonal blocks. -/
def blockDiag'LinearMap {o : Type _} {m' n' : o → Type _} {α : Type _} [Semiring α] :
    Matrix (Σ i : o, m' i) (Σ i : o, n' i) α →ₗ[α] Π i : o, Matrix (m' i) (n' i) α
    where
  toFun x := Matrix.blockDiag' x
  map_add' x y := blockDiag'_add x y
  map_smul' r x := blockDiag'_smul r x

theorem blockDiag'LinearMap_apply {o : Type _} {m' : o → Type _} {n' : o → Type _} {α : Type _}
    [Semiring α] (x : Matrix (Σ i : o, m' i) (Σ i : o, n' i) α) :
    Matrix.blockDiag'LinearMap x = blockDiag' x :=
  rfl

theorem blockDiag'LinearMap_blockDiagonal'AlgHom {o : Type _} {m' : o → Type _} {α : Type _}
    [Fintype o] [DecidableEq o] [∀ i, Fintype (m' i)] [∀ i, DecidableEq (m' i)] [CommSemiring α]
    (x : PiMat α o m') :
    Matrix.blockDiag'LinearMap (Matrix.blockDiagonal'AlgHom x) = x :=
  blockDiag'_blockDiagonal' x

theorem blockDiagonal'_ext {R : Type _} {k : Type _} {s : k → Type _}
    (x y : Matrix (Σ i, s i) (Σ i, s i) R) :
    x = y ↔ ∀ i j k l, x ⟨i, j⟩ ⟨k, l⟩ = y ⟨i, j⟩ ⟨k, l⟩ := by
  simp only [← Matrix.ext_iff, Sigma.forall]

/-- A matrix indexed by a sigma type is block diagonal when its off-diagonal blocks vanish. -/
def IsBlockDiagonal {o : Type _} {m' n' : o → Type _} {α : Type _} [DecidableEq o] [Zero α]
    (x : Matrix (Σ i, m' i) (Σ i, n' i) α) : Prop :=
  blockDiagonal' (blockDiag' x) = x

/-- Include a single matrix block in the corresponding component of a block-indexed family. -/
def includeBlock {o : Type _} [DecidableEq o] {m' : o → Type _} {α : Type _} [Semiring α]
  {i : o} : Matrix (m' i) (m' i) α →ₗ[α] (PiMat α o m') :=
@LinearMap.single α o _ (fun j => Matrix (m' j) (m' j) α) _ _ _ i

theorem includeBlock_apply {o : Type _} [DecidableEq o] {m' : o → Type _} {α : Type _}
    [CommSemiring α] {i : o} (x : Matrix (m' i) (m' i) α) :
    (includeBlock : Matrix (m' i) (m' i) α →ₗ[α] PiMat α o m') x = fun j : o =>
      dite (i = j) (fun h => Eq.mp (by rw [h]) x) fun _ => 0 := by
  ext j₁ j₂ j₃
  simp only [includeBlock, LinearMap.coe_single, Pi.single, Function.update, eq_comm,
    Pi.zero_apply]
  split_ifs with h <;> aesop

theorem includeBlock_hMul_same {o : Type _} [DecidableEq o] {m' : o → Type _}
    {α : Type _} [∀ i, Fintype (m' i)] [CommSemiring α] {i : o}
    (x y : Matrix (m' i) (m' i) α) : includeBlock x * includeBlock y = includeBlock (x * y) := by
  ext i x_1 x_2
  simp_rw [includeBlock_apply, Pi.mul_apply, hMul_dite, dite_hMul, MulZeroClass.mul_zero,
    MulZeroClass.zero_mul]
  simp only [eq_mp_eq_cast, dite_eq_ite, ite_self]
  aesop

theorem includeBlock_hMul_ne_same {o : Type _} [DecidableEq o] {m' : o → Type _}
    {α : Type _} [∀ i, Fintype (m' i)] [CommSemiring α] {i j : o}
    (h : i ≠ j) (x : Matrix (m' i) (m' i) α) (y : Matrix (m' j) (m' j) α) :
    includeBlock x * includeBlock y = 0 := by
  ext
  simp_rw [includeBlock_apply, Pi.mul_apply, hMul_dite, dite_hMul, MulZeroClass.mul_zero,
    MulZeroClass.zero_mul, Pi.zero_apply]
  simp only [eq_mp_eq_cast, dite_eq_ite, ite_self]
  aesop

theorem includeBlock_hMul {o : Type _} [DecidableEq o] {m' : o → Type _} {α : Type _}
    [∀ i, Fintype (m' i)] [CommSemiring α] {i : o}
    (x : Matrix (m' i) (m' i) α) (y : PiMat α o m') :
    includeBlock x * y = includeBlock (x * y i) := by
  ext
  simp only [includeBlock_apply, Pi.mul_apply, dite_hMul, MulZeroClass.zero_mul]
  split_ifs <;> aesop

theorem hMul_includeBlock {o : Type _} [DecidableEq o] {m' : o → Type _} {α : Type _}
    [∀ i, Fintype (m' i)] [CommSemiring α] {i : o}
    (x : PiMat α o m') (y : Matrix (m' i) (m' i) α) :
    x * includeBlock y = includeBlock (x i * y) := by
  ext
  simp only [includeBlock_apply, Pi.mul_apply]
  split_ifs <;> aesop

open scoped BigOperators

theorem sum_includeBlock {R k : Type _} [CommSemiring R] [Fintype k] [DecidableEq k]
    {s : k → Type _} (x : PiMat R k s) :
    ∑ i, includeBlock (x i) = x := by
  ext
  simp only [Finset.sum_apply, includeBlock_apply, Finset.sum_dite_eq', Finset.mem_univ, if_true]
  rfl

theorem blockDiagonal'_includeBlock_trace {R k : Type _} [CommSemiring R] [Fintype k]
    [DecidableEq k] {s : k → Type _} [∀ i, Fintype (s i)]
    (x : PiMat R k s) (j : k) :
    (blockDiagonal' (includeBlock (x j))).trace = (x j).trace := by
  calc
    (blockDiagonal' (includeBlock (x j))).trace
      = ∑ i, (includeBlock (x j) i).trace :=
      by simp_rw [Matrix.trace, Matrix.diag, blockDiagonal'_apply, dif_pos,
      Finset.sum_sigma']; rfl
    _ = ∑ i, ∑ a, includeBlock (x j) i a a := rfl
    _ = ∑ i, ∑ a, dite (j = i) (fun h => by rw [← h]; exact (x j))
      (fun _ => (0 : Matrix (s i) (s i) R)) a a :=
      by simp_rw [includeBlock_apply]; rfl
    _ = ∑ i, ∑ a, dite (j = i) (fun h =>
        (by rw [← h]; exact x j : Matrix (s i) (s i) R) a a)
      (fun _ => (0 : R)) := by congr; ext; congr; ext; aesop
    _ = (x j).trace := by
        simp_rw [Finset.sum_dite_irrel, Finset.sum_const_zero,
          Finset.sum_dite_eq, Finset.mem_univ, if_true]
        rfl

open scoped Matrix

theorem single_hMul_trace {R n p : Type _} [Semiring R] [Fintype p] [DecidableEq p]
    [Fintype n] [DecidableEq n] (i : n) (j : p) (x : Matrix p n R) :
    Matrix.trace (single i j (1 : R) * x) = x j i := by
  simp_rw [Matrix.trace, Matrix.diag, mul_apply, single, of_apply, boole_mul, ite_and,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem ext_iff_trace {R n p : Type _} [Fintype n] [Fintype p]
    [CommSemiring R] (x y : Matrix n p R) : x = y ↔ ∀ a, (x * a).trace = (y * a).trace := by
  classical
  refine ⟨fun h a => by rw [h], fun h => ?_⟩
  ext i j
  specialize h (single j i 1)
  simp_rw [trace_mul_comm _ (single _ _ _), Matrix.single_hMul_trace j i] at h
  exact h

variable {R : Type _} [CommSemiring R]

namespace IsBlockDiagonal

theorem eq {k : Type _} [DecidableEq k] {s : k → Type _}
    {x : Matrix (Σ i, s i) (Σ i, s i) R} (hx : x.IsBlockDiagonal) :
    blockDiagonal' x.blockDiag' = x :=
  hx

theorem add {k : Type _} [DecidableEq k] {s : k → Type _}
    {x y : Matrix (Σ i, s i) (Σ i, s i) R} (hx : x.IsBlockDiagonal) (hy : y.IsBlockDiagonal) :
    (x + y).IsBlockDiagonal := by
  simp only [Matrix.IsBlockDiagonal, blockDiag'_add, blockDiagonal'_add, hx.eq, hy.eq]

end IsBlockDiagonal

/-- The subtype of block-diagonal square matrices indexed by a sigma type. -/
@[reducible]
def BlockDiagonals (R k : Type _) [Zero R] [DecidableEq k] (s : k → Type _) :=
{ x : Matrix (Σ i, s i) (Σ i, s i) R // IsBlockDiagonal x }

namespace IsBlockDiagonal

theorem zero {k : Type _} [DecidableEq k] {s : k → Type _} :
    (0 : Matrix (Σ i, s i) (Σ i, s i) R).IsBlockDiagonal := by
  simp only [Matrix.IsBlockDiagonal, blockDiag'_zero, blockDiagonal'_zero]

instance HAdd {k : Type _} [DecidableEq k] {s : k → Type _} :
    Add (BlockDiagonals R k s) where
  add x y := ⟨↑x + ↑y, Matrix.IsBlockDiagonal.add x.property y.property⟩

theorem coe_add {k : Type _} [DecidableEq k] {s : k → Type _}
    {x y : (BlockDiagonals R k s)} :
    ((x + y : (BlockDiagonals R k s)) :
        Matrix (Σ i, s i) (Σ i, s i) R) =
      x + y :=
  rfl

instance Zero {k : Type _} [DecidableEq k] {s : k → Type _} :
    Zero ((BlockDiagonals R k s)) where zero := ⟨0, IsBlockDiagonal.zero⟩

theorem coe_zero {k : Type _} [DecidableEq k] {s : k → Type _} :
    ((0 : (BlockDiagonals R k s)) :
        Matrix (Σ i, s i) (Σ i, s i) R) =
      0 :=
  rfl

theorem smul {k : Type _} [DecidableEq k] {s : k → Type _}
    {x : Matrix (Σ i, s i) (Σ i, s i) R} (hx : x.IsBlockDiagonal) (α : R) :
    (α • x).IsBlockDiagonal := by
  simp only [Matrix.IsBlockDiagonal, blockDiag'_smul, blockDiagonal'_smul, hx.eq]

instance Smul {k : Type _} [DecidableEq k] {s : k → Type _} :
    SMul R (BlockDiagonals R k s)
    where smul a x :=
    ⟨a • (x : Matrix (Σ i, s i) (Σ i, s i) R), Matrix.IsBlockDiagonal.smul (Subtype.mem x) a⟩

theorem coe_smul {k : Type _} [DecidableEq k] {s : k → Type _}
    (a : R) (x : (BlockDiagonals R k s)) :
    ((a • x : (BlockDiagonals R k s)) :
        Matrix (Σ i, s i) (Σ i, s i) R) =
      a • ↑x :=
  rfl

end IsBlockDiagonal

instance addCommMonoidBlockDiagonal {k : Type _} [DecidableEq k] {s : k → Type _} :
    AddCommMonoid (BlockDiagonals R k s)
    where
  add_assoc x y z := by
    ext
    simp only [IsBlockDiagonal.coe_add, add_assoc]
  zero_add a := by
    ext
    simp only [IsBlockDiagonal.coe_add, IsBlockDiagonal.coe_zero, zero_add]
  add_zero a := by
    ext
    simp only [IsBlockDiagonal.coe_zero, IsBlockDiagonal.coe_add, add_zero]
  add_comm a b := by
    ext
    simp only [IsBlockDiagonal.coe_add, add_comm]
  nsmul n x := (n : R) • x
  nsmul_zero x := by
    ext
    simp only [IsBlockDiagonal.coe_smul, Nat.cast_zero, zero_smul]
    rfl
  nsmul_succ n x := by
    ext
    simp only [IsBlockDiagonal.coe_smul, Nat.cast_succ, add_smul, one_smul, add_comm]
    simp only [IsBlockDiagonal.coe_add, add_apply]
    rw [add_comm]
    rfl


private theorem IsBlockDiagonal.coe_sum_aux {k : Type _} [DecidableEq k] {s : k → Type _} {n : ℕ}
    {x : Fin n → (BlockDiagonals R k s)} :
    ((∑ i, x i : (BlockDiagonals R k s)) :
        Matrix (Σ i, s i) (Σ i, s i) R) =
      ∑ i, (x i : Matrix (Σ i, s i) (Σ i, s i) R) := by
  induction n with
  | zero =>
      rfl
  | succ d hd =>
      simp only [Fin.sum_univ_succ, Matrix.IsBlockDiagonal.coe_add, hd]

namespace IsBlockDiagonal

theorem coe_sum {k : Type _} [DecidableEq k] {s : k → Type _} {n : Type _} [Fintype n]
    {x : n → (BlockDiagonals R k s)} :
    ((∑ i, x i : (BlockDiagonals R k s)) :
        Matrix (Σ i, s i) (Σ i, s i) R) =
      ∑ i, (x i : Matrix (Σ i, s i) (Σ i, s i) R) := by
  let σ : Fin (Fintype.card n) ≃ n := (Fintype.equivFin n).symm
  have : ∑ i : n, x i = ∑ i : Fin (Fintype.card n), x (σ i) := by
    apply Fintype.sum_equiv σ.symm
    intro i
    simp only [Equiv.apply_symm_apply]
  rw [this]
  have : ∑ i : n, (x i : Matrix (Σ i, s i) (Σ i, s i) R) = ∑ i : Fin (Fintype.card n), x (σ i) := by
    simp_rw [IsBlockDiagonal.coe_sum_aux]
    apply Fintype.sum_equiv σ.symm
    intro i
    simp only [Equiv.apply_symm_apply]
  rw [this]

end IsBlockDiagonal

instance mulActionBlockDiagonal {k : Type _} [DecidableEq k] {s : k → Type _} :
    MulAction R (BlockDiagonals R k s)
    where
  one_smul x := by ext; simp only [IsBlockDiagonal.coe_smul, one_smul]
  mul_smul a b x := by ext; simp only [← smul_smul, IsBlockDiagonal.coe_smul]

instance distribMulActionBlockDiagonal {k : Type _} [DecidableEq k] {s : k → Type _} :
    DistribMulAction R (BlockDiagonals R k s)
    where
  smul_zero x := by
    ext
    simp only [IsBlockDiagonal.coe_smul, Matrix.IsBlockDiagonal.coe_zero, smul_zero]
  smul_add a x y := by
    simp only [Subtype.ext_iff, Matrix.IsBlockDiagonal.coe_add, Matrix.IsBlockDiagonal.coe_smul,
      smul_add]

instance moduleBlockDiagonal {k : Type _} [DecidableEq k] {s : k → Type _} :
    Module R (BlockDiagonals R k s)
    where
  add_smul x y a := by
    ext
    simp only [IsBlockDiagonal.coe_add, add_smul, Matrix.IsBlockDiagonal.coe_smul]
  zero_smul a := by
    simp only [Subtype.ext_iff, Matrix.IsBlockDiagonal.coe_smul, zero_smul]
    rfl

namespace IsBlockDiagonal

theorem blockDiagonal' {k : Type _} [DecidableEq k] {s : k → Type _}
    (x : PiMat R k s) : (blockDiagonal' x).IsBlockDiagonal := by
  rw [Matrix.IsBlockDiagonal, blockDiag'_blockDiagonal']

end IsBlockDiagonal

theorem isBlockDiagonal_iff {k : Type _} [DecidableEq k] {s : k → Type _}
    (x : Matrix (Σ i, s i) (Σ i, s i) R) :
    x.IsBlockDiagonal ↔ ∃ y : PiMat R k s, x = blockDiagonal' y :=
  ⟨fun h => ⟨x.blockDiag', h.symm⟩, by
    rintro ⟨y, rfl⟩; exact Matrix.IsBlockDiagonal.blockDiagonal' y⟩

/-- A block-diagonal matrix with one nonzero matrix-entry inside a specified block. -/
def singleBlockDiagonal {k : Type _} [DecidableEq k] {s : k → Type _}
    [∀ i, DecidableEq (s i)] (i : k) (j l : s i) (α : R) :
    (BlockDiagonals R k s) :=
  ⟨single ⟨i, j⟩ ⟨i, l⟩ α, by
    simp only [Matrix.IsBlockDiagonal, blockDiag'_apply, blockDiagonal'_apply,
      Matrix.blockDiagonal'_ext, dite_eq_iff']
    intro a b c d
    constructor
    · intro h
      congr
      simp only [cast_heq]
    · intro h
      symm
      apply single_apply_of_ne
      rintro ⟨⟨rfl, h2⟩, ⟨rfl, h4⟩⟩
      contradiction⟩

theorem includeBlock_conjTranspose {R k : Type _} [CommSemiring R] [StarRing R] [DecidableEq k]
    {s : k → Type _} {i : k}
    {x : Matrix (s i) (s i) R} : star (includeBlock x) = includeBlock xᴴ := by
  ext
  simp only [Pi.star_apply, includeBlock_apply, star_apply]
  split_ifs <;> aesop

theorem includeBlock_inj {k : Type _} [DecidableEq k] {s : k → Type _} {i : k}
    {x y : Matrix (s i) (s i) R} :
    includeBlock x = includeBlock y ↔ x = y := by
  simp only [includeBlock_apply]
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  simp_rw [funext_iff, ← Matrix.ext_iff, eq_mp_eq_cast] at h
  ext j k
  specialize h i j k
  aesop

theorem blockDiagonal'_includeBlock_isHermitian_iff {R k : Type _} [CommSemiring R] [StarRing R]
    [DecidableEq k] {s : k → Type _} {i : k} (x : Matrix (s i) (s i) R) :
    (blockDiagonal' (includeBlock x)).IsHermitian ↔ x.IsHermitian := by
  calc
    (blockDiagonal' (includeBlock x)).IsHermitian ↔
        (blockDiagonal' (includeBlock x))ᴴ = blockDiagonal' (includeBlock x) :=
      by simp only [IsHermitian]
    _ ↔ blockDiagonal' (star (includeBlock x)) = blockDiagonal' (includeBlock x) := by
      simp only [blockDiagonal'_conjTranspose]; rfl
    _ ↔ star (includeBlock x) = (includeBlock x) := blockDiagonal'_inj
    _ ↔ (includeBlock xᴴ) = (includeBlock x) := by simp only [includeBlock_conjTranspose]
    _ ↔ xᴴ = x := includeBlock_inj
    _ ↔ x.IsHermitian := by simp only [IsHermitian]

theorem matrix_eq_sum_includeBlock {R k : Type _} [CommSemiring R] [Fintype k] [DecidableEq k]
    {s : k → Type _} (x : PiMat R k s) :
    x = ∑ i, includeBlock (x i) :=
  (sum_includeBlock _).symm

theorem includeBlock_apply_same {R k : Type _} [CommSemiring R] [DecidableEq k]
    {s : k → Type _} {i : k}
    (x : Matrix (s i) (s i) R) : includeBlock x i = x := by rw [includeBlock_apply]; aesop

theorem includeBlock_apply_ne_same {R k : Type _} [CommSemiring R] [DecidableEq k]
    {s : k → Type _} {i j : k}
    (x : Matrix (s i) (s i) R) (h : i ≠ j) : includeBlock x j = 0 := by
  simp only [includeBlock_apply, h, dif_neg, not_false_iff]

theorem includeBlock_apply_single {R k : Type _} [CommSemiring R] [DecidableEq k]
    {s : k → Type _} [∀ i, DecidableEq (s i)] {i : k}
    (a b : s i) :
    includeBlock (single a b (1 : R)) =
      (single (⟨i, a⟩ : Σ j, s j) (⟨i, b⟩ : Σ j, s j) (1 : R)).blockDiag' := by
  ext c d e
  simp_rw [includeBlock_apply, blockDiag'_apply]
  split_ifs with h
  · simp only [eq_mp_eq_cast, single]
    aesop
  · symm
    apply single_apply_of_ne
    simp only [Sigma.mk.inj_iff, h, false_and, and_self, not_false_eq_true]

theorem includeBlock_hMul_includeBlock {R k : Type _} [CommSemiring R] [DecidableEq k]
    {s : k → Type _} [∀ i, Fintype (s i)] {i j : k}
    (x : Matrix (s i) (s i) R) (y : Matrix (s j) (s j) R) :
    includeBlock x * includeBlock y =
      dite (j = i) (fun h => includeBlock (x * by rw [← h]; exact y)) fun h => 0 := by
  ext
  simp [includeBlock_apply, MulZeroClass.mul_zero, MulZeroClass.zero_mul, dite_apply]
  split_ifs <;> aesop

namespace IsBlockDiagonal

theorem mul {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
    [∀ i, Fintype (s i)] {x y : Matrix (Σ i, s i) (Σ i, s i) R} (hx : x.IsBlockDiagonal)
    (hy : y.IsBlockDiagonal) : (x * y).IsBlockDiagonal := by
  simp only [Matrix.IsBlockDiagonal]
  rw [← hx.eq, ← hy.eq, ← blockDiagonal'_mul, blockDiag'_blockDiagonal']

@[reducible, instance]
def hasMul {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
    [∀ i, Fintype (s i)] :
    Mul (BlockDiagonals R k s)
    where mul x y := ⟨↑x * ↑y, IsBlockDiagonal.mul x.2 y.2⟩

theorem coe_mul {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
    [∀ i, Fintype (s i)]
    {x y : (BlockDiagonals R k s)} :
    ((x * y : (BlockDiagonals R k s)) :
        Matrix (Σ i, s i) (Σ i, s i) R) =
      x * y :=
  rfl

theorem one {k : Type _} [DecidableEq k] {s : k → Type _} [∀ i, DecidableEq (s i)] :
    (1 : Matrix (Σ i, s i) (Σ i, s i) R).IsBlockDiagonal := by
  simp only [Matrix.IsBlockDiagonal, blockDiag'_one, blockDiagonal'_one]

@[reducible, instance]
def hasOne {k : Type _} [DecidableEq k] {s : k → Type _} [∀ i, DecidableEq (s i)] :
    One (BlockDiagonals R k s)
    where one := ⟨(1 : Matrix (Σ i, s i) (Σ i, s i) R), IsBlockDiagonal.one⟩

theorem coe_one {k : Type _} [DecidableEq k] {s : k → Type _} [∀ i, DecidableEq (s i)] :
    ((1 : (BlockDiagonals R k s)) :
        Matrix (Σ i, s i) (Σ i, s i) R) =
      1 :=
  rfl

theorem coe_nsmul {k : Type _} [DecidableEq k] {s : k → Type _} (n : ℕ)
    (x : (BlockDiagonals R k s)) :
    ((n • x : (BlockDiagonals R k s)) :
        Matrix (Σ i, s i) (Σ i, s i) R) =
      n • ↑x :=
  by simp_rw [← Nat.cast_smul_eq_nsmul R n, ← IsBlockDiagonal.coe_smul]

theorem npow {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
    [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] (n : ℕ) {x : Matrix (Σ i, s i) (Σ i, s i) R}
    (hx : x.IsBlockDiagonal) : (x ^ n).IsBlockDiagonal := by
  induction n with
  | zero =>
      simpa only [pow_zero] using IsBlockDiagonal.one
  | succ d hd =>
      simpa only [pow_succ] using IsBlockDiagonal.mul hd hx

@[reducible, instance]
def hasNpow {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
    [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] :
    Pow (BlockDiagonals R k s) ℕ
    where pow x n := ⟨(x : Matrix (Σ i, s i) (Σ i, s i) R) ^ n, IsBlockDiagonal.npow n x.2⟩

theorem coe_npow {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
    [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] (n : ℕ)
    (x : (BlockDiagonals R k s)) :
    ((x ^ n : (BlockDiagonals R k s)) :
        Matrix (Σ i, s i) (Σ i, s i) R) =
      x ^ n :=
  rfl

@[reducible, instance]
def semiring {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
    [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] :
    Semiring (BlockDiagonals R k s)
    where
  mul := (· * ·)
  left_distrib x y z := by
    ext
    simp only [IsBlockDiagonal.coe_mul, IsBlockDiagonal.coe_add, mul_add]
  right_distrib x y z := by
    ext
    simp only [IsBlockDiagonal.coe_mul, IsBlockDiagonal.coe_add, add_mul]
  zero_mul x := by
    ext
    simp only [IsBlockDiagonal.coe_mul, IsBlockDiagonal.coe_zero, MulZeroClass.zero_mul]
  mul_zero x := by
    ext
    simp only [IsBlockDiagonal.coe_mul, IsBlockDiagonal.coe_zero, MulZeroClass.mul_zero]
  mul_assoc x y z := by ext; simp only [IsBlockDiagonal.coe_mul, mul_assoc]
  one := 1
  one_mul x := by ext; simp only [IsBlockDiagonal.coe_mul, IsBlockDiagonal.coe_one, one_mul]
  mul_one x := by ext; simp only [IsBlockDiagonal.coe_mul, IsBlockDiagonal.coe_one, mul_one]
  natCast n := n • 1
  natCast_zero := by
    ext
    simp only [IsBlockDiagonal.coe_zero, zero_smul]
  natCast_succ a := by
    ext
    simp only [IsBlockDiagonal.coe_nsmul, IsBlockDiagonal.coe_one, IsBlockDiagonal.coe_add,
      add_smul, one_smul, add_comm]
  npow n x := x ^ n
  npow_zero x := by
    ext
    simp only [IsBlockDiagonal.coe_npow, IsBlockDiagonal.coe_one, pow_zero]
  npow_succ n x := by
    ext
    simp_rw [IsBlockDiagonal.coe_npow, pow_add, IsBlockDiagonal.coe_mul,
      pow_one, IsBlockDiagonal.coe_npow]

@[reducible, instance]
def algebra {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
    [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] :
    Algebra R (BlockDiagonals R k s)
    where
  algebraMap :=
  { toFun r :=
      ⟨algebraMap R (Matrix (Σ i, s i) (Σ i, s i) R) r, by
          rw [Algebra.algebraMap_eq_smul_one]
          exact Matrix.IsBlockDiagonal.smul Matrix.IsBlockDiagonal.one r⟩
    map_one' := by
      apply Subtype.ext
      exact map_one (algebraMap R (Matrix (Σ i, s i) (Σ i, s i) R))
    map_zero' := by
      apply Subtype.ext
      exact map_zero (algebraMap R (Matrix (Σ i, s i) (Σ i, s i) R))
    map_add' x y := by
      apply Subtype.ext
      exact map_add (algebraMap R (Matrix (Σ i, s i) (Σ i, s i) R)) x y
    map_mul' x y := by
      apply Subtype.ext
      exact map_mul (algebraMap R (Matrix (Σ i, s i) (Σ i, s i) R)) x y }
  commutes' r x := by
    apply Subtype.ext
    exact Algebra.commutes r (x : Matrix (Σ i, s i) (Σ i, s i) R)
  smul_def' r x := by
    apply Subtype.ext
    exact Algebra.smul_def r (x : Matrix (Σ i, s i) (Σ i, s i) R)

theorem coe_blockDiagonal'_blockDiag' {k : Type _} [DecidableEq k] {s : k → Type _}
    (x : (BlockDiagonals R k s)) :
    Matrix.blockDiagonal' (blockDiag' (x : Matrix (Σ i, s i) (Σ i, s i) R)) = x :=
  x.property

end IsBlockDiagonal

/-- Block-diagonal matrices are algebra-equivalent to block-indexed matrix families. -/
@[simps]
def isBlockDiagonalPiAlgEquiv {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
    [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] :
    (BlockDiagonals R k s) ≃ₐ[R] PiMat R k s
    where
  toFun x := blockDiag' (x : Matrix (Σ i, s i) (Σ i, s i) R)
  invFun x := ⟨blockDiagonal' x, Matrix.IsBlockDiagonal.blockDiagonal' x⟩
  left_inv x := by
    ext
    simp only [IsBlockDiagonal.coe_blockDiagonal'_blockDiag']
  right_inv x := by
    ext
    simp only [blockDiag'_blockDiagonal']
  map_add' x y := by
    change blockDiag' ((x : Matrix (Σ i, s i) (Σ i, s i) R) +
        (y : Matrix (Σ i, s i) (Σ i, s i) R)) =
      blockDiag' (x : Matrix (Σ i, s i) (Σ i, s i) R) +
        blockDiag' (y : Matrix (Σ i, s i) (Σ i, s i) R)
    exact blockDiag'_add _ _
  commutes' r := by
    ext i a b
    simp only [Algebra.algebraMap_eq_smul_one, IsBlockDiagonal.coe_smul,
      IsBlockDiagonal.coe_one, blockDiag'_smul, blockDiag'_one, Pi.smul_apply]
  map_mul' x y := by
    apply blockDiagonal'_injective
    calc
      blockDiagonal'
          (blockDiag' ((x * y : BlockDiagonals R k s) :
            Matrix (Σ i, s i) (Σ i, s i) R)) =
          ((x * y : BlockDiagonals R k s) :
            Matrix (Σ i, s i) (Σ i, s i) R) :=
        IsBlockDiagonal.coe_blockDiagonal'_blockDiag' (x * y)
      _ = (x : Matrix (Σ i, s i) (Σ i, s i) R) * y := rfl
      _ =
          blockDiagonal' (blockDiag' (x : Matrix (Σ i, s i) (Σ i, s i) R)) *
            blockDiagonal' (blockDiag' (y : Matrix (Σ i, s i) (Σ i, s i) R)) := by
        rw [IsBlockDiagonal.coe_blockDiagonal'_blockDiag' x,
          IsBlockDiagonal.coe_blockDiagonal'_blockDiag' y]
      _ = blockDiagonal'
          (blockDiag' (x : Matrix (Σ i, s i) (Σ i, s i) R) *
            blockDiag' (y : Matrix (Σ i, s i) (Σ i, s i) R)) := by
        rw [← blockDiagonal'_mul]
        rfl

namespace IsBlockDiagonal

theorem star {R : Type _} [CommSemiring R] [StarAddMonoid R] {k : Type _}
    [DecidableEq k] {s : k → Type _} {x : Matrix (Σ i, s i) (Σ i, s i) R} (hx : x.IsBlockDiagonal) :
    xᴴ.IsBlockDiagonal := by
  rw [IsBlockDiagonal]
  nth_rw 2 [← hx.eq]
  simp_rw [blockDiagonal'_conjTranspose, ← blockDiag'_conjTranspose]

@[reducible, instance]
def hasStar {R : Type _} [CommSemiring R] [StarAddMonoid R] {k : Type _}
    [DecidableEq k] {s : k → Type _} :
    Star (BlockDiagonals R k s)
    where star x := ⟨(x : Matrix (Σ i, s i) (Σ i, s i) R)ᴴ, IsBlockDiagonal.star x.property⟩

theorem coe_star {R : Type _} [CommSemiring R] [StarAddMonoid R] {k : Type _}
    [DecidableEq k] {s : k → Type _}
    (y : (BlockDiagonals R k s)) :
    ((Star.star y : BlockDiagonals R k s) : Matrix (Σ i, s i) (Σ i, s i) R) = yᴴ :=
  rfl

end IsBlockDiagonal

namespace isBlockDiagonalPiAlgEquiv

theorem map_star {R : Type _} [CommSemiring R] [StarAddMonoid R]
    {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _} [∀ i, Fintype (s i)]
    [∀ i, DecidableEq (s i)] (x : (BlockDiagonals R k s)) :
    Matrix.isBlockDiagonalPiAlgEquiv (star x) = star (Matrix.isBlockDiagonalPiAlgEquiv x) := by
  ext1
  simp_rw [Pi.star_apply, isBlockDiagonalPiAlgEquiv_apply, IsBlockDiagonal.coe_star,
    blockDiag'_conjTranspose]
  rfl

theorem symm_map_star {R : Type _} [CommSemiring R] [StarAddMonoid R]
    {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _} [∀ i, Fintype (s i)]
    [∀ i, DecidableEq (s i)] (x : PiMat R k s) :
    Matrix.isBlockDiagonalPiAlgEquiv.symm (star x) =
      star (Matrix.isBlockDiagonalPiAlgEquiv.symm x) := by
  ext1
  simp_rw [IsBlockDiagonal.coe_star, isBlockDiagonalPiAlgEquiv_symm_apply_coe,
    blockDiagonal'_conjTranspose]
  rfl

end isBlockDiagonalPiAlgEquiv

namespace Equiv

/-- A variant of `Equiv.sigmaProdDistrib` with the product coordinate first. -/
@[simps!]
def sigmaProdDistrib' {ι : Type _} (β : Type _) (α : ι → Type _) :
    (β × Σ i : ι, α i) ≃ Σ i : ι, β × α i := by
  let this : (Σ i : ι, β × α i) ≃ Σ i : ι, α i × β := by
    apply Equiv.sigmaCongrRight
    intro i
    exact Equiv.prodComm _ _
  exact ((Equiv.prodComm _ _).trans (Equiv.sigmaProdDistrib _ _)).trans this.symm

end Equiv

/-- Distribute a product of sigma types into a nested sigma type. -/
@[simps]
def sigmaProdSigma {α β : Type _} {ζ : α → Type _} {℘ : β → Type _} :
    ((Σ i, ζ i) × Σ i, ℘ i) ≃ Σ i j, ζ i × ℘ j
    where
  toFun x := by
    refine ⟨(Equiv.sigmaProdDistrib _ _ x).1, (Equiv.sigmaProdDistrib' _ _ x).1, (x.1.2, x.2.2)⟩
  invFun x := (⟨x.1, x.2.2.1⟩, ⟨x.2.1, x.2.2.2⟩)
  left_inv x := by
    ext
    <;> simp only [Equiv.sigmaProdDistrib'_apply_fst, Equiv.sigmaProdDistrib, Equiv.coe_fn_mk]
    <;> rfl
  right_inv x := by
    rcases x with ⟨i, j, z, p⟩
    rfl

namespace IsBlockDiagonal

theorem apply_of_ne {R : Type _} [CommSemiring R] {k : Type _} [DecidableEq k]
    {s : k → Type _} {x : Matrix (Σ i, s i) (Σ i, s i) R} (hx : x.IsBlockDiagonal) (i j : Σ i, s i)
    (h : i.1 ≠ j.1) : x i j = 0 := by
  rw [← hx.eq]
  simp_rw [blockDiagonal'_apply, blockDiag'_apply, dif_neg h]

theorem apply_of_ne_coe {R : Type _} [CommSemiring R] {k : Type _} [DecidableEq k] {s : k → Type _}
    (x : (BlockDiagonals R k s)) (i j : Σ i, s i)
    (h : i.fst ≠ j.fst) : (x : Matrix (Σ i, s i) (Σ i, s i) R) i j = 0 :=
  IsBlockDiagonal.apply_of_ne x.2 i j h

open scoped Kronecker

theorem kronecker_hMul {R : Type _} [CommSemiring R] {k : Type _} [DecidableEq k] {s : k → Type _}
    {x y : Matrix (Σ i, s i) (Σ i, s i) R} (hx : x.IsBlockDiagonal) :
    IsBlockDiagonal fun i j => (x ⊗ₖ y) (sigmaProdSigma.symm i) (sigmaProdSigma.symm j) := by
  rw [Matrix.IsBlockDiagonal, blockDiagonal'_ext]
  intro a b c d
  simp only [blockDiagonal'_apply', blockDiag'_apply, kroneckerMap_apply,
    sigmaProdSigma_symm_apply]
  split_ifs with h
  · congr <;> simp [h]
  · rw [hx.apply_of_ne, MulZeroClass.zero_mul]
    simpa [ne_eq]

end IsBlockDiagonal

/-- Conjugation by the block-diagonal/pi-matrix algebra equivalence on endomorphisms. -/
@[simps!]
def directSumLinearMapAlgEquivIsBlockDiagonalLinearMap {R : Type _} [CommSemiring R] {k : Type _}
    [Fintype k] [DecidableEq k] {s : k → Type _} [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] :
    ((PiMat R k s) →ₗ[R] PiMat R k s) ≃ₐ[R]
      (BlockDiagonals R k s) →ₗ[R]
        (BlockDiagonals R k s) :=
  isBlockDiagonalPiAlgEquiv.symm.toLinearEquiv.innerConj

end Matrix

variable {R k : Type _} [CommSemiring R] [Fintype k] [DecidableEq k] {s : k → Type _}
  [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)]

local notation x " ⊗ₘ " y => TensorProduct.map x y

local notation "ℍ_ " i => Matrix (s i) (s i) R

open Matrix

theorem TensorProduct.assoc_includeBlock {k : Type _} [DecidableEq k] {s : k → Type _} {i j : k} :
    (↑(TensorProduct.assoc R (PiMat R k s) (PiMat R k s)
              (PiMat R k s)).symm ∘ₗ
        (includeBlock : Matrix (s i) (s i) R →ₗ[R] PiMat R k s) ⊗ₘ
          (includeBlock : Matrix (s j) (s j) R →ₗ[R] PiMat R k s) ⊗ₘ
            (includeBlock : Matrix (s j) (s j) R →ₗ[R] PiMat R k s)) =
      (((includeBlock : Matrix (s i) (s i) R →ₗ[R] PiMat R k s) ⊗ₘ
            (includeBlock : Matrix (s j) (s j) R →ₗ[R] PiMat R k s)) ⊗ₘ
          (includeBlock : Matrix (s j) (s j) R →ₗ[R] PiMat R k s)) ∘ₗ
        ↑(TensorProduct.assoc R (Matrix (s i) (s i) R) (Matrix (s j) (s j) R)
              (Matrix (s j) (s j) R)).symm := by
  apply TensorProduct.ext_threefold'
  intro x y z
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.assoc_symm_tmul,
    TensorProduct.map_tmul]
