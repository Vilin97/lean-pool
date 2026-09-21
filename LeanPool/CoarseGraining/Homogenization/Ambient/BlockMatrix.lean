/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Ambient.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Block Matrix -/

namespace Homogenization

abbrev BlockCoord (d : ℕ) := Sum (Fin d) (Fin d)

/-- File-level typeclass cache for `Nonempty (BlockCoord d)`. -/
private instance instNonemptyBlockCoord (d : ℕ) [NeZero d] :
    Nonempty (BlockCoord d) := inferInstance

abbrev FullBlockVec (d : ℕ) := BlockCoord d → ℝ

abbrev FullBlockMat (d : ℕ) := Matrix (BlockCoord d) (BlockCoord d) ℝ

def toFullBlockVec {d : ℕ} (X : BlockVec d) : FullBlockVec d
  | Sum.inl i => X.1 i
  | Sum.inr i => X.2 i

def ofFullBlockVec {d : ℕ} (x : FullBlockVec d) : BlockVec d :=
  (fun i => x (Sum.inl i), fun i => x (Sum.inr i))

def toFullBlockMat {d : ℕ} (A : BlockMat d) : FullBlockMat d
  | Sum.inl i, Sum.inl j => A.upperLeft i j
  | Sum.inl i, Sum.inr j => A.upperRight i j
  | Sum.inr i, Sum.inl j => A.lowerLeft i j
  | Sum.inr i, Sum.inr j => A.lowerRight i j

def ofFullBlockMat {d : ℕ} (M : FullBlockMat d) : BlockMat d :=
  { upperLeft := fun i j => M (Sum.inl i) (Sum.inl j)
    upperRight := fun i j => M (Sum.inl i) (Sum.inr j)
    lowerLeft := fun i j => M (Sum.inr i) (Sum.inl j)
    lowerRight := fun i j => M (Sum.inr i) (Sum.inr j) }

def blockMatEntry {d : ℕ} (A : BlockMat d) : BlockCoord d → BlockCoord d → ℝ
  | Sum.inl i, Sum.inl j => A.upperLeft i j
  | Sum.inl i, Sum.inr j => A.upperRight i j
  | Sum.inr i, Sum.inl j => A.lowerLeft i j
  | Sum.inr i, Sum.inr j => A.lowerRight i j

def blockBasis {d : ℕ} : BlockCoord d → BlockVec d
  | Sum.inl i => (Pi.single i 1, 0)
  | Sum.inr i => (0, Pi.single i 1)

def IsSymmetricBlockMat {d : ℕ} (A : BlockMat d) : Prop :=
  ∀ α β : BlockCoord d, blockMatEntry A α β = blockMatEntry A β α

@[simp] theorem toFullBlockVec_ofFullBlockVec {d : ℕ} (x : FullBlockVec d) :
    toFullBlockVec (ofFullBlockVec x) = x := by
  funext α
  cases α <;> rfl

@[simp] theorem ofFullBlockVec_toFullBlockVec {d : ℕ} (X : BlockVec d) :
    ofFullBlockVec (toFullBlockVec X) = X := by
  cases X
  rfl

@[simp] theorem ofFullBlockVec_add {d : ℕ} (x y : FullBlockVec d) :
    ofFullBlockVec (x + y) = ofFullBlockVec x + ofFullBlockVec y := by
  rfl

@[simp] theorem ofFullBlockVec_smul {d : ℕ} (c : ℝ) (x : FullBlockVec d) :
    ofFullBlockVec (c • x) = c • ofFullBlockVec x := by
  rfl

@[simp] theorem toFullBlockMat_ofFullBlockMat {d : ℕ} (M : FullBlockMat d) :
    toFullBlockMat (ofFullBlockMat M) = M := by
  ext α β
  cases α <;> cases β <;> rfl

@[simp] theorem ofFullBlockMat_toFullBlockMat {d : ℕ} (A : BlockMat d) :
    ofFullBlockMat (toFullBlockMat A) = A := by
  cases A
  rfl

@[simp] theorem blockMatEntry_ofFullBlockMat {d : ℕ} (M : FullBlockMat d)
    (α β : BlockCoord d) :
    blockMatEntry (ofFullBlockMat M) α β = M α β := by
  cases α <;> cases β <;> rfl

theorem dotProduct_toFullBlockVec {d : ℕ} (X Y : BlockVec d) :
    dotProduct (toFullBlockVec X) (toFullBlockVec Y) = blockVecDot X Y := by
  rw [dotProduct, Fintype.sum_sum_type]
  simp [toFullBlockVec, blockVecDot, vecDot]

theorem toFullBlockVec_blockMatVecMul {d : ℕ} (A : BlockMat d) (X : BlockVec d) :
    toFullBlockVec (blockMatVecMul A X) = Matrix.mulVec (toFullBlockMat A) (toFullBlockVec X) := by
  funext α
  cases α with
  | inl i =>
      rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
      simp [toFullBlockVec, blockMatVecMul, toFullBlockMat, matVecMul]
  | inr i =>
      rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
      simp [toFullBlockVec, blockMatVecMul, toFullBlockMat, matVecMul]

theorem blockVecDot_blockMatVecMul_eq_toLinearMap₂' {d : ℕ}
    (A : BlockMat d) (X Y : BlockVec d) :
    blockVecDot X (blockMatVecMul A Y) =
      Matrix.toLinearMap₂' ℝ (toFullBlockMat A) (toFullBlockVec X) (toFullBlockVec Y) := by
  rw [Matrix.toLinearMap₂'_apply']
  rw [← dotProduct_toFullBlockVec X (blockMatVecMul A Y)]
  rw [toFullBlockVec_blockMatVecMul]

theorem isSymmetricBlockMat_of_isSymm {d : ℕ} {M : FullBlockMat d} (hM : M.IsSymm) :
    IsSymmetricBlockMat (ofFullBlockMat M) := by
  intro α β
  simpa using (hM.apply α β).symm

theorem isSymmetricBlockMat_ofFullBlockMat_sub {d : ℕ} {A B : BlockMat d}
    (hA : IsSymmetricBlockMat A) (hB : IsSymmetricBlockMat B) :
    IsSymmetricBlockMat (ofFullBlockMat (toFullBlockMat A - toFullBlockMat B)) := by
  intro α β
  have hA' := hA α β
  have hB' := hB α β
  cases α <;> cases β <;>
    simp [blockMatEntry, ofFullBlockMat, toFullBlockMat] at hA' hB' ⊢ <;>
    linarith

theorem vecDot_single_left {d : ℕ} (i : Fin d) (y : Vec d) :
    vecDot (Pi.single i 1) y = y i := by
  rw [vecDot, Finset.sum_eq_single i]
  · simp
  · intro j _ hij
    simp [Pi.single_eq_of_ne hij]
  · simp

theorem vecDot_single_right {d : ℕ} (x : Vec d) (i : Fin d) :
    vecDot x (Pi.single i 1) = x i := by
  rw [vecDot, Finset.sum_eq_single i]
  · simp
  · intro j _ hij
    simp [Pi.single_eq_of_ne hij]
  · simp

theorem matVecMul_single {d : ℕ} (A : Mat d) (j : Fin d) :
    matVecMul A (Pi.single j 1) = fun i => A i j := by
  funext i
  rw [matVecMul, Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    simp [Pi.single_eq_of_ne hk]
  · simp

theorem matVecMul_zero {d : ℕ} (A : Mat d) :
    matVecMul A 0 = 0 := by
  funext i
  simp [matVecMul]

theorem add_matVecMul {d : ℕ} (A B : Mat d) (x : Vec d) :
    matVecMul (A + B) x = matVecMul A x + matVecMul B x := by
  funext i
  simp [matVecMul, Finset.sum_add_distrib, add_mul]

theorem smul_matVecMul {d : ℕ} (c : ℝ) (A : Mat d) (x : Vec d) :
    matVecMul (c • A) x = c • matVecMul A x := by
  funext i
  calc
    matVecMul (c • A) x i = ∑ j, c * (A i j * x j) := by
      simp [matVecMul, mul_assoc]
    _ = c * ∑ j, A i j * x j := by
      symm
      simpa using (Finset.mul_sum Finset.univ (fun j => A i j * x j) c)
    _ = (c • matVecMul A x) i := by
      simp [matVecMul]

theorem neg_matVecMul {d : ℕ} (A : Mat d) (x : Vec d) :
    matVecMul (-A) x = -matVecMul A x := by
  simpa using smul_matVecMul (-1) A x

theorem sub_matVecMul {d : ℕ} (A B : Mat d) (x : Vec d) :
    matVecMul (A - B) x = matVecMul A x - matVecMul B x := by
  rw [sub_eq_add_neg, add_matVecMul, neg_matVecMul, sub_eq_add_neg]

theorem vecDot_zero_left {d : ℕ} (y : Vec d) :
    vecDot 0 y = 0 := by
  simp [vecDot]

theorem vecDot_zero_right {d : ℕ} (x : Vec d) :
    vecDot x 0 = 0 := by
  simp [vecDot]

theorem vecDot_comm {d : ℕ} (x y : Vec d) :
    vecDot x y = vecDot y x := by
  simp [vecDot, mul_comm]

theorem matVecMul_add {d : ℕ} (A : Mat d) (x y : Vec d) :
    matVecMul A (x + y) = matVecMul A x + matVecMul A y := by
  funext i
  simp [matVecMul, Finset.sum_add_distrib, mul_add]

theorem matVecMul_smul {d : ℕ} (A : Mat d) (c : ℝ) (x : Vec d) :
    matVecMul A (c • x) = c • matVecMul A x := by
  funext i
  simp [matVecMul, Finset.mul_sum, mul_left_comm]

theorem matVecMul_neg {d : ℕ} (A : Mat d) (x : Vec d) :
    matVecMul A (-x) = -matVecMul A x := by
  simpa using matVecMul_smul A (-1) x

theorem matVecMul_mul {d : ℕ} (A B : Mat d) (x : Vec d) :
    matVecMul A (matVecMul B x) = matVecMul (A * B) x := by
  change A.mulVec (B.mulVec x) = (A * B).mulVec x
  exact Matrix.mulVec_mulVec x A B

theorem vecDot_add_left {d : ℕ} (x y z : Vec d) :
    vecDot (x + y) z = vecDot x z + vecDot y z := by
  simp [vecDot, Finset.sum_add_distrib, add_mul]

theorem vecDot_add_right {d : ℕ} (x y z : Vec d) :
    vecDot x (y + z) = vecDot x y + vecDot x z := by
  simp [vecDot, Finset.sum_add_distrib, mul_add]

theorem vecDot_smul_left {d : ℕ} (c : ℝ) (x y : Vec d) :
    vecDot (c • x) y = c * vecDot x y := by
  calc
    vecDot (c • x) y = ∑ i, c * (x i * y i) := by
      simp [vecDot, mul_assoc]
    _ = c * ∑ i, x i * y i := by
      symm
      simpa using (Finset.mul_sum Finset.univ (fun i => x i * y i) c)
    _ = c * vecDot x y := by
      rfl

theorem vecDot_smul_right {d : ℕ} (x y : Vec d) (c : ℝ) :
    vecDot x (c • y) = c * vecDot x y := by
  calc
    vecDot x (c • y) = ∑ i, c * (x i * y i) := by
      simp [vecDot, mul_left_comm]
    _ = c * ∑ i, x i * y i := by
      symm
      simpa using (Finset.mul_sum Finset.univ (fun i => x i * y i) c)
    _ = c * vecDot x y := by
      rfl

theorem vecDot_neg_left {d : ℕ} (x y : Vec d) :
    vecDot (-x) y = -vecDot x y := by
  simpa using vecDot_smul_left (-1) x y

theorem vecDot_neg_right {d : ℕ} (x y : Vec d) :
    vecDot x (-y) = -vecDot x y := by
  simpa using vecDot_smul_right x y (-1)

theorem vecDot_matVecMul_transpose {d : ℕ} (x y : Vec d) (A : Mat d) :
    vecDot x (matVecMul (matTranspose A) y) = vecDot (matVecMul A x) y := by
  calc
    vecDot x (matVecMul (matTranspose A) y)
      = ∑ i, ∑ j, x i * (A j i * y j) := by
          unfold vecDot matVecMul matTranspose
          congr with i
          rw [Finset.mul_sum]
          simp [Matrix.transpose_apply]
    _ = ∑ j, ∑ i, (A j i * x i) * y j := by
          rw [Finset.sum_comm]
          congr with j
          congr with i
          ring
    _ = ∑ j, (∑ i, A j i * x i) * y j := by
          congr with j
          exact (Finset.sum_mul Finset.univ (fun i => A j i * x i) (y j)).symm
    _ = vecDot (matVecMul A x) y := by
          rfl

theorem transpose_mul_symm_mul_isSymm {d : ℕ} (K S : Mat d)
    (hS : S.IsSymm) :
    (((matTranspose K) * S * K)).IsSymm := by
  unfold Matrix.IsSymm
  simpa [matTranspose, Matrix.transpose_mul, Matrix.mul_assoc] using
    congrArg (fun M => (matTranspose K) * M * K) hS

theorem isUnit_det_smul {d : ℕ} {A : Mat d} (hdet : IsUnit A.det)
    {c : ℝ} (hc : c ≠ 0) :
    IsUnit (c • A).det := by
  rw [Matrix.det_smul]
  exact isUnit_iff_ne_zero.mpr <|
    mul_ne_zero (pow_ne_zero _ hc) (isUnit_iff_ne_zero.mp hdet)

theorem nonsing_inv_smul {d : ℕ} {A : Mat d} (c : ℝ) (hc : c ≠ 0)
    (hdet : IsUnit A.det) :
    (c • A)⁻¹ = c⁻¹ • A⁻¹ := by
  let : Invertible c := invertibleOfNonzero hc
  simpa using (Matrix.inv_smul (A := A) c hdet)

theorem basis_sum_pairing {d : ℕ} (M : Mat d) (i j : Fin d) :
    vecDot (Pi.single i 1 + Pi.single j 1)
      (matVecMul M (Pi.single i 1 + Pi.single j 1)) =
      M i i + M i j + M j i + M j j := by
  calc
    vecDot (Pi.single i 1 + Pi.single j 1) (matVecMul M (Pi.single i 1 + Pi.single j 1))
      = vecDot (Pi.single i 1 + Pi.single j 1)
          (matVecMul M (Pi.single i 1) + matVecMul M (Pi.single j 1)) := by
            rw [matVecMul_add]
    _ = vecDot (Pi.single i 1 + Pi.single j 1) (matVecMul M (Pi.single i 1)) +
          vecDot (Pi.single i 1 + Pi.single j 1) (matVecMul M (Pi.single j 1)) := by
            rw [vecDot_add_right]
    _ = (vecDot (Pi.single i 1) (matVecMul M (Pi.single i 1)) +
          vecDot (Pi.single j 1) (matVecMul M (Pi.single i 1))) +
          (vecDot (Pi.single i 1) (matVecMul M (Pi.single j 1)) +
            vecDot (Pi.single j 1) (matVecMul M (Pi.single j 1))) := by
              rw [vecDot_add_left, vecDot_add_left]
    _ = M i i + M i j + M j i + M j j := by
          simp [vecDot_single_left, matVecMul_single]
          ac_rfl

theorem blockMatVecMul_add {d : ℕ} (A : BlockMat d) (X Y : BlockVec d) :
    blockMatVecMul A (X + Y) = blockMatVecMul A X + blockMatVecMul A Y := by
  ext <;> simp [blockMatVecMul, matVecMul_add, add_left_comm, add_comm]

theorem blockMatVecMul_ofFullBlockMat_sub {d : ℕ}
    (A B : BlockMat d) (X : BlockVec d) :
    blockMatVecMul (ofFullBlockMat (toFullBlockMat A - toFullBlockMat B)) X =
      blockMatVecMul A X - blockMatVecMul B X := by
  rcases X with ⟨x, y⟩
  ext i
  · change
      (matVecMul (A.upperLeft - B.upperLeft) x +
          matVecMul (A.upperRight - B.upperRight) y) i =
        (matVecMul A.upperLeft x + matVecMul A.upperRight y -
            (matVecMul B.upperLeft x + matVecMul B.upperRight y)) i
    rw [sub_matVecMul, sub_matVecMul]
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  · change
      (matVecMul (A.lowerLeft - B.lowerLeft) x +
          matVecMul (A.lowerRight - B.lowerRight) y) i =
        (matVecMul A.lowerLeft x + matVecMul A.lowerRight y -
            (matVecMul B.lowerLeft x + matVecMul B.lowerRight y)) i
    rw [sub_matVecMul, sub_matVecMul]
    simp only [Pi.add_apply, Pi.sub_apply]
    ring

theorem blockVecDot_add_left {d : ℕ} (X Y Z : BlockVec d) :
    blockVecDot (X + Y) Z = blockVecDot X Z + blockVecDot Y Z := by
  rcases X with ⟨x₁, x₂⟩
  rcases Y with ⟨y₁, y₂⟩
  rcases Z with ⟨z₁, z₂⟩
  change vecDot (x₁ + y₁) z₁ + vecDot (x₂ + y₂) z₂ =
    (vecDot x₁ z₁ + vecDot x₂ z₂) + (vecDot y₁ z₁ + vecDot y₂ z₂)
  rw [vecDot_add_left, vecDot_add_left]
  ring

theorem blockVecDot_add_right {d : ℕ} (X Y Z : BlockVec d) :
    blockVecDot X (Y + Z) = blockVecDot X Y + blockVecDot X Z := by
  rcases X with ⟨x₁, x₂⟩
  rcases Y with ⟨y₁, y₂⟩
  rcases Z with ⟨z₁, z₂⟩
  change vecDot x₁ (y₁ + z₁) + vecDot x₂ (y₂ + z₂) =
    (vecDot x₁ y₁ + vecDot x₂ y₂) + (vecDot x₁ z₁ + vecDot x₂ z₂)
  rw [vecDot_add_right, vecDot_add_right]
  ring

theorem blockVecDot_sub_right {d : ℕ} (X Y Z : BlockVec d) :
    blockVecDot X (Y - Z) = blockVecDot X Y - blockVecDot X Z := by
  rcases X with ⟨p, q⟩
  rcases Y with ⟨u, v⟩
  rcases Z with ⟨w, z⟩
  simp [blockVecDot, vecDot, mul_sub]
  abel

theorem blockVecDot_comm {d : ℕ} (X Y : BlockVec d) :
    blockVecDot X Y = blockVecDot Y X := by
  rcases X with ⟨p, q⟩
  rcases Y with ⟨u, v⟩
  simp [blockVecDot, vecDot_comm]

@[simp] theorem blockVecDot_swap_right {d : ℕ} (X Y : BlockVec d) :
    blockVecDot X Y.swap = blockVecDot (X.2, X.1) Y := by
  rcases X with ⟨p, q⟩
  rcases Y with ⟨u, v⟩
  simp [blockVecDot, add_comm]

theorem blockMatVecMul_smul {d : ℕ} (A : BlockMat d) (c : ℝ) (X : BlockVec d) :
    blockMatVecMul A (c • X) = c • blockMatVecMul A X := by
  ext <;> simp [blockMatVecMul, matVecMul_smul, smul_add]

theorem blockVecDot_smul_left {d : ℕ} (c : ℝ) (X Y : BlockVec d) :
    blockVecDot (c • X) Y = c * blockVecDot X Y := by
  simp [blockVecDot, vecDot_smul_left, mul_add]

theorem blockVecDot_smul_right {d : ℕ} (X Y : BlockVec d) (c : ℝ) :
    blockVecDot X (c • Y) = c * blockVecDot X Y := by
  simp [blockVecDot, vecDot_smul_right, mul_add]

theorem blockVecDot_blockMatVecMul_ofFullBlockMat_sub {d : ℕ}
    (A B : BlockMat d) (X : BlockVec d) :
    blockVecDot X
        (blockMatVecMul (ofFullBlockMat (toFullBlockMat A - toFullBlockMat B)) X) =
      blockVecDot X (blockMatVecMul A X) -
        blockVecDot X (blockMatVecMul B X) := by
  rw [blockMatVecMul_ofFullBlockMat_sub, blockVecDot_sub_right]

theorem blockVecDot_blockMatVecMul_sub_eq_ofFullBlockMat_sub {d : ℕ}
    (A B : BlockMat d) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul A X) -
        blockVecDot X (blockMatVecMul B X) =
      blockVecDot X
        (blockMatVecMul (ofFullBlockMat (toFullBlockMat A - toFullBlockMat B)) X) :=
  (blockVecDot_blockMatVecMul_ofFullBlockMat_sub A B X).symm

theorem blockVecDot_nonneg {d : ℕ} (X : BlockVec d) :
    0 ≤ blockVecDot X X := by
  rcases X with ⟨p, q⟩
  have hp : 0 ≤ vecDot p p := vecNormSq_nonneg p
  have hq : 0 ≤ vecDot q q := vecNormSq_nonneg q
  simpa [blockVecDot, vecNormSq] using add_nonneg hp hq

theorem sq_blockVecDot_le_blockVecDot_mul_blockVecDot {d : ℕ} (X Y : BlockVec d) :
    blockVecDot X Y ^ 2 ≤ blockVecDot X X * blockVecDot Y Y := by
  rw [← dotProduct_toFullBlockVec X Y, ← dotProduct_toFullBlockVec X X,
    ← dotProduct_toFullBlockVec Y Y]
  simpa [dotProduct, pow_two] using
    (Finset.sum_mul_sq_le_sq_mul_sq
      (s := Finset.univ) (f := toFullBlockVec X) (g := toFullBlockVec Y))

theorem blockVecDot_sub_self_le {d : ℕ} (X Y : BlockVec d) :
    blockVecDot (X - Y) (X - Y) ≤ 2 * (blockVecDot X X + blockVecDot Y Y) := by
  rcases X with ⟨p, q⟩
  rcases Y with ⟨u, v⟩
  change vecNormSq (p - u) + vecNormSq (q - v) ≤
    2 * ((vecNormSq p + vecNormSq q) + (vecNormSq u + vecNormSq v))
  have hp := vecNormSq_sub_le p u
  have hq := vecNormSq_sub_le q v
  nlinarith

/-- A block matrix acts linearly on doubled vectors. -/
def blockMatLinearMap {d : ℕ} (A : BlockMat d) : BlockVec d →ₗ[ℝ] BlockVec d where
  toFun := blockMatVecMul A
  map_add' := blockMatVecMul_add A
  map_smul' := blockMatVecMul_smul A

@[simp] theorem blockMatLinearMap_apply {d : ℕ} (A : BlockMat d) (X : BlockVec d) :
    blockMatLinearMap A X = blockMatVecMul A X :=
  rfl

/-- A block matrix acts continuously on doubled vectors. Continuity is automatic
because the carrier is finite-dimensional. -/
noncomputable def blockMatContinuousLinearMap {d : ℕ} (A : BlockMat d) :
    BlockVec d →L[ℝ] BlockVec d :=
  ⟨blockMatLinearMap A, (blockMatLinearMap A).continuous_of_finiteDimensional⟩

@[simp] theorem blockMatContinuousLinearMap_apply {d : ℕ} (A : BlockMat d) (X : BlockVec d) :
    blockMatContinuousLinearMap A X = blockMatVecMul A X :=
  rfl

theorem blockBasis_pairing {d : ℕ} (A : BlockMat d) (α β : BlockCoord d) :
    blockVecDot (blockBasis α) (blockMatVecMul A (blockBasis β)) = blockMatEntry A α β := by
  cases α <;> cases β <;> simp [blockBasis, blockMatEntry, blockVecDot, blockMatVecMul,
    vecDot_single_left, matVecMul_single, matVecMul_zero, vecDot_zero_left]

theorem blockBasis_sum_pairing {d : ℕ} (A : BlockMat d) (α β : BlockCoord d) :
    blockVecDot (blockBasis α + blockBasis β) (blockMatVecMul A (blockBasis α + blockBasis β)) =
      blockMatEntry A α α + blockMatEntry A α β + blockMatEntry A β α + blockMatEntry A β β := by
  calc
    blockVecDot (blockBasis α + blockBasis β) (blockMatVecMul A (blockBasis α + blockBasis β))
      = blockVecDot (blockBasis α + blockBasis β)
          (blockMatVecMul A (blockBasis α) + blockMatVecMul A (blockBasis β)) := by
            rw [blockMatVecMul_add]
    _ = blockVecDot (blockBasis α + blockBasis β) (blockMatVecMul A (blockBasis α)) +
          blockVecDot (blockBasis α + blockBasis β) (blockMatVecMul A (blockBasis β)) := by
            rw [blockVecDot_add_right]
    _ = (blockVecDot (blockBasis α) (blockMatVecMul A (blockBasis α)) +
          blockVecDot (blockBasis β) (blockMatVecMul A (blockBasis α))) +
          (blockVecDot (blockBasis α) (blockMatVecMul A (blockBasis β)) +
            blockVecDot (blockBasis β) (blockMatVecMul A (blockBasis β))) := by
              rw [blockVecDot_add_left, blockVecDot_add_left]
    _ = blockMatEntry A α α + blockMatEntry A α β + blockMatEntry A β α + blockMatEntry A β β := by
          rw [blockBasis_pairing, blockBasis_pairing, blockBasis_pairing, blockBasis_pairing]
          ac_rfl

def blockReflect {d : ℕ} (A : BlockMat d) : BlockMat d :=
  { upperLeft := A.lowerRight
    upperRight := A.lowerLeft
    lowerLeft := A.upperRight
    lowerRight := A.upperLeft }

theorem isSymmetricBlockMat_blockReflect {d : ℕ} {A : BlockMat d}
    (hA : IsSymmetricBlockMat A) :
    IsSymmetricBlockMat (blockReflect A) := by
  intro α β
  cases α with
  | inl i =>
      cases β with
      | inl j =>
          simpa [blockReflect, blockMatEntry] using hA (Sum.inr i) (Sum.inr j)
      | inr j =>
          simpa [blockReflect, blockMatEntry] using hA (Sum.inr i) (Sum.inl j)
  | inr i =>
      cases β with
      | inl j =>
          simpa [blockReflect, blockMatEntry] using hA (Sum.inl i) (Sum.inr j)
      | inr j =>
          simpa [blockReflect, blockMatEntry] using hA (Sum.inl i) (Sum.inl j)

@[simp] theorem blockReflect_upperLeft {d : ℕ} (A : BlockMat d) :
    (blockReflect A).upperLeft = A.lowerRight := rfl

@[simp] theorem blockReflect_upperRight {d : ℕ} (A : BlockMat d) :
    (blockReflect A).upperRight = A.lowerLeft := rfl

@[simp] theorem blockReflect_lowerLeft {d : ℕ} (A : BlockMat d) :
    (blockReflect A).lowerLeft = A.upperRight := rfl

@[simp] theorem blockReflect_lowerRight {d : ℕ} (A : BlockMat d) :
    (blockReflect A).lowerRight = A.upperLeft := rfl

@[simp] theorem blockReflect_blockReflect {d : ℕ} (A : BlockMat d) :
    blockReflect (blockReflect A) = A := by
  rfl

/--
Löwner order on finite-dimensional real matrices, expressed through the quadratic
form `\frac12 x \cdot A x`.
-/
def MatLoewnerLE {d : ℕ} (A B : Mat d) : Prop :=
  ∀ x : Vec d,
    (1 / 2 : ℝ) * vecDot x (matVecMul A x) ≤
      (1 / 2 : ℝ) * vecDot x (matVecMul B x)

/--
Löwner order on doubled block matrices, expressed through the quadratic form
`\frac12 X \cdot \mathbf A X`.
-/
def BlockMatLoewnerLE {d : ℕ} (A B : BlockMat d) : Prop :=
  ∀ X : BlockVec d,
    (1 / 2 : ℝ) * blockVecDot X (blockMatVecMul A X) ≤
      (1 / 2 : ℝ) * blockVecDot X (blockMatVecMul B X)

theorem MatLoewnerLE.refl {d : ℕ} (A : Mat d) : MatLoewnerLE A A := by
  intro x
  exact le_rfl

theorem MatLoewnerLE.trans {d : ℕ} {A B C : Mat d}
    (hAB : MatLoewnerLE A B) (hBC : MatLoewnerLE B C) :
    MatLoewnerLE A C := by
  intro x
  exact le_trans (hAB x) (hBC x)

theorem BlockMatLoewnerLE.refl {d : ℕ} (A : BlockMat d) : BlockMatLoewnerLE A A := by
  intro X
  exact le_rfl

theorem BlockMatLoewnerLE.trans {d : ℕ} {A B C : BlockMat d}
    (hAB : BlockMatLoewnerLE A B) (hBC : BlockMatLoewnerLE B C) :
    BlockMatLoewnerLE A C := by
  intro X
  exact le_trans (hAB X) (hBC X)

@[simp] theorem blockMatVecMul_blockReflect {d : ℕ} (A : BlockMat d) (X : BlockVec d) :
    blockMatVecMul (blockReflect A) X =
      (blockMatVecMul A (X.2, X.1)).swap := by
  rcases A with ⟨ul, ur, ll, lr⟩
  rcases X with ⟨p, q⟩
  ext <;> simp [blockReflect, blockMatVecMul, add_comm]

@[simp] theorem blockVecDot_blockMatVecMul_blockReflect {d : ℕ} (A : BlockMat d)
    (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (blockReflect A) X) =
      blockVecDot (X.2, X.1) (blockMatVecMul A (X.2, X.1)) := by
  rcases X with ⟨p, q⟩
  simp [blockReflect, blockMatVecMul, blockVecDot, add_comm]

theorem blockMat_ext {d : ℕ} {A B : BlockMat d}
    (hUL : A.upperLeft = B.upperLeft)
    (hUR : A.upperRight = B.upperRight)
    (hLL : A.lowerLeft = B.lowerLeft)
    (hLR : A.lowerRight = B.lowerRight) :
    A = B := by
  cases A
  cases B
  simp at hUL hUR hLL hLR
  simp [hUL, hUR, hLL, hLR]

end Homogenization
