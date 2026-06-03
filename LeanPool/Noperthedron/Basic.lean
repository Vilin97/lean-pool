/-
Copyright (c) 2026 Reuben Steenekamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reuben Steenekamp
-/

import Init.Data.Int.DivMod.Basic
import Mathlib.Algebra.Group.AddChar
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Noperthedron

Auxiliary rotation, projection, and symmetry lemmas from the noperthedron
formalization.
-/

noncomputable section
open Real

namespace LeanPool.Noperthedron

/-- Two-dimensional Euclidean space over `ℝ`. -/
notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
/-- Three-dimensional Euclidean space over `ℝ`. -/
notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Multiplication of continuous linear endomorphisms is composition. -/
theorem mul_eq_comp {R A : Type*} [Semiring R] [AddCommMonoid A] [Module R A]
    [TopologicalSpace A] {f g : A →L[R] A} : g * f = g ∘L f := rfl

/-- The image of a composition of continuous linear maps factors through the images. -/
theorem comp_image {R A B C : Type*} [Semiring R] [AddCommMonoid A] [Module R A]
    [TopologicalSpace A] [AddCommMonoid B] [Module R B] [TopologicalSpace B]
    [AddCommMonoid C] [Module R C] [TopologicalSpace C]
    (S : Set A) (g : B →L[R] C) (f : A →L[R] B) :
    ⇑(g ∘L f) '' S = ⇑g '' (⇑f '' S) := by
  ext p; simp

/-- The matrix of the counterclockwise rotation of the plane by angle `α`. -/
@[simp]
def rot2Mat (α : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun
    | 0, 0 => Real.cos α
    | 0, 1 => -Real.sin α
    | 1, 0 => Real.sin α
    | 1, 1 => Real.cos α

/-- The additive character sending an angle to the corresponding planar rotation. -/
@[simp]
def rot2 : AddChar ℝ (ℝ² →L[ℝ] ℝ²) where
  toFun α := (rot2Mat α).toEuclideanLin.toContinuousLinearMap
  map_zero_eq_one' := by
    ext v i
    fin_cases i <;> simp [Matrix.toLpLin_apply, Matrix.mulVec]
  map_add_eq_mul' := by
    intro α β
    ext v i
    fin_cases i <;>
      simp [Matrix.toLpLin_apply, Matrix.mulVec_eq_sum, rot2Mat, cos_add, sin_add] <;>
      ring_nf

theorem rot2_180 : rot2 π = -1 := by
  ext v i
  fin_cases i <;> simp [Matrix.toLpLin_apply, Matrix.mulVec_eq_sum]

theorem rot2_neg180 : rot2 (-π) = -1 := by
  ext v i
  fin_cases i <;> simp [Matrix.toLpLin_apply, Matrix.mulVec_eq_sum]

theorem rot2_360 : rot2 (2 * π) = 1 := by
  ext v i
  fin_cases i <;> simp [Matrix.toLpLin_apply, Matrix.mulVec_eq_sum]

theorem rot2_neg360 : rot2 (-(2 * π)) = 1 := by
  ext v i
  fin_cases i <;> simp [Matrix.toLpLin_apply, Matrix.mulVec_eq_sum]

theorem rot2_k360 {k : ℤ} : rot2 (k * (2 * π)) = 1 := by
  induction k with
  | zero => simp
  | succ n h =>
      simp only [Int.cast_add, Int.cast_one, one_mul, right_distrib,
        AddChar.map_add_eq_mul, h, rot2_360]
  | pred n h =>
      simp only [Int.cast_neg, neg_mul] at h
      simp only [sub_eq_add_neg, Int.cast_add, Int.cast_neg, Int.cast_one, neg_mul,
        one_mul, mul_one, right_distrib, AddChar.map_add_eq_mul, h, rot2_neg360]

/-- The matrix of rotation about the `x`-axis by angle `α`. -/
@[simp]
def rot3xMat (α : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun
    | 0, 0 => 1
    | 0, 1 => 0
    | 0, 2 => 0
    | 1, 0 => 0
    | 1, 1 => Real.cos α
    | 1, 2 => -Real.sin α
    | 2, 0 => 0
    | 2, 1 => Real.sin α
    | 2, 2 => Real.cos α

/-- The additive character of rotations about the `x`-axis. -/
@[simp]
def rot3x : AddChar ℝ (ℝ³ →L[ℝ] ℝ³) where
  toFun α := (rot3xMat α).toEuclideanLin.toContinuousLinearMap
  map_zero_eq_one' := by
    ext v i
    fin_cases i <;>
      simp [Matrix.toLpLin_apply, Matrix.mulVec_eq_sum, Fin.sum_univ_three]
  map_add_eq_mul' α β := by
    ext v i
    fin_cases i <;>
      simp [rot3xMat, cos_add, sin_add, ContinuousLinearMap.mul_def,
        Matrix.toLpLin_apply, Matrix.mulVec_eq_sum, Fin.sum_univ_three] <;>
      ring_nf

/-- The matrix of rotation about the `y`-axis by angle `α`. -/
@[simp]
def rot3yMat (α : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun
    | 0, 0 => Real.cos α
    | 0, 1 => 0
    | 0, 2 => -Real.sin α
    | 1, 0 => 0
    | 1, 1 => 1
    | 1, 2 => 0
    | 2, 0 => Real.sin α
    | 2, 1 => 0
    | 2, 2 => Real.cos α

/-- The additive character of rotations about the `y`-axis. -/
@[simps]
def rot3y : AddChar ℝ (ℝ³ →L[ℝ] ℝ³) where
  toFun α := (rot3yMat α).toEuclideanLin.toContinuousLinearMap
  map_zero_eq_one' := by
    ext v i
    fin_cases i <;>
      simp [Matrix.toLpLin_apply, Matrix.mulVec_eq_sum, Fin.sum_univ_three]
  map_add_eq_mul' α β := by
    ext v i
    fin_cases i <;>
      simp [rot3yMat, cos_add, sin_add, ContinuousLinearMap.mul_def,
        Matrix.toLpLin_apply, Matrix.mulVec_eq_sum, Fin.sum_univ_three] <;>
      ring_nf

/-- The matrix of rotation about the `z`-axis by angle `α`. -/
@[simp]
def rot3zMat (α : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun
    | 0, 0 => Real.cos α
    | 0, 1 => -Real.sin α
    | 0, 2 => 0
    | 1, 0 => Real.sin α
    | 1, 1 => Real.cos α
    | 1, 2 => 0
    | 2, 0 => 0
    | 2, 1 => 0
    | 2, 2 => 1

/-- The additive character of rotations about the `z`-axis. -/
@[simps]
def rot3z : AddChar ℝ (ℝ³ →L[ℝ] ℝ³) where
  toFun α := (rot3zMat α).toEuclideanLin.toContinuousLinearMap
  map_zero_eq_one' := by
    ext v i
    fin_cases i <;>
      simp [Matrix.toLpLin_apply, Matrix.mulVec_eq_sum, Fin.sum_univ_three]
  map_add_eq_mul' α β := by
    ext v i
    fin_cases i <;>
      simp [rot3zMat, cos_add, sin_add, ContinuousLinearMap.mul_def,
        Matrix.toLpLin_apply, Matrix.mulVec_eq_sum, Fin.sum_univ_three] <;>
      ring_nf

/-- Selects the coordinate-axis rotation matrix for a three-dimensional axis index. -/
def rot3Mat : Fin 3 → ℝ → Matrix (Fin 3) (Fin 3) ℝ
  | 0 => rot3xMat
  | 1 => rot3yMat
  | 2 => rot3zMat

/-- Selects the coordinate-axis rotation additive character for a three-dimensional axis index. -/
def rot3 : Fin 3 → AddChar ℝ (ℝ³ →L[ℝ] ℝ³)
  | 0 => rot3x
  | 1 => rot3y
  | 2 => rot3z

theorem rot3_eq_rot3_mat_toEuclideanLin :
    rot3 d θ = (rot3Mat d θ).toEuclideanLin := by
  fin_cases d <;> simp [rot3, rot3Mat]

@[simp]
theorem rot3_360 : rot3 d (2 * π) = 1 := by
  ext v i
  fin_cases d <;> fin_cases i <;>
    simp [rot3, Matrix.toLpLin_apply, Matrix.mulVec_eq_sum, Fin.sum_univ_three]

@[simp]
theorem rot3_neg360 : rot3 d (-(2 * π)) = 1 := by
  ext v i
  fin_cases d <;> fin_cases i <;>
    simp [rot3, Matrix.toLpLin_apply, Matrix.mulVec_eq_sum, Fin.sum_univ_three]

@[simp]
theorem rot3_k360 {k : ℤ} : rot3 d (k * (2 * π)) = 1 := by
  induction k with
  | zero => simp
  | succ n h =>
      simp only [Int.cast_add, Int.cast_one, one_mul, right_distrib,
        AddChar.map_add_eq_mul, h, rot3_360]
  | pred n h =>
      simp only [Int.cast_neg, neg_mul] at h
      simp only [sub_eq_add_neg, Int.cast_add, Int.cast_neg, Int.cast_one, neg_mul,
        one_mul, mul_one, right_distrib, AddChar.map_add_eq_mul, h, rot3_neg360]

/-- The unit vector in the positive `z` direction. -/
def zhat : ℝ³ :=
  !₂[0, 0, 1]

/-- The unit vector with spherical angles `θ` and `φ`. -/
@[simp]
def unit3 (θ φ : ℝ) : ℝ³ :=
  (rot3 2 θ ∘ rot3 1 (-φ)) zhat

/-- The matrix for projection to the `xy`-plane followed by a right angle rotation. -/
@[simp]
def projXYR90Mat : Matrix (Fin 2) (Fin 3) ℝ :=
  Matrix.of fun
    | 0, 0 => 0
    | 0, 1 => 1
    | 0, 2 => 0
    | 1, 0 => -1
    | 1, 1 => 0
    | 1, 2 => 0

/-- Projection to the `xy`-plane followed by a right angle rotation. -/
@[simp]
def projXYR90 : ℝ³ →L[ℝ] ℝ² :=
  projXYR90Mat.toEuclideanLin.toContinuousLinearMap

/-- The matrix of reflection across the `x`-axis in the plane. -/
@[simp]
def flipYMat : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun
    | 0, 0 => 1
    | 0, 1 => 0
    | 1, 0 => 0
    | 1, 1 => -1

/-- Reflection across the `x`-axis in the plane. -/
@[simp]
def flipY : ℝ² →L[ℝ] ℝ² :=
  flipYMat.toEuclideanLin.toContinuousLinearMap

/-- Projection after first orienting a three-dimensional body by angles `θ` and `φ`. -/
@[simp]
def projRot (θ φ : ℝ) : ℝ³ →L[ℝ] ℝ² :=
  projXYR90 ∘L rot3 1 φ ∘L rot3 2 (-θ)

theorem rot_proj_rot :
    rot2 α ∘L projRot θ φ =
      projXYR90 ∘L rot3 2 α ∘L rot3 1 φ ∘L rot3 2 (-θ) := by
  ext v i
  fin_cases i <;>
    simp [rot3, Matrix.toLpLin_apply, Matrix.mulVec_eq_sum, Fin.sum_univ_two,
      Fin.sum_univ_three] <;>
    ring

/-- A set is in convex position if no point lies in the convex hull of the others. -/
def convexPosition (𝕜 V : Type) [PartialOrder 𝕜] [Semiring 𝕜]
    [AddCommMonoid V] [Module 𝕜 V] (P : Set V) : Prop :=
  ∀ p ∈ P, p ∉ convexHull 𝕜 (P \ Set.singleton p)

/-- A projection-interior formulation of Rupert's property for a set in space. -/
def rupert' (P : Set ℝ³) : Prop :=
  ∃ α θ₁ φ₁ θ₂ φ₂ : ℝ,
    (rot2 α ∘L projRot θ₁ φ₁) '' P ⊆
      interior (convexHull ℝ (projRot θ₂ φ₂ '' P))

/-- The first generating point of the noperthedron seed. -/
def C₁ : ℝ³ :=
  !₂[152024884 / 259375205, 0, 210152163 / 259375205]

/-- The second generating point of the noperthedron seed. -/
def C₂ : ℝ³ :=
  !₂[6632738028e-10, 6106948881e-10, 3980949609e-10]

/-- The third generating point of the noperthedron seed. -/
def C₃ : ℝ³ :=
  !₂[8193990033e-10, 5298215096e-10, 1230614493e-10]

/-- The three generating points used to define the symmetric noperthedron set. -/
def noperthedronSeed : Finset ℝ³ :=
  {C₁, C₂, C₃}

@[simp]
theorem mem_noperthedron_seed (p : ℝ³) :
    p ∈ noperthedronSeed ↔ p = C₁ ∨ p = C₂ ∨ p = C₃ := by
  unfold noperthedronSeed
  grind only [= Finset.mem_insert, = Set.mem_singleton_iff, = Finset.insert_eq_of_mem,
    = Finset.mem_singleton, cases Or]

/-- The finite symmetric point configuration used in the noperthedron construction. -/
def noperthedron : Finset ℝ³ :=
  (({1, -1} : Finset ℤ) ×ˢ Finset.range 15 ×ˢ noperthedronSeed).image
    fun (s, (k, p)) => (s • rot3 2 (k * 15⁻¹ * (2 * π))) p

theorem mem_noperthedron' (p : ℝ³) :
    p ∈ noperthedron ↔
      ∃ (s : ℤ) (k : ℕ) (q : ℝ³),
        s ∈ ({1, -1} : Finset ℤ) ∧
          k < 15 ∧ q ∈ noperthedronSeed ∧
            p = (s • rot3 2 (k * 15⁻¹ * (2 * π))) q := by
  unfold noperthedron
  simp only [Int.reduceNeg, Finset.mem_image, Finset.mem_product, Finset.mem_insert,
    Finset.mem_singleton, Finset.mem_range, Prod.exists]
  constructor
  · rintro ⟨s, k, q, ⟨⟨s_in, k_in, q_in⟩, rfl⟩⟩
    exact ⟨s, k, q, s_in, k_in, q_in, rfl⟩
  · rintro ⟨s, k, q, s_in, k_in, q_in, rfl⟩
    exact ⟨s, k, q, ⟨⟨s_in, k_in, q_in⟩, rfl⟩⟩

@[simp]
theorem mem_noperthedron (p : ℝ³) :
    p ∈ noperthedron ↔
      ∃ (s : ℤ) (k : ℤ) (q : ℝ³),
        s ∈ ({1, -1} : Finset ℤ) ∧
          q ∈ noperthedronSeed ∧
            p = (s • rot3 2 (k * 15⁻¹ * (2 * π))) q := by
  rw [mem_noperthedron']
  constructor
  · rintro ⟨s, k, q, ⟨s_in, _k_in, q_in, rfl⟩⟩
    exact ⟨s, k, q, s_in, q_in, rfl⟩
  · rintro ⟨s, k, q, ⟨s_in, q_in, rfl⟩⟩
    let d := k / 15
    let k' := (k % 15).natAbs
    exists s, k', q
    suffices hrot :
        rot3 2 (k * (1 / 15) * (2 * π)) =
          rot3 2 (k' * (1 / 15) * (2 * π)) by
      have hk'_lt : k' < 15 := by
        have hnonneg : 0 ≤ k % 15 := Int.emod_nonneg k (by norm_num)
        have hlt : k % 15 < 15 := Int.emod_lt_of_pos k (by norm_num)
        omega
      refine ⟨s_in, hk'_lt, q_in, ?_⟩
      simpa [one_div] using congrArg (fun f => (s • f) q) hrot
    calc
      rot3 2 (k * (1 / 15) * (2 * π))
          = rot3 2 ((d * 15 + k % 15 : ℤ) * (1 / 15) * (2 * π)) := by
            rw [Int.ediv_mul_add_emod]
      _ = rot3 2 (((d * 15 : ℤ) + (k % 15 : ℤ)) * (1 / 15) * (2 * π)) := by
            simp
      _ = rot3 2 (d * (2 * π) + (k % 15 : ℤ) * (1 / 15) * (2 * π)) := by
            simp [right_distrib]
      _ = rot3 2 ((k % 15 : ℤ) * (1 / 15) * (2 * π)) := by
            simp only [AddChar.map_add_eq_mul, rot3_k360, one_mul]
      _ = rot3 2 (k' * (1 / 15) * (2 * π)) := by
            rw [(show (k % 15 : ℤ) = k' by grind)]
            norm_cast

theorem noperthedron_point_symmetric {p : ℝ³} :
    p ∈ noperthedron → -p ∈ noperthedron := by
  simp only [mem_noperthedron] at *
  rintro ⟨s, k, q, ⟨s_in, q_in, rfl⟩⟩
  exists -s, k, q
  simp only [Int.reduceNeg, Finset.mem_insert, Finset.mem_singleton] at s_in
  rcases s_in with rfl | rfl <;> simp [q_in]

theorem lemma7_1 :
    (projRot (θ + 2 / 15 * π) φ) '' noperthedron = projRot θ φ '' noperthedron := by
  ext p
  simp only [Set.mem_image, SetLike.mem_coe, mem_noperthedron, mem_noperthedron_seed,
    ↓existsAndEq, and_true, and_or_left, or_and_right, exists_or, projRot]
  have h (p : ℝ³) (s : ℤ) a b := calc
    (projXYR90 ∘L rot3 1 φ ∘L rot3 2 a) ((s • rot3 2 b) p) = _ := by
      rfl
    _ = (projXYR90 ∘L rot3 1 φ ∘L rot3 2 a ∘L (s • rot3 2 b)) p := by
      simp only [ContinuousLinearMap.comp_apply]
    _ = s • (projXYR90 ∘L rot3 1 φ ∘L rot3 2 a ∘L rot3 2 b) p := by
      simp only [ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_apply]
    _ = s • (projXYR90 ∘L rot3 1 φ ∘L (rot3 2 a ∘L rot3 2 b)) p := by
      simp
    _ = s • (projXYR90 ∘L rot3 1 φ ∘L rot3 2 (a + b)) p := by
      simp [AddChar.map_add_eq_mul]
    _ = (projXYR90 ∘L rot3 1 φ ∘L (s • rot3 2 (a + b))) p := by
      simp only [ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_apply]
  constructor <;> rintro (h | h | h) <;> rcases h with ⟨s, k, ⟨s_in, rfl⟩⟩
  · left
    use s, k - 1
    repeat rw [h]
    simp only [Int.cast_sub]
    ring_nf
    trivial
  · right
    left
    use s, k - 1
    repeat rw [h]
    simp only [Int.cast_sub]
    ring_nf
    trivial
  · right
    right
    use s, k - 1
    repeat rw [h]
    simp only [Int.cast_sub]
    ring_nf
    trivial
  · left
    use s, k + 1
    repeat rw [h]
    simp only [Int.cast_add]
    ring_nf
    trivial
  · right
    left
    use s, k + 1
    repeat rw [h]
    simp only [Int.cast_add]
    ring_nf
    trivial
  · right
    right
    use s, k + 1
    repeat rw [h]
    simp only [Int.cast_add]
    ring_nf
    trivial

theorem lemma7_2 :
    (rot2 (α + π) ∘L projRot θ φ) '' noperthedron =
      (rot2 α ∘L projRot θ φ) '' noperthedron := by
  ext p
  constructor <;> rintro ⟨q, q_in, rfl⟩ <;> use -q
  · constructor
    · exact noperthedron_point_symmetric q_in
    · simp only [AddChar.map_add_eq_mul, map_neg, rot2_180, ContinuousLinearMap.mul_def,
        ContinuousLinearMap.neg_comp, ContinuousLinearMap.comp_neg,
        ContinuousLinearMap.neg_apply, ContinuousLinearMap.one_def,
        ContinuousLinearMap.comp_id]
  · constructor
    · exact noperthedron_point_symmetric q_in
    · simp only [AddChar.map_add_eq_mul, map_neg, rot2_180, ContinuousLinearMap.mul_def,
        ContinuousLinearMap.neg_comp, ContinuousLinearMap.comp_neg,
        ContinuousLinearMap.neg_apply, ContinuousLinearMap.one_def,
        ContinuousLinearMap.comp_id, neg_neg]

theorem lemma7_3_1 :
    flipY ∘L projRot θ φ =
      (-projRot (θ + π * 15⁻¹) (π - φ)) ∘L rot3 2 (π * 16 * 15⁻¹) := by
  ext v i
  have h : π * 16 * 15⁻¹ = π * 15⁻¹ + π := by ring
  have hpyth : (sin (π * 15⁻¹)) ^ 2 + (cos (π * 15⁻¹)) ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  fin_cases i <;>
    simp only [flipY, flipYMat, projRot, projXYR90, projXYR90Mat, rot3, rot3y_apply,
      rot3yMat, rot3z_apply, rot3zMat, cos_neg, sin_neg, neg_neg, ContinuousLinearMap.coe_comp',
      LinearMap.coe_toContinuousLinearMap', Function.comp_apply, Matrix.toLpLin_apply,
      Matrix.mulVec_eq_sum, op_smul_eq_smul, Fin.sum_univ_three, Fin.isValue, WithLp.toLp_add,
      WithLp.toLp_smul, WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply,
      Matrix.transpose_apply, Matrix.of_apply, smul_eq_mul, right_distrib, mul_zero, neg_zero,
      mul_one, Fin.sum_univ_two, mul_neg, PiLp.add_apply, PiLp.smul_apply, cos_pi_sub,
      sin_pi_sub, neg_add_rev, cos_add, sin_add, h, cos_pi, sin_pi, sub_zero,
      ContinuousLinearMap.neg_comp, ContinuousLinearMap.neg_apply, PiLp.neg_apply,
      add_zero, neg_mul, zero_add]
  · linear_combination (sin θ * v.ofLp 0 - v.ofLp 1 * cos θ) * hpyth
  · linear_combination cos φ * (-(sin θ * v.ofLp 1) - cos θ * v.ofLp 0) * hpyth

theorem lemma7_3_2 :
    (-rot3 2 (π * 16 * 15⁻¹)) '' noperthedron = noperthedron := by
  ext p
  simp only [Set.mem_image, SetLike.mem_coe, mem_noperthedron]
  constructor
  · rintro ⟨q, ⟨s, k, r, s_in, r_in, rfl⟩, rfl⟩
    use -s, (8 + k), r
    have h := calc
      (-rot3 2 (π * 16 * 15⁻¹)) ((s • rot3 2 (↑k * 15⁻¹ * (2 * π))) r) = _ := by rfl
      _ = (-rot3 2 (π * 16 * 15⁻¹) ∘L (s • rot3 2 (↑k * 15⁻¹ * (2 * π)))) r := by rfl
      _ = (-s • (rot3 2 (16 * 15⁻¹ * π) ∘L rot3 2 (↑k * 15⁻¹ * (2 * π)))) r := by
            simp only [ContinuousLinearMap.comp_smul, ContinuousLinearMap.neg_apply,
              ContinuousLinearMap.smul_apply, neg_smul]
            ring_nf
      _ = (-s • rot3 2 (↑(8 + k) * 15⁻¹ * (2 * π))) r := by
            simp only [Int.cast_add, Distrib.right_distrib, AddChar.map_add_eq_mul,
              mul_eq_comp]
            ring_nf
    rw [h]
    simp only [Finset.mem_insert, Finset.mem_singleton] at s_in ⊢
    exact ⟨by omega, r_in, trivial⟩
  · rintro ⟨s, k, q, s_in, q_in, rfl⟩
    simp only [↓existsAndEq, and_true]
    use -s, (-8 + k), q
    have h := calc
      (-rot3 2 (π * 16 * 15⁻¹)) ((-s • rot3 2 (↑(-8 + k) * 15⁻¹ * (2 * π))) q) = _ := by rfl
      _ = (-rot3 2 (π * 16 * 15⁻¹)) ((-s • rot3 2 ((-8 + k) * 15⁻¹ * (2 * π))) q) := by
            simp [Int.cast_add]
      _ = ((-rot3 2 (π * 16 * 15⁻¹)) ∘L (-s • rot3 2 ((-8 + k) * 15⁻¹ * (2 * π)))) q := by rfl
      _ = (-s • ((-rot3 2 (π * 16 * 15⁻¹)) ∘L
            (rot3 2 ((-8 + k) * 15⁻¹ * (2 * π))))) q := by
              simp only [ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_apply]
      _ = (s • ((rot3 2 (π * 16 * 15⁻¹)) ∘L
            (rot3 2 ((-8 + k) * 15⁻¹ * (2 * π))))) q := by
              simp
      _ = (s • (((rot3 2 (π * 16 * 15⁻¹)) ∘L (rot3 2 (-8 * 15⁻¹ * (2 * π)))) ∘L
            rot3 2 (k * 15⁻¹ * (2 * π)))) q := by
              simp [Distrib.right_distrib, AddChar.map_add_eq_mul, mul_eq_comp]
      _ = (s • (((rot3 2 (π * 16 * 15⁻¹ + -8 * 15⁻¹ * (2 * π)))) ∘L
            rot3 2 (k * 15⁻¹ * (2 * π)))) q := by
              simp [AddChar.map_add_eq_mul]
      _ = (s • (((rot3 2 0 ∘L rot3 2 (k * 15⁻¹ * (2 * π)))))) q := by ring_nf
      _ = (s • rot3 2 (↑k * 15⁻¹ * (2 * π))) q := by simp
    rw [h]
    simp only [Finset.mem_insert, Finset.mem_singleton] at s_in ⊢
    exact ⟨⟨by omega, q_in⟩, trivial⟩

theorem lemma7_3 :
    (flipY ∘L projRot θ φ) '' noperthedron =
      projRot (θ + π * 15⁻¹) (π - φ) '' noperthedron := by
  simp only [lemma7_3_1]
  have h : (-projRot (θ + π * 15⁻¹) (π - φ)) ∘L (rot3 2 (π * 16 * 15⁻¹)) =
      (projRot (θ + π * 15⁻¹) (π - φ)) ∘L (-rot3 2 (π * 16 * 15⁻¹)) := by simp
  simp only [h, comp_image, lemma7_3_2]

theorem lemma9_rot2 : ‖rot2 α‖ = 1 := by
  apply ContinuousLinearMap.opNorm_eq_of_bounds
  · simp
  · intro x
    simp only [rot2, rot2Mat, AddChar.coe_mk, LinearMap.coe_toContinuousLinearMap',
      Matrix.toLpLin_apply, Matrix.mulVec_eq_sum, op_smul_eq_smul,
      Fin.sum_univ_two, Fin.isValue, WithLp.toLp_add, WithLp.toLp_smul, ENNReal.toReal_ofNat,
      Nat.ofNat_pos, PiLp.norm_eq_sum, PiLp.add_apply, PiLp.smul_apply,
      Matrix.transpose_apply, Matrix.of_apply, smul_eq_mul, norm_eq_abs, rpow_ofNat, sq_abs,
      mul_neg, one_div, one_mul]
    refine (rpow_le_rpow_iff ?_ ?_ ?_).mpr ?_
    · apply add_nonneg <;> apply sq_nonneg
    · apply add_nonneg <;> apply sq_nonneg
    · simp
    · simp only [Fin.isValue, add_sq, mul_neg, even_two, Even.neg_pow]; ring_nf
      calc
        x 0 ^ 2 * cos α ^ 2 + x 0 ^ 2 * sin α ^ 2 + cos α ^ 2 * x 1 ^ 2 +
            x 1 ^ 2 * sin α ^ 2 = _ := by rfl
        _ = (x 0 ^ 2 + x 1 ^ 2) * (sin α ^ 2 + cos α ^ 2) := by ring
        _ = (x 0 ^ 2 + x 1 ^ 2) := by simp [Real.sin_sq_add_cos_sq]
        _ ≤ _ := by rfl
  · intro N N_nonneg h
    specialize h !₂[1, 0]
    calc
      1 = ‖(rot2 α) !₂[1, 0]‖ := by simp [Matrix.mulVec_eq_sum, PiLp.norm_eq_sum]
      _ ≤ N * ‖!₂[(1 : ℝ), 0]‖ := by assumption
      _ = N := by simp [PiLp.norm_eq_sum]

theorem lemma9 : ‖rot3 d α‖ = 1 := by
  let d' := d
  let ix (i : Fin 3) : Fin 3 := i + d
  fin_cases d <;>
    · apply ContinuousLinearMap.opNorm_eq_of_bounds
      · simp
      · intro x
        simp only [rot3, rot3x, rot3y, rot3z, rot3xMat, rot3yMat, rot3zMat, AddChar.coe_mk,
          LinearMap.coe_toContinuousLinearMap', Matrix.toLpLin_apply, Matrix.mulVec_eq_sum,
          op_smul_eq_smul, Fin.sum_univ_three, Fin.isValue, WithLp.toLp_add,
          WithLp.toLp_smul, ENNReal.toReal_ofNat, Nat.ofNat_pos, PiLp.norm_eq_sum, PiLp.add_apply,
          PiLp.smul_apply, Matrix.transpose_apply, Matrix.of_apply, smul_eq_mul,
          norm_eq_abs, rpow_ofNat, sq_abs, mul_one, mul_zero, add_zero, zero_add, mul_neg, one_div,
          one_mul]
        refine (rpow_le_rpow_iff ?_ ?_ ?_).mpr ?_
        · positivity
        · positivity
        · simp
        · simp only [Fin.isValue, add_sq, mul_pow, mul_neg, even_two, Even.neg_pow]
          calc
            _ = x (ix 0) ^ 2 + x (ix 1) ^ 2 * cos α ^ 2 + x (ix 1) ^ 2 * sin α ^ 2 +
                cos α ^ 2 * x (ix 2) ^ 2 + x (ix 2) ^ 2 * sin α ^ 2 := by
                  simp only [Fin.zero_eta, Fin.isValue, Fin.reduceAdd, Fin.reduceFinMk, ix]
                  ring_nf
            _ = x (ix 0) ^ 2 + x (ix 1) ^ 2 * (sin α ^ 2 + cos α ^ 2) +
                x (ix 2) ^ 2 * (sin α ^ 2 + cos α ^ 2) := by
                  simp only [Distrib.left_distrib]; ring
            _ = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
                  rw [sin_sq_add_cos_sq]
                  simp only [Fin.zero_eta, Fin.isValue, Fin.reduceAdd, Fin.reduceFinMk, ix]
                  ring_nf
            _ ≤ _ := by rfl
      · intro N N_nonneg h
        specialize h !₂[1, 0, 0]
        calc
          1 = ‖(rot3 d' α) !₂[1, 0, 0]‖ := by
                simp [d', rot3, rot3x, rot3y, rot3z, Matrix.mulVec_eq_sum, Fin.sum_univ_three,
                  PiLp.norm_eq_sum]
          _ ≤ N * ‖!₂[(1 : ℝ), 0, 0]‖ := by assumption
          _ = N := by simp [PiLp.norm_eq_sum, Fin.sum_univ_three]

theorem norm_proj_xy_r90_eq_one : ‖projXYR90‖ = 1 := by
  apply ContinuousLinearMap.opNorm_eq_of_bounds
  · simp
  · intro x
    simp only [projXYR90, projXYR90Mat, LinearMap.coe_toContinuousLinearMap',
      Matrix.toLpLin_apply, Matrix.mulVec_eq_sum, op_smul_eq_smul,
      Fin.sum_univ_three, Fin.isValue, WithLp.toLp_add, WithLp.toLp_smul, ENNReal.toReal_ofNat,
      Nat.ofNat_pos, PiLp.norm_eq_sum, PiLp.add_apply, PiLp.smul_apply,
      Matrix.transpose_apply, Matrix.of_apply, smul_eq_mul, norm_eq_abs, rpow_ofNat, sq_abs,
      Fin.sum_univ_two, mul_zero, mul_one, zero_add, add_zero, mul_neg, even_two, Even.neg_pow,
      one_div, one_mul]
    refine (rpow_le_rpow_iff ?_ ?_ ?_).mpr ?_
    · positivity
    · positivity
    · simp
    · ring_nf; simp only [Fin.isValue, le_add_iff_nonneg_right, sq_nonneg]
  · intro N N_nonneg h
    specialize h !₂[1, 0, 0]
    calc
      1 = ‖projXYR90 !₂[1, 0, 0]‖ := by
            simp [Matrix.mulVec_eq_sum, Fin.sum_univ_three, PiLp.norm_eq_sum]
      _ ≤ N * ‖!₂[(1 : ℝ), 0, 0]‖ := by assumption
      _ = N := by simp [Fin.sum_univ_three, PiLp.norm_eq_sum]

theorem lemma9_proj_rot : ‖projRot θ φ‖ = 1 := by
  apply ContinuousLinearMap.opNorm_eq_of_bounds
  · simp
  · intro x
    simp only [projRot]
    calc
      ‖(projXYR90 ∘L rot3 1 φ ∘L rot3 2 (-θ)) x‖ = _ := by rfl
      _ ≤ ‖projXYR90 ∘L rot3 1 φ ∘L rot3 2 (-θ)‖ * ‖x‖ := by
            apply ContinuousLinearMap.le_opNorm
      _ ≤ (‖projXYR90‖ * ‖rot3 1 φ‖ * ‖rot3 2 (-θ)‖) * ‖x‖ := by
            apply mul_le_mul_of_nonneg_right
            · calc
                ‖projXYR90 ∘L rot3 1 φ ∘L rot3 2 (-θ)‖ = _ := by rfl
                _ ≤ ‖projXYR90‖ * ‖rot3 1 φ ∘L rot3 2 (-θ)‖ := by
                      apply ContinuousLinearMap.opNorm_comp_le
                _ ≤ ‖projXYR90‖ * ‖rot3 1 φ‖ * ‖rot3 2 (-θ)‖ := by
                      rw [mul_assoc]
                      apply mul_le_mul_of_nonneg_left
                      · apply ContinuousLinearMap.opNorm_comp_le
                      · apply norm_nonneg
            · apply norm_nonneg
      _ = 1 * ‖x‖ := by simp only [norm_proj_xy_r90_eq_one, lemma9, mul_one, one_mul]
  · intro N N_nonneg h
    specialize h !₂[-sin θ, cos θ, 0]
    calc
      1 = ((sin θ ^ 2 + cos θ ^ 2) ^ 2) ^ (2 : ℝ)⁻¹ := by simp [Real.sin_sq_add_cos_sq]
      _ = ‖(projRot θ φ) !₂[-sin θ, cos θ, 0]‖ := by
            simp only [rot3, projRot, projXYR90, projXYR90Mat, rot3y_apply, rot3yMat,
              rot3z_apply, rot3zMat, cos_neg, sin_neg, neg_neg, ContinuousLinearMap.coe_comp',
              LinearMap.coe_toContinuousLinearMap', Function.comp_apply, Matrix.toLpLin_toLp,
              Matrix.toLin'_apply, Matrix.mulVec_eq_sum, op_smul_eq_smul, Fin.sum_univ_three,
              Fin.isValue, Matrix.cons_val_zero, neg_smul, Matrix.cons_val_one, Matrix.cons_val,
              zero_smul, add_zero, WithLp.toLp_add, WithLp.toLp_neg, WithLp.toLp_smul, map_add,
              map_neg, map_smul, Matrix.transpose_apply, Matrix.of_apply, smul_add, smul_neg,
              neg_add_rev, one_smul, zero_add, ENNReal.toReal_ofNat, Nat.ofNat_pos,
              PiLp.norm_eq_sum, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.neg_apply,
              norm_eq_abs, rpow_ofNat, sq_abs, Fin.sum_univ_two, mul_one, mul_zero, neg_zero,
              mul_neg, one_div]
            ring_nf
      _ ≤ N * ‖!₂[-sin θ, cos θ, 0]‖ := by assumption
      _ = N := by simp [Fin.sum_univ_three, PiLp.norm_eq_sum]

theorem dist_rot2_apply :
    ‖(rot2 α - rot2 α') v‖ = 2 * |sin ((α - α') / 2)| * ‖v‖ := by
  simp only [rot2, rot2Mat, AddChar.coe_mk, ContinuousLinearMap.coe_sub',
    LinearMap.coe_toContinuousLinearMap', Pi.sub_apply, Matrix.toLpLin_apply,
    Matrix.mulVec_eq_sum, op_smul_eq_smul, Fin.sum_univ_two, Fin.isValue,
    WithLp.toLp_add, WithLp.toLp_smul, ENNReal.toReal_ofNat, Nat.ofNat_pos, PiLp.norm_eq_sum,
    PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, Matrix.transpose_apply,
    Matrix.of_apply, smul_eq_mul, norm_eq_abs, rpow_ofNat, sq_abs, mul_neg, one_div]
  calc
    ((v 0 * cos α + -(v 1 * sin α) - (v 0 * cos α' + -(v 1 * sin α'))) ^ 2 +
        (v 0 * sin α + v 1 * cos α - (v 0 * sin α' + v 1 * cos α')) ^ 2) ^ (2 : ℝ)⁻¹ = _ := by
          rfl
    _ = ((2 * sin ((α - α') / 2)) ^ 2 * (v 0 ^ 2 + v 1 ^ 2)) ^ (2 : ℝ)⁻¹ := by
          have one_neg_cos_nonneg : 0 ≤ 1 - cos (α - α') := by simp [cos_le_one]
          refine (rpow_left_inj ?_ ?_ ?_).mpr ?_ <;> try positivity
          calc
            (v 0 * cos α + -(v 1 * sin α) - (v 0 * cos α' + -(v 1 * sin α'))) ^ 2 +
                (v 0 * sin α + v 1 * cos α - (v 0 * sin α' + v 1 * cos α')) ^ 2 = _ := by rfl
            _ = (v 0 * (cos α - cos α') - v 1 * (sin α - sin α')) ^ 2 +
                (v 0 * (sin α - sin α') + v 1 * (cos α - cos α')) ^ 2 := by ring_nf
            _ = 4 * (v 0 ^ 2 + v 1 ^ 2) * (sin ((α - α') / 2)) ^ 2 *
                ((sin ((α + α') / 2)) ^ 2 + (cos ((α + α') / 2)) ^ 2) := by
                  simp only [Fin.isValue, cos_sub_cos, neg_mul, mul_neg, sin_sub_sin, sq]
                  ring_nf
            _ = 4 * (v 0 ^ 2 + v 1 ^ 2) * (sin ((α - α') / 2)) ^ 2 := by
                  simp [sin_sq_add_cos_sq]
            _ = (2 * sin ((α - α') / 2)) ^ 2 * (v 0 ^ 2 + v 1 ^ 2) := by ring
    _ = 2 * |sin ((α - α') / 2)| * (v 0 ^ 2 + v 1 ^ 2) ^ (2 : ℝ)⁻¹ := by
          rw [mul_rpow, inv_eq_one_div, rpow_div_two_eq_sqrt]
          · simp only [Fin.isValue, sqrt_sq_eq_abs, abs_mul, Nat.abs_ofNat, rpow_one, one_div]
          all_goals positivity

theorem dist_rot3_apply :
    ‖(rot3 d α - rot3 d α') v‖ =
      2 * |sin ((α - α') / 2)| * ‖(WithLp.toLp 2 (Fin.removeNth d v) : ℝ²)‖ := by
  let ix (i : Fin 3) : Fin 3 := match d, i with
    | 0, 0 => 0
    | 0, 1 => 1
    | 0, 2 => 2
    | 1, 0 => 1
    | 1, 1 => 0
    | 1, 2 => 2
    | 2, 0 => 2
    | 2, 1 => 0
    | 2, 2 => 1
  fin_cases d <;>
    · simp only [rot3, rot3x, rot3y, rot3z, rot3xMat, rot3yMat, rot3zMat, AddChar.coe_mk,
        ContinuousLinearMap.coe_sub', LinearMap.coe_toContinuousLinearMap', Pi.sub_apply,
        Matrix.toLpLin_apply, Matrix.mulVec_eq_sum, op_smul_eq_smul,
        Fin.sum_univ_three, Fin.isValue, WithLp.toLp_add, WithLp.toLp_smul, ENNReal.toReal_ofNat,
        Nat.ofNat_pos, PiLp.norm_eq_sum, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
        Matrix.transpose_apply, Matrix.of_apply, smul_eq_mul, norm_eq_abs,
        rpow_ofNat, sq_abs, mul_one, mul_zero, add_zero, sub_self, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, zero_add, mul_neg, one_div, Fin.sum_univ_two]
      calc
        _ = ((v (ix 1) * cos α + -(v (ix 2) * sin α) -
            (v (ix 1) * cos α' + -(v (ix 2) * sin α'))) ^ 2 +
              (v (ix 1) * sin α + v (ix 2) * cos α -
                (v (ix 1) * sin α' + v (ix 2) * cos α')) ^ 2) ^ (2 : ℝ)⁻¹ := by simp only [ix]
        _ = ((2 * sin ((α - α') / 2)) ^ 2 * (v (ix 1) ^ 2 + v (ix 2) ^ 2)) ^ (2 : ℝ)⁻¹ := by
              have one_neg_cos_nonneg : 0 ≤ 1 - cos (α - α') := by simp [cos_le_one]
              refine (rpow_left_inj ?_ ?_ ?_).mpr ?_ <;> try positivity
              calc
                _ = (v (ix 1) * cos α + -(v (ix 2) * sin α) -
                    (v (ix 1) * cos α' + -(v (ix 2) * sin α'))) ^ 2 +
                      (v (ix 1) * sin α + v (ix 2) * cos α -
                        (v (ix 1) * sin α' + v (ix 2) * cos α')) ^ 2 := by simp [ix]
                _ = (v (ix 1) * (cos α - cos α') - v (ix 2) * (sin α - sin α')) ^ 2 +
                    (v (ix 1) * (sin α - sin α') + v (ix 2) * (cos α - cos α')) ^ 2 := by ring_nf
                _ = 4 * (v (ix 1) ^ 2 + v (ix 2) ^ 2) * (sin ((α - α') / 2)) ^ 2 *
                    ((sin ((α + α') / 2)) ^ 2 + (cos ((α + α') / 2)) ^ 2) := by
                      simp [sin_sub_sin, cos_sub_cos, sq]
                      ring_nf
                _ = 4 * (v (ix 1) ^ 2 + v (ix 2) ^ 2) * (sin ((α - α') / 2)) ^ 2 := by
                      simp [sin_sq_add_cos_sq]
                _ = (2 * sin ((α - α') / 2)) ^ 2 * (v (ix 1) ^ 2 + v (ix 2) ^ 2) := by ring
        _ = 2 * |sin ((α - α') / 2)| * (v (ix 1) ^ 2 + v (ix 2) ^ 2) ^ (2 : ℝ)⁻¹ := by
              rw [mul_rpow, inv_eq_one_div, rpow_div_two_eq_sqrt]
              · simp [sqrt_sq_eq_abs]
              all_goals positivity

theorem dist_rot2 :
    ‖rot2 α - rot2 α'‖ = 2 * |sin ((α - α') / 2)| := by
  apply ContinuousLinearMap.opNorm_eq_of_bounds
  · positivity
  · intro v
    rw [dist_rot2_apply]
  · intro N N_nonneg h
    specialize h !₂[1, 0]
    have norm_xhat_eq_one : ‖!₂[(1 : ℝ), 0]‖ = 1 := by simp [PiLp.norm_eq_sum, Fin.sum_univ_two]
    calc
      2 * |sin ((α - α') / 2)| = _ := by rfl
      _ = ‖(rot2 α - rot2 α') !₂[(1 : ℝ), 0]‖ := by
            simp only [dist_rot2_apply, norm_xhat_eq_one, mul_one]
      _ ≤ N * ‖!₂[(1 : ℝ), 0]‖ := by assumption
      _ = N := by simp [norm_xhat_eq_one]

theorem dist_rot3 :
    ‖rot3 d α - rot3 d α'‖ = 2 * |sin ((α - α') / 2)| := by
  apply ContinuousLinearMap.opNorm_eq_of_bounds
  · positivity
  · intro v
    rw [dist_rot3_apply]
    by_cases h : |sin ((α - α') / 2)| = 0
    · rw [h]; simp
    · field_simp
      suffices hsuff : (d.removeNth v.ofLp 0 ^ 2 + d.removeNth v.ofLp 1 ^ 2) ^ (2 : ℝ)⁻¹ ≤
          (v.ofLp 0 ^ 2 + v.ofLp 1 ^ 2 + v.ofLp 2 ^ 2) ^ (2 : ℝ)⁻¹ by
        simpa [PiLp.norm_eq_sum, Fin.sum_univ_three] using hsuff
      apply rpow_le_rpow
      · positivity
      · fin_cases d <;>
          · simp only [Fin.removeNth_apply, Fin.succAbove, Fin.isValue]
            norm_num [Fin.lt_def]
            nlinarith [sq_nonneg (v.ofLp 0), sq_nonneg (v.ofLp 1), sq_nonneg (v.ofLp 2)]
      · positivity
  · intro N N_nonneg h
    let d' := d
    let v : ℝ³ := if d = 0 then !₂[0, 1, 0] else !₂[1, 0, 0]
    have norm_v_one : ‖v‖ = 1 := by
      unfold v
      split <;> simp [PiLp.norm_eq_sum, Fin.sum_univ_three]
    fin_cases d <;>
      · specialize h v
        calc
          2 * |sin ((α - α') / 2)| = _ := by rfl
          _ = ‖(rot3 d' α - rot3 d' α') v‖ := by
                rw [dist_rot3_apply]
                simp [v, d', PiLp.norm_eq_sum, Fin.removeNth_apply, Fin.succAbove]
          _ ≤ N * ‖v‖ := by assumption
          _ = N := by simp [norm_v_one]

theorem dist_rot3_eq_dist_rot :
    ‖rot3 d α - rot3 d α'‖ = ‖rot2 α - rot2 α'‖ := by simp only [dist_rot3, dist_rot2]

theorem two_mul_abs_sin_half_le : 2 * |sin (α / 2)| ≤ |α| := by
  have h : |sin (α / 2)| ≤ |α / 2| := abs_sin_le_abs
  calc
    2 * |sin (α / 2)| = _ := by rfl
    _ ≤ 2 * |α / 2| := by simp [h]
    _ = 2 * (|α| / 2) := by simp [abs_div]
    _ = |α| := by field_simp

theorem dist_rot2_le_dist : ‖rot2 α - rot2 α'‖ ≤ ‖α - α'‖ := by
  calc
    ‖rot2 α - rot2 α'‖ = _ := by rfl
    _ = 2 * |sin ((α - α') / 2)| := by apply dist_rot2
    _ ≤ |α - α'| := by apply two_mul_abs_sin_half_le

theorem one_add_cos_eq : 1 + cos α = 2 * cos (α / 2) ^ 2 := by rw [cos_sq]; field_simp

theorem lemma11_1_1 :
    cos (√(α ^ 2 + β ^ 2) / 2) ^ 2 = cos (√((-α) ^ 2 + β ^ 2) / 2) ^ 2 := by simp

theorem lemma11_1_2 :
    cos (√(α ^ 2 + β ^ 2) / 2) ^ 2 = cos (√(α ^ 2 + (-β) ^ 2) / 2) ^ 2 := by simp

theorem lemma11_1_3 :
    cos (α / 2) ^ 2 * cos (β / 2) ^ 2 = cos ((-α) / 2) ^ 2 * cos (β / 2) ^ 2 := by
  simp only [neg_div, cos_neg]

theorem lemma11_1_4 :
    cos (α / 2) ^ 2 * cos (β / 2) ^ 2 = cos (α / 2) ^ 2 * cos ((-β) / 2) ^ 2 := by
  simp only [neg_div, cos_neg]

/-- The auxiliary function `sin x - x * cos x`, used in convexity estimates. -/
def sinSubMulCos (x : ℝ) : ℝ := sin x - x * cos x

theorem sin_sub_mul_cos_monotone_on : MonotoneOn sinSubMulCos (Set.Icc 0 π) := by
  apply monotoneOn_of_deriv_nonneg
  · apply convex_Icc
  · apply Continuous.continuousOn
    unfold sinSubMulCos
    continuity
  · unfold sinSubMulCos
    simp only [interior_Icc]
    apply DifferentiableOn.sub
    · apply Differentiable.differentiableOn
      simp
    · apply DifferentiableOn.mul
      · apply Differentiable.differentiableOn
        simp
      · apply Differentiable.differentiableOn
        simp
  · simp only [interior_Icc]
    intro x x_in
    unfold sinSubMulCos
    simp only [differentiableAt_sin, differentiableAt_fun_id, differentiableAt_cos,
      DifferentiableAt.fun_mul, deriv_fun_sub, Real.deriv_sin, deriv_fun_mul, deriv_id'', one_mul,
      deriv_cos', mul_neg, sub_add_cancel_left, neg_neg]
    have := sin_pos_of_mem_Ioo x_in
    simp only [Set.mem_Ioo] at x_in
    rcases x_in with ⟨x_pos, x_lt⟩
    apply mul_nonneg <;> linarith

theorem sin_sub_mul_cos_nonneg : x ∈ Set.Icc 0 π → 0 ≤ sinSubMulCos x := by
  simp only [Set.mem_Icc, and_imp]
  intro x_nonneg x_le
  calc
    0 = sinSubMulCos 0 := by simp [sinSubMulCos]
    _ ≤ sinSubMulCos x := by
          apply sin_sub_mul_cos_monotone_on <;>
            (try simp only [Set.mem_Icc, le_refl, true_and]) <;> grind

theorem convexOn_cos_sqrt : ConvexOn ℝ (Set.Icc 0 (π ^ 2)) (cos ∘ sqrt) := by
  have cos_sqrt_deriv : ∀ x ∈ Set.Ioo 0 (π ^ 2),
      deriv (cos ∘ sqrt) x = -sin √x / (2 * √x) := by
    simp only [Set.mem_Ioo, and_imp]
    intro x x_pos x_lt
    rw [deriv_comp, deriv_cos', deriv_sqrt, deriv_id'']
    · field_simp
    · simp
    · linarith
    · simp
    · apply DifferentiableAt.sqrt
      · simp
      · linarith
  apply convexOn_of_deriv2_nonneg
  · apply convex_Icc
  · refine ContinuousOn.comp (t := Set.univ) ?_ ?_ ?_
    · continuity
    · apply Continuous.continuousOn
      continuity
    · apply Set.mapsTo_iff_subset_preimage.mpr
      simp
  · refine DifferentiableOn.comp (t := Set.univ) ?_ ?_ ?_
    · apply Differentiable.differentiableOn
      simp
    · simp only [interior_Icc]
      apply DifferentiableOn.sqrt
      · apply Differentiable.differentiableOn
        simp
      · grind
    · apply Set.mapsTo_iff_subset_preimage.mpr
      simp
  · simp only [interior_Icc]
    apply DifferentiableOn.congr (f := (-((sin ·) / (2 * ·)) ∘ sqrt))
    · simp only [differentiableOn_neg_iff]
      apply DifferentiableOn.comp (t := Set.Ioi 0)
      · apply DifferentiableOn.div
        · apply Differentiable.differentiableOn
          simp
        · apply Differentiable.differentiableOn
          apply Differentiable.mul
          · simp
          · simp
        · grind
      · apply DifferentiableOn.sqrt
        · apply Differentiable.differentiableOn
          simp
        · grind
      · apply Set.mapsTo_iff_subset_preimage.mpr
        simp only [Set.subset_def, Set.mem_Ioo, Set.mem_preimage, Set.mem_Ioi, sqrt_pos, and_imp]
        grind
    · intro x x_in
      simp only [Pi.neg_apply, Function.comp_apply, Pi.div_apply]
      grind
  · simp only [interior_Icc, Set.mem_Ioo, Function.iterate_succ, Function.iterate_zero,
      Function.id_def, Function.comp_apply, and_imp]
    intro x x_pos x_lt
    rw [(Set.EqOn.deriv
      (_ : Set.EqOn (deriv (cos ∘ sqrt)) (fun y => -sin √y / (2 * √y)) (Set.Ioo 0 (π ^ 2)))
      (by simp [Ioo_eq_ball] : IsOpen (Set.Ioo 0 (π ^ 2))))]
    · rw [deriv_fun_div]
      · simp only [deriv.fun_neg', neg_mul, deriv_const_mul_field', sub_neg_eq_add]
        conv in (fun y => sin √y) =>
          change (sin ∘ sqrt)
        rw [deriv_comp, deriv_sqrt, _root_.deriv_sin, deriv_id'']
        · simp only [mul_one, one_div, mul_inv_rev]
          field_simp; ring_nf
          rw [add_comm]
          apply sin_sub_mul_cos_nonneg
          simp only [Set.mem_Icc, sqrt_nonneg, sqrt_le_iff, true_and]
          refine ⟨pi_nonneg, ?_⟩
          linarith
        · simp
        · simp
        · linarith
        · simp
        · apply DifferentiableAt.sqrt
          · simp
          · linarith
      · simp only [differentiableAt_fun_neg_iff]
        apply DifferentiableAt.fun_comp'
        · simp
        · apply DifferentiableAt.sqrt
          · simp
          · linarith
      · apply DifferentiableAt.const_mul
        apply DifferentiableAt.sqrt
        · simp
        · linarith
      · have : 0 < √x := sqrt_pos.mpr x_pos
        linarith
    · grind
    · intro x; apply cos_sqrt_deriv

theorem lemma11_1 :
    |α| ≤ 2 → |β| ≤ 2 → 2 * (1 + cos √(α ^ 2 + β ^ 2)) ≤ (1 + cos α) * (1 + cos β) := by
  repeat rw [one_add_cos_eq]
  field_simp
  suffices ∀ α β, 0 ≤ α → α ≤ 2 → 0 ≤ β → β ≤ 2 →
      cos (√(α ^ 2 + β ^ 2) / 2) ^ 2 ≤ cos (α / 2) ^ 2 * cos (β / 2) ^ 2 by
    simp only [abs_le, and_imp]
    intro le_α α_le le_β β_le
    by_cases α_sign : 0 ≤ α <;> by_cases β_sign : 0 ≤ β
    · apply this <;> linarith
    · rw [lemma11_1_2, lemma11_1_4]
      apply this <;> linarith
    · rw [lemma11_1_1, lemma11_1_3]
      apply this <;> linarith
    · rw [lemma11_1_1, lemma11_1_2, lemma11_1_3, lemma11_1_4]
      apply this <;> linarith
  intro α β α_nonneg α_le β_nonneg β_le
  rw [(calc
      √(α ^ 2 + β ^ 2) / 2 = _ := by rfl
      _ = √((α / 2) ^ 2 + (β / 2) ^ 2) := by field_simp; simp; field_simp)]
  generalize hα : α / 2 = x, hβ : β / 2 = y
  rw [(calc cos x ^ 2 * cos y ^ 2 = (cos x * cos y) ^ 2 := by simp [sq]; ring)]
  apply sq_le_sq.mpr
  repeat rw [abs_of_nonneg]
  · suffices 2 * cos √(x ^ 2 + y ^ 2) ≤ 2 * cos x * cos y by field_simp at this; assumption
    rw [two_mul_cos_mul_cos]
    let f := cos ∘ sqrt
    calc
      2 * cos √(x ^ 2 + y ^ 2) = _ := by rfl
      _ = 2 * f (x ^ 2 + y ^ 2) := by rfl
      _ = 2 * f (1 / 2 * (x - y) ^ 2 + 1 / 2 * (x + y) ^ 2) := by ring_nf
      _ ≤ 2 * (1 / 2 * f ((x - y) ^ 2) + 1 / 2 * f ((x + y) ^ 2)) := by
            subst hα hβ
            simp only [mul_le_mul_iff_right₀, Nat.ofNat_pos]
            apply convexOn_cos_sqrt.2
            · simp only [Set.mem_Icc]
              refine ⟨by positivity, ?_⟩
              apply sq_le_sq.mpr
              field_simp
              simp only [abs_div, Nat.abs_ofNat]
              field_simp
              apply le_of_lt
              calc
                |α - β| = _ := by rfl
                _ ≤ |α| + |β| := by apply abs_sub
                _ ≤ 2 * 3 := by (repeat rw [abs_of_nonneg]) <;> linarith
                _ < 2 * π := by simp [pi_gt_three]
                _ = 2 * |π| := by rw [abs_of_nonneg]; positivity
            · simp only [Set.mem_Icc]
              refine ⟨by positivity, ?_⟩
              apply sq_le_sq.mpr
              repeat rw [abs_of_nonneg]
              · field_simp
                apply le_of_lt
                calc
                  α + β = _ := by rfl
                  _ ≤ 2 * 3 := by linarith
                  _ < 2 * π := by simp [pi_gt_three]
              · positivity
              · positivity
            · positivity
            · positivity
            · ring
      _ = f ((x - y) ^ 2) + f ((x + y) ^ 2) := by field_simp
      _ = cos √((x - y) ^ 2) + cos √((x + y) ^ 2) := by simp [f]
      _ = cos |x - y| + cos |x + y| := by simp [sqrt_sq_eq_abs]
      _ = cos (x - y) + cos (x + y) := by simp
  · subst hα hβ
    have : 3 < π := pi_gt_three
    apply mul_nonneg <;>
      · apply cos_nonneg_of_mem_Icc
        constructor
        · linarith
        · linarith
  · have : 3 < π := pi_gt_three
    apply cos_nonneg_of_mem_Icc
    constructor
    · calc
        -(π / 2) ≤ 0 := by linarith
        _ = √0 := by simp
        _ ≤ √(x ^ 2 + y ^ 2) := by
              apply sqrt_monotone
              positivity
    · subst hα hβ
      field_simp
      rw [sqrt_div, sqrt_sq]
      · field_simp
        apply le_of_lt
        calc
          √(α ^ 2 + β ^ 2) ≤ √(2 ^ 2 + 2 ^ 2) := by
                apply sqrt_monotone
                apply add_le_add <;> apply sq_le_sq.mpr <;>
                  simpa [abs_of_nonneg, α_nonneg, β_nonneg]
          _ = √8 := by ring_nf
          _ ≤ 3 := by simp only [sqrt_le_iff, Nat.ofNat_nonneg, true_and]; linarith
          _ < π := by assumption
      · linarith
      · positivity

/-- The trace of an endomorphism of `ℝ³`. -/
abbrev tr := LinearMap.trace ℝ ℝ³

/-- The trace of an endomorphism of `Fin 3 → ℝ`. -/
abbrev tr' := LinearMap.trace ℝ (Fin 3 → ℝ)

theorem tr_rot3_rot3 :
    d ≠ d' → tr (rot3 d α ∘L rot3 d' β) = cos α + cos β + cos α * cos β := by
  intro d_ne_d'
  calc tr (rot3 d α ∘L rot3 d' β)
    _ = tr ((rot3Mat d α).toEuclideanLin.toContinuousLinearMap ∘L
        (rot3Mat d' β).toEuclideanLin.toContinuousLinearMap) := by
          simp [rot3_eq_rot3_mat_toEuclideanLin]
    _ = tr ((rot3Mat d α * rot3Mat d' β).toEuclideanLin) := by
          simp [Matrix.toLpLin_eq_toLin, Matrix.toLin_mul (v₁ := ?a) (v₂ := ?a) (v₃ := ?a)]
    _ = Matrix.trace (rot3Mat d α * rot3Mat d' β) := by
          simp only [Matrix.toLpLin_eq_toLin, Matrix.trace_toLin_eq]
    _ = cos α + cos β + cos α * cos β := by
          fin_cases d <;> fin_cases d' <;>
            · try contradiction
              try simp only [rot3Mat, rot3xMat, rot3yMat, rot3zMat, Matrix.trace,
                Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_three]
              try ring_nf

theorem tr_rot3z : tr (rot3z α) = 1 + 2 * cos α := by
  have h : (rot3z α : ℝ³ →L[ℝ] ℝ³) = (rot3zMat α).toEuclideanLin.toContinuousLinearMap := rfl
  calc tr (rot3z α)
    _ = LinearMap.trace ℝ ℝ³ ((rot3zMat α).toEuclideanLin) := by rw [h]; rfl
    _ = Matrix.trace (rot3zMat α) := by
          simp only [Matrix.toLpLin_eq_toLin, Matrix.trace_toLin_eq]
    _ = 1 + 2 * cos α := by
          simp [Matrix.trace, rot3zMat, Fin.sum_univ_three]
          ring_nf

theorem lemma12_2 :
    d ≠ d' →
      ‖rot3 d (2 * α) ∘L rot3 d' (2 * β) - 1‖ ≤ 2 * ‖rot3 d α ∘L rot3 d' β - 1‖ := by
  intro d_ne_d'
  calc
    _ = ‖(rot3 d (2 * α) ∘L rot3 d' (2 * β) - rot3 d α ∘L rot3 d' β) +
        (rot3 d α ∘L rot3 d' β - 1)‖ := by simp
    _ ≤ ‖rot3 d (2 * α) ∘L rot3 d' (2 * β) - rot3 d α ∘L rot3 d' β‖ +
        ‖rot3 d α ∘L rot3 d' β - 1‖ := by apply norm_add_le
    _ = ‖(rot3 d α ∘L rot3 d α) ∘L (rot3 d' β ∘L rot3 d' β) - rot3 d α ∘L rot3 d' β‖ +
        ‖rot3 d α ∘L rot3 d' β - 1‖ := by
          fin_cases d <;> fin_cases d' <;>
            · try contradiction
              try simp only [rot3]
              try repeat rw [two_mul, AddChar.map_add_eq_mul, mul_eq_comp]
              try rfl
    _ ≤ ‖rot3 d α ∘L rot3 d' β - 1‖ + ‖rot3 d α ∘L rot3 d' β - 1‖ := by
          gcongr 1
          calc
            _ = ‖rot3 d α ∘L (rot3 d α ∘L rot3 d' β) ∘L rot3 d' β -
                rot3 d α ∘L rot3 d' β‖ := by congr 1
            _ = ‖rot3 d α ∘L (rot3 d α ∘L rot3 d' β) ∘L rot3 d' β -
                rot3 d α ∘L 1 ∘L rot3 d' β‖ := by congr 1
            _ = ‖rot3 d α ∘L (rot3 d α ∘L rot3 d' β - 1) ∘L rot3 d' β‖ := by simp
            _ ≤ ‖(rot3 d α ∘L rot3 d' β - 1)‖ := by
                  repeat grw [ContinuousLinearMap.opNorm_comp_le]
                  repeat rw [lemma9]
                  simp
    _ = 2 * ‖rot3 d α ∘L rot3 d' β - 1‖ := by ring

end LeanPool.Noperthedron
