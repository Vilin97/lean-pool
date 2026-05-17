/-
Copyright (c) 2026 Reuben Steenekamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reuben Steenekamp
-/

import Init.Data.Int.DivMod.Basic
import Mathlib.Algebra.Group.AddChar
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

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

/-- The matrix of the counterclockwise rotation of the plane by angle `α`. -/
@[simp]
def rot2_mat (α : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun
    | 0, 0 => Real.cos α
    | 0, 1 => -Real.sin α
    | 1, 0 => Real.sin α
    | 1, 1 => Real.cos α

/-- The additive character sending an angle to the corresponding planar rotation. -/
@[simp]
def rot2 : AddChar ℝ (ℝ² →L[ℝ] ℝ²) where
  toFun α := (rot2_mat α).toEuclideanLin.toContinuousLinearMap
  map_zero_eq_one' := by
    ext v i
    fin_cases i <;> simp [Matrix.toLpLin_apply, Matrix.mulVec]
  map_add_eq_mul' := by
    intro α β
    ext v i
    fin_cases i <;>
      simp [Matrix.toLpLin_apply, Matrix.mulVec_eq_sum, rot2_mat, cos_add, sin_add] <;>
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
def rot3x_mat (α : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
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
  toFun α := (rot3x_mat α).toEuclideanLin.toContinuousLinearMap
  map_zero_eq_one' := by
    ext v i
    fin_cases i <;>
      simp [Matrix.toLpLin_apply, Matrix.mulVec_eq_sum, Fin.sum_univ_three]
  map_add_eq_mul' α β := by
    ext v i
    fin_cases i <;>
      simp [rot3x_mat, cos_add, sin_add, ContinuousLinearMap.mul_def,
        Matrix.toLpLin_apply, Matrix.mulVec_eq_sum, Fin.sum_univ_three] <;>
      ring_nf

/-- The matrix of rotation about the `y`-axis by angle `α`. -/
@[simp]
def rot3y_mat (α : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
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
  toFun α := (rot3y_mat α).toEuclideanLin.toContinuousLinearMap
  map_zero_eq_one' := by
    ext v i
    fin_cases i <;>
      simp [Matrix.toLpLin_apply, Matrix.mulVec_eq_sum, Fin.sum_univ_three]
  map_add_eq_mul' α β := by
    ext v i
    fin_cases i <;>
      simp [rot3y_mat, cos_add, sin_add, ContinuousLinearMap.mul_def,
        Matrix.toLpLin_apply, Matrix.mulVec_eq_sum, Fin.sum_univ_three] <;>
      ring_nf

/-- The matrix of rotation about the `z`-axis by angle `α`. -/
@[simp]
def rot3z_mat (α : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
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
  toFun α := (rot3z_mat α).toEuclideanLin.toContinuousLinearMap
  map_zero_eq_one' := by
    ext v i
    fin_cases i <;>
      simp [Matrix.toLpLin_apply, Matrix.mulVec_eq_sum, Fin.sum_univ_three]
  map_add_eq_mul' α β := by
    ext v i
    fin_cases i <;>
      simp [rot3z_mat, cos_add, sin_add, ContinuousLinearMap.mul_def,
        Matrix.toLpLin_apply, Matrix.mulVec_eq_sum, Fin.sum_univ_three] <;>
      ring_nf

/-- Selects the coordinate-axis rotation matrix for a three-dimensional axis index. -/
def rot3_mat : Fin 3 → ℝ → Matrix (Fin 3) (Fin 3) ℝ
  | 0 => rot3x_mat
  | 1 => rot3y_mat
  | 2 => rot3z_mat

/-- Selects the coordinate-axis rotation additive character for a three-dimensional axis index. -/
def rot3 : Fin 3 → AddChar ℝ (ℝ³ →L[ℝ] ℝ³)
  | 0 => rot3x
  | 1 => rot3y
  | 2 => rot3z

theorem rot3_eq_rot3_mat_toEuclideanLin :
    rot3 d θ = (rot3_mat d θ).toEuclideanLin := by
  fin_cases d <;> simp [rot3, rot3_mat]

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
def proj_xy_r90_mat : Matrix (Fin 2) (Fin 3) ℝ :=
  Matrix.of fun
    | 0, 0 => 0
    | 0, 1 => 1
    | 0, 2 => 0
    | 1, 0 => -1
    | 1, 1 => 0
    | 1, 2 => 0

/-- Projection to the `xy`-plane followed by a right angle rotation. -/
@[simp]
def proj_xy_r90 : ℝ³ →L[ℝ] ℝ² :=
  proj_xy_r90_mat.toEuclideanLin.toContinuousLinearMap

/-- The matrix of reflection across the `x`-axis in the plane. -/
@[simp]
def flip_y_mat : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun
    | 0, 0 => 1
    | 0, 1 => 0
    | 1, 0 => 0
    | 1, 1 => -1

/-- Reflection across the `x`-axis in the plane. -/
@[simp]
def flip_y : ℝ² →L[ℝ] ℝ² :=
  flip_y_mat.toEuclideanLin.toContinuousLinearMap

/-- Projection after first orienting a three-dimensional body by angles `θ` and `φ`. -/
@[simp]
def proj_rot (θ φ : ℝ) : ℝ³ →L[ℝ] ℝ² :=
  proj_xy_r90 ∘L rot3 1 φ ∘L rot3 2 (-θ)

theorem rot_proj_rot :
    rot2 α ∘L proj_rot θ φ =
      proj_xy_r90 ∘L rot3 2 α ∘L rot3 1 φ ∘L rot3 2 (-θ) := by
  ext v i
  fin_cases i <;>
    simp [rot3, Matrix.toLpLin_apply, Matrix.mulVec_eq_sum, Fin.sum_univ_two,
      Fin.sum_univ_three] <;>
    ring

/-- A set is in convex position if no point lies in the convex hull of the others. -/
def convex_position (𝕜 V : Type) [PartialOrder 𝕜] [Semiring 𝕜]
    [AddCommMonoid V] [Module 𝕜 V] (P : Set V) : Prop :=
  ∀ p ∈ P, p ∉ convexHull 𝕜 (P \ Set.singleton p)

/-- A projection-interior formulation of Rupert's property for a set in space. -/
def rupert' (P : Set ℝ³) : Prop :=
  ∃ α θ₁ φ₁ θ₂ φ₂ : ℝ,
    (rot2 α ∘L proj_rot θ₁ φ₁) '' P ⊆
      interior (convexHull ℝ (proj_rot θ₂ φ₂ '' P))

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
def noperthedron_seed : Finset ℝ³ :=
  {C₁, C₂, C₃}

@[simp]
theorem mem_noperthedron_seed (p : ℝ³) :
    p ∈ noperthedron_seed ↔ p = C₁ ∨ p = C₂ ∨ p = C₃ := by
  unfold noperthedron_seed
  grind only [= Finset.mem_insert, = Set.mem_singleton_iff, = Finset.insert_eq_of_mem,
    = Finset.mem_singleton, cases Or]

/-- The finite symmetric point configuration used in the noperthedron construction. -/
def noperthedron : Finset ℝ³ :=
  (({1, -1} : Finset ℤ) ×ˢ Finset.range 15 ×ˢ noperthedron_seed).image
    fun (s, (k, p)) => (s • rot3 2 (k * 15⁻¹ * (2 * π))) p

theorem mem_noperthedron' (p : ℝ³) :
    p ∈ noperthedron ↔
      ∃ (s : ℤ) (k : ℕ) (q : ℝ³),
        s ∈ ({1, -1} : Finset ℤ) ∧
          k < 15 ∧ q ∈ noperthedron_seed ∧
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
          q ∈ noperthedron_seed ∧
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
    (proj_rot (θ + 2 / 15 * π) φ) '' noperthedron = proj_rot θ φ '' noperthedron := by
  ext p
  simp only [Set.mem_image, SetLike.mem_coe, mem_noperthedron, mem_noperthedron_seed,
    ↓existsAndEq, and_true, and_or_left, or_and_right, exists_or, proj_rot]
  have h (p : ℝ³) (s : ℤ) a b := calc
    (proj_xy_r90 ∘L rot3 1 φ ∘L rot3 2 a) ((s • rot3 2 b) p) = _ := by
      rfl
    _ = (proj_xy_r90 ∘L rot3 1 φ ∘L rot3 2 a ∘L (s • rot3 2 b)) p := by
      simp only [ContinuousLinearMap.comp_apply]
    _ = s • (proj_xy_r90 ∘L rot3 1 φ ∘L rot3 2 a ∘L rot3 2 b) p := by
      simp only [ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_apply]
    _ = s • (proj_xy_r90 ∘L rot3 1 φ ∘L (rot3 2 a ∘L rot3 2 b)) p := by
      simp
    _ = s • (proj_xy_r90 ∘L rot3 1 φ ∘L rot3 2 (a + b)) p := by
      simp [AddChar.map_add_eq_mul]
    _ = (proj_xy_r90 ∘L rot3 1 φ ∘L (s • rot3 2 (a + b))) p := by
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
    (rot2 (α + π) ∘L proj_rot θ φ) '' noperthedron =
      (rot2 α ∘L proj_rot θ φ) '' noperthedron := by
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

end LeanPool.Noperthedron
