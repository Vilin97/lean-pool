/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.DirectionalQuadratic.Frame

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Directional quadratic operators

Rank-one and mixed directional quadratic operators, together with finite sums.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace AleksandrovDifferentiability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Symmetric operators are closed under finite sums. -/
theorem isSymmetricOperator_sum {ι : Type*} {s : Finset ι} {B : ι → E →L[ℝ] E}
    (hB : ∀ i ∈ s, IsSymmetricOperator (B i)) :
    IsSymmetricOperator (∑ i ∈ s, B i) := by
  intro x y
  change inner ℝ ((∑ i ∈ s, B i) x) y = inner ℝ x ((∑ i ∈ s, B i) y)
  rw [sum_apply, sum_apply]
  rw [sum_inner, inner_sum]
  exact Finset.sum_congr rfl fun i hi => hB i hi x y

/-- The symmetric rank-one operator associated to a direction `v`, namely
`z ↦ inner ℝ v z • v`. -/
def directionalQuadraticOperator (v : E) : E →L[ℝ] E :=
  InnerProductSpace.rankOne ℝ v v

@[simp]
theorem directionalQuadraticOperator_apply (v z : E) :
    directionalQuadraticOperator v z = inner ℝ v z • v := by
  simp [directionalQuadraticOperator]

/-- The directional rank-one operator is symmetric. -/
theorem isSymmetricOperator_directionalQuadraticOperator (v : E) :
    IsSymmetricOperator (directionalQuadraticOperator v) := by
  exact InnerProductSpace.isSymmetric_rankOne_self (𝕜 := ℝ) v

/-- The quadratic form associated to a directional rank-one operator is the square of the
directional coordinate. -/
theorem inner_directionalQuadraticOperator_self (v z : E) :
    inner ℝ z (directionalQuadraticOperator v z) = (inner ℝ v z) ^ 2 := by
  rw [directionalQuadraticOperator_apply, real_inner_smul_right, real_inner_comm]
  ring

/-- The symmetric mixed rank-two operator associated to directions `v` and `w`. Its quadratic
form is the product of the two directional coordinates. -/
def mixedDirectionalQuadraticOperator (v w : E) : E →L[ℝ] E :=
  (1 / 2 : ℝ) •
    (InnerProductSpace.rankOne ℝ v w + InnerProductSpace.rankOne ℝ w v)

@[simp]
theorem mixedDirectionalQuadraticOperator_apply (v w z : E) :
    mixedDirectionalQuadraticOperator v w z =
      (1 / 2 : ℝ) • (inner ℝ w z • v + inner ℝ v z • w) := by
  simp [mixedDirectionalQuadraticOperator]

/-- The mixed directional operator is symmetric. -/
theorem isSymmetricOperator_mixedDirectionalQuadraticOperator (v w : E) :
    IsSymmetricOperator (mixedDirectionalQuadraticOperator v w) := by
  intro x y
  change inner ℝ (mixedDirectionalQuadraticOperator v w x) y =
    inner ℝ x (mixedDirectionalQuadraticOperator v w y)
  rw [mixedDirectionalQuadraticOperator_apply, mixedDirectionalQuadraticOperator_apply]
  simp [inner_add_left, inner_add_right, real_inner_smul_right, real_inner_comm]
  ring

/-- The mixed directional operator is symmetric in its two direction arguments. -/
theorem mixedDirectionalQuadraticOperator_comm (v w : E) :
    mixedDirectionalQuadraticOperator v w = mixedDirectionalQuadraticOperator w v := by
  ext z
  rw [mixedDirectionalQuadraticOperator_apply, mixedDirectionalQuadraticOperator_apply]
  rw [add_comm]

/-- The quadratic form of the mixed directional operator is the product of the corresponding
directional coordinates. -/
theorem inner_mixedDirectionalQuadraticOperator_self (v w z : E) :
    inner ℝ z (mixedDirectionalQuadraticOperator v w z) =
      inner ℝ v z * inner ℝ w z := by
  rw [mixedDirectionalQuadraticOperator_apply]
  simp [inner_add_right, real_inner_smul_right, real_inner_comm]
  ring

/-- Quadratic-form polarization for the mixed directional operator. -/
theorem inner_mixedDirectionalQuadraticOperator_self_eq_half_sub
    (v w z : E) :
    inner ℝ z (mixedDirectionalQuadraticOperator v w z) =
      (1 / 2 : ℝ) *
        (inner ℝ z (directionalQuadraticOperator (v + w) z) -
          inner ℝ z (directionalQuadraticOperator v z) -
            inner ℝ z (directionalQuadraticOperator w z)) := by
  rw [inner_mixedDirectionalQuadraticOperator_self,
    inner_directionalQuadraticOperator_self,
    inner_directionalQuadraticOperator_self,
    inner_directionalQuadraticOperator_self]
  simp [inner_add_left]
  ring

/-- Operator-level polarization for the mixed directional operator. -/
theorem mixedDirectionalQuadraticOperator_eq_half_sub
    (v w : E) :
    mixedDirectionalQuadraticOperator v w =
      (1 / 2 : ℝ) •
        (directionalQuadraticOperator (v + w) -
          directionalQuadraticOperator v - directionalQuadraticOperator w) := by
  ext z
  rw [mixedDirectionalQuadraticOperator_apply]
  simp [directionalQuadraticOperator_apply, inner_add_left, sub_eq_add_neg]
  module

/-- The mixed operator with the same direction twice is the pure directional rank-one operator. -/
theorem mixedDirectionalQuadraticOperator_self (v : E) :
    mixedDirectionalQuadraticOperator v v = directionalQuadraticOperator v := by
  ext z
  rw [mixedDirectionalQuadraticOperator_apply, directionalQuadraticOperator_apply]
  rw [← add_smul]
  rw [smul_smul]
  rw [show (1 / 2 * (inner ℝ v z + inner ℝ v z)) = inner ℝ v z by ring]

/-- A finite weighted sum of directional rank-one operators. -/
def directionalQuadraticSum {ι : Type*} (s : Finset ι) (v : ι → E) (q : ι → ℝ) :
    E →L[ℝ] E :=
  ∑ i ∈ s, q i • directionalQuadraticOperator (v i)

/-- Finite weighted sums of directional rank-one operators are symmetric. -/
theorem isSymmetricOperator_directionalQuadraticSum
    {ι : Type*} (s : Finset ι) (v : ι → E) (q : ι → ℝ) :
    IsSymmetricOperator (directionalQuadraticSum s v q) := by
  unfold directionalQuadraticSum
  exact isSymmetricOperator_sum fun i _ =>
    (isSymmetricOperator_directionalQuadraticOperator (v i)).smul (q i)

/-- The quadratic form of a finite weighted directional sum is the corresponding weighted sum of
squared directional coordinates. -/
theorem inner_directionalQuadraticSum_self
    {ι : Type*} (s : Finset ι) (v : ι → E) (q : ι → ℝ) (z : E) :
    inner ℝ z (directionalQuadraticSum s v q z) =
      ∑ i ∈ s, q i * (inner ℝ (v i) z) ^ 2 := by
  unfold directionalQuadraticSum
  rw [sum_apply, inner_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [smul_apply, real_inner_smul_right,
    inner_directionalQuadraticOperator_self]

/-- A finite matrix of mixed directional quadratic operators. The coefficient `a i j` multiplies
the operator with quadratic form `inner ℝ (v i) z * inner ℝ (v j) z`. -/
def mixedDirectionalQuadraticSum {ι : Type*} (s : Finset ι) (v : ι → E)
    (a : ι → ι → ℝ) : E →L[ℝ] E :=
  ∑ i ∈ s, ∑ j ∈ s, a i j • mixedDirectionalQuadraticOperator (v i) (v j)

/-- The mixed-directional sum is zero for the zero coefficient matrix. -/
@[simp]
theorem mixedDirectionalQuadraticSum_zero
    {ι : Type*} (s : Finset ι) (v : ι → E) :
    mixedDirectionalQuadraticSum s v (fun _ _ => 0) = 0 := by
  unfold mixedDirectionalQuadraticSum
  simp

/-- The mixed-directional sum is additive in the coefficient matrix. -/
theorem mixedDirectionalQuadraticSum_add
    {ι : Type*} (s : Finset ι) (v : ι → E) (a b : ι → ι → ℝ) :
    mixedDirectionalQuadraticSum s v (fun i j => a i j + b i j) =
      mixedDirectionalQuadraticSum s v a + mixedDirectionalQuadraticSum s v b := by
  unfold mixedDirectionalQuadraticSum
  ext z
  simp [add_smul, Finset.sum_add_distrib]

/-- The mixed-directional sum is homogeneous in the coefficient matrix. -/
theorem mixedDirectionalQuadraticSum_smul
    {ι : Type*} (s : Finset ι) (v : ι → E) (c : ℝ) (a : ι → ι → ℝ) :
    mixedDirectionalQuadraticSum s v (fun i j => c * a i j) =
      c • mixedDirectionalQuadraticSum s v a := by
  unfold mixedDirectionalQuadraticSum
  ext z
  simp [mul_smul, Finset.smul_sum]

/-- Finite coefficient matrices of mixed directional quadratic operators are symmetric. -/
theorem isSymmetricOperator_mixedDirectionalQuadraticSum
    {ι : Type*} (s : Finset ι) (v : ι → E) (a : ι → ι → ℝ) :
    IsSymmetricOperator (mixedDirectionalQuadraticSum s v a) := by
  unfold mixedDirectionalQuadraticSum
  refine isSymmetricOperator_sum fun i _ => ?_
  refine isSymmetricOperator_sum fun j _ => ?_
  exact (isSymmetricOperator_mixedDirectionalQuadraticOperator (v i) (v j)).smul (a i j)

/-- The quadratic form of a finite mixed directional sum is the corresponding coefficient
matrix expression in the directional coordinates. -/
theorem inner_mixedDirectionalQuadraticSum_self
    {ι : Type*} (s : Finset ι) (v : ι → E) (a : ι → ι → ℝ) (z : E) :
    inner ℝ z (mixedDirectionalQuadraticSum s v a z) =
      ∑ i ∈ s, ∑ j ∈ s,
        a i j * inner ℝ (v i) z * inner ℝ (v j) z := by
  unfold mixedDirectionalQuadraticSum
  rw [sum_apply, inner_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [sum_apply, inner_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [smul_apply, real_inner_smul_right,
    inner_mixedDirectionalQuadraticOperator_self]
  ring

/-- A finite mixed-directional quadratic form is bounded by the sum of the absolute coefficient
values times `‖z‖ ^ 2` on a finite orthonormal spanning family. -/
theorem abs_inner_mixedDirectionalQuadraticSum_self_le
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → E}
    (hv : FiniteOrthonormalSpanningOn s v) (a : ι → ι → ℝ) (z : E) :
    |inner ℝ z (mixedDirectionalQuadraticSum s v a z)| ≤
      (∑ i ∈ s, ∑ j ∈ s, |a i j|) * ‖z‖ ^ 2 := by
  rw [inner_mixedDirectionalQuadraticSum_self]
  calc
    |∑ i ∈ s, ∑ j ∈ s, a i j * inner ℝ (v i) z * inner ℝ (v j) z|
        ≤ ∑ i ∈ s, |∑ j ∈ s, a i j * inner ℝ (v i) z * inner ℝ (v j) z| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, |a i j * inner ℝ (v i) z * inner ℝ (v j) z| := by
          exact Finset.sum_le_sum fun i hi => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, |a i j| * ‖z‖ ^ 2 := by
          refine Finset.sum_le_sum fun i hi => ?_
          refine Finset.sum_le_sum fun j hj => ?_
          have hterm :
              |a i j * inner ℝ (v i) z * inner ℝ (v j) z| =
                |a i j| * |inner ℝ (v i) z * inner ℝ (v j) z| := by
            rw [mul_assoc, abs_mul]
          rw [hterm]
          exact mul_le_mul_of_nonneg_left
            (hv.abs_inner_mul_inner_le_norm_sq hi hj z) (abs_nonneg (a i j))
    _ = (∑ i ∈ s, ∑ j ∈ s, |a i j|) * ‖z‖ ^ 2 := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [Finset.sum_mul]

/-- Constant-bound form of `abs_inner_mixedDirectionalQuadraticSum_self_le`. -/
theorem exists_const_abs_inner_mixedDirectionalQuadraticSum_self_le
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → E}
    (hv : FiniteOrthonormalSpanningOn s v) (a : ι → ι → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : E, |inner ℝ z (mixedDirectionalQuadraticSum s v a z)| ≤ C * ‖z‖ ^ 2 := by
  refine ⟨∑ i ∈ s, ∑ j ∈ s, |a i j|, ?_, ?_⟩
  · exact Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj => abs_nonneg _
  · intro z
    exact abs_inner_mixedDirectionalQuadraticSum_self_le hv a z

/-- Constant-bound form for the actual half-quadratic term used in second-order expansions. -/
theorem exists_const_norm_half_inner_mixedDirectionalQuadraticSum_le
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → E}
    (hv : FiniteOrthonormalSpanningOn s v) (a : ι → ι → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : E, ‖(1 / 2 : ℝ) * inner ℝ z (mixedDirectionalQuadraticSum s v a z)‖ ≤
        C * ‖z‖ ^ 2 := by
  rcases exists_const_abs_inner_mixedDirectionalQuadraticSum_self_le hv a with
    ⟨C, hC, hbound⟩
  refine ⟨(1 / 2 : ℝ) * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro z
  calc
    ‖(1 / 2 : ℝ) * inner ℝ z (mixedDirectionalQuadraticSum s v a z)‖
        = (1 / 2 : ℝ) * |inner ℝ z (mixedDirectionalQuadraticSum s v a z)| := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
    _ ≤ (1 / 2 : ℝ) * (C * ‖z‖ ^ 2) := by
          exact mul_le_mul_of_nonneg_left (hbound z) (by norm_num)
    _ = ((1 / 2 : ℝ) * C) * ‖z‖ ^ 2 := by ring

/-- Transposing the finite mixed-directional coefficient matrix does not change the resulting
operator. -/
theorem mixedDirectionalQuadraticSum_transpose
    {ι : Type*} (s : Finset ι) (v : ι → E) (a : ι → ι → ℝ) :
    mixedDirectionalQuadraticSum s v (fun i j => a j i) =
      mixedDirectionalQuadraticSum s v a := by
  unfold mixedDirectionalQuadraticSum
  calc
    (∑ i ∈ s, ∑ j ∈ s, a j i • mixedDirectionalQuadraticOperator (v i) (v j))
        = ∑ j ∈ s, ∑ i ∈ s,
            a j i • mixedDirectionalQuadraticOperator (v i) (v j) := by
          rw [Finset.sum_comm]
    _ = ∑ j ∈ s, ∑ i ∈ s,
            a j i • mixedDirectionalQuadraticOperator (v j) (v i) := by
          refine Finset.sum_congr rfl fun j hj => ?_
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [mixedDirectionalQuadraticOperator_comm]
    _ = ∑ i ∈ s, ∑ j ∈ s, a i j • mixedDirectionalQuadraticOperator (v i) (v j) := rfl

/-- Replacing a coefficient matrix by its symmetric part does not change the assembled
mixed-directional quadratic operator. -/
theorem mixedDirectionalQuadraticSum_symmetrized
    {ι : Type*} (s : Finset ι) (v : ι → E) (a : ι → ι → ℝ) :
    mixedDirectionalQuadraticSum s v (fun i j => (1 / 2 : ℝ) * (a i j + a j i)) =
      mixedDirectionalQuadraticSum s v a := by
  calc
    mixedDirectionalQuadraticSum s v (fun i j => (1 / 2 : ℝ) * (a i j + a j i))
        = mixedDirectionalQuadraticSum s v
            (fun i j => (1 / 2 : ℝ) * a i j + (1 / 2 : ℝ) * a j i) := by
          congr
          ext i j
          ring
    _ = mixedDirectionalQuadraticSum s v (fun i j => (1 / 2 : ℝ) * a i j) +
          mixedDirectionalQuadraticSum s v (fun i j => (1 / 2 : ℝ) * a j i) := by
          rw [mixedDirectionalQuadraticSum_add]
    _ = (1 / 2 : ℝ) • mixedDirectionalQuadraticSum s v a +
          (1 / 2 : ℝ) • mixedDirectionalQuadraticSum s v (fun i j => a j i) := by
          rw [mixedDirectionalQuadraticSum_smul, mixedDirectionalQuadraticSum_smul]
    _ = (1 / 2 : ℝ) • mixedDirectionalQuadraticSum s v a +
          (1 / 2 : ℝ) • mixedDirectionalQuadraticSum s v a := by
          rw [mixedDirectionalQuadraticSum_transpose]
    _ = mixedDirectionalQuadraticSum s v a := by
          module

/-- A diagonal mixed-directional coefficient matrix gives the corresponding pure directional
quadratic sum. -/
theorem mixedDirectionalQuadraticSum_diagonal
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → E) (q : ι → ℝ) :
    mixedDirectionalQuadraticSum s v (fun i j => if i = j then q i else 0) =
      directionalQuadraticSum s v q := by
  unfold mixedDirectionalQuadraticSum directionalQuadraticSum
  ext z
  rw [sum_apply, sum_apply]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [sum_apply]
  by_cases his : i ∈ s
  · rw [Finset.sum_eq_single i]
    · simp [mixedDirectionalQuadraticOperator_self]
    · intro j hj hji
      have hij : i ≠ j := fun h => hji h.symm
      simp [hij]
    · intro hi_not
      exact (hi_not his).elim
  · exact (his hi).elim

/-- The coefficient matrix recovered from pure directional quadratic coefficients `q i` and
pairwise-sum coefficients `r i j` by the usual polarization formula. The diagonal is kept equal
to the pure coefficient, and off-diagonal entries use
`(r i j - q i - q j) / 2`. -/
def polarizedMixedCoefficient {ι : Type*} [DecidableEq ι]
    (q : ι → ℝ) (r : ι → ι → ℝ) : ι → ι → ℝ :=
  fun i j => if i = j then q i else (r i j - q i - q j) / 2

@[simp]
theorem polarizedMixedCoefficient_self
    {ι : Type*} [DecidableEq ι] (q : ι → ℝ) (r : ι → ι → ℝ) (i : ι) :
    polarizedMixedCoefficient q r i i = q i := by
  simp [polarizedMixedCoefficient]

theorem polarizedMixedCoefficient_of_ne
    {ι : Type*} [DecidableEq ι] (q : ι → ℝ) (r : ι → ι → ℝ)
    {i j : ι} (hij : i ≠ j) :
    polarizedMixedCoefficient q r i j = (r i j - q i - q j) / 2 := by
  simp [polarizedMixedCoefficient, hij]

/-- The polarized mixed coefficient matrix is symmetric on a finite set when the supplied
pairwise-sum coefficients are symmetric there. -/
theorem polarizedMixedCoefficient_symm_on
    {ι : Type*} [DecidableEq ι] {s : Finset ι} (q : ι → ℝ) (r : ι → ι → ℝ)
    (hr : ∀ ⦃i : ι⦄, i ∈ s → ∀ ⦃j : ι⦄, j ∈ s → r j i = r i j)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) :
    polarizedMixedCoefficient q r j i = polarizedMixedCoefficient q r i j := by
  by_cases hij : i = j
  · subst j
    simp
  · have hji : j ≠ i := fun h => hij h.symm
    rw [polarizedMixedCoefficient_of_ne q r hji,
      polarizedMixedCoefficient_of_ne q r hij, hr hi hj]
    ring

/-- The mixed-directional quadratic operator assembled from pure coefficients `q i` and
pairwise-sum coefficients `r i j` by polarization. -/
def polarizedMixedQuadraticSum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → E) (q : ι → ℝ) (r : ι → ι → ℝ) : E →L[ℝ] E :=
  mixedDirectionalQuadraticSum s v (polarizedMixedCoefficient q r)

@[simp]
theorem polarizedMixedQuadraticSum_eq
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → E)
    (q : ι → ℝ) (r : ι → ι → ℝ) :
    polarizedMixedQuadraticSum s v q r =
      mixedDirectionalQuadraticSum s v (polarizedMixedCoefficient q r) :=
  rfl

/-- The polarized mixed-directional quadratic operator is symmetric. -/
theorem isSymmetricOperator_polarizedMixedQuadraticSum
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → E)
    (q : ι → ℝ) (r : ι → ι → ℝ) :
    IsSymmetricOperator (polarizedMixedQuadraticSum s v q r) :=
  isSymmetricOperator_mixedDirectionalQuadraticSum s v (polarizedMixedCoefficient q r)

/-- Quadratic form of the polarized mixed-directional model. -/
theorem inner_polarizedMixedQuadraticSum_self
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → E)
    (q : ι → ℝ) (r : ι → ι → ℝ) (z : E) :
    inner ℝ z (polarizedMixedQuadraticSum s v q r z) =
      ∑ i ∈ s, ∑ j ∈ s,
        polarizedMixedCoefficient q r i j * inner ℝ (v i) z * inner ℝ (v j) z :=
  inner_mixedDirectionalQuadraticSum_self s v (polarizedMixedCoefficient q r) z

end AleksandrovDifferentiability
