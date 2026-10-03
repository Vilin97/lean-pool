/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Foundation.SecondOrder

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Directional quadratic operators

This file records small finite-dimensional-algebra helpers for rebuilding symmetric quadratic
candidates from directional second-order coefficients. The analytic slicing argument will later
produce scalar coefficients along selected directions; these definitions package the corresponding
rank-one symmetric operators.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace AleksandrovDifferentiability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A finite list of directions is orthonormal on the selected index set. This lightweight
finite-set predicate is convenient for the slicing reconstruction layer, where the directions are
usually carried by a `Finset` rather than by a global basis object. -/
def FiniteOrthonormalOn {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → E) : Prop :=
  ∀ ⦃i : ι⦄, i ∈ s → ∀ ⦃j : ι⦄, j ∈ s →
    inner ℝ (v i) (v j) = if i = j then 1 else 0

/-- A finite list of directions spans the ambient space on the selected index set. -/
def FiniteSpanningOn {ι : Type*} (s : Finset ι) (v : ι → E) : Prop :=
  ∀ z : E, z ∈ Submodule.span ℝ (v '' (s : Set ι))

/-- A finite orthonormal spanning family on the selected index set. This is the finite-frame
condition expected for the eventual directional reconstruction step. -/
def FiniteOrthonormalSpanningOn {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → E) : Prop :=
  FiniteOrthonormalOn s v ∧ FiniteSpanningOn s v

namespace FiniteOrthonormalOn

theorem of_orthonormal {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → E}
    (hv : Orthonormal ℝ v) :
    FiniteOrthonormalOn s v := by
  intro i _hi j _hj
  exact (orthonormal_iff_ite.mp hv) i j

theorem mono {ι : Type*} [DecidableEq ι] {s t : Finset ι} {v : ι → E}
    (hv : FiniteOrthonormalOn s v) (hts : t ⊆ s) :
    FiniteOrthonormalOn t v := by
  intro i hi j hj
  exact hv (hts hi) (hts hj)

/-- Linear isometry equivalences preserve finite orthonormal families. -/
theorem image_linearIsometryEquiv
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → E}
    (hv : FiniteOrthonormalOn s v) (e : E ≃ₗᵢ[ℝ] F) :
    FiniteOrthonormalOn s (fun i ↦ e (v i)) := by
  intro i hi j hj
  rw [LinearIsometryEquiv.inner_map_map]
  exact hv hi hj

theorem univ_iff_orthonormal {ι : Type*} [Fintype ι] [DecidableEq ι] {v : ι → E} :
    FiniteOrthonormalOn Finset.univ v ↔ Orthonormal ℝ v := by
  constructor
  · intro hv
    rw [orthonormal_iff_ite]
    intro i j
    exact hv (Finset.mem_univ i) (Finset.mem_univ j)
  · exact of_orthonormal

theorem inner_eq_ite {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → E}
    (hv : FiniteOrthonormalOn s v) {i j : ι} (hi : i ∈ s) (hj : j ∈ s) :
    inner ℝ (v i) (v j) = if i = j then 1 else 0 :=
  hv hi hj

theorem inner_self {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → E}
    (hv : FiniteOrthonormalOn s v) {i : ι} (hi : i ∈ s) :
    inner ℝ (v i) (v i) = 1 := by
  rw [hv hi hi]
  simp

/-- Every member of a finite orthonormal family has squared norm one. -/
theorem norm_sq {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → E}
    (hv : FiniteOrthonormalOn s v) {i : ι} (hi : i ∈ s) :
    ‖v i‖ ^ 2 = 1 := by
  simpa only [real_inner_self_eq_norm_sq] using hv.inner_self hi

theorem inner_ne {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → E}
    (hv : FiniteOrthonormalOn s v) {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
    (hij : i ≠ j) :
    inner ℝ (v i) (v j) = 0 := by
  rw [hv hi hj]
  simp [hij]

/-- The coordinate projection onto a finite orthonormal family has the expected coordinate in
each selected direction. -/
theorem inner_sum_inner_smul {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → E}
    (hv : FiniteOrthonormalOn s v) {k : ι} (hk : k ∈ s) (z : E) :
    inner ℝ (v k) (∑ i ∈ s, inner ℝ (v i) z • v i) = inner ℝ (v k) z := by
  rw [inner_sum]
  rw [Finset.sum_eq_single k]
  · rw [real_inner_smul_right, hv.inner_self hk]
    ring
  · intro i hi hik
    rw [real_inner_smul_right, hv.inner_ne hk hi (fun h => hik h.symm)]
    ring
  · intro hk_not
    exact (hk_not hk).elim

end FiniteOrthonormalOn

namespace FiniteSpanningOn

theorem univ_of_basis {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E) :
    FiniteSpanningOn Finset.univ (b : ι → E) := by
  intro z
  have hz : z ∈ (⊤ : Submodule ℝ E) := trivial
  rw [← b.span_eq] at hz
  simp at hz ⊢

theorem univ_of_orthonormalBasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) :
    FiniteSpanningOn Finset.univ (b : ι → E) := by
  simpa [OrthonormalBasis.coe_toBasis] using
    (univ_of_basis (b := b.toBasis))

/-- Linear isometry equivalences preserve finite spanning families. -/
theorem image_linearIsometryEquiv
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {ι : Type*} {s : Finset ι} {v : ι → E}
    (hv : FiniteSpanningOn s v) (e : E ≃ₗᵢ[ℝ] F) :
    FiniteSpanningOn s (fun i ↦ e (v i)) := by
  intro y
  have hpre := hv (e.symm y)
  have hmap :
      e (e.symm y) ∈ Submodule.span ℝ ((fun i ↦ e (v i)) '' (s : Set ι)) := by
    refine Submodule.span_induction (fun z hz ↦ ?_) ?_ ?_ ?_ hpre
    · rcases hz with ⟨i, hi, rfl⟩
      exact Submodule.subset_span ⟨i, hi, rfl⟩
    · simp
    · intro z w _hz _hw hzmem hwmem
      simpa [map_add] using Submodule.add_mem _ hzmem hwmem
    · intro a z _hz hzmem
      simpa [map_smul] using Submodule.smul_mem _ a hzmem
  simpa using hmap

end FiniteSpanningOn

namespace FiniteOrthonormalSpanningOn

theorem univ_of_orthonormalBasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ E) :
    FiniteOrthonormalSpanningOn Finset.univ (b : ι → E) :=
  ⟨FiniteOrthonormalOn.of_orthonormal (s := Finset.univ) b.orthonormal,
    FiniteSpanningOn.univ_of_orthonormalBasis b⟩

/-- Linear isometry equivalences preserve finite orthonormal spanning families. -/
theorem image_linearIsometryEquiv
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → E}
    (hv : FiniteOrthonormalSpanningOn s v) (e : E ≃ₗᵢ[ℝ] F) :
    FiniteOrthonormalSpanningOn s (fun i ↦ e (v i)) :=
  ⟨hv.1.image_linearIsometryEquiv e, hv.2.image_linearIsometryEquiv e⟩

/-- Mathlib's standard orthonormal basis is a finite orthonormal spanning family. -/
theorem univ_of_stdOrthonormalBasis
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] :
    FiniteOrthonormalSpanningOn Finset.univ
      (stdOrthonormalBasis ℝ E : Fin (Module.finrank ℝ E) → E) :=
  univ_of_orthonormalBasis (stdOrthonormalBasis ℝ E)

/-- Coordinate reconstruction in a finite orthonormal spanning family. -/
theorem sum_inner_smul_eq {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → E}
    (hv : FiniteOrthonormalSpanningOn s v) (z : E) :
    (∑ i ∈ s, inner ℝ (v i) z • v i) = z := by
  let P : E := ∑ i ∈ s, inner ℝ (v i) z • v i
  have hP : P ∈ Submodule.span ℝ (v '' (s : Set ι)) := by
    dsimp [P]
    exact Submodule.sum_mem _ fun i hi =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  have hdiff : z - P ∈ Submodule.span ℝ (v '' (s : Set ι)) :=
    Submodule.sub_mem _ (hv.2 z) hP
  have horth_gen :
      ∀ ⦃i : ι⦄, i ∈ s → inner ℝ (v i) (z - P) = 0 := by
    intro i hi
    rw [inner_sub_right]
    have hcoord := hv.1.inner_sum_inner_smul hi z
    change inner ℝ (v i) z -
        inner ℝ (v i) (∑ j ∈ s, inner ℝ (v j) z • v j) = 0
    rw [hcoord]
    ring
  have horth_span :
      ∀ y ∈ Submodule.span ℝ (v '' (s : Set ι)), inner ℝ y (z - P) = 0 := by
    intro y hy
    refine Submodule.span_induction (fun y hy => ?_) ?_ ?_ ?_ hy
    · rcases hy with ⟨i, hi, rfl⟩
      exact horth_gen hi
    · simp
    · intro y w _hy _hw hy0 hw0
      rw [inner_add_left, hy0, hw0, add_zero]
    · intro a y _hy hy0
      rw [real_inner_smul_left, hy0, mul_zero]
  have hzero_inner : inner ℝ (z - P) (z - P) = 0 :=
    horth_span (z - P) hdiff
  have hzero : z - P = 0 := inner_self_eq_zero.mp hzero_inner
  exact (sub_eq_zero.mp hzero).symm

/-- A finite orthonormal spanning family contains a nonzero selected vector whenever the ambient
space contains a nonzero vector. -/
theorem exists_ne_zero_of_nonzero {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → E}
    (hv : FiniteOrthonormalSpanningOn s v) {z : E} (hz : z ≠ 0) :
    ∃ i, i ∈ s ∧ v i ≠ 0 := by
  by_contra hnone
  have hzero : ∀ ⦃i : ι⦄, i ∈ s → v i = 0 := by
    intro i hi
    by_contra hvi
    exact hnone ⟨i, hi, hvi⟩
  have hsum : (∑ i ∈ s, inner ℝ (v i) z • v i) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    simp [hzero hi]
  have hcoord := hv.sum_inner_smul_eq z
  exact hz (by simpa [hsum] using hcoord.symm)

/-- Pythagorean identity for coordinates in a finite orthonormal spanning family. -/
theorem sum_inner_sq_eq_norm_sq {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → E}
    (hv : FiniteOrthonormalSpanningOn s v) (z : E) :
    (∑ i ∈ s, (inner ℝ (v i) z) ^ 2) = ‖z‖ ^ 2 := by
  have hcoord := hv.sum_inner_smul_eq z
  calc
    (∑ i ∈ s, (inner ℝ (v i) z) ^ 2)
        = inner ℝ (∑ i ∈ s, inner ℝ (v i) z • v i) z := by
          rw [sum_inner]
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [real_inner_smul_left]
          ring
    _ = inner ℝ z z := by rw [hcoord]
    _ = ‖z‖ ^ 2 := real_inner_self_eq_norm_sq z

/-- Each coordinate square is bounded by the squared norm in a finite orthonormal spanning
family. -/
theorem inner_sq_le_norm_sq {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → E}
    (hv : FiniteOrthonormalSpanningOn s v) {i : ι} (hi : i ∈ s) (z : E) :
    (inner ℝ (v i) z) ^ 2 ≤ ‖z‖ ^ 2 := by
  rw [← hv.sum_inner_sq_eq_norm_sq z]
  exact Finset.single_le_sum
    (s := s) (f := fun j => (inner ℝ (v j) z) ^ 2)
    (fun _ _ => sq_nonneg _) hi

/-- Absolute-value form of the coordinate bound in a finite orthonormal spanning family. -/
theorem abs_inner_le_norm {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → E}
    (hv : FiniteOrthonormalSpanningOn s v) {i : ι} (hi : i ∈ s) (z : E) :
    |inner ℝ (v i) z| ≤ ‖z‖ :=
  abs_le_of_sq_le_sq (hv.inner_sq_le_norm_sq hi z) (norm_nonneg z)

/-- Products of two frame coordinates are bounded by the squared norm. -/
theorem abs_inner_mul_inner_le_norm_sq {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {v : ι → E} (hv : FiniteOrthonormalSpanningOn s v)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (z : E) :
    |inner ℝ (v i) z * inner ℝ (v j) z| ≤ ‖z‖ ^ 2 := by
  rw [abs_mul]
  have hi_le := hv.abs_inner_le_norm hi z
  have hj_le := hv.abs_inner_le_norm hj z
  calc
    |inner ℝ (v i) z| * |inner ℝ (v j) z| ≤ ‖z‖ * ‖z‖ :=
      mul_le_mul hi_le hj_le (abs_nonneg _) (norm_nonneg _)
    _ = ‖z‖ ^ 2 := by ring

/-- Uniformly weighted coordinate-square sum in a finite orthonormal spanning family. -/
theorem sum_const_mul_inner_sq_eq_mul_norm_sq {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {v : ι → E} (hv : FiniteOrthonormalSpanningOn s v)
    (c : ℝ) (z : E) :
    (∑ i ∈ s, c * (inner ℝ (v i) z) ^ 2) = c * ‖z‖ ^ 2 := by
  rw [← Finset.mul_sum, hv.sum_inner_sq_eq_norm_sq]

/-- If a symmetric operator has zero quadratic form on each frame direction and on each pairwise
sum of frame directions, then the operator is zero. This is the algebraic uniqueness input for
recovering a Hessian candidate from pure and pairwise-sum directional coefficients. -/
theorem eq_zero_of_quadraticForm_eq_zero_on_frame_and_add
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → E}
    (hv : FiniteOrthonormalSpanningOn s v) {B : E →L[ℝ] E}
    (hB : IsSymmetricOperator B)
    (hpure : ∀ ⦃i : ι⦄, i ∈ s → inner ℝ (v i) (B (v i)) = 0)
    (hpair : ∀ ⦃i : ι⦄, i ∈ s → ∀ ⦃j : ι⦄, j ∈ s →
      inner ℝ (v i + v j) (B (v i + v j)) = 0) :
    B = 0 := by
  have hcoord : ∀ ⦃i : ι⦄, i ∈ s → ∀ ⦃j : ι⦄, j ∈ s →
      inner ℝ (v i) (B (v j)) = 0 := by
    intro i hi j hj
    by_cases hij : i = j
    · subst j
      exact hpure hi
    · have hp := hpair hi hj
      have hsymm : inner ℝ (v j) (B (v i)) = inner ℝ (v i) (B (v j)) := by
        calc
          inner ℝ (v j) (B (v i)) = inner ℝ (B (v i)) (v j) := by
            rw [real_inner_comm]
          _ = inner ℝ (v i) (B (v j)) := hB (v i) (v j)
      have hexpand :
          inner ℝ (v i + v j) (B (v i + v j)) =
            inner ℝ (v i) (B (v i)) + inner ℝ (v i) (B (v j)) +
              (inner ℝ (v j) (B (v i)) + inner ℝ (v j) (B (v j))) := by
        simp [map_add, inner_add_left, inner_add_right]
        ring
      have hsum :
          inner ℝ (v i) (B (v j)) + inner ℝ (v j) (B (v i)) = 0 := by
        rw [hexpand, hpure hi, hpure hj] at hp
        linarith
      rw [hsymm] at hsum
      linarith
  have hbilin : ∀ x y : E, inner ℝ x (B y) = 0 := by
    intro x y
    have hx := hv.sum_inner_smul_eq x
    have hy := hv.sum_inner_smul_eq y
    calc
      inner ℝ x (B y)
          = inner ℝ (∑ i ∈ s, inner ℝ (v i) x • v i)
              (B (∑ j ∈ s, inner ℝ (v j) y • v j)) := by
                rw [hx, hy]
      _ = 0 := by
        rw [map_sum]
        simp_rw [map_smul, inner_sum, sum_inner, real_inner_smul_left,
          real_inner_smul_right]
        refine Finset.sum_eq_zero fun j hj => ?_
        refine Finset.sum_eq_zero fun i hi => ?_
        rw [hcoord hi hj]
        ring
  ext y
  have hself : inner ℝ (B y) (B y) = 0 := hbilin (B y) y
  exact inner_self_eq_zero.mp hself

/-- Two symmetric operators are equal if their quadratic forms agree on each frame direction and
on each pairwise sum of frame directions. -/
theorem ext_of_quadraticForm_eq_on_frame_and_add
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → E}
    (hv : FiniteOrthonormalSpanningOn s v) {B C : E →L[ℝ] E}
    (hB : IsSymmetricOperator B) (hC : IsSymmetricOperator C)
    (hpure : ∀ ⦃i : ι⦄, i ∈ s →
      inner ℝ (v i) (B (v i)) = inner ℝ (v i) (C (v i)))
    (hpair : ∀ ⦃i : ι⦄, i ∈ s → ∀ ⦃j : ι⦄, j ∈ s →
      inner ℝ (v i + v j) (B (v i + v j)) =
        inner ℝ (v i + v j) (C (v i + v j))) :
    B = C := by
  have hsymm : IsSymmetricOperator (B - C) := by
    intro x y
    calc
      inner ℝ ((B - C) x) y = inner ℝ (B x) y - inner ℝ (C x) y := by
        simp [inner_sub_left]
      _ = inner ℝ x (B y) - inner ℝ x (C y) := by
        have hBx : inner ℝ (B x) y = inner ℝ x (B y) := by
          simpa using hB x y
        have hCx : inner ℝ (C x) y = inner ℝ x (C y) := by
          simpa using hC x y
        rw [hBx, hCx]
      _ = inner ℝ x ((B - C) y) := by
        simp [inner_sub_right]
  have hzero : B - C = 0 := by
    refine hv.eq_zero_of_quadraticForm_eq_zero_on_frame_and_add hsymm ?_ ?_
    · intro i hi
      simpa [sub_apply, inner_sub_right] using
        sub_eq_zero.mpr (hpure hi)
    · intro i hi j hj
      let d := v i + v j
      calc
        inner ℝ d ((B - C) d)
            = inner ℝ d (B (v i) + B (v j)) -
                inner ℝ d (C (v i) + C (v j)) := by
              simp [d, map_add, inner_sub_right,
                inner_add_right]
              ring
        _ = inner ℝ d (B d) - inner ℝ d (C d) := by
              simp [d, map_add]
        _ = 0 := by
              rw [hpair hi hj, sub_self]
  exact sub_eq_zero.mp hzero

/-- Off-diagonal version of
`FiniteOrthonormalSpanningOn.eq_zero_of_quadraticForm_eq_zero_on_frame_and_add`.
The diagonal pairwise-sum directions carry no additional information beyond the pure directions. -/
theorem eq_zero_of_quadraticForm_eq_zero_on_frame_and_add_offDiagonal
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → E}
    (hv : FiniteOrthonormalSpanningOn s v) {B : E →L[ℝ] E}
    (hB : IsSymmetricOperator B)
    (hpure : ∀ ⦃i : ι⦄, i ∈ s → inner ℝ (v i) (B (v i)) = 0)
    (hpair : ∀ ⦃i : ι⦄, i ∈ s → ∀ ⦃j : ι⦄, j ∈ s → i ≠ j →
      inner ℝ (v i + v j) (B (v i + v j)) = 0) :
    B = 0 := by
  have hcoord : ∀ ⦃i : ι⦄, i ∈ s → ∀ ⦃j : ι⦄, j ∈ s →
      inner ℝ (v i) (B (v j)) = 0 := by
    intro i hi j hj
    by_cases hij : i = j
    · subst j
      exact hpure hi
    · have hp := hpair hi hj hij
      have hsymm : inner ℝ (v j) (B (v i)) = inner ℝ (v i) (B (v j)) := by
        calc
          inner ℝ (v j) (B (v i)) = inner ℝ (B (v i)) (v j) := by
            rw [real_inner_comm]
          _ = inner ℝ (v i) (B (v j)) := hB (v i) (v j)
      have hexpand :
          inner ℝ (v i + v j) (B (v i + v j)) =
            inner ℝ (v i) (B (v i)) + inner ℝ (v i) (B (v j)) +
              (inner ℝ (v j) (B (v i)) + inner ℝ (v j) (B (v j))) := by
        simp [map_add, inner_add_left, inner_add_right]
        ring
      have hsum :
          inner ℝ (v i) (B (v j)) + inner ℝ (v j) (B (v i)) = 0 := by
        rw [hexpand, hpure hi, hpure hj] at hp
        linarith
      rw [hsymm] at hsum
      linarith
  have hbilin : ∀ x y : E, inner ℝ x (B y) = 0 := by
    intro x y
    have hx := hv.sum_inner_smul_eq x
    have hy := hv.sum_inner_smul_eq y
    calc
      inner ℝ x (B y)
          = inner ℝ (∑ i ∈ s, inner ℝ (v i) x • v i)
              (B (∑ j ∈ s, inner ℝ (v j) y • v j)) := by
                rw [hx, hy]
      _ = 0 := by
        rw [map_sum]
        simp_rw [map_smul, inner_sum, sum_inner, real_inner_smul_left,
          real_inner_smul_right]
        refine Finset.sum_eq_zero fun j hj => ?_
        refine Finset.sum_eq_zero fun i hi => ?_
        rw [hcoord hi hj]
        ring
  ext y
  have hself : inner ℝ (B y) (B y) = 0 := hbilin (B y) y
  exact inner_self_eq_zero.mp hself

/-- Off-diagonal version of
`FiniteOrthonormalSpanningOn.ext_of_quadraticForm_eq_on_frame_and_add`. -/
theorem ext_of_quadraticForm_eq_on_frame_and_add_offDiagonal
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → E}
    (hv : FiniteOrthonormalSpanningOn s v) {B C : E →L[ℝ] E}
    (hB : IsSymmetricOperator B) (hC : IsSymmetricOperator C)
    (hpure : ∀ ⦃i : ι⦄, i ∈ s →
      inner ℝ (v i) (B (v i)) = inner ℝ (v i) (C (v i)))
    (hpair : ∀ ⦃i : ι⦄, i ∈ s → ∀ ⦃j : ι⦄, j ∈ s → i ≠ j →
      inner ℝ (v i + v j) (B (v i + v j)) =
        inner ℝ (v i + v j) (C (v i + v j))) :
    B = C := by
  have hsymm : IsSymmetricOperator (B - C) := by
    intro x y
    calc
      inner ℝ ((B - C) x) y = inner ℝ (B x) y - inner ℝ (C x) y := by
        simp [inner_sub_left]
      _ = inner ℝ x (B y) - inner ℝ x (C y) := by
        have hBx : inner ℝ (B x) y = inner ℝ x (B y) := by
          simpa using hB x y
        have hCx : inner ℝ (C x) y = inner ℝ x (C y) := by
          simpa using hC x y
        rw [hBx, hCx]
      _ = inner ℝ x ((B - C) y) := by
        simp [inner_sub_right]
  have hzero : B - C = 0 := by
    refine hv.eq_zero_of_quadraticForm_eq_zero_on_frame_and_add_offDiagonal hsymm ?_ ?_
    · intro i hi
      simpa [sub_apply, inner_sub_right] using
        sub_eq_zero.mpr (hpure hi)
    · intro i hi j hj hij
      let d := v i + v j
      calc
        inner ℝ d ((B - C) d)
            = inner ℝ d (B (v i) + B (v j)) -
                inner ℝ d (C (v i) + C (v j)) := by
              simp [d, map_add, inner_sub_right,
                inner_add_right]
              ring
        _ = inner ℝ d (B d) - inner ℝ d (C d) := by
              simp [d, map_add]
        _ = 0 := by
              rw [hpair hi hj hij, sub_self]
  exact sub_eq_zero.mp hzero

end FiniteOrthonormalSpanningOn

end AleksandrovDifferentiability
