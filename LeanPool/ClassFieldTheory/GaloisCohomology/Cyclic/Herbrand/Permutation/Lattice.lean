/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.LinearAlgebra.Matrix.Gershgorin
/-!
# Permutation-stable sublattices

This file proves the permutation-stable sublattice lemma.  The proof
also handles a
permutation basis with more than one orbit: approximate every large coordinate
vector by a lattice point and average all these approximations equivariantly
over the finite group.
-/

noncomputable section

namespace CyclicCohomology

open Module Submodule
open scoped BigOperators

universe uG uι

variable {G : Type uG} {ι : Type uι}

/-- The linear coordinate permutation attached to a permutation of the
indexing type. -/
def coordinatePermutation (σ : Equiv.Perm ι) :
    (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ) where
  toFun x i := x (σ.symm i)
  invFun x i := x (σ i)
  left_inv x := by
    funext i
    simp
  right_inv x := by
    funext i
    simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem coordinatePermutation_apply
    (σ : Equiv.Perm ι) (x : ι → ℝ) (i : ι) :
    coordinatePermutation σ x i = x (σ.symm i) :=
  rfl

@[simp]
theorem coordinatePermutation_refl :
    coordinatePermutation (Equiv.refl ι) =
      LinearEquiv.refl ℝ (ι → ℝ) := by
  ext x i
  rfl

theorem coordinatePermutation_mul
    (σ τ : Equiv.Perm ι) :
    coordinatePermutation (σ * τ) =
      (coordinatePermutation τ).trans
        (coordinatePermutation σ) := by
  ext x i
  rfl

@[simp]
theorem coordinatePermutation_inv
    (σ : Equiv.Perm ι) :
    coordinatePermutation σ⁻¹ =
      (coordinatePermutation σ).symm := by
  rw [show σ⁻¹ = σ.symm from rfl]
  ext x i
  rfl

@[simp]
theorem coordinatePermutation_single
    [DecidableEq ι] (σ : Equiv.Perm ι) (i : ι) :
    coordinatePermutation σ (Pi.single i (1 : ℝ)) =
      Pi.single (σ i) 1 := by
  ext j
  by_cases h : j = σ i
  · subst j
    simp
  · have h' : σ.symm j ≠ i := by
      intro hij
      apply h
      simpa using congrArg σ hij
    simp [coordinatePermutation_apply, h, h']

section Approximation

variable [Fintype ι]

/-- A canonical lattice point whose difference from `x` lies in the
fundamental parallelepiped of a chosen lattice basis. -/
def latticeApproximation
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L] (x : ι → ℝ) : L := by
  let b : Basis ι ℤ L := IsZLattice.basis L
  let bℝ : Basis ι ℝ (ι → ℝ) := b.ofZLatticeBasis ℝ L
  refine ⟨ZSpan.floor bℝ x, ?_⟩
  let z : ι → ℝ := (ZSpan.floor bℝ x).1
  change z ∈ L
  rw [← b.ofZLatticeBasis_span ℝ]
  exact (ZSpan.floor bℝ x).property

/-- A uniform approximation radius for the canonical lattice
approximation. -/
def latticeApproximationRadius
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L] : ℝ :=
  let b : Basis ι ℤ L := IsZLattice.basis L
  let bℝ : Basis ι ℝ (ι → ℝ) := b.ofZLatticeBasis ℝ L
  ∑ i, ‖bℝ i‖

theorem latticeApproximationRadius_nonneg
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L] :
    0 ≤ latticeApproximationRadius L := by
  unfold latticeApproximationRadius
  exact Finset.sum_nonneg fun _ _ ↦ norm_nonneg _

theorem norm_sub_latticeApproximation_le
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L] (x : ι → ℝ) :
    ‖x - (latticeApproximation L x : ι → ℝ)‖ ≤
      latticeApproximationRadius L := by
  let b : Basis ι ℤ L := IsZLattice.basis L
  let bℝ : Basis ι ℝ (ι → ℝ) := b.ofZLatticeBasis ℝ L
  simpa only [latticeApproximation, latticeApproximationRadius,
    ZSpan.fract] using ZSpan.norm_fract_le bℝ x

theorem abs_latticeApproximation_sub_apply_le
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L] (x : ι → ℝ) (i : ι) :
    |(latticeApproximation L x : ι → ℝ) i - x i| ≤
      latticeApproximationRadius L := by
  have hcoord :
      ‖(x - (latticeApproximation L x : ι → ℝ)) i‖ ≤
        ‖x - (latticeApproximation L x : ι → ℝ)‖ :=
    norm_le_pi_norm (x - (latticeApproximation L x : ι → ℝ)) i
  rw [Pi.sub_apply, Real.norm_eq_abs, abs_sub_comm] at hcoord
  exact hcoord.trans (norm_sub_latticeApproximation_le L x)

end Approximation

section Averaging

variable [Fintype G] [Group G] [Fintype ι] [DecidableEq ι]

/-- The action of `g` on the coordinate space for a permutation
representation `ρ`. -/
def permutationRepresentation
    (ρ : G →* Equiv.Perm ι) (g : G) :
    (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ) :=
  coordinatePermutation (ρ g)

omit [Fintype G] [Fintype ι] [DecidableEq ι] in
@[simp]
theorem permutationRepresentation_one
    (ρ : G →* Equiv.Perm ι) :
    permutationRepresentation ρ 1 =
      LinearEquiv.refl ℝ (ι → ℝ) := by
  change coordinatePermutation (ρ 1) =
    LinearEquiv.refl ℝ (ι → ℝ)
  rw [map_one]
  exact coordinatePermutation_refl

omit [Fintype G] [Fintype ι] [DecidableEq ι] in
theorem permutationRepresentation_mul
    (ρ : G →* Equiv.Perm ι) (g h : G) :
    permutationRepresentation ρ (g * h) =
      (permutationRepresentation ρ h).trans
        (permutationRepresentation ρ g) := by
  simp only [permutationRepresentation, map_mul]
  exact coordinatePermutation_mul _ _

/-- Restrict a permutation representation to an invariant lattice. -/
def permutationLatticeEquiv
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ))
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L)
    (g : G) : L ≃ₗ[ℤ] L where
  toFun x :=
    ⟨permutationRepresentation ρ g x.1, hL g x.1 x.2⟩
  invFun x :=
    ⟨permutationRepresentation ρ g⁻¹ x.1,
      hL g⁻¹ x.1 x.2⟩
  left_inv x := by
    apply Subtype.ext
    change coordinatePermutation (ρ g⁻¹)
      (coordinatePermutation (ρ g) x.1) = x.1
    rw [map_inv,
      coordinatePermutation_inv]
    exact (coordinatePermutation (ρ g)).symm_apply_apply x.1
  right_inv x := by
    apply Subtype.ext
    change coordinatePermutation (ρ g)
      (coordinatePermutation (ρ g⁻¹) x.1) = x.1
    rw [map_inv,
      coordinatePermutation_inv]
    exact (coordinatePermutation (ρ g)).apply_symm_apply x.1
  map_add' x y := by
    apply Subtype.ext
    exact map_add _ _ _
  map_smul' n x := by
    apply Subtype.ext
    exact map_zsmul _ _ _

omit [Fintype G] [Fintype ι] [DecidableEq ι] in
@[simp]
theorem coe_permutationLatticeEquiv
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ))
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L)
    (g : G) (x : L) :
    ((permutationLatticeEquiv ρ L hL g x : L) : ι → ℝ) =
      permutationRepresentation ρ g x :=
  rfl

/-- The equivariant average of lattice approximations to the large
coordinate vectors. -/
def averagedLatticeVector
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L)
    (t : ℝ) (i : ι) : L :=
  ∑ g : G,
    permutationLatticeEquiv ρ L hL g
      (latticeApproximation L
        (t • Pi.single ((ρ g).symm i) (1 : ℝ)))

/-- A scale large enough to make the averaged lattice vectors strictly
column diagonally dominant. -/
def permutationLatticeScale
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L] : ℝ :=
  ((Fintype.card ι : ℝ) + 1) *
      latticeApproximationRadius L + 1

omit [DecidableEq ι] in
theorem permutationLatticeScale_pos
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L] :
    0 < permutationLatticeScale L := by
  have hB := latticeApproximationRadius_nonneg L
  have hs : 0 ≤ (Fintype.card ι : ℝ) := by positivity
  unfold permutationLatticeScale
  nlinarith

@[simp]
theorem averagedLatticeVector_apply
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L)
    (t : ℝ) (i j : ι) :
    (averagedLatticeVector ρ L hL t i : ι → ℝ) j =
      ∑ g : G,
        (latticeApproximation L
          (t • Pi.single ((ρ g).symm i) (1 : ℝ)) :
            ι → ℝ) ((ρ g).symm j) := by
  simp [averagedLatticeVector, permutationRepresentation]

omit [Fintype G] in
theorem averagingSummand_diagonal_bound
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L] (t : ℝ) (g : G) (i : ι) :
    |(latticeApproximation L
          (t • Pi.single ((ρ g).symm i) (1 : ℝ)) :
        ι → ℝ) ((ρ g).symm i) - t| ≤
      latticeApproximationRadius L := by
  have h :=
    abs_latticeApproximation_sub_apply_le L
      (t • Pi.single ((ρ g).symm i) (1 : ℝ))
      ((ρ g).symm i)
  simpa using h

omit [Fintype G] in
theorem averagingSummand_offDiagonal_bound
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L] (t : ℝ) (g : G) {i j : ι}
    (hji : j ≠ i) :
    |(latticeApproximation L
          (t • Pi.single ((ρ g).symm i) (1 : ℝ)) :
        ι → ℝ) ((ρ g).symm j)| ≤
      latticeApproximationRadius L := by
  have h :=
    abs_latticeApproximation_sub_apply_le L
      (t • Pi.single ((ρ g).symm i) (1 : ℝ))
      ((ρ g).symm j)
  have hne : (ρ g).symm j ≠ (ρ g).symm i :=
    (ρ g).symm.injective.ne hji
  simpa [hne] using h

theorem averagedLatticeVector_diagonal_bound
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L)
    (t : ℝ) (i : ι) :
    |(averagedLatticeVector ρ L hL t i : ι → ℝ) i -
        (Fintype.card G : ℝ) * t| ≤
      (Fintype.card G : ℝ) *
        latticeApproximationRadius L := by
  rw [averagedLatticeVector_apply]
  let a : G → ℝ := fun g ↦
    (latticeApproximation L
      (t • Pi.single ((ρ g).symm i) (1 : ℝ)) :
        ι → ℝ) ((ρ g).symm i)
  change |(∑ g : G, a g) -
    (Fintype.card G : ℝ) * t| ≤
      (Fintype.card G : ℝ) *
        latticeApproximationRadius L
  have ha (g : G) :
      |a g - t| ≤ latticeApproximationRadius L := by
    simpa only [a] using
      averagingSummand_diagonal_bound ρ L t g i
  have heq :
      (∑ g : G, a g) -
          (Fintype.card G : ℝ) * t =
        ∑ g : G, (a g - t) := by
    rw [Finset.sum_sub_distrib]
    simp
  rw [heq]
  calc
    |∑ g : G, (a g - t)| ≤
        ∑ g : G, |a g - t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _g : G, latticeApproximationRadius L :=
      Finset.sum_le_sum fun g _ ↦ ha g
    _ = (Fintype.card G : ℝ) *
        latticeApproximationRadius L := by simp

theorem averagedLatticeVector_offDiagonal_bound
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L)
    (t : ℝ) {i j : ι} (hji : j ≠ i) :
    |(averagedLatticeVector ρ L hL t i : ι → ℝ) j| ≤
      (Fintype.card G : ℝ) *
        latticeApproximationRadius L := by
  rw [averagedLatticeVector_apply]
  let a : G → ℝ := fun g ↦
    (latticeApproximation L
      (t • Pi.single ((ρ g).symm i) (1 : ℝ)) :
        ι → ℝ) ((ρ g).symm j)
  change |∑ g : G, a g| ≤
    (Fintype.card G : ℝ) *
      latticeApproximationRadius L
  have ha (g : G) :
      |a g| ≤ latticeApproximationRadius L := by
    simpa only [a] using
      averagingSummand_offDiagonal_bound
        ρ L t g hji
  calc
    |∑ g : G, a g| ≤ ∑ g : G, |a g| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _g : G, latticeApproximationRadius L :=
      Finset.sum_le_sum fun g _ ↦ ha g
    _ = (Fintype.card G : ℝ) *
        latticeApproximationRadius L := by simp

/-- The coordinate matrix whose columns are the averaged lattice
vectors. -/
def averagedLatticeMatrix
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L)
    (t : ℝ) : Matrix ι ι ℝ :=
  fun row column ↦
    (averagedLatticeVector ρ L hL t column :
      ι → ℝ) row

theorem averagedLatticeMatrix_sum_col_lt_diag
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    ∀ k : ι,
      ∑ j ∈ Finset.univ.erase k,
          ‖averagedLatticeMatrix ρ L hL
            (permutationLatticeScale L) j k‖ <
        ‖averagedLatticeMatrix ρ L hL
            (permutationLatticeScale L) k k‖ := by
  intro k
  let B : ℝ := latticeApproximationRadius L
  let n : ℝ := Fintype.card G
  let s : ℝ := Fintype.card ι
  let t : ℝ := permutationLatticeScale L
  let E : ℝ := n * B
  have hB : 0 ≤ B :=
    latticeApproximationRadius_nonneg L
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card G)
  have hs : 0 ≤ s := by positivity
  have hE : 0 ≤ E := mul_nonneg hn.le hB
  have hoff (j : ι) (hjk : j ≠ k) :
      ‖averagedLatticeMatrix ρ L hL t j k‖ ≤ E := by
    change
      |(averagedLatticeVector ρ L hL t k :
        ι → ℝ) j| ≤ E
    exact averagedLatticeVector_offDiagonal_bound
      ρ L hL t hjk
  have hsum :
      ∑ j ∈ Finset.univ.erase k,
          ‖averagedLatticeMatrix ρ L hL t j k‖ ≤
        s * E := by
    calc
      ∑ j ∈ Finset.univ.erase k,
          ‖averagedLatticeMatrix ρ L hL t j k‖ ≤
          ∑ _j ∈ Finset.univ.erase k, E :=
        Finset.sum_le_sum fun j hj ↦
          hoff j (Finset.ne_of_mem_erase hj)
      _ ≤ ∑ _j : ι, E :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.erase_subset k Finset.univ)
          (fun _ _ _ ↦ hE)
      _ = s * E := by simp [s]
  have hdiag :
      |(averagedLatticeMatrix ρ L hL t k k) -
          n * t| ≤ E := by
    exact averagedLatticeVector_diagonal_bound
      ρ L hL t k
  have hdiagLower :
      n * t - E ≤
        |averagedLatticeMatrix ρ L hL t k k| := by
    have hleft := (abs_le.mp hdiag).1
    have hself :
        averagedLatticeMatrix ρ L hL t k k ≤
          |averagedLatticeMatrix ρ L hL t k k| :=
      le_abs_self _
    nlinarith
  have hnumeric : s * E < n * t - E := by
    dsimp only [E, n, s, t, B]
    unfold permutationLatticeScale
    nlinarith
  calc
    ∑ j ∈ Finset.univ.erase k,
        ‖averagedLatticeMatrix ρ L hL
          (permutationLatticeScale L) j k‖ =
        ∑ j ∈ Finset.univ.erase k,
          ‖averagedLatticeMatrix ρ L hL t j k‖ := by rfl
    _ ≤ s * E := hsum
    _ < n * t - E := hnumeric
    _ ≤ |averagedLatticeMatrix ρ L hL t k k| :=
      hdiagLower
    _ = ‖averagedLatticeMatrix ρ L hL
        (permutationLatticeScale L) k k‖ := by
      rfl

theorem averagedLatticeMatrix_det_ne_zero
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    (averagedLatticeMatrix ρ L hL
      (permutationLatticeScale L)).det ≠ 0 :=
  det_ne_zero_of_sum_col_lt_diag
    (averagedLatticeMatrix_sum_col_lt_diag ρ L hL)

theorem averagedLatticeVector_linearIndependent
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    LinearIndependent ℝ
      (fun i ↦
        (averagedLatticeVector ρ L hL
          (permutationLatticeScale L) i :
            ι → ℝ)) := by
  have hcols :=
    Matrix.linearIndependent_cols_of_det_ne_zero
      (averagedLatticeMatrix_det_ne_zero ρ L hL)
  change LinearIndependent ℝ
    (fun i j ↦
      averagedLatticeMatrix ρ L hL
        (permutationLatticeScale L) j i) at hcols
  simpa only [averagedLatticeMatrix] using hcols

theorem averagedLatticeVector_equivariant
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L)
    (t : ℝ) (g : G) (i : ι) :
    permutationLatticeEquiv ρ L hL g
        (averagedLatticeVector ρ L hL t i) =
      averagedLatticeVector ρ L hL t (ρ g i) := by
  classical
  apply Subtype.ext
  ext j
  simp only [coe_permutationLatticeEquiv,
    permutationRepresentation, coordinatePermutation_apply,
    averagedLatticeVector_apply]
  let F : G → ℝ := fun h ↦
      (latticeApproximation L
        (t • Pi.single ((ρ h).symm i) (1 : ℝ)) :
          ι → ℝ) ((ρ h).symm ((ρ g).symm j))
  let H : G → ℝ := fun k ↦
      (latticeApproximation L
        (t • Pi.single ((ρ k).symm (ρ g i)) (1 : ℝ)) :
          ι → ℝ) ((ρ k).symm j)
  have hterm (h : G) : F h = H (g * h) := by
    dsimp only [F, H]
    have hindex :
        (ρ (g * h)).symm (ρ g i) = (ρ h).symm i := by
      rw [Equiv.symm_apply_eq]
      simp [map_mul]
    have hcoordinate :
        (ρ (g * h)).symm j =
          (ρ h).symm ((ρ g).symm j) := by
      rw [Equiv.symm_apply_eq]
      simp [map_mul]
    rw [hindex, hcoordinate]
  calc
    ∑ h : G, F h = ∑ h : G, H (g * h) := by
      exact Finset.sum_congr rfl fun h _ ↦ hterm h
    _ = ∑ k : G, H k := by
      exact Fintype.sum_bijective (g * ·)
        (Group.mulLeft_bijective g) (fun h ↦ H (g * h)) H
        fun _ ↦ rfl

/-- The complete sublattice generated by the equivariantly averaged
vectors. -/
def permutationSublattice
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    Submodule ℤ (ι → ℝ) :=
  Submodule.span ℤ
    (Set.range fun i ↦
      (averagedLatticeVector ρ L hL
        (permutationLatticeScale L) i : ι → ℝ))

theorem permutationSublattice_le
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    permutationSublattice ρ L hL ≤ L := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact (averagedLatticeVector ρ L hL
    (permutationLatticeScale L) i).property

instance permutationSublattice_discreteTopology
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    DiscreteTopology (permutationSublattice ρ L hL) := by
  let f : permutationSublattice ρ L hL → L :=
    fun x ↦ ⟨x.1, permutationSublattice_le ρ L hL x.2⟩
  refine DiscreteTopology.of_continuous_injective
    (f := f) ?_ ?_
  · exact Continuous.subtype_mk continuous_subtype_val _
  · intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : L ↦ (z : ι → ℝ)) hxy

theorem permutationSublattice_span_eq_top
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    Submodule.span ℝ
        (permutationSublattice ρ L hL :
          Set (ι → ℝ)) = ⊤ := by
  let w : ι → (ι → ℝ) := fun i ↦
    (averagedLatticeVector ρ L hL
      (permutationLatticeScale L) i : ι → ℝ)
  have hw :
      LinearIndependent ℝ w :=
    averagedLatticeVector_linearIndependent ρ L hL
  have hwspan :
      Submodule.span ℝ (Set.range w) = ⊤ :=
    hw.span_eq_top_of_card_eq_finrank'
      (Module.finrank_fintype_fun_eq_card ℝ).symm
  rw [eq_top_iff, ← hwspan]
  apply Submodule.span_mono (R := ℝ)
  rintro _ ⟨i, rfl⟩
  exact Submodule.subset_span ⟨i, rfl⟩

instance permutationSublattice_isZLattice
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    IsZLattice ℝ (permutationSublattice ρ L hL) where
  span_top := permutationSublattice_span_eq_top ρ L hL

/-- The distinguished basis of the permutation-stable sublattice. -/
def permutationSublatticeBasis
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    Basis ι ℤ (permutationSublattice ρ L hL) :=
  Basis.span
    ((averagedLatticeVector_linearIndependent ρ L hL).restrict_scalars' ℤ)

@[simp]
theorem permutationSublatticeBasis_apply_coe
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L)
    (i : ι) :
    ((permutationSublatticeBasis ρ L hL i :
        permutationSublattice ρ L hL) : ι → ℝ) =
      averagedLatticeVector ρ L hL
        (permutationLatticeScale L) i := by
  let hli :=
    (averagedLatticeVector_linearIndependent
      ρ L hL).restrict_scalars' ℤ
  change
    ((Basis.span hli i :
      permutationSublattice ρ L hL) : ι → ℝ) =
        (averagedLatticeVector ρ L hL
          (permutationLatticeScale L) i : ι → ℝ)
  exact Basis.coe_span_apply hli i

theorem permutationSublatticeBasis_permuted
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L)
    (g : G) (i : ι) :
    permutationRepresentation ρ g
        (permutationSublatticeBasis ρ L hL i :
          ι → ℝ) =
      (permutationSublatticeBasis ρ L hL (ρ g i) :
        ι → ℝ) := by
  have h :=
    congrArg (fun x : L ↦ (x : ι → ℝ))
      (averagedLatticeVector_equivariant
        ρ L hL (permutationLatticeScale L) g i)
  simpa only [coe_permutationLatticeEquiv,
    permutationSublatticeBasis_apply_coe] using h

omit [DecidableEq ι] [Fintype G] in
/-- An invariant complete lattice in a real
permutation representation contains a complete sublattice with a basis
permuted in exactly the prescribed way. -/
theorem exists_complete_permutationSublattice [Finite G]
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    ∃ L' : Submodule ℤ (ι → ℝ),
      L' ≤ L ∧
      DiscreteTopology L' ∧
      Submodule.span ℝ (L' : Set (ι → ℝ)) = ⊤ ∧
      ∃ b : Basis ι ℤ L',
        ∀ (g : G) (i : ι),
          permutationRepresentation ρ g
              (b i : ι → ℝ) =
            (b (ρ g i) : ι → ℝ) := by
  classical
  let : DecidableEq ι := Classical.decEq ι
  let := Fintype.ofFinite G
  refine ⟨permutationSublattice ρ L hL,
    permutationSublattice_le ρ L hL,
    inferInstance,
    permutationSublattice_span_eq_top ρ L hL,
    permutationSublatticeBasis ρ L hL, ?_⟩
  exact permutationSublatticeBasis_permuted ρ L hL

end Averaging

section GeneralPermutationBasis

variable [Fintype G] [Group G] [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [Fintype G] in
omit [DecidableEq ι] [Fintype ι] in
theorem basisEquivFunL_symm_coordinatePermutation [Finite ι]
    (b : Basis ι ℝ E)
    (ρ : G →* Equiv.Perm ι)
    (α : G →* (E ≃ₗ[ℝ] E))
    (hb : ∀ (g : G) (i : ι),
      α g (b i) = b (ρ g i))
    (g : G) (x : ι → ℝ) :
    b.equivFunL.symm
        (coordinatePermutation (ρ g) x) =
      α g (b.equivFunL.symm x) := by
  classical
  let : DecidableEq ι := Classical.decEq ι
  let := Fintype.ofFinite ι
  have hmaps :
      b.equivFunL.symm.toLinearMap.comp
          (coordinatePermutation (ρ g)).toLinearMap =
        (α g).toLinearMap.comp
          b.equivFunL.symm.toLinearMap := by
    apply (Pi.basisFun ℝ ι).ext
    intro i
    simp only [LinearMap.comp_apply, Pi.basisFun_apply]
    have hsingle (j : ι) :
        b.equivFunL.symm (Pi.single j 1) = b j := by
      exact _root_.Basis.equivFun_symm_single b j
    calc
      b.equivFunL.symm
          (coordinatePermutation (ρ g)
            (Pi.single i 1)) =
          b.equivFunL.symm
            (Pi.single (ρ g i) 1) :=
        congrArg b.equivFunL.symm
          (coordinatePermutation_single (ρ g) i)
      _ = b (ρ g i) := hsingle (ρ g i)
      _ = α g (b i) := (hb g i).symm
      _ = α g
          (b.equivFunL.symm (Pi.single i 1)) := by
        rw [hsingle i]
  exact LinearMap.congr_fun hmaps x

omit [DecidableEq ι] [Fintype G] [Fintype ι] in
/-- Invariant formulation: if a finite group acts on a
finite-dimensional real vector space by permuting a specified basis, every
invariant complete lattice contains a complete sublattice with a basis
permuted in the same way. -/
theorem exists_complete_permutationSublattice_of_basis [Finite G] [Finite ι]
    (b : Basis ι ℝ E)
    (ρ : G →* Equiv.Perm ι)
    (α : G →* (E ≃ₗ[ℝ] E))
    (hb : ∀ (g : G) (i : ι),
      α g (b i) = b (ρ g i))
    (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : E), x ∈ L →
      α g x ∈ L) :
    ∃ L' : Submodule ℤ E,
      L' ≤ L ∧
      DiscreteTopology L' ∧
      Submodule.span ℝ (L' : Set E) = ⊤ ∧
      ∃ b' : Basis ι ℤ L',
        ∀ (g : G) (i : ι),
          α g (b' i : E) =
            (b' (ρ g i) : E) := by
  classical
  let : DecidableEq ι := Classical.decEq ι
  let := Fintype.ofFinite G
  let := Fintype.ofFinite ι
  let e : E ≃L[ℝ] (ι → ℝ) := b.equivFunL
  let Lc : Submodule ℤ (ι → ℝ) :=
    ZLattice.comap ℝ L e.symm.toLinearMap
  let : DiscreteTopology Lc := by
    dsimp only [Lc]
    infer_instance
  let : IsZLattice ℝ Lc := by
    dsimp only [Lc]
    infer_instance
  have hLc :
      ∀ (g : G) (x : ι → ℝ), x ∈ Lc →
        permutationRepresentation ρ g x ∈ Lc := by
    intro g x hx
    change b.equivFunL.symm
      (coordinatePermutation (ρ g) x) ∈ L
    rw [basisEquivFunL_symm_coordinatePermutation
      b ρ α hb]
    apply hL g
    exact hx
  let Lc' : Submodule ℤ (ι → ℝ) :=
    permutationSublattice ρ Lc hLc
  let : DiscreteTopology Lc' := by
    dsimp only [Lc']
    infer_instance
  let : IsZLattice ℝ Lc' := by
    dsimp only [Lc']
    infer_instance
  let L' : Submodule ℤ E :=
    ZLattice.comap ℝ Lc' e.toLinearMap
  let : DiscreteTopology L' := by
    dsimp only [L']
    infer_instance
  let : IsZLattice ℝ L' := by
    dsimp only [L']
    infer_instance
  let bc : Basis ι ℤ Lc' :=
    permutationSublatticeBasis ρ Lc hLc
  let b' : Basis ι ℤ L' :=
    bc.ofZLatticeComap ℝ Lc' e.toLinearEquiv
  have hle : L' ≤ L := by
    intro x hx
    have hxc' : e x ∈ Lc' := hx
    have hxc : e x ∈ Lc :=
      permutationSublattice_le ρ Lc hLc hxc'
    change e.symm (e x) ∈ L at hxc
    simpa using hxc
  refine ⟨L', hle, inferInstance,
    IsZLattice.span_top, b', ?_⟩
  intro g i
  have hcoord :=
    permutationSublatticeBasis_permuted
      ρ Lc hLc g i
  have hintertwine :=
    basisEquivFunL_symm_coordinatePermutation
      b ρ α hb g (bc i : ι → ℝ)
  have hcoord' :
      coordinatePermutation (ρ g) (bc i : ι → ℝ) =
        (bc (ρ g i) : ι → ℝ) := by
    simpa only [permutationRepresentation, bc] using hcoord
  change
    α g (e.symm (bc i : ι → ℝ)) =
      e.symm (bc (ρ g i) : ι → ℝ)
  calc
    α g (e.symm (bc i : ι → ℝ)) =
        b.equivFunL.symm
          (coordinatePermutation (ρ g)
            (bc i : ι → ℝ)) := hintertwine.symm
    _ = b.equivFunL.symm
        (bc (ρ g i) : ι → ℝ) :=
      congrArg b.equivFunL.symm hcoord'
    _ = e.symm (bc (ρ g i) : ι → ℝ) := rfl

end GeneralPermutationBasis

section FiniteIndex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]

/-- Two complete integral lattices in the same real vector space are
commensurable: if one is contained in the other, its quotient in the
larger lattice is finite. -/
theorem finite_quotient_of_complete_sublattice
    (L L' : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L]
    [DiscreteTopology L'] [IsZLattice ℝ L']
    (hL' : L' ≤ L) :
    Finite (L ⧸ L'.comap L.subtype) := by
  let N : Submodule ℤ L := L'.comap L.subtype
  let e : N ≃ₗ[ℤ] L' :=
    Submodule.comapSubtypeEquivOfLe hL'
  let : Module.Finite ℤ L :=
    ZLattice.module_finite ℝ L
  have hrank : Module.finrank ℤ N =
      Module.finrank ℤ L := by
    calc
      Module.finrank ℤ N =
          Module.finrank ℤ L' :=
        LinearEquiv.finrank_eq e
      _ = Module.finrank ℝ E :=
        ZLattice.rank ℝ L'
      _ = Module.finrank ℤ L :=
        (ZLattice.rank ℝ L).symm
  exact
    Submodule.finiteQuotientOfFreeOfRankEq
      (L'.comap L.subtype) hrank

end FiniteIndex

section PermutationFiniteIndex

variable [Fintype G] [Group G] [Fintype ι] [DecidableEq ι]

/-- The canonical permutation sublattice has
finite index in the original complete invariant lattice. -/
theorem permutationSublattice_finite_quotient
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    Finite
      (L ⧸
        (permutationSublattice ρ L hL).comap
          L.subtype) :=
  finite_quotient_of_complete_sublattice
    L (permutationSublattice ρ L hL)
      (permutationSublattice_le ρ L hL)

end PermutationFiniteIndex

end CyclicCohomology
