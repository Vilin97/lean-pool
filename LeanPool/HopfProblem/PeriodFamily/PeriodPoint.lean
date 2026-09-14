/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Toric.ToricSpace1
import all LeanPool.HopfProblem.Foundations.Core1
import all LeanPool.HopfProblem.Lattice.Core1
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.Toric.ToricSpace1

/-!
# Hopf problem: period family · period point

Supporting definitions and proofs for this stage of the six-sphere construction.
-/


open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

@[ext]
private structure PeriodPoint where
  τ : ℂ
  μ : ℂ
  β : ℂ

private def PeriodPoint.discriminant (p : PeriodPoint) : ℝ :=
  p.β.im - 6 * p.μ.im ^ 2 / p.τ.im

private def PeriodPoint.Admissible (p : PeriodPoint) : Prop :=
  0 < p.τ.im ∧ p.discriminant < 0

private def PeriodPoint.matrix (p : PeriodPoint) : Matrix (Fin 2) (Fin 4) ℂ :=
  !![6 * p.μ, p.τ, 1, 0; p.β, p.μ, 0, 1]

private def PeriodPoint.realMatrix (p : PeriodPoint) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![6 * p.μ.re, p.τ.re, 1, 0;
    6 * p.μ.im, p.τ.im, 0, 0;
    p.β.re, p.μ.re, 0, 1;
    p.β.im, p.μ.im, 0, 0]

private def PeriodPoint.step₁ (p : PeriodPoint) : PeriodPoint :=
  ⟨(p.τ - 1) / p.τ, (1 - p.μ) / p.τ, p.β + 2 - 6 * (1 - p.μ) ^ 2 / p.τ⟩

private def PeriodPoint.step₂ (p : PeriodPoint) : PeriodPoint :=
  ⟨-1 / p.τ, 1 + p.μ / p.τ, p.β - 3 - 6 * p.μ ^ 2 / p.τ⟩

private def PeriodPoint.R₁ (p : PeriodPoint) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-1 / p.τ, 0; (1 - p.μ) / p.τ, 1]

private def PeriodPoint.R₂ (p : PeriodPoint) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1 / p.τ, 0; -p.μ / p.τ, 1]

private theorem PeriodPoint.τ_ne_zero (p : PeriodPoint) (h : 0 < p.τ.im) : p.τ ≠ 0 := by
  intro heq
  simp [heq] at h

private theorem PeriodPoint.det_realMatrix (p : PeriodPoint) :
    p.realMatrix.det = p.τ.im * p.β.im - 6 * p.μ.im ^ 2 := by
  have hminor :
    p.realMatrix.submatrix (Fin.succAbove (0 : Fin 4)) (Fin.succAbove (2 : Fin 4)) =
      !![6 * p.μ.im, p.τ.im, 0; p.β.re, p.μ.re, 1; p.β.im, p.μ.im, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_column _ 2, Fin.sum_univ_four, hminor]
  norm_num [realMatrix, Matrix.det_fin_three, Matrix.cons_val_two, Matrix.cons_val_three]
  ring

private theorem PeriodPoint.det_realMatrix_eq_discriminant (p : PeriodPoint) (h : p.τ.im ≠ 0) :
    p.realMatrix.det = p.τ.im * p.discriminant := by
  rw [det_realMatrix]
  unfold discriminant
  field_simp

private theorem PeriodPoint.det_realMatrix_neg (p : PeriodPoint) (h : p.Admissible) :
    p.realMatrix.det < 0 := by
  rw [det_realMatrix_eq_discriminant p (ne_of_gt h.1)]
  exact mul_neg_of_pos_of_neg h.1 h.2

private theorem PeriodPoint.det_R₁ (p : PeriodPoint) : p.R₁.det = -1 / p.τ := by
  simp [R₁, Matrix.det_fin_two]

private theorem PeriodPoint.det_R₂ (p : PeriodPoint) : p.R₂.det = 1 / p.τ := by
  simp [R₂, Matrix.det_fin_two]

private theorem PeriodPoint.step₁_matrix (p : PeriodPoint) (h : p.τ ≠ 0) :
    p.step₁.matrix = p.R₁ * p.matrix * (T₁.map (Int.castRingHom ℂ)).transpose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
        simp [step₁, PeriodPoint.matrix, R₁, T₁, Matrix.mul_apply, Fin.sum_univ_succ] <;>
      field_simp <;>
    ring

private theorem PeriodPoint.step₂_matrix (p : PeriodPoint) (h : p.τ ≠ 0) :
    p.step₂.matrix = p.R₂ * p.matrix * (T₂.map (Int.castRingHom ℂ)).transpose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
        simp [step₂, PeriodPoint.matrix, R₂, T₂, Matrix.mul_apply, Fin.sum_univ_succ] <;>
      field_simp <;>
    ring

private theorem PeriodPoint.step₂_discriminant (p : PeriodPoint) (h : p.τ.im ≠ 0) :
    p.step₂.discriminant = p.discriminant := by
  have hτ : p.τ ≠ 0 := by
    intro heq
    exact h (by simp [heq])
  have hn : Complex.normSq p.τ ≠ 0 := mt Complex.normSq_eq_zero.mp hτ
  simp [step₂, discriminant, Complex.div_im, Complex.mul_im, Complex.mul_re, pow_two]
  field_simp
  simp [Complex.normSq_apply]
  ring

private theorem PeriodPoint.step₁_discriminant (p : PeriodPoint) (h : p.τ.im ≠ 0) :
    p.step₁.discriminant = p.discriminant := by
  have hτ : p.τ ≠ 0 := by
    intro heq
    exact h (by simp [heq])
  have hs := step₂_discriminant ⟨p.τ, 1 - p.μ, p.β⟩ h
  simpa [step₁, step₂, discriminant, sub_div, hτ, Complex.div_im, neg_div] using hs

private theorem PeriodPoint.step₁_im (p : PeriodPoint) (h : p.τ ≠ 0) :
    p.step₁.τ.im = p.τ.im / Complex.normSq p.τ := by simp [step₁, sub_div, h, neg_div]

private theorem
    PeriodPoint.step₂_im (p : PeriodPoint) : p.step₂.τ.im = p.τ.im / Complex.normSq p.τ := by
  simp [step₂, neg_div]

private theorem
    PeriodPoint.step₁_admissible (p : PeriodPoint) (h : p.Admissible) : p.step₁.Admissible := by
  refine ⟨?_, ?_⟩
  · rw [step₁_im p (p.τ_ne_zero h.1)]
    exact div_pos h.1 (Complex.normSq_pos.mpr (p.τ_ne_zero h.1))
  · rw [step₁_discriminant p (ne_of_gt h.1)]
    exact h.2

private theorem
    PeriodPoint.step₂_admissible (p : PeriodPoint) (h : p.Admissible) : p.step₂.Admissible := by
  refine ⟨?_, ?_⟩
  · rw [step₂_im]
    exact div_pos h.1 (Complex.normSq_pos.mpr (p.τ_ne_zero h.1))
  · rw [step₂_discriminant p (ne_of_gt h.1)]
    exact h.2

private theorem PeriodPoint.step₁_sq (p : PeriodPoint) (h₀ : p.τ ≠ 0) (h₁ : p.τ - 1 ≠ 0) :
    p.step₁.step₁ =
      ⟨-1 / (p.τ - 1), (p.τ - 1 + p.μ) / (p.τ - 1), p.β - 2 - 6 * p.μ ^ 2 / (p.τ - 1)⟩ := by
  apply PeriodPoint.ext <;> simp [step₁] <;> field_simp <;> ring

private theorem PeriodPoint.step₂_sq (p : PeriodPoint) (h : p.τ ≠ 0) :
    p.step₂.step₂ = ⟨p.τ, 1 - p.τ - p.μ, p.β - 6 + 6 * p.τ + 12 * p.μ⟩ := by
  apply PeriodPoint.ext <;> simp [step₂] <;> field_simp <;> ring

private theorem PeriodPoint.step₁_cube (p : PeriodPoint) (h₀ : p.τ ≠ 0) (h₁ : p.τ - 1 ≠ 0) :
    p.step₁.step₁.step₁ = p := by
  rw [step₁_sq p h₀ h₁]
  apply PeriodPoint.ext <;> simp [step₁] <;> field_simp <;> ring

private theorem PeriodPoint.step₂_fourth (p : PeriodPoint) (h : p.τ ≠ 0) :
    p.step₂.step₂.step₂.step₂ = p := by
  rw [step₂_sq (p.step₂.step₂), step₂_sq p h]
  · apply PeriodPoint.ext <;> simp
    all_goals ring
  · simpa [step₂] using h

private theorem PeriodPoint.step₁_step₂ (p : PeriodPoint) (h : p.τ ≠ 0) :
    p.step₂.step₁ = ⟨p.τ + 1, p.μ, p.β - 1⟩ := by
  apply PeriodPoint.ext <;> simp [step₁, step₂] <;> field_simp <;> ring

private abbrev PeriodDomain :=
  { p : PeriodPoint // p.Admissible }

private def PeriodDomain.realEquiv (p : PeriodDomain) : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ) :=
  Matrix.toLinearEquiv (Pi.basisFun ℝ (Fin 4)) p.val.realMatrix
    (isUnit_iff_ne_zero.mpr (ne_of_lt (p.val.det_realMatrix_neg p.property)))

private theorem PeriodDomain.realEquiv_apply (p : PeriodDomain) (v : Fin 4 → ℝ) :
    p.realEquiv v = p.val.realMatrix *ᵥ v := by
  simp [realEquiv, Matrix.toLin_eq_toLin', Matrix.toLin'_apply]

private def PeriodDomain.basis (p : PeriodDomain) : Module.Basis (Fin 4) ℝ ComplexPlane₂ :=
  (Pi.basisFun ℝ (Fin 4)).map (p.realEquiv.trans complexCoordinates)

private theorem PeriodDomain.basis_apply (p : PeriodDomain) (j : Fin 4) :
    p.basis j = fun i => p.val.matrix i j := by
  simp only [basis, Module.Basis.map_apply, LinearEquiv.trans_apply, realEquiv_apply,
    Pi.basisFun_apply, Matrix.mulVec_single_one]
  ext i : 1
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [complexCoordinates, PeriodPoint.realMatrix, PeriodPoint.matrix]

private def PeriodDomain.lattice (p : PeriodDomain) : Submodule ℤ ComplexPlane₂ :=
  Submodule.span ℤ (Set.range (fun j i => p.val.matrix i j))

private theorem PeriodDomain.lattice_eq_span_basis (p : PeriodDomain) :
    p.lattice = Submodule.span ℤ (Set.range p.basis) := by
  unfold lattice
  congr 2
  funext j
  exact (p.basis_apply j).symm

private instance PeriodDomain.lattice_discrete (p : PeriodDomain) : DiscreteTopology p.lattice := by
  rw [lattice_eq_span_basis]
  infer_instance

private instance PeriodDomain.lattice_isZLattice (p : PeriodDomain) : IsZLattice ℝ p.lattice := by
  constructor
  rw [lattice_eq_span_basis]
  exact ZSpan.span_top p.basis

private instance PeriodDomain.lattice_addSubgroup_discrete (p : PeriodDomain) :
    DiscreteTopology p.lattice.toAddSubgroup :=
  inferInstanceAs (DiscreteTopology p.lattice)

private instance PeriodDomain.lattice_isClosed (p : PeriodDomain) :
    IsClosed (p.lattice : Set ComplexPlane₂) := by
  change IsClosed (p.lattice.toAddSubgroup : Set ComplexPlane₂)
  exact AddSubgroup.isClosed_of_discrete (H := p.lattice.toAddSubgroup)

private abbrev PeriodDomain.Torus (p : PeriodDomain) :=
  ComplexPlane₂ ⧸ p.lattice

private instance PeriodDomain.torus_pathConnected (p : PeriodDomain) : PathConnectedSpace p.Torus :=
  p.lattice.mkQ_surjective.pathConnectedSpace p.lattice.continuous_mkQ

private instance PeriodDomain.torus_compact (p : PeriodDomain) : CompactSpace p.Torus := by
  let f := p.lattice.mkQ
  have hf : Continuous f := p.lattice.continuous_mkQ
  have hper : ∀ z w, w ∈ p.lattice → f (z + w) = f z := by
    intro z w hw
    have hw' : f w = 0 := (Submodule.Quotient.mk_eq_zero p.lattice).mpr hw
    rw [map_add, hw', add_zero]
  have hc := IsZLattice.isCompact_range_of_periodic p.lattice f hf hper
  have hs : Function.Surjective f := Submodule.Quotient.mk_surjective p.lattice
  exact ⟨by simpa only [Set.range_eq_univ.mpr hs] using hc⟩

/-- A full period matrix equipped with a nonvanishing determinant witness. -/
public
structure FullPeriodMatrix where
  /-- The complex matrix underlying a full period matrix. -/
  matrix : Matrix (Fin 2) (Fin 2) ℂ
  nondegenerate : Function.Bijective (matrix.map Complex.im).mulVecLin

private def
    FullPeriodMatrix.imaginaryEquiv (p : FullPeriodMatrix) : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ) :=
  LinearEquiv.ofBijective (p.matrix.map Complex.im).mulVecLin p.nondegenerate

private def FullPeriodMatrix.periodLinear (p : FullPeriodMatrix) : RealPair₂ →ₗ[ℝ] ComplexPlane₂
    where
  toFun x := fun i => (x.1 i : ℂ) + (p.matrix *ᵥ fun j => (x.2 j : ℂ)) i
  map_add' x
    y := by
    ext i
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Complex.ofReal_add, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two]
    ring
  map_smul' a
    x := by
    ext i
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    simp only [Complex.real_smul, RingHom.id_apply]
    ring

private theorem
    FullPeriodMatrix.periodLinear_re (p : FullPeriodMatrix) (x : RealPair₂) (i : Fin 2) :
    (p.periodLinear x i).re = x.1 i + ((p.matrix.map Complex.re) *ᵥ x.2) i := by
  simp [periodLinear, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.mul_re]

private theorem
    FullPeriodMatrix.periodLinear_im (p : FullPeriodMatrix) (x : RealPair₂) (i : Fin 2) :
    (p.periodLinear x i).im = p.imaginaryEquiv x.2 i := by
  simp [periodLinear, imaginaryEquiv, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.mul_im]

private theorem FullPeriodMatrix.periodLinear_bijective (p : FullPeriodMatrix) :
    Function.Bijective p.periodLinear := by
  constructor
  · intro x y hxy
    have him : p.imaginaryEquiv x.2 = p.imaginaryEquiv y.2 := by
      ext i
      simpa only [periodLinear_im] using congrArg Complex.im (congrFun hxy i)
    have hs : x.2 = y.2 := p.imaginaryEquiv.injective him
    apply Prod.ext _ hs
    ext i
    have he := congrArg Complex.re (congrFun hxy i)
    simpa only [periodLinear_re, hs, add_left_inj] using he
  · intro z
    let b := p.imaginaryEquiv.symm (fun i => (z i).im)
    let a := (fun i => (z i).re) - (p.matrix.map Complex.re) *ᵥ b
    refine ⟨(a, b), ?_⟩
    ext i
    apply Complex.ext
    · simp only [periodLinear_re, a, Pi.sub_apply, sub_add_cancel]
    · simpa only [periodLinear_im] using congrFun (p.imaginaryEquiv.apply_symm_apply _) i

private def FullPeriodMatrix.periodEquiv (p : FullPeriodMatrix) : RealPair₂ ≃ₗ[ℝ] ComplexPlane₂ :=
  LinearEquiv.ofBijective p.periodLinear p.periodLinear_bijective

private def FullPeriodMatrix.basis (p : FullPeriodMatrix) :
    Module.Basis (Fin 2 ⊕ Fin 2) ℝ ComplexPlane₂ :=
  ((Pi.basisFun ℝ (Fin 2)).prod (Pi.basisFun ℝ (Fin 2))).map p.periodEquiv

private theorem FullPeriodMatrix.basis_inl (p : FullPeriodMatrix) (j : Fin 2) :
    p.basis (Sum.inl j) = Pi.single j 1 := by
  ext i
  fin_cases i <;> fin_cases j <;>
    simp [basis, periodEquiv, periodLinear, Module.Basis.prod_apply, Pi.basisFun_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem FullPeriodMatrix.basis_inr (p : FullPeriodMatrix) (j : Fin 2) :
    p.basis (Sum.inr j) = fun i => p.matrix i j := by
  ext i
  fin_cases i <;> fin_cases j <;>
    simp [basis, periodEquiv, periodLinear, Module.Basis.prod_apply, Pi.basisFun_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private def FullPeriodMatrix.lattice (p : FullPeriodMatrix) : Submodule ℤ ComplexPlane₂ :=
  Submodule.span ℤ (Set.range p.basis)

private theorem FullPeriodMatrix.basis_integer_sum (p : FullPeriodMatrix) (c : Fin 2 ⊕ Fin 2 → ℤ) :
    ∑ j, c j • p.basis j =
      (fun i => (c (Sum.inl i) : ℂ)) + p.matrix *ᵥ (fun i => (c (Sum.inr i) : ℂ)) := by
  ext i
  fin_cases i <;>
    simp [Fintype.sum_sum_type, basis_inl, basis_inr, Fin.sum_univ_two, Pi.single_apply,
      zsmul_eq_mul, mul_comm]

private theorem FullPeriodMatrix.mem_lattice_iff (p : FullPeriodMatrix) (z : ComplexPlane₂) :
    z ∈ p.lattice ↔
      ∃ m n : Fin 2 → ℤ, z = (fun i => (m i : ℂ)) + p.matrix *ᵥ (fun i => (n i : ℂ)) := by
  rw [lattice, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨fun i => c (Sum.inl i), fun i => c (Sum.inr i), hc.symm.trans (p.basis_integer_sum c)⟩
  · rintro ⟨m, n, rfl⟩
    exact ⟨Sum.elim m n, p.basis_integer_sum (Sum.elim m n)⟩

private instance
    FullPeriodMatrix.lattice_discrete (p : FullPeriodMatrix) : DiscreteTopology p.lattice := by
  unfold lattice; infer_instance

private instance
    FullPeriodMatrix.lattice_isZLattice (p : FullPeriodMatrix) : IsZLattice ℝ p.lattice :=
  ⟨ZSpan.span_top p.basis⟩

private abbrev FullPeriodMatrix.Torus (p : FullPeriodMatrix) :=
  ComplexPlane₂ ⧸ p.lattice

private instance FullPeriodMatrix.torus_pathConnected (p : FullPeriodMatrix) :
    PathConnectedSpace p.Torus :=
  p.lattice.mkQ_surjective.pathConnectedSpace p.lattice.continuous_mkQ

private instance FullPeriodMatrix.torus_compact (p : FullPeriodMatrix) : CompactSpace p.Torus := by
  have hper : ∀ z w, w ∈ p.lattice → p.lattice.mkQ (z + w) = p.lattice.mkQ z := by
    intro z w hw
    have hw' : p.lattice.mkQ w = 0 := (Submodule.Quotient.mk_eq_zero p.lattice).mpr hw
    rw [map_add, hw', add_zero]
  have hc :=
    IsZLattice.isCompact_range_of_periodic p.lattice p.lattice.mkQ p.lattice.continuous_mkQ hper
  exact ⟨by simpa only [Set.range_eq_univ.mpr p.lattice.mkQ_surjective] using hc⟩

private def PeriodDomain.step₁ (p : PeriodDomain) : PeriodDomain :=
  ⟨p.val.step₁, p.val.step₁_admissible p.property⟩

private def PeriodDomain.step₂ (p : PeriodDomain) : PeriodDomain :=
  ⟨p.val.step₂, p.val.step₂_admissible p.property⟩

private def PeriodDomain.R₁Equiv (p : PeriodDomain) : ComplexPlane₂ ≃L[ℂ] ComplexPlane₂ :=
  (Matrix.toLinearEquiv (Pi.basisFun ℂ (Fin 2)) p.val.R₁
      (isUnit_iff_ne_zero.mpr
        (by
          rw [PeriodPoint.det_R₁]
          exact
            div_ne_zero (by norm_num) (p.val.τ_ne_zero p.property.1)))).toContinuousLinearEquiv

private def PeriodDomain.R₂Equiv (p : PeriodDomain) : ComplexPlane₂ ≃L[ℂ] ComplexPlane₂ :=
  (Matrix.toLinearEquiv (Pi.basisFun ℂ (Fin 2)) p.val.R₂
      (isUnit_iff_ne_zero.mpr
        (by
          rw [PeriodPoint.det_R₂]
          exact div_ne_zero one_ne_zero (p.val.τ_ne_zero p.property.1)))).toContinuousLinearEquiv

private theorem PeriodDomain.R₁Equiv_apply (p : PeriodDomain) (z : ComplexPlane₂) :
    p.R₁Equiv z = p.val.R₁ *ᵥ z := by simp [R₁Equiv, Matrix.toLin_eq_toLin', Matrix.toLin'_apply]

private theorem PeriodDomain.R₂Equiv_apply (p : PeriodDomain) (z : ComplexPlane₂) :
    p.R₂Equiv z = p.val.R₂ *ᵥ z := by simp [R₂Equiv, Matrix.toLin_eq_toLin', Matrix.toLin'_apply]

private theorem PeriodDomain.R₁Equiv_map_lattice (p : PeriodDomain) :
    p.lattice.map (p.R₁Equiv.toLinearEquiv.restrictScalars ℤ).toLinearMap = p.step₁.lattice := by
  have he :
    (p.R₁Equiv.toLinearEquiv.restrictScalars ℤ).toLinearMap =
      p.val.R₁.mulVecLin.restrictScalars ℤ := by exact LinearMap.ext fun z => R₁Equiv_apply p z
  change (columnLattice p.val.matrix).map _ = columnLattice p.val.step₁.matrix
  rw [he, map_columnLattice, p.val.step₁_matrix (p.val.τ_ne_zero p.property.1)]
  exact (columnLattice_mul_eq _ T₁.transpose A₁ (by decide)).symm

private theorem PeriodDomain.R₂Equiv_map_lattice (p : PeriodDomain) :
    p.lattice.map (p.R₂Equiv.toLinearEquiv.restrictScalars ℤ).toLinearMap = p.step₂.lattice := by
  have he :
    (p.R₂Equiv.toLinearEquiv.restrictScalars ℤ).toLinearMap =
      p.val.R₂.mulVecLin.restrictScalars ℤ := by exact LinearMap.ext fun z => R₂Equiv_apply p z
  change (columnLattice p.val.matrix).map _ = columnLattice p.val.step₂.matrix
  rw [he, map_columnLattice, p.val.step₂_matrix (p.val.τ_ne_zero p.property.1)]
  exact (columnLattice_mul_eq _ T₂.transpose A₂ (by decide)).symm

private def PeriodPoint.leftBlock (p : PeriodPoint) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![6 * p.μ, p.τ; p.β, p.μ]

private theorem PeriodPoint.leftBlock_apply (p : PeriodPoint) (i j : Fin 2) :
    p.leftBlock i j = p.matrix i (Fin.castAdd 2 j) := by fin_cases i <;> fin_cases j <;> rfl

private theorem PeriodPoint.matrix_rightBlock (p : PeriodPoint) (i j : Fin 2) :
    p.matrix i (Fin.natAdd 2 j) = (Pi.single j (1 : ℂ) : ComplexPlane₂) i := by
  fin_cases i <;> fin_cases j <;> simp [PeriodPoint.matrix]

private theorem PeriodDomain.fullPeriodLattice_eq (p : PeriodDomain) (q : FullPeriodMatrix)
    (h : q.matrix = p.val.leftBlock) : q.lattice = p.lattice := by
  have hrange : Set.range q.basis = Set.range (fun j i => p.val.matrix i j) := by
    ext z
    constructor
    · rintro ⟨j, rfl⟩
      cases j with
      | inl j =>
        refine ⟨Fin.natAdd 2 j, ?_⟩
        ext i
        rw [q.basis_inl]
        exact p.val.matrix_rightBlock i j
      | inr j =>
        refine ⟨Fin.castAdd 2 j, ?_⟩
        ext i
        rw [q.basis_inr, h]
        exact (p.val.leftBlock_apply i j).symm
    · rintro ⟨j, rfl⟩
      fin_cases j
      · refine ⟨Sum.inr 0, ?_⟩
        rw [q.basis_inr, h]
        ext i
        exact p.val.leftBlock_apply i 0
      · refine ⟨Sum.inr 1, ?_⟩
        rw [q.basis_inr, h]
        ext i
        exact p.val.leftBlock_apply i 1
      · refine ⟨Sum.inl 0, ?_⟩
        rw [q.basis_inl]
        ext i
        exact (p.val.matrix_rightBlock i 0).symm
      · refine ⟨Sum.inl 1, ?_⟩
        rw [q.basis_inl]
        ext i
        exact (p.val.matrix_rightBlock i 1).symm
  exact congrArg (Submodule.span ℤ) hrange

private structure HolomorphicPeriodMap (V B : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] where
  point : B → PeriodDomain
  holomorphic_tau :
    ContMDiff (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ ℂ) ω (fun b => (point b).val.τ)
  holomorphic_mu :
    ContMDiff (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ ℂ) ω (fun b => (point b).val.μ)
  holomorphic_beta :
    ContMDiff (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ ℂ) ω (fun b => (point b).val.β)

private def HolomorphicPeriodMap.periodEquiv {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B) (b : B) :
    RealPlane₄ ≃ₗ[ℝ] ComplexPlane₂ :=
  (P.point b).realEquiv.trans complexCoordinates

private theorem HolomorphicPeriodMap.periodEquiv_apply {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B)
    (b : B) (v : RealPlane₄) :
    P.periodEquiv b v = complexCoordinates ((P.point b).val.realMatrix *ᵥ v) := by
  simp only [periodEquiv, LinearEquiv.trans_apply, PeriodDomain.realEquiv_apply]

private theorem HolomorphicPeriodMap.periodEquiv_symm_apply {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B)
    (b : B) (z : ComplexPlane₂) :
    (P.periodEquiv b).symm z = (P.point b).val.realMatrix⁻¹ *ᵥ complexCoordinates.symm z := by
  simp [periodEquiv, PeriodDomain.realEquiv, Matrix.toLinearEquiv, Matrix.toLin_eq_toLin',
    Matrix.toLin'_apply]

private theorem HolomorphicPeriodMap.continuous_realMatrix {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B) :
    Continuous (fun b => (P.point b).val.realMatrix) := by
  have ht := P.holomorphic_tau.continuous
  have hm := P.holomorphic_mu.continuous
  have hb := P.holomorphic_beta.continuous
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [PeriodPoint.realMatrix] <;> fun_prop

private theorem HolomorphicPeriodMap.continuous_realMatrix_inv {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B) :
    Continuous (fun b => (P.point b).val.realMatrix⁻¹) := by
  apply continuous_iff_continuousAt.mpr
  intro b
  have hd : (P.point b).val.realMatrix.det ≠ 0 :=
    ne_of_lt ((P.point b).val.det_realMatrix_neg (P.point b).property)
  have hinv : ContinuousAt (fun A : Matrix (Fin 4) (Fin 4) ℝ => A⁻¹) (P.point b).val.realMatrix :=
    by
    apply continuousAt_matrix_inv
    simpa only [Ring.inverse_eq_inv'] using ContinuousInv₀.continuousAt_inv₀ hd
  exact
    hinv.comp (f := fun b : B => (P.point b).val.realMatrix)
      (P.continuous_realMatrix.continuousAt (x := b))

private theorem HolomorphicPeriodMap.continuous_periodEquiv {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B) :
    Continuous (fun x : B × RealPlane₄ => P.periodEquiv x.1 x.2) := by
  simp_rw [periodEquiv_apply]
  exact
    complexCoordinates.toContinuousLinearEquiv.continuous.comp
      ((P.continuous_realMatrix.comp continuous_fst).matrix_mulVec continuous_snd)

private theorem
    HolomorphicPeriodMap.continuous_periodEquiv_symm {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B) :
    Continuous (fun x : B × ComplexPlane₂ => (P.periodEquiv x.1).symm x.2) := by
  simp_rw [periodEquiv_symm_apply]
  exact
    (P.continuous_realMatrix_inv.comp continuous_fst).matrix_mulVec
      (complexCoordinates.symm.toContinuousLinearEquiv.continuous.comp continuous_snd)

private def
    HolomorphicPeriodMap.realTrivialization {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B) :
    (B × ComplexPlane₂) ≃ₜ (B × RealPlane₄)
    where
  toFun x := (x.1, (P.periodEquiv x.1).symm x.2)
  invFun x := (x.1, P.periodEquiv x.1 x.2)
  left_inv x := by simp
  right_inv x := by simp
  continuous_toFun := continuous_fst.prodMk P.continuous_periodEquiv_symm
  continuous_invFun := continuous_fst.prodMk P.continuous_periodEquiv

end Mathoverflow1973

end
