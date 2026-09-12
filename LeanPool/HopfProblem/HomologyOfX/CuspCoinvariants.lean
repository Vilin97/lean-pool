/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Recognition.Degree1
import all LeanPool.HopfProblem.Foundations.Core1
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.Lattice.Core1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology2
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.Toric.ToricSpace1
import all LeanPool.HopfProblem.Uniformization.CuspUniformization1
import all LeanPool.HopfProblem.Foundations.Core3
import all LeanPool.HopfProblem.CuspFibre.CuspPositiveRetraction
import all LeanPool.HopfProblem.Lattice.Core2
import all LeanPool.HopfProblem.Threefold.SpecialPeriods1
import all LeanPool.HopfProblem.Pi1.MappingTorus
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology6
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology7
import all LeanPool.HopfProblem.CuspFibre.CuspSpecialization
import all LeanPool.HopfProblem.Recognition.Degree1

/-!
# Hopf problem: homology of x · cusp coinvariants

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

private def TrianglePeriodFamilyHomologyAlgebra.columnEquiv (H : Type*) [AddCommGroup H] :
    (H × (H × H)) ≃ₗ[ℤ] (H × (H × H)) :=
  ({    toFun := fun x => (x.1 + x.2.1 + x.2.2, x.2)
        invFun := fun x => (x.1 - x.2.1 - x.2.2, x.2)
        left_inv := by
          rintro ⟨a, b, c⟩
          apply Prod.ext
          · dsimp; abel
          · rfl
        right_inv := by
          rintro ⟨a, b, c⟩
          apply Prod.ext
          · dsimp; abel
          · rfl
        map_add' := by
          rintro ⟨a, b, c⟩ ⟨a', b', c'⟩
          apply Prod.ext
          · dsimp; abel
          · rfl } :
      (H × (H × H)) ≃+ (H × (H × H))).toIntLinearEquiv

@[simp]
private theorem
    TrianglePeriodFamilyHomologyAlgebra.columnEquiv_symm_apply (H : Type*) [AddCommGroup H]
    (x : H × (H × H)) : (columnEquiv H).symm x = (x.1 - x.2.1 - x.2.2, x.2) :=
  rfl

private def TrianglePeriodFamilyHomologyAlgebra.rowEquiv (H : Type*) [AddCommGroup H] :
    (H × H) ≃ₗ[ℤ] (H × H) :=
  ({    toFun := fun x => (x.1, -x.1 - x.2)
        invFun := fun x => (x.1, -x.1 - x.2)
        left_inv := by
          rintro ⟨a, b⟩
          apply Prod.ext
          · rfl
          · dsimp; abel
        right_inv := by
          rintro ⟨a, b⟩
          apply Prod.ext
          · rfl
          · dsimp; abel
        map_add' := by
          rintro ⟨a, b⟩ ⟨a', b'⟩
          apply Prod.ext
          · rfl
          · dsimp; abel } :
      (H × H) ≃+ (H × H)).toIntLinearEquiv

@[simp]
private theorem TrianglePeriodFamilyHomologyAlgebra.rowEquiv_apply (H : Type*) [AddCommGroup H]
    (x : H × H) : rowEquiv H x = (x.1, -x.1 - x.2) :=
  rfl

private def TrianglePeriodFamilyHomologyAlgebra.delta {H : Type*} [AddCommGroup H] [Module ℤ H]
    (P Q : H →ₗ[ℤ] H) : (H × H) →ₗ[ℤ] H :=
  PeriodTorusHigherHomology.intLinearMapOfAddHom
    { toFun x := (P x.1 - x.1) + (Q x.2 - x.2)
      map_zero' := by simp
      map_add' x
        y := by
        dsimp
        rw [map_add, map_add]
        abel }

@[simp]
private theorem
    TrianglePeriodFamilyHomologyAlgebra.delta_apply {H : Type*} [AddCommGroup H] [Module ℤ H]
    (P Q : H →ₗ[ℤ] H) (x : H × H) : delta P Q x = (P x.1 - x.1) + (Q x.2 - x.2) :=
  rfl

private def TrianglePeriodFamilyHomologyAlgebra.overlapMap {H : Type*} [AddCommGroup H] [Module ℤ H]
    (P Q : H →ₗ[ℤ] H) : (H × (H × H)) →ₗ[ℤ] (H × H) :=
  PeriodTorusHigherHomology.intLinearMapOfAddHom
    { toFun x := (x.1 + x.2.1 + x.2.2, -(x.1 + P x.2.1 + Q x.2.2))
      map_zero' := by simp
      map_add' x
        y := by
        apply Prod.ext
        · dsimp; abel
        · dsimp
          rw [map_add, map_add]
          abel }

@[simp]
private theorem TrianglePeriodFamilyHomologyAlgebra.overlapMap_apply {H : Type*} [AddCommGroup H]
    [Module ℤ H] (P Q : H →ₗ[ℤ] H) (x : H × (H × H)) :
    overlapMap P Q x = (x.1 + x.2.1 + x.2.2, -(x.1 + P x.2.1 + Q x.2.2)) :=
  rfl

private theorem TrianglePeriodFamilyHomologyAlgebra.row_overlapMap {H : Type*} [AddCommGroup H]
    [Module ℤ H] (P Q : H →ₗ[ℤ] H) (x : H × (H × H)) :
    rowEquiv H (overlapMap P Q x) = (x.1 + x.2.1 + x.2.2, delta P Q x.2) := by
  apply Prod.ext
  · rfl
  · change
      -(x.1 + x.2.1 + x.2.2) - -(x.1 + P x.2.1 + Q x.2.2) = (P x.2.1 - x.2.1) + (Q x.2.2 - x.2.2)
    abel

private theorem TrianglePeriodFamilyHomologyAlgebra.row_overlapMap_column_symm {H : Type*}
    [AddCommGroup H] [Module ℤ H] (P Q : H →ₗ[ℤ] H) (x : H × (H × H)) :
    rowEquiv H (overlapMap P Q ((columnEquiv H).symm x)) = (x.1, delta P Q x.2) := by
  rw [row_overlapMap, columnEquiv_symm_apply]
  apply Prod.ext
  · dsimp; abel
  · rfl

private theorem
    TrianglePeriodFamilyHomologyAlgebra.overlapMap_eq_zero_iff {H : Type*} [AddCommGroup H]
    [Module ℤ H] (P Q : H →ₗ[ℤ] H) (x : H × (H × H)) :
    overlapMap P Q x = 0 ↔ x.1 + x.2.1 + x.2.2 = 0 ∧ delta P Q x.2 = 0 := by
  constructor
  · intro h
    have hr := congrArg (rowEquiv H) h
    rw [row_overlapMap, map_zero] at hr
    exact ⟨congrArg Prod.fst hr, congrArg Prod.snd hr⟩
  · rintro ⟨hs, hd⟩
    apply (rowEquiv H).injective
    rw [row_overlapMap, map_zero]
    exact Prod.ext hs hd

private theorem
    TrianglePeriodFamilyHomologyAlgebra.overlapMap_mem_range_iff {H : Type*} [AddCommGroup H]
    [Module ℤ H] (P Q : H →ₗ[ℤ] H) (y : H × H) :
    y ∈ LinearMap.range (overlapMap P Q) ↔ -y.1 - y.2 ∈ LinearMap.range (delta P Q) := by
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨x.2, ?_⟩
    exact (congrArg Prod.snd (row_overlapMap P Q x)).symm
  · rintro ⟨bc, hbc⟩
    refine ⟨(columnEquiv H).symm (y.1, bc), ?_⟩
    apply (rowEquiv H).injective
    rw [row_overlapMap_column_symm, rowEquiv_apply, hbc]

private def TrianglePeriodFamilyHomologyLattice.deltaOne : (Lattice × Lattice) →ₗ[ℤ] Lattice :=
  TrianglePeriodFamilyHomologyAlgebra.delta A₁.mulVecLin A₂.mulVecLin

private def TrianglePeriodFamilyHomologyLattice.deltaThree : (Lattice × Lattice) →ₗ[ℤ] Lattice :=
  TrianglePeriodFamilyHomologyAlgebra.delta PeriodTorusHigherHomologyExterior.cubeA₁.mulVecLin
    PeriodTorusHigherHomologyExterior.cubeA₂.mulVecLin

private def TrianglePeriodFamilyHomologyLattice.functionalOdd : Lattice →ₗ[ℤ] ℤ :=
  LinearMap.proj 0

private theorem TrianglePeriodFamilyHomologyLattice.functionalOdd_surjective :
    Function.Surjective functionalOdd := by
  intro a
  exact ⟨![a, 0, 0, 0], rfl⟩

private theorem TrianglePeriodFamilyHomologyLattice.deltaOne_apply (b c : Lattice) :
    deltaOne (b, c) =
      ![0, 6 * b 0 - b 1 + b 2 - c 1 - c 2, -6 * b 0 - b 1 - 2 * b 2 - 6 * c 0 + c 1 - c 2,
        -2 * b 0 + b 1 + 3 * c 0 + c 2] := by
  change (A₁ *ᵥ b - b) + (A₂ *ᵥ c - c) = _
  ext i
  fin_cases i <;> simp [A₁, A₂, dotProduct, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail] <;>
    ring

private theorem TrianglePeriodFamilyHomologyLattice.deltaThree_apply (b c : Lattice) :
    deltaThree (b, c) =
      ![0, -b 0 - b 1 + b 2 - c 1 - c 2, b 0 - b 1 - 2 * b 2 + c 0 + c 1 - c 2,
        -2 * b 0 - 6 * b 1 + 3 * c 0 - 6 * c 2] := by
  change
    (PeriodTorusHigherHomologyExterior.cubeA₁ *ᵥ b - b) +
        (PeriodTorusHigherHomologyExterior.cubeA₂ *ᵥ c - c) =
      _
  rw [PeriodTorusHigherHomologyExterior.cubeA₁_eq, PeriodTorusHigherHomologyExterior.cubeA₂_eq]
  ext i
  fin_cases i <;> simp [dotProduct, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail] <;> ring

private def TrianglePeriodFamilyHomologyLattice.preimageOne (x : Lattice) : Lattice × Lattice :=
  (![0, x 3, -x 1 - x 2 - 2 * x 3, 0], ![0, -2 * x 1 - x 2 - 3 * x 3, 0, 0])

private def TrianglePeriodFamilyHomologyLattice.preimageThree (x : Lattice) : Lattice × Lattice :=
  (![x 3, 0, x 3 - x 1 - x 2, 0], ![x 3, -2 * x 1 - x 2, 0, 0])

private theorem TrianglePeriodFamilyHomologyLattice.deltaOne_preimage (x : Lattice) :
    deltaOne (preimageOne x) = ![0, x 1, x 2, x 3] := by
  rw [preimageOne, deltaOne_apply]
  ext i
  fin_cases i <;> simp <;> ring

private theorem TrianglePeriodFamilyHomologyLattice.deltaThree_preimage (x : Lattice) :
    deltaThree (preimageThree x) = ![0, x 1, x 2, x 3] := by
  rw [preimageThree, deltaThree_apply]
  ext i
  fin_cases i <;> simp <;> ring

private theorem TrianglePeriodFamilyHomologyLattice.deltaOne_range :
    LinearMap.range deltaOne = LinearMap.ker functionalOdd := by
  ext x
  constructor
  · rintro ⟨⟨b, c⟩, rfl⟩
    change functionalOdd (deltaOne (b, c)) = 0
    rw [deltaOne_apply]
    rfl
  · intro hx
    have hx0 : x 0 = 0 := hx
    refine ⟨preimageOne x, ?_⟩
    rw [deltaOne_preimage]
    ext i
    fin_cases i <;> simp [hx0]

private theorem TrianglePeriodFamilyHomologyLattice.deltaThree_range :
    LinearMap.range deltaThree = LinearMap.ker functionalOdd := by
  ext x
  constructor
  · rintro ⟨⟨b, c⟩, rfl⟩
    change functionalOdd (deltaThree (b, c)) = 0
    rw [deltaThree_apply]
    rfl
  · intro hx
    have hx0 : x 0 = 0 := hx
    refine ⟨preimageThree x, ?_⟩
    rw [deltaThree_preimage]
    ext i
    fin_cases i <;> simp [hx0]

private def TrianglePeriodFamilyHomologyLattice.cokernelOneEquiv :
    (Lattice ⧸ LinearMap.range deltaOne) ≃ₗ[ℤ] ℤ :=
  (Submodule.quotEquivOfEq _ _ deltaOne_range).trans
    (functionalOdd.quotKerEquivOfSurjective functionalOdd_surjective)

private def TrianglePeriodFamilyHomologyLattice.cokernelThreeEquiv :
    (Lattice ⧸ LinearMap.range deltaThree) ≃ₗ[ℤ] ℤ :=
  (Submodule.quotEquivOfEq _ _ deltaThree_range).trans
    (functionalOdd.quotKerEquivOfSurjective functionalOdd_surjective)

@[simp]
private theorem TrianglePeriodFamilyHomologyLattice.cokernelThreeEquiv_mk (x : Lattice) :
    cokernelThreeEquiv (Submodule.Quotient.mk x) = x 0 := by
  simp [cokernelThreeEquiv]
  rfl

private theorem ThreefoldHomology.SecondSource.kernel_coordinates (x y : Lattice)
    (h : TrianglePeriodFamilyHomologyLattice.deltaOne (x, y) = 0) :
    x 2 = -4 * x 0 ∧ y 1 = 3 * y 0 ∧ y 2 = 2 * x 0 - x 1 - 3 * y 0 := by
  rw [TrianglePeriodFamilyHomologyLattice.deltaOne_apply] at h
  have h₁ := congrFun h 1
  have h₂ := congrFun h 2
  have h₃ := congrFun h 3
  change 6 * x 0 - x 1 + x 2 - y 1 - y 2 = 0 at h₁
  change -6 * x 0 - x 1 - 2 * x 2 - 6 * y 0 + y 1 - y 2 = 0 at h₂
  change -2 * x 0 + x 1 + 3 * y 0 + y 2 = 0 at h₃
  omega

private def ThreefoldHomology.SecondSource.deltaVector : Lattice :=
  ![0, 0, 0, 1]

private def
    ThreefoldHomology.SecondSource.threeCoordinates (κ₃ κ₄ : ℤ) (x y : Lattice) : Fin 2 → ℤ :=
  ![x 3 + (x 1 - 2 * x 0) + (κ₄ * y 0 - y 3) + κ₃ * x 0, x 0]

private def ThreefoldHomology.SecondSource.fourCoordinates (y : Lattice) : Fin 2 → ℤ :=
  ![0, -y 0]

private def ThreefoldHomology.SecondSource.cuspCoordinates (κ₄ : ℤ) (x y : Lattice) : Lattice :=
  ![0, 0, x 1 - 2 * x 0, κ₄ * y 0 - y 3]

private def ThreefoldHomology.SecondSource.threeWangVector (κ₃ : ℤ) (a : Fin 2 → ℤ) : Lattice :=
  a 1 • ε + (a 0 - κ₃ * a 1) • deltaVector

private def ThreefoldHomology.SecondSource.fourWangVector (κ₄ : ℤ) (a : Fin 2 → ℤ) : Lattice :=
  a 1 • (-ε') + (2 * a 0 - κ₄ * a 1) • deltaVector

private theorem
    ThreefoldHomology.SecondSource.threeCoordinates_reconstruct (κ₃ κ₄ : ℤ) (x y : Lattice)
    (h : TrianglePeriodFamilyHomologyLattice.deltaOne (x, y) = 0) :
    threeWangVector κ₃ (threeCoordinates κ₃ κ₄ x y) - A₂ *ᵥ cuspCoordinates κ₄ x y = x := by
  have hx₂ := (kernel_coordinates x y h).1
  ext i
  fin_cases i <;>
      simp [threeWangVector, threeCoordinates, cuspCoordinates, deltaVector, ε, A₂, hx₂] <;>
    ring

private theorem ThreefoldHomology.SecondSource.fourCoordinates_reconstruct (κ₄ : ℤ) (x y : Lattice)
    (h : TrianglePeriodFamilyHomologyLattice.deltaOne (x, y) = 0) :
    fourWangVector κ₄ (fourCoordinates y) - cuspCoordinates κ₄ x y = y := by
  have hy₁ := (kernel_coordinates x y h).2.1
  have hy₂ := (kernel_coordinates x y h).2.2
  ext i
  fin_cases i <;>
      simp [fourWangVector, fourCoordinates, cuspCoordinates, deltaVector, ε', hy₁, hy₂] <;>
    ring

private theorem ThreefoldHomology.SecondSource.cuspCoordinates_fixed (κ₄ : ℤ) (x y : Lattice) :
    M₀ *ᵥ cuspCoordinates κ₄ x y = cuspCoordinates κ₄ x y := by
  ext i
  fin_cases i <;> simp [cuspCoordinates, M₀, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

private abbrev ThreefoldHomologyFinitenessCusp.FullSpace (D : SpecialPeriods.CuspFamily.Data) :=
  CuspQuotient.QuotientSpace D.correction D.radius

private def ThreefoldHomologyFinitenessCusp.parameterNorm (D : SpecialPeriods.CuspFamily.Data) :
    C(FullSpace D, ℝ) :=
  ⟨fun x => ‖CuspQuotient.projection D.correction D.radius x‖,
    (CuspQuotient.projection_continuous D.correction D.radius).norm⟩

private theorem ThreefoldHomologyFinitenessCusp.exponential_norm_mo1973_10230 (s : ℂ) :
    ‖CuspUniformization.exponential s‖ = Real.exp (-2 * Real.pi * s.im) :=
  (Real.exp_log (norm_pos_iff.mpr (CuspUniformization.exponential_ne_zero s))).symm.trans
    (congrArg Real.exp (CuspUniformization.log_norm_exponential s))

private theorem ThreefoldHomologyFinitenessCusp.parameterNorm_product_symm
    (D : SpecialPeriods.CuspFamily.Data)
    (p :
      ThreefoldOverlapMappingTorus.Cusp.Height D.radius ×
        ThreefoldOverlapMappingTorus.Cusp.Boundary) :
    parameterNorm D ((ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D).symm p) =
      Real.exp (-2 * Real.pi * (p.1 : ℝ)) := by
  rcases p with ⟨h, y⟩
  obtain ⟨⟨t, x⟩, rfl⟩ := MappingTorus.mk_surjective ThreefoldOverlapMappingTorus.Cusp.monodromy y
  change
    ‖CuspQuotient.projection D.correction D.radius
          (ThreefoldOverlapMappingTorus.Cusp.puncturedFamilyHomeomorph D
            ((ThreefoldOverlapMappingTorus.Cusp.familyProductHomeomorph D).symm
              (h, MappingTorus.mk ThreefoldOverlapMappingTorus.Cusp.monodromy (t, x))))‖ =
      _
  rw [ThreefoldOverlapMappingTorus.Cusp.familyProductHomeomorph_symm_mk,
    ThreefoldOverlapMappingTorus.Cusp.puncturedFamilyHomeomorph_base, D.projection_quotient]
  change
    ‖CuspUniformization.exponential
          (ThreefoldOverlapMappingTorus.Cusp.logPoint D.radius D.radius_pos t h)‖ =
      _
  rw [exponential_norm_mo1973_10230, ThreefoldOverlapMappingTorus.Cusp.logPoint_im]

private theorem ThreefoldHomologyFinitenessCusp.parameterNorm_punctured
    (D : SpecialPeriods.CuspFamily.Data)
    (x : CuspUniformization.PuncturedQuotient D.correction D.radius) :
    parameterNorm D x =
      Real.exp
        (-2 * Real.pi *
          ((ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D x).1 : ℝ)) := by
  have h :=
    parameterNorm_product_symm D
      (ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D x)
  rwa [Homeomorph.symm_apply_apply] at h

private def ThreefoldHomologyFinitenessCusp.heightCutoff (r H : ℝ) :
    C(unitInterval × ThreefoldOverlapMappingTorus.Cusp.Height r,
      ThreefoldOverlapMappingTorus.Cusp.Height r)
    where
  toFun
    p :=
    ⟨(p.2 : ℝ) + (p.1 : ℝ) * (Max.max (p.2 : ℝ) H - (p.2 : ℝ)),
      lt_of_lt_of_le p.2.property
        (le_add_of_nonneg_right (mul_nonneg p.1.property.1 (sub_nonneg.mpr (le_max_left _ _))))⟩
  continuous_toFun :=
    ((continuous_subtype_val.comp continuous_snd).add
          ((continuous_subtype_val.comp continuous_fst).mul
            (((continuous_subtype_val.comp continuous_snd).max continuous_const).sub
              (continuous_subtype_val.comp continuous_snd)))).subtype_mk
      _

@[simp]
private theorem ThreefoldHomologyFinitenessCusp.heightCutoff_zero (r H : ℝ)
    (h : ThreefoldOverlapMappingTorus.Cusp.Height r) : heightCutoff r H (0, h) = h := by
  apply Subtype.ext
  change (h : ℝ) + 0 * (Max.max (h : ℝ) H - (h : ℝ)) = (h : ℝ)
  simp

private theorem ThreefoldHomologyFinitenessCusp.heightCutoff_one (r H : ℝ)
    (h : ThreefoldOverlapMappingTorus.Cusp.Height r) :
    (heightCutoff r H (1, h) : ℝ) = Max.max (h : ℝ) H := by
  change (h : ℝ) + 1 * (Max.max (h : ℝ) H - (h : ℝ)) = _
  ring

private theorem ThreefoldHomologyFinitenessCusp.heightCutoff_ge (r H : ℝ) (t : unitInterval)
    (h : ThreefoldOverlapMappingTorus.Cusp.Height r) : (h : ℝ) ≤ (heightCutoff r H (t, h) : ℝ) :=
  le_add_of_nonneg_right (mul_nonneg t.property.1 (sub_nonneg.mpr (le_max_left _ _)))

private theorem ThreefoldHomologyFinitenessCusp.heightCutoff_fixed (r H : ℝ) (t : unitInterval)
    (h : ThreefoldOverlapMappingTorus.Cusp.Height r) (hh : H ≤ (h : ℝ)) :
    heightCutoff r H (t, h) = h := by
  apply Subtype.ext
  change (h : ℝ) + (t : ℝ) * (Max.max (h : ℝ) H - (h : ℝ)) = (h : ℝ)
  rw [max_eq_left hh, sub_self, MulZeroClass.mul_zero, add_zero]

private def
    ThreefoldHomologyFinitenessCusp.puncturedHeightCutoff (D : SpecialPeriods.CuspFamily.Data)
    (H : ℝ) :
    C(unitInterval × CuspUniformization.PuncturedQuotient D.correction D.radius,
      CuspUniformization.PuncturedQuotient D.correction D.radius)
    where
  toFun
    p :=
    (ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D).symm
      (heightCutoff D.radius H
          (p.1, (ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D p.2).1),
        (ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D p.2).2)
  continuous_toFun :=
    (ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D).symm.continuous.comp
      (((heightCutoff D.radius H).continuous.comp
            (continuous_fst.prodMk
              (continuous_fst.comp
                ((ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D).continuous.comp
                  continuous_snd)))).prodMk
        (continuous_snd.comp
          ((ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D).continuous.comp
            continuous_snd)))

private theorem ThreefoldHomologyFinitenessCusp.puncturedHeightCutoff_product
    (D : SpecialPeriods.CuspFamily.Data) (H : ℝ) (t : unitInterval)
    (x : CuspUniformization.PuncturedQuotient D.correction D.radius) :
    ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D
        (puncturedHeightCutoff D H (t, x)) =
      (heightCutoff D.radius H
          (t, (ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D x).1),
        (ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D x).2) :=
  (ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D).apply_symm_apply _

@[simp]
private theorem ThreefoldHomologyFinitenessCusp.puncturedHeightCutoff_zero
    (D : SpecialPeriods.CuspFamily.Data) (H : ℝ)
    (x : CuspUniformization.PuncturedQuotient D.correction D.radius) :
    puncturedHeightCutoff D H (0, x) = x := by
  apply (ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D).injective
  rw [puncturedHeightCutoff_product, heightCutoff_zero]

private theorem ThreefoldHomologyFinitenessCusp.puncturedHeightCutoff_parameterNorm
    (D : SpecialPeriods.CuspFamily.Data) (H : ℝ) (t : unitInterval)
    (x : CuspUniformization.PuncturedQuotient D.correction D.radius) :
    parameterNorm D (puncturedHeightCutoff D H (t, x)) =
      Real.exp
        (-2 * Real.pi *
          (heightCutoff D.radius H
              (t, (ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D x).1) :
            ℝ)) := by exact parameterNorm_product_symm D _

private theorem ThreefoldHomologyFinitenessCusp.puncturedHeightCutoff_norm_nonincrease
    (D : SpecialPeriods.CuspFamily.Data) (H : ℝ) (t : unitInterval)
    (x : CuspUniformization.PuncturedQuotient D.correction D.radius) :
    parameterNorm D (puncturedHeightCutoff D H (t, x)) ≤ parameterNorm D x := by
  rw [puncturedHeightCutoff_parameterNorm, parameterNorm_punctured]
  apply Real.exp_le_exp.mpr
  have hh :=
    heightCutoff_ge D.radius H t
      (ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D x).1
  nlinarith [Real.pi_pos]

private def ThreefoldHomologyFinitenessCusp.cutoffRadius (H : ℝ) : ℝ :=
  Real.exp (-2 * Real.pi * H)

private theorem ThreefoldHomologyFinitenessCusp.cutoffRadius_pos (H : ℝ) : 0 < cutoffRadius H :=
  Real.exp_pos _

private theorem ThreefoldHomologyFinitenessCusp.puncturedHeightCutoff_one_norm_le
    (D : SpecialPeriods.CuspFamily.Data) (H : ℝ)
    (x : CuspUniformization.PuncturedQuotient D.correction D.radius) :
    parameterNorm D (puncturedHeightCutoff D H (1, x)) ≤ cutoffRadius H := by
  rw [puncturedHeightCutoff_parameterNorm, heightCutoff_one]
  apply Real.exp_le_exp.mpr
  have hh :=
    le_max_right ((ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D x).1 : ℝ) H
  nlinarith [Real.pi_pos]

private theorem ThreefoldHomologyFinitenessCusp.puncturedHeightCutoff_fixed
    (D : SpecialPeriods.CuspFamily.Data) (H : ℝ) (t : unitInterval)
    (x : CuspUniformization.PuncturedQuotient D.correction D.radius)
    (hx : parameterNorm D x < cutoffRadius H) : puncturedHeightCutoff D H (t, x) = x := by
  have hh : H ≤ ((ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D x).1 : ℝ) := by
    rw [parameterNorm_punctured] at hx
    have he := Real.exp_lt_exp.mp hx
    nlinarith [Real.pi_pos]
  apply (ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D).injective
  rw [puncturedHeightCutoff_product, heightCutoff_fixed D.radius H t _ hh]

private theorem ThreefoldHomologyFinitenessCusp.cutoffRadius_threshold_lt {δ : ℝ} (hδ : 0 < δ) :
    cutoffRadius (ThreefoldOverlapMappingTorus.Cusp.heightThreshold δ + 1) < δ := by
  apply (Real.log_lt_log_iff (cutoffRadius_pos _) hδ).mp
  change
    Real.log
        (Real.exp (-2 * Real.pi * (ThreefoldOverlapMappingTorus.Cusp.heightThreshold δ + 1))) <
      Real.log δ
  rw [Real.log_exp]
  have ht : 2 * Real.pi * ThreefoldOverlapMappingTorus.Cusp.heightThreshold δ = -Real.log δ := by
    unfold ThreefoldOverlapMappingTorus.Cusp.heightThreshold
    exact mul_div_cancel₀ _ (ne_of_gt (mul_pos (by norm_num) Real.pi_pos))
  nlinarith [Real.pi_pos]

private abbrev ThreefoldHomologyFinitenessRetraction.Positive {X : Type*} [TopologicalSpace X]
    (ρ : C(X, ℝ)) :=
  { x : X // 0 < ρ x }

private abbrev ThreefoldHomologyFinitenessRetraction.Sublevel {X : Type*} [TopologicalSpace X]
    (ρ : C(X, ℝ)) (δ : ℝ) :=
  { x : X // ρ x < δ }

private def ThreefoldHomologyFinitenessRetraction.extensionFun {X : Type*} [TopologicalSpace X]
    (ρ : C(X, ℝ)) (H : C((unitInterval) × Positive ρ, Positive ρ)) (s : (unitInterval) × X) : X :=
  by classical exact if hx : 0 < ρ s.2 then (H (s.1, ⟨s.2, hx⟩)).val else s.2

private theorem ThreefoldHomologyFinitenessRetraction.extensionFun_apply_of_pos {X : Type*}
    [TopologicalSpace X] (ρ : C(X, ℝ)) (H : C((unitInterval) × Positive ρ, Positive ρ))
    (s : (unitInterval) × X) (hs : 0 < ρ s.2) : extensionFun ρ H s = (H (s.1, ⟨s.2, hs⟩)).val := by
  classical simp only [extensionFun, dite_eq_left hs]

private theorem ThreefoldHomologyFinitenessRetraction.extensionFun_apply_of_nonpos {X : Type*}
    [TopologicalSpace X] (ρ : C(X, ℝ)) (H : C((unitInterval) × Positive ρ, Positive ρ))
    (s : (unitInterval) × X) (hs : ρ s.2 ≤ 0) : extensionFun ρ H s = s.2 := by
  classical simp only [extensionFun, dite_eq_right (not_lt_of_ge hs)]

private theorem ThreefoldHomologyFinitenessRetraction.extensionFun_apply_of_small {X : Type*}
    [TopologicalSpace X] (ρ : C(X, ℝ)) (H : C((unitInterval) × Positive ρ, Positive ρ)) (η : ℝ)
    (hfix : ∀ (t : (unitInterval)) (x : Positive ρ), ρ x.val < η → H (t, x) = x)
    (s : (unitInterval) × X) (hs : ρ s.2 < η) : extensionFun ρ H s = s.2 := by
  by_cases hp : 0 < ρ s.2
  · rw [extensionFun_apply_of_pos ρ H s hp, hfix s.1 ⟨s.2, hp⟩ hs]
  · exact extensionFun_apply_of_nonpos ρ H s (le_of_not_gt hp)

private theorem ThreefoldHomologyFinitenessRetraction.extensionFun_continuousOn_positive {X : Type*}
    [TopologicalSpace X] (ρ : C(X, ℝ)) (H : C((unitInterval) × Positive ρ, Positive ρ)) :
    ContinuousOn (extensionFun ρ H) {s : (unitInterval) × X | 0 < ρ s.2} := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have hpair :
    Continuous
      (fun s : { s : (unitInterval) × X // 0 < ρ s.2 } =>
        (s.val.1, (⟨s.val.2, s.property⟩ : Positive ρ))) :=
    continuous_subtype_val.fst.prodMk (continuous_subtype_val.snd.subtype_mk _)
  exact
    (continuous_subtype_val.comp (H.continuous.comp hpair)).congr
      (fun s => (extensionFun_apply_of_pos ρ H s.val s.property).symm)

private theorem ThreefoldHomologyFinitenessRetraction.extensionFun_continuousOn_small {X : Type*}
    [TopologicalSpace X] (ρ : C(X, ℝ)) (H : C((unitInterval) × Positive ρ, Positive ρ)) (η : ℝ)
    (hfix : ∀ (t : (unitInterval)) (x : Positive ρ), ρ x.val < η → H (t, x) = x) :
    ContinuousOn (extensionFun ρ H) {s : (unitInterval) × X | ρ s.2 < η} :=
  continuous_snd.continuousOn.congr (fun s hs => extensionFun_apply_of_small ρ H η hfix s hs)

private theorem ThreefoldHomologyFinitenessRetraction.extensionFun_continuous {X : Type*}
    [TopologicalSpace X] (ρ : C(X, ℝ)) (H : C((unitInterval) × Positive ρ, Positive ρ)) (η : ℝ)
    (hη : 0 < η) (hfix : ∀ (t : (unitInterval)) (x : Positive ρ), ρ x.val < η → H (t, x) = x) :
    Continuous (extensionFun ρ H) := by
  have hρ : Continuous (fun s : (unitInterval) × X => ρ s.2) := ρ.continuous.comp continuous_snd
  have hopen : IsOpen {s : (unitInterval) × X | 0 < ρ s.2} := isOpen_lt continuous_const hρ
  have hsmall : IsOpen {s : (unitInterval) × X | ρ s.2 < η} := isOpen_lt hρ continuous_const
  apply continuous_iff_continuousAt.mpr
  intro s
  by_cases hs : 0 < ρ s.2
  · exact (extensionFun_continuousOn_positive ρ H).continuousAt (hopen.mem_nhds hs)
  · exact
      (extensionFun_continuousOn_small ρ H η hfix).continuousAt
        (hsmall.mem_nhds ((le_of_not_gt hs).trans_lt hη))

private def
    ThreefoldHomologyFinitenessRetraction.extension {X : Type*} [TopologicalSpace X] (ρ : C(X, ℝ))
    (H : C((unitInterval) × Positive ρ, Positive ρ)) (η : ℝ) (hη : 0 < η)
    (hfix : ∀ (t : (unitInterval)) (x : Positive ρ), ρ x.val < η → H (t, x) = x) :
    C((unitInterval) × X, X) :=
  ⟨extensionFun ρ H, extensionFun_continuous ρ H η hη hfix⟩

private theorem ThreefoldHomologyFinitenessRetraction.extension_apply_of_pos {X : Type*}
    [TopologicalSpace X] (ρ : C(X, ℝ)) (H : C((unitInterval) × Positive ρ, Positive ρ)) (η : ℝ)
    (hη : 0 < η) (hfix : ∀ (t : (unitInterval)) (x : Positive ρ), ρ x.val < η → H (t, x) = x)
    (s : (unitInterval) × X) (hs : 0 < ρ s.2) :
    extension ρ H η hη hfix s = (H (s.1, ⟨s.2, hs⟩)).val :=
  extensionFun_apply_of_pos ρ H s hs

private theorem ThreefoldHomologyFinitenessRetraction.extension_apply_of_nonpos {X : Type*}
    [TopologicalSpace X] (ρ : C(X, ℝ)) (H : C((unitInterval) × Positive ρ, Positive ρ)) (η : ℝ)
    (hη : 0 < η) (hfix : ∀ (t : (unitInterval)) (x : Positive ρ), ρ x.val < η → H (t, x) = x)
    (s : (unitInterval) × X) (hs : ρ s.2 ≤ 0) : extension ρ H η hη hfix s = s.2 :=
  extensionFun_apply_of_nonpos ρ H s hs

private theorem ThreefoldHomologyFinitenessRetraction.extension_apply_of_small {X : Type*}
    [TopologicalSpace X] (ρ : C(X, ℝ)) (H : C((unitInterval) × Positive ρ, Positive ρ)) (η : ℝ)
    (hη : 0 < η) (hfix : ∀ (t : (unitInterval)) (x : Positive ρ), ρ x.val < η → H (t, x) = x)
    (s : (unitInterval) × X) (hs : ρ s.2 < η) : extension ρ H η hη hfix s = s.2 :=
  extensionFun_apply_of_small ρ H η hfix s hs

private theorem
    ThreefoldHomologyFinitenessRetraction.extension_zero {X : Type*} [TopologicalSpace X]
    (ρ : C(X, ℝ)) (H : C(unitInterval × Positive ρ, Positive ρ)) (η : ℝ) (hη : 0 < η)
    (hfix : ∀ (t : unitInterval) (x : Positive ρ), ρ x.val < η → H (t, x) = x)
    (hzero : ∀ x : Positive ρ, H (0, x) = x) (x : X) : extension ρ H η hη hfix (0, x) = x := by
  by_cases hx : 0 < ρ x
  · exact
      (extension_apply_of_pos ρ H η hη hfix (0, x) hx).trans
        (congrArg Subtype.val (hzero ⟨x, hx⟩))
  · exact extension_apply_of_nonpos ρ H η hη hfix (0, x) (le_of_not_gt hx)

private theorem
    ThreefoldHomologyFinitenessRetraction.extension_radius_le {X : Type*} [TopologicalSpace X]
    (ρ : C(X, ℝ)) (H : C(unitInterval × Positive ρ, Positive ρ)) (η : ℝ) (hη : 0 < η)
    (hfix : ∀ (t : unitInterval) (x : Positive ρ), ρ x.val < η → H (t, x) = x)
    (hmono : ∀ (t : unitInterval) (x : Positive ρ), ρ (H (t, x)).val ≤ ρ x.val)
    (s : unitInterval × X) : ρ (extension ρ H η hη hfix s) ≤ ρ s.2 := by
  by_cases hs : 0 < ρ s.2
  · rw [extension_apply_of_pos ρ H η hη hfix s hs]
    exact hmono s.1 ⟨s.2, hs⟩
  · exact (congrArg ρ (extension_apply_of_nonpos ρ H η hη hfix s (le_of_not_gt hs))).le

private theorem
    ThreefoldHomologyFinitenessRetraction.extension_one_lt {X : Type*} [TopologicalSpace X]
    (ρ : C(X, ℝ)) (H : C(unitInterval × Positive ρ, Positive ρ)) (η : ℝ) (hη : 0 < η)
    (hfix : ∀ (t : unitInterval) (x : Positive ρ), ρ x.val < η → H (t, x) = x) (δ : ℝ)
    (hηδ : η ≤ δ) (hone : ∀ x : Positive ρ, ρ (H (1, x)).val < δ) (x : X) :
    ρ (extension ρ H η hη hfix (1, x)) < δ := by
  by_cases hx : 0 < ρ x
  · rw [extension_apply_of_pos ρ H η hη hfix (1, x) hx]
    exact hone ⟨x, hx⟩
  · rw [extension_apply_of_nonpos ρ H η hη hfix (1, x) (le_of_not_gt hx)]
    exact (le_of_not_gt hx).trans_lt (hη.trans_le hηδ)

private theorem ThreefoldHomologyFinitenessRetraction.extension_stays_sublevel {X : Type*}
    [TopologicalSpace X] (ρ : C(X, ℝ)) (H : C(unitInterval × Positive ρ, Positive ρ)) (η : ℝ)
    (hη : 0 < η) (hfix : ∀ (t : unitInterval) (x : Positive ρ), ρ x.val < η → H (t, x) = x)
    (hmono : ∀ (t : unitInterval) (x : Positive ρ), ρ (H (t, x)).val ≤ ρ x.val) (δ : ℝ)
    (s : unitInterval × Sublevel ρ δ) : ρ (extension ρ H η hη hfix (s.1, s.2.val)) < δ :=
  (extension_radius_le ρ H η hη hfix hmono (s.1, s.2.val)).trans_lt s.2.property

private def ThreefoldHomologyFinitenessRetraction.sublevelInclusion {X : Type*} [TopologicalSpace X]
    (ρ : C(X, ℝ)) (δ : ℝ) : C(Sublevel ρ δ, X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

private def ThreefoldHomologyFinitenessRetraction.sublevelMap {X : Type*} [TopologicalSpace X]
    (ρ : C(X, ℝ)) (H : C(unitInterval × Positive ρ, Positive ρ)) (η : ℝ) (hη : 0 < η)
    (hfix : ∀ (t : unitInterval) (x : Positive ρ), ρ x.val < η → H (t, x) = x) (δ : ℝ)
    (hηδ : η ≤ δ) (hone : ∀ x : Positive ρ, ρ (H (1, x)).val < δ) : C(X, Sublevel ρ δ)
    where
  toFun x := ⟨extension ρ H η hη hfix (1, x), extension_one_lt ρ H η hη hfix δ hηδ hone x⟩
  continuous_toFun :=
    ((extension ρ H η hη hfix).continuous.comp (continuous_const.prodMk continuous_id)).subtype_mk
      _

private def ThreefoldHomologyFinitenessRetraction.extendedHomotopy {X : Type*} [TopologicalSpace X]
    (ρ : C(X, ℝ)) (H : C(unitInterval × Positive ρ, Positive ρ)) (η : ℝ) (hη : 0 < η)
    (hfix : ∀ (t : unitInterval) (x : Positive ρ), ρ x.val < η → H (t, x) = x)
    (hzero : ∀ x : Positive ρ, H (0, x) = x) (δ : ℝ) (hηδ : η ≤ δ)
    (hone : ∀ x : Positive ρ, ρ (H (1, x)).val < δ) :
    (ContinuousMap.id X).HomotopyRel
      ((sublevelInclusion ρ δ).comp (sublevelMap ρ H η hη hfix δ hηδ hone)) {x : X | ρ x < η}
    where
  toFun := extension ρ H η hη hfix
  continuous_toFun := (extension ρ H η hη hfix).continuous
  map_zero_left := extension_zero ρ H η hη hfix hzero
  map_one_left _ := rfl
  prop' t x hx := extension_apply_of_small ρ H η hη hfix (t, x) hx

private def
    ThreefoldHomologyFinitenessRetraction.restrictedHomotopy {X : Type*} [TopologicalSpace X]
    (ρ : C(X, ℝ)) (H : C(unitInterval × Positive ρ, Positive ρ)) (η : ℝ) (hη : 0 < η)
    (hfix : ∀ (t : unitInterval) (x : Positive ρ), ρ x.val < η → H (t, x) = x)
    (hzero : ∀ x : Positive ρ, H (0, x) = x)
    (hmono : ∀ (t : unitInterval) (x : Positive ρ), ρ (H (t, x)).val ≤ ρ x.val) (δ : ℝ)
    (hηδ : η ≤ δ) (hone : ∀ x : Positive ρ, ρ (H (1, x)).val < δ) :
    (ContinuousMap.id (Sublevel ρ δ)).HomotopyRel
      ((sublevelMap ρ H η hη hfix δ hηδ hone).comp (sublevelInclusion ρ δ))
      {x : Sublevel ρ δ | ρ x.val < η}
    where
  toFun
    s :=
    ⟨extension ρ H η hη hfix (s.1, s.2.val), extension_stays_sublevel ρ H η hη hfix hmono δ s⟩
  continuous_toFun :=
    ((extension ρ H η hη hfix).continuous.comp
          (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk
      _
  map_zero_left
    x := by
    apply Subtype.ext
    exact extension_zero ρ H η hη hfix hzero x.val
  map_one_left _ := rfl
  prop' t x
    hx := by
    apply Subtype.ext
    exact extension_apply_of_small ρ H η hη hfix (t, x.val) hx

private def
    ThreefoldHomologyFinitenessRetraction.sublevelHomotopyEquiv {X : Type*} [TopologicalSpace X]
    (ρ : C(X, ℝ)) (H : C(unitInterval × Positive ρ, Positive ρ)) (η : ℝ) (hη : 0 < η)
    (hfix : ∀ (t : unitInterval) (x : Positive ρ), ρ x.val < η → H (t, x) = x)
    (hzero : ∀ x : Positive ρ, H (0, x) = x)
    (hmono : ∀ (t : unitInterval) (x : Positive ρ), ρ (H (t, x)).val ≤ ρ x.val) (δ : ℝ)
    (hηδ : η ≤ δ) (hone : ∀ x : Positive ρ, ρ (H (1, x)).val < δ) : X ≃ₕ Sublevel ρ δ
    where
  toFun := sublevelMap ρ H η hη hfix δ hηδ hone
  invFun := sublevelInclusion ρ δ
  left_inv := ⟨(extendedHomotopy ρ H η hη hfix hzero δ hηδ hone).toHomotopy.symm⟩
  right_inv := ⟨(restrictedHomotopy ρ H η hη hfix hzero hmono δ hηδ hone).toHomotopy.symm⟩

private def ThreefoldHomologyFinitenessCusp.positivePuncturedHomeomorph
    (D : SpecialPeriods.CuspFamily.Data) :
    ThreefoldHomologyFinitenessRetraction.Positive (parameterNorm D) ≃ₜ
      CuspUniformization.PuncturedQuotient D.correction D.radius
    where
  toFun
    x :=
    ⟨x.val,
      norm_pos_iff.mp
        (show 0 < ‖CuspQuotient.projection D.correction D.radius x.val‖ from x.property)⟩
  invFun x := ⟨x.val, norm_pos_iff.mpr x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

private def
    ThreefoldHomologyFinitenessCusp.positiveHeightCutoff (D : SpecialPeriods.CuspFamily.Data)
    (H : ℝ) :
    C(unitInterval × ThreefoldHomologyFinitenessRetraction.Positive (parameterNorm D),
      ThreefoldHomologyFinitenessRetraction.Positive (parameterNorm D))
    where
  toFun
    p :=
    (positivePuncturedHomeomorph D).symm
      (puncturedHeightCutoff D H (p.1, positivePuncturedHomeomorph D p.2))
  continuous_toFun :=
    (positivePuncturedHomeomorph D).symm.continuous.comp
      ((puncturedHeightCutoff D H).continuous.comp
        (continuous_fst.prodMk ((positivePuncturedHomeomorph D).continuous.comp continuous_snd)))

@[simp]
private theorem ThreefoldHomologyFinitenessCusp.positiveHeightCutoff_zero
    (D : SpecialPeriods.CuspFamily.Data) (H : ℝ)
    (x : ThreefoldHomologyFinitenessRetraction.Positive (parameterNorm D)) :
    positiveHeightCutoff D H (0, x) = x := by
  change
    (positivePuncturedHomeomorph D).symm
        (puncturedHeightCutoff D H (0, positivePuncturedHomeomorph D x)) =
      x
  rw [puncturedHeightCutoff_zero, Homeomorph.symm_apply_apply]

private theorem ThreefoldHomologyFinitenessCusp.positiveHeightCutoff_norm_nonincrease
    (D : SpecialPeriods.CuspFamily.Data) (H : ℝ) (t : unitInterval)
    (x : ThreefoldHomologyFinitenessRetraction.Positive (parameterNorm D)) :
    parameterNorm D (positiveHeightCutoff D H (t, x)).val ≤ parameterNorm D x.val :=
  puncturedHeightCutoff_norm_nonincrease D H t (positivePuncturedHomeomorph D x)

private theorem ThreefoldHomologyFinitenessCusp.positiveHeightCutoff_one_norm_le
    (D : SpecialPeriods.CuspFamily.Data) (H : ℝ)
    (x : ThreefoldHomologyFinitenessRetraction.Positive (parameterNorm D)) :
    parameterNorm D (positiveHeightCutoff D H (1, x)).val ≤ cutoffRadius H :=
  puncturedHeightCutoff_one_norm_le D H (positivePuncturedHomeomorph D x)

private theorem ThreefoldHomologyFinitenessCusp.positiveHeightCutoff_fixed
    (D : SpecialPeriods.CuspFamily.Data) (H : ℝ) (t : unitInterval)
    (x : ThreefoldHomologyFinitenessRetraction.Positive (parameterNorm D))
    (hx : parameterNorm D x.val < cutoffRadius H) : positiveHeightCutoff D H (t, x) = x := by
  change
    (positivePuncturedHomeomorph D).symm
        (puncturedHeightCutoff D H (t, positivePuncturedHomeomorph D x)) =
      x
  rw [puncturedHeightCutoff_fixed D H t _ hx, Homeomorph.symm_apply_apply]

private def
    ThreefoldHomologyFinitenessCusp.fullSublevelHomotopyEquiv (D : SpecialPeriods.CuspFamily.Data)
    (δ : ℝ) (hδ : 0 < δ) :
    FullSpace D ≃ₕ CuspCentralHomology.OpenQuotient D.correction D.radius δ :=
  ThreefoldHomologyFinitenessRetraction.sublevelHomotopyEquiv (parameterNorm D)
    (positiveHeightCutoff D (ThreefoldOverlapMappingTorus.Cusp.heightThreshold δ + 1))
    (cutoffRadius (ThreefoldOverlapMappingTorus.Cusp.heightThreshold δ + 1)) (cutoffRadius_pos _)
    (positiveHeightCutoff_fixed D _) (positiveHeightCutoff_zero D _)
    (positiveHeightCutoff_norm_nonincrease D _) δ (cutoffRadius_threshold_lt hδ).le
    (fun x => (positiveHeightCutoff_one_norm_le D _ x).trans_lt (cutoffRadius_threshold_lt hδ))

private def
    ThreefoldHomologyFinitenessCusp.fullCentralInclusion (D : SpecialPeriods.CuspFamily.Data) :
    C(CuspRetraction.QuotientCentralFibre D.correction D.radius, FullSpace D) :=
  ⟨Subtype.val, continuous_subtype_val⟩

private theorem ThreefoldHomologyFinitenessCusp.exists_fullCentralHomotopyEquiv
    (D : SpecialPeriods.CuspFamily.Data) :
    ∃ e : CuspRetraction.QuotientCentralFibre D.correction D.radius ≃ₕ FullSpace D,
      e.toFun = fullCentralInclusion D := by
  obtain ⟨δ, hδ, hδr, _hδ1, he⟩ :=
    CuspCentralHomology.exists_centralHomotopyEquiv D.correction D.radius D.radius_pos
      D.holomorphic
  obtain ⟨e, he⟩ := he δ hδ le_rfl hδr.le
  let eR := CuspCentralHomology.openQuotientRadiusHomeomorph D.correction hδr.le D.holomorphic
  let eF := fullSublevelHomotopyEquiv D δ hδ
  refine ⟨(e.trans eR.toHomotopyEquiv).trans eF.symm, ?_⟩
  apply ContinuousMap.ext
  intro x
  change (eR (e x)).val = x.val
  have hx := ContinuousMap.congr_fun he x
  change e x = eR.symm (CuspCentralHomology.centralIntoOpen D.correction D.radius δ hδ x) at hx
  rw [hx, Homeomorph.apply_symm_apply]
  rfl

private def ThreefoldHomologyFinitenessCusp.fullCentralHomotopyEquiv
    (D : SpecialPeriods.CuspFamily.Data) :
    CuspRetraction.QuotientCentralFibre D.correction D.radius ≃ₕ FullSpace D :=
  Classical.choose (exists_fullCentralHomotopyEquiv D)

@[simp]
private theorem ThreefoldHomologyFinitenessCusp.fullCentralHomotopyEquiv_toFun
    (D : SpecialPeriods.CuspFamily.Data) :
    (fullCentralHomotopyEquiv D).toFun = fullCentralInclusion D :=
  Classical.choose_spec (exists_fullCentralHomotopyEquiv D)

private def
    ThreefoldHomologyFinitenessCusp.fullCentralHomologyEquiv (D : SpecialPeriods.CuspFamily.Data)
    (n : ℕ) :
    SingularMayerVietoris.SingularHomology
        (CuspRetraction.QuotientCentralFibre D.correction D.radius) n ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (FullSpace D) n :=
  PeriodTorusHigherHomology.homotopyEquivHomologyEquiv (fullCentralHomotopyEquiv D) n

@[simp]
private theorem ThreefoldHomologyFinitenessCusp.fullCentralHomologyEquiv_toLinearMap
    (D : SpecialPeriods.CuspFamily.Data) (n : ℕ) :
    (fullCentralHomologyEquiv D n).toLinearMap =
      SingularMayerVietoris.singularHomologyMap (fullCentralInclusion D) n := by
  change SingularMayerVietoris.singularHomologyMap (fullCentralHomotopyEquiv D).toFun n = _
  rw [fullCentralHomotopyEquiv_toFun]

private def
    ThreefoldHomologyFinitenessCusp.fullHomologyCoordinates (D : SpecialPeriods.CuspFamily.Data)
    (n : ℕ) :
    SingularMayerVietoris.SingularHomology (FullSpace D) n ≃ₗ[ℤ]
      (Fin (CuspCentralHomology.centralBetti n) → ℤ) :=
  (fullCentralHomologyEquiv D n).symm.trans
    (CuspCentralHomology.centralSingularHomologyEquiv D.correction D.radius D.radius_pos
      D.holomorphic n)

private theorem
    ThreefoldHomologyFinitenessCusp.fullHomology_free (D : SpecialPeriods.CuspFamily.Data)
    (n : ℕ) : Module.Free ℤ (SingularMayerVietoris.SingularHomology (FullSpace D) n) :=
  Module.Free.of_equiv (fullHomologyCoordinates D n).symm

private theorem
    ThreefoldHomologyFinitenessCusp.fullHomology_finite (D : SpecialPeriods.CuspFamily.Data)
    (n : ℕ) : Module.Finite ℤ (SingularMayerVietoris.SingularHomology (FullSpace D) n) :=
  Module.Finite.of_surjective (fullHomologyCoordinates D n).symm.toLinearMap
    (fullHomologyCoordinates D n).symm.surjective

private theorem
    ThreefoldHomologyFinitenessCusp.fullHomology_finrank (D : SpecialPeriods.CuspFamily.Data)
    (n : ℕ) :
    Module.finrank ℤ (SingularMayerVietoris.SingularHomology (FullSpace D) n) =
      CuspCentralHomology.centralBetti n := by
  rw [(fullHomologyCoordinates D n).finrank_eq]
  exact Module.finrank_fin_fun ℤ

private theorem ThreefoldHomologyFinitenessCusp.fullHomology_subsingleton_of_four_lt
    (D : SpecialPeriods.CuspFamily.Data) {n : ℕ} (hn : 4 < n) :
    Subsingleton (SingularMayerVietoris.SingularHomology (FullSpace D) n) := by
  have :=
    CuspCentralHomology.centralSingularHomology_subsingleton_of_four_lt D.correction D.radius
      D.radius_pos D.holomorphic hn
  refine ⟨fun a b => (fullCentralHomologyEquiv D n).symm.injective ?_⟩
  exact Subsingleton.elim _ _

private def CuspCoinvariants.oneDifference : (Fin 4 → ℤ) →ₗ[ℤ] (Fin 4 → ℤ) :=
  (M₀ - 1).mulVecLin

private def CuspCoinvariants.squareDifference : (Fin 6 → ℤ) →ₗ[ℤ] (Fin 6 → ℤ) :=
  (PeriodTorusHigherHomologyExterior.squareM₀ - 1).mulVecLin

private def CuspCoinvariants.cubeDifference : (Fin 4 → ℤ) →ₗ[ℤ] (Fin 4 → ℤ) :=
  (PeriodTorusHigherHomologyExterior.cubeM₀ - 1).mulVecLin

@[simp]
private theorem CuspCoinvariants.squareDifference_apply (v : Fin 6 → ℤ) :
    squareDifference v = ![0, v 0, 0, 0, v 0, v 0 + v 1 + v 4] := by
  ext i
  fin_cases i <;>
    simp [squareDifference, PeriodTorusHigherHomologyExterior.squareM₀_eq, dotProduct,
      Fin.sum_univ_succ]
  ring

private theorem CuspCoinvariants.cubeM₀_eq_M₀ : PeriodTorusHigherHomologyExterior.cubeM₀ = M₀ := by
  rw [PeriodTorusHigherHomologyExterior.cubeM₀_eq]
  rfl

private theorem
    CuspCoinvariants.cubeDifference_eq_oneDifference : cubeDifference = oneDifference := by
  rw [cubeDifference, oneDifference, cubeM₀_eq_M₀]

private def CuspCoinvariants.squareProjection : (Fin 6 → ℤ) →ₗ[ℤ] (Fin 4 → ℤ)
    where
  toFun v := ![v 0, v 2, v 3, v 4 - v 1]
  map_add' v
    w := by
    ext i
    fin_cases i <;> simp
    ring
  map_smul' c
    v := by
    ext i
    fin_cases i <;> simp
    ring

private def CuspCoinvariants.squareSection : (Fin 4 → ℤ) →ₗ[ℤ] (Fin 6 → ℤ)
    where
  toFun z := ![z 0, 0, z 1, z 2, z 3, 0]
  map_add' v
    w := by
    ext i
    fin_cases i <;> simp
  map_smul' c
    v := by
    ext i
    fin_cases i <;> simp

@[simp]
private theorem CuspCoinvariants.squareProjection_section (z : Fin 4 → ℤ) :
    squareProjection (squareSection z) = z := by
  ext i
  fin_cases i <;> simp [squareProjection, squareSection]

private theorem
    CuspCoinvariants.squareProjection_surjective : Function.Surjective squareProjection :=
  fun z => ⟨squareSection z, squareProjection_section z⟩

private theorem CuspCoinvariants.squareDifference_range_iff (v : Fin 6 → ℤ) :
    v ∈ LinearMap.range squareDifference ↔ v 0 = 0 ∧ v 2 = 0 ∧ v 3 = 0 ∧ v 4 = v 1 := by
  change (∃ w, squareDifference w = v) ↔ _
  constructor
  · rintro ⟨w, rfl⟩
    simp
  · rintro ⟨h0, h2, h3, h41⟩
    refine ⟨![v 1, v 5 - v 1, 0, 0, 0, 0], ?_⟩
    rw [squareDifference_apply]
    ext i
    fin_cases i <;> simp [h0, h2, h3, h41]

private theorem CuspCoinvariants.squareProjection_eq_zero_iff (v : Fin 6 → ℤ) :
    squareProjection v = 0 ↔ v 0 = 0 ∧ v 2 = 0 ∧ v 3 = 0 ∧ v 4 = v 1 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    have h3 := congrFun h 3
    change v 0 = 0 at h0
    change v 2 = 0 at h1
    change v 3 = 0 at h2
    change v 4 - v 1 = 0 at h3
    exact ⟨h0, h1, h2, sub_eq_zero.mp h3⟩
  · rintro ⟨h0, h2, h3, h41⟩
    ext i
    fin_cases i <;> simp [squareProjection, h0, h2, h3, h41]

private theorem CuspCoinvariants.squareProjection_ker_eq_range :
    LinearMap.ker squareProjection = LinearMap.range squareDifference := by
  ext v
  rw [LinearMap.mem_ker, squareProjection_eq_zero_iff, squareDifference_range_iff]

private def CuspCoinvariants.squareCoinvariantEquiv :
    ((Fin 6 → ℤ) ⧸ LinearMap.range squareDifference) ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  (Submodule.quotEquivOfEq _ _ squareProjection_ker_eq_range.symm).trans
    (squareProjection.quotKerEquivOfSurjective squareProjection_surjective)

private def CuspCoinvariants.oneProjection : (Fin 4 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ)
    where
  toFun v := ![v 0, v 1]
  map_add' v
    w := by
    ext i
    fin_cases i <;> rfl
  map_smul' c
    v := by
    ext i
    fin_cases i <;> rfl

private def CuspCoinvariants.oneSection : (Fin 2 → ℤ) →ₗ[ℤ] (Fin 4 → ℤ)
    where
  toFun z := ![z 0, z 1, 0, 0]
  map_add' v
    w := by
    ext i
    fin_cases i <;> simp
  map_smul' c
    v := by
    ext i
    fin_cases i <;> simp

@[simp]
private theorem CuspCoinvariants.oneProjection_section (z : Fin 2 → ℤ) :
    oneProjection (oneSection z) = z := by
  ext i
  fin_cases i <;> rfl

private theorem
    CuspCoinvariants.oneProjection_surjective : Function.Surjective oneProjection := fun z =>
  ⟨oneSection z, oneProjection_section z⟩

private theorem CuspCoinvariants.oneDifference_range_iff (v : Fin 4 → ℤ) :
    v ∈ LinearMap.range oneDifference ↔ v 0 = 0 ∧ v 1 = 0 :=
  M₀_sub_one_range v

private theorem CuspCoinvariants.oneProjection_eq_zero_iff (v : Fin 4 → ℤ) :
    oneProjection v = 0 ↔ v 0 = 0 ∧ v 1 = 0 := by
  constructor
  · intro h
    exact ⟨congrFun h 0, congrFun h 1⟩
  · rintro ⟨h0, h1⟩
    ext i
    fin_cases i <;> simp [oneProjection, h0, h1]

private theorem CuspCoinvariants.oneProjection_ker_eq_range :
    LinearMap.ker oneProjection = LinearMap.range oneDifference := by
  ext v
  rw [LinearMap.mem_ker, oneProjection_eq_zero_iff, oneDifference_range_iff]

private def CuspCoinvariants.oneCoinvariantEquiv :
    ((Fin 4 → ℤ) ⧸ LinearMap.range oneDifference) ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (Submodule.quotEquivOfEq _ _ oneProjection_ker_eq_range.symm).trans
    (oneProjection.quotKerEquivOfSurjective oneProjection_surjective)

private abbrev CuspCoinvariants.cubeProjection :=
  oneProjection

private theorem CuspCoinvariants.cubeProjection_surjective : Function.Surjective cubeProjection :=
  oneProjection_surjective

private theorem CuspCoinvariants.cubeProjection_ker_eq_range :
    LinearMap.ker cubeProjection = LinearMap.range cubeDifference := by
  rw [cubeDifference_eq_oneDifference]
  exact oneProjection_ker_eq_range

private def CuspCoinvariants.cubeCoinvariantEquiv :
    ((Fin 4 → ℤ) ⧸ LinearMap.range cubeDifference) ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (Submodule.quotEquivOfEq _ _ cubeProjection_ker_eq_range.symm).trans
    (cubeProjection.quotKerEquivOfSurjective cubeProjection_surjective)

private theorem
    CuspCoinvariants.map_range_of_intertwines {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (e : M ≃ₗ[ℤ] N) (A : M →ₗ[ℤ] M) (B : N →ₗ[ℤ] N)
    (h : ∀ x, e (A x) = B (e x)) : (LinearMap.range A).map e.toLinearMap = LinearMap.range B := by
  ext y
  constructor
  · rintro ⟨x, ⟨z, rfl⟩, rfl⟩
    exact ⟨e z, (h z).symm⟩
  · rintro ⟨z, rfl⟩
    refine ⟨A (e.symm z), ⟨e.symm z, rfl⟩, ?_⟩
    change e (A (e.symm z)) = B z
    rw [h, LinearEquiv.apply_symm_apply]

private def CuspCoinvariants.quotientRangeEquiv {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (e : M ≃ₗ[ℤ] N) (A : M →ₗ[ℤ] M) (B : N →ₗ[ℤ] N)
    (h : ∀ x, e (A x) = B (e x)) : (M ⧸ LinearMap.range A) ≃ₗ[ℤ] (N ⧸ LinearMap.range B) := by
  let q :=
    Submodule.Quotient.equiv (LinearMap.range A) (LinearMap.range B) e
      (map_range_of_intertwines e A B h)
  let qa : (M ⧸ LinearMap.range A) ≃+ (N ⧸ LinearMap.range B) := by
    letI := Submodule.Quotient.module (LinearMap.range A)
    letI := Submodule.Quotient.module (LinearMap.range B)
    exact q.toAddEquiv
  exact qa.toIntLinearEquiv

public
theorem CuspCoinvariants.mem_range_iff_of_intertwines {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (e : M ≃ₗ[ℤ] N) (A : M →ₗ[ℤ] M) (B : N →ₗ[ℤ] N)
    (h : ∀ x, e (A x) = B (e x)) (x : M) : x ∈ LinearMap.range A ↔ e x ∈ LinearMap.range B := by
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨e z, (h z).symm⟩
  · rintro ⟨z, hz⟩
    refine ⟨e.symm z, e.injective ?_⟩
    rw [h, LinearEquiv.apply_symm_apply, hz]

private def CuspCoinvariants.torusDifference (q : ℕ) :
    SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) q →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) q :=
  SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap M₀) q -
    LinearMap.id

@[simp]
private theorem CuspCoinvariants.torusDifference_apply (q : ℕ)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) q) :
    torusDifference q a =
      SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap M₀) q
          a -
        a :=
  rfl

private theorem CuspCoinvariants.torusDifference_two_coordinates
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) 2) :
    PeriodTorusHigherHomology.coordinateTorusH2Coordinates (torusDifference 2 a) =
      squareDifference (PeriodTorusHigherHomology.coordinateTorusH2Coordinates a) := by
  rw [torusDifference_apply, map_sub,
    PeriodTorusHigherHomology.coordinateTorusH2Coordinates_matrix]
  simp only [squareDifference, Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec,
    PeriodTorusHigherHomologyExterior.squareM₀]

private theorem CuspCoinvariants.torusDifference_three_coordinates
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) 3) :
    PeriodTorusHigherHomology.coordinateTorusH3Coordinates (torusDifference 3 a) =
      cubeDifference (PeriodTorusHigherHomology.coordinateTorusH3Coordinates a) := by
  rw [torusDifference_apply, map_sub,
    PeriodTorusHigherHomology.coordinateTorusH3Coordinates_matrix]
  simp only [cubeDifference, Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec,
    PeriodTorusHigherHomologyExterior.cubeM₀]

private abbrev CuspCoinvariants.TorusCoinvariants (q : ℕ) :=
  SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) q ⧸
    LinearMap.range (torusDifference q)

private def CuspCoinvariants.torusTwoCoinvariantEquiv : TorusCoinvariants 2 ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  ((quotientRangeEquiv PeriodTorusHigherHomology.coordinateTorusH2Coordinates (torusDifference 2)
          squareDifference torusDifference_two_coordinates).toAddEquiv.trans
      squareCoinvariantEquiv.toAddEquiv).toIntLinearEquiv

private def CuspCoinvariants.torusThreeCoinvariantEquiv : TorusCoinvariants 3 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  ((quotientRangeEquiv PeriodTorusHigherHomology.coordinateTorusH3Coordinates (torusDifference 3)
          cubeDifference torusDifference_three_coordinates).toAddEquiv.trans
      cubeCoinvariantEquiv.toAddEquiv).toIntLinearEquiv

private def CuspCoinvariants.integerLinearMapOfAdd_mo1973_14485 {M N : Type*} [AddCommGroup M]
    [Module ℤ M] [AddCommGroup N] [Module ℤ N] (g : M →+ N) : M →ₗ[ℤ] N
    where
  toFun := g
  map_add' := g.map_add
  map_smul' c x := by simpa only [Int.cast_id, RingHom.id_apply] using map_intCast_smul g ℤ ℤ c x

private def
    CuspCoinvariants.quotientLiftMap {M N : Type*} [AddCommGroup M] [Module ℤ M] [AddCommGroup N]
    [Module ℤ N] (S : Submodule ℤ M) (f : M →ₗ[ℤ] N) (hS : S ≤ LinearMap.ker f) :
    (M ⧸ S) →ₗ[ℤ] N :=
  integerLinearMapOfAdd_mo1973_14485 (S.liftQ f hS).toAddMonoidHom

private theorem CuspCoinvariants.quotientLift_surjective {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (S : Submodule ℤ M) (f : M →ₗ[ℤ] N) (hf : Function.Surjective f)
    (hS : S ≤ LinearMap.ker f) : Function.Surjective (S.liftQ f hS) := by
  intro y
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨Submodule.Quotient.mk x, rfl⟩

private theorem CuspCoinvariants.quotientLift_bijective_of_finrank {M N : Type*} [AddCommGroup M]
    [Module ℤ M] [AddCommGroup N] [Module ℤ N] [Module.Free ℤ N] [Module.Finite ℤ N]
    (S : Submodule ℤ M) {r : ℕ} (e : (M ⧸ S) ≃ₗ[ℤ] (Fin r → ℤ)) (f : M →ₗ[ℤ] N)
    (hf : Function.Surjective f) (hS : S ≤ LinearMap.ker f) (hrank : Module.finrank ℤ N = r) :
    Function.Bijective (S.liftQ f hS) := by
  let g : (Fin r → ℤ) →ₗ[ℤ] N := (quotientLiftMap S f hS).comp e.symm.toLinearMap
  have hgs : Function.Surjective g := (quotientLift_surjective S f hf hS).comp e.symm.surjective
  have hgb : Function.Bijective g := by
    apply OrzechProperty.bijective_of_surjective_of_finrank_le g hgs
    rw [Module.finrank_fin_fun, hrank]
  refine ⟨?_, quotientLift_surjective S f hf hS⟩
  intro x y hxy
  apply e.injective
  apply hgb.injective
  change S.liftQ f hS (e.symm (e x)) = S.liftQ f hS (e.symm (e y))
  simpa only [LinearEquiv.symm_apply_apply] using hxy

private theorem
    CuspCoinvariants.kernel_eq_of_quotient_equiv {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] [Module.Free ℤ N] [Module.Finite ℤ N] (S : Submodule ℤ M)
    {r : ℕ} (e : (M ⧸ S) ≃ₗ[ℤ] (Fin r → ℤ)) (f : M →ₗ[ℤ] N) (hf : Function.Surjective f)
    (hS : S ≤ LinearMap.ker f) (hrank : Module.finrank ℤ N = r) : LinearMap.ker f = S := by
  apply le_antisymm ?_ hS
  intro x hx
  apply (Submodule.Quotient.mk_eq_zero S).mp
  apply (quotientLift_bijective_of_finrank S e f hf hS hrank).injective
  rw [Submodule.liftQ_apply, map_zero]
  exact hx

private def CuspCoinvariants.exteriorSquareDifference :
    PeriodTorusHigherHomologyExterior.latticeExterior 2 →ₗ[ℤ]
      PeriodTorusHigherHomologyExterior.latticeExterior 2 :=
  exteriorPower.map 2 M₀.mulVecLin - LinearMap.id

private def CuspCoinvariants.exteriorCubeDifference :
    PeriodTorusHigherHomologyExterior.latticeExterior 3 →ₗ[ℤ]
      PeriodTorusHigherHomologyExterior.latticeExterior 3 :=
  exteriorPower.map 3 M₀.mulVecLin - LinearMap.id

private theorem CuspCoinvariants.range_difference_le_ker_of_invariant {M N : Type*} [AddCommGroup M]
    [Module ℤ M] [AddCommGroup N] [Module ℤ N] (A : M →ₗ[ℤ] M) (f : M →ₗ[ℤ] N)
    (h : ∀ x, f (A x) = f x) : LinearMap.range (A - LinearMap.id) ≤ LinearMap.ker f := by
  rintro x ⟨y, rfl⟩
  change f (A y - y) = 0
  rw [map_sub, h, sub_self]

private theorem CuspCoinvariants.torusTwo_kernel_eq {N : Type*} [AddCommGroup N] [Module ℤ N]
    [Module.Free ℤ N] [Module.Finite ℤ N]
    (f :
      SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) 2 →ₗ[ℤ] N)
    (hf : Function.Surjective f) (hS : LinearMap.range (torusDifference 2) ≤ LinearMap.ker f)
    (hrank : Module.finrank ℤ N = 4) : LinearMap.ker f = LinearMap.range (torusDifference 2) :=
  kernel_eq_of_quotient_equiv _ torusTwoCoinvariantEquiv f hf hS hrank

private theorem CuspCoinvariants.torusThree_kernel_eq {N : Type*} [AddCommGroup N] [Module ℤ N]
    [Module.Free ℤ N] [Module.Finite ℤ N]
    (f :
      SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) 3 →ₗ[ℤ] N)
    (hf : Function.Surjective f) (hS : LinearMap.range (torusDifference 3) ≤ LinearMap.ker f)
    (hrank : Module.finrank ℤ N = 2) : LinearMap.ker f = LinearMap.range (torusDifference 3) :=
  kernel_eq_of_quotient_equiv _ torusThreeCoinvariantEquiv f hf hS hrank

private theorem
    CuspCoinvariants.torusTwo_kernel_eq_of_invariant {N : Type*} [AddCommGroup N] [Module ℤ N]
    [Module.Free ℤ N] [Module.Finite ℤ N]
    (f :
      SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) 2 →ₗ[ℤ] N)
    (hf : Function.Surjective f)
    (hinv :
      ∀ x,
        f
            (SingularMayerVietoris.singularHomologyMap
              (PeriodTorusHigherHomology.torusMatrixMap M₀) 2 x) =
          f x)
    (hrank : Module.finrank ℤ N = 4) : LinearMap.ker f = LinearMap.range (torusDifference 2) :=
  torusTwo_kernel_eq f hf (range_difference_le_ker_of_invariant _ f hinv) hrank

private theorem CuspCoinvariants.torusThree_kernel_eq_of_invariant {N : Type*} [AddCommGroup N]
    [Module ℤ N] [Module.Free ℤ N] [Module.Finite ℤ N]
    (f :
      SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) 3 →ₗ[ℤ] N)
    (hf : Function.Surjective f)
    (hinv :
      ∀ x,
        f
            (SingularMayerVietoris.singularHomologyMap
              (PeriodTorusHigherHomology.torusMatrixMap M₀) 3 x) =
          f x)
    (hrank : Module.finrank ℤ N = 2) : LinearMap.ker f = LinearMap.range (torusDifference 3) :=
  torusThree_kernel_eq f hf (range_difference_le_ker_of_invariant _ f hinv) hrank

private def
    ThreefoldHomologyCuspFibre.actualFibreInclusion (D : SpecialPeriods.CuspFamily.Data) (t : ℂ) :
    C(CuspControlledRetraction.ActualQuotientFibre D.correction D.radius t,
      ThreefoldHomologyFinitenessCusp.FullSpace D) :=
  ⟨Subtype.val, continuous_subtype_val⟩

end Mathoverflow1973

end
