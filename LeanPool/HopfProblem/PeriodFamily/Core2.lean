/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology8
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.PeriodFamily.PeriodPoint
import all LeanPool.HopfProblem.Foundations.Core3
import all LeanPool.HopfProblem.PeriodFamily.HolomorphicPeriodMap1
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods2
import all LeanPool.HopfProblem.PeriodFamily.Core1
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods6
import all LeanPool.HopfProblem.Toric.DiagonalQuotient1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology8

/-!
# Hopf problem: period family · core 2

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

@[instance_reducible]
private def PeriodFamily.Data.totalAction {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction SpecialPeriods.TriangleGroup B]
    (D : PeriodFamily.Data V B) : MulAction SpecialPeriods.TriangleGroup D.TotalSpace := by
  let := SpecialPeriods.triangleTorusAction
  exact inferInstanceAs (MulAction SpecialPeriods.TriangleGroup (B × RealTorus₄))

private theorem PeriodFamily.Data.totalAction_zeroSection {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (g : SpecialPeriods.TriangleGroup) (b : B) :
    letI := D.totalAction
    g • D.periods.zeroSection b = D.periods.zeroSection (g • b) := by
  let := D.totalAction
  change (g • b, SpecialPeriods.triangleTorusHomeomorph g 0) = (g • b, 0)
  rw [SpecialPeriods.triangleTorusHomeomorph_zero]

private theorem PeriodFamily.Data.periodEquiv_matrix {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B) (b : B)
    (x : RealPlane₄) :
    D.periods.periodEquiv b x = (D.periods.point b).val.matrix *ᵥ (fun i => (x i : ℂ)) := by
  rw [HolomorphicPeriodMap.periodEquiv_coordinates]
  ext i
  fin_cases i <;> simp [PeriodPoint.matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

private theorem PeriodFamily.Data.realEquiv_complexCast (g : SpecialPeriods.TriangleGroup)
    (x : RealPlane₄) :
    (fun i => ((SpecialPeriods.triangleRealEquiv g x) i : ℂ)) =
      PeriodFamily.dualComplexMatrix g *ᵥ (fun i => (x i : ℂ)) := by
  ext i
  simp [SpecialPeriods.triangleRealEquiv_apply, PeriodFamily.dualComplexMatrix, Matrix.mulVec,
    dotProduct]

private theorem PeriodFamily.Data.periodEquiv_monodromy {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (g : SpecialPeriods.TriangleGroup) (b : B) (x : RealPlane₄) :
    D.periods.periodEquiv (g • b) (SpecialPeriods.triangleRealEquiv g x) =
      D.rightBlock g b *ᵥ D.periods.periodEquiv b x := by
  rw [D.periodEquiv_matrix, realEquiv_complexCast, Matrix.mulVec_mulVec, D.periodEquiv_matrix,
    Matrix.mulVec_mulVec, D.matrix_covariance]

private theorem PeriodFamily.Data.periodEquiv_symm_monodromy {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (g : SpecialPeriods.TriangleGroup) (b : B) (w : ComplexPlane₂) :
    (D.periods.periodEquiv (g • b)).symm (D.rightBlock g b *ᵥ w) =
      SpecialPeriods.triangleRealEquiv g ((D.periods.periodEquiv b).symm w) := by
  apply (D.periods.periodEquiv (g • b)).injective
  rw [LinearEquiv.apply_symm_apply, D.periodEquiv_monodromy, LinearEquiv.apply_symm_apply]

private def PeriodFamily.Data.complexLift {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction SpecialPeriods.TriangleGroup B]
    (D : PeriodFamily.Data V B) (g : SpecialPeriods.TriangleGroup) (x : B × ComplexPlane₂) :
    B × ComplexPlane₂ :=
  (g • x.1, D.rightBlock g x.1 *ᵥ x.2)

private theorem PeriodFamily.Data.complexLift_quotientMap {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (g : SpecialPeriods.TriangleGroup) (x : B × ComplexPlane₂) :
    letI := D.totalAction
    D.periods.quotientMap (D.complexLift g x) = g • D.periods.quotientMap x := by
  let := D.totalAction
  change
    (g • x.1,
        standardLattice.mkQ
          ((D.periods.periodEquiv (g • x.1)).symm (D.rightBlock g x.1 *ᵥ x.2))) =
      (g • x.1,
        SpecialPeriods.triangleTorusHomeomorph g
          (standardLattice.mkQ ((D.periods.periodEquiv x.1).symm x.2)))
  rw [D.periodEquiv_symm_monodromy, SpecialPeriods.triangleTorusHomeomorph_mkQ]

/-- The product charted-space structure on the covering space of a period family. -/
@[instance_reducible]
public
def PeriodFamily.Data.coveringChartedSpace {V B : Type*} [NormedAddCommGroup V]
    [TopologicalSpace B] [ChartedSpace V B] :
    ChartedSpace (V × ComplexPlane₂) (B × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd V ComplexPlane₂) (B × ComplexPlane₂))

attribute [local instance] PeriodFamily.Data.coveringChartedSpace in
public
theorem
    PeriodFamily.Data.coveringManifold {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [IsManifold (modelWithCornersSelf ℂ V) ω B] :
    IsManifold (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω (B × ComplexPlane₂) := by
  rw [modelWithCornersSelf_prod]
  exact
    IsManifold.prod (I := modelWithCornersSelf ℂ V) (I' := modelWithCornersSelf ℂ ComplexPlane₂) B
      ComplexPlane₂

attribute [local instance] PeriodFamily.Data.coveringChartedSpace
    PeriodFamily.Data.coveringManifold in
private theorem
    PeriodFamily.Data.periodMatrix_entry_holomorphic {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B) (i : Fin 2)
    (k : Fin 4) :
    ContMDiff (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ ℂ) ω
      (fun b : B => (D.periods.point b).val.matrix i k) := by
  fin_cases i
  · fin_cases k
    · exact contMDiff_const.mul D.periods.holomorphic_mu
    · exact D.periods.holomorphic_tau
    · exact contMDiff_const
    · exact contMDiff_const
  · fin_cases k
    · exact D.periods.holomorphic_beta
    · exact D.periods.holomorphic_mu
    · exact contMDiff_const
    · exact contMDiff_const

attribute [local instance] PeriodFamily.Data.coveringChartedSpace
    PeriodFamily.Data.coveringManifold in
private theorem PeriodFamily.Data.rightBlock_entry_holomorphic {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (g : SpecialPeriods.TriangleGroup) (i k : Fin 2) :
    ContMDiff (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ ℂ) ω
      (fun b : B => D.rightBlock g b i k) := by
  have h₀ :=
    ((D.periodMatrix_entry_holomorphic i 0).comp (D.base_holomorphic g)).mul
      (contMDiff_const (c := PeriodFamily.dualComplexMatrix g 0 (![2, 3] k)))
  have h₁ :=
    ((D.periodMatrix_entry_holomorphic i 1).comp (D.base_holomorphic g)).mul
      (contMDiff_const (c := PeriodFamily.dualComplexMatrix g 1 (![2, 3] k)))
  have h₂ :=
    ((D.periodMatrix_entry_holomorphic i 2).comp (D.base_holomorphic g)).mul
      (contMDiff_const (c := PeriodFamily.dualComplexMatrix g 2 (![2, 3] k)))
  have h₃ :=
    ((D.periodMatrix_entry_holomorphic i 3).comp (D.base_holomorphic g)).mul
      (contMDiff_const (c := PeriodFamily.dualComplexMatrix g 3 (![2, 3] k)))
  convert ((h₀.add h₁).add h₂).add h₃ using 1
  funext b
  simp [rightBlock, Matrix.mul_apply, Fin.sum_univ_four, add_assoc, Function.comp_def]

attribute [local instance] PeriodFamily.Data.coveringChartedSpace
    PeriodFamily.Data.coveringManifold in
private theorem PeriodFamily.Data.linearLift_holomorphic {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (g : SpecialPeriods.TriangleGroup) :
    ContMDiff (modelWithCornersSelf ℂ (V × ComplexPlane₂)) (modelWithCornersSelf ℂ ComplexPlane₂)
      ω (fun x : B × ComplexPlane₂ => D.rightBlock g x.1 *ᵥ x.2) := by
  have hf :
    ContMDiff (modelWithCornersSelf ℂ (V × ComplexPlane₂)) (modelWithCornersSelf ℂ V) ω
      (Prod.fst : B × ComplexPlane₂ → B) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_fst
  have hs :
    ContMDiff (modelWithCornersSelf ℂ (V × ComplexPlane₂)) (modelWithCornersSelf ℂ ComplexPlane₂)
      ω (Prod.snd : B × ComplexPlane₂ → ComplexPlane₂) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_snd
  apply contMDiff_pi_space.mpr
  intro i
  have h₀ := ((D.rightBlock_entry_holomorphic g i 0).comp hf).mul ((contMDiff_pi_space.mp hs) 0)
  have h₁ := ((D.rightBlock_entry_holomorphic g i 1).comp hf).mul ((contMDiff_pi_space.mp hs) 1)
  convert h₀.add h₁ using 1
  funext x
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Function.comp_def]

attribute [local instance] PeriodFamily.Data.coveringChartedSpace
    PeriodFamily.Data.coveringManifold in
private theorem PeriodFamily.Data.complexLift_holomorphic {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (g : SpecialPeriods.TriangleGroup) :
    ContMDiff (modelWithCornersSelf ℂ (V × ComplexPlane₂))
      (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω (D.complexLift g) := by
  have hf :
    ContMDiff (modelWithCornersSelf ℂ (V × ComplexPlane₂)) (modelWithCornersSelf ℂ V) ω
      (fun x : B × ComplexPlane₂ => g • x.1) := by
    rw [modelWithCornersSelf_prod]
    exact (D.base_holomorphic g).comp contMDiff_fst
  have hs := D.linearLift_holomorphic g
  rw [modelWithCornersSelf_prod] at hf hs ⊢
  exact hf.prodMk hs

attribute [local instance] PeriodFamily.Data.coveringChartedSpace
    PeriodFamily.Data.coveringManifold in
private theorem PeriodFamily.Data.totalAction_holomorphic {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    [IsManifold (modelWithCornersSelf ℂ V) ω B] (g : SpecialPeriods.TriangleGroup) :
    letI := D.periods.totalChartedSpace
    letI := D.totalAction
    ContMDiff (modelWithCornersSelf ℂ (V × ComplexPlane₂))
      (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω (fun x : D.TotalSpace => g • x) := by
  let := D.periods.totalChartedSpace
  let := D.totalAction
  let := D.periods.coveringAction
  apply
    CoveringQuotient.contMDiff_of_comp (E := V × ComplexPlane₂) D.periods.quotientCoveringMap
      (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω
  have h := D.periods.quotientMap_holomorphic.comp (D.complexLift_holomorphic g)
  convert h using 1
  funext x
  exact (D.complexLift_quotientMap g x).symm

private def PeriodFamily.Data.BaseSpace {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction SpecialPeriods.TriangleGroup B]
    (_D : PeriodFamily.Data V B) : Type _ :=
  DiagonalQuotient.BaseSpace SpecialPeriods.TriangleGroup B

private def PeriodFamily.Data.Space {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction SpecialPeriods.TriangleGroup B]
    (D : PeriodFamily.Data V B) : Type _ :=
  @MulAction.orbitRel.Quotient SpecialPeriods.TriangleGroup D.TotalSpace _ D.totalAction

private instance PeriodFamily.Data.baseSpaceTopology {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B) :
    TopologicalSpace D.BaseSpace :=
  inferInstanceAs (TopologicalSpace (DiagonalQuotient.BaseSpace SpecialPeriods.TriangleGroup B))

private instance
    PeriodFamily.Data.spaceTopology {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction SpecialPeriods.TriangleGroup B]
    (D : PeriodFamily.Data V B) : TopologicalSpace D.Space :=
  inferInstanceAs
    (TopologicalSpace
      (@MulAction.orbitRel.Quotient SpecialPeriods.TriangleGroup D.TotalSpace _ D.totalAction))

private def PeriodFamily.Data.baseQuotient {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction SpecialPeriods.TriangleGroup B]
    (D : PeriodFamily.Data V B) : B → D.BaseSpace :=
  DiagonalQuotient.baseQuotient SpecialPeriods.TriangleGroup B

private def PeriodFamily.Data.quotient {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction SpecialPeriods.TriangleGroup B]
    (D : PeriodFamily.Data V B) : D.TotalSpace → D.Space := by
  let := SpecialPeriods.triangleTorusAction
  exact DiagonalQuotient.quotient SpecialPeriods.TriangleGroup B RealTorus₄

private def PeriodFamily.Data.projection {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction SpecialPeriods.TriangleGroup B]
    (D : PeriodFamily.Data V B) : D.Space → D.BaseSpace := by
  let := SpecialPeriods.triangleTorusAction
  exact DiagonalQuotient.projection SpecialPeriods.TriangleGroup B RealTorus₄

@[simp]
private theorem PeriodFamily.Data.projection_quotient {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B) (x : D.TotalSpace) :
    D.projection (D.quotient x) = D.baseQuotient (D.periods.projection x) :=
  rfl

private theorem PeriodFamily.Data.quotient_surjective {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B) :
    Function.Surjective D.quotient := by
  let := SpecialPeriods.triangleTorusAction
  exact DiagonalQuotient.quotient_surjective SpecialPeriods.TriangleGroup B RealTorus₄

private theorem PeriodFamily.Data.quotient_continuous {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B) :
    Continuous D.quotient := by
  let := SpecialPeriods.triangleTorusAction
  exact DiagonalQuotient.quotient_continuous SpecialPeriods.TriangleGroup B RealTorus₄

private theorem PeriodFamily.Data.projection_continuous {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B) :
    Continuous D.projection := by
  let := SpecialPeriods.triangleTorusAction
  exact DiagonalQuotient.projection_continuous SpecialPeriods.TriangleGroup B RealTorus₄

private theorem PeriodFamily.Data.quotient_isQuotientMap {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B) :
    Topology.IsQuotientMap D.quotient := by
  let := SpecialPeriods.triangleTorusAction
  exact DiagonalQuotient.quotient_isQuotientMap SpecialPeriods.TriangleGroup B RealTorus₄

private theorem
    PeriodFamily.Data.quotient_eq_iff {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction SpecialPeriods.TriangleGroup B]
    (D : PeriodFamily.Data V B) (x y : D.TotalSpace) :
    letI := D.totalAction
    D.quotient x = D.quotient y ↔ ∃ g : SpecialPeriods.TriangleGroup, g • y = x := by
  let := SpecialPeriods.triangleTorusAction
  exact DiagonalQuotient.quotient_eq_iff SpecialPeriods.TriangleGroup B RealTorus₄ x y

@[simp]
private theorem
    PeriodFamily.Data.quotient_smul {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction SpecialPeriods.TriangleGroup B]
    (D : PeriodFamily.Data V B) (g : SpecialPeriods.TriangleGroup) (x : D.TotalSpace) :
    letI := D.totalAction
    D.quotient (g • x) = D.quotient x := by
  let := SpecialPeriods.triangleTorusAction
  exact DiagonalQuotient.quotient_smul SpecialPeriods.TriangleGroup B RealTorus₄ g x

private theorem PeriodFamily.Data.quotientCoveringMap {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient SpecialPeriods.TriangleGroup) :
    letI := D.totalAction
    IsQuotientCoveringMap D.quotient SpecialPeriods.TriangleGroup := by
  let := SpecialPeriods.triangleTorusAction
  let := SpecialPeriods.triangleTorusAction_continuous
  exact DiagonalQuotient.quotientCoveringMap (F := RealTorus₄) hq

private theorem
    PeriodFamily.Data.projection_proper {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction SpecialPeriods.TriangleGroup B]
    (D : PeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient SpecialPeriods.TriangleGroup) :
    IsProperMap D.projection := by
  let := SpecialPeriods.triangleTorusAction
  let := SpecialPeriods.triangleTorusAction_continuous
  exact DiagonalQuotient.projection_proper (F := RealTorus₄) hq

private theorem PeriodFamily.Data.baseT2Space {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction SpecialPeriods.TriangleGroup B]
    (D : PeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient SpecialPeriods.TriangleGroup) [T2Space B]
    [LocallyCompactSpace B] [ProperlyDiscontinuousSMul SpecialPeriods.TriangleGroup B] :
    T2Space D.BaseSpace :=
  DiagonalQuotient.baseT2Space hq

private theorem
    PeriodFamily.Data.spaceT2Space {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction SpecialPeriods.TriangleGroup B]
    (D : PeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient SpecialPeriods.TriangleGroup)
    [T2Space D.BaseSpace] : T2Space D.Space := by
  let := SpecialPeriods.triangleTorusAction
  let := SpecialPeriods.triangleTorusAction_continuous
  let : T2Space (DiagonalQuotient.BaseSpace SpecialPeriods.TriangleGroup B) :=
    ‹T2Space D.BaseSpace›
  exact DiagonalQuotient.spaceT2Space (F := RealTorus₄) hq

private theorem PeriodFamily.Data.spaceT2Space_of_properlyDiscontinuous {V B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient SpecialPeriods.TriangleGroup) [T2Space B]
    [LocallyCompactSpace B] [ProperlyDiscontinuousSMul SpecialPeriods.TriangleGroup B] :
    T2Space D.Space := by
  let := D.baseT2Space hq
  exact D.spaceT2Space hq

private theorem PeriodFamily.Data.spaceSecondCountable {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient SpecialPeriods.TriangleGroup)
    [SecondCountableTopology B] : SecondCountableTopology D.Space := by
  let := SpecialPeriods.triangleTorusAction
  let := SpecialPeriods.triangleTorusAction_continuous
  exact DiagonalQuotient.spaceSecondCountable (F := RealTorus₄) hq

@[instance_reducible]
private def PeriodFamily.Data.chartedSpace {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction SpecialPeriods.TriangleGroup B]
    (D : PeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient SpecialPeriods.TriangleGroup) :
    ChartedSpace (V × ComplexPlane₂) D.Space := by
  let := D.periods.totalChartedSpace
  let := D.totalAction
  exact CoveringQuotient.chartedSpace (E := V × ComplexPlane₂) (D.quotientCoveringMap hq)

private theorem PeriodFamily.Data.isManifold {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction SpecialPeriods.TriangleGroup B]
    (D : PeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient SpecialPeriods.TriangleGroup)
    [IsManifold (modelWithCornersSelf ℂ V) ω B] :
    letI := D.chartedSpace hq
    IsManifold (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω D.Space := by
  let := D.periods.totalChartedSpace
  let := D.periods.totalSpace_isManifold
  let := D.totalAction
  exact CoveringQuotient.isManifold (D.quotientCoveringMap hq) ω D.totalAction_holomorphic

private theorem PeriodFamily.Data.quotient_holomorphic {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient SpecialPeriods.TriangleGroup)
    [IsManifold (modelWithCornersSelf ℂ V) ω B] :
    letI := D.periods.totalChartedSpace
    letI := D.chartedSpace hq
    ContMDiff (modelWithCornersSelf ℂ (V × ComplexPlane₂))
      (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω D.quotient := by
  let := D.periods.totalChartedSpace
  let := D.periods.totalSpace_isManifold
  let := D.totalAction
  exact CoveringQuotient.contMDiff_project (D.quotientCoveringMap hq) ω D.totalAction_holomorphic

private def PeriodFamily.Data.fibreHomeomorph {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction SpecialPeriods.TriangleGroup B]
    (D : PeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient SpecialPeriods.TriangleGroup) (b : B) :
    (D.periods.point b).Torus ≃ₜ (D.projection ⁻¹' {D.baseQuotient b}) := by
  let := SpecialPeriods.triangleTorusAction
  let := SpecialPeriods.triangleTorusAction_continuous
  exact
    (D.periods.torusHomeomorph b).symm.trans
      (DiagonalQuotient.fibreHomeomorphOver (F := RealTorus₄) hq b).symm

private def PeriodFamily.Data.zeroSection {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction SpecialPeriods.TriangleGroup B]
    (D : PeriodFamily.Data V B) : D.BaseSpace → D.Space := by
  let := D.totalAction
  refine Quotient.lift (fun b : B => D.quotient (D.periods.zeroSection b)) ?_
  rintro b b' ⟨g, hg⟩
  rw [← hg, ← D.totalAction_zeroSection, D.quotient_smul]

@[simp]
private theorem PeriodFamily.Data.zeroSection_baseQuotient {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B) (b : B) :
    D.zeroSection (D.baseQuotient b) = D.quotient (D.periods.zeroSection b) :=
  rfl

@[simp]
private theorem PeriodFamily.Data.projection_zeroSection {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B) (b : D.BaseSpace) :
    D.projection (D.zeroSection b) = b := by
  induction b using Quotient.inductionOn with
  | h b => rfl

private theorem PeriodFamily.Data.zeroSection_continuous {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B) :
    Continuous D.zeroSection := by
  exact
    isQuotientMap_quotient_mk'.continuous_iff.mpr
      (D.quotient_continuous.comp (continuous_id.prodMk continuous_const))

private theorem PeriodFamily.Data.quotient_isLocalDiffeomorph {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient SpecialPeriods.TriangleGroup)
    [IsManifold (modelWithCornersSelf ℂ V) ω B] :
    letI := D.periods.totalChartedSpace
    letI := D.chartedSpace hq
    IsLocalDiffeomorph (modelWithCornersSelf ℂ (V × ComplexPlane₂))
      (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω D.quotient := by
  let := D.periods.totalChartedSpace
  let := D.periods.totalSpace_isManifold
  let := D.totalAction
  exact
    CoveringQuotient.project_isLocalDiffeomorph (D.quotientCoveringMap hq)
      D.totalAction_holomorphic

private def PeriodFamily.regularPeriods (P : HolomorphicPeriodMap ℂ ℍ) :
    HolomorphicPeriodMap ℂ SpecialPeriods.TriangleRegularPoint
    where
  point z := P.point z.val
  holomorphic_tau :=
    P.holomorphic_tau.comp (contMDiff_subtype_val (U := SpecialPeriods.triangleRegularDomain))
  holomorphic_mu :=
    P.holomorphic_mu.comp (contMDiff_subtype_val (U := SpecialPeriods.triangleRegularDomain))
  holomorphic_beta :=
    P.holomorphic_beta.comp (contMDiff_subtype_val (U := SpecialPeriods.triangleRegularDomain))

private def PeriodFamily.regularData (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    Data ℂ SpecialPeriods.TriangleRegularPoint
    where
  periods := regularPeriods P
  base_holomorphic := SpecialPeriods.triangleRegularAction_holomorphic
  covariance₁
    z := by
    change
      P.point
          (SpecialPeriods.triangleGeometricRepresentation SpecialPeriods.triangleGenerator₁
            z.val) =
        _
    rw [SpecialPeriods.triangleGeometricRepresentation_generator₁_apply]
    exact h₁ z.val
  covariance₂
    z := by
    change
      P.point
          (SpecialPeriods.triangleGeometricRepresentation SpecialPeriods.triangleGenerator₂
            z.val) =
        _
    rw [SpecialPeriods.triangleGeometricRepresentation_generator₂_apply]
    exact h₂ z.val

private theorem PeriodFamily.regularCovering (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    IsQuotientCoveringMap (regularData P h₁ h₂).baseQuotient SpecialPeriods.TriangleGroup :=
  SpecialPeriods.triangleRegularProject_covering

end Mathoverflow1973

end
