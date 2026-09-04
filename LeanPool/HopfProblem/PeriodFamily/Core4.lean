/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology9
public import LeanPool.HopfProblem.Toric.DiagonalQuotient3
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.Lattice.Core1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology2
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology3
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.Foundations.Core3
import all LeanPool.HopfProblem.Elliptic.Core1
import all LeanPool.HopfProblem.Pi1.MappingTorus
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods2
import all LeanPool.HopfProblem.PeriodFamily.Core1
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods6
import all LeanPool.HopfProblem.Toric.DiagonalQuotient1
import all LeanPool.HopfProblem.HomologyOfX.CuspCoinvariants
import all LeanPool.HopfProblem.PeriodFamily.Core2
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods7
import all LeanPool.HopfProblem.Pi1.FundamentalGroupVanKampen2
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods8
import all LeanPool.HopfProblem.PeriodFamily.Core3
import all LeanPool.HopfProblem.Threefold.SpecialPeriods10
import all LeanPool.HopfProblem.HomologyOfX.TrianglePeriodFamilyHomologyAlgebra
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology9
import all LeanPool.HopfProblem.Toric.DiagonalQuotient3

/-!
# Hopf problem: period family · core 4

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

private theorem PeriodFamily.Boundary.clockwiseFinalLift_projection (b : Bool) (t : unitInterval) :
    SpecialPeriods.triangleRegularProject (clockwiseFinalLift b t) =
      SpecialPeriods.EllipticAttachingMeridians.clockwiseRegularMeridian b t := by
  by_cases h : PeriodFamily.Meridians.normalizationReversesMeridians = Bool.true
  · rw [clockwiseFinalLift, SpecialPeriods.EllipticAttachingMeridians.clockwiseRegularMeridian,
      ite_eq_left h, ite_eq_left h]
    exact compatibleLift_projection b t
  · rw [clockwiseFinalLift, SpecialPeriods.EllipticAttachingMeridians.clockwiseRegularMeridian,
      ite_eq_right h, ite_eq_right h]
    change
      SpecialPeriods.triangleRegularProject
          (PeriodFamily.Meridians.compatibleMeridianGenerator b •
            PeriodFamily.Meridians.compatibleMeridianLift b (unitInterval.symm t)) =
        _
    rw [SpecialPeriods.triangleRegularProject_covering.map_smul]
    exact compatibleLift_projection b (unitInterval.symm t)

private def PeriodFamily.Boundary.chosenNativeLift (j : Elliptic.Kind) :
    C(unitInterval, SpecialPeriods.TriangleRegularPoint) :=
  ⟨SpecialPeriods.Threefold.EllipticGeometry.attachingUpstairsPoint j
      (SpecialPeriods.Threefold.EllipticGeometry.chosenAttachingParameter j)
      (SpecialPeriods.Threefold.EllipticGeometry.chosenAttachingParameter_im_pos j),
    SpecialPeriods.Threefold.EllipticGeometry.attachingUpstairsPoint_continuous j _ _⟩

@[simp]
private theorem
    PeriodFamily.Boundary.chosenNativeLift_projection (j : Elliptic.Kind) (t : unitInterval) :
    SpecialPeriods.triangleRegularProject (chosenNativeLift j t) =
      SpecialPeriods.Threefold.EllipticGeometry.chosenAttachingBaseLoop j t :=
  rfl

private theorem PeriodFamily.Boundary.chosenNativeLift_one (j : Elliptic.Kind) :
    chosenNativeLift j 1 = SpecialPeriods.Triangle.ellipticGenerator j • chosenNativeLift j 0 :=
  SpecialPeriods.Threefold.EllipticGeometry.attachingUpstairsPoint_one j _ _

private def PeriodFamily.Boundary.chosenNativeSquareLift (j : Elliptic.Kind) :
    C(unitInterval × unitInterval, SpecialPeriods.TriangleRegularPoint) :=
  loopSquareLift (SpecialPeriods.Threefold.EllipticGeometry.chosenAttachingSquare j)
    (chosenNativeLift j) (chosenNativeLift_projection j)

private def
    PeriodFamily.Boundary.nativeTailFrame (j : Elliptic.Kind) : SpecialPeriods.TriangleGroup :=
  (loopSquareLift_exists_frame (SpecialPeriods.Threefold.EllipticGeometry.chosenAttachingSquare j)
      (chosenNativeLift j) (chosenNativeLift_projection j)
      PeriodFamily.Meridians.normalizedRegularMeridianBasepoint rfl).choose

private theorem PeriodFamily.Boundary.nativeTailFrame_apply (j : Elliptic.Kind) :
    chosenNativeSquareLift j (1, 0) =
      nativeTailFrame j • PeriodFamily.Meridians.normalizedRegularMeridianBasepoint :=
  (loopSquareLift_exists_frame (SpecialPeriods.Threefold.EllipticGeometry.chosenAttachingSquare j)
      (chosenNativeLift j) (chosenNativeLift_projection j)
      PeriodFamily.Meridians.normalizedRegularMeridianBasepoint rfl).choose_spec

private theorem PeriodFamily.Boundary.nativeTailFrame_relation (j : Elliptic.Kind) :
    SpecialPeriods.Triangle.ellipticGenerator j * nativeTailFrame j =
      nativeTailFrame j *
        clockwiseLiftEndpoint
          (SpecialPeriods.Threefold.EllipticGeometry.attachingMeridianIndex j) := by
  apply
    loopSquareLift_frame_relation
      (SpecialPeriods.Threefold.EllipticGeometry.chosenAttachingSquare j) (chosenNativeLift j)
      (chosenNativeLift_projection j) (SpecialPeriods.Triangle.ellipticGenerator j)
      (chosenNativeLift_one j)
      (clockwiseFinalLift (SpecialPeriods.Threefold.EllipticGeometry.attachingMeridianIndex j))
      (clockwiseFinalLift_projection
        (SpecialPeriods.Threefold.EllipticGeometry.attachingMeridianIndex j))
      (clockwiseLiftEndpoint (SpecialPeriods.Threefold.EllipticGeometry.attachingMeridianIndex j))
      (clockwiseFinalLift_one
        (SpecialPeriods.Threefold.EllipticGeometry.attachingMeridianIndex j))
      (nativeTailFrame j)
  rw [clockwiseFinalLift_zero]
  exact nativeTailFrame_apply j

private theorem PeriodFamily.Boundary.nativeTailFrame_relation_if (j : Elliptic.Kind) :
    SpecialPeriods.Triangle.ellipticGenerator j * nativeTailFrame j =
      nativeTailFrame j *
        (if PeriodFamily.Meridians.normalizationReversesMeridians then
          (SpecialPeriods.Triangle.ellipticGenerator j)⁻¹
        else SpecialPeriods.Triangle.ellipticGenerator j) := by
  have h := nativeTailFrame_relation j
  cases j <;> exact h

private def PeriodFamily.Boundary.firstCyclicCharacter :
    SpecialPeriods.TriangleGroup →* Multiplicative (ZMod 3) :=
  Monoid.Coprod.lift (MonoidHom.id _) 1

@[simp]
private theorem PeriodFamily.Boundary.firstCyclicCharacter_generator :
    firstCyclicCharacter SpecialPeriods.triangleGenerator₁ = Multiplicative.ofAdd (1 : ZMod 3) := by
  simp [firstCyclicCharacter, SpecialPeriods.triangleGenerator₁]

private theorem PeriodFamily.Boundary.firstGenerator_not_inverse_conjugate
    (d : SpecialPeriods.TriangleGroup) :
    SpecialPeriods.triangleGenerator₁ * d ≠ d * SpecialPeriods.triangleGenerator₁⁻¹ := by
  intro he
  have hm := congrArg firstCyclicCharacter he
  simp only [map_mul, map_inv, firstCyclicCharacter_generator] at hm
  rw [mul_comm (Multiplicative.ofAdd (1 : ZMod 3)) (firstCyclicCharacter d)] at hm
  have hc := mul_left_cancel hm
  have ha := congrArg (fun x : Multiplicative (ZMod 3) => x.toAdd) hc
  exact (by decide : (1 : ZMod 3) ≠ -1) ha

private theorem PeriodFamily.Boundary.normalizationReversesMeridians_false :
    PeriodFamily.Meridians.normalizationReversesMeridians = Bool.false := by
  apply Bool.eq_false_iff.mpr
  intro h
  apply firstGenerator_not_inverse_conjugate (nativeTailFrame .three)
  simpa [h, SpecialPeriods.Triangle.ellipticGenerator] using nativeTailFrame_relation_if .three

private theorem PeriodFamily.Boundary.normalizationOrientation_nonpos :
    RiemannMapping.normalizationOrientation ≤ 0 := by
  apply le_of_not_gt
  have h := normalizationReversesMeridians_false
  simpa only [PeriodFamily.Meridians.normalizationReversesMeridians,
    decide_eq_false_iff_not] using h

private theorem PeriodFamily.Boundary.nativeTailFrame_commute (j : Elliptic.Kind) :
    Commute (SpecialPeriods.Triangle.ellipticGenerator j) (nativeTailFrame j) := by
  change
    SpecialPeriods.Triangle.ellipticGenerator j * nativeTailFrame j =
      nativeTailFrame j * SpecialPeriods.Triangle.ellipticGenerator j
  have h := nativeTailFrame_relation_if j
  simpa only [normalizationReversesMeridians_false, Bool.false_eq_true, ite_false] using h

private theorem PeriodFamily.Boundary.nativeTailFrame_inv_eq_power (j : Elliptic.Kind) :
    ∃ k : ℕ,
      k < j.order ∧ (nativeTailFrame j)⁻¹ = SpecialPeriods.Triangle.ellipticGenerator j ^ k := by
  cases j
  · exact
      SpecialPeriods.triangleGenerator₁_commute_eq_pow _
        (nativeTailFrame_commute .three).inv_right
  · exact
      SpecialPeriods.triangleGenerator₂_commute_eq_pow _ (nativeTailFrame_commute .four).inv_right

private def PeriodFamily.Homology.regularOpen
    (U : TopologicalSpace.Opens SpecialPeriods.Triangle.TwicePuncturedPlane) :
    TopologicalSpace.Opens SpecialPeriods.TriangleRegularQuotient :=
  ⟨SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph ⁻¹'
      (U : Set SpecialPeriods.Triangle.TwicePuncturedPlane),
    U.isOpen.preimage SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph.continuous⟩

@[simp]
private theorem PeriodFamily.Homology.mem_regularOpen
    (U : TopologicalSpace.Opens SpecialPeriods.Triangle.TwicePuncturedPlane)
    (x : SpecialPeriods.TriangleRegularQuotient) :
    x ∈ regularOpen U ↔ SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph x ∈ U :=
  Iff.rfl

private def PeriodFamily.Homology.regularOpenHomeomorph
    (U : TopologicalSpace.Opens SpecialPeriods.Triangle.TwicePuncturedPlane) :
    regularOpen U ≃ₜ U :=
  SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph.subtype (fun _ => Iff.rfl)

private theorem PeriodFamily.Homology.regularOpen_locallyPathConnectedSpace
    (U : TopologicalSpace.Opens SpecialPeriods.Triangle.TwicePuncturedPlane) :
    LocallyPathConnectedSpace (regularOpen U) := by
  let := SpecialPeriods.Triangle.twicePuncturedPlaneDomain.isOpen.locallyPathConnectedSpace
  let := U.isOpen.locallyPathConnectedSpace
  exact (regularOpenHomeomorph U).isOpenEmbedding.locallyPathConnectedSpace

private abbrev PeriodFamily.Homology.upperBase :=
  regularOpen SpecialPeriods.Triangle.upperSlit

private abbrev PeriodFamily.Homology.lowerBase :=
  regularOpen SpecialPeriods.Triangle.lowerSlit

private abbrev PeriodFamily.Homology.overlapBase (i : Fin 3) :=
  regularOpen (SpecialPeriods.Triangle.slitOverlapStrip i)

private instance PeriodFamily.Homology.upperBase_contractibleSpace : ContractibleSpace upperBase :=
  (regularOpenHomeomorph SpecialPeriods.Triangle.upperSlit).contractibleSpace

private instance PeriodFamily.Homology.lowerBase_contractibleSpace : ContractibleSpace lowerBase :=
  (regularOpenHomeomorph SpecialPeriods.Triangle.lowerSlit).contractibleSpace

private instance PeriodFamily.Homology.overlapBase_contractibleSpace (i : Fin 3) :
    ContractibleSpace (overlapBase i) :=
  (regularOpenHomeomorph (SpecialPeriods.Triangle.slitOverlapStrip i)).contractibleSpace

private instance PeriodFamily.Homology.upperBase_locallyPathConnectedSpace :
    LocallyPathConnectedSpace upperBase :=
  regularOpen_locallyPathConnectedSpace SpecialPeriods.Triangle.upperSlit

private instance PeriodFamily.Homology.lowerBase_locallyPathConnectedSpace :
    LocallyPathConnectedSpace lowerBase :=
  regularOpen_locallyPathConnectedSpace SpecialPeriods.Triangle.lowerSlit

private theorem PeriodFamily.Homology.overlapBase_subset (i : Fin 3) :
    (overlapBase i : Set SpecialPeriods.TriangleRegularQuotient) ⊆
      (upperBase : Set SpecialPeriods.TriangleRegularQuotient) ∩ lowerBase :=
  fun _ hx => SpecialPeriods.Triangle.slitOverlapStrip_subset_overlap i hx

private theorem PeriodFamily.Homology.overlapBase_pairwise_disjoint :
    Pairwise fun i j : Fin 3 =>
      Disjoint (overlapBase i : Set SpecialPeriods.TriangleRegularQuotient) (overlapBase j) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  exact
    Set.disjoint_left.mp (SpecialPeriods.Triangle.slitOverlapStrip_pairwise_disjoint hij) hi hj

private theorem PeriodFamily.Homology.overlapBase_iUnion :
    (⋃ i : Fin 3, (overlapBase i : Set SpecialPeriods.TriangleRegularQuotient)) =
      (upperBase : Set SpecialPeriods.TriangleRegularQuotient) ∩ lowerBase := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact overlapBase_subset i hi
  · intro hx
    have hh :
      SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph x ∈
        ⋃ i : Fin 3,
          (SpecialPeriods.Triangle.slitOverlapStrip i :
            Set SpecialPeriods.Triangle.TwicePuncturedPlane) := by
      rw [SpecialPeriods.Triangle.slitOverlapStrip_iUnion]
      exact hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hh
    exact Set.mem_iUnion.mpr ⟨i, hi⟩

private def PeriodFamily.Homology.overlapBasePoint (i : Fin 3) : overlapBase i :=
  (regularOpenHomeomorph (SpecialPeriods.Triangle.slitOverlapStrip i)).symm
    (SpecialPeriods.Triangle.slitOverlapStripPoint i)

private def PeriodFamily.Homology.slitBasepoint : SpecialPeriods.TriangleRegularQuotient :=
  SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph.symm
    SpecialPeriods.Triangle.meridianBasepoint

@[simp]
private theorem PeriodFamily.Homology.slitBasepoint_coordinate :
    SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph slitBasepoint =
      SpecialPeriods.Triangle.meridianBasepoint :=
  SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph.apply_symm_apply
    SpecialPeriods.Triangle.meridianBasepoint

private theorem PeriodFamily.Homology.slitBasepoint_mem_upper : slitBasepoint ∈ upperBase := by
  rw [mem_regularOpen, slitBasepoint_coordinate]
  change (1 / 2 : ℂ) ∈ SpecialPeriods.Triangle.upperSlitPlane
  norm_num [SpecialPeriods.Triangle.upperSlitPlane]

private theorem PeriodFamily.Homology.slitBasepoint_mem_lower : slitBasepoint ∈ lowerBase := by
  rw [mem_regularOpen, slitBasepoint_coordinate]
  change (1 / 2 : ℂ) ∈ SpecialPeriods.Triangle.lowerSlitPlane
  norm_num [SpecialPeriods.Triangle.lowerSlitPlane]

private def PeriodFamily.Homology.upperBasePoint : upperBase :=
  ⟨slitBasepoint, slitBasepoint_mem_upper⟩

private def PeriodFamily.Homology.lowerBasePoint : lowerBase :=
  ⟨slitBasepoint, slitBasepoint_mem_lower⟩

private abbrev PeriodFamily.Homology.SlitBaseLift :=
  SpecialPeriods.triangleRegularProject ⁻¹'
    ({ slitBasepoint } : Set SpecialPeriods.TriangleRegularQuotient)

private def PeriodFamily.Homology.upperBaseInclusion :
    C(upperBase, SpecialPeriods.TriangleRegularQuotient) :=
  ⟨Subtype.val, continuous_subtype_val⟩

private def PeriodFamily.Homology.lowerBaseInclusion :
    C(lowerBase, SpecialPeriods.TriangleRegularQuotient) :=
  ⟨Subtype.val, continuous_subtype_val⟩

private theorem PeriodFamily.Homology.upperLift_existsUnique (b : SlitBaseLift) :
    ∃! s : C(upperBase, SpecialPeriods.TriangleRegularPoint),
      s upperBasePoint = b.val ∧ SpecialPeriods.triangleRegularProject ∘ s = upperBaseInclusion :=
  SpecialPeriods.triangleRegularProject_covering.isCoveringMap.existsUnique_continuousMap_lifts
    upperBaseInclusion upperBasePoint b.val b.property

private theorem PeriodFamily.Homology.lowerLift_existsUnique (b : SlitBaseLift) :
    ∃! s : C(lowerBase, SpecialPeriods.TriangleRegularPoint),
      s lowerBasePoint = b.val ∧ SpecialPeriods.triangleRegularProject ∘ s = lowerBaseInclusion :=
  SpecialPeriods.triangleRegularProject_covering.isCoveringMap.existsUnique_continuousMap_lifts
    lowerBaseInclusion lowerBasePoint b.val b.property

private def PeriodFamily.Homology.upperLift (b : SlitBaseLift) :
    C(upperBase, SpecialPeriods.TriangleRegularPoint) :=
  (upperLift_existsUnique b).choose

private def PeriodFamily.Homology.lowerLift (b : SlitBaseLift) :
    C(lowerBase, SpecialPeriods.TriangleRegularPoint) :=
  (lowerLift_existsUnique b).choose

@[simp]
private theorem PeriodFamily.Homology.upperLift_basepoint (b : SlitBaseLift) :
    upperLift b upperBasePoint = b.val :=
  (upperLift_existsUnique b).choose_spec.1.1

@[simp]
private theorem PeriodFamily.Homology.lowerLift_basepoint (b : SlitBaseLift) :
    lowerLift b lowerBasePoint = b.val :=
  (lowerLift_existsUnique b).choose_spec.1.1

@[simp]
private theorem PeriodFamily.Homology.upperLift_project (b : SlitBaseLift) (x : upperBase) :
    SpecialPeriods.triangleRegularProject (upperLift b x) = x.val :=
  congrFun (upperLift_existsUnique b).choose_spec.1.2 x

@[simp]
private theorem PeriodFamily.Homology.lowerLift_project (b : SlitBaseLift) (x : lowerBase) :
    SpecialPeriods.triangleRegularProject (lowerLift b x) = x.val :=
  congrFun (lowerLift_existsUnique b).choose_spec.1.2 x

private def PeriodFamily.Homology.overlapToUpper (i : Fin 3) : C(overlapBase i, upperBase) :=
  ⟨fun x => ⟨x.val, (overlapBase_subset i x.property).1⟩, by fun_prop⟩

private def PeriodFamily.Homology.overlapToLower (i : Fin 3) : C(overlapBase i, lowerBase) :=
  ⟨fun x => ⟨x.val, (overlapBase_subset i x.property).2⟩, by fun_prop⟩

private def PeriodFamily.Homology.upperLiftOnOverlap (b : SlitBaseLift) (i : Fin 3) :
    C(overlapBase i, SpecialPeriods.TriangleRegularPoint) :=
  (upperLift b).comp (overlapToUpper i)

private def PeriodFamily.Homology.lowerLiftOnOverlap (b : SlitBaseLift) (i : Fin 3) :
    C(overlapBase i, SpecialPeriods.TriangleRegularPoint) :=
  (lowerLift b).comp (overlapToLower i)

@[simp]
private theorem PeriodFamily.Homology.upperLiftOnOverlap_project (b : SlitBaseLift) (i : Fin 3)
    (x : overlapBase i) :
    SpecialPeriods.triangleRegularProject (upperLiftOnOverlap b i x) = x.val :=
  upperLift_project b (overlapToUpper i x)

@[simp]
private theorem PeriodFamily.Homology.lowerLiftOnOverlap_project (b : SlitBaseLift) (i : Fin 3)
    (x : overlapBase i) :
    SpecialPeriods.triangleRegularProject (lowerLiftOnOverlap b i x) = x.val :=
  lowerLift_project b (overlapToLower i x)

private theorem PeriodFamily.Homology.overlapTransition_exists (b : SlitBaseLift) (i : Fin 3) :
    ∃ g : SpecialPeriods.TriangleGroup,
      g • upperLiftOnOverlap b i (overlapBasePoint i) =
        lowerLiftOnOverlap b i (overlapBasePoint i) := by
  apply SpecialPeriods.triangleRegularProject_covering.apply_eq_iff_mem_orbit.mp
  rw [upperLiftOnOverlap_project, lowerLiftOnOverlap_project]

private def PeriodFamily.Homology.overlapTransition (b : SlitBaseLift) (i : Fin 3) :
    SpecialPeriods.TriangleGroup :=
  (overlapTransition_exists b i).choose

private theorem PeriodFamily.Homology.overlapTransition_at_point (b : SlitBaseLift) (i : Fin 3) :
    overlapTransition b i • upperLiftOnOverlap b i (overlapBasePoint i) =
      lowerLiftOnOverlap b i (overlapBasePoint i) :=
  (overlapTransition_exists b i).choose_spec

private theorem PeriodFamily.Homology.overlapTransition_apply (b : SlitBaseLift) (i : Fin 3)
    (x : overlapBase i) :
    overlapTransition b i • upperLiftOnOverlap b i x = lowerLiftOnOverlap b i x := by
  have he :
    (fun y => overlapTransition b i • upperLiftOnOverlap b i y) = lowerLiftOnOverlap b i := by
    apply
      SpecialPeriods.triangleRegularProject_covering.isCoveringMap.eq_of_comp_eq
        ((SpecialPeriods.triangleRegularProject_covering.continuous_const_smul _).comp
          (upperLiftOnOverlap b i).continuous)
        (lowerLiftOnOverlap b i).continuous
    · funext y
      change
        SpecialPeriods.triangleRegularProject (overlapTransition b i • upperLiftOnOverlap b i y) =
          SpecialPeriods.triangleRegularProject (lowerLiftOnOverlap b i y)
      rw [SpecialPeriods.triangleRegularProject_covering.map_smul, upperLiftOnOverlap_project,
        lowerLiftOnOverlap_project]
    · exact overlapTransition_at_point b i
  exact congrFun he x

private theorem PeriodFamily.Homology.overlapTransition_eq_of_apply (b : SlitBaseLift) (i : Fin 3)
    (g : SpecialPeriods.TriangleGroup) (x : overlapBase i)
    (hg : g • upperLiftOnOverlap b i x = lowerLiftOnOverlap b i x) : overlapTransition b i = g := by
  let := SpecialPeriods.triangleRegularProject_covering.isCancelSMul
  exact
    IsCancelSMul.right_cancel _ _ (upperLiftOnOverlap b i x)
      ((overlapTransition_apply b i x).trans hg.symm)

private def PeriodFamily.Homology.middleOverlapPoint : overlapBase 1 := by
  refine ⟨slitBasepoint, ?_⟩
  rw [mem_regularOpen, slitBasepoint_coordinate]
  change (1 / 2 : ℂ) ∈ SpecialPeriods.Triangle.overlapStrip 1
  norm_num [SpecialPeriods.Triangle.overlapStrip]

@[simp]
private theorem PeriodFamily.Homology.upperLift_middleOverlapPoint (b : SlitBaseLift) :
    upperLiftOnOverlap b 1 middleOverlapPoint = b.val :=
  upperLift_basepoint b

@[simp]
private theorem PeriodFamily.Homology.lowerLift_middleOverlapPoint (b : SlitBaseLift) :
    lowerLiftOnOverlap b 1 middleOverlapPoint = b.val :=
  lowerLift_basepoint b

@[simp]
private theorem PeriodFamily.Homology.overlapTransition_middle (b : SlitBaseLift) :
    overlapTransition b 1 = 1 := by
  apply overlapTransition_eq_of_apply b 1 1 middleOverlapPoint
  rw [one_smul, upperLift_middleOverlapPoint, lowerLift_middleOverlapPoint]

private def PeriodFamily.Homology.normalizedSlitBaseLift : SlitBaseLift :=
  ⟨PeriodFamily.Meridians.normalizedRegularMeridianBasepoint,
    by
    change
      SpecialPeriods.triangleRegularProject
          PeriodFamily.Meridians.normalizedRegularMeridianBasepoint =
        slitBasepoint
    apply SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph.injective
    rw [PeriodFamily.Meridians.normalizedRegularMeridianBasepoint_coordinate,
      slitBasepoint_coordinate]⟩

@[simp]
private theorem PeriodFamily.Homology.normalizedSlitBaseLift_val :
    normalizedSlitBaseLift.val = PeriodFamily.Meridians.normalizedRegularMeridianBasepoint :=
  rfl

private theorem PeriodFamily.Homology.upperLift_path (b : SlitBaseLift)
    {z : SpecialPeriods.TriangleRegularPoint} (p : Path b.val z)
    (hp : ∀ t, SpecialPeriods.triangleRegularProject (p t) ∈ upperBase) (t : unitInterval) :
    upperLift b ⟨SpecialPeriods.triangleRegularProject (p t), hp t⟩ = p t := by
  let q : C(unitInterval, upperBase) :=
    ⟨fun s => ⟨SpecialPeriods.triangleRegularProject (p s), hp s⟩,
      (SpecialPeriods.triangleRegularProject_covering.continuous.comp p.continuous).subtype_mk hp⟩
  have hq : q 0 = upperBasePoint := by
    apply Subtype.ext
    change SpecialPeriods.triangleRegularProject (p 0) = slitBasepoint
    rw [p.source]
    exact b.property
  have h :
    (fun s => upperLift b (q s)) = (p : unitInterval → SpecialPeriods.TriangleRegularPoint) := by
    refine
      SpecialPeriods.triangleRegularProject_covering.isCoveringMap.eq_of_comp_eq
        ((upperLift b).continuous.comp q.continuous) p.continuous ?_ (0 : unitInterval) ?_
    · funext s
      exact upperLift_project b (q s)
    · rw [hq, upperLift_basepoint, p.source]
  exact congrFun h t

private theorem PeriodFamily.Homology.lowerLift_path (b : SlitBaseLift)
    {z : SpecialPeriods.TriangleRegularPoint} (p : Path b.val z)
    (hp : ∀ t, SpecialPeriods.triangleRegularProject (p t) ∈ lowerBase) (t : unitInterval) :
    lowerLift b ⟨SpecialPeriods.triangleRegularProject (p t), hp t⟩ = p t := by
  let q : C(unitInterval, lowerBase) :=
    ⟨fun s => ⟨SpecialPeriods.triangleRegularProject (p s), hp s⟩,
      (SpecialPeriods.triangleRegularProject_covering.continuous.comp p.continuous).subtype_mk hp⟩
  have hq : q 0 = lowerBasePoint := by
    apply Subtype.ext
    change SpecialPeriods.triangleRegularProject (p 0) = slitBasepoint
    rw [p.source]
    exact b.property
  have h :
    (fun s => lowerLift b (q s)) = (p : unitInterval → SpecialPeriods.TriangleRegularPoint) := by
    refine
      SpecialPeriods.triangleRegularProject_covering.isCoveringMap.eq_of_comp_eq
        ((lowerLift b).continuous.comp q.continuous) p.continuous ?_ (0 : unitInterval) ?_
    · funext s
      exact lowerLift_project b (q s)
    · rw [hq, lowerLift_basepoint, p.source]
  exact congrFun h t

private theorem PeriodFamily.Homology.upperLift_endpoint (b : SlitBaseLift) (x : upperBase)
    {z : SpecialPeriods.TriangleRegularPoint} (p : Path b.val z)
    (hp : ∀ t, SpecialPeriods.triangleRegularProject (p t) ∈ upperBase)
    (hx : x.val = SpecialPeriods.triangleRegularProject z) : upperLift b x = z := by
  have hx' : x = ⟨SpecialPeriods.triangleRegularProject (p 1), hp 1⟩ :=
    Subtype.ext (hx.trans (congrArg SpecialPeriods.triangleRegularProject p.target.symm))
  calc
    upperLift b x = upperLift b ⟨SpecialPeriods.triangleRegularProject (p 1), hp 1⟩ :=
      congrArg (upperLift b) hx'
    _ = p 1 := (upperLift_path b p hp 1)
    _ = z := p.target

private theorem PeriodFamily.Homology.lowerLift_endpoint (b : SlitBaseLift) (x : lowerBase)
    {z : SpecialPeriods.TriangleRegularPoint} (p : Path b.val z)
    (hp : ∀ t, SpecialPeriods.triangleRegularProject (p t) ∈ lowerBase)
    (hx : x.val = SpecialPeriods.triangleRegularProject z) : lowerLift b x = z := by
  have hx' : x = ⟨SpecialPeriods.triangleRegularProject (p 1), hp 1⟩ :=
    Subtype.ext (hx.trans (congrArg SpecialPeriods.triangleRegularProject p.target.symm))
  calc
    lowerLift b x = lowerLift b ⟨SpecialPeriods.triangleRegularProject (p 1), hp 1⟩ :=
      congrArg (lowerLift b) hx'
    _ = p 1 := (lowerLift_path b p hp 1)
    _ = z := p.target

private def PeriodFamily.Homology.meridianLeftOverlapPoint : overlapBase 0 := by
  refine
    ⟨SpecialPeriods.triangleRegularProject
        PeriodFamily.Meridians.normalizedRegularMeridianLeftPoint,
      ?_⟩
  rw [mem_regularOpen, PeriodFamily.Meridians.normalizedRegularMeridianLeftPoint_coordinate]
  change (-1 / 2 : ℂ) ∈ SpecialPeriods.Triangle.overlapStrip 0
  norm_num [SpecialPeriods.Triangle.overlapStrip]

private def PeriodFamily.Homology.meridianRightOverlapPoint : overlapBase 2 := by
  refine
    ⟨SpecialPeriods.triangleRegularProject
        PeriodFamily.Meridians.normalizedRegularMeridianRightPoint,
      ?_⟩
  rw [mem_regularOpen, PeriodFamily.Meridians.normalizedRegularMeridianRightPoint_coordinate]
  change (3 / 2 : ℂ) ∈ SpecialPeriods.Triangle.overlapStrip 2
  norm_num [SpecialPeriods.Triangle.overlapStrip]

private def PeriodFamily.Homology.normalizedOverlapTransition (i : Fin 3) :
    SpecialPeriods.TriangleGroup :=
  overlapTransition normalizedSlitBaseLift i

private theorem PeriodFamily.Homology.normalizedOverlapTransition_left_of_pos
    (ho : 0 < RiemannMapping.normalizationOrientation) :
    normalizedOverlapTransition 0 = SpecialPeriods.triangleGenerator₁⁻¹ := by
  apply
    overlapTransition_eq_of_apply normalizedSlitBaseLift 0 SpecialPeriods.triangleGenerator₁⁻¹
      meridianLeftOverlapPoint
  have hU :
    upperLiftOnOverlap normalizedSlitBaseLift 0 meridianLeftOverlapPoint =
      PeriodFamily.Meridians.normalizedRegularMeridianLeftPoint := by
    change
      upperLift normalizedSlitBaseLift
          ⟨SpecialPeriods.triangleRegularProject
              PeriodFamily.Meridians.normalizedRegularMeridianLeftPoint,
            _⟩ =
        _
    have hp (t : unitInterval) :
      SpecialPeriods.triangleRegularProject (PeriodFamily.Meridians.liftedZeroHalfPath t) ∈
        upperBase := by
      rw [mem_regularOpen, PeriodFamily.Meridians.liftedZeroHalfPath_coordinate,
        PeriodFamily.Meridians.zeroHalfPath, ite_eq_left ho]
      exact SpecialPeriods.Triangle.upperZeroPath_mem_upperSlitPlane t
    apply upperLift_endpoint normalizedSlitBaseLift _ PeriodFamily.Meridians.liftedZeroHalfPath hp
    rfl
  have hL :
    lowerLiftOnOverlap normalizedSlitBaseLift 0 meridianLeftOverlapPoint =
      SpecialPeriods.triangleGenerator₁⁻¹ •
        PeriodFamily.Meridians.normalizedRegularMeridianLeftPoint := by
    change
      lowerLift normalizedSlitBaseLift
          ⟨SpecialPeriods.triangleRegularProject
              PeriodFamily.Meridians.normalizedRegularMeridianLeftPoint,
            _⟩ =
        _
    have hp (t : unitInterval) :
      SpecialPeriods.triangleRegularProject (PeriodFamily.Meridians.reflectedZeroHalfPath t) ∈
        lowerBase := by
      rw [mem_regularOpen, PeriodFamily.Meridians.reflectedZeroHalfPath_coordinate,
        PeriodFamily.Meridians.oppositeZeroPath, ite_eq_left ho]
      exact SpecialPeriods.Triangle.lowerZeroPath_mem_lowerSlitPlane t
    apply
      lowerLift_endpoint normalizedSlitBaseLift _ PeriodFamily.Meridians.reflectedZeroHalfPath hp
    exact (SpecialPeriods.triangleRegularProject_covering.map_smul _).symm
  rw [hU, hL]

private theorem PeriodFamily.Homology.normalizedOverlapTransition_left_of_nonpos
    (ho : RiemannMapping.normalizationOrientation ≤ 0) :
    normalizedOverlapTransition 0 = SpecialPeriods.triangleGenerator₁ := by
  have hn : ¬0 < RiemannMapping.normalizationOrientation := not_lt.mpr ho
  apply
    overlapTransition_eq_of_apply normalizedSlitBaseLift 0 SpecialPeriods.triangleGenerator₁
      meridianLeftOverlapPoint
  have hU :
    upperLiftOnOverlap normalizedSlitBaseLift 0 meridianLeftOverlapPoint =
      SpecialPeriods.triangleGenerator₁⁻¹ •
        PeriodFamily.Meridians.normalizedRegularMeridianLeftPoint := by
    change
      upperLift normalizedSlitBaseLift
          ⟨SpecialPeriods.triangleRegularProject
              PeriodFamily.Meridians.normalizedRegularMeridianLeftPoint,
            _⟩ =
        _
    have hp (t : unitInterval) :
      SpecialPeriods.triangleRegularProject (PeriodFamily.Meridians.reflectedZeroHalfPath t) ∈
        upperBase := by
      rw [mem_regularOpen, PeriodFamily.Meridians.reflectedZeroHalfPath_coordinate,
        PeriodFamily.Meridians.oppositeZeroPath, ite_eq_right hn]
      exact SpecialPeriods.Triangle.upperZeroPath_mem_upperSlitPlane t
    apply
      upperLift_endpoint normalizedSlitBaseLift _ PeriodFamily.Meridians.reflectedZeroHalfPath hp
    exact (SpecialPeriods.triangleRegularProject_covering.map_smul _).symm
  have hL :
    lowerLiftOnOverlap normalizedSlitBaseLift 0 meridianLeftOverlapPoint =
      PeriodFamily.Meridians.normalizedRegularMeridianLeftPoint := by
    change
      lowerLift normalizedSlitBaseLift
          ⟨SpecialPeriods.triangleRegularProject
              PeriodFamily.Meridians.normalizedRegularMeridianLeftPoint,
            _⟩ =
        _
    have hp (t : unitInterval) :
      SpecialPeriods.triangleRegularProject (PeriodFamily.Meridians.liftedZeroHalfPath t) ∈
        lowerBase := by
      rw [mem_regularOpen, PeriodFamily.Meridians.liftedZeroHalfPath_coordinate,
        PeriodFamily.Meridians.zeroHalfPath, ite_eq_right hn]
      exact SpecialPeriods.Triangle.lowerZeroPath_mem_lowerSlitPlane t
    apply lowerLift_endpoint normalizedSlitBaseLift _ PeriodFamily.Meridians.liftedZeroHalfPath hp
    rfl
  rw [hU, hL, smul_inv_smul]

private theorem PeriodFamily.Homology.normalizedOverlapTransition_right_of_pos
    (ho : 0 < RiemannMapping.normalizationOrientation) :
    normalizedOverlapTransition 2 = SpecialPeriods.triangleGenerator₂ := by
  apply
    overlapTransition_eq_of_apply normalizedSlitBaseLift 2 SpecialPeriods.triangleGenerator₂
      meridianRightOverlapPoint
  have hU :
    upperLiftOnOverlap normalizedSlitBaseLift 2 meridianRightOverlapPoint =
      PeriodFamily.Meridians.normalizedRegularMeridianRightPoint := by
    change
      upperLift normalizedSlitBaseLift
          ⟨SpecialPeriods.triangleRegularProject
              PeriodFamily.Meridians.normalizedRegularMeridianRightPoint,
            _⟩ =
        _
    have hp (t : unitInterval) :
      SpecialPeriods.triangleRegularProject (PeriodFamily.Meridians.liftedOneHalfPath t) ∈
        upperBase := by
      rw [mem_regularOpen, PeriodFamily.Meridians.liftedOneHalfPath_coordinate,
        PeriodFamily.Meridians.oneHalfPath, ite_eq_left ho]
      exact SpecialPeriods.Triangle.upperOnePath_mem_upperSlitPlane t
    apply upperLift_endpoint normalizedSlitBaseLift _ PeriodFamily.Meridians.liftedOneHalfPath hp
    rfl
  have hL :
    lowerLiftOnOverlap normalizedSlitBaseLift 2 meridianRightOverlapPoint =
      SpecialPeriods.triangleGenerator₂ •
        PeriodFamily.Meridians.normalizedRegularMeridianRightPoint := by
    change
      lowerLift normalizedSlitBaseLift
          ⟨SpecialPeriods.triangleRegularProject
              PeriodFamily.Meridians.normalizedRegularMeridianRightPoint,
            _⟩ =
        _
    have hp (t : unitInterval) :
      SpecialPeriods.triangleRegularProject (PeriodFamily.Meridians.reflectedOneHalfPath t) ∈
        lowerBase := by
      rw [mem_regularOpen, PeriodFamily.Meridians.reflectedOneHalfPath_coordinate,
        PeriodFamily.Meridians.oppositeOnePath, ite_eq_left ho]
      exact SpecialPeriods.Triangle.lowerOnePath_mem_lowerSlitPlane t
    apply
      lowerLift_endpoint normalizedSlitBaseLift _ PeriodFamily.Meridians.reflectedOneHalfPath hp
    exact (SpecialPeriods.triangleRegularProject_covering.map_smul _).symm
  rw [hU, hL]

private theorem PeriodFamily.Homology.normalizedOverlapTransition_right_of_nonpos
    (ho : RiemannMapping.normalizationOrientation ≤ 0) :
    normalizedOverlapTransition 2 = SpecialPeriods.triangleGenerator₂⁻¹ := by
  have hn : ¬0 < RiemannMapping.normalizationOrientation := not_lt.mpr ho
  apply
    overlapTransition_eq_of_apply normalizedSlitBaseLift 2 SpecialPeriods.triangleGenerator₂⁻¹
      meridianRightOverlapPoint
  have hU :
    upperLiftOnOverlap normalizedSlitBaseLift 2 meridianRightOverlapPoint =
      SpecialPeriods.triangleGenerator₂ •
        PeriodFamily.Meridians.normalizedRegularMeridianRightPoint := by
    change
      upperLift normalizedSlitBaseLift
          ⟨SpecialPeriods.triangleRegularProject
              PeriodFamily.Meridians.normalizedRegularMeridianRightPoint,
            _⟩ =
        _
    have hp (t : unitInterval) :
      SpecialPeriods.triangleRegularProject (PeriodFamily.Meridians.reflectedOneHalfPath t) ∈
        upperBase := by
      rw [mem_regularOpen, PeriodFamily.Meridians.reflectedOneHalfPath_coordinate,
        PeriodFamily.Meridians.oppositeOnePath, ite_eq_right hn]
      exact SpecialPeriods.Triangle.upperOnePath_mem_upperSlitPlane t
    apply
      upperLift_endpoint normalizedSlitBaseLift _ PeriodFamily.Meridians.reflectedOneHalfPath hp
    exact (SpecialPeriods.triangleRegularProject_covering.map_smul _).symm
  have hL :
    lowerLiftOnOverlap normalizedSlitBaseLift 2 meridianRightOverlapPoint =
      PeriodFamily.Meridians.normalizedRegularMeridianRightPoint := by
    change
      lowerLift normalizedSlitBaseLift
          ⟨SpecialPeriods.triangleRegularProject
              PeriodFamily.Meridians.normalizedRegularMeridianRightPoint,
            _⟩ =
        _
    have hp (t : unitInterval) :
      SpecialPeriods.triangleRegularProject (PeriodFamily.Meridians.liftedOneHalfPath t) ∈
        lowerBase := by
      rw [mem_regularOpen, PeriodFamily.Meridians.liftedOneHalfPath_coordinate,
        PeriodFamily.Meridians.oneHalfPath, ite_eq_right hn]
      exact SpecialPeriods.Triangle.lowerOnePath_mem_lowerSlitPlane t
    apply lowerLift_endpoint normalizedSlitBaseLift _ PeriodFamily.Meridians.liftedOneHalfPath hp
    rfl
  rw [hU, hL, inv_smul_smul]

private theorem
    PeriodFamily.Homology.normalizedOverlapTransition_apply (i : Fin 3) (x : overlapBase i) :
    normalizedOverlapTransition i • upperLiftOnOverlap normalizedSlitBaseLift i x =
      lowerLiftOnOverlap normalizedSlitBaseLift i x :=
  overlapTransition_apply normalizedSlitBaseLift i x

private def PeriodFamily.Homology.triangleHomologyEquiv (g : SpecialPeriods.TriangleGroup) (n : ℕ) :
    SingularMayerVietoris.SingularHomology RealTorus₄ n ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology RealTorus₄ n :=
  PeriodTorusHigherHomology.homeomorphHomologyEquiv (SpecialPeriods.triangleTorusHomeomorph g) n

@[simp]
private theorem PeriodFamily.Homology.triangleHomologyEquiv_one (n : ℕ) :
    triangleHomologyEquiv 1 n =
      LinearEquiv.refl ℤ (SingularMayerVietoris.SingularHomology RealTorus₄ n) := by
  rw [triangleHomologyEquiv, SpecialPeriods.triangleTorusHomeomorph_one,
    PeriodTorusHigherHomology.homeomorphHomologyEquiv_refl]

@[simp]
private theorem PeriodFamily.Homology.triangleHomologyEquiv_inv (g : SpecialPeriods.TriangleGroup)
    (n : ℕ) : triangleHomologyEquiv g⁻¹ n = (triangleHomologyEquiv g n).symm := by
  rw [triangleHomologyEquiv, SpecialPeriods.triangleTorusHomeomorph_inv]
  exact
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv_symm
        (SpecialPeriods.triangleTorusHomeomorph g) n).symm

private theorem
    PeriodFamily.Homology.triangleHomologyEquiv_zero (g : SpecialPeriods.TriangleGroup) :
    triangleHomologyEquiv g 0 =
      LinearEquiv.refl ℤ (SingularMayerVietoris.SingularHomology RealTorus₄ 0) := by
  apply LinearEquiv.ext
  intro a
  apply (PeriodTorusHigherHomology.connectedHomologyZeroEquiv RealTorus₄).injective
  exact
    PeriodTorusHigherHomology.connectedHomologyZeroEquiv_natural
      (SpecialPeriods.triangleTorusHomeomorph g : C(RealTorus₄, RealTorus₄)) a

private def PeriodFamily.Homology.overlapHomologyAction (b : SlitBaseLift) (i : Fin 3) (n : ℕ) :
    SingularMayerVietoris.SingularHomology RealTorus₄ n →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology RealTorus₄ n :=
  (triangleHomologyEquiv (overlapTransition b i) n).toLinearMap

private def PeriodFamily.Homology.generatorHomologyEquiv (j : Bool) (n : ℕ) :
    SingularMayerVietoris.SingularHomology RealTorus₄ n ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology RealTorus₄ n :=
  triangleHomologyEquiv
    (if j then SpecialPeriods.triangleGenerator₂ else SpecialPeriods.triangleGenerator₁) n

private def PeriodFamily.Homology.sourceDifference (n : ℕ) :
    (SingularMayerVietoris.SingularHomology RealTorus₄ n ×
        SingularMayerVietoris.SingularHomology RealTorus₄ n) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology RealTorus₄ n :=
  TrianglePeriodFamilyHomologyAlgebra.delta (generatorHomologyEquiv Bool.false n).toLinearMap
    (generatorHomologyEquiv Bool.true n).toLinearMap

private def PeriodFamily.Homology.slitDifference (b : SlitBaseLift) (n : ℕ) :
    (SingularMayerVietoris.SingularHomology RealTorus₄ n ×
        SingularMayerVietoris.SingularHomology RealTorus₄ n) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology RealTorus₄ n :=
  TrianglePeriodFamilyHomologyAlgebra.delta (overlapHomologyAction b 0 n)
    (overlapHomologyAction b 2 n)

private abbrev PeriodFamily.Homology.normalizedSlitDifference (n : ℕ) :=
  slitDifference normalizedSlitBaseLift n

private theorem PeriodFamily.Homology.normalizedSlitDifference_of_pos (n : ℕ)
    (ho : 0 < RiemannMapping.normalizationOrientation) :
    normalizedSlitDifference n =
      TrianglePeriodFamilyHomologyAlgebra.delta
        (generatorHomologyEquiv Bool.false n).symm.toLinearMap
        (generatorHomologyEquiv Bool.true n).toLinearMap := by
  change
    TrianglePeriodFamilyHomologyAlgebra.delta
        (triangleHomologyEquiv (normalizedOverlapTransition 0) n).toLinearMap
        (triangleHomologyEquiv (normalizedOverlapTransition 2) n).toLinearMap =
      _
  rw [normalizedOverlapTransition_left_of_pos ho, normalizedOverlapTransition_right_of_pos ho,
    triangleHomologyEquiv_inv]
  rfl

private theorem PeriodFamily.Homology.normalizedSlitDifference_of_nonpos (n : ℕ)
    (ho : RiemannMapping.normalizationOrientation ≤ 0) :
    normalizedSlitDifference n =
      TrianglePeriodFamilyHomologyAlgebra.delta (generatorHomologyEquiv Bool.false n).toLinearMap
        (generatorHomologyEquiv Bool.true n).symm.toLinearMap := by
  change
    TrianglePeriodFamilyHomologyAlgebra.delta
        (triangleHomologyEquiv (normalizedOverlapTransition 0) n).toLinearMap
        (triangleHomologyEquiv (normalizedOverlapTransition 2) n).toLinearMap =
      _
  rw [normalizedOverlapTransition_left_of_nonpos ho,
    normalizedOverlapTransition_right_of_nonpos ho, triangleHomologyEquiv_inv]
  rfl

private def PeriodFamily.Homology.normalizedSourceDomainEquiv (n : ℕ) :
    (SingularMayerVietoris.SingularHomology RealTorus₄ n ×
        SingularMayerVietoris.SingularHomology RealTorus₄ n) ≃ₗ[ℤ]
      (SingularMayerVietoris.SingularHomology RealTorus₄ n ×
        SingularMayerVietoris.SingularHomology RealTorus₄ n) :=
  if 0 < RiemannMapping.normalizationOrientation then
    TrianglePeriodFamilyHomologyAlgebra.inverseFirstCoordinate
      (generatorHomologyEquiv Bool.false n)
  else
    TrianglePeriodFamilyHomologyAlgebra.inverseSecondCoordinate
      (generatorHomologyEquiv Bool.true n)

private theorem PeriodFamily.Homology.sourceDifference_coordinate_change (n : ℕ)
    (x :
      SingularMayerVietoris.SingularHomology RealTorus₄ n ×
        SingularMayerVietoris.SingularHomology RealTorus₄ n) :
    sourceDifference n (normalizedSourceDomainEquiv n x) = normalizedSlitDifference n x := by
  by_cases ho : 0 < RiemannMapping.normalizationOrientation
  · rw [normalizedSourceDomainEquiv, ite_eq_left ho, normalizedSlitDifference_of_pos n ho]
    exact
      TrianglePeriodFamilyHomologyAlgebra.delta_inverse_first
        (generatorHomologyEquiv Bool.false n) (generatorHomologyEquiv Bool.true n).toLinearMap x
  · rw [normalizedSourceDomainEquiv, ite_eq_right ho,
      normalizedSlitDifference_of_nonpos n (le_of_not_gt ho)]
    exact
      TrianglePeriodFamilyHomologyAlgebra.delta_inverse_second
        (generatorHomologyEquiv Bool.false n).toLinearMap (generatorHomologyEquiv Bool.true n) x

private theorem PeriodFamily.Homology.normalizedSlitDifference_range (n : ℕ) :
    LinearMap.range (normalizedSlitDifference n) = LinearMap.range (sourceDifference n) :=
  TrianglePeriodFamilyHomologyAlgebra.range_eq_of_coordinates _ _ (normalizedSourceDomainEquiv n)
    (sourceDifference_coordinate_change n)

private def PeriodFamily.Homology.normalizedSlitKernelEquiv (n : ℕ) :
    LinearMap.ker (normalizedSlitDifference n) ≃ₗ[ℤ] LinearMap.ker (sourceDifference n) :=
  TrianglePeriodFamilyHomologyAlgebra.kernelEquivOfCoordinates _ _ (normalizedSourceDomainEquiv n)
    (sourceDifference_coordinate_change n)

private def PeriodFamily.Homology.normalizedSlitCokernelEquiv (n : ℕ) :
    (SingularMayerVietoris.SingularHomology RealTorus₄ n ⧸
        LinearMap.range (normalizedSlitDifference n)) ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology RealTorus₄ n ⧸
        LinearMap.range (sourceDifference n) :=
  TrianglePeriodFamilyHomologyAlgebra.integralQuotientCongr (H :=
    SingularMayerVietoris.SingularHomology RealTorus₄ n)
    (LinearMap.range (normalizedSlitDifference n)) (LinearMap.range (sourceDifference n))
    (normalizedSlitDifference_range n)

@[simp]
private theorem PeriodFamily.Homology.normalizedSlitCokernelEquiv_mk (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ n) :
    normalizedSlitCokernelEquiv n (Submodule.Quotient.mk a) = Submodule.Quotient.mk a :=
  rfl

@[simp]
private theorem PeriodFamily.Homology.sourceDifference_zero : sourceDifference 0 = 0 := by
  apply LinearMap.ext
  intro x
  change
    (triangleHomologyEquiv SpecialPeriods.triangleGenerator₁ 0 x.1 - x.1) +
        (triangleHomologyEquiv SpecialPeriods.triangleGenerator₂ 0 x.2 - x.2) =
      0
  rw [triangleHomologyEquiv_zero, triangleHomologyEquiv_zero]
  simp

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem
    PeriodFamily.Boundary.triangleHomologyEquiv_mul_apply (g h : SpecialPeriods.TriangleGroup)
    (n : ℕ) (a : SingularMayerVietoris.SingularHomology RealTorus₄ n) :
    PeriodFamily.Homology.triangleHomologyEquiv (g * h) n a =
      PeriodFamily.Homology.triangleHomologyEquiv g n
        (PeriodFamily.Homology.triangleHomologyEquiv h n a) := by
  unfold PeriodFamily.Homology.triangleHomologyEquiv
  rw [SpecialPeriods.triangleTorusHomeomorph_mul,
    PeriodTorusHigherHomology.homeomorphHomologyEquiv_trans]
  rfl

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem
    PeriodFamily.Boundary.triangleHomologyEquiv_pow_fixed (g : SpecialPeriods.TriangleGroup)
    (n : ℕ) (a : SingularMayerVietoris.SingularHomology RealTorus₄ n)
    (ha : PeriodFamily.Homology.triangleHomologyEquiv g n a = a) (k : ℕ) :
    PeriodFamily.Homology.triangleHomologyEquiv (g ^ k) n a = a := by
  induction k with
  | zero => rw [pow_zero, PeriodFamily.Homology.triangleHomologyEquiv_one]; rfl
  | succ k ih => rw [pow_succ, triangleHomologyEquiv_mul_apply, ha, ih]

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Boundary.ellipticTriangle_mkQ (j : Elliptic.Kind)
    (x : Elliptic.RealCoordinates) :
    SpecialPeriods.triangleTorusHomeomorph (SpecialPeriods.Triangle.ellipticGenerator j)
        (standardLattice.mkQ x) =
      standardLattice.mkQ (Elliptic.flatLinear j x) := by
  cases j
  · exact SpecialPeriods.triangleTorusAction_generator₁_mkQ x
  · exact SpecialPeriods.triangleTorusAction_generator₂_mkQ x

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Boundary.flatTorusAffine_eq_translation_triangle (j : Elliptic.Kind)
    (v : Lattice) :
    (Elliptic.flatTorusAffine j v : C(RealTorus₄, RealTorus₄)) =
      (PeriodTorusHigherHomology.rightTranslation
            (standardLattice.mkQ ((1 / (j.order : ℝ)) • Elliptic.realCast v))).comp
        (SpecialPeriods.triangleTorusHomeomorph (SpecialPeriods.Triangle.ellipticGenerator j) :
          C(RealTorus₄, RealTorus₄)) := by
  apply ContinuousMap.ext
  intro x
  obtain ⟨u, rfl⟩ := standardLattice.mkQ_surjective x
  simp only [ContinuousMap.comp_apply, PeriodTorusHigherHomology.rightTranslation_apply]
  calc
    _ = standardLattice.mkQ (Elliptic.flatAffine j v u) := Elliptic.flatTorusAffine_mkQ j v u
    _ = _ := by
      rw [Elliptic.flatAffine, map_add]
      exact
        congrArg
          (fun w : RealTorus₄ =>
            w + standardLattice.mkQ ((1 / (j.order : ℝ)) • Elliptic.realCast v))
          (ellipticTriangle_mkQ j u).symm

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem
    PeriodFamily.Boundary.flatTorusAffine_homology_triangle (j : Elliptic.Kind) (v : Lattice)
    (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap
        (Elliptic.flatTorusAffine j v : C(RealTorus₄, RealTorus₄)) n =
      (PeriodFamily.Homology.triangleHomologyEquiv (SpecialPeriods.Triangle.ellipticGenerator j)
          n).toLinearMap := by
  rw [flatTorusAffine_eq_translation_triangle, PeriodTorusHigherHomology.singularHomologyMap_comp,
    PeriodTorusHigherHomology.rightTranslation_singularHomologyMap, LinearMap.id_comp]
  rfl

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Boundary.nativeTailFrame_inv_homology_fixed (j : Elliptic.Kind) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ n)
    (ha :
      PeriodFamily.Homology.triangleHomologyEquiv (SpecialPeriods.Triangle.ellipticGenerator j) n
          a =
        a) :
    PeriodFamily.Homology.triangleHomologyEquiv (nativeTailFrame j)⁻¹ n a = a := by
  obtain ⟨k, _, hk⟩ := nativeTailFrame_inv_eq_power j
  rw [hk]
  exact triangleHomologyEquiv_pow_fixed (SpecialPeriods.Triangle.ellipticGenerator j) n a ha k

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Boundary.ellipticWangBoundary_generator_fixed (j : Elliptic.Kind)
    (v : Lattice) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology (MappingTorus.Torus (Elliptic.flatTorusAffine j v))
        (n + 1)) :
    PeriodFamily.Homology.triangleHomologyEquiv (SpecialPeriods.Triangle.ellipticGenerator j) n
        (MappingTorusHomology.wangBoundary (Elliptic.flatTorusAffine j v) n a) =
      MappingTorusHomology.wangBoundary (Elliptic.flatTorusAffine j v) n a := by
  have hb :
    MappingTorusHomology.wangBoundary (Elliptic.flatTorusAffine j v) n a ∈
      LinearMap.ker (MappingTorusHomology.wangDifference (Elliptic.flatTorusAffine j v) n) := by
    rw [← MappingTorusHomology.wangBoundary_range]
    exact ⟨a, rfl⟩
  have he := LinearMap.mem_ker.mp hb
  change
    MappingTorusHomology.wangBoundary (Elliptic.flatTorusAffine j v) n a -
        SingularMayerVietoris.singularHomologyMap
          (Elliptic.flatTorusAffine j v : C(RealTorus₄, RealTorus₄)) n
          (MappingTorusHomology.wangBoundary (Elliptic.flatTorusAffine j v) n a) =
      0 at he
  rw [flatTorusAffine_homology_triangle] at he
  exact (sub_eq_zero.mp he).symm

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem
    PeriodFamily.Boundary.nativeTailFrame_inv_wangBoundary (j : Elliptic.Kind) (v : Lattice)
    (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology (MappingTorus.Torus (Elliptic.flatTorusAffine j v))
        (n + 1)) :
    PeriodFamily.Homology.triangleHomologyEquiv (nativeTailFrame j)⁻¹ n
        (MappingTorusHomology.wangBoundary (Elliptic.flatTorusAffine j v) n a) =
      MappingTorusHomology.wangBoundary (Elliptic.flatTorusAffine j v) n a :=
  nativeTailFrame_inv_homology_fixed j n _ (ellipticWangBoundary_generator_fixed j v n a)

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
private theorem PeriodFamily.HomologyDifference.mem_range_iff_of_commuting {M N M' N' : Type*}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup M'] [AddCommGroup N'] [Module ℤ M]
    [Module ℤ N] [Module ℤ M'] [Module ℤ N'] (f : M →ₗ[ℤ] N) (g : M' →ₗ[ℤ] N') (e : M ≃ₗ[ℤ] M')
    (d : N ≃ₗ[ℤ] N') (h : ∀ x, d (f x) = g (e x)) (y : N) :
    d y ∈ LinearMap.range g ↔ y ∈ LinearMap.range f := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨e.symm x, d.injective ?_⟩
    calc
      d (f (e.symm x)) = g (e (e.symm x)) := h _
      _ = g x := (congrArg g (e.apply_symm_apply x))
      _ = d y := hx
  · rintro ⟨x, hx⟩
    exact ⟨e x, (h x).symm.trans (congrArg d hx)⟩

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
private def
    PeriodFamily.HomologyDifference.kernelEquivOfCommuting {M N M' N' : Type*} [AddCommGroup M]
    [AddCommGroup N] [AddCommGroup M'] [AddCommGroup N'] [Module ℤ M] [Module ℤ N] [Module ℤ M']
    [Module ℤ N'] (f : M →ₗ[ℤ] N) (g : M' →ₗ[ℤ] N') (e : M ≃ₗ[ℤ] M') (d : N ≃ₗ[ℤ] N')
    (h : ∀ x, d (f x) = g (e x)) : LinearMap.ker f ≃ₗ[ℤ] LinearMap.ker g :=
  ({    toFun
          x :=
          ⟨e x.val, by
            change g (e x.val) = 0
            calc
              g (e x.val) = d (f x.val) := (h x.val).symm
              _ = d 0 := (congrArg d x.property)
              _ = 0 := d.map_zero⟩
        invFun
          y :=
          ⟨e.symm y.val, by
            change f (e.symm y.val) = 0
            apply d.injective
            calc
              d (f (e.symm y.val)) = g (e (e.symm y.val)) := h _
              _ = g y.val := (congrArg g (e.apply_symm_apply y.val))
              _ = 0 := y.property
              _ = d 0 := d.map_zero.symm⟩
        left_inv x := Subtype.ext (e.symm_apply_apply x.val)
        right_inv y := Subtype.ext (e.apply_symm_apply y.val)
        map_add' x y := Subtype.ext (e.map_add x.val y.val) } :
      LinearMap.ker f ≃+ LinearMap.ker g).toIntLinearEquiv

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
private def
    PeriodFamily.HomologyDifference.cokernelEquivOfCommuting {M N M' N' : Type*} [AddCommGroup M]
    [AddCommGroup N] [AddCommGroup M'] [AddCommGroup N'] [Module ℤ M] [Module ℤ N] [Module ℤ M']
    [Module ℤ N'] (f : M →ₗ[ℤ] N) (g : M' →ₗ[ℤ] N') (e : M ≃ₗ[ℤ] M') (d : N ≃ₗ[ℤ] N')
    (h : ∀ x, d (f x) = g (e x)) : (N ⧸ LinearMap.range f) ≃ₗ[ℤ] (N' ⧸ LinearMap.range g) :=
  ({    toEquiv :=
          @Quotient.congr N N' (Submodule.quotientRel (LinearMap.range f))
            (Submodule.quotientRel (LinearMap.range g)) d.toEquiv
            (fun x y =>
              by
              change
                (LinearMap.range f).quotientRel x y ↔ (LinearMap.range g).quotientRel (d x) (d y)
              rw [Submodule.quotientRel_def, Submodule.quotientRel_def, ← map_sub]
              exact (mem_range_iff_of_commuting f g e d h (x - y)).symm)
        map_add' := by
          rintro ⟨x⟩ ⟨y⟩
          change Submodule.Quotient.mk (d (x + y)) = Submodule.Quotient.mk (d x + d y)
          exact congrArg Submodule.Quotient.mk (d.map_add x y) } :
      (N ⧸ LinearMap.range f) ≃+ (N' ⧸ LinearMap.range g)).toIntLinearEquiv

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private def
    PeriodFamily.Homology.familyOpen (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (U : TopologicalSpace.Opens SpecialPeriods.TriangleRegularQuotient) :
    TopologicalSpace.Opens D.Space :=
  ⟨D.projection ⁻¹' (U : Set SpecialPeriods.TriangleRegularQuotient),
    U.isOpen.preimage D.projection_continuous⟩

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private abbrev PeriodFamily.Homology.upperFamily
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :=
  familyOpen D upperBase

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private abbrev PeriodFamily.Homology.lowerFamily
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :=
  familyOpen D lowerBase

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private abbrev PeriodFamily.Homology.overlapFamily
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (i : Fin 3) :=
  familyOpen D (overlapBase i)

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Homology.upperFamily_union_lowerFamily
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :
    (upperFamily D : Set D.Space) ∪ lowerFamily D = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact
    SpecialPeriods.Triangle.mem_upperSlit_or_lowerSlit
      (SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph (D.projection x))

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Homology.overlapFamily_subset
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (i : Fin 3) :
    (overlapFamily D i : Set D.Space) ⊆ (upperFamily D : Set D.Space) ∩ lowerFamily D :=
  fun _ hx => overlapBase_subset i hx

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Homology.overlapFamily_pairwise_disjoint
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :
    Pairwise fun i j : Fin 3 => Disjoint (overlapFamily D i : Set D.Space) (overlapFamily D j) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  exact Set.disjoint_left.mp (overlapBase_pairwise_disjoint hij) hi hj

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Homology.overlapFamily_iUnion
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :
    (⋃ i : Fin 3, (overlapFamily D i : Set D.Space)) =
      (upperFamily D : Set D.Space) ∩ lowerFamily D := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact overlapFamily_subset D i hi
  · intro hx
    have hh :
      D.projection x ∈
        ⋃ i : Fin 3, (overlapBase i : Set SpecialPeriods.TriangleRegularQuotient) := by
      rw [overlapBase_iUnion]
      exact hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hh
    exact Set.mem_iUnion.mpr ⟨i, hi⟩

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private def PeriodFamily.Homology.sectionChart
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (U : TopologicalSpace.Opens SpecialPeriods.TriangleRegularQuotient)
    (s : C(U, SpecialPeriods.TriangleRegularPoint))
    (hs : ∀ x, SpecialPeriods.triangleRegularProject (s x) = x.val) :
    familyOpen D U ≃ₜ U × RealTorus₄ :=
  DiagonalQuotient.sectionHomeomorph SpecialPeriods.triangleRegularProject_covering U s hs

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
@[simp]
private theorem PeriodFamily.Homology.sectionChart_symm_coe
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (U : TopologicalSpace.Opens SpecialPeriods.TriangleRegularQuotient)
    (s : C(U, SpecialPeriods.TriangleRegularPoint))
    (hs : ∀ x, SpecialPeriods.triangleRegularProject (s x) = x.val) (x : U × RealTorus₄) :
    ((sectionChart D U s hs).symm x : D.Space) = D.quotient (s x.1, x.2) :=
  rfl

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Homology.sectionChart_projection
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (U : TopologicalSpace.Opens SpecialPeriods.TriangleRegularQuotient)
    (s : C(U, SpecialPeriods.TriangleRegularPoint))
    (hs : ∀ x, SpecialPeriods.triangleRegularProject (s x) = x.val) (x : familyOpen D U) :
    ((sectionChart D U s hs x).1 : SpecialPeriods.TriangleRegularQuotient) = D.projection x.val :=
  DiagonalQuotient.sectionHomeomorph_projection SpecialPeriods.triangleRegularProject_covering U s
    hs x

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
@[simp]
private theorem PeriodFamily.Homology.sectionChart_apply_quotient
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (U : TopologicalSpace.Opens SpecialPeriods.TriangleRegularQuotient)
    (s : C(U, SpecialPeriods.TriangleRegularPoint))
    (hs : ∀ x, SpecialPeriods.triangleRegularProject (s x) = x.val) (x : U) (f : RealTorus₄) :
    sectionChart D U s hs
        ⟨D.quotient (s x, f),
          by
          change SpecialPeriods.triangleRegularProject (s x) ∈ U
          rw [hs x]
          exact x.property⟩ =
      (x, f) :=
  DiagonalQuotient.sectionHomeomorph_apply_quotient SpecialPeriods.triangleRegularProject_covering
    U s hs x f

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private def
    PeriodFamily.Homology.upperChart (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (b : SlitBaseLift) : upperFamily D ≃ₜ upperBase × RealTorus₄ :=
  sectionChart D upperBase (upperLift b) (upperLift_project b)

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private def
    PeriodFamily.Homology.lowerChart (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (b : SlitBaseLift) : lowerFamily D ≃ₜ lowerBase × RealTorus₄ :=
  sectionChart D lowerBase (lowerLift b) (lowerLift_project b)

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private def PeriodFamily.Homology.overlapChart
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) (i : Fin 3) :
    overlapFamily D i ≃ₜ overlapBase i × RealTorus₄ :=
  sectionChart D (overlapBase i) (upperLiftOnOverlap b i) (upperLiftOnOverlap_project b i)

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
@[simp]
private theorem PeriodFamily.Homology.overlapChart_symm_coe
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) (i : Fin 3)
    (x : overlapBase i × RealTorus₄) :
    ((overlapChart D b i).symm x : D.Space) = D.quotient (upperLiftOnOverlap b i x.1, x.2) :=
  rfl

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private def PeriodFamily.Homology.overlapFamilyToUpper
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (i : Fin 3) :
    C(overlapFamily D i, upperFamily D) :=
  ⟨fun x => ⟨x.val, (overlapFamily_subset D i x.property).1⟩, by fun_prop⟩

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private def PeriodFamily.Homology.overlapFamilyToLower
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (i : Fin 3) :
    C(overlapFamily D i, lowerFamily D) :=
  ⟨fun x => ⟨x.val, (overlapFamily_subset D i x.property).2⟩, by fun_prop⟩

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Homology.upperChart_overlapFamilyToUpper
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) (i : Fin 3)
    (x : overlapFamily D i) :
    upperChart D b (overlapFamilyToUpper D i x) =
      (overlapToUpper i (overlapChart D b i x).1, (overlapChart D b i x).2) := by
  obtain ⟨y, rfl⟩ := (overlapChart D b i).symm.surjective x
  rw [Homeomorph.apply_symm_apply]
  exact
    sectionChart_apply_quotient D upperBase (upperLift b) (upperLift_project b)
      (overlapToUpper i y.1) y.2

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Homology.lowerChart_overlapFamilyToLower
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) (i : Fin 3)
    (x : overlapFamily D i) :
    lowerChart D b (overlapFamilyToLower D i x) =
      (overlapToLower i (overlapChart D b i x).1,
        SpecialPeriods.triangleTorusHomeomorph (overlapTransition b i)
          (overlapChart D b i x).2) := by
  obtain ⟨y, rfl⟩ := (overlapChart D b i).symm.surjective x
  rw [Homeomorph.apply_symm_apply]
  apply (lowerChart D b).symm.injective
  rw [Homeomorph.symm_apply_apply]
  apply Subtype.ext
  change
    D.quotient (upperLiftOnOverlap b i y.1, y.2) =
      D.quotient
        (lowerLiftOnOverlap b i y.1,
          SpecialPeriods.triangleTorusHomeomorph (overlapTransition b i) y.2)
  rw [← overlapTransition_apply b i y.1]
  exact
    (DiagonalQuotient.quotient_smul SpecialPeriods.TriangleGroup
        SpecialPeriods.TriangleRegularPoint RealTorus₄ (overlapTransition b i)
        (upperLiftOnOverlap b i y.1, y.2)).symm

private abbrev PeriodFamily.Homology.familyLeftHomologyMap
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (n : ℕ) :=
  SingularMayerVietoris.leftHomologyMap (upperFamily D : Set D.Space) (lowerFamily D) n

private abbrev PeriodFamily.Homology.familyRightHomologyMap
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (n : ℕ) :=
  SingularMayerVietoris.rightHomologyMap (upperFamily D : Set D.Space) (lowerFamily D) n

private def PeriodFamily.Homology.familyConnectingHomomorphism
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (n : ℕ) :
    SingularMayerVietoris.SingularHomology D.Space (n + 1) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology
        ((upperFamily D : Set D.Space) ∩ lowerFamily D : Set D.Space) n :=
  SingularMayerVietoris.connectingHomomorphism (upperFamily D : Set D.Space) (lowerFamily D)
    (upperFamily D).isOpen (lowerFamily D).isOpen (upperFamily_union_lowerFamily D) n

private theorem PeriodFamily.Homology.family_exact_at_pair
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (n : ℕ) :
    Function.Exact (familyLeftHomologyMap D n) (familyRightHomologyMap D n) := by
  apply LinearMap.exact_iff.mpr
  exact
    (SingularMayerVietoris.exact_at_pair (upperFamily D : Set D.Space) (lowerFamily D)
        (upperFamily D).isOpen (lowerFamily D).isOpen (upperFamily_union_lowerFamily D) n).symm

private theorem PeriodFamily.Homology.family_exact_at_ambient
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (n : ℕ) :
    Function.Exact (familyRightHomologyMap D (n + 1)) (familyConnectingHomomorphism D n) := by
  apply LinearMap.exact_iff.mpr
  exact
    (SingularMayerVietoris.exact_at_ambient (upperFamily D : Set D.Space) (lowerFamily D)
        (upperFamily D).isOpen (lowerFamily D).isOpen (upperFamily_union_lowerFamily D) n).symm

private theorem PeriodFamily.Homology.family_exact_at_intersection
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (n : ℕ) :
    Function.Exact (familyConnectingHomomorphism D n) (familyLeftHomologyMap D n) := by
  apply LinearMap.exact_iff.mpr
  exact
    (SingularMayerVietoris.exact_at_intersection (upperFamily D : Set D.Space) (lowerFamily D)
        (upperFamily D).isOpen (lowerFamily D).isOpen (upperFamily_union_lowerFamily D) n).symm

private theorem PeriodFamily.Homology.familyRightHomologyMap_zero_surjective
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :
    Function.Surjective (familyRightHomologyMap D 0) :=
  SingularMayerVietoris.rightHomologyMap_zero_surjective (upperFamily D : Set D.Space)
    (lowerFamily D) (upperFamily D).isOpen (lowerFamily D).isOpen
    (upperFamily_union_lowerFamily D)

private def PeriodFamily.Homology.familyIntersection
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :
    TopologicalSpace.Opens D.Space :=
  upperFamily D ⊓ lowerFamily D

private def PeriodFamily.Homology.intersectionIndex : Fin 3 → Fin 3 :=
  Equiv.swap 0 1

@[simp]
private theorem PeriodFamily.Homology.intersectionIndex_zero : intersectionIndex 0 = 1 := by decide

@[simp]
private theorem PeriodFamily.Homology.intersectionIndex_one : intersectionIndex 1 = 0 := by decide

@[simp]
private theorem PeriodFamily.Homology.intersectionIndex_two : intersectionIndex 2 = 2 := by decide

private theorem PeriodFamily.Homology.intersectionIndex_injective :
    Function.Injective intersectionIndex :=
  (Equiv.swap (0 : Fin 3) 1).injective

private theorem PeriodFamily.Homology.intersectionIndex_surjective :
    Function.Surjective intersectionIndex :=
  (Equiv.swap (0 : Fin 3) 1).surjective

private def PeriodFamily.Homology.intersectionPiece
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (i : Fin 3) :
    TopologicalSpace.Opens (familyIntersection D) :=
  ⟨Subtype.val ⁻¹' (overlapFamily D (intersectionIndex i) : Set D.Space),
    (overlapFamily D (intersectionIndex i)).isOpen.preimage continuous_subtype_val⟩

private theorem PeriodFamily.Homology.intersectionPiece_pairwise_disjoint
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :
    Pairwise fun i j : Fin 3 =>
      Disjoint (intersectionPiece D i : Set (familyIntersection D)) (intersectionPiece D j) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  exact
    Set.disjoint_left.mp
      (overlapFamily_pairwise_disjoint D (fun h => hij (intersectionIndex_injective h))) hi hj

private theorem PeriodFamily.Homology.intersectionPiece_iUnion
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :
    (⋃ i : Fin 3, (intersectionPiece D i : Set (familyIntersection D))) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hx : x.val ∈ ⋃ j : Fin 3, (overlapFamily D j : Set D.Space) := by
    rw [overlapFamily_iUnion]
    exact x.property
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
  obtain ⟨i, hi⟩ := intersectionIndex_surjective j
  apply Set.mem_iUnion.mpr
  refine ⟨i, ?_⟩
  change x.val ∈ overlapFamily D (intersectionIndex i)
  rw [hi]
  exact hj

private def PeriodFamily.Homology.intersectionPieceHomeomorph
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (i : Fin 3) :
    intersectionPiece D i ≃ₜ overlapFamily D (intersectionIndex i)
    where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, overlapFamily_subset D (intersectionIndex i) x.property⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private def PeriodFamily.Homology.intersectionToUpper
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :
    C(familyIntersection D, upperFamily D) :=
  ⟨fun x => ⟨x.val, x.property.1⟩, by fun_prop⟩

private def PeriodFamily.Homology.intersectionToLower
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :
    C(familyIntersection D, lowerFamily D) :=
  ⟨fun x => ⟨x.val, x.property.2⟩, by fun_prop⟩

private theorem PeriodFamily.Homology.intersectionToUpper_comp_piece
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (i : Fin 3) :
    (intersectionToUpper D).comp
        (⟨Subtype.val, continuous_subtype_val⟩ : C(intersectionPiece D i, familyIntersection D)) =
      (overlapFamilyToUpper D (intersectionIndex i)).comp
        (intersectionPieceHomeomorph D i : C(_, _)) :=
  rfl

private theorem PeriodFamily.Homology.intersectionToLower_comp_piece
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (i : Fin 3) :
    (intersectionToLower D).comp
        (⟨Subtype.val, continuous_subtype_val⟩ : C(intersectionPiece D i, familyIntersection D)) =
      (overlapFamilyToLower D (intersectionIndex i)).comp
        (intersectionPieceHomeomorph D i : C(_, _)) :=
  rfl

private def PeriodFamily.Homology.upperHomotopyEquiv
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) :
    upperFamily D ≃ₕ RealTorus₄ :=
  (upperChart D b).toHomotopyEquiv.trans
    (PeriodTorusHigherHomology.CircleTopology.contractibleProdHomotopyEquiv upperBase RealTorus₄)

private def PeriodFamily.Homology.lowerHomotopyEquiv
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) :
    lowerFamily D ≃ₕ RealTorus₄ :=
  (lowerChart D b).toHomotopyEquiv.trans
    (PeriodTorusHigherHomology.CircleTopology.contractibleProdHomotopyEquiv lowerBase RealTorus₄)

private def PeriodFamily.Homology.overlapHomotopyEquiv
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) (i : Fin 3) :
    overlapFamily D i ≃ₕ RealTorus₄ :=
  (overlapChart D b i).toHomotopyEquiv.trans
    (PeriodTorusHigherHomology.CircleTopology.contractibleProdHomotopyEquiv (overlapBase i)
      RealTorus₄)

private theorem PeriodFamily.Homology.upperHomotopyEquiv_comp_overlap
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) (i : Fin 3) :
    (upperHomotopyEquiv D b).toFun.comp (overlapFamilyToUpper D i) =
      (overlapHomotopyEquiv D b i).toFun := by
  apply ContinuousMap.ext
  intro x
  exact congrArg Prod.snd (upperChart_overlapFamilyToUpper D b i x)

private theorem PeriodFamily.Homology.lowerHomotopyEquiv_comp_overlap
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) (i : Fin 3) :
    (lowerHomotopyEquiv D b).toFun.comp (overlapFamilyToLower D i) =
      (SpecialPeriods.triangleTorusHomeomorph (overlapTransition b i) :
            C(RealTorus₄, RealTorus₄)).comp
        (overlapHomotopyEquiv D b i).toFun := by
  apply ContinuousMap.ext
  intro x
  exact congrArg Prod.snd (lowerChart_overlapFamilyToLower D b i x)

private def PeriodFamily.Homology.upperHomologyEquiv
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) (n : ℕ) :
    SingularMayerVietoris.SingularHomology (upperFamily D) n ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology RealTorus₄ n :=
  PeriodTorusHigherHomology.homotopyEquivHomologyEquiv (upperHomotopyEquiv D b) n

private def PeriodFamily.Homology.lowerHomologyEquiv
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) (n : ℕ) :
    SingularMayerVietoris.SingularHomology (lowerFamily D) n ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology RealTorus₄ n :=
  PeriodTorusHigherHomology.homotopyEquivHomologyEquiv (lowerHomotopyEquiv D b) n

private def PeriodFamily.Homology.overlapHomologyEquiv
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) (i : Fin 3)
    (n : ℕ) :
    SingularMayerVietoris.SingularHomology (overlapFamily D i) n ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology RealTorus₄ n :=
  PeriodTorusHigherHomology.homotopyEquivHomologyEquiv (overlapHomotopyEquiv D b i) n

@[simp]
private theorem PeriodFamily.Homology.upperHomologyEquiv_apply
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (upperFamily D) n) :
    upperHomologyEquiv D b n a =
      SingularMayerVietoris.singularHomologyMap (upperHomotopyEquiv D b).toFun n a :=
  rfl

@[simp]
private theorem PeriodFamily.Homology.lowerHomologyEquiv_apply
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (lowerFamily D) n) :
    lowerHomologyEquiv D b n a =
      SingularMayerVietoris.singularHomologyMap (lowerHomotopyEquiv D b).toFun n a :=
  rfl

private theorem PeriodFamily.Homology.upperHomologyEquiv_overlap
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) (i : Fin 3)
    (n : ℕ) (a : SingularMayerVietoris.SingularHomology (overlapFamily D i) n) :
    upperHomologyEquiv D b n
        (SingularMayerVietoris.singularHomologyMap (overlapFamilyToUpper D i) n a) =
      overlapHomologyEquiv D b i n a := by
  rw [upperHomologyEquiv_apply, ← LinearMap.comp_apply, ←
    PeriodTorusHigherHomology.singularHomologyMap_comp, upperHomotopyEquiv_comp_overlap]
  rfl

private theorem PeriodFamily.Homology.lowerHomologyEquiv_overlap
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) (i : Fin 3)
    (n : ℕ) (a : SingularMayerVietoris.SingularHomology (overlapFamily D i) n) :
    lowerHomologyEquiv D b n
        (SingularMayerVietoris.singularHomologyMap (overlapFamilyToLower D i) n a) =
      SingularMayerVietoris.singularHomologyMap
        (SpecialPeriods.triangleTorusHomeomorph (overlapTransition b i) :
          C(RealTorus₄, RealTorus₄))
        n (overlapHomologyEquiv D b i n a) := by
  rw [lowerHomologyEquiv_apply, ← LinearMap.comp_apply, ←
    PeriodTorusHigherHomology.singularHomologyMap_comp, lowerHomotopyEquiv_comp_overlap,
    PeriodTorusHigherHomology.singularHomologyMap_comp]
  rfl

private def PeriodFamily.Homology.pairHomologyEquiv
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) (n : ℕ) :
    (SingularMayerVietoris.SingularHomology (upperFamily D) n ×
        SingularMayerVietoris.SingularHomology (lowerFamily D) n) ≃ₗ[ℤ]
      (SingularMayerVietoris.SingularHomology RealTorus₄ n ×
        SingularMayerVietoris.SingularHomology RealTorus₄ n) :=
  ((upperHomologyEquiv D b n).toAddEquiv.prodCongr
      (lowerHomologyEquiv D b n).toAddEquiv).toIntLinearEquiv

private abbrev PeriodFamily.Homology.openPartitionSum {X : Type} [TopologicalSpace X]
    (U : Fin 3 → TopologicalSpace.Opens X) :=
  U 0 ⊕ (U 1 ⊕ U 2)

private def PeriodFamily.Homology.openPartitionInclusion {X : Type} [TopologicalSpace X]
    (U : Fin 3 → TopologicalSpace.Opens X) (i : Fin 3) : C(U i, X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

private def PeriodFamily.Homology.openPartitionSumMap {X : Type} [TopologicalSpace X]
    (U : Fin 3 → TopologicalSpace.Opens X) : C(openPartitionSum U, X) :=
  PeriodTorusHigherHomology.sumElimMap (openPartitionInclusion U 0)
    (PeriodTorusHigherHomology.sumElimMap (openPartitionInclusion U 1)
      (openPartitionInclusion U 2))

private theorem PeriodFamily.Homology.openPartitionSumMap_isOpenMap {X : Type} [TopologicalSpace X]
    (U : Fin 3 → TopologicalSpace.Opens X) : IsOpenMap (openPartitionSumMap U) :=
  (U 0).isOpen.isOpenMap_subtype_val.sumElim
    ((U 1).isOpen.isOpenMap_subtype_val.sumElim (U 2).isOpen.isOpenMap_subtype_val)

public
theorem PeriodFamily.Homology.openPartitionInclusion_ne_mo1973_25234 {X : Type}
    [TopologicalSpace X] (U : Fin 3 → TopologicalSpace.Opens X)
    (hdisj : Pairwise fun i j : Fin 3 => Disjoint (U i : Set X) (U j : Set X)) {i j : Fin 3}
    (hij : i ≠ j) (x : U i) (y : U j) : (x : X) ≠ (y : X) := by
  intro h
  exact Set.disjoint_left.mp (hdisj hij) x.property (h.symm ▸ y.property)

private theorem PeriodFamily.Homology.openPartitionSumMap_injective {X : Type} [TopologicalSpace X]
    (U : Fin 3 → TopologicalSpace.Opens X)
    (hdisj : Pairwise fun i j : Fin 3 => Disjoint (U i : Set X) (U j : Set X)) :
    Function.Injective (openPartitionSumMap U) := by
  rintro (x | (x | x)) (y | (y | y)) h
  · exact congrArg Sum.inl (Subtype.ext h)
  · exact
      False.elim
        (openPartitionInclusion_ne_mo1973_25234 U hdisj (by decide : (0 : Fin 3) ≠ 1) x y h)
  · exact
      False.elim
        (openPartitionInclusion_ne_mo1973_25234 U hdisj (by decide : (0 : Fin 3) ≠ 2) x y h)
  · exact
      False.elim
        (openPartitionInclusion_ne_mo1973_25234 U hdisj (by decide : (1 : Fin 3) ≠ 0) x y h)
  · exact congrArg (Sum.inr ∘ Sum.inl) (Subtype.ext h)
  · exact
      False.elim
        (openPartitionInclusion_ne_mo1973_25234 U hdisj (by decide : (1 : Fin 3) ≠ 2) x y h)
  · exact
      False.elim
        (openPartitionInclusion_ne_mo1973_25234 U hdisj (by decide : (2 : Fin 3) ≠ 0) x y h)
  · exact
      False.elim
        (openPartitionInclusion_ne_mo1973_25234 U hdisj (by decide : (2 : Fin 3) ≠ 1) x y h)
  · exact congrArg (Sum.inr ∘ Sum.inr) (Subtype.ext h)

private theorem PeriodFamily.Homology.openPartitionSumMap_surjective {X : Type} [TopologicalSpace X]
    (U : Fin 3 → TopologicalSpace.Opens X) (hcover : (⋃ i, (U i : Set X)) = Set.univ) :
    Function.Surjective (openPartitionSumMap U) := by
  intro x
  have hx : x ∈ ⋃ i, (U i : Set X) := by rw [hcover]; exact Set.mem_univ x
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  fin_cases i
  · exact ⟨Sum.inl ⟨x, hi⟩, rfl⟩
  · exact ⟨Sum.inr (Sum.inl ⟨x, hi⟩), rfl⟩
  · exact ⟨Sum.inr (Sum.inr ⟨x, hi⟩), rfl⟩

private def PeriodFamily.Homology.openPartitionHomeomorph {X : Type} [TopologicalSpace X]
    (U : Fin 3 → TopologicalSpace.Opens X)
    (hdisj : Pairwise fun i j : Fin 3 => Disjoint (U i : Set X) (U j : Set X))
    (hcover : (⋃ i, (U i : Set X)) = Set.univ) : X ≃ₜ openPartitionSum U :=
  ((Equiv.ofBijective (openPartitionSumMap U)
          ⟨openPartitionSumMap_injective U hdisj,
            openPartitionSumMap_surjective U hcover⟩).toHomeomorphOfContinuousOpen
      (openPartitionSumMap U).continuous (openPartitionSumMap_isOpenMap U)).symm

@[simp]
private theorem
    PeriodFamily.Homology.openPartitionHomeomorph_symm_apply {X : Type} [TopologicalSpace X]
    (U : Fin 3 → TopologicalSpace.Opens X)
    (hdisj : Pairwise fun i j : Fin 3 => Disjoint (U i : Set X) (U j : Set X))
    (hcover : (⋃ i, (U i : Set X)) = Set.univ) (a : openPartitionSum U) :
    (openPartitionHomeomorph U hdisj hcover).symm a = openPartitionSumMap U a :=
  rfl

private def PeriodFamily.Homology.tripleSumHomologyEquiv (A B C : Type) [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace C] (n : ℕ) :
    SingularMayerVietoris.SingularHomology (A ⊕ (B ⊕ C)) n ≃ₗ[ℤ]
      (SingularMayerVietoris.SingularHomology A n ×
        (SingularMayerVietoris.SingularHomology B n ×
          SingularMayerVietoris.SingularHomology C n)) :=
  (PeriodTorusHigherHomology.sumHomologyEquiv A (B ⊕ C) n).trans
    (((AddEquiv.refl (SingularMayerVietoris.SingularHomology A n)).prodCongr
        (PeriodTorusHigherHomology.sumHomologyEquiv B C n).toAddEquiv).toIntLinearEquiv)

private theorem
    PeriodFamily.Homology.tripleSumHomologyEquiv_sumElim_symm {A : Type} {B : Type} {C : Type}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] {D : Type} [TopologicalSpace D]
    (f : C(A, D)) (g : C(B, D)) (h : C(C, D)) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology A n ×
        (SingularMayerVietoris.SingularHomology B n ×
          SingularMayerVietoris.SingularHomology C n)) :
    SingularMayerVietoris.singularHomologyMap
        (PeriodTorusHigherHomology.sumElimMap f (PeriodTorusHigherHomology.sumElimMap g h)) n
        ((tripleSumHomologyEquiv A B C n).symm a) =
      SingularMayerVietoris.singularHomologyMap f n a.1 +
        (SingularMayerVietoris.singularHomologyMap g n a.2.1 +
          SingularMayerVietoris.singularHomologyMap h n a.2.2) := by
  change
    SingularMayerVietoris.singularHomologyMap
        (PeriodTorusHigherHomology.sumElimMap f (PeriodTorusHigherHomology.sumElimMap g h)) n
        ((PeriodTorusHigherHomology.sumHomologyEquiv A (B ⊕ C) n).symm
          (a.1, (PeriodTorusHigherHomology.sumHomologyEquiv B C n).symm a.2)) =
      _
  rw [PeriodTorusHigherHomology.sumHomologyEquiv_sumElim_symm,
    PeriodTorusHigherHomology.sumHomologyEquiv_sumElim_symm]

private theorem PeriodFamily.Homology.openPartitionHomeomorph_symm_toContinuousMap {X : Type}
    [TopologicalSpace X] (U : Fin 3 → TopologicalSpace.Opens X)
    (hdisj : Pairwise fun i j : Fin 3 => Disjoint (U i : Set X) (U j : Set X))
    (hcover : (⋃ i, (U i : Set X)) = Set.univ) :
    ((openPartitionHomeomorph U hdisj hcover).symm : C(openPartitionSum U, X)) =
      openPartitionSumMap U := by
  apply ContinuousMap.ext
  exact openPartitionHomeomorph_symm_apply U hdisj hcover

private def PeriodFamily.Homology.openPartitionHomologyEquiv {X : Type} [TopologicalSpace X]
    (U : Fin 3 → TopologicalSpace.Opens X)
    (hdisj : Pairwise fun i j : Fin 3 => Disjoint (U i : Set X) (U j : Set X))
    (hcover : (⋃ i, (U i : Set X)) = Set.univ) (n : ℕ) :
    SingularMayerVietoris.SingularHomology X n ≃ₗ[ℤ]
      (SingularMayerVietoris.SingularHomology (U 0) n ×
        (SingularMayerVietoris.SingularHomology (U 1) n ×
          SingularMayerVietoris.SingularHomology (U 2) n)) :=
  (PeriodTorusHigherHomology.homeomorphHomologyEquiv (openPartitionHomeomorph U hdisj hcover)
        n).trans
    (tripleSumHomologyEquiv (U 0) (U 1) (U 2) n)

private theorem PeriodFamily.Homology.openPartitionHomologyEquiv_symm_apply {X : Type}
    [TopologicalSpace X] (U : Fin 3 → TopologicalSpace.Opens X)
    (hdisj : Pairwise fun i j : Fin 3 => Disjoint (U i : Set X) (U j : Set X))
    (hcover : (⋃ i, (U i : Set X)) = Set.univ) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology (U 0) n ×
        (SingularMayerVietoris.SingularHomology (U 1) n ×
          SingularMayerVietoris.SingularHomology (U 2) n)) :
    (openPartitionHomologyEquiv U hdisj hcover n).symm a =
      SingularMayerVietoris.singularHomologyMap (openPartitionInclusion U 0) n a.1 +
        (SingularMayerVietoris.singularHomologyMap (openPartitionInclusion U 1) n a.2.1 +
          SingularMayerVietoris.singularHomologyMap (openPartitionInclusion U 2) n a.2.2) := by
  change
    SingularMayerVietoris.singularHomologyMap
        ((openPartitionHomeomorph U hdisj hcover).symm : C(openPartitionSum U, X)) n
        ((tripleSumHomologyEquiv (U 0) (U 1) (U 2) n).symm a) =
      _
  rw [openPartitionHomeomorph_symm_toContinuousMap]
  exact
    tripleSumHomologyEquiv_sumElim_symm (openPartitionInclusion U 0) (openPartitionInclusion U 1)
      (openPartitionInclusion U 2) n a

@[simp]
private theorem PeriodFamily.Homology.openPartitionHomologyEquiv_inclusion_zero {X : Type}
    [TopologicalSpace X] (U : Fin 3 → TopologicalSpace.Opens X)
    (hdisj : Pairwise fun i j : Fin 3 => Disjoint (U i : Set X) (U j : Set X))
    (hcover : (⋃ i, (U i : Set X)) = Set.univ) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (U 0) n) :
    openPartitionHomologyEquiv U hdisj hcover n
        (SingularMayerVietoris.singularHomologyMap (openPartitionInclusion U 0) n a) =
      (a, (0, 0)) := by
  apply (openPartitionHomologyEquiv U hdisj hcover n).symm.injective
  rw [LinearEquiv.symm_apply_apply, openPartitionHomologyEquiv_symm_apply]
  simp only [map_zero, add_zero]

@[simp]
private theorem PeriodFamily.Homology.openPartitionHomologyEquiv_inclusion_one {X : Type}
    [TopologicalSpace X] (U : Fin 3 → TopologicalSpace.Opens X)
    (hdisj : Pairwise fun i j : Fin 3 => Disjoint (U i : Set X) (U j : Set X))
    (hcover : (⋃ i, (U i : Set X)) = Set.univ) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (U 1) n) :
    openPartitionHomologyEquiv U hdisj hcover n
        (SingularMayerVietoris.singularHomologyMap (openPartitionInclusion U 1) n a) =
      (0, (a, 0)) := by
  apply (openPartitionHomologyEquiv U hdisj hcover n).symm.injective
  rw [LinearEquiv.symm_apply_apply, openPartitionHomologyEquiv_symm_apply]
  simp only [map_zero, zero_add, add_zero]

@[simp]
private theorem PeriodFamily.Homology.openPartitionHomologyEquiv_inclusion_two {X : Type}
    [TopologicalSpace X] (U : Fin 3 → TopologicalSpace.Opens X)
    (hdisj : Pairwise fun i j : Fin 3 => Disjoint (U i : Set X) (U j : Set X))
    (hcover : (⋃ i, (U i : Set X)) = Set.univ) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (U 2) n) :
    openPartitionHomologyEquiv U hdisj hcover n
        (SingularMayerVietoris.singularHomologyMap (openPartitionInclusion U 2) n a) =
      (0, (0, a)) := by
  apply (openPartitionHomologyEquiv U hdisj hcover n).symm.injective
  rw [LinearEquiv.symm_apply_apply, openPartitionHomologyEquiv_symm_apply]
  simp only [map_zero, zero_add]

private theorem PeriodFamily.Homology.openPartitionHomologyEquiv_map_out_symm {X : Type}
    [TopologicalSpace X] (U : Fin 3 → TopologicalSpace.Opens X)
    (hdisj : Pairwise fun i j : Fin 3 => Disjoint (U i : Set X) (U j : Set X))
    (hcover : (⋃ i, (U i : Set X)) = Set.univ) {Y : Type} [TopologicalSpace Y] (f : C(X, Y))
    (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology (U 0) n ×
        (SingularMayerVietoris.SingularHomology (U 1) n ×
          SingularMayerVietoris.SingularHomology (U 2) n)) :
    SingularMayerVietoris.singularHomologyMap f n
        ((openPartitionHomologyEquiv U hdisj hcover n).symm a) =
      SingularMayerVietoris.singularHomologyMap (f.comp (openPartitionInclusion U 0)) n a.1 +
        (SingularMayerVietoris.singularHomologyMap (f.comp (openPartitionInclusion U 1)) n a.2.1 +
          SingularMayerVietoris.singularHomologyMap (f.comp (openPartitionInclusion U 2)) n
            a.2.2) := by
  rw [openPartitionHomologyEquiv_symm_apply, map_add, map_add,
    PeriodTorusHigherHomology.singularHomologyMap_comp,
    PeriodTorusHigherHomology.singularHomologyMap_comp,
    PeriodTorusHigherHomology.singularHomologyMap_comp]
  rfl

private theorem
    PeriodFamily.Homology.openPartitionHomologyEquiv_map_out {X : Type} [TopologicalSpace X]
    (U : Fin 3 → TopologicalSpace.Opens X)
    (hdisj : Pairwise fun i j : Fin 3 => Disjoint (U i : Set X) (U j : Set X))
    (hcover : (⋃ i, (U i : Set X)) = Set.univ) {Y : Type} [TopologicalSpace Y] (f : C(X, Y))
    (n : ℕ) (a : SingularMayerVietoris.SingularHomology X n) :
    SingularMayerVietoris.singularHomologyMap f n a =
      SingularMayerVietoris.singularHomologyMap (f.comp (openPartitionInclusion U 0)) n
          (openPartitionHomologyEquiv U hdisj hcover n a).1 +
        (SingularMayerVietoris.singularHomologyMap (f.comp (openPartitionInclusion U 1)) n
            (openPartitionHomologyEquiv U hdisj hcover n a).2.1 +
          SingularMayerVietoris.singularHomologyMap (f.comp (openPartitionInclusion U 2)) n
            (openPartitionHomologyEquiv U hdisj hcover n a).2.2) := by
  have h :=
    openPartitionHomologyEquiv_map_out_symm U hdisj hcover f n
      (openPartitionHomologyEquiv U hdisj hcover n a)
  rwa [LinearEquiv.symm_apply_apply] at h

private def PeriodFamily.Homology.intersectionPieceHomologyEquiv
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) (i : Fin 3)
    (n : ℕ) :
    SingularMayerVietoris.SingularHomology (intersectionPiece D i) n ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology RealTorus₄ n :=
  (PeriodTorusHigherHomology.homeomorphHomologyEquiv (intersectionPieceHomeomorph D i) n).trans
    (overlapHomologyEquiv D b (intersectionIndex i) n)

private abbrev PeriodFamily.Homology.intersectionPartitionHomologyEquiv
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (n : ℕ) :
    SingularMayerVietoris.SingularHomology (familyIntersection D) n ≃ₗ[ℤ]
      (SingularMayerVietoris.SingularHomology (intersectionPiece D 0) n ×
        (SingularMayerVietoris.SingularHomology (intersectionPiece D 1) n ×
          SingularMayerVietoris.SingularHomology (intersectionPiece D 2) n)) :=
  openPartitionHomologyEquiv (intersectionPiece D) (intersectionPiece_pairwise_disjoint D)
    (intersectionPiece_iUnion D) n

private def PeriodFamily.Homology.intersectionHomologyEquiv
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) (n : ℕ) :
    SingularMayerVietoris.SingularHomology (familyIntersection D) n ≃ₗ[ℤ]
      (SingularMayerVietoris.SingularHomology RealTorus₄ n ×
        (SingularMayerVietoris.SingularHomology RealTorus₄ n ×
          SingularMayerVietoris.SingularHomology RealTorus₄ n)) :=
  (intersectionPartitionHomologyEquiv D n).trans
    (((intersectionPieceHomologyEquiv D b 0 n).toAddEquiv.prodCongr
        ((intersectionPieceHomologyEquiv D b 1 n).toAddEquiv.prodCongr
          (intersectionPieceHomologyEquiv D b 2 n).toAddEquiv)).toIntLinearEquiv)

@[simp]
private theorem PeriodFamily.Homology.intersectionHomologyEquiv_apply
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (familyIntersection D) n) :
    intersectionHomologyEquiv D b n a =
      (intersectionPieceHomologyEquiv D b 0 n (intersectionPartitionHomologyEquiv D n a).1,
        (intersectionPieceHomologyEquiv D b 1 n (intersectionPartitionHomologyEquiv D n a).2.1,
          intersectionPieceHomologyEquiv D b 2 n
            (intersectionPartitionHomologyEquiv D n a).2.2)) :=
  rfl

private theorem PeriodFamily.Homology.intersectionHomologyEquiv_inclusion_middle
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (intersectionPiece D 0) n) :
    intersectionHomologyEquiv D b n
        (SingularMayerVietoris.singularHomologyMap
          (openPartitionInclusion (intersectionPiece D) 0) n a) =
      (intersectionPieceHomologyEquiv D b 0 n a, (0, 0)) := by
  simp only [intersectionHomologyEquiv_apply, intersectionPartitionHomologyEquiv,
    openPartitionHomologyEquiv_inclusion_zero, map_zero]

private theorem PeriodFamily.Homology.intersectionHomologyEquiv_inclusion_left
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (intersectionPiece D 1) n) :
    intersectionHomologyEquiv D b n
        (SingularMayerVietoris.singularHomologyMap
          (openPartitionInclusion (intersectionPiece D) 1) n a) =
      (0, (intersectionPieceHomologyEquiv D b 1 n a, 0)) := by
  simp only [intersectionHomologyEquiv_apply, intersectionPartitionHomologyEquiv,
    openPartitionHomologyEquiv_inclusion_one, map_zero]

private theorem PeriodFamily.Homology.intersectionHomologyEquiv_inclusion_right
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (intersectionPiece D 2) n) :
    intersectionHomologyEquiv D b n
        (SingularMayerVietoris.singularHomologyMap
          (openPartitionInclusion (intersectionPiece D) 2) n a) =
      (0, (0, intersectionPieceHomologyEquiv D b 2 n a)) := by
  simp only [intersectionHomologyEquiv_apply, intersectionPartitionHomologyEquiv,
    openPartitionHomologyEquiv_inclusion_two, map_zero]

private theorem PeriodFamily.Homology.upperHomologyEquiv_intersectionPiece
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) (i : Fin 3)
    (n : ℕ) (a : SingularMayerVietoris.SingularHomology (intersectionPiece D i) n) :
    upperHomologyEquiv D b n
        (SingularMayerVietoris.singularHomologyMap
          ((intersectionToUpper D).comp (openPartitionInclusion (intersectionPiece D) i)) n a) =
      intersectionPieceHomologyEquiv D b i n a := by
  rw [openPartitionInclusion, intersectionToUpper_comp_piece,
    PeriodTorusHigherHomology.singularHomologyMap_comp]
  exact upperHomologyEquiv_overlap D b (intersectionIndex i) n _

private theorem PeriodFamily.Homology.lowerHomologyEquiv_intersectionPiece
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) (i : Fin 3)
    (n : ℕ) (a : SingularMayerVietoris.SingularHomology (intersectionPiece D i) n) :
    lowerHomologyEquiv D b n
        (SingularMayerVietoris.singularHomologyMap
          ((intersectionToLower D).comp (openPartitionInclusion (intersectionPiece D) i)) n a) =
      SingularMayerVietoris.singularHomologyMap
        (SpecialPeriods.triangleTorusHomeomorph (overlapTransition b (intersectionIndex i)) :
          C(RealTorus₄, RealTorus₄))
        n (intersectionPieceHomologyEquiv D b i n a) := by
  rw [openPartitionInclusion, intersectionToLower_comp_piece,
    PeriodTorusHigherHomology.singularHomologyMap_comp]
  exact lowerHomologyEquiv_overlap D b (intersectionIndex i) n _

private theorem PeriodFamily.Homology.upperHomologyEquiv_intersection
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (familyIntersection D) n) :
    upperHomologyEquiv D b n
        (SingularMayerVietoris.singularHomologyMap (intersectionToUpper D) n a) =
      (intersectionHomologyEquiv D b n a).1 + (intersectionHomologyEquiv D b n a).2.1 +
        (intersectionHomologyEquiv D b n a).2.2 := by
  have h :=
    congrArg (upperHomologyEquiv D b n)
      (openPartitionHomologyEquiv_map_out (intersectionPiece D)
        (intersectionPiece_pairwise_disjoint D) (intersectionPiece_iUnion D)
        (intersectionToUpper D) n a)
  simp only [map_add, upperHomologyEquiv_intersectionPiece] at h
  simpa only [intersectionHomologyEquiv_apply, ← add_assoc] using h

private theorem PeriodFamily.Homology.lowerHomologyEquiv_intersection
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (familyIntersection D) n) :
    lowerHomologyEquiv D b n
        (SingularMayerVietoris.singularHomologyMap (intersectionToLower D) n a) =
      (intersectionHomologyEquiv D b n a).1 +
          SingularMayerVietoris.singularHomologyMap
            (SpecialPeriods.triangleTorusHomeomorph (overlapTransition b 0) :
              C(RealTorus₄, RealTorus₄))
            n (intersectionHomologyEquiv D b n a).2.1 +
        SingularMayerVietoris.singularHomologyMap
          (SpecialPeriods.triangleTorusHomeomorph (overlapTransition b 2) :
            C(RealTorus₄, RealTorus₄))
          n (intersectionHomologyEquiv D b n a).2.2 := by
  have hidentity :
    SingularMayerVietoris.singularHomologyMap
        (Homeomorph.refl RealTorus₄ : C(RealTorus₄, RealTorus₄)) n =
      LinearMap.id := by
    change SingularMayerVietoris.singularHomologyMap (ContinuousMap.id RealTorus₄) n = _
    exact PeriodTorusHigherHomology.singularHomologyMap_id RealTorus₄ n
  have h :=
    congrArg (lowerHomologyEquiv D b n)
      (openPartitionHomologyEquiv_map_out (intersectionPiece D)
        (intersectionPiece_pairwise_disjoint D) (intersectionPiece_iUnion D)
        (intersectionToLower D) n a)
  simp only [map_add, lowerHomologyEquiv_intersectionPiece, intersectionIndex_zero,
    intersectionIndex_one, intersectionIndex_two, overlapTransition_middle,
    SpecialPeriods.triangleTorusHomeomorph_one, hidentity, LinearMap.id_apply] at h
  simpa only [intersectionHomologyEquiv_apply, ← add_assoc] using h

private theorem PeriodFamily.Homology.pairHomologyEquiv_leftHomologyMap
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (familyIntersection D) n) :
    pairHomologyEquiv D b n
        (SingularMayerVietoris.leftHomologyMap (upperFamily D : Set D.Space) (lowerFamily D) n
          a) =
      TrianglePeriodFamilyHomologyAlgebra.overlapMap
        (SingularMayerVietoris.singularHomologyMap
          (SpecialPeriods.triangleTorusHomeomorph (overlapTransition b 0) :
            C(RealTorus₄, RealTorus₄))
          n)
        (SingularMayerVietoris.singularHomologyMap
          (SpecialPeriods.triangleTorusHomeomorph (overlapTransition b 2) :
            C(RealTorus₄, RealTorus₄))
          n)
        (intersectionHomologyEquiv D b n a) := by
  refine
    (congrArg (pairHomologyEquiv D b n)
          (SingularMayerVietoris.leftHomologyMap_apply (upperFamily D : Set D.Space)
            (lowerFamily D) n a)).trans
      ?_
  change
    (upperHomologyEquiv D b n
          (SingularMayerVietoris.singularHomologyMap (intersectionToUpper D) n a),
        lowerHomologyEquiv D b n
          (-SingularMayerVietoris.singularHomologyMap (intersectionToLower D) n a)) =
      _
  rw [map_neg, TrianglePeriodFamilyHomologyAlgebra.overlapMap_apply]
  apply Prod.ext
  · exact upperHomologyEquiv_intersection D b n a
  · exact congrArg Neg.neg (lowerHomologyEquiv_intersection D b n a)

private abbrev PeriodFamily.Homology.slitOverlapMap (b : SlitBaseLift) (n : ℕ) :=
  TrianglePeriodFamilyHomologyAlgebra.overlapMap (overlapHomologyAction b 0 n)
    (overlapHomologyAction b 2 n)

private def PeriodFamily.Homology.familyMarkedRight
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) (n : ℕ) :
    (SingularMayerVietoris.SingularHomology RealTorus₄ n ×
        SingularMayerVietoris.SingularHomology RealTorus₄ n) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology D.Space n :=
  (familyRightHomologyMap D n).comp (pairHomologyEquiv D b n).symm.toLinearMap

private def PeriodFamily.Homology.familyMarkedConnecting
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) (n : ℕ) :
    SingularMayerVietoris.SingularHomology D.Space (n + 1) →ₗ[ℤ]
      (SingularMayerVietoris.SingularHomology RealTorus₄ n ×
        (SingularMayerVietoris.SingularHomology RealTorus₄ n ×
          SingularMayerVietoris.SingularHomology RealTorus₄ n)) :=
  (intersectionHomologyEquiv D b n).toLinearMap.comp (familyConnectingHomomorphism D n)

@[simp]
private theorem PeriodFamily.Homology.familyMarkedRight_apply
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology RealTorus₄ n ×
        SingularMayerVietoris.SingularHomology RealTorus₄ n) :
    familyMarkedRight D b n a = familyRightHomologyMap D n ((pairHomologyEquiv D b n).symm a) :=
  rfl

@[simp]
private theorem PeriodFamily.Homology.familyMarkedConnecting_apply
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology D.Space (n + 1)) :
    familyMarkedConnecting D b n a =
      intersectionHomologyEquiv D b n (familyConnectingHomomorphism D n a) :=
  rfl

private theorem PeriodFamily.Homology.slitOverlapMap_intersection
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (familyIntersection D) n) :
    slitOverlapMap b n (intersectionHomologyEquiv D b n a) =
      pairHomologyEquiv D b n (familyLeftHomologyMap D n a) :=
  (pairHomologyEquiv_leftHomologyMap D b n a).symm

private theorem PeriodFamily.Homology.familyMarked_exact_at_pair
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) (n : ℕ) :
    Function.Exact (slitOverlapMap b n) (familyMarkedRight D b n) := by
  intro x
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := (family_exact_at_pair D n ((pairHomologyEquiv D b n).symm x)).mp hx
    refine ⟨intersectionHomologyEquiv D b n a, ?_⟩
    exact
      (slitOverlapMap_intersection D b n a).trans
        ((congrArg (pairHomologyEquiv D b n) ha).trans
          ((pairHomologyEquiv D b n).apply_symm_apply x))
  · rintro ⟨v, rfl⟩
    obtain ⟨a, rfl⟩ := (intersectionHomologyEquiv D b n).surjective v
    rw [familyMarkedRight_apply, slitOverlapMap_intersection, LinearEquiv.symm_apply_apply]
    exact (family_exact_at_pair D n).apply_apply_eq_zero a

private theorem PeriodFamily.Homology.familyMarked_exact_at_ambient
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) (n : ℕ) :
    Function.Exact (familyMarkedRight D b (n + 1)) (familyMarkedConnecting D b n) := by
  intro x
  constructor
  · intro hx
    have hzero : familyConnectingHomomorphism D n x = 0 := by
      apply (intersectionHomologyEquiv D b n).injective
      exact hx.trans (intersectionHomologyEquiv D b n).map_zero.symm
    obtain ⟨a, ha⟩ := (family_exact_at_ambient D n x).mp hzero
    refine ⟨pairHomologyEquiv D b (n + 1) a, ?_⟩
    rw [familyMarkedRight_apply, LinearEquiv.symm_apply_apply]
    exact ha
  · rintro ⟨a, rfl⟩
    rw [familyMarkedConnecting_apply, familyMarkedRight_apply,
      (family_exact_at_ambient D n).apply_apply_eq_zero]
    exact (intersectionHomologyEquiv D b n).map_zero

private theorem PeriodFamily.Homology.familyMarked_exact_at_intersection
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) (n : ℕ) :
    Function.Exact (familyMarkedConnecting D b n) (slitOverlapMap b n) := by
  intro x
  constructor
  · intro hx
    have hzero : familyLeftHomologyMap D n ((intersectionHomologyEquiv D b n).symm x) = 0 := by
      apply (pairHomologyEquiv D b n).injective
      rw [← slitOverlapMap_intersection, LinearEquiv.apply_symm_apply, hx, map_zero]
    obtain ⟨a, ha⟩ :=
      (family_exact_at_intersection D n ((intersectionHomologyEquiv D b n).symm x)).mp hzero
    refine ⟨a, ?_⟩
    rw [familyMarkedConnecting_apply, ha, LinearEquiv.apply_symm_apply]
  · rintro ⟨a, rfl⟩
    exact
      (slitOverlapMap_intersection D b n (familyConnectingHomomorphism D n a)).trans
        ((congrArg (pairHomologyEquiv D b n)
              ((family_exact_at_intersection D n).apply_apply_eq_zero a)).trans
          (pairHomologyEquiv D b n).map_zero)

end Mathoverflow1973

end
