/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology8
public import LeanPool.HopfProblem.HomologyOfX.CuspCoinvariants
import all LeanPool.HopfProblem.Foundations.Core1
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.Lattice.Core1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology2
import all LeanPool.HopfProblem.CuspFibre.CuspCentralHomology2
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology3
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology4
import all LeanPool.HopfProblem.Toric.ToricSpace1
import all LeanPool.HopfProblem.Toric.ToricSpace2
import all LeanPool.HopfProblem.CuspFibre.CuspPositiveRetraction
import all LeanPool.HopfProblem.HomologyTheory.FirstHurewicz3
import all LeanPool.HopfProblem.Elliptic.Core1
import all LeanPool.HopfProblem.Toric.CuspHoneycombHexagon
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology6
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology7
import all LeanPool.HopfProblem.CuspFibre.CuspCentralHomology1
import all LeanPool.HopfProblem.CuspFibre.CuspCentralHomology3
import all LeanPool.HopfProblem.CuspFibre.CuspSpecialization
import all LeanPool.HopfProblem.HomologyOfX.CuspCoinvariants
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology8

/-!
# Hopf problem: cusp fibre · cusp central homology 4

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

private theorem CuspSpecialization.torusDifference_one_coordinates
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) 1) :
    coordinateTorusH1Coordinates (CuspCoinvariants.torusDifference 1 a) =
      CuspCoinvariants.oneDifference (coordinateTorusH1Coordinates a) := by
  rw [CuspCoinvariants.torusDifference_apply, map_sub, coordinateTorusH1Coordinates_matrix]
  simp only [CuspCoinvariants.oneDifference, Matrix.mulVecLin_apply, Matrix.sub_mulVec,
    Matrix.one_mulVec]

private def CuspSpecialization.torusOneCoinvariantEquiv :
    CuspCoinvariants.TorusCoinvariants 1 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  ((CuspCoinvariants.quotientRangeEquiv coordinateTorusH1Coordinates
          (CuspCoinvariants.torusDifference 1) CuspCoinvariants.oneDifference
          torusDifference_one_coordinates).toAddEquiv.trans
      CuspCoinvariants.oneCoinvariantEquiv.toAddEquiv).toIntLinearEquiv

private def CuspCentralHomology.baseTorusPoint (y : CuspHoneycombTiling.Plane) :
    PeriodTorusHigherHomology.ProductTorus 2 :=
  PeriodTorusHigherHomology.coordinateProjection 2 (CuspSpecialization.sourceBaseMarking y)

@[simp]
private theorem CuspCentralHomology.baseTorusPoint_apply (y : CuspHoneycombTiling.Plane) :
    baseTorusPoint y =
      PeriodTorusHigherHomology.coordinateProjection 2 (-ToricSpace.realCuspVector y) :=
  rfl

private theorem CuspCentralHomology.baseTorusPoint_continuous : Continuous baseTorusPoint :=
  (PeriodTorusHigherHomology.coordinateProjection_continuous 2).comp
    CuspSpecialization.sourceBaseMarking.continuous

private theorem
    CuspCentralHomology.baseTorusPoint_surjective : Function.Surjective baseTorusPoint :=
  (PeriodTorusHigherHomology.coordinateProjection_surjective 2).comp
    CuspSpecialization.sourceBaseMarking.surjective

private theorem
    CuspCentralHomology.baseTorusPoint_deck (v : Fin 2 → ℤ) (y : CuspHoneycombTiling.Plane) :
    baseTorusPoint (y + CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector v)) =
      baseTorusPoint y := by
  apply (CuspSpecialization.sourceCoordinateProjection_eq_iff _ _).mpr
  exact ⟨v, CuspSpecialization.sourceBaseMarking_deck v y⟩

private theorem CuspCentralHomology.baseTorusPoint_realCuspVector (y : CuspHoneycombTiling.Plane) :
    baseTorusPoint (ToricSpace.realCuspVector y) =
      PeriodTorusHigherHomology.coordinateProjection 2 y := by
  change
    PeriodTorusHigherHomology.coordinateProjection 2
        (CuspSpecialization.sourceBaseMarking (CuspSpecialization.sourceBaseMarking.symm y)) =
      _
  rw [Homeomorph.apply_symm_apply]

private theorem CuspCentralHomology.baseTorusPoint_eq_iff (y z : CuspHoneycombTiling.Plane) :
    baseTorusPoint y = baseTorusPoint z ↔
      ∃ v : Fin 2 → ℤ, y = z + CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector v) := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := (CuspSpecialization.sourceCoordinateProjection_eq_iff _ _).mp h
    refine ⟨v, CuspSpecialization.sourceBaseMarking.injective ?_⟩
    rw [CuspSpecialization.sourceBaseMarking_deck]
    exact hv
  · rintro ⟨v, rfl⟩
    exact baseTorusPoint_deck v z

private theorem CuspCentralHomology.baseTorusPoint_eq_of_collapse_eq_mo1973_14352
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) (p q : CuspHoneycomb.PhasePlane)
    (h :
      CuspHoneycomb.honeycombCollapseMap C r hr p = CuspHoneycomb.honeycombCollapseMap C r hr q) :
    baseTorusPoint p.2 = baseTorusPoint q.2 := by
  obtain ⟨v, hv, _⟩ := (CuspHoneycomb.honeycombCollapseMap_eq_iff C r hr p q).mp h
  rw [hv, baseTorusPoint_deck]

private def CuspCentralHomology.baseTorusProjection (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) :
    CuspRetraction.QuotientCentralFibre C r → PeriodTorusHigherHomology.ProductTorus 2 :=
  CuspHoneycombHexagon.CommonFibres.descend (CuspHoneycomb.honeycombCollapseMap C r hr)
    (fun p => baseTorusPoint p.2) (CuspHoneycomb.honeycombCollapseMap_surjective C r hr)

@[simp]
private theorem CuspCentralHomology.baseTorusProjection_honeycombCollapseMap
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) (p : CuspHoneycomb.PhasePlane) :
    baseTorusProjection C r hr (CuspHoneycomb.honeycombCollapseMap C r hr p) =
      baseTorusPoint p.2 :=
  CuspHoneycombHexagon.CommonFibres.descend_apply _ _ _
    (baseTorusPoint_eq_of_collapse_eq_mo1973_14352 C r hr) p

private theorem
    CuspCentralHomology.baseTorusProjection_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Continuous (baseTorusProjection C r hr) :=
  CuspHoneycombHexagon.CommonFibres.descend_continuous _ _ _
    (CuspHoneycomb.honeycombCollapseMap_isQuotientMap C r hr hC)
    (baseTorusPoint_continuous.comp continuous_snd)
    (baseTorusPoint_eq_of_collapse_eq_mo1973_14352 C r hr)

private def CuspCentralHomology.baseTorusProjectionMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    C(CuspRetraction.QuotientCentralFibre C r, PeriodTorusHigherHomology.ProductTorus 2) :=
  ⟨baseTorusProjection C r hr, baseTorusProjection_continuous C r hr hC⟩

@[simp]
private theorem
    CuspCentralHomology.baseTorusProjection_productCollapse (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r)
    (p : ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2) :
    baseTorusProjection C r hr (CuspSpecialization.productCollapse C r hr p) = p.2 := by
  rcases p with ⟨u, t⟩
  obtain ⟨y, rfl⟩ := PeriodTorusHigherHomology.coordinateProjection_surjective 2 t
  rw [CuspSpecialization.productCollapse_coordinateProjection,
    baseTorusProjection_honeycombCollapseMap]
  exact baseTorusPoint_realCuspVector y

private def
    CuspCentralHomology.baseTorusSection (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) :
    C(PeriodTorusHigherHomology.ProductTorus 2, CuspRetraction.QuotientCentralFibre C r)
    where
  toFun t := CuspSpecialization.productCollapse C r hr (1, t)
  continuous_toFun :=
    (CuspSpecialization.productCollapse C r hr).continuous.comp
      (continuous_const.prodMk continuous_id)

@[simp]
private theorem
    CuspCentralHomology.baseTorusProjection_section (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (t : PeriodTorusHigherHomology.ProductTorus 2) :
    baseTorusProjection C r hr (baseTorusSection C r hr t) = t :=
  baseTorusProjection_productCollapse C r hr (1, t)

private abbrev CuspCentralHomology.Theta :=
  Suspension (Fin 3)

private def CuspCentralHomology.thetaEdgeIndex (j : Fin 3) : Fin 6 :=
  j.castLE (by decide)

private def CuspCentralHomology.thetaCircleInclusion (j : Fin 3) (z : Circle) : ThreeCircles :=
  ![Sum.inl z, Sum.inr (Sum.inl z), Sum.inr (Sum.inr z)] j

private theorem CuspCentralHomology.thetaCircleInclusion_continuous (j : Fin 3) :
    Continuous (thetaCircleInclusion j) := by
  fin_cases j
  · exact continuous_inl
  · exact continuous_inr.comp continuous_inl
  · exact continuous_inr.comp continuous_inr

private def
    CuspCentralHomology.thetaCharacterMap : C(ToricSpace.CompactFibreTorus × Fin 3, ThreeCircles)
    where
  toFun p := thetaCircleInclusion p.2 (hexagonCharacter (thetaEdgeIndex p.2) p.1)
  continuous_toFun :=
    continuous_prod_of_discrete_right.mpr fun j =>
      (thetaCircleInclusion_continuous j).comp
        (edgeCharacter_continuous (ToricComponent.hexagonRay (thetaEdgeIndex j)))

private def CuspCentralHomology.thetaCharacterCollapseFun_mo1973_14386
    (p : ToricSpace.CompactFibreTorus × Theta) : ThreeCircleSuspension :=
  Quotient.lift (s := suspensionSetoid (Fin 3))
    (fun q => Suspension.mk q.1 (thetaCharacterMap (p.1, q.2)))
    (fun a b hab => by
      apply (Suspension.mk_eq_mk_iff _ _ _ _).mpr
      rcases hab with ⟨ht, hzero | hone | hj⟩
      · exact ⟨ht, Or.inl hzero⟩
      · exact ⟨ht, Or.inr (Or.inl hone)⟩
      · exact ⟨ht, Or.inr (Or.inr (by rw [hj]))⟩)
    p.2

private theorem CuspCentralHomology.thetaCharacterCollapseFun_continuous_mo1973_14387 :
    Continuous thetaCharacterCollapseFun_mo1973_14386 := by
  apply (Suspension.isQuotientMap_mk (X := Fin 3)).continuous_lift_prod_right
  change
    Continuous
      (fun p : ToricSpace.CompactFibreTorus × (unitInterval × Fin 3) =>
        Suspension.mk p.2.1 (thetaCharacterMap (p.1, p.2.2)))
  exact
    Suspension.continuous_mk.comp
      ((continuous_fst.comp continuous_snd).prodMk
        (thetaCharacterMap.continuous.comp
          (continuous_fst.prodMk (continuous_snd.comp continuous_snd))))

private def CuspCentralHomology.thetaCharacterCollapse :
    C(ToricSpace.CompactFibreTorus × Theta, ThreeCircleSuspension) :=
  ⟨thetaCharacterCollapseFun_mo1973_14386, thetaCharacterCollapseFun_continuous_mo1973_14387⟩

@[simp]
private theorem CuspCentralHomology.thetaCharacterCollapse_mk (u : ToricSpace.CompactFibreTorus)
    (t : unitInterval) (j : Fin 3) :
    thetaCharacterCollapse (u, Suspension.mk t j) =
      Suspension.mk t (thetaCircleInclusion j (hexagonCharacter (thetaEdgeIndex j) u)) :=
  rfl

@[simp]
private theorem CuspCentralHomology.thetaCharacterCollapse_height
    (p : ToricSpace.CompactFibreTorus × Theta) :
    Suspension.height (thetaCharacterCollapse p) = Suspension.height p.2 := by
  rcases p with ⟨u, q⟩
  obtain ⟨⟨t, j⟩, rfl⟩ := Suspension.mk_surjective q
  rfl

private def CuspCentralHomology.thetaNorth : Set (ToricSpace.CompactFibreTorus × Theta) :=
  Prod.snd ⁻¹' Suspension.northOpen

private def CuspCentralHomology.thetaSouth : Set (ToricSpace.CompactFibreTorus × Theta) :=
  Prod.snd ⁻¹' Suspension.southOpen

@[simp]
private theorem CuspCentralHomology.mem_thetaNorth (p : ToricSpace.CompactFibreTorus × Theta) :
    p ∈ thetaNorth ↔ (Suspension.height p.2 : ℝ) < 3 / 4 :=
  Iff.rfl

@[simp]
private theorem CuspCentralHomology.mem_thetaSouth (p : ToricSpace.CompactFibreTorus × Theta) :
    p ∈ thetaSouth ↔ 1 / 4 < (Suspension.height p.2 : ℝ) :=
  Iff.rfl

private theorem CuspCentralHomology.thetaNorth_isOpen : IsOpen thetaNorth :=
  Suspension.northOpen_isOpen.preimage continuous_snd

private theorem CuspCentralHomology.thetaSouth_isOpen : IsOpen thetaSouth :=
  Suspension.southOpen_isOpen.preimage continuous_snd

private theorem CuspCentralHomology.theta_open_cover : thetaNorth ∪ thetaSouth = Set.univ := by
  rw [thetaNorth, thetaSouth, ← Set.preimage_union, Suspension.open_cover, Set.preimage_univ]

private theorem CuspCentralHomology.thetaCharacterCollapse_preimage_north :
    thetaCharacterCollapse ⁻¹' Suspension.northOpen = thetaNorth := by
  ext p
  simp only [Set.mem_preimage, Suspension.mem_northOpen, mem_thetaNorth,
    thetaCharacterCollapse_height]

private theorem CuspCentralHomology.thetaCharacterCollapse_preimage_south :
    thetaCharacterCollapse ⁻¹' Suspension.southOpen = thetaSouth := by
  ext p
  simp only [Set.mem_preimage, Suspension.mem_southOpen, mem_thetaSouth,
    thetaCharacterCollapse_height]

private theorem CuspCentralHomology.thetaCharacterCollapse_mapsTo_north :
    Set.MapsTo thetaCharacterCollapse thetaNorth Suspension.northOpen := by
  intro p hp
  rw [← thetaCharacterCollapse_preimage_north] at hp
  exact hp

private theorem CuspCentralHomology.thetaCharacterCollapse_mapsTo_south :
    Set.MapsTo thetaCharacterCollapse thetaSouth Suspension.southOpen := by
  intro p hp
  rw [← thetaCharacterCollapse_preimage_south] at hp
  exact hp

private def CuspCentralHomology.thetaCircleLabel : C(ThreeCircles, Fin 3)
    where
  toFun := Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 2))
  continuous_toFun := continuous_const.sumElim (continuous_const.sumElim continuous_const)

@[simp]
private theorem CuspCentralHomology.thetaCircleLabel_inl (z : _root_.Circle) :
    thetaCircleLabel (Sum.inl z) = 0 :=
  rfl

@[simp]
private theorem CuspCentralHomology.thetaCircleLabel_inr_inl (z : _root_.Circle) :
    thetaCircleLabel (Sum.inr (Sum.inl z)) = 1 :=
  rfl

@[simp]
private theorem CuspCentralHomology.thetaCircleLabel_inr_inr (z : _root_.Circle) :
    thetaCircleLabel (Sum.inr (Sum.inr z)) = 2 :=
  rfl

@[simp]
private theorem CuspCentralHomology.thetaCircleLabel_inclusion (j : Fin 3) (z : _root_.Circle) :
    thetaCircleLabel (thetaCircleInclusion j z) = j := by fin_cases j <;> rfl

private def CuspCentralHomology.thetaForgetCircleFun_mo1973_14410 :
    ThreeCircleSuspension → Theta :=
  Quotient.lift (s := suspensionSetoid ThreeCircles)
    (fun p => Suspension.mk p.1 (thetaCircleLabel p.2))
    (fun a b hab => by
      apply (Suspension.mk_eq_mk_iff _ _ _ _).mpr
      rcases hab with ⟨ht, hzero | hone | hz⟩
      · exact ⟨ht, Or.inl hzero⟩
      · exact ⟨ht, Or.inr (Or.inl hone)⟩
      · exact ⟨ht, Or.inr (Or.inr (congrArg thetaCircleLabel hz))⟩)

private theorem CuspCentralHomology.thetaForgetCircleFun_continuous_mo1973_14411 :
    Continuous thetaForgetCircleFun_mo1973_14410 := by
  apply (Suspension.isQuotientMap_mk (X := ThreeCircles)).continuous_iff.mpr
  change
    Continuous (fun p : unitInterval × ThreeCircles => Suspension.mk p.1 (thetaCircleLabel p.2))
  exact
    Suspension.continuous_mk.comp
      (continuous_fst.prodMk (thetaCircleLabel.continuous.comp continuous_snd))

private def CuspCentralHomology.thetaForgetCircle : C(ThreeCircleSuspension, Theta) :=
  ⟨thetaForgetCircleFun_mo1973_14410, thetaForgetCircleFun_continuous_mo1973_14411⟩

@[simp]
private theorem CuspCentralHomology.thetaForgetCircle_mk (t : unitInterval) (z : ThreeCircles) :
    thetaForgetCircle (Suspension.mk t z) = Suspension.mk t (thetaCircleLabel z) :=
  rfl

private theorem CuspCentralHomology.thetaForgetCircle_circle (t : unitInterval) (j : Fin 3)
    (z : _root_.Circle) :
    thetaForgetCircle (Suspension.mk t (thetaCircleInclusion j z)) = Suspension.mk t j := by
  rw [thetaForgetCircle_mk, thetaCircleLabel_inclusion]

@[simp]
private theorem CuspCentralHomology.thetaForgetCircle_collapse (u : ToricSpace.CompactFibreTorus)
    (q : Theta) : thetaForgetCircle (thetaCharacterCollapse (u, q)) = q := by
  obtain ⟨⟨t, j⟩, rfl⟩ := Suspension.mk_surjective q
  rw [thetaCharacterCollapse_mk, thetaForgetCircle_circle]

private theorem CuspCentralHomology.threePoint_homology_subsingleton (n : ℕ) (hn : n ≠ 0) :
    Subsingleton (SingularMayerVietoris.SingularHomology (Fin 3) n) :=
  PeriodTorusHigherHomology.totallyDisconnected_homology_subsingleton (Fin 3) n hn

private theorem CuspCentralHomology.theta_homology_subsingleton (n : ℕ) :
    Subsingleton (SingularMayerVietoris.SingularHomology Theta (n + 2)) := by
  let := threePoint_homology_subsingleton (n + 1) (Nat.succ_ne_zero n)
  exact
    ((contractibleCoverHomologyHigherEquiv (Suspension.northOpen : Set Theta) Suspension.southOpen
            Suspension.northOpen_isOpen Suspension.southOpen_isOpen Suspension.open_cover n).trans
        (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
          (Suspension.middleBandHomotopyEquiv (X := Fin 3)) (n + 1))).injective.subsingleton

private def CuspCentralHomology.dualSidePoint (k : Fin 6) (t : unitInterval) :
    (CuspHoneycombTiling.Plane) :=
  CuspHoneycombTiling.dualStandardPlaneHomeomorph.symm
    (CuspHoneycombHexagon.sideIntervalHomeomorph k t : (CuspHoneycombTiling.Plane))

private theorem
    CuspCentralHomology.dualSidePoint_continuous (k : Fin 6) : Continuous (dualSidePoint k) :=
  CuspHoneycombTiling.dualStandardPlaneHomeomorph.symm.continuous.comp
    (continuous_subtype_val.comp (CuspHoneycombHexagon.sideIntervalHomeomorph k).continuous)

private theorem CuspCentralHomology.edgeArcBase_eq_dualSidePoint (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (t : unitInterval) :
    (edgeArcBase C₀ k t : (CuspHoneycombTiling.Plane)) = dualSidePoint k t := by
  have h :
    edgeArcBase C₀ k t =
      CuspHoneycombTiling.standardHexagonDualHomeomorph
        ⟨(CuspHoneycombHexagon.sideIntervalHomeomorph k t : (CuspHoneycombTiling.Plane)),
          (CuspHoneycombHexagon.sideIntervalHomeomorph k t).2.1⟩ := by
    apply (CuspHoneycombHexagon.compatibleCellHomeomorph C₀).injective
    rw [compatibleCellHomeomorph_edgeArcBase,
      CuspHoneycombHexagon.compatibleCellHomeomorph_sideInterval]
  exact congrArg Subtype.val h

private def CuspCentralHomology.orientedEdgeBasePoint (t : unitInterval) (j : Fin 3) :
    (CuspHoneycombTiling.Plane) :=
  dualSidePoint (thetaEdgeIndex j) (if j = 1 then unitInterval.symm t else t)

@[simp]
private theorem CuspCentralHomology.orientedEdgeBasePoint_zero (t : unitInterval) :
    orientedEdgeBasePoint t 0 = dualSidePoint 0 t := by
  simp [thetaEdgeIndex, orientedEdgeBasePoint]

@[simp]
private theorem CuspCentralHomology.orientedEdgeBasePoint_one (t : unitInterval) :
    orientedEdgeBasePoint t 1 = dualSidePoint 1 (unitInterval.symm t) := by
  simp [thetaEdgeIndex, orientedEdgeBasePoint]

@[simp]
private theorem CuspCentralHomology.orientedEdgeBasePoint_two (t : unitInterval) :
    orientedEdgeBasePoint t 2 = dualSidePoint 2 t := by
  simp [thetaEdgeIndex, orientedEdgeBasePoint]

private theorem CuspCentralHomology.orientedEdgeBasePoint_continuous (j : Fin 3) :
    Continuous (fun t => orientedEdgeBasePoint t j) := by
  by_cases hj : j = 1
  · simpa only [orientedEdgeBasePoint, ite_eq_left hj, Function.comp_def] using
      (dualSidePoint_continuous (thetaEdgeIndex j)).comp unitInterval.continuous_symm
  · simpa only [orientedEdgeBasePoint, ite_eq_right hj] using
      dualSidePoint_continuous (thetaEdgeIndex j)

private def CuspCentralHomology.thetaBaseCylinder (p : unitInterval × Fin 3) :
    PeriodTorusHigherHomology.ProductTorus 2 :=
  baseTorusPoint (orientedEdgeBasePoint p.1 p.2)

@[simp]
private theorem CuspCentralHomology.thetaBaseCylinder_apply (t : unitInterval) (j : Fin 3) :
    thetaBaseCylinder (t, j) = baseTorusPoint (orientedEdgeBasePoint t j) :=
  rfl

private theorem CuspCentralHomology.thetaBaseCylinder_continuous : Continuous thetaBaseCylinder :=
  continuous_prod_of_discrete_right.mpr fun j =>
    baseTorusPoint_continuous.comp (orientedEdgeBasePoint_continuous j)

@[simp]
private theorem
    CuspCentralHomology.baseTorusProjection_edgeCylinder (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (k : Fin 6) (t : unitInterval) (a : Circle) :
    baseTorusProjection C r hr
        (CuspCollapse.centralProject C r hr (edgeCylinder (C 0) k (t, a))) =
      baseTorusPoint (dualSidePoint k t) := by
  have h :
    CuspCollapse.centralProject C r hr (edgeCylinder (C 0) k (t, a)) =
      CuspHoneycomb.honeycombCollapseMap C r hr
        (hexagonCharacterSection k a, (edgeArcBase (C 0) k t : (CuspHoneycombTiling.Plane))) := by
    change
      CuspCollapse.centralCollapseMap C r hr
          (hexagonCharacterSection k a, edgeArcPositive (C 0) k t) =
        CuspCollapse.centralCollapseMap C r hr
          (hexagonCharacterSection k a,
            CuspHoneycomb.honeycombHomeomorph (C 0)
              (edgeArcBase (C 0) k t : (CuspHoneycombTiling.Plane)))
    rw [honeycombHomeomorph_edgeArcBase]
  rw [h, baseTorusProjection_honeycombCollapseMap, edgeArcBase_eq_dualSidePoint]

private theorem
    CuspCentralHomology.baseTorusProjection_doubleCylinder (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (p : unitInterval × ThreeCircles) :
    baseTorusProjection C r hr (doubleCylinder C r hr p) =
      thetaBaseCylinder (p.1, thetaCircleLabel p.2) := by
  rcases p with ⟨t, a | (a | a)⟩ <;>
    simp only [doubleCylinder_first, doubleCylinder_middle, doubleCylinder_last,
      baseTorusProjection_edgeCylinder, thetaCircleLabel_inl, thetaCircleLabel_inr_inl,
      thetaCircleLabel_inr_inr, thetaBaseCylinder_apply, orientedEdgeBasePoint_zero,
      orientedEdgeBasePoint_one, orientedEdgeBasePoint_two]

private theorem CuspCentralHomology.thetaBaseCylinder_respects (p q : unitInterval × Fin 3)
    (h : (suspensionSetoid (Fin 3)).r p q) : thetaBaseCylinder p = thetaBaseCylinder q := by
  have h' :
    (suspensionSetoid ThreeCircles).r (p.1, thetaCircleInclusion p.2 1)
      (q.1, thetaCircleInclusion q.2 1) := by
    rcases h with ⟨ht, hzero | hone | hj⟩
    · exact ⟨ht, Or.inl hzero⟩
    · exact ⟨ht, Or.inr (Or.inl hone)⟩
    · exact ⟨ht, Or.inr (Or.inr (congrArg (fun j => thetaCircleInclusion j 1) hj))⟩
  have he :=
    congrArg (baseTorusProjection (fun _ => 0) 1 zero_lt_one)
      (doubleCylinder_respects (fun _ => 0) 1 zero_lt_one _ _ h')
  simpa only [baseTorusProjection_doubleCylinder, thetaCircleLabel_inclusion] using he

private def CuspCentralHomology.thetaBaseMapFun_mo1973_14442 :
    Theta → PeriodTorusHigherHomology.ProductTorus 2 :=
  Quotient.lift thetaBaseCylinder thetaBaseCylinder_respects

private theorem CuspCentralHomology.thetaBaseMapFun_continuous_mo1973_14443 :
    Continuous thetaBaseMapFun_mo1973_14442 :=
  (Suspension.isQuotientMap_mk (X := Fin 3)).continuous_iff.mpr thetaBaseCylinder_continuous

private def CuspCentralHomology.thetaBaseMap : C(Theta, PeriodTorusHigherHomology.ProductTorus 2) :=
  ⟨thetaBaseMapFun_mo1973_14442, thetaBaseMapFun_continuous_mo1973_14443⟩

@[simp]
private theorem CuspCentralHomology.thetaBaseMap_mk (t : unitInterval) (j : Fin 3) :
    thetaBaseMap (Suspension.mk t j) = thetaBaseCylinder (t, j) :=
  rfl

private theorem CuspCentralHomology.thetaBaseMap_mk_point (t : unitInterval) (j : Fin 3) :
    thetaBaseMap (Suspension.mk t j) =
      baseTorusPoint
        (dualSidePoint (thetaEdgeIndex j) (if j = 1 then unitInterval.symm t else t)) :=
  rfl

private theorem CuspCentralHomology.thetaBaseMap_mk_zero (t : unitInterval) :
    thetaBaseMap (Suspension.mk t 0) = baseTorusPoint (dualSidePoint 0 t) := by
  simp only [thetaBaseMap_mk, thetaBaseCylinder_apply, orientedEdgeBasePoint_zero]

private theorem CuspCentralHomology.thetaBaseMap_mk_one (t : unitInterval) :
    thetaBaseMap (Suspension.mk t 1) = baseTorusPoint (dualSidePoint 1 (unitInterval.symm t)) := by
  simp only [thetaBaseMap_mk, thetaBaseCylinder_apply, orientedEdgeBasePoint_one]

private theorem CuspCentralHomology.thetaBaseMap_mk_two (t : unitInterval) :
    thetaBaseMap (Suspension.mk t 2) = baseTorusPoint (dualSidePoint 2 t) := by
  simp only [thetaBaseMap_mk, thetaBaseCylinder_apply, orientedEdgeBasePoint_two]

private theorem CuspCentralHomology.thetaBaseMap_homology_eq_zero (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap thetaBaseMap (n + 2) = 0 := by
  let := theta_homology_subsingleton n
  exact Subsingleton.elim _ _

private theorem CuspCentralHomology.baseTorusProjection_doubleSuspensionMap
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) (q : ThreeCircleSuspension) :
    baseTorusProjection C r hr (doubleSuspensionMap C r hr q) =
      thetaBaseMap (thetaForgetCircle q) := by
  obtain ⟨⟨t, a⟩, rfl⟩ := Suspension.mk_surjective q
  rw [doubleSuspensionMap_mk, baseTorusProjection_doubleCylinder, thetaForgetCircle_mk,
    thetaBaseMap_mk]

private theorem CuspCentralHomology.baseTorusProjection_boundary (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 r))
    (hR : ToricSpace.SmallDrift C r) (q : centralBoundary C r hr) :
    baseTorusProjection C r hr (q : CuspRetraction.QuotientCentralFibre C r) =
      thetaBaseMap (thetaForgetCircle (centralBoundarySuspensionHomeomorph C r hr hr1 hC hR q)) :=
  by
  obtain ⟨p, rfl⟩ := (centralBoundarySuspensionHomeomorph C r hr hr1 hC hR).symm.surjective q
  rw [Homeomorph.apply_symm_apply, centralBoundarySuspensionHomeomorph_symm_coe]
  exact baseTorusProjection_doubleSuspensionMap C r hr p

private theorem CuspCentralHomology.baseTorusProjectionMap_comp_boundaryInclusion
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 r))
    (hR : ToricSpace.SmallDrift C r) :
    (baseTorusProjectionMap C r hr hC).comp (centralBoundaryInclusion C r hr) =
      thetaBaseMap.comp
        (thetaForgetCircle.comp
          (centralBoundarySuspensionHomeomorph C r hr hr1 hC hR :
            C(centralBoundary C r hr, ThreeCircleSuspension))) := by
  apply ContinuousMap.ext
  intro q
  exact baseTorusProjection_boundary C r hr hr1 hC hR q

private theorem CuspCentralHomology.baseTorusProjection_boundary_homology_eq_zero
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 r))
    (hR : ToricSpace.SmallDrift C r) (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap
        ((baseTorusProjectionMap C r hr hC).comp (centralBoundaryInclusion C r hr)) (n + 2) =
      0 := by
  rw [baseTorusProjectionMap_comp_boundaryInclusion C r hr hr1 hC hR,
    PeriodTorusHigherHomology.singularHomologyMap_comp, thetaBaseMap_homology_eq_zero,
    LinearMap.zero_comp]

private theorem CuspCentralHomology.baseTorusProjection_boundary_homology_two_eq_zero
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 r))
    (hR : ToricSpace.SmallDrift C r) :
    SingularMayerVietoris.singularHomologyMap
        ((baseTorusProjectionMap C r hr hC).comp (centralBoundaryInclusion C r hr)) 2 =
      0 :=
  baseTorusProjection_boundary_homology_eq_zero C r hr hr1 hC hR 0

private abbrev
    CuspCentralHomology.baseTorusSectionHomologyMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (n : ℕ) :
    SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 2) n →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) n :=
  SingularMayerVietoris.singularHomologyMap (baseTorusSection C r hr) n

private abbrev CuspCentralHomology.baseTorusProjectionHomologyMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (n : ℕ) :
    SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) n →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 2) n :=
  SingularMayerVietoris.singularHomologyMap (baseTorusProjectionMap C r hr hC) n

@[simp]
private theorem
    CuspCentralHomology.baseTorusProjectionMap_comp_section (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    (baseTorusProjectionMap C r hr hC).comp (baseTorusSection C r hr) =
      ContinuousMap.id (PeriodTorusHigherHomology.ProductTorus 2) :=
  ContinuousMap.ext (baseTorusProjection_section C r hr)

@[simp]
private theorem CuspCentralHomology.baseTorusProjectionHomologyMap_comp_section
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (n : ℕ) :
    (baseTorusProjectionHomologyMap C r hr hC n).comp (baseTorusSectionHomologyMap C r hr n) =
      LinearMap.id := by
  rw [← PeriodTorusHigherHomology.singularHomologyMap_comp, baseTorusProjectionMap_comp_section,
    PeriodTorusHigherHomology.singularHomologyMap_id]

@[simp]
private theorem CuspCentralHomology.baseTorusProjectionHomologyMap_section
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 2) n) :
    baseTorusProjectionHomologyMap C r hr hC n (baseTorusSectionHomologyMap C r hr n a) = a :=
  LinearMap.congr_fun (baseTorusProjectionHomologyMap_comp_section C r hr hC n) a

private theorem CuspCentralHomology.baseTorusProjectionHomologyMap_surjective
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (n : ℕ) :
    Function.Surjective (baseTorusProjectionHomologyMap C r hr hC n) :=
  (show
      Function.LeftInverse (baseTorusProjectionHomologyMap C r hr hC n)
        (baseTorusSectionHomologyMap C r hr n)
      from baseTorusProjectionHomologyMap_section C r hr hC n).surjective

private def CuspCentralHomology.baseTorusH2Marking :
    SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 2) 2 ≃ₗ[ℤ] ℤ :=
  (PeriodTorusHigherHomology.productTorusHomologyEquiv 2 2).trans
    (LinearEquiv.funUnique (Fin 1) ℤ ℤ)

private def CuspCentralHomology.baseTorusH2Functional (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) 2 →ₗ[ℤ] ℤ :=
  baseTorusH2Marking.toLinearMap.comp (baseTorusProjectionHomologyMap C r hr hC 2)

private theorem
    CuspCentralHomology.baseTorusH2Functional_boundary (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (hr1 : r < 1) (hR : ToricSpace.SmallDrift C r)
    (a : SingularMayerVietoris.SingularHomology (centralBoundary C r hr) 2) :
    baseTorusH2Functional C r hr hC
        (SingularMayerVietoris.singularHomologyMap (centralBoundaryInclusion C r hr) 2 a) =
      0 := by
  change
    baseTorusH2Marking
        (((baseTorusProjectionHomologyMap C r hr hC 2).comp
            (SingularMayerVietoris.singularHomologyMap (centralBoundaryInclusion C r hr) 2))
          a) =
      0
  rw [← PeriodTorusHigherHomology.singularHomologyMap_comp,
    baseTorusProjection_boundary_homology_two_eq_zero C r hr hr1 hC hR, LinearMap.zero_apply,
    map_zero]

private theorem CuspCentralHomology.baseTorusProjection_homology_one_injective
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Function.Injective (baseTorusProjectionHomologyMap C r hr hC 1) := by
  let := PeriodTorusHigherHomology.productTorus_homology_finite 2 1
  let e :
    SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) 1 ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 2) 1 :=
    (centralSingularH1Equiv C r hr hC).trans
      (PeriodTorusHigherHomology.productTorusHomologyEquiv 2 1).symm
  exact
    IsNoetherian.injective_of_surjective_of_injective e.toLinearMap
      (baseTorusProjectionHomologyMap C r hr hC 1) e.injective
      (baseTorusProjectionHomologyMap_surjective C r hr hC 1)

private theorem CuspCentralHomology.baseTorusSection_homology_one_surjective
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Function.Surjective (baseTorusSectionHomologyMap C r hr 1) := by
  intro a
  refine ⟨baseTorusProjectionHomologyMap C r hr hC 1 a, ?_⟩
  apply baseTorusProjection_homology_one_injective C r hr hC
  exact baseTorusProjectionHomologyMap_section C r hr hC 1 _

private def CuspSpecialization.productBaseTorusSection :
    C(PeriodTorusHigherHomology.ProductTorus 2,
      ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2)
    where
  toFun b := (1, b)
  continuous_toFun := continuous_const.prodMk continuous_id

private theorem CuspSpecialization.productCollapse_comp_baseTorusSection
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) :
    (productCollapse C r hr).comp productBaseTorusSection =
      CuspCentralHomology.baseTorusSection C r hr :=
  ContinuousMap.ext fun _ => rfl

private theorem CuspSpecialization.productCollapse_homology_one_surjective
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Function.Surjective (SingularMayerVietoris.singularHomologyMap (productCollapse C r hr) 1) := by
  intro a
  obtain ⟨b, hb⟩ := CuspCentralHomology.baseTorusSection_homology_one_surjective C r hr hC a
  refine ⟨SingularMayerVietoris.singularHomologyMap productBaseTorusSection 1 b, ?_⟩
  change
    ((SingularMayerVietoris.singularHomologyMap (productCollapse C r hr) 1).comp
          (SingularMayerVietoris.singularHomologyMap productBaseTorusSection 1))
        b =
      a
  rw [← PeriodTorusHigherHomology.singularHomologyMap_comp, productCollapse_comp_baseTorusSection]
  exact hb

private theorem CuspSpecialization.markedCollapse_homology_one_surjective
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Function.Surjective (SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) 1) :=
  markedCollapse_homology_surjective_of_product C r hr 1
    (productCollapse_homology_one_surjective C r hr hC)

private theorem
    CuspSpecialization.markedCollapse_homology_one_kernel (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    LinearMap.ker (SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) 1) =
      LinearMap.range (CuspCoinvariants.torusDifference 1) := by
  let := CuspCentralHomology.centralSingularH1_free C r hr hC
  let := CuspCentralHomology.centralSingularH1_finite C r hr hC
  exact
    CuspCoinvariants.kernel_eq_of_quotient_equiv
      (LinearMap.range (CuspCoinvariants.torusDifference 1)) torusOneCoinvariantEquiv
      (SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) 1)
      (markedCollapse_homology_one_surjective C r hr hC)
      (markedCollapse_homology_range_variation C r hr 1)
      (CuspCentralHomology.centralSingularH1_finrank C r hr hC)

private theorem CuspSpecialization.markedCollapse_homologyOne_surjective
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Function.Surjective (SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) 1) :=
  markedCollapse_homology_one_surjective C r hr hC

private theorem
    CuspSpecialization.markedCollapse_homologyOne_kernel (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    LinearMap.ker (SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) 1) =
      LinearMap.range (CuspCoinvariants.torusDifference 1) :=
  markedCollapse_homology_one_kernel C r hr hC

private theorem CuspCentralHomology.dualSidePoint_mem_frontier (k : Fin 6) (t : unitInterval) :
    dualSidePoint k t ∈ frontier CuspHoneycombTiling.baseCell := by
  rw [← edgeArcBase_eq_dualSidePoint (0 : Matrix (Fin 2) (Fin 2) ℂ) k t]
  exact edgeArcBase_mem_frontier (0 : Matrix (Fin 2) (Fin 2) ℂ) k t

private theorem
    CuspCentralHomology.orientedEdgeBasePoint_mem_frontier (t : unitInterval) (j : Fin 3) :
    orientedEdgeBasePoint t j ∈ frontier CuspHoneycombTiling.baseCell :=
  dualSidePoint_mem_frontier (thetaEdgeIndex j) (if j = 1 then unitInterval.symm t else t)

private def CuspCentralHomology.thetaProductMap :
    C(ToricSpace.CompactFibreTorus × Theta,
      ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2) :=
  (ContinuousMap.id ToricSpace.CompactFibreTorus).prodMap thetaBaseMap

@[simp]
private theorem CuspCentralHomology.thetaProductMap_mk (u : ToricSpace.CompactFibreTorus)
    (t : unitInterval) (j : Fin 3) :
    thetaProductMap (u, Suspension.mk t j) = (u, baseTorusPoint (orientedEdgeBasePoint t j)) :=
  rfl

private theorem
    CuspCentralHomology.productCollapse_thetaProductMap_mk (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (u : ToricSpace.CompactFibreTorus) (t : unitInterval) (j : Fin 3) :
    CuspSpecialization.productCollapse C ε hε (thetaProductMap (u, Suspension.mk t j)) =
      CuspHoneycomb.honeycombCollapseMap C ε hε
        (u * CuspSpecialization.sourcePhaseCharacter (C 0) (orientedEdgeBasePoint t j),
          orientedEdgeBasePoint t j) := by
  rw [thetaProductMap_mk, baseTorusPoint_apply,
    CuspSpecialization.productCollapse_coordinateProjection,
    CuspSpecialization.realCuspVector_neg_realCuspVector]

private theorem CuspCentralHomology.productCollapse_thetaProductMap_mem_centralBoundary
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (p : ToricSpace.CompactFibreTorus × Theta) :
    CuspSpecialization.productCollapse C ε hε (thetaProductMap p) ∈ centralBoundary C ε hε := by
  rcases p with ⟨u, q⟩
  obtain ⟨⟨t, j⟩, rfl⟩ := Suspension.mk_surjective q
  rw [productCollapse_thetaProductMap_mk, centralBoundary_eq_image]
  exact
    ⟨(u * CuspSpecialization.sourcePhaseCharacter (C 0) (orientedEdgeBasePoint t j),
        orientedEdgeBasePoint t j),
      ⟨Set.mem_univ _, orientedEdgeBasePoint_mem_frontier t j⟩, rfl⟩

private def
    CuspCentralHomology.boundaryLift (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    C(ToricSpace.CompactFibreTorus × Theta, centralBoundary C ε hε)
    where
  toFun
    p :=
    ⟨CuspSpecialization.productCollapse C ε hε (thetaProductMap p),
      productCollapse_thetaProductMap_mem_centralBoundary C ε hε p⟩
  continuous_toFun :=
    ((CuspSpecialization.productCollapse C ε hε).continuous.comp
          thetaProductMap.continuous).subtype_mk
      _

private theorem CuspCentralHomology.centralBoundaryInclusion_comp_boundaryLift
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    (centralBoundaryInclusion C ε hε).comp (boundaryLift C ε hε) =
      (CuspSpecialization.productCollapse C ε hε).comp thetaProductMap :=
  rfl

@[simp]
private theorem CuspCentralHomology.boundaryLift_mk_coe (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (u : ToricSpace.CompactFibreTorus) (t : unitInterval) (j : Fin 3) :
    (boundaryLift C ε hε (u, Suspension.mk t j) : CuspRetraction.QuotientCentralFibre C ε) =
      CuspHoneycomb.honeycombCollapseMap C ε hε
        (u * CuspSpecialization.sourcePhaseCharacter (C 0) (orientedEdgeBasePoint t j),
          orientedEdgeBasePoint t j) :=
  productCollapse_thetaProductMap_mk C ε hε u t j

private theorem CuspCentralHomology.centralProject_edgeCylinder_character_dualSide
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (k : Fin 6) (t : unitInterval)
    (u : ToricSpace.CompactFibreTorus) :
    CuspCollapse.centralProject C ε hε (edgeCylinder (C 0) k (t, hexagonCharacter k u)) =
      CuspHoneycomb.honeycombCollapseMap C ε hε (u, dualSidePoint k t) := by
  rw [edgeCylinder_character_all]
  change
    CuspCollapse.centralCollapseMap C ε hε (u, edgeArcPositive (C 0) k t) =
      CuspCollapse.centralCollapseMap C ε hε
        (u, CuspHoneycomb.honeycombHomeomorph (C 0) (dualSidePoint k t))
  rw [← edgeArcBase_eq_dualSidePoint (C 0) k t, honeycombHomeomorph_edgeArcBase]

private theorem CuspCentralHomology.doubleSuspensionMap_character_orientedEdge
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (u : ToricSpace.CompactFibreTorus)
    (t : unitInterval) (j : Fin 3) :
    doubleSuspensionMap C ε hε
        (Suspension.mk t (thetaCircleInclusion j (hexagonCharacter (thetaEdgeIndex j) u))) =
      CuspHoneycomb.honeycombCollapseMap C ε hε (u, orientedEdgeBasePoint t j) := by
  fin_cases j
  · exact centralProject_edgeCylinder_character_dualSide C ε hε 0 t u
  · exact centralProject_edgeCylinder_character_dualSide C ε hε 1 (unitInterval.symm t) u
  · exact centralProject_edgeCylinder_character_dualSide C ε hε 2 t u

private def
    CuspCentralHomology.thetaShearCylinder (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (s : unitInterval)
    (u : ToricSpace.CompactFibreTorus) (t : unitInterval) (j : Fin 3) : ThreeCircleSuspension :=
  Suspension.mk t
    (thetaCircleInclusion j
      (hexagonCharacter (thetaEdgeIndex j)
        (u * CuspSpecialization.sourcePhaseCharacter C₀ ((s : ℝ) • orientedEdgeBasePoint t j))))

private theorem CuspCentralHomology.thetaShearCylinder_respects (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (s : unitInterval) (u : ToricSpace.CompactFibreTorus) (p q : unitInterval × Fin 3)
    (hpq : (suspensionSetoid (Fin 3)).r p q) :
    thetaShearCylinder C₀ s u p.1 p.2 = thetaShearCylinder C₀ s u q.1 q.2 := by
  apply (Suspension.mk_eq_mk_iff _ _ _ _).mpr
  rcases hpq with ⟨ht, hzero | hone | hj⟩
  · exact ⟨ht, Or.inl hzero⟩
  · exact ⟨ht, Or.inr (Or.inl hone)⟩
  · refine ⟨ht, Or.inr (Or.inr ?_)⟩
    rw [ht, hj]

private def CuspCentralHomology.thetaShearLiftFun_mo1973_14554 (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (p : (unitInterval × ToricSpace.CompactFibreTorus) × Theta) : ThreeCircleSuspension :=
  Quotient.lift (s := suspensionSetoid (Fin 3))
    (fun q => thetaShearCylinder C₀ p.1.1 p.1.2 q.1 q.2)
    (thetaShearCylinder_respects C₀ p.1.1 p.1.2) p.2

private theorem CuspCentralHomology.thetaShearCylinder_continuous (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    Continuous
      (fun p : (unitInterval × ToricSpace.CompactFibreTorus) × (unitInterval × Fin 3) =>
        thetaShearCylinder C₀ p.1.1 p.1.2 p.2.1 p.2.2) := by
  have h :
    Continuous
      (fun p : ((unitInterval × ToricSpace.CompactFibreTorus) × unitInterval) × Fin 3 =>
        Suspension.mk p.1.2
          (thetaCircleInclusion p.2
            (hexagonCharacter (thetaEdgeIndex p.2)
              (p.1.1.2 *
                CuspSpecialization.sourcePhaseCharacter C₀
                  ((p.1.1.1 : ℝ) • orientedEdgeBasePoint p.1.2 p.2))))) := by
    apply continuous_prod_of_discrete_right.mpr
    intro j
    exact
      Suspension.continuous_mk.comp
        (continuous_snd.prodMk
          ((thetaCircleInclusion_continuous j).comp
            ((edgeCharacter_continuous (ToricComponent.hexagonRay (thetaEdgeIndex j))).comp
              ((continuous_snd.comp continuous_fst).mul
                ((CuspSpecialization.sourcePhaseCharacter_continuous C₀).comp
                  ((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).smul
                    ((orientedEdgeBasePoint_continuous j).comp continuous_snd)))))))
  exact
    h.comp
      ((continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk
        (continuous_snd.comp continuous_snd))

private theorem CuspCentralHomology.thetaShearLiftFun_continuous_mo1973_14557
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) : Continuous (thetaShearLiftFun_mo1973_14554 C₀) := by
  apply (Suspension.isQuotientMap_mk (X := Fin 3)).continuous_lift_prod_right
  change
    Continuous
      (fun p : (unitInterval × ToricSpace.CompactFibreTorus) × (unitInterval × Fin 3) =>
        thetaShearCylinder C₀ p.1.1 p.1.2 p.2.1 p.2.2)
  exact thetaShearCylinder_continuous C₀

private def CuspCentralHomology.thetaShearMap (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    C(unitInterval × (ToricSpace.CompactFibreTorus × Theta), ThreeCircleSuspension)
    where
  toFun p := thetaShearLiftFun_mo1973_14554 C₀ ((p.1, p.2.1), p.2.2)
  continuous_toFun :=
    (thetaShearLiftFun_continuous_mo1973_14557 C₀).comp
      ((continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk
        (continuous_snd.comp continuous_snd))

@[simp]
private theorem
    CuspCentralHomology.thetaShearMap_mk (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (s : unitInterval)
    (u : ToricSpace.CompactFibreTorus) (t : unitInterval) (j : Fin 3) :
    thetaShearMap C₀ (s, (u, Suspension.mk t j)) = thetaShearCylinder C₀ s u t j :=
  rfl

@[simp]
private theorem CuspCentralHomology.thetaShearMap_zero (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (p : ToricSpace.CompactFibreTorus × Theta) :
    thetaShearMap C₀ (0, p) = thetaCharacterCollapse p := by
  rcases p with ⟨u, q⟩
  obtain ⟨⟨t, j⟩, rfl⟩ := Suspension.mk_surjective q
  rw [thetaShearMap_mk]
  simp [thetaShearCylinder]

private def CuspCentralHomology.shearedThetaCollapse (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    C(ToricSpace.CompactFibreTorus × Theta, ThreeCircleSuspension) :=
  (thetaShearMap C₀).comp ⟨fun p => (1, p), continuous_const.prodMk continuous_id⟩

@[simp]
private theorem CuspCentralHomology.shearedThetaCollapse_mk (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (u : ToricSpace.CompactFibreTorus) (t : unitInterval) (j : Fin 3) :
    shearedThetaCollapse C₀ (u, Suspension.mk t j) =
      Suspension.mk t
        (thetaCircleInclusion j
          (hexagonCharacter (thetaEdgeIndex j)
            (u * CuspSpecialization.sourcePhaseCharacter C₀ (orientedEdgeBasePoint t j)))) := by
  change
    Suspension.mk t
        (thetaCircleInclusion j
          (hexagonCharacter (thetaEdgeIndex j)
            (u *
              CuspSpecialization.sourcePhaseCharacter C₀
                ((1 : ℝ) • orientedEdgeBasePoint t j)))) =
      _
  rw [one_smul]

private def CuspCentralHomology.thetaShearHomotopy (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    thetaCharacterCollapse.Homotopy (shearedThetaCollapse C₀)
    where
  toContinuousMap := thetaShearMap C₀
  map_zero_left := thetaShearMap_zero C₀
  map_one_left _ := rfl

private def CuspCentralHomology.rightPreimageHomeomorph (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (S : Set Y) : (Prod.snd ⁻¹' S : Set (X × Y)) ≃ₜ X × S
    where
  toFun p := (p.1.1, ⟨p.1.2, p.2⟩)
  invFun p := ⟨(p.1, p.2), p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
  continuous_invFun :=
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _

private def CuspCentralHomology.rightPreimageProjection (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (S : Set Y) : C((Prod.snd ⁻¹' S : Set (X × Y)), X) :=
  ⟨fun p => p.1.1, continuous_fst.comp continuous_subtype_val⟩

private def
    CuspCentralHomology.rightPreimageContractibleHomotopyEquiv (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (S : Set Y) [ContractibleSpace S] :
    (Prod.snd ⁻¹' S : Set (X × Y)) ≃ₕ X :=
  (rightPreimageHomeomorph X Y S).toHomotopyEquiv.trans
    (((ContinuousMap.HomotopyEquiv.refl X).prodCongr
          (Classical.choice (ContractibleSpace.hequiv_unit S))).trans
      (Homeomorph.prodUnique X Unit).toHomotopyEquiv)

private theorem CuspCentralHomology.rightPreimageProjection_homology_injective (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (S : Set Y) [ContractibleSpace S] (n : ℕ) :
    Function.Injective
      (SingularMayerVietoris.singularHomologyMap (rightPreimageProjection X Y S) n) :=
  (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
      (rightPreimageContractibleHomotopyEquiv X Y S) n).injective

private def CuspCentralHomology.suspensionMiddleSection (Y : Type) [TopologicalSpace Y] :
    C(Y, Suspension.middleBand Y) :=
  ⟨fun y => Suspension.middleBandHomeomorph.symm (⟨1 / 2, by norm_num⟩, y),
    Suspension.middleBandHomeomorph.symm.continuous.comp (continuous_const.prodMk continuous_id)⟩

@[simp]
private theorem
    CuspCentralHomology.suspensionMiddleSection_coe (Y : Type) [TopologicalSpace Y] (y : Y) :
    (suspensionMiddleSection Y y : Suspension Y) = Suspension.mk ⟨1 / 2, by norm_num⟩ y :=
  rfl

private theorem CuspCentralHomology.suspensionMiddleSection_label (Y : Type) [TopologicalSpace Y]
    (y : Y) : Suspension.middleBandHomotopyEquiv (suspensionMiddleSection Y y) = y := by
  change
    (Suspension.middleBandHomeomorph
          (Suspension.middleBandHomeomorph.symm (⟨1 / 2, by norm_num⟩, y))).2 =
      y
  rw [Homeomorph.apply_symm_apply]

private def CuspCentralHomology.suspensionProductMiddleSection (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (y : Y) :
    C(X, (Prod.snd ⁻¹' Suspension.middleBand Y : Set (X × Suspension Y))) :=
  ⟨fun x => ⟨(x, suspensionMiddleSection Y y), (suspensionMiddleSection Y y).2⟩,
    (continuous_id.prodMk continuous_const).subtype_mk _⟩

private theorem CuspCentralHomology.contractibleTargetCoverMap_homology_surjective (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (U V : Set X) (U' V' : Set Y)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (hU' : IsOpen U')
    (hV' : IsOpen V') (hcover' : U' ∪ V' = Set.univ) [ContractibleSpace U'] [ContractibleSpace V']
    (hfU : Set.MapsTo f U U') (hfV : Set.MapsTo f V V') (n : ℕ)
    (hlift :
      ∀ b : SingularMayerVietoris.SingularHomology (U' ∩ V' : Set Y) n,
        ∃ c : SingularMayerVietoris.SingularHomology (U ∩ V : Set X) n,
          SingularMayerVietoris.leftHomologyMap U V n c = 0 ∧
            SingularMayerVietoris.singularHomologyMap
                (SingularMayerVietoris.intersectionRestriction f U V U' V' hfU hfV) n c =
              b) :
    Function.Surjective (SingularMayerVietoris.singularHomologyMap f (n + 1)) := by
  intro b
  obtain ⟨c, hc, hcb⟩ :=
    hlift (SingularMayerVietoris.connectingHomomorphism U' V' hU' hV' hcover' n b)
  have hr :
    c ∈ LinearMap.range (SingularMayerVietoris.connectingHomomorphism U V hU hV hcover n) := by
    rw [SingularMayerVietoris.exact_at_intersection]
    exact hc
  obtain ⟨a, ha⟩ := hr
  refine ⟨a, contractibleCoverConnecting_injective U' V' hU' hV' hcover' n ?_⟩
  have hn :=
    SingularMayerVietoris.connectingHomomorphism_naturality_apply f U V U' V' hfU hfV hU hV hcover
      hU' hV' hcover' n a
  rw [ha, hcb] at hn
  exact hn.symm

private abbrev CuspCentralHomology.ThetaBelt :=
  thetaNorth ∩ thetaSouth

private def CuspCentralHomology.thetaBeltSection (j : Fin 3) :
    C(ToricSpace.CompactFibreTorus, ThetaBelt) :=
  suspensionProductMiddleSection ToricSpace.CompactFibreTorus (Fin 3) j

@[simp]
private theorem
    CuspCentralHomology.thetaBeltSection_coe (j : Fin 3) (u : ToricSpace.CompactFibreTorus) :
    (thetaBeltSection j u : ToricSpace.CompactFibreTorus × Theta) =
      (u, Suspension.mk ⟨1 / 2, by norm_num⟩ j) :=
  rfl

private def CuspCentralHomology.thetaBeltProjection : C(ThetaBelt, ToricSpace.CompactFibreTorus) :=
  rightPreimageProjection ToricSpace.CompactFibreTorus Theta (Suspension.middleBand (Fin 3))

@[simp]
private theorem CuspCentralHomology.thetaBeltProjection_comp_section (j : Fin 3) :
    thetaBeltProjection.comp (thetaBeltSection j) =
      ContinuousMap.id ToricSpace.CompactFibreTorus :=
  rfl

@[simp]
private theorem CuspCentralHomology.thetaBeltProjection_homology_section (j : Fin 3) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology ToricSpace.CompactFibreTorus n) :
    SingularMayerVietoris.singularHomologyMap thetaBeltProjection n
        (SingularMayerVietoris.singularHomologyMap (thetaBeltSection j) n a) =
      a := by
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp,
    thetaBeltProjection_comp_section, PeriodTorusHigherHomology.singularHomologyMap_id,
    LinearMap.id_apply]

private def CuspCentralHomology.thetaBeltSum
    (v : Fin 3 → SingularMayerVietoris.SingularHomology ToricSpace.CompactFibreTorus 1) :
    SingularMayerVietoris.SingularHomology ThetaBelt 1 :=
  ∑ j, SingularMayerVietoris.singularHomologyMap (thetaBeltSection j) 1 (v j)

@[simp]
private theorem CuspCentralHomology.thetaBeltProjection_homology_sum
    (v : Fin 3 → SingularMayerVietoris.SingularHomology ToricSpace.CompactFibreTorus 1) :
    SingularMayerVietoris.singularHomologyMap thetaBeltProjection 1 (thetaBeltSum v) = ∑ j, v j :=
  by simp only [thetaBeltSum, map_sum, thetaBeltProjection_homology_section]

private theorem CuspCentralHomology.thetaBelt_mem_ker_of_projection_eq_zero (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology ThetaBelt n)
    (ha : SingularMayerVietoris.singularHomologyMap thetaBeltProjection n a = 0) :
    SingularMayerVietoris.leftHomologyMap thetaNorth thetaSouth n a = 0 := by
  have hleft :
    SingularMayerVietoris.singularHomologyMap
        (ContinuousMap.inclusion (Set.inter_subset_left : ThetaBelt ⊆ thetaNorth)) n a =
      0 := by
    let proj : C(thetaNorth, ToricSpace.CompactFibreTorus) :=
      rightPreimageProjection ToricSpace.CompactFibreTorus Theta Suspension.northOpen
    apply
      (show Function.Injective (SingularMayerVietoris.singularHomologyMap proj n) from
        rightPreimageProjection_homology_injective ToricSpace.CompactFibreTorus Theta
          Suspension.northOpen n)
    rw [map_zero, ← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp]
    exact ha
  have hright :
    SingularMayerVietoris.singularHomologyMap
        (ContinuousMap.inclusion (Set.inter_subset_right : ThetaBelt ⊆ thetaSouth)) n a =
      0 := by
    let proj : C(thetaSouth, ToricSpace.CompactFibreTorus) :=
      rightPreimageProjection ToricSpace.CompactFibreTorus Theta Suspension.southOpen
    apply
      (show Function.Injective (SingularMayerVietoris.singularHomologyMap proj n) from
        rightPreimageProjection_homology_injective ToricSpace.CompactFibreTorus Theta
          Suspension.southOpen n)
    rw [map_zero, ← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp]
    exact ha
  rw [SingularMayerVietoris.leftHomologyMap_apply, hleft, hright, neg_zero]
  rfl

private theorem CuspCentralHomology.thetaBeltSum_mem_ker
    (v : Fin 3 → SingularMayerVietoris.SingularHomology ToricSpace.CompactFibreTorus 1)
    (hv : ∑ j, v j = 0) :
    SingularMayerVietoris.leftHomologyMap thetaNorth thetaSouth 1 (thetaBeltSum v) = 0 := by
  apply thetaBelt_mem_ker_of_projection_eq_zero
  rw [thetaBeltProjection_homology_sum, hv]

private def CuspCentralHomology.thetaCircleMap (j : Fin 3) : C(_root_.Circle, ThreeCircles) :=
  ⟨thetaCircleInclusion j, thetaCircleInclusion_continuous j⟩

private theorem CuspCentralHomology.thetaCircleMap_zero :
    thetaCircleMap 0 =
      PeriodTorusHigherHomology.sumInlMap _root_.Circle (_root_.Circle ⊕ _root_.Circle) :=
  rfl

private theorem CuspCentralHomology.thetaCircleMap_one :
    thetaCircleMap 1 =
      (PeriodTorusHigherHomology.sumInrMap _root_.Circle (_root_.Circle ⊕ _root_.Circle)).comp
        (PeriodTorusHigherHomology.sumInlMap _root_.Circle _root_.Circle) :=
  rfl

private theorem CuspCentralHomology.thetaCircleMap_two :
    thetaCircleMap 2 =
      (PeriodTorusHigherHomology.sumInrMap _root_.Circle (_root_.Circle ⊕ _root_.Circle)).comp
        (PeriodTorusHigherHomology.sumInrMap _root_.Circle _root_.Circle) :=
  rfl

private theorem CuspCentralHomology.threeCirclesHomologySplit_apply_mo1973_14596 (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology ThreeCircles n) :
    threeCirclesHomologySplit n a =
      ((PeriodTorusHigherHomology.sumHomologyEquiv _root_.Circle (_root_.Circle ⊕ _root_.Circle) n
            a).1,
        PeriodTorusHigherHomology.sumHomologyEquiv _root_.Circle _root_.Circle n
          (PeriodTorusHigherHomology.sumHomologyEquiv _root_.Circle
              (_root_.Circle ⊕ _root_.Circle) n a).2) :=
  rfl

private theorem CuspCentralHomology.thetaCircleMap_homologySplit (j : Fin 3) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology _root_.Circle n) :
    threeCirclesHomologySplit n
        (SingularMayerVietoris.singularHomologyMap (thetaCircleMap j) n a) =
      ![(a, (0, 0)), (0, (a, 0)), (0, (0, a))] j := by
  fin_cases j <;>
    simp [thetaCircleMap_zero, thetaCircleMap_one, thetaCircleMap_two,
      PeriodTorusHigherHomology.singularHomologyMap_comp,
      threeCirclesHomologySplit_apply_mo1973_14596]
  rfl

private theorem CuspCentralHomology.threeCirclesHomologyOneEquiv_apply_mo1973_14598
    (a : SingularMayerVietoris.SingularHomology ThreeCircles 1) :
    threeCirclesHomologyOneEquiv a =
      ![unitCircleHomologyOneEquiv (threeCirclesHomologySplit 1 a).1,
        unitCircleHomologyOneEquiv (threeCirclesHomologySplit 1 a).2.1,
        unitCircleHomologyOneEquiv (threeCirclesHomologySplit 1 a).2.2] :=
  rfl

private theorem CuspCentralHomology.thetaCircleMap_homologyOne (j : Fin 3)
    (a : SingularMayerVietoris.SingularHomology _root_.Circle 1) :
    threeCirclesHomologyOneEquiv
        (SingularMayerVietoris.singularHomologyMap (thetaCircleMap j) 1 a) =
      Pi.single j (unitCircleHomologyOneEquiv a) := by
  rw [threeCirclesHomologyOneEquiv_apply_mo1973_14598, thetaCircleMap_homologySplit]
  fin_cases j <;> funext k <;> fin_cases k <;> simp

private noncomputable def CuspCentralHomology.thetaTargetBeltHomologyEquiv :
    SingularMayerVietoris.SingularHomology (Suspension.middleBand ThreeCircles) 1 ≃ₗ[ℤ]
      (Fin 3 → ℤ) :=
  (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
        (Suspension.middleBandHomotopyEquiv (X := ThreeCircles)) 1).trans
    threeCirclesHomologyOneEquiv

private theorem CuspCentralHomology.thetaTargetBeltHomologyEquiv_middleSection
    (a : SingularMayerVietoris.SingularHomology ThreeCircles 1) :
    thetaTargetBeltHomologyEquiv
        (SingularMayerVietoris.singularHomologyMap (suspensionMiddleSection ThreeCircles) 1 a) =
      threeCirclesHomologyOneEquiv a := by
  have hsection :
    (Suspension.middleBandHomotopyEquiv (X := ThreeCircles)).toFun.comp
        (suspensionMiddleSection ThreeCircles) =
      ContinuousMap.id ThreeCircles := by
    apply ContinuousMap.ext
    exact suspensionMiddleSection_label ThreeCircles
  change
    threeCirclesHomologyOneEquiv
        (((SingularMayerVietoris.singularHomologyMap
                (Suspension.middleBandHomotopyEquiv (X := ThreeCircles)).toFun 1).comp
            (SingularMayerVietoris.singularHomologyMap (suspensionMiddleSection ThreeCircles) 1))
          a) =
      _
  rw [← PeriodTorusHigherHomology.singularHomologyMap_comp, hsection,
    PeriodTorusHigherHomology.singularHomologyMap_id]
  rfl

private def CuspCentralHomology.thetaEdgeCharacterMap (j : Fin 3) :
    C(ToricSpace.CompactFibreTorus, _root_.Circle) :=
  ⟨hexagonCharacter (thetaEdgeIndex j),
    edgeCharacter_continuous (ToricComponent.hexagonRay (thetaEdgeIndex j))⟩

private def CuspCentralHomology.thetaBeltMap : C(ThetaBelt, Suspension.middleBand ThreeCircles) :=
  SingularMayerVietoris.intersectionRestriction thetaCharacterCollapse thetaNorth thetaSouth
    Suspension.northOpen Suspension.southOpen thetaCharacterCollapse_mapsTo_north
    thetaCharacterCollapse_mapsTo_south

private theorem CuspCentralHomology.thetaBeltMap_comp_section (j : Fin 3) :
    thetaBeltMap.comp (thetaBeltSection j) =
      (suspensionMiddleSection ThreeCircles).comp
        ((thetaCircleMap j).comp (thetaEdgeCharacterMap j)) := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  change
    thetaCharacterCollapse (thetaBeltSection j u : ToricSpace.CompactFibreTorus × Theta) =
      (suspensionMiddleSection ThreeCircles (thetaCircleMap j (thetaEdgeCharacterMap j u)) :
        ThreeCircleSuspension)
  rw [thetaBeltSection_coe, suspensionMiddleSection_coe, thetaCharacterCollapse_mk]
  rfl

private theorem CuspCentralHomology.thetaBeltMap_homologyOne_section (j : Fin 3)
    (a : SingularMayerVietoris.SingularHomology ToricSpace.CompactFibreTorus 1) :
    thetaTargetBeltHomologyEquiv
        (SingularMayerVietoris.singularHomologyMap thetaBeltMap 1
          (SingularMayerVietoris.singularHomologyMap (thetaBeltSection j) 1 a)) =
      Pi.single j
        (unitCircleHomologyOneEquiv
          (SingularMayerVietoris.singularHomologyMap (thetaEdgeCharacterMap j) 1 a)) := by
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp,
    thetaBeltMap_comp_section, PeriodTorusHigherHomology.singularHomologyMap_comp,
    LinearMap.comp_apply, thetaTargetBeltHomologyEquiv_middleSection,
    PeriodTorusHigherHomology.singularHomologyMap_comp, LinearMap.comp_apply,
    thetaCircleMap_homologyOne]

private theorem CuspCentralHomology.thetaBeltMap_homologyOne_sum
    (v : Fin 3 → SingularMayerVietoris.SingularHomology ToricSpace.CompactFibreTorus 1) :
    thetaTargetBeltHomologyEquiv
        (SingularMayerVietoris.singularHomologyMap thetaBeltMap 1 (thetaBeltSum v)) =
      fun j =>
      unitCircleHomologyOneEquiv
        (SingularMayerVietoris.singularHomologyMap (thetaEdgeCharacterMap j) 1 (v j)) := by
  simp only [thetaBeltSum, map_sum, thetaBeltMap_homologyOne_section]
  funext j
  simp

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def CuspCentralHomology.compactPhaseH1IndexEquiv : Fin 2 ≃ Fin (Nat.choose 2 1) :=
  Fin.revPerm.trans (finCongr (by decide))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def CuspCentralHomology.compactPhaseH1OrderEquiv :
    PeriodTorusHigherHomology.binomialModule 2 1 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  ({    toFun v i := v (compactPhaseH1IndexEquiv i)
        invFun v i := v (compactPhaseH1IndexEquiv.symm i)
        left_inv v := by ext i; exact congrArg v (compactPhaseH1IndexEquiv.apply_symm_apply i)
        right_inv v := by ext i; exact congrArg v (compactPhaseH1IndexEquiv.symm_apply_apply i)
        map_add' _ _ := rfl } :
      PeriodTorusHigherHomology.binomialModule 2 1 ≃+ (Fin 2 → ℤ)).toIntLinearEquiv

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def CuspCentralHomology.compactPhaseH1Equiv :
    SingularMayerVietoris.SingularHomology ToricSpace.CompactFibreTorus 1 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  ((PeriodTorusHigherHomology.homeomorphHomologyEquiv compactFibreTorusHomeomorph 1).trans
        (PeriodTorusHigherHomology.productTorusHomologyEquiv 2 1)).trans
    compactPhaseH1OrderEquiv

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def CuspCentralHomology.compactPhaseCircleMap (v : Fin 2 → ℤ) :
    C(_root_.Circle, ToricSpace.CompactFibreTorus) :=
  ⟨ToricSpace.edgeCompactPhase v, ToricSpace.edgeCompactPhase_continuous v⟩

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem CuspCentralHomology.compactPhaseCircleMap_coordinates (v : Fin 2 → ℤ) :
    (compactFibreTorusHomeomorph :
            C(ToricSpace.CompactFibreTorus, PeriodTorusHigherHomology.ProductTorus 2)).comp
        ((compactPhaseCircleMap v).comp
          (circleCoordinateHomeomorph.symm : C(AddCircle (1 : ℝ), _root_.Circle))) =
      PeriodTorusHigherHomology.coordinateCircleMap v := by
  apply ContinuousMap.ext
  intro z
  ext i
  change circleCoordinateHomeomorph (circleCoordinateHomeomorph.symm z ^ v i) = v i • z
  rw [circleCoordinateHomeomorph_zpow, Homeomorph.apply_symm_apply]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem CuspCentralHomology.compactPhaseCircleMap_positiveHomology (v : Fin 2 → ℤ) :
    PeriodTorusHigherHomology.homeomorphHomologyEquiv compactFibreTorusHomeomorph 1
        (SingularMayerVietoris.singularHomologyMap (compactPhaseCircleMap v) 1
          (unitCircleHomologyOneEquiv.symm 1)) =
      FirstHurewicz.loopHomologyClass (PeriodTorusHigherHomology.coordinatePeriodLoop 2 v) := by
  change
    ((SingularMayerVietoris.singularHomologyMap
              (compactFibreTorusHomeomorph :
                C(ToricSpace.CompactFibreTorus, PeriodTorusHigherHomology.ProductTorus 2))
              1).comp
          ((SingularMayerVietoris.singularHomologyMap (compactPhaseCircleMap v) 1).comp
            (SingularMayerVietoris.singularHomologyMap
              (circleCoordinateHomeomorph.symm : C(AddCircle (1 : ℝ), _root_.Circle)) 1)))
        (PeriodTorusHigherHomology.circleHomologyOneEquiv.symm 1) =
      _
  rw [← PeriodTorusHigherHomology.singularHomologyMap_comp, ←
    PeriodTorusHigherHomology.singularHomologyMap_comp, compactPhaseCircleMap_coordinates,
    PeriodTorusHigherHomology.circleHomologyOneEquiv_symm_one]
  exact PeriodTorusHigherHomology.coordinateCircleMap_positiveHomology v

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem CuspCentralHomology.compactPhase_coordinateTorusClass (i : Fin 2) :
    PeriodTorusHigherHomology.coordinateTorusClass 2 1 (compactPhaseH1IndexEquiv i) =
      FirstHurewicz.loopHomologyClass
        (PeriodTorusHigherHomology.coordinatePeriodLoop 2 (Pi.single i 1)) := by
  rw [PeriodTorusHigherHomology.coordinateTorusClass,
    PeriodTorusHigherHomology.productTorusTopClass_one,
    PeriodTorusHigherHomology.coordinateTorusMap_eq_torusMatrixMap]
  change
    FirstHurewicz.inducedHomology
        (PeriodTorusHigherHomology.torusMatrixMap
          (PeriodTorusHigherHomology.coordinateTorusMatrix 2 1 (compactPhaseH1IndexEquiv i)))
        (FirstHurewicz.loopHomologyClass
          (PeriodTorusHigherHomology.coordinatePeriodLoop 1 (Pi.single 0 1))) =
      _
  rw [PeriodTorusHigherHomology.torusMatrixMap_coordinatePeriodHomology]
  congr 2
  fin_cases i <;> decide

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def CuspCentralHomology.compactPhaseCoordinateClass (i : Fin 2) :
    SingularMayerVietoris.SingularHomology ToricSpace.CompactFibreTorus 1 :=
  SingularMayerVietoris.singularHomologyMap (compactPhaseCircleMap (Pi.single i 1)) 1
    (unitCircleHomologyOneEquiv.symm 1)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem CuspCentralHomology.compactPhaseH1Equiv_coordinateClass (i : Fin 2) :
    compactPhaseH1Equiv (compactPhaseCoordinateClass i) = Pi.single i 1 := by
  change
    compactPhaseH1OrderEquiv
        (PeriodTorusHigherHomology.productTorusHomologyEquiv 2 1
          (PeriodTorusHigherHomology.homeomorphHomologyEquiv compactFibreTorusHomeomorph 1
            (SingularMayerVietoris.singularHomologyMap (compactPhaseCircleMap (Pi.single i 1)) 1
              (unitCircleHomologyOneEquiv.symm 1)))) =
      _
  rw [compactPhaseCircleMap_positiveHomology, ← compactPhase_coordinateTorusClass,
    PeriodTorusHigherHomology.productTorusHomologyEquiv_coordinateTorusClass]
  ext j
  fin_cases i <;> fin_cases j <;> rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem CuspCentralHomology.compactPhaseH1Equiv_symm_single (i : Fin 2) :
    compactPhaseH1Equiv.symm (Pi.single i 1) = compactPhaseCoordinateClass i := by
  apply compactPhaseH1Equiv.injective
  rw [LinearEquiv.apply_symm_apply, compactPhaseH1Equiv_coordinateClass]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem CuspCentralHomology.compactPhaseH1Equiv_symm_apply (v : Fin 2 → ℤ) :
    compactPhaseH1Equiv.symm v =
      v 0 • compactPhaseCoordinateClass 0 + v 1 • compactPhaseCoordinateClass 1 := by
  have hv : v = v 0 • Pi.single 0 1 + v 1 • Pi.single 1 1 := by
    ext i
    fin_cases i <;> simp
  conv_lhs => rw [hv]
  rw [map_add, map_zsmul, map_zsmul, compactPhaseH1Equiv_symm_single,
    compactPhaseH1Equiv_symm_single]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def CuspCentralHomology.compactPhaseCoordinateHomology :
    (Fin 2 → ℤ) →ₗ[ℤ] SingularMayerVietoris.SingularHomology ToricSpace.CompactFibreTorus 1 :=
  compactPhaseH1Equiv.symm.toLinearMap

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem CuspCentralHomology.compactPhaseCoordinateHomology_apply (v : Fin 2 → ℤ) :
    compactPhaseCoordinateHomology v =
      v 0 • compactPhaseCoordinateClass 0 + v 1 • compactPhaseCoordinateClass 1 :=
  compactPhaseH1Equiv_symm_apply v

private def CuspCentralHomology.circlePowerMap (k : ℤ) : C(_root_.Circle, _root_.Circle) :=
  ⟨fun z => z ^ k, continuous_id.zpow k⟩

private def CuspCentralHomology.additiveCirclePowerMap_mo1973_14639 (k : ℤ) :
    C(AddCircle (1 : ℝ), AddCircle (1 : ℝ)) :=
  ⟨fun z => k • z, continuous_id.zsmul k⟩

private def CuspCentralHomology.firstCircleProjection_mo1973_14640 :
    C(PeriodTorusHigherHomology.ProductTorus 4, AddCircle (1 : ℝ)) :=
  ⟨fun x => x 0, continuous_apply 0⟩

private theorem CuspCentralHomology.firstCircleProjection_positiveLoop_mo1973_14641 :
    (PeriodTorusHigherHomology.coordinatePeriodLoop 4 (Pi.single (0 : Fin 4) 1)).map
        firstCircleProjection_mo1973_14640.continuous =
      PeriodTorusHigherHomology.CirclePaths.positiveLoop := by
  apply Path.ext
  funext t
  change
    PeriodTorusHigherHomology.coordinatePeriodLoop 4 (Pi.single (0 : Fin 4) 1) t 0 =
      PeriodTorusHigherHomology.CirclePaths.positiveLoop t
  simp only [PeriodTorusHigherHomology.coordinatePeriodLoop_apply, Pi.single_eq_same,
    Int.cast_one, mul_one, PeriodTorusHigherHomology.CirclePaths.positiveLoop_apply]

private theorem CuspCentralHomology.firstCircleProjection_scalarLoop_mo1973_14642 (k : ℤ) :
    (PeriodTorusHigherHomology.coordinatePeriodLoop 4 (k • Pi.single (0 : Fin 4) 1)).map
        firstCircleProjection_mo1973_14640.continuous =
      (PeriodTorusHigherHomology.CirclePaths.positiveLoop.map
            (additiveCirclePowerMap_mo1973_14639 k).continuous).cast
        (by simp [additiveCirclePowerMap_mo1973_14639, firstCircleProjection_mo1973_14640])
        (by simp [additiveCirclePowerMap_mo1973_14639, firstCircleProjection_mo1973_14640]) := by
  apply Path.ext
  funext t
  change
    PeriodTorusHigherHomology.coordinatePeriodLoop 4 (k • Pi.single (0 : Fin 4) 1) t 0 =
      k • PeriodTorusHigherHomology.CirclePaths.positiveLoop t
  rw [PeriodTorusHigherHomology.coordinatePeriodLoop_apply,
    PeriodTorusHigherHomology.CirclePaths.positiveLoop_apply]
  simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  change (((t : ℝ) * (k : ℝ) : ℝ) : AddCircle (1 : ℝ)) = ((k • (t : ℝ) : ℝ) : AddCircle (1 : ℝ))
  congr 1
  simp only [zsmul_eq_mul, mul_comm]

private theorem CuspCentralHomology.additiveCirclePowerMap_positiveClass_mo1973_14643 (k : ℤ) :
    SingularMayerVietoris.singularHomologyMap (additiveCirclePowerMap_mo1973_14639 k) 1
        (FirstHurewicz.loopHomologyClass PeriodTorusHigherHomology.CirclePaths.positiveLoop) =
      k • FirstHurewicz.loopHomologyClass PeriodTorusHigherHomology.CirclePaths.positiveLoop := by
  have h :=
    congrArg (FirstHurewicz.inducedHomology firstCircleProjection_mo1973_14640)
      (map_zsmul (PeriodTorusHigherHomology.coordinateH1 4) k (Pi.single (0 : Fin 4) 1))
  rw [PeriodTorusHigherHomology.coordinateH1_four_apply (Elliptic.examplePeriod .four),
    PeriodTorusHigherHomology.coordinateH1_single, map_zsmul,
    FirstHurewicz.inducedHomology_loopHomologyClass,
    FirstHurewicz.inducedHomology_loopHomologyClass,
    firstCircleProjection_scalarLoop_mo1973_14642,
    firstCircleProjection_positiveLoop_mo1973_14641] at h
  rw [SingularMayerVietoris.singularHomologyMap_one,
    FirstHurewicz.inducedHomology_loopHomologyClass]
  exact h

private theorem CuspCentralHomology.additiveCirclePowerMap_homology_mo1973_14644 (k : ℤ)
    (a : SingularMayerVietoris.SingularHomology (AddCircle (1 : ℝ)) 1) :
    PeriodTorusHigherHomology.circleHomologyOneEquiv
        (SingularMayerVietoris.singularHomologyMap (additiveCirclePowerMap_mo1973_14639 k) 1 a) =
      k * PeriodTorusHigherHomology.circleHomologyOneEquiv a := by
  obtain ⟨m, rfl⟩ := PeriodTorusHigherHomology.circleHomologyOneEquiv.symm.surjective a
  rw [LinearEquiv.apply_symm_apply, PeriodTorusHigherHomology.circleHomologyOneEquiv_symm_int,
    map_zsmul, additiveCirclePowerMap_positiveClass_mo1973_14643, map_zsmul, map_zsmul,
    PeriodTorusHigherHomology.circleHomologyOneEquiv_positiveLoop]
  simp [mul_comm]

private theorem CuspCentralHomology.circlePowerMap_coordinate_mo1973_14645 (k : ℤ) :
    (circleCoordinateHomeomorph : C(_root_.Circle, AddCircle (1 : ℝ))).comp (circlePowerMap k) =
      (additiveCirclePowerMap_mo1973_14639 k).comp
        (circleCoordinateHomeomorph : C(_root_.Circle, AddCircle (1 : ℝ))) := by
  apply ContinuousMap.ext
  intro z
  exact circleCoordinateHomeomorph_zpow z k

private theorem CuspCentralHomology.unitCircleHomologyOneEquiv_circlePowerMap (k : ℤ)
    (a : SingularMayerVietoris.SingularHomology _root_.Circle 1) :
    unitCircleHomologyOneEquiv
        (SingularMayerVietoris.singularHomologyMap (circlePowerMap k) 1 a) =
      k * unitCircleHomologyOneEquiv a := by
  change
    PeriodTorusHigherHomology.circleHomologyOneEquiv
        (SingularMayerVietoris.singularHomologyMap
          (circleCoordinateHomeomorph : C(_root_.Circle, AddCircle (1 : ℝ))) 1
          (SingularMayerVietoris.singularHomologyMap (circlePowerMap k) 1 a)) =
      k *
        PeriodTorusHigherHomology.circleHomologyOneEquiv
          (SingularMayerVietoris.singularHomologyMap
            (circleCoordinateHomeomorph : C(_root_.Circle, AddCircle (1 : ℝ))) 1 a)
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp,
    circlePowerMap_coordinate_mo1973_14645, PeriodTorusHigherHomology.singularHomologyMap_comp,
    LinearMap.comp_apply]
  exact additiveCirclePowerMap_homology_mo1973_14644 k _

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def CuspCentralHomology.edgeCharacterMap (n : Fin 2 → ℤ) :
    C(ToricSpace.CompactFibreTorus, _root_.Circle) :=
  ⟨edgeCharacter n, edgeCharacter_continuous n⟩

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem CuspCentralHomology.edgeCharacterMap_comp_circle (n v : Fin 2 → ℤ) :
    (edgeCharacterMap n).comp (compactPhaseCircleMap v) =
      circlePowerMap (n 0 * v 1 - n 1 * v 0) := by
  apply ContinuousMap.ext
  intro z
  exact edgeCharacter_edgeCompactPhase n v z

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem CuspCentralHomology.edgeCharacter_circleHomology (n v : Fin 2 → ℤ) :
    unitCircleHomologyOneEquiv
        (SingularMayerVietoris.singularHomologyMap (edgeCharacterMap n) 1
          (SingularMayerVietoris.singularHomologyMap (compactPhaseCircleMap v) 1
            (unitCircleHomologyOneEquiv.symm 1))) =
      -n 1 * v 0 + n 0 * v 1 := by
  change
    unitCircleHomologyOneEquiv
        (((SingularMayerVietoris.singularHomologyMap (edgeCharacterMap n) 1).comp
            (SingularMayerVietoris.singularHomologyMap (compactPhaseCircleMap v) 1))
          (unitCircleHomologyOneEquiv.symm 1)) =
      _
  rw [← PeriodTorusHigherHomology.singularHomologyMap_comp, edgeCharacterMap_comp_circle,
    unitCircleHomologyOneEquiv_circlePowerMap, LinearEquiv.apply_symm_apply, mul_one]
  ring

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem CuspCentralHomology.edgeCharacter_coordinateClass_zero (n : Fin 2 → ℤ) :
    unitCircleHomologyOneEquiv
        (SingularMayerVietoris.singularHomologyMap (edgeCharacterMap n) 1
          (compactPhaseCoordinateClass 0)) =
      -n 1 := by
  simpa only [compactPhaseCoordinateClass, Pi.single_eq_same,
    Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0), mul_one, MulZeroClass.mul_zero,
    add_zero] using edgeCharacter_circleHomology n (Pi.single 0 1)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem CuspCentralHomology.edgeCharacter_coordinateClass_one (n : Fin 2 → ℤ) :
    unitCircleHomologyOneEquiv
        (SingularMayerVietoris.singularHomologyMap (edgeCharacterMap n) 1
          (compactPhaseCoordinateClass 1)) =
      n 0 := by
  simpa only [compactPhaseCoordinateClass, Pi.single_eq_same,
    Pi.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1), mul_one, MulZeroClass.mul_zero,
    zero_add] using edgeCharacter_circleHomology n (Pi.single 1 1)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem CuspCentralHomology.edgeCharacter_coordinateHomology (n v : Fin 2 → ℤ) :
    unitCircleHomologyOneEquiv
        (SingularMayerVietoris.singularHomologyMap (edgeCharacterMap n) 1
          (compactPhaseCoordinateHomology v)) =
      -n 1 * v 0 + n 0 * v 1 := by
  rw [compactPhaseCoordinateHomology_apply]
  simp only [map_add, map_zsmul, edgeCharacter_coordinateClass_zero,
    edgeCharacter_coordinateClass_one, zsmul_eq_mul, Int.cast_id]
  ring

private def CuspCentralHomology.thetaPhaseTripleSum : (Fin 3 → Fin 2 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ)
    where
  toFun v := ∑ j, v j
  map_add' v w := by simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c v := by simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]

private theorem CuspCentralHomology.thetaPhaseTripleSum_apply (v : Fin 3 → Fin 2 → ℤ) (i : Fin 2) :
    thetaPhaseTripleSum v i = v 0 i + v 1 i + v 2 i := by
  simp [thetaPhaseTripleSum, Fin.sum_univ_succ, add_assoc]

private def CuspCentralHomology.thetaPhaseTripleCharacters : (Fin 3 → Fin 2 → ℤ) →ₗ[ℤ] (Fin 3 → ℤ)
    where
  toFun v := ![v 0 1, -(v 1 0), -(v 2 0) - v 2 1]
  map_add' v
    w := by
    funext j
    fin_cases j <;> simp <;> ring
  map_smul' c
    v := by
    funext j
    fin_cases j <;> simp
    ring

private theorem CuspCentralHomology.thetaPhaseTripleCharacters_eq_det (v : Fin 3 → Fin 2 → ℤ)
    (j : Fin 3) :
    thetaPhaseTripleCharacters v j =
      ToricComponent.hexagonRay (j.castLE (by decide)) 0 * v j 1 -
        ToricComponent.hexagonRay (j.castLE (by decide)) 1 * v j 0 := by
  fin_cases j <;> simp [thetaPhaseTripleCharacters, ToricComponent.hexagonRay]
  ring

private def CuspCentralHomology.thetaPhaseTripleSection : (Fin 3 → ℤ) →ₗ[ℤ] (Fin 3 → Fin 2 → ℤ)
    where
  toFun z := ![![z 2 + z 1 - z 0, z 0], ![-z 1, 0], ![z 0 - z 2, -z 0] ]
  map_add' z
    w := by
    funext j i
    fin_cases j <;> fin_cases i <;> simp <;> ring
  map_smul' c
    z := by
    funext j i
    fin_cases j <;> fin_cases i <;> simp <;> ring

private theorem CuspCentralHomology.thetaPhaseTripleSum_section (z : Fin 3 → ℤ) :
    thetaPhaseTripleSum (thetaPhaseTripleSection z) = 0 := by
  funext i
  rw [thetaPhaseTripleSum_apply]
  fin_cases i <;> simp [thetaPhaseTripleSection]
  ring

private theorem CuspCentralHomology.thetaPhaseTripleCharacters_section (z : Fin 3 → ℤ) :
    thetaPhaseTripleCharacters (thetaPhaseTripleSection z) = z := by
  funext j
  fin_cases j <;> simp [thetaPhaseTripleCharacters, thetaPhaseTripleSection]

private def CuspCentralHomology.thetaBeltPhaseClasses (z : Fin 3 → ℤ) (j : Fin 3) :
    SingularMayerVietoris.SingularHomology ToricSpace.CompactFibreTorus 1 :=
  compactPhaseCoordinateHomology (thetaPhaseTripleSection z j)

private theorem CuspCentralHomology.thetaBeltPhaseClasses_sum (z : Fin 3 → ℤ) :
    ∑ j, thetaBeltPhaseClasses z j = 0 := by
  change (∑ j, compactPhaseCoordinateHomology (thetaPhaseTripleSection z j)) = 0
  rw [← map_sum]
  change compactPhaseCoordinateHomology (thetaPhaseTripleSum (thetaPhaseTripleSection z)) = 0
  rw [thetaPhaseTripleSum_section, map_zero]

private def CuspCentralHomology.thetaBeltLift (z : Fin 3 → ℤ) :
    SingularMayerVietoris.SingularHomology ThetaBelt 1 :=
  thetaBeltSum (thetaBeltPhaseClasses z)

private theorem CuspCentralHomology.thetaBeltLift_mem_ker (z : Fin 3 → ℤ) :
    SingularMayerVietoris.leftHomologyMap thetaNorth thetaSouth 1 (thetaBeltLift z) = 0 :=
  thetaBeltSum_mem_ker (thetaBeltPhaseClasses z) (thetaBeltPhaseClasses_sum z)

private theorem CuspCentralHomology.thetaBeltPhaseClasses_character (z : Fin 3 → ℤ) (j : Fin 3) :
    unitCircleHomologyOneEquiv
        (SingularMayerVietoris.singularHomologyMap (thetaEdgeCharacterMap j) 1
          (thetaBeltPhaseClasses z j)) =
      thetaPhaseTripleCharacters (thetaPhaseTripleSection z) j := by
  rw [thetaPhaseTripleCharacters_eq_det]
  calc
    _ =
        -ToricComponent.hexagonRay (thetaEdgeIndex j) 1 * thetaPhaseTripleSection z j 0 +
          ToricComponent.hexagonRay (thetaEdgeIndex j) 0 * thetaPhaseTripleSection z j 1 :=
      edgeCharacter_coordinateHomology (ToricComponent.hexagonRay (thetaEdgeIndex j))
        (thetaPhaseTripleSection z j)
    _ = _ := by
      change
        -ToricComponent.hexagonRay (thetaEdgeIndex j) 1 * thetaPhaseTripleSection z j 0 +
            ToricComponent.hexagonRay (thetaEdgeIndex j) 0 * thetaPhaseTripleSection z j 1 =
          ToricComponent.hexagonRay (thetaEdgeIndex j) 0 * thetaPhaseTripleSection z j 1 -
            ToricComponent.hexagonRay (thetaEdgeIndex j) 1 * thetaPhaseTripleSection z j 0
      ring

private theorem CuspCentralHomology.thetaBeltLift_image (z : Fin 3 → ℤ) :
    thetaTargetBeltHomologyEquiv
        (SingularMayerVietoris.singularHomologyMap thetaBeltMap 1 (thetaBeltLift z)) =
      z := by
  rw [thetaBeltLift, thetaBeltMap_homologyOne_sum]
  funext j
  rw [thetaBeltPhaseClasses_character, thetaPhaseTripleCharacters_section]

private theorem CuspCentralHomology.thetaBelt_kernel_lifts
    (b : SingularMayerVietoris.SingularHomology (Suspension.middleBand ThreeCircles) 1) :
    ∃ c : SingularMayerVietoris.SingularHomology ThetaBelt 1,
      SingularMayerVietoris.leftHomologyMap thetaNorth thetaSouth 1 c = 0 ∧
        SingularMayerVietoris.singularHomologyMap thetaBeltMap 1 c = b := by
  refine ⟨thetaBeltLift (thetaTargetBeltHomologyEquiv b), thetaBeltLift_mem_ker _, ?_⟩
  apply thetaTargetBeltHomologyEquiv.injective
  exact thetaBeltLift_image (thetaTargetBeltHomologyEquiv b)

private theorem CuspCentralHomology.thetaCharacterCollapse_homologyTwo_surjective :
    Function.Surjective (SingularMayerVietoris.singularHomologyMap thetaCharacterCollapse 2) :=
  contractibleTargetCoverMap_homology_surjective (ToricSpace.CompactFibreTorus × Theta)
    ThreeCircleSuspension thetaCharacterCollapse thetaNorth thetaSouth Suspension.northOpen
    Suspension.southOpen thetaNorth_isOpen thetaSouth_isOpen theta_open_cover
    Suspension.northOpen_isOpen Suspension.southOpen_isOpen Suspension.open_cover
    thetaCharacterCollapse_mapsTo_north thetaCharacterCollapse_mapsTo_south 1
    thetaBelt_kernel_lifts

private def
    CuspCentralHomology.doubleSuspensionBoundaryContinuousMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) : C(ThreeCircleSuspension, centralBoundary C ε hε) :=
  ⟨doubleSuspensionBoundaryMap C ε hε, doubleSuspensionBoundaryMap_continuous C ε hε⟩

private theorem CuspCentralHomology.boundaryLift_coe_eq_doubleSuspensionMap
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (p : ToricSpace.CompactFibreTorus × Theta) :
    (boundaryLift C ε hε p : CuspRetraction.QuotientCentralFibre C ε) =
      doubleSuspensionMap C ε hε (shearedThetaCollapse (C 0) p) := by
  rcases p with ⟨u, q⟩
  obtain ⟨⟨t, j⟩, rfl⟩ := Suspension.mk_surjective q
  rw [boundaryLift_mk_coe, shearedThetaCollapse_mk, doubleSuspensionMap_character_orientedEdge]

private theorem CuspCentralHomology.boundaryLift_eq_doubleSuspensionBoundaryMap_comp
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    boundaryLift C ε hε =
      (doubleSuspensionBoundaryContinuousMap C ε hε).comp (shearedThetaCollapse (C 0)) := by
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  exact boundaryLift_coe_eq_doubleSuspensionMap C ε hε p

private def
    CuspCentralHomology.boundaryLiftCharacterHomotopy (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) :
    ((doubleSuspensionBoundaryContinuousMap C ε hε).comp thetaCharacterCollapse).Homotopy
      (boundaryLift C ε hε) :=
  ((ContinuousMap.Homotopy.refl (doubleSuspensionBoundaryContinuousMap C ε hε)).comp
        (thetaShearHomotopy (C 0))).cast
    rfl (boundaryLift_eq_doubleSuspensionBoundaryMap_comp C ε hε).symm

private theorem
    CuspCentralHomology.boundaryLift_homology_eq (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap (boundaryLift C ε hε) n =
      (SingularMayerVietoris.singularHomologyMap (doubleSuspensionBoundaryContinuousMap C ε hε)
            n).comp
        (SingularMayerVietoris.singularHomologyMap thetaCharacterCollapse n) := by
  rw [← PeriodTorusHigherHomology.homotopy_homologyMap (boundaryLiftCharacterHomotopy C ε hε) n]
  exact
    PeriodTorusHigherHomology.singularHomologyMap_comp thetaCharacterCollapse
      (doubleSuspensionBoundaryContinuousMap C ε hε) n

private theorem CuspCentralHomology.doubleSuspensionBoundaryContinuousMap_eq_homeomorph
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    doubleSuspensionBoundaryContinuousMap C ε hε =
      (doubleSuspensionBoundaryHomeomorph C ε hε hε1 hC hR :
        C(ThreeCircleSuspension, centralBoundary C ε hε)) :=
  rfl

private theorem
    CuspCentralHomology.boundaryLift_homologyTwo_surjective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    Function.Surjective (SingularMayerVietoris.singularHomologyMap (boundaryLift C ε hε) 2) := by
  rw [boundaryLift_homology_eq,
    doubleSuspensionBoundaryContinuousMap_eq_homeomorph C ε hε hε1 hC hR]
  exact
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv
          (doubleSuspensionBoundaryHomeomorph C ε hε hε1 hC hR) 2).surjective.comp
      thetaCharacterCollapse_homologyTwo_surjective

private theorem CuspCentralHomology.boundaryInclusion_homologyTwo_range_le_productCollapse
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    LinearMap.range
        (SingularMayerVietoris.singularHomologyMap (centralBoundaryInclusion C ε hε) 2) ≤
      LinearMap.range
        (SingularMayerVietoris.singularHomologyMap (CuspSpecialization.productCollapse C ε hε)
          2) := by
  rintro _ ⟨b, rfl⟩
  obtain ⟨c, hc⟩ := boundaryLift_homologyTwo_surjective C ε hε hε1 hC hR b
  refine ⟨SingularMayerVietoris.singularHomologyMap thetaProductMap 2 c, ?_⟩
  have h :=
    congrArg (fun f => SingularMayerVietoris.singularHomologyMap f 2)
      (centralBoundaryInclusion_comp_boundaryLift C ε hε)
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp,
    PeriodTorusHigherHomology.singularHomologyMap_comp] at h
  have he := LinearMap.congr_fun h c
  change
    SingularMayerVietoris.singularHomologyMap (centralBoundaryInclusion C ε hε) 2
        (SingularMayerVietoris.singularHomologyMap (boundaryLift C ε hε) 2 c) =
      SingularMayerVietoris.singularHomologyMap (CuspSpecialization.productCollapse C ε hε) 2
        (SingularMayerVietoris.singularHomologyMap thetaProductMap 2 c) at he
  rw [hc] at he
  exact he.symm

private def CuspCentralHomology.productBaseSection :
    C(PeriodTorusHigherHomology.ProductTorus 2,
      ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2) :=
  ⟨fun t => (1, t), continuous_const.prodMk continuous_id⟩

private theorem CuspCentralHomology.productCollapse_comp_productBaseSection
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    (CuspSpecialization.productCollapse C ε hε).comp productBaseSection =
      baseTorusSection C ε hε :=
  rfl

private theorem CuspCentralHomology.baseTorusSection_homology_factorization
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap (baseTorusSection C ε hε) n =
      (SingularMayerVietoris.singularHomologyMap (CuspSpecialization.productCollapse C ε hε)
            n).comp
        (SingularMayerVietoris.singularHomologyMap productBaseSection n) := by
  rw [← productCollapse_comp_productBaseSection,
    PeriodTorusHigherHomology.singularHomologyMap_comp]

private theorem CuspCentralHomology.baseTorusSection_homology_range_le_productCollapse
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (n : ℕ) :
    LinearMap.range (SingularMayerVietoris.singularHomologyMap (baseTorusSection C ε hε) n) ≤
      LinearMap.range
        (SingularMayerVietoris.singularHomologyMap (CuspSpecialization.productCollapse C ε hε)
          n) := by
  rintro _ ⟨x, rfl⟩
  refine ⟨SingularMayerVietoris.singularHomologyMap productBaseSection n x, ?_⟩
  exact (LinearMap.congr_fun (baseTorusSection_homology_factorization C ε hε n) x).symm

private theorem
    CuspCentralHomology.integerExtension_quotient_factorization {A B : Type*} [AddCommGroup A]
    [AddCommGroup B] [Module ℤ A] [Module ℤ B] (i : A →ₗ[ℤ] B) (d p : B →ₗ[ℤ] ℤ)
    (hi : Function.Injective i) (hd : Function.Surjective d)
    (hexact : LinearMap.range i = LinearMap.ker d) (hpi : ∀ a, p (i a) = 0) (x : B) :
    p x = d x * p (integerExtensionLift d hd) := by
  calc
    p x =
        p
          ((splitIntegerExtensionEquiv i d hi hd hexact).symm
            (splitIntegerExtensionEquiv i d hi hd hexact x)) := by rw [LinearEquiv.symm_apply_apply]
    _ = d x * p (integerExtensionLift d hd) := by
      rw [splitIntegerExtensionEquiv_symm_apply, map_add, hpi, map_zsmul,
        splitIntegerExtensionEquiv_snd]
      simp only [zero_add, zsmul_eq_mul, Int.cast_id]

private theorem CuspCentralHomology.integerExtension_quotient_coefficient_isUnit {A B : Type*}
    [AddCommGroup A] [AddCommGroup B] [Module ℤ A] [Module ℤ B] (i : A →ₗ[ℤ] B) (d p : B →ₗ[ℤ] ℤ)
    (hi : Function.Injective i) (hd : Function.Surjective d)
    (hexact : LinearMap.range i = LinearMap.ker d) (hpi : ∀ a, p (i a) = 0)
    (hp : Function.Surjective p) : IsUnit (p (integerExtensionLift d hd)) := by
  obtain ⟨x, hx⟩ := hp 1
  have he : d x * p (integerExtensionLift d hd) = 1 :=
    (integerExtension_quotient_factorization i d p hi hd hexact hpi x).symm.trans hx
  exact ⟨⟨p (integerExtensionLift d hd), d x, (mul_comm _ _).trans he, he⟩, rfl⟩

private theorem CuspCentralHomology.integerExtension_replaceQuotient {A B : Type*} [AddCommGroup A]
    [AddCommGroup B] [Module ℤ A] [Module ℤ B] (i : A →ₗ[ℤ] B) (d p : B →ₗ[ℤ] ℤ)
    (hi : Function.Injective i) (hd : Function.Surjective d)
    (hexact : LinearMap.range i = LinearMap.ker d) (hpi : ∀ a, p (i a) = 0)
    (hp : Function.Surjective p) : LinearMap.range i = LinearMap.ker p := by
  have hc : p (integerExtensionLift d hd) ≠ 0 :=
    (integerExtension_quotient_coefficient_isUnit i d p hi hd hexact hpi hp).ne_zero
  rw [hexact]
  ext x
  change d x = 0 ↔ p x = 0
  rw [integerExtension_quotient_factorization i d p hi hd hexact hpi x, mul_eq_zero]
  simp only [hc, or_false]

private def
    CuspCentralHomology.actualSectionAssembly {A B T : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup T] [Module ℤ A] [Module ℤ B] [Module ℤ T] (i : A →ₗ[ℤ] B) (s : T →ₗ[ℤ] B) :
    (A × T) →ₗ[ℤ] B :=
  PeriodTorusHigherHomology.intLinearMapOfAddHom (i.coprod s).toAddMonoidHom

private theorem
    CuspCentralHomology.coprod_projection_of_exact_section {A B T : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup T] [Module ℤ A] [Module ℤ B] [Module ℤ T] (i : A →ₗ[ℤ] B)
    (p : B →ₗ[ℤ] T) (s : T →ₗ[ℤ] B) (hexact : LinearMap.range i = LinearMap.ker p)
    (hps : ∀ t, p (s t) = t) (az : A × T) : p (i.coprod s az) = az.2 := by
  have hi : p (i az.1) = 0 := by
    have ha : i az.1 ∈ LinearMap.range i := ⟨az.1, rfl⟩
    rw [hexact] at ha
    exact ha
  rw [LinearMap.coprod_apply, map_add, hi, hps, zero_add]

private theorem
    CuspCentralHomology.coprod_injective_of_exact_section {A B T : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup T] [Module ℤ A] [Module ℤ B] [Module ℤ T] (i : A →ₗ[ℤ] B)
    (p : B →ₗ[ℤ] T) (s : T →ₗ[ℤ] B) (hi : Function.Injective i)
    (hexact : LinearMap.range i = LinearMap.ker p) (hps : ∀ t, p (s t) = t) :
    Function.Injective (i.coprod s) := by
  intro az au h
  have hsnd : az.2 = au.2 := by
    have hp := congrArg p h
    simpa only [coprod_projection_of_exact_section i p s hexact hps] using hp
  apply Prod.ext _ hsnd
  apply hi
  apply add_right_cancel (b := s au.2)
  simpa only [LinearMap.coprod_apply, hsnd] using h

public
theorem
    CuspCentralHomology.coprod_surjective_of_exact_section {A B T : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup T] [Module ℤ A] [Module ℤ B] [Module ℤ T] (i : A →ₗ[ℤ] B)
    (p : B →ₗ[ℤ] T) (s : T →ₗ[ℤ] B) (hexact : LinearMap.range i = LinearMap.ker p)
    (hps : ∀ t, p (s t) = t) : Function.Surjective (i.coprod s) := by
  intro b
  have hk : b - s (p b) ∈ LinearMap.ker p := by
    change p (b - s (p b)) = 0
    rw [map_sub, hps, sub_self]
  rw [← hexact] at hk
  obtain ⟨a, ha⟩ := hk
  refine ⟨(a, p b), ?_⟩
  change i a + s (p b) = b
  rw [ha, sub_add_cancel]

private def
    CuspCentralHomology.splitFromActualSection {A B T : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup T] [Module ℤ A] [Module ℤ B] [Module ℤ T] (i : A →ₗ[ℤ] B) (p : B →ₗ[ℤ] T)
    (s : T →ₗ[ℤ] B) (hi : Function.Injective i) (hexact : LinearMap.range i = LinearMap.ker p)
    (hps : ∀ t, p (s t) = t) : (A × T) ≃ₗ[ℤ] B :=
  LinearEquiv.ofBijective (actualSectionAssembly i s)
    ⟨coprod_injective_of_exact_section i p s hi hexact hps,
      coprod_surjective_of_exact_section i p s hexact hps⟩

private abbrev CuspCentralHomology.boundaryH2Inclusion (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) :
    SingularMayerVietoris.SingularHomology (centralBoundary C r hr) 2 →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) 2 :=
  SingularMayerVietoris.singularHomologyMap (centralBoundaryInclusion C r hr) 2

private def
    CuspCentralHomology.boundaryH2Quotient (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hr1 : r < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (hR : ToricSpace.SmallDrift C r) :
    SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) 2 →ₗ[ℤ] ℤ :=
  middleQuotientMap C r hr hr1 hC hR (1 / 2) (by norm_num) (by norm_num)

private theorem CuspCentralHomology.boundaryH2Inclusion_injective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (hR : ToricSpace.SmallDrift C r) : Function.Injective (boundaryH2Inclusion C r hr) := by
  let e := outerRegionBoundaryHomotopyEquiv C r hr (1 / 2) (by norm_num) (by norm_num) hr1 hC hR
  have he :
    (SingularMayerVietoris.subtypeInclusion (outerRegion C r hr (1 / 2))).comp e.symm.toFun =
      centralBoundaryInclusion C r hr := by
    apply ContinuousMap.ext
    intro q
    rfl
  change
    Function.Injective
      (SingularMayerVietoris.singularHomologyMap (centralBoundaryInclusion C r hr) 2)
  rw [← he, PeriodTorusHigherHomology.singularHomologyMap_comp]
  intro x y hxy
  have hE :
    SingularMayerVietoris.singularHomologyMap e.symm.toFun 2 x =
      SingularMayerVietoris.singularHomologyMap e.symm.toFun 2 y :=
    (middleOuterInclusion_injective C r hr hr1 hC hR (1 / 2) (by norm_num) (by norm_num)) hxy
  apply (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv e 2).symm.injective
  simpa only [PeriodTorusHigherHomology.homotopyEquivHomologyEquiv_symm_apply] using hE

private theorem
    CuspCentralHomology.boundaryH2Inclusion_range_eq_outer (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (hR : ToricSpace.SmallDrift C r) :
    LinearMap.range (boundaryH2Inclusion C r hr) =
      LinearMap.range
        (SingularMayerVietoris.singularHomologyMap
          (SingularMayerVietoris.subtypeInclusion (outerRegion C r hr (1 / 2))) 2) := by
  let e := outerRegionBoundaryHomotopyEquiv C r hr (1 / 2) (by norm_num) (by norm_num) hr1 hC hR
  have he :
    (SingularMayerVietoris.subtypeInclusion (outerRegion C r hr (1 / 2))).comp e.symm.toFun =
      centralBoundaryInclusion C r hr := by
    apply ContinuousMap.ext
    intro q
    rfl
  change
    LinearMap.range
        (SingularMayerVietoris.singularHomologyMap (centralBoundaryInclusion C r hr) 2) =
      _
  rw [← he, PeriodTorusHigherHomology.singularHomologyMap_comp]
  exact
    LinearMap.range_comp_of_range_eq_top _
      (LinearEquiv.range (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv e 2).symm)

private theorem CuspCentralHomology.boundaryH2Quotient_surjective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (hR : ToricSpace.SmallDrift C r) :
    Function.Surjective (boundaryH2Quotient C r hr hr1 hC hR) :=
  middleQuotientMap_surjective C r hr hr1 hC hR (1 / 2) (by norm_num) (by norm_num)

private theorem
    CuspCentralHomology.boundaryH2Inclusion_range_eq_ker (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (hR : ToricSpace.SmallDrift C r) :
    LinearMap.range (boundaryH2Inclusion C r hr) =
      LinearMap.ker (boundaryH2Quotient C r hr hr1 hC hR) := by
  rw [boundaryH2Inclusion_range_eq_outer C r hr hr1 hC hR]
  exact middleSecondHomology_exact C r hr hr1 hC hR (1 / 2) (by norm_num) (by norm_num)

private theorem
    CuspCentralHomology.baseTorusH2Functional_surjective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Function.Surjective (baseTorusH2Functional C r hr hC) :=
  baseTorusH2Marking.surjective.comp (baseTorusProjectionHomologyMap_surjective C r hr hC 2)

private theorem
    CuspCentralHomology.baseTorusH2Functional_ker (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    LinearMap.ker (baseTorusH2Functional C r hr hC) =
      LinearMap.ker (baseTorusProjectionHomologyMap C r hr hC 2) := by
  ext x
  change
    baseTorusH2Marking (baseTorusProjectionHomologyMap C r hr hC 2 x) = 0 ↔
      baseTorusProjectionHomologyMap C r hr hC 2 x = 0
  constructor
  · intro h
    apply baseTorusH2Marking.injective
    simpa only [map_zero] using h
  · intro h
    rw [h, map_zero]

private theorem CuspCentralHomology.boundaryH2Inclusion_range_eq_ker_baseFunctional
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (hR : ToricSpace.SmallDrift C r) :
    LinearMap.range (boundaryH2Inclusion C r hr) =
      LinearMap.ker (baseTorusH2Functional C r hr hC) :=
  integerExtension_replaceQuotient (boundaryH2Inclusion C r hr)
    (boundaryH2Quotient C r hr hr1 hC hR) (baseTorusH2Functional C r hr hC)
    (boundaryH2Inclusion_injective C r hr hr1 hC hR)
    (boundaryH2Quotient_surjective C r hr hr1 hC hR)
    (boundaryH2Inclusion_range_eq_ker C r hr hr1 hC hR)
    (baseTorusH2Functional_boundary C r hr hC hr1 hR) (baseTorusH2Functional_surjective C r hr hC)

private theorem
    CuspCentralHomology.baseTorusProjectionHomologyMap_ker (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (hR : ToricSpace.SmallDrift C r) :
    LinearMap.ker (baseTorusProjectionHomologyMap C r hr hC 2) =
      LinearMap.range (boundaryH2Inclusion C r hr) := by
  rw [← baseTorusH2Functional_ker, ←
    boundaryH2Inclusion_range_eq_ker_baseFunctional C r hr hr1 hC hR]

private def
    CuspCentralHomology.baseTorusH2Split (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hr1 : r < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (hR : ToricSpace.SmallDrift C r) :
    (SingularMayerVietoris.SingularHomology (centralBoundary C r hr) 2 ×
        SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 2) 2) ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) 2 :=
  splitFromActualSection (boundaryH2Inclusion C r hr) (baseTorusProjectionHomologyMap C r hr hC 2)
    (baseTorusSectionHomologyMap C r hr 2) (boundaryH2Inclusion_injective C r hr hr1 hC hR)
    (baseTorusProjectionHomologyMap_ker C r hr hr1 hC hR).symm
    (baseTorusProjectionHomologyMap_section C r hr hC 2)

private theorem CuspCentralHomology.baseTorusH2_generated (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (hR : ToricSpace.SmallDrift C r)
    (x : SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) 2) :
    ∃ a : SingularMayerVietoris.SingularHomology (centralBoundary C r hr) 2,
      ∃ b : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 2) 2,
        SingularMayerVietoris.singularHomologyMap (centralBoundaryInclusion C r hr) 2 a +
            baseTorusSectionHomologyMap C r hr 2 b =
          x := by
  obtain ⟨⟨a, b⟩, h⟩ := (baseTorusH2Split C r hr hr1 hC hR).surjective x
  exact ⟨a, b, h⟩

private theorem CuspCentralHomology.productCollapse_homologyTwo_surjective
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    Function.Surjective
      (SingularMayerVietoris.singularHomologyMap (CuspSpecialization.productCollapse C ε hε) 2) :=
  by
  intro x
  obtain ⟨a, b, hab⟩ := baseTorusH2_generated C ε hε hε1 hC hR x
  change
    SingularMayerVietoris.singularHomologyMap (centralBoundaryInclusion C ε hε) 2 a +
        SingularMayerVietoris.singularHomologyMap (baseTorusSection C ε hε) 2 b =
      x at hab
  have ha :
    SingularMayerVietoris.singularHomologyMap (centralBoundaryInclusion C ε hε) 2 a ∈
      LinearMap.range
        (SingularMayerVietoris.singularHomologyMap (CuspSpecialization.productCollapse C ε hε)
          2) :=
    boundaryInclusion_homologyTwo_range_le_productCollapse C ε hε hε1 hC hR ⟨a, rfl⟩
  have hb :
    SingularMayerVietoris.singularHomologyMap (baseTorusSection C ε hε) 2 b ∈
      LinearMap.range
        (SingularMayerVietoris.singularHomologyMap (CuspSpecialization.productCollapse C ε hε)
          2) :=
    baseTorusSection_homology_range_le_productCollapse C ε hε 2 ⟨b, rfl⟩
  obtain ⟨c, hc⟩ := ha
  obtain ⟨d, hd⟩ := hb
  refine ⟨c + d, ?_⟩
  rw [map_add, hc, hd]
  exact hab

private theorem CuspCentralHomology.productCollapse_homologyTwo_surjective_of_holomorphic
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Function.Surjective
      (SingularMayerVietoris.singularHomologyMap (CuspSpecialization.productCollapse C r hr) 2) :=
  by
  obtain ⟨δ, hδ, hδr, hδ1, hRCδ, _hRDδ⟩ :=
    CuspRetraction.exists_common_frozen_radius C hr (fun i j => (hC i j).continuousOn)
  have hCδ (i j) : ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 δ) :=
    (hC i j).mono (Metric.ball_subset_ball hδr.le)
  have he :=
    congrArg (fun f => SingularMayerVietoris.singularHomologyMap f 2)
      (centralRadiusHomeomorph_comp_productCollapse C r δ hδr.le hC hδ)
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp] at he
  rw [← he]
  exact
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv
          (centralRadiusHomeomorph C r δ hδr.le hC hδ) 2).surjective.comp
      (productCollapse_homologyTwo_surjective C δ hδ hδ1 hCδ hRCδ)

private theorem CuspSpecialization.torusDifference_two_exterior
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) 2) :
    PeriodTorusHigherHomology.coordinateTorusH2ExteriorEquiv
        (CuspCoinvariants.torusDifference 2 a) =
      CuspCoinvariants.exteriorSquareDifference
        (PeriodTorusHigherHomology.coordinateTorusH2ExteriorEquiv a) := by
  change
    PeriodTorusHigherHomology.coordinateTorusH2ExteriorEquiv
        (SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap M₀) 2
            a -
          a) =
      exteriorPower.map 2 M₀.mulVecLin
          (PeriodTorusHigherHomology.coordinateTorusH2ExteriorEquiv a) -
        PeriodTorusHigherHomology.coordinateTorusH2ExteriorEquiv a
  rw [map_sub, PeriodTorusHigherHomology.coordinateTorusH2ExteriorEquiv_matrix]

private theorem CuspSpecialization.markedCollapse_homologyTwo_surjective
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε)) :
    Function.Surjective (SingularMayerVietoris.singularHomologyMap (markedCollapse C ε hε) 2) :=
  markedCollapse_homology_surjective_of_product C ε hε 2
    (CuspCentralHomology.productCollapse_homologyTwo_surjective_of_holomorphic C ε hε hC)

private theorem
    CuspSpecialization.markedCollapse_homologyTwo_kernel (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε)) :
    LinearMap.ker (SingularMayerVietoris.singularHomologyMap (markedCollapse C ε hε) 2) =
      LinearMap.range (CuspCoinvariants.torusDifference 2) := by
  let := CuspCentralHomology.centralSingularH2_free C ε hε hC
  let := CuspCentralHomology.centralSingularH2_finite C ε hε hC
  exact
    CuspCoinvariants.torusTwo_kernel_eq_of_invariant _
      (markedCollapse_homologyTwo_surjective C ε hε hC)
      (markedCollapse_homology_invariant C ε hε 2)
      (CuspCentralHomology.centralSingularH2_finrank C ε hε hC)

private theorem CuspSpecialization.markedCollapse_homologyTwo_eq_zero_iff
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) 2) :
    SingularMayerVietoris.singularHomologyMap (markedCollapse C ε hε) 2 a = 0 ↔
      ∃ v : PeriodTorusHigherHomologyExterior.latticeExterior 2,
        exteriorPower.map 2 M₀.mulVecLin v - v =
          PeriodTorusHigherHomology.coordinateTorusH2ExteriorEquiv a := by
  change
    a ∈ LinearMap.ker (SingularMayerVietoris.singularHomologyMap (markedCollapse C ε hε) 2) ↔
      PeriodTorusHigherHomology.coordinateTorusH2ExteriorEquiv a ∈
        LinearMap.range CuspCoinvariants.exteriorSquareDifference
  rw [markedCollapse_homologyTwo_kernel C ε hε hC]
  exact
    CuspCoinvariants.mem_range_iff_of_intertwines
      PeriodTorusHigherHomology.coordinateTorusH2ExteriorEquiv
      (CuspCoinvariants.torusDifference 2) CuspCoinvariants.exteriorSquareDifference
      torusDifference_two_exterior a

private abbrev CuspCentralHomology.BaseCover.BaseTorus :=
  PeriodTorusHigherHomology.ProductTorus 2

private abbrev CuspCentralHomology.BaseCover.basePoint :=
  CuspCentralHomology.baseTorusPoint

private theorem CuspCentralHomology.BaseCover.basePoint_eq_iff (y z : (CuspHoneycombTiling.Plane)) :
    basePoint y = basePoint z ↔
      ∃ v : (CuspHoneycombTiling.Lattice), y = z + CuspHoneycombTiling.latticePoint v := by
  rw [CuspCentralHomology.baseTorusPoint_eq_iff]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨ToricSpace.cuspVector v, hv⟩
  · rintro ⟨v, hv⟩
    refine ⟨-ToricSpace.cuspVector v, ?_⟩
    simpa only [ToricSpace.cuspVector_neg, ToricSpace.cuspVector_cuspVector, neg_neg] using hv

private theorem CuspCentralHomology.BaseCover.basePoint_add_latticePoint
    (v : (CuspHoneycombTiling.Lattice)) (y : (CuspHoneycombTiling.Plane)) :
    basePoint (y + CuspHoneycombTiling.latticePoint v) = basePoint y :=
  (basePoint_eq_iff _ _).mpr ⟨v, rfl⟩

private theorem CuspCentralHomology.BaseCover.basePoint_sub_latticePoint
    (v : (CuspHoneycombTiling.Lattice)) (y : (CuspHoneycombTiling.Plane)) :
    basePoint (y - CuspHoneycombTiling.latticePoint v) = basePoint y := by
  simpa only [CuspHoneycombTiling.latticePoint_neg, sub_eq_add_neg] using
    basePoint_add_latticePoint (-v) y

private def CuspCentralHomology.BaseCover.cellMap : C(CuspHoneycombTiling.baseCell, BaseTorus) :=
  ⟨fun y => basePoint (y : (CuspHoneycombTiling.Plane)),
    CuspCentralHomology.baseTorusPoint_continuous.comp continuous_subtype_val⟩

private theorem CuspCentralHomology.BaseCover.cellMap_surjective : Function.Surjective cellMap := by
  intro q
  obtain ⟨y, hy⟩ := CuspCentralHomology.baseTorusPoint_surjective q
  exact
    ⟨⟨y - CuspHoneycombTiling.latticePoint (CuspHoneycombTiling.floorCenter y),
        CuspHoneycombTiling.mem_cell_floorCenter y⟩,
      (basePoint_sub_latticePoint (CuspHoneycombTiling.floorCenter y) y).trans hy⟩

private theorem CuspCentralHomology.BaseCover.cellMap_eq_iff (y z : CuspHoneycombTiling.baseCell) :
    cellMap y = cellMap z ↔
      ∃ v : (CuspHoneycombTiling.Lattice),
        (y : (CuspHoneycombTiling.Plane)) =
          (z : (CuspHoneycombTiling.Plane)) + CuspHoneycombTiling.latticePoint v :=
  basePoint_eq_iff y z

private theorem CuspCentralHomology.BaseCover.cellMap_isProperMap : IsProperMap cellMap := by
  let : CompactSpace CuspHoneycombTiling.baseCell :=
    isCompact_iff_compactSpace.mp CuspHoneycombTiling.baseCell_isCompact
  exact cellMap.continuous.isProperMap

private theorem CuspCentralHomology.BaseCover.cellMap_isClosedMap : IsClosedMap cellMap :=
  cellMap_isProperMap.isClosedMap

private theorem
    CuspCentralHomology.BaseCover.cellMap_isQuotientMap : Topology.IsQuotientMap cellMap :=
  cellMap_isClosedMap.isQuotientMap cellMap.continuous cellMap_surjective

private theorem
    CuspCentralHomology.BaseCover.cellMap_eq_of_interior (y z : CuspHoneycombTiling.baseCell)
    (hy : (y : (CuspHoneycombTiling.Plane)) ∈ interior CuspHoneycombTiling.baseCell)
    (h : cellMap y = cellMap z) : y = z := by
  obtain ⟨v, hv⟩ := (cellMap_eq_iff y z).mp h
  have hyv : (y : (CuspHoneycombTiling.Plane)) ∈ CuspHoneycombTiling.cell v := by
    rw [hv, CuspHoneycombTiling.mem_cell, add_sub_cancel_right]
    exact z.property
  have hv0 : v = 0 := ((CuspHoneycombTiling.mem_interior_baseCell_iff _).mp hy v).mp hyv
  apply Subtype.ext
  simpa only [hv0, CuspHoneycombTiling.latticePoint_zero, add_zero] using hv

private theorem CuspCentralHomology.BaseCover.cellMap_interior_iff_of_eq
    (y z : CuspHoneycombTiling.baseCell) (h : cellMap y = cellMap z) :
    (y : (CuspHoneycombTiling.Plane)) ∈ interior CuspHoneycombTiling.baseCell ↔
      (z : (CuspHoneycombTiling.Plane)) ∈ interior CuspHoneycombTiling.baseCell := by
  constructor
  · intro hy
    simpa only [← cellMap_eq_of_interior y z hy h] using hy
  · intro hz
    simpa only [← cellMap_eq_of_interior z y hz h.symm] using hz

private theorem
    CuspCentralHomology.BaseCover.cellMap_eq_or_frontier (y z : CuspHoneycombTiling.baseCell)
    (h : cellMap y = cellMap z) :
    y = z ∨
      ((y : (CuspHoneycombTiling.Plane)) ∈ frontier CuspHoneycombTiling.baseCell ∧
        (z : (CuspHoneycombTiling.Plane)) ∈ frontier CuspHoneycombTiling.baseCell) := by
  by_cases hy : (y : (CuspHoneycombTiling.Plane)) ∈ interior CuspHoneycombTiling.baseCell
  · exact Or.inl (cellMap_eq_of_interior y z hy h)
  · right
    rw [CuspHoneycombTiling.baseCell_isClosed.frontier_eq]
    refine ⟨⟨y.property, hy⟩, z.property, ?_⟩
    intro hz
    exact hy ((cellMap_interior_iff_of_eq y z h).mpr hz)

private theorem CuspCentralHomology.BaseCover.cellGauge_eq_of_cellMap_eq
    (y z : CuspHoneycombTiling.baseCell) (h : cellMap y = cellMap z) :
    CuspCentralHomology.Radial.cellGauge (y : (CuspHoneycombTiling.Plane)) =
      CuspCentralHomology.Radial.cellGauge (z : (CuspHoneycombTiling.Plane)) := by
  rcases cellMap_eq_or_frontier y z h with rfl | ⟨hy, hz⟩
  · rfl
  · rw [(CuspCentralHomology.Radial.mem_frontier_baseCell_iff _).mp hy,
      (CuspCentralHomology.Radial.mem_frontier_baseCell_iff _).mp hz]

private def CuspCentralHomology.BaseCover.cellRadius : C(CuspHoneycombTiling.baseCell, ℝ) :=
  ⟨fun y => CuspCentralHomology.Radial.cellGauge (y : (CuspHoneycombTiling.Plane)),
    CuspCentralHomology.Radial.cellGauge_continuous.comp continuous_subtype_val⟩

private def CuspCentralHomology.BaseCover.radius : C(BaseTorus, ℝ)
    where
  toFun := CuspHoneycombHexagon.CommonFibres.descend cellMap cellRadius cellMap_surjective
  continuous_toFun :=
    CuspHoneycombHexagon.CommonFibres.descend_continuous cellMap cellRadius cellMap_surjective
      cellMap_isQuotientMap cellRadius.continuous cellGauge_eq_of_cellMap_eq

@[simp]
private theorem CuspCentralHomology.BaseCover.radius_cellMap (y : CuspHoneycombTiling.baseCell) :
    radius (cellMap y) = CuspCentralHomology.Radial.cellGauge (y : (CuspHoneycombTiling.Plane)) :=
  CuspHoneycombHexagon.CommonFibres.descend_apply cellMap cellRadius cellMap_surjective
    cellGauge_eq_of_cellMap_eq y

private def CuspCentralHomology.BaseCover.boundary : Set BaseTorus :=
  {q | radius q = 1}

private def CuspCentralHomology.BaseCover.innerRegion : Set BaseTorus :=
  {q | radius q < 1}

private def CuspCentralHomology.BaseCover.outerRegion (a : ℝ) : Set BaseTorus :=
  {q | a < radius q}

private theorem CuspCentralHomology.BaseCover.cellMap_mem_boundary_iff
    (y : CuspHoneycombTiling.baseCell) :
    cellMap y ∈ boundary ↔
      (y : (CuspHoneycombTiling.Plane)) ∈ frontier CuspHoneycombTiling.baseCell := by
  change radius (cellMap y) = 1 ↔ _
  rw [radius_cellMap]
  exact (CuspCentralHomology.Radial.mem_frontier_baseCell_iff _).symm

private theorem CuspCentralHomology.BaseCover.cellMap_mem_innerRegion_iff
    (y : CuspHoneycombTiling.baseCell) :
    cellMap y ∈ innerRegion ↔
      (y : (CuspHoneycombTiling.Plane)) ∈ interior CuspHoneycombTiling.baseCell := by
  change radius (cellMap y) < 1 ↔ _
  rw [radius_cellMap]
  exact (CuspCentralHomology.Radial.mem_interior_baseCell_iff _).symm

private theorem CuspCentralHomology.BaseCover.cellMap_mem_outerRegion_iff (a : ℝ)
    (y : CuspHoneycombTiling.baseCell) :
    cellMap y ∈ outerRegion a ↔
      a < CuspCentralHomology.Radial.cellGauge (y : (CuspHoneycombTiling.Plane)) := by
  change a < radius (cellMap y) ↔ _
  rw [radius_cellMap]

private theorem CuspCentralHomology.BaseCover.innerRegion_isOpen : IsOpen innerRegion :=
  isOpen_lt radius.continuous continuous_const

private theorem CuspCentralHomology.BaseCover.outerRegion_isOpen (a : ℝ) : IsOpen (outerRegion a) :=
  isOpen_lt continuous_const radius.continuous

private theorem CuspCentralHomology.BaseCover.boundary_subset_outerRegion (a : ℝ) (ha : a < 1) :
    boundary ⊆ outerRegion a := by
  intro q hq
  change a < radius q
  change radius q = 1 at hq
  rwa [hq]

private theorem CuspCentralHomology.BaseCover.outerRegion_union_innerRegion (a : ℝ) (ha : a < 1) :
    outerRegion a ∪ innerRegion = Set.univ := by
  apply Set.eq_univ_of_forall
  intro q
  by_cases hq : radius q < 1
  · exact Or.inr hq
  · exact Or.inl (ha.trans_le (le_of_not_gt hq))

private theorem
    CuspCentralHomology.BaseCover.dualSidePoint_mem_frontier (k : Fin 6) (t : unitInterval) :
    CuspCentralHomology.dualSidePoint k t ∈ frontier CuspHoneycombTiling.baseCell := by
  rw [← CuspCentralHomology.edgeArcBase_eq_dualSidePoint (0 : Matrix (Fin 2) (Fin 2) ℂ)]
  exact CuspCentralHomology.edgeArcBase_mem_frontier 0 k t

private theorem CuspCentralHomology.BaseCover.exists_dualSidePoint_of_mem_frontier
    (y : (CuspHoneycombTiling.Plane)) (hy : y ∈ frontier CuspHoneycombTiling.baseCell) :
    ∃ k : Fin 6, ∃ t : unitInterval, CuspCentralHomology.dualSidePoint k t = y := by
  obtain ⟨k, t, ht⟩ :=
    CuspCentralHomology.exists_edgeArcBase_of_mem_frontier (0 : Matrix (Fin 2) (Fin 2) ℂ) y hy
  exact ⟨k, t, (CuspCentralHomology.edgeArcBase_eq_dualSidePoint 0 k t).symm.trans ht⟩

private theorem
    CuspCentralHomology.BaseCover.dualSidePoint_opposite (k : Fin 6) (t : unitInterval) :
    CuspCentralHomology.dualSidePoint (k + 3) (unitInterval.symm t) =
      CuspCentralHomology.dualSidePoint k t -
        CuspHoneycombTiling.latticePoint (ToricComponent.hexagonRay k) :=
  CuspHoneycombTiling.dual_sideInterval_opposite k t

private theorem CuspCentralHomology.BaseCover.basePoint_dualSidePoint_opposite (k : Fin 6)
    (t : unitInterval) :
    CuspCentralHomology.baseTorusPoint
        (CuspCentralHomology.dualSidePoint (k + 3) (unitInterval.symm t)) =
      CuspCentralHomology.baseTorusPoint (CuspCentralHomology.dualSidePoint k t) := by
  rw [dualSidePoint_opposite]
  exact
    basePoint_sub_latticePoint (ToricComponent.hexagonRay k)
      (CuspCentralHomology.dualSidePoint k t)

private theorem
    CuspCentralHomology.BaseCover.thetaBaseMap_mem_boundary (q : CuspCentralHomology.Theta) :
    CuspCentralHomology.thetaBaseMap q ∈ boundary := by
  obtain ⟨⟨t, j⟩, rfl⟩ := CuspCentralHomology.Suspension.mk_surjective q
  rw [CuspCentralHomology.thetaBaseMap_mk_point]
  let y :=
    CuspCentralHomology.dualSidePoint (CuspCentralHomology.thetaEdgeIndex j)
      (if j = 1 then unitInterval.symm t else t)
  have hy : y ∈ frontier CuspHoneycombTiling.baseCell := dualSidePoint_mem_frontier _ _
  exact
    (cellMap_mem_boundary_iff ⟨y, CuspHoneycombTiling.baseCell_isClosed.frontier_subset hy⟩).mpr
      hy

private theorem CuspCentralHomology.BaseCover.dualSidePoint_basePoint_mem_range (k : Fin 6)
    (t : unitInterval) :
    CuspCentralHomology.baseTorusPoint (CuspCentralHomology.dualSidePoint k t) ∈
      Set.range CuspCentralHomology.thetaBaseMap := by
  fin_cases k
  · exact
      ⟨CuspCentralHomology.Suspension.mk t (0 : Fin 3),
        CuspCentralHomology.thetaBaseMap_mk_zero t⟩
  · refine ⟨CuspCentralHomology.Suspension.mk (unitInterval.symm t) (1 : Fin 3), ?_⟩
    rw [CuspCentralHomology.thetaBaseMap_mk_one, unitInterval.symm_symm]
    rfl
  · exact
      ⟨CuspCentralHomology.Suspension.mk t (2 : Fin 3), CuspCentralHomology.thetaBaseMap_mk_two t⟩
  · refine ⟨CuspCentralHomology.Suspension.mk (unitInterval.symm t) (0 : Fin 3), ?_⟩
    rw [CuspCentralHomology.thetaBaseMap_mk_zero]
    have hi : (0 : Fin 6) + 3 = ⟨3, by decide⟩ := by decide
    simpa only [unitInterval.symm_symm, hi] using
      (basePoint_dualSidePoint_opposite 0 (unitInterval.symm t)).symm
  · refine ⟨CuspCentralHomology.Suspension.mk t (1 : Fin 3), ?_⟩
    rw [CuspCentralHomology.thetaBaseMap_mk_one]
    have hi : (1 : Fin 6) + 3 = ⟨4, by decide⟩ := by decide
    simpa only [unitInterval.symm_symm, hi] using
      (basePoint_dualSidePoint_opposite 1 (unitInterval.symm t)).symm
  · refine ⟨CuspCentralHomology.Suspension.mk (unitInterval.symm t) (2 : Fin 3), ?_⟩
    rw [CuspCentralHomology.thetaBaseMap_mk_two]
    have hi : (2 : Fin 6) + 3 = ⟨5, by decide⟩ := by decide
    simpa only [unitInterval.symm_symm, hi] using
      (basePoint_dualSidePoint_opposite 2 (unitInterval.symm t)).symm

private theorem CuspCentralHomology.BaseCover.range_thetaBaseMap :
    Set.range CuspCentralHomology.thetaBaseMap = boundary := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    exact thetaBaseMap_mem_boundary x
  · intro hq
    obtain ⟨y, rfl⟩ := cellMap_surjective q
    obtain ⟨k, t, ht⟩ :=
      exists_dualSidePoint_of_mem_frontier (y : (CuspHoneycombTiling.Plane))
        ((cellMap_mem_boundary_iff y).mp hq)
    change
      CuspCentralHomology.baseTorusPoint (y : (CuspHoneycombTiling.Plane)) ∈
        Set.range CuspCentralHomology.thetaBaseMap
    rw [← ht]
    exact dualSidePoint_basePoint_mem_range k t

private def
    CuspCentralHomology.BaseCover.thetaBoundaryMap : C(CuspCentralHomology.Theta, boundary) :=
  ⟨fun q => ⟨CuspCentralHomology.thetaBaseMap q, thetaBaseMap_mem_boundary q⟩,
    CuspCentralHomology.thetaBaseMap.continuous.subtype_mk _⟩

private theorem CuspCentralHomology.BaseCover.thetaBoundaryMap_surjective :
    Function.Surjective thetaBoundaryMap := by
  intro q
  have hq : (q : BaseTorus) ∈ Set.range CuspCentralHomology.thetaBaseMap :=
    range_thetaBaseMap.symm.le q.2
  obtain ⟨x, hx⟩ := hq
  exact ⟨x, Subtype.ext hx⟩

private theorem CuspCentralHomology.BaseCover.zeroCorrection_deckFibrePhase_mo1973_14847
    (v : Fin 2 → ℤ) : CuspCollapse.deckFibrePhase (0 : Matrix (Fin 2) (Fin 2) ℂ) v = 1 := by
  funext i
  simp [CuspCollapse.deckFibrePhase, CuspPositive.frozenPhaseCoordinate_eq_exp]

private theorem CuspCentralHomology.BaseCover.phaseOneCollapse_eq_of_base_eq_mo1973_14848
    {y z : (CuspHoneycombTiling.Plane)}
    (h : CuspCentralHomology.baseTorusPoint y = CuspCentralHomology.baseTorusPoint z) :
    CuspHoneycomb.honeycombCollapseMap (fun _ => 0) 1 zero_lt_one (1, y) =
      CuspHoneycomb.honeycombCollapseMap (fun _ => 0) 1 zero_lt_one (1, z) := by
  obtain ⟨v, hv⟩ := (CuspCentralHomology.baseTorusPoint_eq_iff y z).mp h
  apply (CuspHoneycomb.honeycombCollapseMap_eq_iff (fun _ => 0) 1 zero_lt_one _ _).mpr
  refine ⟨v, hv, ?_⟩
  simp only [zeroCorrection_deckFibrePhase_mo1973_14847, inv_one, mul_one]
  exact
    (MulAction.stabilizer ToricSpace.CompactFibreTorus
        ((CuspHoneycomb.honeycombHomeomorph 0 y).1 : ToricSpace.Space)).one_mem

private theorem CuspCentralHomology.BaseCover.phaseOne_edgeCylinder_mo1973_14849 (k : Fin 6)
    (t : unitInterval) :
    CuspCollapse.centralProject (fun _ => 0) 1 zero_lt_one
        (CuspCentralHomology.edgeCylinder 0 k (t, 1)) =
      CuspHoneycomb.honeycombCollapseMap (fun _ => 0) 1 zero_lt_one
        (1, CuspCentralHomology.dualSidePoint k t) := by
  have h :
    CuspCollapse.centralProject (fun _ => 0) 1 zero_lt_one
        (CuspCentralHomology.edgeCylinder 0 k (t, 1)) =
      CuspHoneycomb.honeycombCollapseMap (fun _ => 0) 1 zero_lt_one
        (CuspCentralHomology.hexagonCharacterSection k 1,
          (CuspCentralHomology.edgeArcBase 0 k t : (CuspHoneycombTiling.Plane))) := by
    change
      CuspCollapse.centralCollapseMap (fun _ => 0) 1 zero_lt_one
          (CuspCentralHomology.hexagonCharacterSection k 1,
            CuspCentralHomology.edgeArcPositive 0 k t) =
        CuspCollapse.centralCollapseMap (fun _ => 0) 1 zero_lt_one
          (CuspCentralHomology.hexagonCharacterSection k 1,
            CuspHoneycomb.honeycombHomeomorph 0
              (CuspCentralHomology.edgeArcBase 0 k t : (CuspHoneycombTiling.Plane)))
    rw [CuspCentralHomology.honeycombHomeomorph_edgeArcBase]
  simpa only [map_one, CuspCentralHomology.edgeArcBase_eq_dualSidePoint] using h

private theorem CuspCentralHomology.BaseCover.phaseOne_doubleCylinder_mo1973_14850
    (t : unitInterval) (j : Fin 3) :
    CuspCentralHomology.doubleCylinder (fun _ => 0) 1 zero_lt_one
        (t, CuspCentralHomology.thetaCircleInclusion j 1) =
      CuspHoneycomb.honeycombCollapseMap (fun _ => 0) 1 zero_lt_one
        (1, CuspCentralHomology.orientedEdgeBasePoint t j) := by
  fin_cases j
  · exact phaseOne_edgeCylinder_mo1973_14849 0 t
  · exact phaseOne_edgeCylinder_mo1973_14849 1 (unitInterval.symm t)
  · exact phaseOne_edgeCylinder_mo1973_14849 2 t

private theorem
    CuspCentralHomology.BaseCover.thetaBaseCylinder_eq_iff (p q : unitInterval × Fin 3) :
    CuspCentralHomology.thetaBaseCylinder p = CuspCentralHomology.thetaBaseCylinder q ↔
      (CuspCentralHomology.suspensionSetoid (Fin 3)).r p q := by
  rcases p with ⟨s, j⟩
  rcases q with ⟨t, k⟩
  constructor
  · intro h
    have he :
      CuspCentralHomology.doubleCylinder (fun _ => 0) 1 zero_lt_one
          (s, CuspCentralHomology.thetaCircleInclusion j 1) =
        CuspCentralHomology.doubleCylinder (fun _ => 0) 1 zero_lt_one
          (t, CuspCentralHomology.thetaCircleInclusion k 1) := by
      rw [phaseOne_doubleCylinder_mo1973_14850, phaseOne_doubleCylinder_mo1973_14850]
      exact phaseOneCollapse_eq_of_base_eq_mo1973_14848 h
    obtain ⟨hst, hzero | hone | hlabel⟩ :=
      (CuspCentralHomology.doubleCylinder_eq_iff (fun _ => 0) 1 zero_lt_one
            (s, CuspCentralHomology.thetaCircleInclusion j 1)
            (t, CuspCentralHomology.thetaCircleInclusion k 1)).mp
        he
    · exact ⟨hst, Or.inl hzero⟩
    · exact ⟨hst, Or.inr (Or.inl hone)⟩
    · refine ⟨hst, Or.inr (Or.inr ?_)⟩
      simpa only [CuspCentralHomology.thetaCircleLabel_inclusion] using
        congrArg CuspCentralHomology.thetaCircleLabel hlabel
  · exact CuspCentralHomology.thetaBaseCylinder_respects _ _

private theorem CuspCentralHomology.BaseCover.thetaBaseMap_injective :
    Function.Injective CuspCentralHomology.thetaBaseMap := by
  intro x y h
  obtain ⟨⟨s, j⟩, rfl⟩ := CuspCentralHomology.Suspension.mk_surjective x
  obtain ⟨⟨t, k⟩, rfl⟩ := CuspCentralHomology.Suspension.mk_surjective y
  exact Quotient.sound ((thetaBaseCylinder_eq_iff (s, j) (t, k)).mp h)

private theorem CuspCentralHomology.BaseCover.thetaBoundaryMap_injective :
    Function.Injective thetaBoundaryMap := by
  intro x y h
  exact thetaBaseMap_injective (congrArg Subtype.val h)

private def CuspCentralHomology.BaseCover.thetaBoundaryHomeomorph :
    CuspCentralHomology.Theta ≃ₜ boundary :=
  (thetaBoundaryMap.continuous.isClosedEmbedding
        thetaBoundaryMap_injective).toIsEmbedding |>.toHomeomorphOfSurjective
    thetaBoundaryMap_surjective

private def CuspCentralHomology.BaseCover.boundaryThetaHomeomorph :
    boundary ≃ₜ CuspCentralHomology.Theta :=
  thetaBoundaryHomeomorph.symm

private theorem CuspCentralHomology.BaseCover.thetaBaseMap_boundaryThetaHomeomorph (q : boundary) :
    CuspCentralHomology.thetaBaseMap (boundaryThetaHomeomorph q) = (q : BaseTorus) :=
  congrArg Subtype.val (thetaBoundaryHomeomorph.apply_symm_apply q)

private def CuspCentralHomology.BaseCover.boundaryInclusion : C(boundary, BaseTorus) :=
  ⟨Subtype.val, continuous_subtype_val⟩

private def CuspCentralHomology.BaseCover.frontierBoundaryMap :
    C(frontier CuspHoneycombTiling.baseCell, boundary) :=
  ⟨fun y =>
    ⟨cellMap
        ⟨(y : (CuspHoneycombTiling.Plane)),
          CuspHoneycombTiling.baseCell_isClosed.frontier_subset y.2⟩,
      (cellMap_mem_boundary_iff _).mpr y.2⟩,
    (cellMap.continuous.comp (continuous_subtype_val.subtype_mk _)).subtype_mk _⟩

private def CuspCentralHomology.BaseCover.circleBoundaryMap : C(Circle, boundary) :=
  frontierBoundaryMap.comp
    (CuspCentralHomology.Radial.frontierCellCircleHomeomorph.symm :
      C(Circle, frontier CuspHoneycombTiling.baseCell))

@[simp]
private theorem CuspCentralHomology.BaseCover.circleBoundaryMap_coe (z : Circle) :
    (circleBoundaryMap z : BaseTorus) =
      CuspCentralHomology.baseTorusPoint
        (CuspCentralHomology.Radial.frontierCellCircleHomeomorph.symm z :
          (CuspHoneycombTiling.Plane)) :=
  rfl

private def CuspCentralHomology.BaseCover.circleThetaMap : C(Circle, CuspCentralHomology.Theta) :=
  (boundaryThetaHomeomorph : C(boundary, CuspCentralHomology.Theta)).comp circleBoundaryMap

private theorem CuspCentralHomology.BaseCover.thetaBaseMap_circleThetaMap :
    CuspCentralHomology.thetaBaseMap.comp circleThetaMap =
      boundaryInclusion.comp circleBoundaryMap := by
  apply ContinuousMap.ext
  intro z
  exact thetaBaseMap_boundaryThetaHomeomorph (circleBoundaryMap z)

private def CuspCentralHomology.BaseCover.collarCellInclusion (a : ℝ)
    (p : CuspCentralHomology.Radial.OpenCollar a) : CuspHoneycombTiling.baseCell :=
  ⟨(p : (CuspHoneycombTiling.Plane)), (CuspCentralHomology.Radial.mem_baseCell_iff _).mpr p.2.2⟩

private theorem CuspCentralHomology.BaseCover.collarCellInclusion_continuous (a : ℝ) :
    Continuous (collarCellInclusion a) :=
  continuous_subtype_val.subtype_mk _

private theorem CuspCentralHomology.BaseCover.collarCellInclusion_injective (a : ℝ) :
    Function.Injective (collarCellInclusion a) := by
  intro p q h
  apply Subtype.ext
  exact congrArg (fun y : CuspHoneycombTiling.baseCell => (y : (CuspHoneycombTiling.Plane))) h

private def CuspCentralHomology.BaseCover.collarCellMap (a : ℝ)
    (p : CuspCentralHomology.Radial.OpenCollar a) : outerRegion a :=
  ⟨cellMap (collarCellInclusion a p), (cellMap_mem_outerRegion_iff a _).mpr p.2.1⟩

@[simp]
private theorem CuspCentralHomology.BaseCover.collarCellMap_coe (a : ℝ)
    (p : CuspCentralHomology.Radial.OpenCollar a) :
    (collarCellMap a p : BaseTorus) = basePoint (p : (CuspHoneycombTiling.Plane)) :=
  rfl

private theorem CuspCentralHomology.BaseCover.radius_collarCellMap (a : ℝ)
    (p : CuspCentralHomology.Radial.OpenCollar a) :
    radius (collarCellMap a p) =
      CuspCentralHomology.Radial.cellGauge (p : (CuspHoneycombTiling.Plane)) :=
  radius_cellMap (collarCellInclusion a p)

private theorem CuspCentralHomology.BaseCover.collarCellMap_continuous (a : ℝ) :
    Continuous (collarCellMap a) :=
  (cellMap.continuous.comp (collarCellInclusion_continuous a)).subtype_mk _

private theorem CuspCentralHomology.BaseCover.collarCellMap_surjective (a : ℝ) :
    Function.Surjective (collarCellMap a) := by
  rintro ⟨q, hq⟩
  obtain ⟨y, hy⟩ := cellMap_surjective q
  have hg : a < CuspCentralHomology.Radial.cellGauge (y : (CuspHoneycombTiling.Plane)) := by
    apply (cellMap_mem_outerRegion_iff a y).mp
    rwa [hy]
  refine
    ⟨⟨(y : (CuspHoneycombTiling.Plane)), hg,
        (CuspCentralHomology.Radial.mem_baseCell_iff _).mp y.2⟩,
      ?_⟩
  apply Subtype.ext
  exact hy

private def CuspCentralHomology.BaseCover.collarPreimageHomeomorph (a : ℝ) :
    CuspCentralHomology.Radial.OpenCollar a ≃ₜ (cellMap ⁻¹' outerRegion a)
    where
  toFun p := ⟨collarCellInclusion a p, (cellMap_mem_outerRegion_iff a _).mpr p.2.1⟩
  invFun
    p :=
    ⟨(p.1 : (CuspHoneycombTiling.Plane)), (cellMap_mem_outerRegion_iff a p.1).mp p.2,
      (CuspCentralHomology.Radial.mem_baseCell_iff _).mp p.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (collarCellInclusion_continuous a).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

private theorem CuspCentralHomology.BaseCover.collarCellMap_isProperMap (a : ℝ) :
    IsProperMap (collarCellMap a) := by
  have hf := cellMap_isProperMap.restrictPreimage (outerRegion a)
  have hc := hf.comp (collarPreimageHomeomorph a).isProperMap
  have he :
    (outerRegion a).restrictPreimage cellMap ∘ collarPreimageHomeomorph a = collarCellMap a := by
    funext p
    apply Subtype.ext
    rfl
  rw [he] at hc
  exact hc

private theorem CuspCentralHomology.BaseCover.collarCellMap_isClosedMap (a : ℝ) :
    IsClosedMap (collarCellMap a) :=
  (collarCellMap_isProperMap a).isClosedMap

private theorem CuspCentralHomology.BaseCover.collarCellMap_isQuotientMap (a : ℝ) :
    Topology.IsQuotientMap (collarCellMap a) :=
  (collarCellMap_isClosedMap a).isQuotientMap (collarCellMap_continuous a)
    (collarCellMap_surjective a)

private theorem CuspCentralHomology.BaseCover.collarCellHomotopy_compatible (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) (s : unitInterval) (p q : CuspCentralHomology.Radial.OpenCollar a)
    (h : collarCellMap a p = collarCellMap a q) :
    collarCellMap a (CuspCentralHomology.Radial.outwardOpenCollarHomotopy a ha ha1 (s, p)) =
      collarCellMap a (CuspCentralHomology.Radial.outwardOpenCollarHomotopy a ha ha1 (s, q)) := by
  have he : cellMap (collarCellInclusion a p) = cellMap (collarCellInclusion a q) :=
    congrArg Subtype.val h
  rcases cellMap_eq_or_frontier (collarCellInclusion a p) (collarCellInclusion a q) he with hpq |
    ⟨hp, hq⟩
  · rw [collarCellInclusion_injective a hpq]
  · rw [CuspCentralHomology.Radial.outwardOpenCollarHomotopy_fixed a ha ha1 s p hp,
      CuspCentralHomology.Radial.outwardOpenCollarHomotopy_fixed a ha ha1 s q hq]
    exact h

private def CuspCentralHomology.BaseCover.outerRegionBoundaryInclusion (a : ℝ) (ha1 : a < 1) :
    C(boundary, outerRegion a)
    where
  toFun x := ⟨x, boundary_subset_outerRegion a ha1 x.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

private def CuspCentralHomology.BaseCover.outerRegionDeformation (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (s : unitInterval) (x : outerRegion a) : outerRegion a :=
  CuspHoneycombHexagon.CommonFibres.descend (collarCellMap a)
    (fun p =>
      collarCellMap a (CuspCentralHomology.Radial.outwardOpenCollarHomotopy a ha ha1 (s, p)))
    (collarCellMap_surjective a) x

@[simp]
private theorem
    CuspCentralHomology.BaseCover.outerRegionDeformation_collarCellMap (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) (s : unitInterval) (p : CuspCentralHomology.Radial.OpenCollar a) :
    outerRegionDeformation a ha ha1 s (collarCellMap a p) =
      collarCellMap a (CuspCentralHomology.Radial.outwardOpenCollarHomotopy a ha ha1 (s, p)) :=
  CuspHoneycombHexagon.CommonFibres.descend_apply (collarCellMap a)
    (fun p =>
      collarCellMap a (CuspCentralHomology.Radial.outwardOpenCollarHomotopy a ha ha1 (s, p)))
    (collarCellMap_surjective a) (collarCellHomotopy_compatible a ha ha1 s) p

private theorem CuspCentralHomology.BaseCover.outerRegionDeformation_collarCellMap_coe (a : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (s : unitInterval) (p : CuspCentralHomology.Radial.OpenCollar a) :
    (outerRegionDeformation a ha ha1 s (collarCellMap a p) : BaseTorus) =
      basePoint
        (((1 - (s : ℝ)) + (s : ℝ) / CuspCentralHomology.Radial.cellGauge p) •
          (p : (CuspHoneycombTiling.Plane))) := by
  rw [outerRegionDeformation_collarCellMap, collarCellMap_coe,
    CuspCentralHomology.Radial.outwardOpenCollarHomotopy_coe]

@[simp]
private theorem CuspCentralHomology.BaseCover.outerRegionDeformation_zero (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) (x : outerRegion a) : outerRegionDeformation a ha ha1 0 x = x := by
  obtain ⟨p, rfl⟩ := collarCellMap_surjective a x
  rw [outerRegionDeformation_collarCellMap,
    (CuspCentralHomology.Radial.outwardOpenCollarHomotopy a ha ha1).apply_zero]
  rfl

private theorem CuspCentralHomology.BaseCover.outerRegionDeformation_radius (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) (s : unitInterval) (x : outerRegion a) :
    radius (outerRegionDeformation a ha ha1 s x) = (1 - (s : ℝ)) * radius x + (s : ℝ) := by
  obtain ⟨p, rfl⟩ := collarCellMap_surjective a x
  rw [outerRegionDeformation_collarCellMap, radius_collarCellMap, radius_collarCellMap]
  exact CuspCentralHomology.Radial.outwardOpenCollarHomotopy_gauge a ha ha1 s p

private theorem
    CuspCentralHomology.BaseCover.outerRegionDeformation_one_mem_boundary (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) (x : outerRegion a) :
    (outerRegionDeformation a ha ha1 1 x : BaseTorus) ∈ boundary := by
  change radius (outerRegionDeformation a ha ha1 1 x) = 1
  rw [outerRegionDeformation_radius]
  simp

private theorem CuspCentralHomology.BaseCover.outerRegionDeformation_fixed (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) (s : unitInterval) (x : outerRegion a) (hx : (x : BaseTorus) ∈ boundary) :
    outerRegionDeformation a ha ha1 s x = x := by
  obtain ⟨p, rfl⟩ := collarCellMap_surjective a x
  have hp : (p : (CuspHoneycombTiling.Plane)) ∈ frontier CuspHoneycombTiling.baseCell := by
    apply (CuspCentralHomology.Radial.mem_frontier_baseCell_iff _).mpr
    change radius (collarCellMap a p) = 1 at hx
    rwa [radius_collarCellMap] at hx
  rw [outerRegionDeformation_collarCellMap,
    CuspCentralHomology.Radial.outwardOpenCollarHomotopy_fixed a ha ha1 s p hp]

private theorem CuspCentralHomology.BaseCover.outerRegionDeformation_continuous (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) :
    Continuous
      (fun p : unitInterval × outerRegion a => outerRegionDeformation a ha ha1 p.1 p.2) := by
  apply (collarCellMap_isQuotientMap a).continuous_lift_prod_right
  have hc :=
    (collarCellMap_continuous a).comp
      (CuspCentralHomology.Radial.outwardOpenCollarHomotopy a ha ha1).continuous
  simpa only [outerRegionDeformation_collarCellMap, Function.comp_def, Prod.eta] using hc

private def CuspCentralHomology.BaseCover.outerRegionRetraction (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    C(outerRegion a, boundary)
    where
  toFun
    x := ⟨outerRegionDeformation a ha ha1 1 x, outerRegionDeformation_one_mem_boundary a ha ha1 x⟩
  continuous_toFun :=
    (continuous_subtype_val.comp
          ((outerRegionDeformation_continuous a ha ha1).comp
            (continuous_const.prodMk continuous_id))).subtype_mk
      _

@[simp]
private theorem
    CuspCentralHomology.BaseCover.outerRegionRetraction_coe (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (x : outerRegion a) :
    (outerRegionRetraction a ha ha1 x : BaseTorus) = outerRegionDeformation a ha ha1 1 x :=
  rfl

private theorem
    CuspCentralHomology.BaseCover.outerRegionRetraction_collarCellMap (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) (p : CuspCentralHomology.Radial.OpenCollar a) :
    (outerRegionRetraction a ha ha1 (collarCellMap a p) : BaseTorus) =
      basePoint
        ((CuspCentralHomology.Radial.cellGauge p)⁻¹ • (p : (CuspHoneycombTiling.Plane))) := by
  rw [outerRegionRetraction_coe, outerRegionDeformation_collarCellMap_coe]
  simp

@[simp]
private theorem
    CuspCentralHomology.BaseCover.outerRegionRetraction_comp_inclusion (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) :
    (outerRegionRetraction a ha ha1).comp (outerRegionBoundaryInclusion a ha1) =
      ContinuousMap.id boundary := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change
    (outerRegionDeformation a ha ha1 1 (outerRegionBoundaryInclusion a ha1 x) : BaseTorus) = x
  exact
    congrArg Subtype.val
      (outerRegionDeformation_fixed a ha ha1 1 (outerRegionBoundaryInclusion a ha1 x) x.2)

private def
    CuspCentralHomology.BaseCover.outerRegionHomotopyRel (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    (ContinuousMap.id (outerRegion a)).HomotopyRel
      ((outerRegionBoundaryInclusion a ha1).comp (outerRegionRetraction a ha ha1))
      {x : outerRegion a | (x : BaseTorus) ∈ boundary}
    where
  toFun p := outerRegionDeformation a ha ha1 p.1 p.2
  continuous_toFun := outerRegionDeformation_continuous a ha ha1
  map_zero_left := outerRegionDeformation_zero a ha ha1
  map_one_left _ := rfl
  prop' := outerRegionDeformation_fixed a ha ha1

private def CuspCentralHomology.BaseCover.outerRegionBoundaryHomotopyEquiv (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) : outerRegion a ≃ₕ boundary
    where
  toFun := outerRegionRetraction a ha ha1
  invFun := outerRegionBoundaryInclusion a ha1
  left_inv := ⟨(outerRegionHomotopyRel a ha ha1).toHomotopy.symm⟩
  right_inv := by
    refine ⟨?_⟩
    rw [outerRegionRetraction_comp_inclusion]
    exact ContinuousMap.Homotopy.refl _

private def CuspCentralHomology.BaseCover.interiorCellInclusion :
    C(CuspCentralHomology.Radial.InteriorCell, CuspHoneycombTiling.baseCell)
    where
  toFun y := ⟨(y : (CuspHoneycombTiling.Plane)), interior_subset y.property⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

private def CuspCentralHomology.BaseCover.interiorCellMap :
    C(CuspCentralHomology.Radial.InteriorCell, BaseTorus) :=
  cellMap.comp interiorCellInclusion

private def CuspCentralHomology.BaseCover.interiorCellToInnerRegion :
    C(CuspCentralHomology.Radial.InteriorCell, innerRegion)
    where
  toFun
    y :=
    ⟨cellMap (interiorCellInclusion y),
      (cellMap_mem_innerRegion_iff (interiorCellInclusion y)).mpr y.property⟩
  continuous_toFun := interiorCellMap.continuous.subtype_mk _

private theorem CuspCentralHomology.BaseCover.interiorCellToInnerRegion_injective :
    Function.Injective interiorCellToInnerRegion := by
  intro y z h
  have he : interiorCellInclusion y = interiorCellInclusion z :=
    cellMap_eq_of_interior (interiorCellInclusion y) (interiorCellInclusion z) y.property
      (congrArg Subtype.val h)
  apply Subtype.ext
  exact congrArg (fun x : CuspHoneycombTiling.baseCell => (x : (CuspHoneycombTiling.Plane))) he

private theorem CuspCentralHomology.BaseCover.interiorCellToInnerRegion_surjective :
    Function.Surjective interiorCellToInnerRegion := by
  intro q
  obtain ⟨y, hy⟩ := cellMap_surjective (q : BaseTorus)
  have hyinner : (y : (CuspHoneycombTiling.Plane)) ∈ interior CuspHoneycombTiling.baseCell := by
    apply (cellMap_mem_innerRegion_iff y).mp
    rw [hy]
    exact q.property
  refine ⟨⟨(y : (CuspHoneycombTiling.Plane)), hyinner⟩, ?_⟩
  apply Subtype.ext
  exact hy

private def CuspCentralHomology.BaseCover.interiorPreimageHomeomorph :
    CuspCentralHomology.Radial.InteriorCell ≃ₜ (cellMap ⁻¹' innerRegion)
    where
  toFun
    y :=
    ⟨interiorCellInclusion y,
      (cellMap_mem_innerRegion_iff (interiorCellInclusion y)).mpr y.property⟩
  invFun
    y := ⟨(y.1 : (CuspHoneycombTiling.Plane)), (cellMap_mem_innerRegion_iff y.1).mp y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := interiorCellInclusion.continuous.subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val

private theorem CuspCentralHomology.BaseCover.interiorCellToInnerRegion_isProperMap :
    IsProperMap interiorCellToInnerRegion := by
  have h :=
    (cellMap_isProperMap.restrictPreimage innerRegion).comp interiorPreimageHomeomorph.isProperMap
  have he :
    innerRegion.restrictPreimage cellMap ∘ interiorPreimageHomeomorph =
      interiorCellToInnerRegion := by
    funext y
    apply Subtype.ext
    rfl
  rw [he] at h
  exact h

private theorem CuspCentralHomology.BaseCover.interiorCellToInnerRegion_isClosedMap :
    IsClosedMap interiorCellToInnerRegion :=
  interiorCellToInnerRegion_isProperMap.isClosedMap

private def CuspCentralHomology.BaseCover.interiorCellHomeomorph :
    CuspCentralHomology.Radial.InteriorCell ≃ₜ innerRegion :=
  Equiv.toHomeomorphOfContinuousClosed
    (Equiv.ofBijective interiorCellToInnerRegion
      ⟨interiorCellToInnerRegion_injective, interiorCellToInnerRegion_surjective⟩)
    interiorCellToInnerRegion.continuous interiorCellToInnerRegion_isClosedMap

@[simp]
private theorem CuspCentralHomology.BaseCover.interiorCellHomeomorph_coe
    (y : CuspCentralHomology.Radial.InteriorCell) :
    (interiorCellHomeomorph y : BaseTorus) = cellMap (interiorCellInclusion y) :=
  rfl

private def CuspCentralHomology.BaseCover.innerRegionCellHomeomorph :
    innerRegion ≃ₜ CuspCentralHomology.Radial.InteriorCell :=
  interiorCellHomeomorph.symm

private def CuspCentralHomology.BaseCover.innerRegionPointHomotopyEquiv : innerRegion ≃ₕ Unit :=
  innerRegionCellHomeomorph.toHomotopyEquiv.trans
    CuspCentralHomology.Radial.interiorCellPointHomotopyEquiv

private instance CuspCentralHomology.BaseCover.innerRegion_contractibleSpace :
    ContractibleSpace innerRegion :=
  innerRegionPointHomotopyEquiv.contractibleSpace

private def CuspCentralHomology.BaseCover.overlapRegion (a : ℝ) : Set BaseTorus :=
  outerRegion a ∩ innerRegion

private def
    CuspCentralHomology.BaseCover.overlapIntoInner (a : ℝ) : C(overlapRegion a, innerRegion) :=
  ⟨fun q => ⟨(q : BaseTorus), q.property.2⟩, continuous_subtype_val.subtype_mk _⟩

private def
    CuspCentralHomology.BaseCover.overlapIntoOuter (a : ℝ) : C(overlapRegion a, outerRegion a) :=
  ⟨fun q => ⟨(q : BaseTorus), q.property.1⟩, continuous_subtype_val.subtype_mk _⟩

private def CuspCentralHomology.BaseCover.annulusCellInclusion (a : ℝ) :
    C(CuspCentralHomology.Radial.Annulus a, CuspCentralHomology.Radial.InteriorCell) :=
  ⟨fun y =>
    ⟨(y : (CuspHoneycombTiling.Plane)),
      (CuspCentralHomology.Radial.mem_interior_baseCell_iff _).mpr y.property.2⟩,
    continuous_subtype_val.subtype_mk _⟩

@[simp]
private theorem CuspCentralHomology.BaseCover.annulusCellInclusion_coe (a : ℝ)
    (y : CuspCentralHomology.Radial.Annulus a) :
    (annulusCellInclusion a y : (CuspHoneycombTiling.Plane)) =
      (y : (CuspHoneycombTiling.Plane)) :=
  rfl

private theorem CuspCentralHomology.BaseCover.annulusCellInclusion_injective (a : ℝ) :
    Function.Injective (annulusCellInclusion a) := by
  intro y z h
  apply Subtype.ext
  exact
    congrArg
      (fun x : CuspCentralHomology.Radial.InteriorCell => (x : (CuspHoneycombTiling.Plane))) h

private theorem CuspCentralHomology.BaseCover.interiorCellHomeomorph_radius
    (y : CuspCentralHomology.Radial.InteriorCell) :
    radius (interiorCellHomeomorph y : BaseTorus) =
      CuspCentralHomology.Radial.cellGauge (y : (CuspHoneycombTiling.Plane)) := by
  rw [interiorCellHomeomorph_coe, radius_cellMap]
  rfl

private def CuspCentralHomology.BaseCover.overlapCellMap (a : ℝ) :
    C(CuspCentralHomology.Radial.Annulus a, overlapRegion a)
    where
  toFun
    y :=
    ⟨(interiorCellHomeomorph (annulusCellInclusion a y) : BaseTorus),
      by
      constructor
      · change a < radius (interiorCellHomeomorph (annulusCellInclusion a y) : BaseTorus)
        rw [interiorCellHomeomorph_radius, annulusCellInclusion_coe]
        exact y.property.1
      · exact (interiorCellHomeomorph (annulusCellInclusion a y)).property⟩
  continuous_toFun :=
    (continuous_subtype_val.comp
          (interiorCellHomeomorph.continuous.comp (annulusCellInclusion a).continuous)).subtype_mk
      _

private theorem CuspCentralHomology.BaseCover.overlapCellMap_intoInner (a : ℝ)
    (y : CuspCentralHomology.Radial.Annulus a) :
    overlapIntoInner a (overlapCellMap a y) = interiorCellHomeomorph (annulusCellInclusion a y) :=
  rfl

private def CuspCentralHomology.BaseCover.overlapCellInverse (a : ℝ) :
    C(overlapRegion a, CuspCentralHomology.Radial.Annulus a)
    where
  toFun
    q :=
    let y := interiorCellHomeomorph.symm (overlapIntoInner a q)
    ⟨(y : (CuspHoneycombTiling.Plane)), by
      constructor
      · rw [← interiorCellHomeomorph_radius y]
        dsimp only [y]
        rw [Homeomorph.apply_symm_apply]
        exact q.property.1
      · exact (CuspCentralHomology.Radial.mem_interior_baseCell_iff _).mp y.property⟩
  continuous_toFun :=
    (continuous_subtype_val.comp
          (interiorCellHomeomorph.symm.continuous.comp
            (overlapIntoInner a).continuous)).subtype_mk
      _

private theorem
    CuspCentralHomology.BaseCover.overlapCellInverse_interior (a : ℝ) (q : overlapRegion a) :
    annulusCellInclusion a (overlapCellInverse a q) =
      interiorCellHomeomorph.symm (overlapIntoInner a q) :=
  rfl

private def CuspCentralHomology.BaseCover.annulusOverlapHomeomorph (a : ℝ) :
    CuspCentralHomology.Radial.Annulus a ≃ₜ overlapRegion a
    where
  toFun := overlapCellMap a
  invFun := overlapCellInverse a
  left_inv
    y := by
    apply annulusCellInclusion_injective a
    rw [overlapCellInverse_interior, overlapCellMap_intoInner, Homeomorph.symm_apply_apply]
  right_inv
    q := by
    apply Subtype.ext
    change
      (interiorCellHomeomorph (annulusCellInclusion a (overlapCellInverse a q)) : BaseTorus) =
        (q : BaseTorus)
    rw [overlapCellInverse_interior, Homeomorph.apply_symm_apply]
    rfl
  continuous_toFun := (overlapCellMap a).continuous
  continuous_invFun := (overlapCellInverse a).continuous

private def CuspCentralHomology.BaseCover.overlapHomeomorph (a : ℝ) (ha : 0 ≤ a) :
    overlapRegion a ≃ₜ CuspCentralHomology.Radial.CellFrontier × Set.Ioo a 1 :=
  (annulusOverlapHomeomorph a).symm.trans (CuspCentralHomology.Radial.annulusHomeomorph a ha)

private def CuspCentralHomology.BaseCover.overlapDirection (a : ℝ) (ha : 0 ≤ a) :
    C(overlapRegion a, CuspCentralHomology.Radial.CellFrontier) :=
  ⟨fun q => (overlapHomeomorph a ha q).1, continuous_fst.comp (overlapHomeomorph a ha).continuous⟩

private theorem CuspCentralHomology.BaseCover.overlapDirection_annulus (a : ℝ) (ha : 0 ≤ a)
    (y : CuspCentralHomology.Radial.Annulus a) :
    (overlapDirection a ha (annulusOverlapHomeomorph a y) : (CuspHoneycombTiling.Plane)) =
      (CuspCentralHomology.Radial.cellGauge (y : (CuspHoneycombTiling.Plane)))⁻¹ •
        (y : (CuspHoneycombTiling.Plane)) := by
  change
    ((CuspCentralHomology.Radial.annulusHomeomorph a ha
            ((annulusOverlapHomeomorph a).symm (annulusOverlapHomeomorph a y))).1 :
        (CuspHoneycombTiling.Plane)) =
      _
  rw [Homeomorph.symm_apply_apply]
  rfl

private def
    CuspCentralHomology.BaseCover.overlapCircleHomotopyEquiv (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    overlapRegion a ≃ₕ _root_.Circle :=
  (annulusOverlapHomeomorph a).symm.toHomotopyEquiv.trans
    (CuspCentralHomology.Radial.annulusCircleHomotopyEquiv a ha ha1)

private theorem
    CuspCentralHomology.BaseCover.overlapCircleHomotopyEquiv_eq_direction (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) (q : overlapRegion a) :
    overlapCircleHomotopyEquiv a ha ha1 q =
      CuspCentralHomology.Radial.frontierCellCircleHomeomorph (overlapDirection a ha q) :=
  rfl

private theorem CuspCentralHomology.BaseCover.overlapIntoOuter_boundary_map (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) :
    (outerRegionRetraction a ha ha1).comp (overlapIntoOuter a) =
      circleBoundaryMap.comp (overlapCircleHomotopyEquiv a ha ha1).toFun := by
  apply ContinuousMap.ext
  intro q
  obtain ⟨y, rfl⟩ := (annulusOverlapHomeomorph a).surjective q
  apply Subtype.ext
  have hin :
    overlapIntoOuter a (annulusOverlapHomeomorph a y) =
      collarCellMap a ⟨(y : (CuspHoneycombTiling.Plane)), y.2.1, y.2.2.le⟩ :=
    rfl
  change
    (outerRegionRetraction a ha ha1 (overlapIntoOuter a (annulusOverlapHomeomorph a y)) :
        BaseTorus) =
      (circleBoundaryMap (overlapCircleHomotopyEquiv a ha ha1 (annulusOverlapHomeomorph a y)) :
        BaseTorus)
  rw [hin, outerRegionRetraction_collarCellMap, circleBoundaryMap_coe,
    overlapCircleHomotopyEquiv_eq_direction, Homeomorph.symm_apply_apply,
    overlapDirection_annulus]

private def CuspCentralHomology.BaseCover.outerRegionThetaHomotopyEquiv (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) : outerRegion a ≃ₕ CuspCentralHomology.Theta :=
  (outerRegionBoundaryHomotopyEquiv a ha ha1).trans boundaryThetaHomeomorph.toHomotopyEquiv

private theorem CuspCentralHomology.BaseCover.overlapIntoOuter_theta_map (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) :
    (outerRegionThetaHomotopyEquiv a ha ha1).toFun.comp (overlapIntoOuter a) =
      circleThetaMap.comp (overlapCircleHomotopyEquiv a ha ha1).toFun := by
  apply ContinuousMap.ext
  intro q
  exact
    congrArg (fun f : C(overlapRegion a, boundary) => boundaryThetaHomeomorph (f q))
      (overlapIntoOuter_boundary_map a ha ha1)

private def CuspCentralHomology.BaseCover.baseBoundaryNullhomotopy :
    (boundaryInclusion.comp circleBoundaryMap).Homotopy
      (ContinuousMap.const Circle
        (CuspCentralHomology.baseTorusPoint (0 : (CuspHoneycombTiling.Plane))))
    where
  toFun
    p :=
    CuspCentralHomology.baseTorusPoint
      ((1 - (p.1 : ℝ)) •
        (CuspCentralHomology.Radial.frontierCellCircleHomeomorph.symm p.2 :
          (CuspHoneycombTiling.Plane)))
  continuous_toFun :=
    CuspCentralHomology.baseTorusPoint_continuous.comp
      ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
        (continuous_subtype_val.comp
          (CuspCentralHomology.Radial.frontierCellCircleHomeomorph.symm.continuous.comp
            continuous_snd)))
  map_zero_left
    z := by
    change
      CuspCentralHomology.baseTorusPoint
          ((1 - (0 : ℝ)) •
            (CuspCentralHomology.Radial.frontierCellCircleHomeomorph.symm z :
              (CuspHoneycombTiling.Plane))) =
        _
    rw [sub_zero, one_smul]
    rfl
  map_one_left
    z := by
    change
      CuspCentralHomology.baseTorusPoint
          ((1 - (1 : ℝ)) •
            (CuspCentralHomology.Radial.frontierCellCircleHomeomorph.symm z :
              (CuspHoneycombTiling.Plane))) =
        _
    rw [sub_self, zero_smul]
    rfl

private theorem CuspCentralHomology.BaseCover.baseBoundary_homotopic_const :
    (boundaryInclusion.comp circleBoundaryMap).Homotopic
      (ContinuousMap.const Circle
        (CuspCentralHomology.baseTorusPoint (0 : (CuspHoneycombTiling.Plane)))) :=
  ⟨baseBoundaryNullhomotopy⟩

private theorem CuspCentralHomology.BaseCover.thetaBaseMap_circleThetaMap_homotopic_const :
    (CuspCentralHomology.thetaBaseMap.comp circleThetaMap).Homotopic
      (ContinuousMap.const Circle
        (CuspCentralHomology.baseTorusPoint (0 : (CuspHoneycombTiling.Plane)))) := by
  rw [thetaBaseMap_circleThetaMap]
  exact baseBoundary_homotopic_const

private abbrev CuspCentralHomology.BaseCover.PhaseBase :=
  ToricSpace.CompactFibreTorus × BaseTorus

private def CuspCentralHomology.BaseCover.phaseOuterRegion (a : ℝ) : Set PhaseBase :=
  Prod.snd ⁻¹' outerRegion a

private def CuspCentralHomology.BaseCover.phaseInnerRegion : Set PhaseBase :=
  Prod.snd ⁻¹' innerRegion

private def CuspCentralHomology.BaseCover.phaseOverlapRegion (a : ℝ) : Set PhaseBase :=
  phaseOuterRegion a ∩ phaseInnerRegion

private theorem CuspCentralHomology.BaseCover.phaseOuterRegion_isOpen (a : ℝ) :
    IsOpen (phaseOuterRegion a) :=
  (outerRegion_isOpen a).preimage continuous_snd

private theorem CuspCentralHomology.BaseCover.phaseInnerRegion_isOpen : IsOpen phaseInnerRegion :=
  innerRegion_isOpen.preimage continuous_snd

private theorem CuspCentralHomology.BaseCover.phaseOuterRegion_union_phaseInnerRegion (a : ℝ)
    (ha1 : a < 1) : phaseOuterRegion a ∪ phaseInnerRegion = Set.univ := by
  change Prod.snd ⁻¹' outerRegion a ∪ Prod.snd ⁻¹' innerRegion = Set.univ
  rw [← Set.preimage_union, outerRegion_union_innerRegion a ha1, Set.preimage_univ]

private def CuspCentralHomology.BaseCover.phaseRegionProductHomeomorph_mo1973_14992
    (s : Set BaseTorus) : (Prod.snd ⁻¹' s : Set PhaseBase) ≃ₜ ToricSpace.CompactFibreTorus × s
    where
  toFun p := (p.1.1, ⟨p.1.2, p.2⟩)
  invFun p := ⟨(p.1, (p.2 : BaseTorus)), p.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
  continuous_invFun :=
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _

private def CuspCentralHomology.BaseCover.phaseOuterRegionHomeomorph (a : ℝ) :
    phaseOuterRegion a ≃ₜ ToricSpace.CompactFibreTorus × outerRegion a :=
  phaseRegionProductHomeomorph_mo1973_14992 (outerRegion a)

private def CuspCentralHomology.BaseCover.phaseInnerRegionHomeomorph :
    phaseInnerRegion ≃ₜ ToricSpace.CompactFibreTorus × innerRegion :=
  phaseRegionProductHomeomorph_mo1973_14992 innerRegion

private def CuspCentralHomology.BaseCover.phaseOverlapRegionHomeomorph (a : ℝ) :
    phaseOverlapRegion a ≃ₜ ToricSpace.CompactFibreTorus × overlapRegion a :=
  phaseRegionProductHomeomorph_mo1973_14992 (overlapRegion a)

private def CuspCentralHomology.BaseCover.phaseOverlapIntoInner (a : ℝ) :
    C(phaseOverlapRegion a, phaseInnerRegion) :=
  ⟨fun p => ⟨(p : PhaseBase), p.property.2⟩, continuous_subtype_val.subtype_mk _⟩

private def CuspCentralHomology.BaseCover.phaseOverlapIntoOuter (a : ℝ) :
    C(phaseOverlapRegion a, phaseOuterRegion a) :=
  ⟨fun p => ⟨(p : PhaseBase), p.property.1⟩, continuous_subtype_val.subtype_mk _⟩

private def CuspCentralHomology.BaseCover.phaseOuterThetaHomotopyEquiv (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) :
    phaseOuterRegion a ≃ₕ ToricSpace.CompactFibreTorus × CuspCentralHomology.Theta :=
  (phaseOuterRegionHomeomorph a).toHomotopyEquiv.trans
    ((ContinuousMap.HomotopyEquiv.refl ToricSpace.CompactFibreTorus).prodCongr
      (outerRegionThetaHomotopyEquiv a ha ha1))

private def CuspCentralHomology.BaseCover.phaseInnerHomotopyEquiv :
    phaseInnerRegion ≃ₕ ToricSpace.CompactFibreTorus :=
  phaseInnerRegionHomeomorph.toHomotopyEquiv.trans
    (((ContinuousMap.HomotopyEquiv.refl ToricSpace.CompactFibreTorus).prodCongr
          innerRegionPointHomotopyEquiv).trans
      (Homeomorph.prodUnique ToricSpace.CompactFibreTorus Unit).toHomotopyEquiv)

private def CuspCentralHomology.BaseCover.phaseOverlapCircleHomotopyEquiv (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) : phaseOverlapRegion a ≃ₕ ToricSpace.CompactFibreTorus × Circle :=
  (phaseOverlapRegionHomeomorph a).toHomotopyEquiv.trans
    ((ContinuousMap.HomotopyEquiv.refl ToricSpace.CompactFibreTorus).prodCongr
      (overlapCircleHomotopyEquiv a ha ha1))

private theorem CuspCentralHomology.BaseCover.phaseOverlapIntoInner_phase_map (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) :
    phaseInnerHomotopyEquiv.toFun.comp (phaseOverlapIntoInner a) =
      (ContinuousMap.fst :
            C(ToricSpace.CompactFibreTorus × Circle, ToricSpace.CompactFibreTorus)).comp
        (phaseOverlapCircleHomotopyEquiv a ha ha1).toFun := by
  apply ContinuousMap.ext
  intro p
  rfl

private theorem CuspCentralHomology.BaseCover.phaseOverlapIntoOuter_theta_map (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) :
    (phaseOuterThetaHomotopyEquiv a ha ha1).toFun.comp (phaseOverlapIntoOuter a) =
      ((ContinuousMap.id ToricSpace.CompactFibreTorus).prodMap circleThetaMap).comp
        (phaseOverlapCircleHomotopyEquiv a ha ha1).toFun := by
  apply ContinuousMap.ext
  intro p
  apply Prod.ext
  · rfl
  · exact
      congrArg
        (fun f : C(overlapRegion a, CuspCentralHomology.Theta) =>
          f (phaseOverlapRegionHomeomorph a p).2)
        (overlapIntoOuter_theta_map a ha ha1)

private theorem CuspCentralHomology.SpecializationCover.productCollapse_basePoint
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (u : ToricSpace.CompactFibreTorus)
    (y : (CuspHoneycombTiling.Plane)) :
    CuspSpecialization.productCollapse C ε hε (u, CuspCentralHomology.BaseCover.basePoint y) =
      CuspHoneycomb.honeycombCollapseMap C ε hε
        (u * CuspSpecialization.sourcePhaseCharacter (C 0) y, y) := by
  change
    CuspSpecialization.productCollapse C ε hε
        (u, PeriodTorusHigherHomology.coordinateProjection 2 (-ToricSpace.realCuspVector y)) =
      _
  rw [CuspSpecialization.productCollapse_coordinateProjection,
    CuspSpecialization.realCuspVector_neg_realCuspVector]

private theorem CuspCentralHomology.SpecializationCover.productCollapse_cellMap
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (u : ToricSpace.CompactFibreTorus)
    (y : CuspHoneycombTiling.baseCell) :
    CuspSpecialization.productCollapse C ε hε (u, CuspCentralHomology.BaseCover.cellMap y) =
      CuspCentralHomology.fundamentalCellMap C ε hε
        (u * CuspSpecialization.sourcePhaseCharacter (C 0) (y : (CuspHoneycombTiling.Plane)),
          y) :=
  productCollapse_basePoint C ε hε u y

private theorem CuspCentralHomology.SpecializationCover.productCollapse_radius
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (p : CuspCentralHomology.BaseCover.PhaseBase) :
    CuspCentralHomology.centralRadius C ε hε (CuspSpecialization.productCollapse C ε hε p) =
      CuspCentralHomology.BaseCover.radius p.2 := by
  rcases p with ⟨u, b⟩
  obtain ⟨y, rfl⟩ := CuspCentralHomology.BaseCover.cellMap_surjective b
  rw [productCollapse_cellMap, CuspCentralHomology.centralRadius_fundamentalCellMap,
    CuspCentralHomology.BaseCover.radius_cellMap]

@[simp]
private theorem CuspCentralHomology.SpecializationCover.productCollapse_mem_outer_iff
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (a : ℝ)
    (p : CuspCentralHomology.BaseCover.PhaseBase) :
    CuspSpecialization.productCollapse C ε hε p ∈ CuspCentralHomology.outerRegion C ε hε a ↔
      p ∈ CuspCentralHomology.BaseCover.phaseOuterRegion a := by
  change
    a < CuspCentralHomology.centralRadius C ε hε (CuspSpecialization.productCollapse C ε hε p) ↔
      a < CuspCentralHomology.BaseCover.radius p.2
  rw [productCollapse_radius]

@[simp]
private theorem CuspCentralHomology.SpecializationCover.productCollapse_mem_inner_iff
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (p : CuspCentralHomology.BaseCover.PhaseBase) :
    CuspSpecialization.productCollapse C ε hε p ∈ CuspCentralHomology.innerRegion C ε hε ↔
      p ∈ CuspCentralHomology.BaseCover.phaseInnerRegion := by
  change
    CuspCentralHomology.centralRadius C ε hε (CuspSpecialization.productCollapse C ε hε p) < 1 ↔
      CuspCentralHomology.BaseCover.radius p.2 < 1
  rw [productCollapse_radius]

@[simp]
private theorem CuspCentralHomology.SpecializationCover.productCollapse_mem_overlap_iff
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (a : ℝ)
    (p : CuspCentralHomology.BaseCover.PhaseBase) :
    CuspSpecialization.productCollapse C ε hε p ∈ CuspCentralHomology.overlapRegion C ε hε a ↔
      p ∈ CuspCentralHomology.BaseCover.phaseOverlapRegion a := by
  change (_ ∧ _) ↔ (_ ∧ _)
  rw [productCollapse_mem_outer_iff, productCollapse_mem_inner_iff]

private theorem CuspCentralHomology.SpecializationCover.productCollapse_mapsTo_outer
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (a : ℝ) :
    Set.MapsTo (CuspSpecialization.productCollapse C ε hε)
      (CuspCentralHomology.BaseCover.phaseOuterRegion a)
      (CuspCentralHomology.outerRegion C ε hε a) :=
  fun p hp => (productCollapse_mem_outer_iff C ε hε a p).mpr hp

private theorem CuspCentralHomology.SpecializationCover.productCollapse_mapsTo_inner
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    Set.MapsTo (CuspSpecialization.productCollapse C ε hε)
      CuspCentralHomology.BaseCover.phaseInnerRegion (CuspCentralHomology.innerRegion C ε hε) :=
  fun p hp => (productCollapse_mem_inner_iff C ε hε p).mpr hp

private def
    CuspCentralHomology.SpecializationCover.overlapMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (a : ℝ) :
    C(CuspCentralHomology.BaseCover.phaseOverlapRegion a,
      CuspCentralHomology.overlapRegion C ε hε a)
    where
  toFun
    p :=
    ⟨CuspSpecialization.productCollapse C ε hε p,
      (productCollapse_mem_overlap_iff C ε hε a p).mpr p.property⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (CuspSpecialization.productCollapse C ε hε).continuous.comp continuous_subtype_val

@[simp]
private theorem
    CuspCentralHomology.SpecializationCover.overlapMap_coe (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (a : ℝ) (p : CuspCentralHomology.BaseCover.phaseOverlapRegion a) :
    (overlapMap C ε hε a p : CuspRetraction.QuotientCentralFibre C ε) =
      CuspSpecialization.productCollapse C ε hε p :=
  rfl

private theorem CuspCentralHomology.productCollapse_connecting_naturality
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha1 : a < 1) (n : ℕ)
    (x : SingularMayerVietoris.SingularHomology BaseCover.PhaseBase (n + 1)) :
    SingularMayerVietoris.singularHomologyMap (SpecializationCover.overlapMap C ε hε a) n
        (SingularMayerVietoris.connectingHomomorphism (BaseCover.phaseOuterRegion a)
          BaseCover.phaseInnerRegion (BaseCover.phaseOuterRegion_isOpen a)
          BaseCover.phaseInnerRegion_isOpen
          (BaseCover.phaseOuterRegion_union_phaseInnerRegion a ha1) n x) =
      SingularMayerVietoris.connectingHomomorphism (outerRegion C ε hε a) (innerRegion C ε hε)
        (outerRegion_isOpen C ε hε hε1 hC hR a) (innerRegion_isOpen C ε hε hε1 hC hR)
        (outerRegion_union_innerRegion C ε hε a ha1) n
        (SingularMayerVietoris.singularHomologyMap (CuspSpecialization.productCollapse C ε hε)
          (n + 1) x) :=
  SingularMayerVietoris.connectingHomomorphism_naturality_apply
    (CuspSpecialization.productCollapse C ε hε) (BaseCover.phaseOuterRegion a)
    BaseCover.phaseInnerRegion (outerRegion C ε hε a) (innerRegion C ε hε)
    (SpecializationCover.productCollapse_mapsTo_outer C ε hε a)
    (SpecializationCover.productCollapse_mapsTo_inner C ε hε)
    (BaseCover.phaseOuterRegion_isOpen a) BaseCover.phaseInnerRegion_isOpen
    (BaseCover.phaseOuterRegion_union_phaseInnerRegion a ha1)
    (outerRegion_isOpen C ε hε hε1 hC hR a) (innerRegion_isOpen C ε hε hε1 hC hR)
    (outerRegion_union_innerRegion C ε hε a ha1) n x

private def CuspCentralHomology.SpecializationCover.phaseCellShear (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (s : Set (CuspHoneycombTiling.Plane)) :
    (ToricSpace.CompactFibreTorus × s) ≃ₜ (ToricSpace.CompactFibreTorus × s)
    where
  toFun
    p :=
    (p.1 * CuspSpecialization.sourcePhaseCharacter C₀ (p.2 : (CuspHoneycombTiling.Plane)), p.2)
  invFun
    p :=
    (p.1 * (CuspSpecialization.sourcePhaseCharacter C₀ (p.2 : (CuspHoneycombTiling.Plane)))⁻¹,
      p.2)
  left_inv p := by simp only [mul_inv_cancel_right, Prod.eta]
  right_inv p := by simp only [mul_assoc, inv_mul_cancel, mul_one, Prod.eta]
  continuous_toFun :=
    (continuous_fst.mul
          ((CuspSpecialization.sourcePhaseCharacter_continuous C₀).comp
            (continuous_subtype_val.comp continuous_snd))).prodMk
      continuous_snd
  continuous_invFun :=
    (continuous_fst.mul
          (((CuspSpecialization.sourcePhaseCharacter_continuous C₀).comp
              (continuous_subtype_val.comp continuous_snd)).inv)).prodMk
      continuous_snd

@[simp]
private theorem CuspCentralHomology.SpecializationCover.phaseCellShear_apply
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (s : Set (CuspHoneycombTiling.Plane))
    (p : ToricSpace.CompactFibreTorus × s) :
    phaseCellShear C₀ s p =
      (p.1 * CuspSpecialization.sourcePhaseCharacter C₀ (p.2 : (CuspHoneycombTiling.Plane)),
        p.2) :=
  rfl

private def
    CuspCentralHomology.SpecializationCover.phaseCellShearHomotopy (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (s : Set (CuspHoneycombTiling.Plane)) :
    (ContinuousMap.id (ToricSpace.CompactFibreTorus × s)).Homotopy
      (phaseCellShear C₀ s :
        C(ToricSpace.CompactFibreTorus × s, ToricSpace.CompactFibreTorus × s))
    where
  toFun
    p :=
    (p.2.1 *
        CuspSpecialization.sourcePhaseCharacter C₀
          ((p.1 : ℝ) • (p.2.2 : (CuspHoneycombTiling.Plane))),
      p.2.2)
  continuous_toFun := by
    have hy :
      Continuous
        (fun p : unitInterval × (ToricSpace.CompactFibreTorus × s) =>
          (p.1 : ℝ) • (p.2.2 : (CuspHoneycombTiling.Plane))) :=
      (continuous_subtype_val.comp continuous_fst).smul
        (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))
    have hχ :
      Continuous
        (fun p : unitInterval × (ToricSpace.CompactFibreTorus × s) =>
          CuspSpecialization.sourcePhaseCharacter C₀
            ((p.1 : ℝ) • (p.2.2 : (CuspHoneycombTiling.Plane)))) := by
      simpa only [Function.comp_def] using
        (CuspSpecialization.sourcePhaseCharacter_continuous C₀).comp hy
    exact
      ((continuous_fst.comp continuous_snd).mul hχ).prodMk (continuous_snd.comp continuous_snd)
  map_zero_left p := by simp [CuspSpecialization.sourcePhaseCharacter_zero]
  map_one_left p := by simp [phaseCellShear_apply]

private theorem CuspCentralHomology.BaseCover.overlapRegion_pathConnectedSpace (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) : PathConnectedSpace (overlapRegion a) := by
  let : PathConnectedSpace CuspCentralHomology.Radial.CellFrontier :=
    CuspCentralHomology.Radial.frontierCellCircleHomeomorph.symm.surjective.pathConnectedSpace
      CuspCentralHomology.Radial.frontierCellCircleHomeomorph.symm.continuous
  let : PathConnectedSpace (Set.Ioo a 1) :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((convex_Ioo a 1).isPathConnected (Set.nonempty_Ioo.mpr ha1))
  exact
    (overlapHomeomorph a ha).symm.surjective.pathConnectedSpace
      (overlapHomeomorph a ha).symm.continuous

private theorem CuspCentralHomology.BaseCover.halfCoverLeftHomologyZero_injective :
    Function.Injective
      (SingularMayerVietoris.leftHomologyMap (CuspCentralHomology.BaseCover.outerRegion (1 / 2))
        (CuspCentralHomology.BaseCover.innerRegion) 0) := by
  let := overlapRegion_pathConnectedSpace (1 / 2) (by norm_num) (by norm_num)
  let i :
    C((CuspCentralHomology.BaseCover.overlapRegion (1 / 2)),
      (CuspCentralHomology.BaseCover.innerRegion)) :=
    ContinuousMap.inclusion
      (Set.inter_subset_right :
        (CuspCentralHomology.BaseCover.outerRegion (1 / 2)) ∩
            (CuspCentralHomology.BaseCover.innerRegion) ⊆
          (CuspCentralHomology.BaseCover.innerRegion))
  intro x y hxy
  have hi :
    SingularMayerVietoris.singularHomologyMap i 0 x =
      SingularMayerVietoris.singularHomologyMap i 0 y := by
    have h := congrArg Prod.snd hxy
    simp only [SingularMayerVietoris.leftHomologyMap_apply, neg_inj] at h
    change
      SingularMayerVietoris.singularHomologyMap i 0 x =
        SingularMayerVietoris.singularHomologyMap i 0 y at h
    exact h
  apply
    (PeriodTorusHigherHomology.connectedHomologyZeroEquiv
        (CuspCentralHomology.BaseCover.overlapRegion (1 / 2))).injective
  have h :=
    congrArg
      (PeriodTorusHigherHomology.connectedHomologyZeroEquiv
        (CuspCentralHomology.BaseCover.innerRegion))
      hi
  exact
    (PeriodTorusHigherHomology.connectedHomologyZeroEquiv_natural i x).symm.trans
      (h.trans (PeriodTorusHigherHomology.connectedHomologyZeroEquiv_natural i y))

private theorem CuspCentralHomology.BaseCover.halfCoverRightHomologyOne_surjective :
    Function.Surjective
      (SingularMayerVietoris.rightHomologyMap (CuspCentralHomology.BaseCover.outerRegion (1 / 2))
        (CuspCentralHomology.BaseCover.innerRegion) 1) := by
  let hU := outerRegion_isOpen (1 / 2)
  let hV := innerRegion_isOpen
  let hc := outerRegion_union_innerRegion (1 / 2) (by norm_num)
  intro x
  have hz :
    SingularMayerVietoris.connectingHomomorphism
        (CuspCentralHomology.BaseCover.outerRegion (1 / 2))
        (CuspCentralHomology.BaseCover.innerRegion) hU hV hc 0 x =
      0 := by
    apply halfCoverLeftHomologyZero_injective
    have h :=
      LinearMap.congr_fun
        (SingularMayerVietoris.connectingHomomorphism_comp_left
          (CuspCentralHomology.BaseCover.outerRegion (1 / 2))
          (CuspCentralHomology.BaseCover.innerRegion) hU hV hc 0)
        x
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply, map_zero] using h
  have hm :
    x ∈
      LinearMap.ker
        (SingularMayerVietoris.connectingHomomorphism
          (CuspCentralHomology.BaseCover.outerRegion (1 / 2))
          (CuspCentralHomology.BaseCover.innerRegion) hU hV hc 0) :=
    hz
  rw [←
    SingularMayerVietoris.exact_at_ambient (CuspCentralHomology.BaseCover.outerRegion (1 / 2))
      (CuspCentralHomology.BaseCover.innerRegion) hU hV hc 0] at hm
  exact hm

private theorem CuspCentralHomology.BaseCover.thetaBaseMap_homology_one_surjective :
    Function.Surjective
      (SingularMayerVietoris.singularHomologyMap CuspCentralHomology.thetaBaseMap 1) := by
  let :
    Subsingleton
      (SingularMayerVietoris.SingularHomology (CuspCentralHomology.BaseCover.innerRegion) 1) :=
    PeriodTorusHigherHomology.contractible_homology_subsingleton
      (CuspCentralHomology.BaseCover.innerRegion) 1 (by decide)
  let e := outerRegionThetaHomotopyEquiv (1 / 2) (by norm_num) (by norm_num)
  let E := PeriodTorusHigherHomology.homotopyEquivHomologyEquiv e 1
  have he :
    (SingularMayerVietoris.subtypeInclusion
            (CuspCentralHomology.BaseCover.outerRegion (1 / 2))).comp
        e.symm.toFun =
      CuspCentralHomology.thetaBaseMap := by
    apply ContinuousMap.ext
    intro q
    rfl
  intro z
  obtain ⟨⟨x, y⟩, hxy⟩ := halfCoverRightHomologyOne_surjective z
  refine ⟨E x, ?_⟩
  rw [← he, PeriodTorusHigherHomology.singularHomologyMap_comp]
  change
    SingularMayerVietoris.singularHomologyMap
        (SingularMayerVietoris.subtypeInclusion
          (CuspCentralHomology.BaseCover.outerRegion (1 / 2)))
        1 (E.symm (E x)) =
      z
  rw [E.symm_apply_apply]
  have hy : y = 0 := Subsingleton.elim _ _
  simpa only [SingularMayerVietoris.rightHomologyMap_apply, hy, map_zero, add_zero] using hxy

private def CuspCentralHomology.BaseCover.thetaForgetSection :
    C(CuspCentralHomology.Theta, CuspCentralHomology.ThreeCircleSuspension) :=
  ⟨fun q => CuspCentralHomology.thetaCharacterCollapse (1, q),
    CuspCentralHomology.thetaCharacterCollapse.continuous.comp
      (continuous_const.prodMk continuous_id)⟩

@[simp]
private theorem
    CuspCentralHomology.BaseCover.thetaForgetCircle_section (q : CuspCentralHomology.Theta) :
    CuspCentralHomology.thetaForgetCircle (thetaForgetSection q) = q :=
  CuspCentralHomology.thetaForgetCircle_collapse 1 q

private theorem CuspCentralHomology.BaseCover.thetaForgetCircle_comp_section :
    CuspCentralHomology.thetaForgetCircle.comp thetaForgetSection =
      ContinuousMap.id CuspCentralHomology.Theta := by
  apply ContinuousMap.ext
  exact thetaForgetCircle_section

private theorem CuspCentralHomology.BaseCover.thetaForgetCircle_homology_surjective (n : ℕ) :
    Function.Surjective
      (SingularMayerVietoris.singularHomologyMap CuspCentralHomology.thetaForgetCircle n) := by
  have h :
    (SingularMayerVietoris.singularHomologyMap CuspCentralHomology.thetaForgetCircle n).comp
        (SingularMayerVietoris.singularHomologyMap thetaForgetSection n) =
      LinearMap.id := by
    rw [← PeriodTorusHigherHomology.singularHomologyMap_comp, thetaForgetCircle_comp_section,
      PeriodTorusHigherHomology.singularHomologyMap_id]
  intro x
  exact
    ⟨SingularMayerVietoris.singularHomologyMap thetaForgetSection n x, LinearMap.congr_fun h x⟩

private theorem CuspCentralHomology.BaseCover.thetaBaseMap_comp_forget_homology_one_injective :
    Function.Injective
      ((SingularMayerVietoris.singularHomologyMap CuspCentralHomology.thetaBaseMap 1).comp
        (SingularMayerVietoris.singularHomologyMap CuspCentralHomology.thetaForgetCircle 1)) := by
  let : Module.Finite ℤ (SingularMayerVietoris.SingularHomology BaseTorus 1) :=
    PeriodTorusHigherHomology.productTorus_homology_finite 2 1
  let e : SingularMayerVietoris.SingularHomology BaseTorus 1 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
    PeriodTorusHigherHomology.productTorusHomologyEquiv 2 1
  let i := CuspCentralHomology.threeCircleSuspensionHomologyOneEquiv.trans e.symm
  exact
    IsNoetherian.injective_of_surjective_of_injective i.toLinearMap _ i.injective
      (thetaBaseMap_homology_one_surjective.comp (thetaForgetCircle_homology_surjective 1))

private theorem CuspCentralHomology.BaseCover.thetaBaseMap_homology_one_injective :
    Function.Injective
      (SingularMayerVietoris.singularHomologyMap CuspCentralHomology.thetaBaseMap 1) := by
  intro x y hxy
  obtain ⟨x', rfl⟩ := thetaForgetCircle_homology_surjective 1 x
  obtain ⟨y', rfl⟩ := thetaForgetCircle_homology_surjective 1 y
  exact
    congrArg (SingularMayerVietoris.singularHomologyMap CuspCentralHomology.thetaForgetCircle 1)
      (thetaBaseMap_comp_forget_homology_one_injective hxy)

private theorem CuspCentralHomology.BaseCover.circleThetaMap_homology_one_eq_zero :
    SingularMayerVietoris.singularHomologyMap circleThetaMap 1 = 0 := by
  have hzero :=
    CuspCentralHomology.singularHomologyMap_eq_zero_of_nullhomotopic
      (CuspCentralHomology.thetaBaseMap.comp circleThetaMap)
      ⟨CuspCentralHomology.baseTorusPoint 0, thetaBaseMap_circleThetaMap_homotopic_const⟩ 1
      (by decide)
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp] at hzero
  apply LinearMap.ext
  intro x
  apply thetaBaseMap_homology_one_injective
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply, map_zero] using
    LinearMap.congr_fun hzero x

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def CuspCentralHomology.productParameterSection {D : Type} [TopologicalSpace D] (X : Type)
    [TopologicalSpace X] (d : D) : C(X, X × D) :=
  (ContinuousMap.id X).prodMk (ContinuousMap.const X d)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem CuspCentralHomology.additiveProductParameter_homology_factor {X D : Type}
    [TopologicalSpace X] [TopologicalSpace D] (β : C(AddCircle (1 : ℝ), D))
    (hβ : SingularMayerVietoris.singularHomologyMap β 1 = 0) (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap (β.prodMap (ContinuousMap.id X)) (n + 1) =
      (SingularMayerVietoris.singularHomologyMap
            ((ContinuousMap.const X (β 0)).prodMk (ContinuousMap.id X)) (n + 1)).comp
        (PeriodTorusHigherHomology.circleProjectionHomology X (n + 1)) := by
  have hs (a : SingularMayerVietoris.SingularHomology X (n + 1)) :
    SingularMayerVietoris.singularHomologyMap (β.prodMap (ContinuousMap.id X)) (n + 1)
        (PeriodTorusHigherHomology.circleSectionHomology X (n + 1) a) =
      SingularMayerVietoris.singularHomologyMap
        ((ContinuousMap.const X (β 0)).prodMk (ContinuousMap.id X)) (n + 1) a := by
    change
      ((SingularMayerVietoris.singularHomologyMap (β.prodMap (ContinuousMap.id X)) (n + 1)).comp
            (SingularMayerVietoris.singularHomologyMap
              (PeriodTorusHigherHomology.CircleTopology.productSection X) (n + 1)))
          a =
        _
    rw [← PeriodTorusHigherHomology.singularHomologyMap_comp]
    rfl
  apply LinearMap.ext
  intro a
  obtain ⟨p, rfl⟩ := (PeriodTorusHigherHomology.circleProductHomologyEquiv X n).symm.surjective a
  have hp :
    PeriodTorusHigherHomology.circleProjectionHomology X (n + 1)
        ((PeriodTorusHigherHomology.circleProductHomologyEquiv X n).symm p) =
      p.1 := by
    change
      (PeriodTorusHigherHomology.circleProductHomologyEquiv X n
            ((PeriodTorusHigherHomology.circleProductHomologyEquiv X n).symm p)).1 =
        p.1
    rw [LinearEquiv.apply_symm_apply]
  rw [LinearMap.comp_apply, hp,
    PeriodTorusHigherHomology.circleProductHomologyEquiv_symm_eq_section_add_cross, map_add, hs,
    parameterMap_positiveCircleCross_eq_zero β hβ, add_zero]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    CuspCentralHomology.productParameter_homology_factor {X D : Type} [TopologicalSpace X]
    [TopologicalSpace D] (α : C(_root_.Circle, D))
    (hα : SingularMayerVietoris.singularHomologyMap α 1 = 0) (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap ((ContinuousMap.id X).prodMap α) (n + 1) =
      (SingularMayerVietoris.singularHomologyMap (productParameterSection X (α 1)) (n + 1)).comp
        (SingularMayerVietoris.singularHomologyMap (ContinuousMap.fst : C(X × _root_.Circle, X))
          (n + 1)) := by
  let β : C(AddCircle (1 : ℝ), D) :=
    α.comp (circleCoordinateHomeomorph.symm : C(AddCircle (1 : ℝ), _root_.Circle))
  have hβ : SingularMayerVietoris.singularHomologyMap β 1 = 0 := by
    rw [show β = α.comp (circleCoordinateHomeomorph.symm : C(AddCircle (1 : ℝ), _root_.Circle))
        from rfl,
      PeriodTorusHigherHomology.singularHomologyMap_comp, hα, LinearMap.zero_comp]
  let g : C(AddCircle (1 : ℝ) × X, X × _root_.Circle) :=
    (circleParametrizedSourceHomeomorph X : C(AddCircle (1 : ℝ) × X, X × _root_.Circle))
  have hmap :
    ((ContinuousMap.id X).prodMap α).comp g =
      (Homeomorph.prodComm D X : C(D × X, X × D)).comp (β.prodMap (ContinuousMap.id X)) :=
    rfl
  have hsection :
    (Homeomorph.prodComm D X : C(D × X, X × D)).comp
        ((ContinuousMap.const X (β 0)).prodMk (ContinuousMap.id X)) =
      productParameterSection X (α 1) := by
    apply ContinuousMap.ext
    intro x
    change (x, α (circleCoordinateHomeomorph.symm 0)) = (x, α 1)
    rw [circleCoordinateHomeomorph_symm_apply, AddCircle.toCircle_zero]
  have hprojection :
    (SingularMayerVietoris.singularHomologyMap (ContinuousMap.fst : C(X × _root_.Circle, X))
            (n + 1)).comp
        (SingularMayerVietoris.singularHomologyMap g (n + 1)) =
      PeriodTorusHigherHomology.circleProjectionHomology X (n + 1) := by
    rw [← PeriodTorusHigherHomology.singularHomologyMap_comp]
    rfl
  have hpre :
    (SingularMayerVietoris.singularHomologyMap ((ContinuousMap.id X).prodMap α) (n + 1)).comp
        (SingularMayerVietoris.singularHomologyMap g (n + 1)) =
      ((SingularMayerVietoris.singularHomologyMap (productParameterSection X (α 1)) (n + 1)).comp
            (SingularMayerVietoris.singularHomologyMap
              (ContinuousMap.fst : C(X × _root_.Circle, X)) (n + 1))).comp
        (SingularMayerVietoris.singularHomologyMap g (n + 1)) := by
    rw [← PeriodTorusHigherHomology.singularHomologyMap_comp, hmap,
      PeriodTorusHigherHomology.singularHomologyMap_comp,
      additiveProductParameter_homology_factor β hβ n, ← LinearMap.comp_assoc, ←
      PeriodTorusHigherHomology.singularHomologyMap_comp, hsection, LinearMap.comp_assoc,
      hprojection]
  apply LinearMap.ext
  intro a
  obtain ⟨b, rfl⟩ :=
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv (circleParametrizedSourceHomeomorph X)
          (n + 1)).surjective
      a
  exact LinearMap.congr_fun hpre b

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem CuspCentralHomology.productParameter_homology_eq_zero_of_projection {X D : Type}
    [TopologicalSpace X] [TopologicalSpace D] (α : C(_root_.Circle, D))
    (hα : SingularMayerVietoris.singularHomologyMap α 1 = 0) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (X × _root_.Circle) (n + 1))
    (ha :
      SingularMayerVietoris.singularHomologyMap (ContinuousMap.fst : C(X × _root_.Circle, X))
          (n + 1) a =
        0) :
    SingularMayerVietoris.singularHomologyMap ((ContinuousMap.id X).prodMap α) (n + 1) a = 0 := by
  rw [productParameter_homology_factor α hα n, LinearMap.comp_apply, ha, map_zero]

private def
    CuspCentralHomology.BaseCover.phaseOverlapHomologyEquiv (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (n : ℕ) :
    SingularMayerVietoris.SingularHomology (phaseOverlapRegion a) n ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (ToricSpace.CompactFibreTorus × Circle) n :=
  PeriodTorusHigherHomology.homotopyEquivHomologyEquiv (phaseOverlapCircleHomotopyEquiv a ha ha1)
    n

private def CuspCentralHomology.BaseCover.phaseOuterHomologyEquiv (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (n : ℕ) :
    SingularMayerVietoris.SingularHomology (phaseOuterRegion a) n ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology
        (ToricSpace.CompactFibreTorus × CuspCentralHomology.Theta) n :=
  PeriodTorusHigherHomology.homotopyEquivHomologyEquiv (phaseOuterThetaHomotopyEquiv a ha ha1) n

private def CuspCentralHomology.BaseCover.phaseInnerHomologyEquiv (n : ℕ) :
    SingularMayerVietoris.SingularHomology (CuspCentralHomology.BaseCover.phaseInnerRegion)
        n ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology ToricSpace.CompactFibreTorus n :=
  PeriodTorusHigherHomology.homotopyEquivHomologyEquiv phaseInnerHomotopyEquiv n

private theorem CuspCentralHomology.BaseCover.phaseInnerProjection_natural (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) (n : ℕ) (z : SingularMayerVietoris.SingularHomology (phaseOverlapRegion a) n) :
    phaseInnerHomologyEquiv n
        (SingularMayerVietoris.singularHomologyMap (phaseOverlapIntoInner a) n z) =
      SingularMayerVietoris.singularHomologyMap
        (ContinuousMap.fst :
          C(ToricSpace.CompactFibreTorus × Circle, ToricSpace.CompactFibreTorus))
        n (phaseOverlapHomologyEquiv a ha ha1 n z) := by
  have hm :=
    congrArg
      (fun f : C((phaseOverlapRegion a), ToricSpace.CompactFibreTorus) =>
        SingularMayerVietoris.singularHomologyMap f n)
      (phaseOverlapIntoInner_phase_map a ha ha1)
  simpa only [PeriodTorusHigherHomology.singularHomologyMap_comp, LinearMap.comp_apply,
    phaseInnerHomologyEquiv, phaseOverlapHomologyEquiv,
    PeriodTorusHigherHomology.homotopyEquivHomologyEquiv_apply] using LinearMap.congr_fun hm z

private theorem CuspCentralHomology.BaseCover.phaseOuterParameter_natural (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) (n : ℕ) (z : SingularMayerVietoris.SingularHomology (phaseOverlapRegion a) n) :
    phaseOuterHomologyEquiv a ha ha1 n
        (SingularMayerVietoris.singularHomologyMap (phaseOverlapIntoOuter a) n z) =
      SingularMayerVietoris.singularHomologyMap
        ((ContinuousMap.id ToricSpace.CompactFibreTorus).prodMap circleThetaMap) n
        (phaseOverlapHomologyEquiv a ha ha1 n z) := by
  have hm :=
    congrArg
      (fun f :
          C((phaseOverlapRegion a), ToricSpace.CompactFibreTorus × CuspCentralHomology.Theta) =>
        SingularMayerVietoris.singularHomologyMap f n)
      (phaseOverlapIntoOuter_theta_map a ha ha1)
  simpa only [PeriodTorusHigherHomology.singularHomologyMap_comp, LinearMap.comp_apply,
    phaseOuterHomologyEquiv, phaseOverlapHomologyEquiv,
    PeriodTorusHigherHomology.homotopyEquivHomologyEquiv_apply] using LinearMap.congr_fun hm z

private theorem
    CuspCentralHomology.BaseCover.phaseOverlapIntoOuter_homology_eq_zero_of_projection (a : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (n : ℕ)
    (z : SingularMayerVietoris.SingularHomology (phaseOverlapRegion a) (n + 1))
    (hz :
      SingularMayerVietoris.singularHomologyMap
          (ContinuousMap.fst :
            C(ToricSpace.CompactFibreTorus × Circle, ToricSpace.CompactFibreTorus))
          (n + 1) (phaseOverlapHomologyEquiv a ha ha1 (n + 1) z) =
        0) :
    SingularMayerVietoris.singularHomologyMap (phaseOverlapIntoOuter a) (n + 1) z = 0 := by
  apply (phaseOuterHomologyEquiv a ha ha1 (n + 1)).injective
  rw [map_zero, phaseOuterParameter_natural]
  exact
    CuspCentralHomology.productParameter_homology_eq_zero_of_projection circleThetaMap
      circleThetaMap_homology_one_eq_zero n _ hz

private theorem CuspCentralHomology.BaseCover.phaseLeftHomologyMap_eq_zero_iff_projection (a : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (n : ℕ)
    (z : SingularMayerVietoris.SingularHomology (phaseOverlapRegion a) (n + 1)) :
    SingularMayerVietoris.leftHomologyMap (phaseOuterRegion a)
          (CuspCentralHomology.BaseCover.phaseInnerRegion) (n + 1) z =
        0 ↔
      SingularMayerVietoris.singularHomologyMap
          (ContinuousMap.fst :
            C(ToricSpace.CompactFibreTorus × Circle, ToricSpace.CompactFibreTorus))
          (n + 1) (phaseOverlapHomologyEquiv a ha ha1 (n + 1) z) =
        0 := by
  have hleft :
    SingularMayerVietoris.leftHomologyMap (phaseOuterRegion a)
        (CuspCentralHomology.BaseCover.phaseInnerRegion) (n + 1) z =
      (SingularMayerVietoris.singularHomologyMap (phaseOverlapIntoOuter a) (n + 1) z,
        -SingularMayerVietoris.singularHomologyMap (phaseOverlapIntoInner a) (n + 1) z) :=
    SingularMayerVietoris.leftHomologyMap_apply (phaseOuterRegion a)
      (CuspCentralHomology.BaseCover.phaseInnerRegion) (n + 1) z
  constructor
  · intro hz
    have hi : SingularMayerVietoris.singularHomologyMap (phaseOverlapIntoInner a) (n + 1) z = 0 :=
      by
      apply neg_eq_zero.mp
      exact congrArg Prod.snd (hleft.symm.trans hz)
    rw [← phaseInnerProjection_natural a ha ha1 (n + 1) z, hi, map_zero]
  · intro hz
    have hi : SingularMayerVietoris.singularHomologyMap (phaseOverlapIntoInner a) (n + 1) z = 0 :=
      by
      apply (phaseInnerHomologyEquiv (n + 1)).injective
      rw [map_zero, phaseInnerProjection_natural a ha ha1 (n + 1) z]
      exact hz
    have ho := phaseOverlapIntoOuter_homology_eq_zero_of_projection a ha ha1 n z hz
    exact hleft.trans (by rw [ho, hi, neg_zero]; rfl)

private theorem
    CuspCentralHomology.BaseCover.phaseConnecting_lift (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (n : ℕ)
    (x : SingularMayerVietoris.SingularHomology (ToricSpace.CompactFibreTorus × Circle) (n + 1))
    (hx :
      SingularMayerVietoris.singularHomologyMap
          (ContinuousMap.fst :
            C(ToricSpace.CompactFibreTorus × Circle, ToricSpace.CompactFibreTorus))
          (n + 1) x =
        0) :
    ∃ y : SingularMayerVietoris.SingularHomology PhaseBase (n + 2),
      phaseOverlapHomologyEquiv a ha ha1 (n + 1)
          (SingularMayerVietoris.connectingHomomorphism (phaseOuterRegion a)
            (CuspCentralHomology.BaseCover.phaseInnerRegion) (phaseOuterRegion_isOpen a)
            phaseInnerRegion_isOpen (phaseOuterRegion_union_phaseInnerRegion a ha1) (n + 1) y) =
        x := by
  let e := phaseOverlapHomologyEquiv a ha ha1 (n + 1)
  have hz :
    e.symm x ∈
      LinearMap.ker
        (SingularMayerVietoris.leftHomologyMap (phaseOuterRegion a)
          (CuspCentralHomology.BaseCover.phaseInnerRegion) (n + 1)) := by
    apply (phaseLeftHomologyMap_eq_zero_iff_projection a ha ha1 n (e.symm x)).mpr
    change
      SingularMayerVietoris.singularHomologyMap
          (ContinuousMap.fst :
            C(ToricSpace.CompactFibreTorus × Circle, ToricSpace.CompactFibreTorus))
          (n + 1) (e (e.symm x)) =
        0
    rw [e.apply_symm_apply]
    exact hx
  have hmem :=
    (SingularMayerVietoris.exact_at_intersection (phaseOuterRegion a)
          (CuspCentralHomology.BaseCover.phaseInnerRegion) (phaseOuterRegion_isOpen a)
          phaseInnerRegion_isOpen (phaseOuterRegion_union_phaseInnerRegion a ha1) (n + 1)).symm.le
      hz
  obtain ⟨y, hy⟩ := hmem
  exact ⟨y, (congrArg e hy).trans (e.apply_symm_apply x)⟩

private abbrev CuspCentralHomology.SpecializationCover.annulusSet (a : ℝ) :
    Set (CuspHoneycombTiling.Plane) :=
  {y | a < CuspCentralHomology.Radial.cellGauge y ∧ CuspCentralHomology.Radial.cellGauge y < 1}

private def CuspCentralHomology.SpecializationCover.sourceOverlapPhaseHomeomorph (a : ℝ) :
    CuspCentralHomology.BaseCover.phaseOverlapRegion a ≃ₜ
      CuspCentralHomology.OverlapPhaseCell a :=
  (CuspCentralHomology.BaseCover.phaseOverlapRegionHomeomorph a).trans
    ((Homeomorph.refl ToricSpace.CompactFibreTorus).prodCongr
      (CuspCentralHomology.BaseCover.annulusOverlapHomeomorph a).symm)

@[simp]
private theorem
    CuspCentralHomology.SpecializationCover.sourceOverlapPhaseHomeomorph_symm_coe (a : ℝ)
    (p : CuspCentralHomology.OverlapPhaseCell a) :
    ((sourceOverlapPhaseHomeomorph a).symm p : CuspCentralHomology.BaseCover.PhaseBase) =
      (p.1, CuspCentralHomology.BaseCover.basePoint (p.2 : (CuspHoneycombTiling.Plane))) :=
  rfl

private theorem
    CuspCentralHomology.SpecializationCover.sourceOverlapCircle_factor (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) :
    (CuspCentralHomology.BaseCover.phaseOverlapCircleHomotopyEquiv a ha ha1).toFun =
      (CuspCentralHomology.Radial.phaseAnnulusHomotopyEquiv ToricSpace.CompactFibreTorus a ha
            ha1).toFun.comp
        (sourceOverlapPhaseHomeomorph a :
          C(CuspCentralHomology.BaseCover.phaseOverlapRegion a,
            CuspCentralHomology.OverlapPhaseCell a)) :=
  rfl

private theorem CuspCentralHomology.SpecializationCover.phaseCellShear_homologyMap
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (s : Set (CuspHoneycombTiling.Plane)) (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap
        (phaseCellShear C₀ s :
          C(ToricSpace.CompactFibreTorus × s, ToricSpace.CompactFibreTorus × s))
        n =
      LinearMap.id := by
  have h := PeriodTorusHigherHomology.homotopy_homologyMap (phaseCellShearHomotopy C₀ s) n
  rw [PeriodTorusHigherHomology.singularHomologyMap_id] at h
  exact h.symm

private def CuspCentralHomology.SpecializationCover.collapseOverlapHomeomorph
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) :
    CuspCentralHomology.BaseCover.phaseOverlapRegion a ≃ₜ
      CuspCentralHomology.overlapRegion C ε hε a :=
  (sourceOverlapPhaseHomeomorph a).trans
    ((phaseCellShear (C 0) (annulusSet a)).trans
      (CuspCentralHomology.overlapPhaseHomeomorph C ε hε hε1 hC hR a))

private theorem CuspCentralHomology.SpecializationCover.collapseOverlapHomeomorph_apply
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ)
    (q : CuspCentralHomology.BaseCover.phaseOverlapRegion a) :
    collapseOverlapHomeomorph C ε hε hε1 hC hR a q = overlapMap C ε hε a q := by
  obtain ⟨p, rfl⟩ := (sourceOverlapPhaseHomeomorph a).symm.surjective q
  apply Subtype.ext
  rw [overlapMap_coe, sourceOverlapPhaseHomeomorph_symm_coe, productCollapse_basePoint]
  change
    (CuspCentralHomology.overlapPhaseHomeomorph C ε hε hε1 hC hR a
          (phaseCellShear (C 0) (annulusSet a)
            (sourceOverlapPhaseHomeomorph a ((sourceOverlapPhaseHomeomorph a).symm p))) :
        CuspRetraction.QuotientCentralFibre C ε) =
      _
  rw [Homeomorph.apply_symm_apply, CuspCentralHomology.overlapPhaseHomeomorph_coe]
  rfl

private theorem CuspCentralHomology.SpecializationCover.overlapMap_phase_coordinates
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ)
    (q : CuspCentralHomology.BaseCover.phaseOverlapRegion a) :
    (CuspCentralHomology.overlapPhaseHomeomorph C ε hε hε1 hC hR a).symm (overlapMap C ε hε a q) =
      phaseCellShear (C 0) (annulusSet a) (sourceOverlapPhaseHomeomorph a q) := by
  apply (CuspCentralHomology.overlapPhaseHomeomorph C ε hε hε1 hC hR a).injective
  rw [Homeomorph.apply_symm_apply]
  exact (collapseOverlapHomeomorph_apply C ε hε hε1 hC hR a q).symm

private theorem CuspCentralHomology.SpecializationCover.targetOverlapCircle_factor
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    (CuspCentralHomology.overlapCircleHomotopyEquiv C ε hε hε1 hC hR a ha ha1).toFun.comp
        (overlapMap C ε hε a) =
      (CuspCentralHomology.Radial.phaseAnnulusHomotopyEquiv ToricSpace.CompactFibreTorus a ha
            ha1).toFun.comp
        ((phaseCellShear (C 0) (annulusSet a) :
              C(ToricSpace.CompactFibreTorus × annulusSet a,
                ToricSpace.CompactFibreTorus × annulusSet a)).comp
          (sourceOverlapPhaseHomeomorph a :
            C(CuspCentralHomology.BaseCover.phaseOverlapRegion a,
              CuspCentralHomology.OverlapPhaseCell a))) := by
  apply ContinuousMap.ext
  intro q
  change
    CuspCentralHomology.Radial.phaseAnnulusHomotopyEquiv ToricSpace.CompactFibreTorus a ha ha1
        ((CuspCentralHomology.overlapPhaseHomeomorph C ε hε hε1 hC hR a).symm
          (overlapMap C ε hε a q)) =
      _
  rw [overlapMap_phase_coordinates]
  rfl

private theorem CuspCentralHomology.SpecializationCover.overlapMap_homology_intertwining
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (n : ℕ) :
    (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
            (CuspCentralHomology.overlapCircleHomotopyEquiv C ε hε hε1 hC hR a ha ha1)
            n).toLinearMap.comp
        (SingularMayerVietoris.singularHomologyMap (overlapMap C ε hε a) n) =
      (CuspCentralHomology.BaseCover.phaseOverlapHomologyEquiv a ha ha1 n).toLinearMap := by
  change
    (SingularMayerVietoris.singularHomologyMap
            (CuspCentralHomology.overlapCircleHomotopyEquiv C ε hε hε1 hC hR a ha ha1).toFun
            n).comp
        (SingularMayerVietoris.singularHomologyMap (overlapMap C ε hε a) n) =
      SingularMayerVietoris.singularHomologyMap
        (CuspCentralHomology.BaseCover.phaseOverlapCircleHomotopyEquiv a ha ha1).toFun n
  rw [← PeriodTorusHigherHomology.singularHomologyMap_comp, targetOverlapCircle_factor,
    PeriodTorusHigherHomology.singularHomologyMap_comp,
    PeriodTorusHigherHomology.singularHomologyMap_comp, phaseCellShear_homologyMap,
    LinearMap.id_comp, sourceOverlapCircle_factor,
    PeriodTorusHigherHomology.singularHomologyMap_comp]

private theorem CuspCentralHomology.SpecializationCover.overlapMap_homology_coordinates
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (n : ℕ)
    (x :
      SingularMayerVietoris.SingularHomology (CuspCentralHomology.BaseCover.phaseOverlapRegion a)
        n) :
    PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
        (CuspCentralHomology.overlapCircleHomotopyEquiv C ε hε hε1 hC hR a ha ha1) n
        (SingularMayerVietoris.singularHomologyMap (overlapMap C ε hε a) n x) =
      CuspCentralHomology.BaseCover.phaseOverlapHomologyEquiv a ha ha1 n x :=
  LinearMap.congr_fun (overlapMap_homology_intertwining C ε hε hε1 hC hR a ha ha1 n) x

private theorem CuspCentralHomology.productCollapse_homology_three_add_surjective
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (n : ℕ) :
    Function.Surjective
      (SingularMayerVietoris.singularHomologyMap (CuspSpecialization.productCollapse C ε hε)
        (n + 3)) := by
  let a : ℝ := 1 / 2
  have ha : 0 ≤ a := by norm_num [a]
  have ha1 : a < 1 := by norm_num [a]
  let U := outerRegion C ε hε a
  let V := innerRegion C ε hε
  let hU := outerRegion_isOpen C ε hε hε1 hC hR a
  let hV := innerRegion_isOpen C ε hε hε1 hC hR
  let hc := outerRegion_union_innerRegion C ε hε a ha1
  let δT := SingularMayerVietoris.connectingHomomorphism U V hU hV hc (n + 2)
  let δS :=
    SingularMayerVietoris.connectingHomomorphism (BaseCover.phaseOuterRegion a)
      BaseCover.phaseInnerRegion (BaseCover.phaseOuterRegion_isOpen a)
      BaseCover.phaseInnerRegion_isOpen (BaseCover.phaseOuterRegion_union_phaseInnerRegion a ha1)
      (n + 2)
  let eT := middleOverlapHomologyEquiv C ε hε hε1 hC hR a ha ha1 (n + 2)
  let : Subsingleton (SingularMayerVietoris.SingularHomology U (n + 3)) :=
    outerRegion_homology_subsingleton C ε hε hε1 hC hR a ha ha1 n
  let : Subsingleton (SingularMayerVietoris.SingularHomology V (n + 3)) :=
    innerRegion_homology_subsingleton C ε hε hε1 hC hR n
  have hδT : Function.Injective δT := coverConnecting_injective_of_vanishing U V hU hV hc (n + 2)
  intro b
  have hk : δT b ∈ LinearMap.ker (SingularMayerVietoris.leftHomologyMap U V (n + 2)) := by
    change SingularMayerVietoris.leftHomologyMap U V (n + 2) (δT b) = 0
    have h :=
      LinearMap.congr_fun
        (SingularMayerVietoris.connectingHomomorphism_comp_left U V hU hV hc (n + 2)) b
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using h
  have hx :
    SingularMayerVietoris.singularHomologyMap
        (ContinuousMap.fst :
          C(ToricSpace.CompactFibreTorus × Circle, ToricSpace.CompactFibreTorus))
        (n + 2) (eT (δT b)) =
      0 :=
    (middleLeftHomology_mem_ker_iff C ε hε hε1 hC hR a ha ha1 (n + 1) (δT b)).mp hk
  obtain ⟨s, hs⟩ := BaseCover.phaseConnecting_lift a ha ha1 (n + 1) (eT (δT b)) hx
  refine ⟨s, hδT (eT.injective ?_)⟩
  have hnat :
    SingularMayerVietoris.singularHomologyMap (SpecializationCover.overlapMap C ε hε a) (n + 2)
        (δS s) =
      δT
        (SingularMayerVietoris.singularHomologyMap (CuspSpecialization.productCollapse C ε hε)
          (n + 3) s) :=
    productCollapse_connecting_naturality C ε hε hε1 hC hR a ha1 (n + 2) s
  calc
    eT
          (δT
            (SingularMayerVietoris.singularHomologyMap (CuspSpecialization.productCollapse C ε hε)
              (n + 3) s)) =
        eT
          (SingularMayerVietoris.singularHomologyMap (SpecializationCover.overlapMap C ε hε a)
            (n + 2) (δS s)) :=
      congrArg eT hnat.symm
    _ = BaseCover.phaseOverlapHomologyEquiv a ha ha1 (n + 2) (δS s) :=
      (SpecializationCover.overlapMap_homology_coordinates C ε hε hε1 hC hR a ha ha1 (n + 2)
        (δS s))
    _ = eT (δT b) := hs

private theorem CuspCentralHomology.productCollapse_homology_three_add_surjective_of_holomorphic
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (n : ℕ) :
    Function.Surjective
      (SingularMayerVietoris.singularHomologyMap (CuspSpecialization.productCollapse C r hr)
        (n + 3)) := by
  obtain ⟨δ, hδ, hδr, hδ1, hRCδ, _hRDδ⟩ :=
    CuspRetraction.exists_common_frozen_radius C hr (fun i j => (hC i j).continuousOn)
  have hCδ (i j) : ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 δ) :=
    (hC i j).mono (Metric.ball_subset_ball hδr.le)
  have he :=
    congrArg (fun f => SingularMayerVietoris.singularHomologyMap f (n + 3))
      (centralRadiusHomeomorph_comp_productCollapse C r δ hδr.le hC hδ)
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp] at he
  rw [← he]
  exact
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv
          (centralRadiusHomeomorph C r δ hδr.le hC hδ) (n + 3)).surjective.comp
      (productCollapse_homology_three_add_surjective C δ hδ hδ1 hCδ hRCδ n)

private theorem CuspCentralHomology.productCollapse_homologyThree_surjective_of_holomorphic
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Function.Surjective
      (SingularMayerVietoris.singularHomologyMap (CuspSpecialization.productCollapse C r hr) 3) :=
  productCollapse_homology_three_add_surjective_of_holomorphic C r hr hC 0

private theorem CuspCentralHomology.productCollapse_homologyFour_surjective_of_holomorphic
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Function.Surjective
      (SingularMayerVietoris.singularHomologyMap (CuspSpecialization.productCollapse C r hr) 4) :=
  productCollapse_homology_three_add_surjective_of_holomorphic C r hr hC 1

private theorem CuspSpecialization.torusDifference_three_exterior
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) 3) :
    PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv
        (CuspCoinvariants.torusDifference 3 a) =
      CuspCoinvariants.exteriorCubeDifference
        (PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv a) := by
  change
    PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv
        (SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap M₀) 3
            a -
          a) =
      exteriorPower.map 3 M₀.mulVecLin
          (PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv a) -
        PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv a
  rw [map_sub, PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv_matrix]

private theorem CuspSpecialization.markedCollapse_homologyThree_surjective
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε)) :
    Function.Surjective (SingularMayerVietoris.singularHomologyMap (markedCollapse C ε hε) 3) :=
  markedCollapse_homology_surjective_of_product C ε hε 3
    (CuspCentralHomology.productCollapse_homologyThree_surjective_of_holomorphic C ε hε hC)

private theorem
    CuspSpecialization.markedCollapse_homologyThree_kernel (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε)) :
    LinearMap.ker (SingularMayerVietoris.singularHomologyMap (markedCollapse C ε hε) 3) =
      LinearMap.range (CuspCoinvariants.torusDifference 3) := by
  let := CuspCentralHomology.centralSingularH3_free C ε hε hC
  let := CuspCentralHomology.centralSingularH3_finite C ε hε hC
  exact
    CuspCoinvariants.torusThree_kernel_eq_of_invariant _
      (markedCollapse_homologyThree_surjective C ε hε hC)
      (markedCollapse_homology_invariant C ε hε 3)
      (CuspCentralHomology.centralSingularH3_finrank C ε hε hC)

private theorem CuspSpecialization.markedCollapse_homologyThree_eq_zero_iff
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) 3) :
    SingularMayerVietoris.singularHomologyMap (markedCollapse C ε hε) 3 a = 0 ↔
      ∃ v : PeriodTorusHigherHomologyExterior.latticeExterior 3,
        exteriorPower.map 3 M₀.mulVecLin v - v =
          PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv a := by
  change
    a ∈ LinearMap.ker (SingularMayerVietoris.singularHomologyMap (markedCollapse C ε hε) 3) ↔
      PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv a ∈
        LinearMap.range CuspCoinvariants.exteriorCubeDifference
  rw [markedCollapse_homologyThree_kernel C ε hε hC]
  exact
    CuspCoinvariants.mem_range_iff_of_intertwines
      PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv
      (CuspCoinvariants.torusDifference 3) CuspCoinvariants.exteriorCubeDifference
      torusDifference_three_exterior a

private theorem CuspSpecialization.markedCollapse_homologyZero_augmentation
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) 0) :
    CuspCentralHomology.centralSingularH0Equiv C r hr
        (SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) 0 a) =
      PeriodTorusHigherHomology.connectedHomologyZeroEquiv
        (PeriodTorusHigherHomology.ProductTorus 4) a :=
  CuspCentralHomology.centralSingularH0Equiv_natural C r hr (markedCollapse C r hr) a

private theorem CuspSpecialization.markedCollapse_homologyZero_bijective
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) :
    Function.Bijective (SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) 0) := by
  constructor
  · intro a b hab
    apply
      (PeriodTorusHigherHomology.connectedHomologyZeroEquiv
          (PeriodTorusHigherHomology.ProductTorus 4)).injective
    rw [← markedCollapse_homologyZero_augmentation C r hr a, ←
      markedCollapse_homologyZero_augmentation C r hr b, hab]
  · intro b
    obtain ⟨a, ha⟩ :=
      (PeriodTorusHigherHomology.connectedHomologyZeroEquiv
            (PeriodTorusHigherHomology.ProductTorus 4)).surjective
        (CuspCentralHomology.centralSingularH0Equiv C r hr b)
    refine ⟨a, ?_⟩
    apply (CuspCentralHomology.centralSingularH0Equiv C r hr).injective
    rw [markedCollapse_homologyZero_augmentation]
    exact ha

private theorem
    CuspSpecialization.markedCollapse_homologyZero_kernel (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) :
    LinearMap.ker (SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) 0) = ⊥ :=
  LinearMap.ker_eq_bot.mpr (markedCollapse_homologyZero_bijective C r hr).injective

private theorem
    CuspSpecialization.markedMonodromy_homologyZero (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) :
    SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap M₀) 0 =
      LinearMap.id := by
  apply LinearMap.ext
  intro a
  apply (markedCollapse_homologyZero_bijective C r hr).injective
  exact markedCollapse_homology_invariant C r hr 0 a

private theorem CuspSpecialization.markedMonodromy_homologyZero_variation_zero
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) :
    SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap M₀) 0 -
        LinearMap.id =
      0 := by rw [markedMonodromy_homologyZero C r hr, sub_self]

private theorem CuspSpecialization.markedMonodromy_homologyZero_variation_range
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) :
    LinearMap.range
        (SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap M₀)
            0 -
          LinearMap.id) =
      ⊥ := by rw [markedMonodromy_homologyZero_variation_zero C r hr, LinearMap.range_zero]

private theorem CuspSpecialization.markedCollapse_homologyZero_kernel_eq_variation
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) :
    LinearMap.ker (SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) 0) =
      LinearMap.range
        (SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap M₀)
            0 -
          LinearMap.id) := by
  rw [markedCollapse_homologyZero_kernel, markedMonodromy_homologyZero_variation_range C r hr]

private theorem CuspSpecialization.markedCollapse_homologyFour_surjective
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Function.Surjective (SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) 4) :=
  markedCollapse_homology_surjective_of_product C r hr 4
    (CuspCentralHomology.productCollapse_homologyFour_surjective_of_holomorphic C r hr hC)

private theorem CuspSpecialization.markedCollapse_homologyFour_bijective
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Function.Bijective (SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) 4) := by
  let := PeriodTorusHigherHomology.productTorus_homology_free 4 4
  let := PeriodTorusHigherHomology.productTorus_homology_finite 4 4
  let := CuspCentralHomology.centralSingularH4_free C r hr hC
  let := CuspCentralHomology.centralSingularH4_finite C r hr hC
  apply
    OrzechProperty.bijective_of_surjective_of_finrank_le
      (SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) 4)
      (markedCollapse_homologyFour_surjective C r hr hC)
  rw [PeriodTorusHigherHomology.productTorus_homology_finrank,
    CuspCentralHomology.centralSingularH4_finrank C r hr hC]
  simp

private theorem
    CuspSpecialization.markedCollapse_homologyFour_kernel (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    LinearMap.ker (SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) 4) = ⊥ :=
  LinearMap.ker_eq_bot.mpr (markedCollapse_homologyFour_bijective C r hr hC).injective

private theorem
    CuspSpecialization.markedMonodromy_homologyFour (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap M₀) 4 =
      LinearMap.id := by
  apply LinearMap.ext
  intro a
  apply (markedCollapse_homologyFour_bijective C r hr hC).injective
  exact markedCollapse_homology_invariant C r hr 4 a

private theorem CuspSpecialization.markedMonodromy_homologyFour_variation_zero
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap M₀) 4 -
        LinearMap.id =
      0 := by rw [markedMonodromy_homologyFour C r hr hC, sub_self]

private theorem CuspSpecialization.markedMonodromy_homologyFour_variation_range
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    LinearMap.range
        (SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap M₀)
            4 -
          LinearMap.id) =
      ⊥ := by rw [markedMonodromy_homologyFour_variation_zero C r hr hC, LinearMap.range_zero]

private theorem CuspSpecialization.markedCollapse_homologyFour_kernel_eq_variation
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    LinearMap.ker (SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) 4) =
      LinearMap.range
        (SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap M₀)
            4 -
          LinearMap.id) := by
  rw [markedCollapse_homologyFour_kernel C r hr hC,
    markedMonodromy_homologyFour_variation_range C r hr hC]

private theorem CuspSpecialization.markedCollapse_homologyHigher_bijective
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (n : ℕ) (hn : 4 < n) :
    Function.Bijective (SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) n) := by
  let := PeriodTorusHigherHomology.productTorus_homology_subsingleton_of_lt hn
  let := CuspCentralHomology.centralSingularHomology_subsingleton_of_four_lt C r hr hC hn
  exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun b => ⟨0, Subsingleton.elim _ b⟩⟩

private theorem
    CuspSpecialization.markedCollapse_homologyHigher_kernel (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (n : ℕ)
    (hn : 4 < n) :
    LinearMap.ker (SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) n) = ⊥ :=
  LinearMap.ker_eq_bot.mpr (markedCollapse_homologyHigher_bijective C r hr hC n hn).injective

private theorem CuspSpecialization.markedCollapse_homologyHigher_kernel_eq_variation
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (n : ℕ) (hn : 4 < n) :
    LinearMap.ker (SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) n) =
      LinearMap.range
        (SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap M₀)
            n -
          LinearMap.id) := by
  let := PeriodTorusHigherHomology.productTorus_homology_subsingleton_of_lt hn
  have hvariation :
    SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap M₀) n -
        LinearMap.id =
      0 := by
    apply LinearMap.ext
    intro a
    exact Subsingleton.elim _ _
  rw [markedCollapse_homologyHigher_kernel C r hr hC n hn, hvariation, LinearMap.range_zero]

private theorem
    CuspSpecialization.markedCollapse_homology_surjective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (n : ℕ) :
    Function.Surjective (SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) n) := by
  rcases n with _ | (_ | (_ | n))
  · exact (markedCollapse_homologyZero_bijective C r hr).surjective
  · exact markedCollapse_homologyOne_surjective C r hr hC
  · exact markedCollapse_homologyTwo_surjective C r hr hC
  · exact
      markedCollapse_homology_surjective_of_product C r hr (n + 3)
        (CuspCentralHomology.productCollapse_homology_three_add_surjective_of_holomorphic C r hr
          hC n)

private theorem CuspSpecialization.markedCollapse_homology_kernel (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (n : ℕ) :
    LinearMap.ker (SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) n) =
      LinearMap.range
        (SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap M₀)
            n -
          LinearMap.id) := by
  rcases n with _ | (_ | (_ | (_ | (_ | n))))
  · exact markedCollapse_homologyZero_kernel_eq_variation C r hr
  · simpa only [CuspCoinvariants.torusDifference] using
      markedCollapse_homologyOne_kernel C r hr hC
  · simpa only [CuspCoinvariants.torusDifference] using
      markedCollapse_homologyTwo_kernel C r hr hC
  · simpa only [CuspCoinvariants.torusDifference] using
      markedCollapse_homologyThree_kernel C r hr hC
  · exact markedCollapse_homologyFour_kernel_eq_variation C r hr hC
  · exact markedCollapse_homologyHigher_kernel_eq_variation C r hr hC (n + 5) (by omega)

private theorem
    CuspSpecialization.markedCollapse_homology_eq_zero_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) n) :
    SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) n a = 0 ↔
      ∃ b : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) n,
        SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap M₀) n
              b -
            b =
          a := by
  change
    a ∈ LinearMap.ker (SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) n) ↔ _
  rw [markedCollapse_homology_kernel C r hr hC n]
  rfl

private theorem
    CuspSpecialization.markedSpecialization_homology_map (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) {X : Type} [TopologicalSpace X]
    (E : PeriodTorusHigherHomology.ProductTorus 4 ≃ₜ X)
    (f : C(X, CuspRetraction.QuotientCentralFibre C r))
    (h :
      (markedCollapse C r hr).Homotopic
        (f.comp (E : C(PeriodTorusHigherHomology.ProductTorus 4, X))))
    (n : ℕ) (a : SingularMayerVietoris.SingularHomology X n) :
    SingularMayerVietoris.singularHomologyMap f n a =
      SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) n
        ((PeriodTorusHigherHomology.homeomorphHomologyEquiv E n).symm a) := by
  have heq := PeriodTorusHigherHomology.homotopic_homologyMap h n
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp] at heq
  have ha :=
    LinearMap.congr_fun heq ((PeriodTorusHigherHomology.homeomorphHomologyEquiv E n).symm a)
  change
    SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) n
        ((PeriodTorusHigherHomology.homeomorphHomologyEquiv E n).symm a) =
      SingularMayerVietoris.singularHomologyMap f n
        (PeriodTorusHigherHomology.homeomorphHomologyEquiv E n
          ((PeriodTorusHigherHomology.homeomorphHomologyEquiv E n).symm a)) at ha
  rw [LinearEquiv.apply_symm_apply] at ha
  exact ha.symm

private theorem CuspSpecialization.markedSpecialization_homology_surjective
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) {X : Type}
    [TopologicalSpace X] (E : PeriodTorusHigherHomology.ProductTorus 4 ≃ₜ X)
    (f : C(X, CuspRetraction.QuotientCentralFibre C r))
    (h :
      (markedCollapse C r hr).Homotopic
        (f.comp (E : C(PeriodTorusHigherHomology.ProductTorus 4, X))))
    (n : ℕ) : Function.Surjective (SingularMayerVietoris.singularHomologyMap f n) := by
  intro b
  obtain ⟨a, ha⟩ := markedCollapse_homology_surjective C r hr hC n b
  refine ⟨PeriodTorusHigherHomology.homeomorphHomologyEquiv E n a, ?_⟩
  rw [markedSpecialization_homology_map C r hr E f h n, LinearEquiv.symm_apply_apply]
  exact ha

private theorem CuspSpecialization.markedSpecialization_homology_eq_zero_iff
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) {X : Type}
    [TopologicalSpace X] (E : PeriodTorusHigherHomology.ProductTorus 4 ≃ₜ X)
    (f : C(X, CuspRetraction.QuotientCentralFibre C r))
    (h :
      (markedCollapse C r hr).Homotopic
        (f.comp (E : C(PeriodTorusHigherHomology.ProductTorus 4, X))))
    (n : ℕ) (a : SingularMayerVietoris.SingularHomology X n) :
    SingularMayerVietoris.singularHomologyMap f n a = 0 ↔
      ∃ b : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) n,
        SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap M₀) n
              b -
            b =
          (PeriodTorusHigherHomology.homeomorphHomologyEquiv E n).symm a := by
  rw [markedSpecialization_homology_map C r hr E f h n,
    markedCollapse_homology_eq_zero_iff C r hr hC n]

private theorem CuspSpecialization.markedSpecialization_homologyTwo_eq_zero_iff
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) {X : Type}
    [TopologicalSpace X] (E : PeriodTorusHigherHomology.ProductTorus 4 ≃ₜ X)
    (f : C(X, CuspRetraction.QuotientCentralFibre C r))
    (h :
      (markedCollapse C r hr).Homotopic
        (f.comp (E : C(PeriodTorusHigherHomology.ProductTorus 4, X))))
    (a : SingularMayerVietoris.SingularHomology X 2) :
    SingularMayerVietoris.singularHomologyMap f 2 a = 0 ↔
      ∃ v : PeriodTorusHigherHomologyExterior.latticeExterior 2,
        exteriorPower.map 2 M₀.mulVecLin v - v =
          PeriodTorusHigherHomology.coordinateTorusH2ExteriorEquiv
            ((PeriodTorusHigherHomology.homeomorphHomologyEquiv E 2).symm a) := by
  rw [markedSpecialization_homology_map C r hr E f h 2,
    markedCollapse_homologyTwo_eq_zero_iff C r hr hC]

private theorem CuspSpecialization.markedSpecialization_homologyThree_eq_zero_iff
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) {X : Type}
    [TopologicalSpace X] (E : PeriodTorusHigherHomology.ProductTorus 4 ≃ₜ X)
    (f : C(X, CuspRetraction.QuotientCentralFibre C r))
    (h :
      (markedCollapse C r hr).Homotopic
        (f.comp (E : C(PeriodTorusHigherHomology.ProductTorus 4, X))))
    (a : SingularMayerVietoris.SingularHomology X 3) :
    SingularMayerVietoris.singularHomologyMap f 3 a = 0 ↔
      ∃ v : PeriodTorusHigherHomologyExterior.latticeExterior 3,
        exteriorPower.map 3 M₀.mulVecLin v - v =
          PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv
            ((PeriodTorusHigherHomology.homeomorphHomologyEquiv E 3).symm a) := by
  rw [markedSpecialization_homology_map C r hr E f h 3,
    markedCollapse_homologyThree_eq_zero_iff C r hr hC]

private theorem CuspCentralHomology.exists_actual_specialization_homology
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    ∃ (η₀ : ℝ) (_hη₀ : 0 < η₀),
      η₀ < r ∧
        η₀ < 1 ∧
          ∀ (t : ℂ) (ht : t ≠ 0),
            ‖t‖ ≤ η₀ →
              ∃ E :
                PeriodTorusHigherHomology.ProductTorus 4 ≃ₜ
                  CuspControlledRetraction.ActualQuotientFibre C r t,
                ∀ (η : ℝ) (_hη : η ≤ η₀) (htη : ‖t‖ ≤ η) (hηr : η < r),
                  ∃ hc :
                    Continuous
                      (CuspControlledRetraction.prescribedActualFibreCollapse C r hr hηr t ht
                        htη),
                    let f :
                      C(CuspControlledRetraction.ActualQuotientFibre C r t,
                        CuspRetraction.QuotientCentralFibre C r) :=
                      ⟨CuspControlledRetraction.prescribedActualFibreCollapse C r hr hηr t ht htη,
                        hc⟩
                    (CuspSpecialization.markedCollapse C r hr).Homotopic
                        (f.comp
                          (E :
                            C(PeriodTorusHigherHomology.ProductTorus 4,
                              CuspControlledRetraction.ActualQuotientFibre C r t))) ∧
                      (∀ n : ℕ,
                          Function.Surjective (SingularMayerVietoris.singularHomologyMap f n) ∧
                            ∀ a :
                              SingularMayerVietoris.SingularHomology
                                (CuspControlledRetraction.ActualQuotientFibre C r t) n,
                              SingularMayerVietoris.singularHomologyMap f n a = 0 ↔
                                ∃ b :
                                  SingularMayerVietoris.SingularHomology
                                    (PeriodTorusHigherHomology.ProductTorus 4) n,
                                  SingularMayerVietoris.singularHomologyMap
                                        (PeriodTorusHigherHomology.torusMatrixMap M₀) n b -
                                      b =
                                    (PeriodTorusHigherHomology.homeomorphHomologyEquiv E n).symm
                                      a) ∧
                        (∀ a :
                            SingularMayerVietoris.SingularHomology
                              (CuspControlledRetraction.ActualQuotientFibre C r t) 2,
                            SingularMayerVietoris.singularHomologyMap f 2 a = 0 ↔
                              ∃ v : PeriodTorusHigherHomologyExterior.latticeExterior 2,
                                exteriorPower.map 2 M₀.mulVecLin v - v =
                                  PeriodTorusHigherHomology.coordinateTorusH2ExteriorEquiv
                                    ((PeriodTorusHigherHomology.homeomorphHomologyEquiv E 2).symm
                                      a)) ∧
                          (∀ a :
                            SingularMayerVietoris.SingularHomology
                              (CuspControlledRetraction.ActualQuotientFibre C r t) 3,
                            SingularMayerVietoris.singularHomologyMap f 3 a = 0 ↔
                              ∃ v : PeriodTorusHigherHomologyExterior.latticeExterior 3,
                                exteriorPower.map 3 M₀.mulVecLin v - v =
                                  PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv
                                    ((PeriodTorusHigherHomology.homeomorphHomologyEquiv E 3).symm
                                      a)) := by
  obtain ⟨η₀, hη₀, hη₀r, hη₀1, hmodels⟩ :=
    CuspSpecialization.exists_original_marked_specialization_models C r hr hC
  refine ⟨η₀, hη₀, hη₀r, hη₀1, ?_⟩
  intro t ht ht₀
  obtain ⟨E, hE⟩ := hmodels t ht ht₀
  refine ⟨E, ?_⟩
  intro η hη htη hηr
  obtain ⟨hc, hh, _⟩ := hE η hη htη hηr
  let f :
    C(CuspControlledRetraction.ActualQuotientFibre C r t,
      CuspRetraction.QuotientCentralFibre C r) :=
    ⟨CuspControlledRetraction.prescribedActualFibreCollapse C r hr hηr t ht htη, hc⟩
  refine ⟨hc, hh, ?_, ?_, ?_⟩
  · intro n
    exact
      ⟨CuspSpecialization.markedSpecialization_homology_surjective C r hr hC E f hh n,
        CuspSpecialization.markedSpecialization_homology_eq_zero_iff C r hr hC E f hh n⟩
  · exact CuspSpecialization.markedSpecialization_homologyTwo_eq_zero_iff C r hr hC E f hh
  · exact CuspSpecialization.markedSpecialization_homologyThree_eq_zero_iff C r hr hC E f hh

private def CuspCentralHomology.retractionEndpointHomotopy {X A : Type} [TopologicalSpace X]
    [TopologicalSpace A] (i : C(A, X)) (R S : C(X, A)) (hR : R.comp i = ContinuousMap.id A)
    (H : (ContinuousMap.id X).Homotopy (i.comp S)) : R.Homotopy S
    where
  toFun p := R (H p)
  continuous_toFun := R.continuous.comp H.continuous
  map_zero_left x := congrArg R (H.map_zero_left x)
  map_one_left x := (congrArg R (H.map_one_left x)).trans (ContinuousMap.congr_fun hR (S x))

private def
    CuspCentralHomology.actualFibreIntoClosed (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r η : ℝ) (t : ℂ)
    (htη : ‖t‖ ≤ η) :
    C(CuspControlledRetraction.ActualQuotientFibre C r t, CuspRetraction.ClosedQuotient C r η)
    where
  toFun q := ⟨q.1, by rw [q.2]; exact htη⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val

private theorem CuspCentralHomology.exists_controlled_retraction_all_levels
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {r : ℝ} (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    ∃ η₀ : ℝ,
      0 < η₀ ∧
        η₀ < r ∧
          η₀ < 1 ∧
            ∀ (η : ℝ) (hη : 0 < η),
              η ≤ η₀ →
                ∀ (hηr : η < r) (t₀ : ℂ) (ht₀ : t₀ ≠ 0) (ht₀η : ‖t₀‖ ≤ η),
                  ∃ R :
                    C(CuspRetraction.ClosedQuotient C r η,
                      CuspRetraction.QuotientCentralFibre C r),
                    R.comp (CuspRetraction.quotientCentralIntoClosed C r η hη.le) =
                        ContinuousMap.id (CuspRetraction.QuotientCentralFibre C r) ∧
                      ∃ H :
                        (ContinuousMap.id (CuspRetraction.ClosedQuotient C r η)).HomotopyRel
                          ((CuspRetraction.quotientCentralIntoClosed C r η hη.le).comp R)
                          {q : CuspRetraction.ClosedQuotient C r η |
                            CuspQuotient.projection C r q = 0},
                        (∀ s q,
                            ‖CuspQuotient.projection C r (H (s, q))‖ ≤
                              ‖CuspQuotient.projection C r q‖) ∧
                          ∃ hc₀ :
                            Continuous
                              (CuspControlledRetraction.prescribedActualFibreCollapse C r hr hηr
                                t₀ ht₀ ht₀η),
                            R.comp (actualFibreIntoClosed C r η t₀ ht₀η) =
                                ⟨CuspControlledRetraction.prescribedActualFibreCollapse C r hr hηr
                                    t₀ ht₀ ht₀η,
                                  hc₀⟩ ∧
                              ∀ (t : ℂ) (ht : t ≠ 0) (htη : ‖t‖ ≤ η),
                                ∃ hc :
                                  Continuous
                                    (CuspControlledRetraction.prescribedActualFibreCollapse C r hr
                                      hηr t ht htη),
                                  (R.comp (actualFibreIntoClosed C r η t htη)).Homotopic
                                      ⟨CuspControlledRetraction.prescribedActualFibreCollapse C r
                                          hr hηr t ht htη,
                                        hc⟩ ∧
                                    ∀ n,
                                      SingularMayerVietoris.singularHomologyMap
                                          (R.comp (actualFibreIntoClosed C r η t htη)) n =
                                        SingularMayerVietoris.singularHomologyMap
                                          ⟨CuspControlledRetraction.prescribedActualFibreCollapse
                                              C r hr hηr t ht htη,
                                            hc⟩
                                          n := by
  obtain ⟨η₀, hη₀, hη₀r, hη₀1, hret⟩ :=
    CuspControlledRetraction.exists_controlled_actual_fibre_retraction C hr hC
  refine ⟨η₀, hη₀, hη₀r, hη₀1, ?_⟩
  intro η hη hηη₀ hηr t₀ ht₀ ht₀η
  obtain ⟨R, hR, H, hmono, hendpoint⟩ := hret η hη hηη₀ t₀ ht₀ ht₀η
  obtain ⟨hc₀, he₀, _hrep₀⟩ := hendpoint hηr
  refine ⟨R, hR, H, hmono, hc₀, ?_, ?_⟩
  · apply ContinuousMap.ext
    intro q
    exact he₀ q
  · intro t ht htη
    obtain ⟨S, _hS, HS, _hmonoS, hendpointS⟩ := hret η hη hηη₀ t ht htη
    obtain ⟨hc, he, _hrep⟩ := hendpointS hηr
    have hemap :
      S.comp (actualFibreIntoClosed C r η t htη) =
        (⟨CuspControlledRetraction.prescribedActualFibreCollapse C r hr hηr t ht htη, hc⟩ :
          C(CuspControlledRetraction.ActualQuotientFibre C r t,
            CuspRetraction.QuotientCentralFibre C r)) := by
      apply ContinuousMap.ext
      intro q
      exact he q
    let K :=
      retractionEndpointHomotopy (CuspRetraction.quotientCentralIntoClosed C r η hη.le) R S hR
        HS.toHomotopy
    have hk :
      (R.comp (actualFibreIntoClosed C r η t htη)).Homotopic
        ⟨CuspControlledRetraction.prescribedActualFibreCollapse C r hr hηr t ht htη, hc⟩ :=
      ⟨(K.comp (ContinuousMap.Homotopy.refl (actualFibreIntoClosed C r η t htη))).cast rfl hemap⟩
    exact ⟨hc, hk, fun n => PeriodTorusHigherHomology.homotopic_homologyMap hk n⟩

end Mathoverflow1973

end
