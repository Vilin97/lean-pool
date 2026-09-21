/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Recognition.Smale9
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.Lattice.Core1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology2
import all LeanPool.HopfProblem.HomologyTheory.FirstHurewicz1
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology4
import all LeanPool.HopfProblem.Foundations.Core3
import all LeanPool.HopfProblem.HomologyTheory.FirstHurewicz3
import all LeanPool.HopfProblem.Elliptic.Core1
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods1
import all LeanPool.HopfProblem.Pi1.MappingTorus
import all LeanPool.HopfProblem.Pi1.ThreefoldOverlapMappingTorus1
import all LeanPool.HopfProblem.Elliptic.Core2
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods2
import all LeanPool.HopfProblem.Threefold.SpecialPeriods4
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology6
import all LeanPool.HopfProblem.PeriodFamily.Core2
import all LeanPool.HopfProblem.Threefold.SpecialPeriods6
import all LeanPool.HopfProblem.Elliptic.Core3
import all LeanPool.HopfProblem.HomologyOfX.ThreefoldGluing1
import all LeanPool.HopfProblem.Uniformization.TriangleUniformizationGluing
import all LeanPool.HopfProblem.Threefold.SpecialPeriods7
import all LeanPool.HopfProblem.Threefold.SpecialPeriods8
import all LeanPool.HopfProblem.Pi1.FundamentalGroupVanKampen2
import all LeanPool.HopfProblem.Recognition.Smale9

/-!
# Hopf problem: pi 1 · mapping torus homology

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

attribute [local instance] SpecialPeriods.Threefold.specialRegularFamilyChartedSpace
    SpecialPeriods.Threefold.specialEllipticPieceChartedSpace
    SpecialPeriods.EllipticFilling.specialFullFillingChartedSpace in
private theorem
    ThreefoldOverlapMappingTorus.Elliptic.puncturedPieceToRegular_elliptic (j : Elliptic.Kind)
    (x : ThreefoldOverlapMappingTorus.PuncturedPiece (Option.some j)) :
    ThreefoldOverlapMappingTorus.puncturedPieceToRegular (Option.some j) x =
      SpecialPeriods.Threefold.specialEllipticOverlap j x.val := by
  apply (SpecialPeriods.Threefold.inclusion_openEmbedding Option.none).injective
  have hx : x.val ∈ (SpecialPeriods.Threefold.specialEllipticOverlap j).source := by
    rw [SpecialPeriods.Threefold.specialEllipticOverlap_source]
    exact x.property
  refine
    (ThreefoldOverlapMappingTorus.puncturedPieceToRegular_inclusion (Option.some j) x).trans ?_
  change
    SpecialPeriods.Threefold.gluingData.inclusion (Option.some (Option.some j)) x.val =
      SpecialPeriods.Threefold.gluingData.inclusion Option.none
        (SpecialPeriods.Threefold.specialEllipticOverlap j x.val)
  exact
    (SpecialPeriods.Threefold.gluingData.inclusion_eq_iff (Option.some (Option.some j))
          Option.none _ _).mpr
      ⟨hx, rfl⟩

private def
    ThreefoldOverlapMappingTorus.timeShift {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) (θ : ℝ) :
    C(MappingTorus.Torus f, MappingTorus.Torus f)
    where
  toFun :=
    Quotient.lift (fun p : ℝ × X => MappingTorus.mk f (p.1 + θ, p.2))
      (by
        rintro p q ⟨k, rfl⟩
        simpa only [MappingTorus.deck, add_assoc, add_left_comm, add_comm] using
          (MappingTorus.mk_deck f k (p.1 + θ, p.2)).symm)
  continuous_toFun :=
    ((MappingTorus.mk_continuous f).comp
          ((continuous_fst.add continuous_const).prodMk continuous_snd)).quotient_lift
      _

@[simp]
private theorem
    ThreefoldOverlapMappingTorus.timeShift_mk {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X)
    (θ t : ℝ) (x : X) : timeShift f θ (MappingTorus.mk f (t, x)) = MappingTorus.mk f (t + θ, x) :=
  rfl

@[simp]
private theorem
    ThreefoldOverlapMappingTorus.timeShift_zero {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X)
    (x : MappingTorus.Torus f) : timeShift f 0 x = x := by
  obtain ⟨⟨t, u⟩, rfl⟩ := MappingTorus.mk_surjective f x
  simp only [timeShift_mk, add_zero]

private theorem
    ThreefoldOverlapMappingTorus.timeShift_jointly_continuous {X : Type*} [TopologicalSpace X]
    (f : X ≃ₜ X) : Continuous (fun p : ℝ × MappingTorus.Torus f => timeShift f p.1 p.2) := by
  have hq : IsOpenQuotientMap (MappingTorus.mk f) :=
    ⟨MappingTorus.mk_surjective f, MappingTorus.mk_continuous f, MappingTorus.mk_open f⟩
  apply (IsOpenQuotientMap.id.prodMap hq).continuous_comp_iff.mp
  change Continuous (fun p : ℝ × (ℝ × X) => MappingTorus.mk f (p.2.1 + p.1, p.2.2))
  exact
    (MappingTorus.mk_continuous f).comp
      (((continuous_fst.comp continuous_snd).add continuous_fst).prodMk
        (continuous_snd.comp continuous_snd))

private def
    ThreefoldOverlapMappingTorus.Elliptic.boundaryInclusionAt (j : Elliptic.Kind) (v : Lattice)
    (hv : Elliptic.AdmissibleTwist j v) (r : ℝ)
    (a : ThreefoldOverlapMappingTorus.Radius j.order r) (θ : ℝ) :
    C(Boundary j v, PuncturedFilling j v hv r) :=
  ⟨fun x =>
    (puncturedProductHomeomorph j v hv r).symm
      (a, ThreefoldOverlapMappingTorus.timeShift (Elliptic.flatTorusAffine j v) θ x),
    (puncturedProductHomeomorph j v hv r).symm.continuous.comp
      (continuous_const.prodMk
        (ThreefoldOverlapMappingTorus.timeShift (Elliptic.flatTorusAffine j v) θ).continuous)⟩

@[simp]
private theorem ThreefoldOverlapMappingTorus.Elliptic.boundaryInclusionAt_mk (j : Elliptic.Kind)
    (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) (r : ℝ)
    (a : ThreefoldOverlapMappingTorus.Radius j.order r) (θ t : ℝ) (x : RealTorus₄) :
    boundaryInclusionAt j v hv r a θ (MappingTorus.mk (Elliptic.flatTorusAffine j v) (t, x)) =
      polarQuotient j v hv r
        (a, ((((t + θ) / j.order : ℝ) : ThreefoldOverlapMappingTorus.Circle), x)) := by
  change
    (puncturedProductHomeomorph j v hv r).symm
        (a,
          ThreefoldOverlapMappingTorus.timeShift (Elliptic.flatTorusAffine j v) θ
            (MappingTorus.mk _ (t, x))) =
      _
  rw [ThreefoldOverlapMappingTorus.timeShift_mk, puncturedProductHomeomorph_symm_mk]

private def ThreefoldOverlapMappingTorus.Elliptic.boundaryRadiusPhaseHomotopy (j : Elliptic.Kind)
    (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) (r : ℝ)
    (a b : ThreefoldOverlapMappingTorus.Radius j.order r) (θ : ℝ) :
    (boundaryInclusion j v hv r a).Homotopy (boundaryInclusionAt j v hv r b θ)
    where
  toFun
    p :=
    (puncturedProductHomeomorph j v hv r).symm
      (ThreefoldOverlapMappingTorus.radiusSegment a b p.1,
        ThreefoldOverlapMappingTorus.timeShift (Elliptic.flatTorusAffine j v) ((p.1 : ℝ) * θ) p.2)
  continuous_toFun :=
    (puncturedProductHomeomorph j v hv r).symm.continuous.comp
      (((ThreefoldOverlapMappingTorus.radiusSegment_continuous a).comp
            (continuous_fst.prodMk continuous_const)).prodMk
        ((ThreefoldOverlapMappingTorus.timeShift_jointly_continuous
              (Elliptic.flatTorusAffine j v)).comp
          (((continuous_subtype_val.comp continuous_fst).mul continuous_const).prodMk
            continuous_snd)))
  map_zero_left
    x := by
    change
      (puncturedProductHomeomorph j v hv r).symm
          (ThreefoldOverlapMappingTorus.radiusSegment a b 0,
            ThreefoldOverlapMappingTorus.timeShift (Elliptic.flatTorusAffine j v)
              ((0 : unitInterval) * θ) x) =
        (puncturedProductHomeomorph j v hv r).symm (a, x)
    simp
  map_one_left
    x := by
    change
      (puncturedProductHomeomorph j v hv r).symm
          (ThreefoldOverlapMappingTorus.radiusSegment a b 1,
            ThreefoldOverlapMappingTorus.timeShift (Elliptic.flatTorusAffine j v)
              ((1 : unitInterval) * θ) x) =
        (puncturedProductHomeomorph j v hv r).symm
          (b, ThreefoldOverlapMappingTorus.timeShift (Elliptic.flatTorusAffine j v) θ x)
    simp

private def ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryInclusionAt (j : Elliptic.Kind)
    (a :
      ThreefoldOverlapMappingTorus.Radius j.order
        (SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j)))
    (θ : ℝ) : C(SpecialBoundary j, ThreefoldOverlapMappingTorus.PuncturedPiece (Option.some j)) :=
  ((specialPuncturedHomeomorph j).symm : C(_, _)).comp
    (boundaryInclusionAt j j.twist (Elliptic.mainTwist_admissible j)
      (SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j)) a θ)

private def
    ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryRadiusPhaseHomotopy (j : Elliptic.Kind)
    (a :
      ThreefoldOverlapMappingTorus.Radius j.order
        (SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j)))
    (θ : ℝ) : (specialBoundaryInclusion j).Homotopy (specialBoundaryInclusionAt j a θ) :=
  (ContinuousMap.Homotopy.refl
        ((specialPuncturedHomeomorph j).symm :
          C(PuncturedFilling j j.twist (Elliptic.mainTwist_admissible j)
              (SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j)),
            ThreefoldOverlapMappingTorus.PuncturedPiece (Option.some j)))).comp
    (boundaryRadiusPhaseHomotopy j j.twist (Elliptic.mainTwist_admissible j)
      (SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j)) (specialRootRadius j) a
      θ)

private theorem
    ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryInclusionAt_mk (j : Elliptic.Kind)
    (a :
      ThreefoldOverlapMappingTorus.Radius j.order
        (SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j)))
    (θ : ℝ) (t : ℝ) (x : RealTorus₄) :
    ((specialBoundaryInclusionAt j a θ
              (MappingTorus.mk (Elliptic.flatTorusAffine j j.twist) (t, x))).val :
          SpecialPeriods.Threefold.SpecialEllipticPiece j).val =
      (SpecialPeriods.EllipticFilling.specialLocalData j).quotient j.twist
        (Elliptic.mainTwist_admissible j)
        (ThreefoldOverlapMappingTorus.root j.order
            (SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j)) a
            (((t + θ) / j.order : ℝ) : ThreefoldOverlapMappingTorus.Circle),
          x) := by
  change
    (((specialPuncturedHomeomorph j).symm
              (boundaryInclusionAt j j.twist (Elliptic.mainTwist_admissible j)
                (SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j)) a θ
                (MappingTorus.mk _ (t, x)))).val :
          SpecialPeriods.Threefold.SpecialEllipticPiece j).val =
      _
  rw [boundaryInclusionAt_mk]
  rfl

private def
    ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryToRegularFamilyAt (j : Elliptic.Kind)
    (a :
      ThreefoldOverlapMappingTorus.Radius j.order
        (SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j)))
    (θ : ℝ) : C(SpecialBoundary j, SpecialPeriods.Threefold.SpecialRegularFamily) :=
  (ThreefoldOverlapMappingTorus.puncturedPieceToRegular (Option.some j)).comp
    (specialBoundaryInclusionAt j a θ)

private theorem ThreefoldOverlapMappingTorus.Elliptic.boundaryToRegularFamily_homotopic_at
    (j : Elliptic.Kind)
    (a :
      ThreefoldOverlapMappingTorus.Radius j.order
        (SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j)))
    (θ : ℝ) :
    (ThreefoldOverlapMappingTorus.boundaryToRegularFamily (Option.some j)).Homotopic
      (specialBoundaryToRegularFamilyAt j a θ) := by
  change
    ((ThreefoldOverlapMappingTorus.puncturedPieceToRegular (Option.some j)).comp
          (specialBoundaryInclusion j)).Homotopic
      _
  exact
    ⟨(ContinuousMap.Homotopy.refl
            (ThreefoldOverlapMappingTorus.puncturedPieceToRegular (Option.some j))).comp
        (specialBoundaryRadiusPhaseHomotopy j a θ)⟩

private theorem
    ThreefoldOverlapMappingTorus.Elliptic.boundaryRegularHomologyMap_at (j : Elliptic.Kind)
    (a :
      ThreefoldOverlapMappingTorus.Radius j.order
        (SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j)))
    (θ : ℝ) (n : ℕ) :
    ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap (Option.some j) n =
      SingularMayerVietoris.singularHomologyMap (specialBoundaryToRegularFamilyAt j a θ) n :=
  PeriodTorusHigherHomology.homotopic_homologyMap (boundaryToRegularFamily_homotopic_at j a θ) n

private def MappingTorusHomology.Covering.lowerSection {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (k : ℕ) : C(X, ↥(MappingTorus.HomologyCover.U f ∩ MappingTorus.HomologyCover.V f))
    where
  toFun
    x :=
    (MappingTorus.HomologyCover.intersectionHomeomorph f).symm
      (Sum.inl (⟨(1 / 4 : ℝ), by norm_num⟩, (f ^ k) x))
  continuous_toFun :=
    (MappingTorus.HomologyCover.intersectionHomeomorph f).symm.continuous.comp
      (continuous_inl.comp (continuous_const.prodMk (f ^ k).continuous))

private def MappingTorusHomology.Covering.upperSection {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (k : ℕ) : C(X, ↥(MappingTorus.HomologyCover.U f ∩ MappingTorus.HomologyCover.V f))
    where
  toFun
    x :=
    (MappingTorus.HomologyCover.intersectionHomeomorph f).symm
      (Sum.inr (⟨(3 / 4 : ℝ), by norm_num⟩, (f ^ k) x))
  continuous_toFun :=
    (MappingTorus.HomologyCover.intersectionHomeomorph f).symm.continuous.comp
      (continuous_inr.comp (continuous_const.prodMk (f ^ k).continuous))

@[simp]
private theorem MappingTorusHomology.Covering.lowerSection_val {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (k : ℕ) (x : X) :
    (lowerSection f k x : MappingTorus.Torus f) = MappingTorus.mk f (1 / 4, (f ^ k) x) :=
  MappingTorus.HomologyCover.intersectionHomeomorph_symm_inl_coe f _

@[simp]
private theorem MappingTorusHomology.Covering.upperSection_val {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (k : ℕ) (x : X) :
    (upperSection f k x : MappingTorus.Torus f) = MappingTorus.mk f (3 / 4, (f ^ k) x) :=
  MappingTorus.HomologyCover.intersectionHomeomorph_symm_inr_coe f _

private def MappingTorusHomology.Covering.uTime (t : unitInterval) : Set.Ioo (0 : ℝ) 1 :=
  ⟨(1 / 4 : ℝ) + (t : ℝ) / 2, by constructor <;> linarith [t.property.1, t.property.2]⟩

private theorem MappingTorusHomology.Covering.uTime_continuous : Continuous uTime :=
  (continuous_const.add (continuous_subtype_val.div_const 2)).subtype_mk _

private def
    MappingTorusHomology.Covering.vTime (t : unitInterval) : Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) :=
  ⟨-(1 / 4 : ℝ) + (t : ℝ) / 2, by constructor <;> linarith [t.property.1, t.property.2]⟩

private theorem MappingTorusHomology.Covering.vTime_continuous : Continuous vTime :=
  (continuous_const.add (continuous_subtype_val.div_const 2)).subtype_mk _

private def
    MappingTorusHomology.Covering.uStrip {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) (k : ℕ) :
    C(unitInterval × X, MappingTorus.HomologyCover.U f)
    where
  toFun p := (MappingTorus.HomologyCover.chartU f).symm (uTime p.1, (f ^ k) p.2)
  continuous_toFun :=
    (MappingTorus.HomologyCover.chartU f).symm.continuous.comp
      ((uTime_continuous.comp continuous_fst).prodMk ((f ^ k).continuous.comp continuous_snd))

private def
    MappingTorusHomology.Covering.vStrip {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) (k : ℕ) :
    C(unitInterval × X, MappingTorus.HomologyCover.V f)
    where
  toFun p := (MappingTorus.HomologyCover.chartV f).symm (vTime p.1, (f ^ (k + 1)) p.2)
  continuous_toFun :=
    (MappingTorus.HomologyCover.chartV f).symm.continuous.comp
      ((vTime_continuous.comp continuous_fst).prodMk
        ((f ^ (k + 1)).continuous.comp continuous_snd))

@[simp]
private theorem
    MappingTorusHomology.Covering.uStrip_val {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (k : ℕ) (p : unitInterval × X) :
    (uStrip f k p : MappingTorus.Torus f) =
      MappingTorus.mk f ((1 / 4 : ℝ) + (p.1 : ℝ) / 2, (f ^ k) p.2) :=
  MappingTorus.HomologyCover.chartU_symm_coe f _

@[simp]
private theorem
    MappingTorusHomology.Covering.vStrip_val {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (k : ℕ) (p : unitInterval × X) :
    (vStrip f k p : MappingTorus.Torus f) =
      MappingTorus.mk f (-(1 / 4 : ℝ) + (p.1 : ℝ) / 2, (f ^ (k + 1)) p.2) :=
  MappingTorus.HomologyCover.chartV_symm_coe f _

private theorem
    MappingTorusHomology.Covering.uStrip_zero {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (k : ℕ) :
    (uStrip f k).comp (PeriodTorusHigherHomology.crossInsertLeft (0 : unitInterval)) =
      (MappingTorus.HomologyCover.intersectionToU f).comp (lowerSection f k) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change (uStrip f k (0, x) : MappingTorus.Torus f) = (lowerSection f k x : MappingTorus.Torus f)
  rw [uStrip_val, lowerSection_val]
  simp

private theorem
    MappingTorusHomology.Covering.uStrip_one {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (k : ℕ) :
    (uStrip f k).comp (PeriodTorusHigherHomology.crossInsertLeft (1 : unitInterval)) =
      (MappingTorus.HomologyCover.intersectionToU f).comp (upperSection f k) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change (uStrip f k (1, x) : MappingTorus.Torus f) = (upperSection f k x : MappingTorus.Torus f)
  rw [uStrip_val, upperSection_val]
  norm_num

private theorem
    MappingTorusHomology.Covering.vStrip_zero {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (k : ℕ) :
    (vStrip f k).comp (PeriodTorusHigherHomology.crossInsertLeft (0 : unitInterval)) =
      (MappingTorus.HomologyCover.intersectionToV f).comp (upperSection f k) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change (vStrip f k (0, x) : MappingTorus.Torus f) = (upperSection f k x : MappingTorus.Torus f)
  rw [vStrip_val, upperSection_val]
  have hpow : (f ^ (k + 1)) x = f ((f ^ k) x) := by rw [pow_succ', Homeomorph.mul_apply]
  rw [hpow]
  convert MappingTorus.mk_sub_one f (3 / 4) ((f ^ k) x) using 1
  norm_num

private theorem
    MappingTorusHomology.Covering.vStrip_one {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (k : ℕ) :
    (vStrip f k).comp (PeriodTorusHigherHomology.crossInsertLeft (1 : unitInterval)) =
      (MappingTorus.HomologyCover.intersectionToV f).comp (lowerSection f (k + 1)) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change
    (vStrip f k (1, x) : MappingTorus.Torus f) = (lowerSection f (k + 1) x : MappingTorus.Torus f)
  rw [vStrip_val, lowerSection_val]
  norm_num

private theorem MappingTorusHomology.Covering.lowerSection_period {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (m : ℕ) (hf : f ^ m = 1) : lowerSection f m = lowerSection f 0 := by
  apply ContinuousMap.ext
  intro x
  change
    (MappingTorus.HomologyCover.intersectionHomeomorph f).symm (Sum.inl (_, (f ^ m) x)) =
      (MappingTorus.HomologyCover.intersectionHomeomorph f).symm (Sum.inl (_, (f ^ 0) x))
  rw [hf, pow_zero]

private theorem MappingTorusHomology.Covering.lowerSection_component {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (k : ℕ) :
    (MappingTorus.HomologyCover.intersectionHomotopyEquiv f).toFun.comp (lowerSection f k) =
      (⟨Sum.inl, continuous_inl⟩ : C(X, X ⊕ X)).comp ((f ^ k : X ≃ₜ X) : C(X, X)) := by
  apply ContinuousMap.ext
  intro x
  exact MappingTorus.HomologyCover.intersectionHomotopyEquiv_inl f _

private theorem MappingTorusHomology.Covering.upperSection_component {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (k : ℕ) :
    (MappingTorus.HomologyCover.intersectionHomotopyEquiv f).toFun.comp (upperSection f k) =
      (⟨Sum.inr, continuous_inr⟩ : C(X, X ⊕ X)).comp ((f ^ k : X ≃ₜ X) : C(X, X)) := by
  apply ContinuousMap.ext
  intro x
  exact MappingTorus.HomologyCover.intersectionHomotopyEquiv_inr f _

private theorem MappingTorusHomology.Covering.lowerSection_homology_coordinates {X : Type}
    [TopologicalSpace X] (f : X ≃ₜ X) (k n : ℕ) (a : SingularMayerVietoris.SingularHomology X n) :
    MappingTorusHomology.intersectionHomologyEquiv f n
        (SingularMayerVietoris.singularHomologyMap (lowerSection f k) n a) =
      (SingularMayerVietoris.singularHomologyMap ((f ^ k : X ≃ₜ X) : C(X, X)) n a, 0) := by
  rw [MappingTorusHomology.intersectionHomologyEquiv_apply, ← LinearMap.comp_apply, ←
    PeriodTorusHigherHomology.singularHomologyMap_comp, lowerSection_component,
    PeriodTorusHigherHomology.singularHomologyMap_comp]
  exact PeriodTorusHigherHomology.sumHomologyEquiv_inl X X n _

private theorem MappingTorusHomology.Covering.upperSection_homology_coordinates {X : Type}
    [TopologicalSpace X] (f : X ≃ₜ X) (k n : ℕ) (a : SingularMayerVietoris.SingularHomology X n) :
    MappingTorusHomology.intersectionHomologyEquiv f n
        (SingularMayerVietoris.singularHomologyMap (upperSection f k) n a) =
      (0, SingularMayerVietoris.singularHomologyMap ((f ^ k : X ≃ₜ X) : C(X, X)) n a) := by
  rw [MappingTorusHomology.intersectionHomologyEquiv_apply, ← LinearMap.comp_apply, ←
    PeriodTorusHigherHomology.singularHomologyMap_comp, upperSection_component,
    PeriodTorusHigherHomology.singularHomologyMap_comp]
  exact PeriodTorusHigherHomology.sumHomologyEquiv_inr X X n _

private theorem
    MappingTorusHomology.Covering.mk_add_int {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (t : ℝ) (k : ℤ) (x : X) :
    MappingTorus.mk f (t + (k : ℝ), x) = MappingTorus.mk f (t, (f ^ k) x) := by
  apply (MappingTorus.mk_eq_mk_iff f _ _).mpr
  exact ⟨-k, by simp, by simp⟩

private def
    MappingTorusHomology.Covering.productCover {X : Type} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) :
    C(MappingTorus.Circle × X, MappingTorus.Torus B.symm)
    where
  toFun :=
    Elliptic.HigherHomology.MappingTorusQuotient.mappingTorusHomeomorph m B hB ∘
      Elliptic.HigherHomology.MappingTorusQuotient.project m B hB
  continuous_toFun :=
    (Elliptic.HigherHomology.MappingTorusQuotient.mappingTorusHomeomorph m B hB).continuous.comp
      (Elliptic.HigherHomology.MappingTorusQuotient.project_continuous m B hB)

private theorem
    MappingTorusHomology.Covering.productCover_real_apply {X : Type} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) (t : ℝ)
    (x : X) :
    productCover m B hB ((t : MappingTorus.Circle), x) = MappingTorus.mk B.symm (t * m, x) :=
  Elliptic.HigherHomology.MappingTorusQuotient.mappingTorusHomeomorph_project m B hB t x

@[simp]
private theorem
    MappingTorusHomology.Covering.productCover_zero_apply {X : Type} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) (x : X) :
    productCover m B hB (0, x) = MappingTorus.mk B.symm (0, x) := by
  simpa only [AddCircle.coe_zero, MulZeroClass.zero_mul] using productCover_real_apply m B hB 0 x

@[simp]
private theorem MappingTorusHomology.Covering.productCover_comp_productSection {X : Type}
    [TopologicalSpace X] [CompactSpace X] [T2Space X] (m : ℕ) [NeZero m] (B : X ≃ₜ X)
    (hB : B ^ m = 1) :
    (productCover m B hB).comp (PeriodTorusHigherHomology.CircleTopology.productSection X) =
      MappingTorus.HomologyCover.fibreInclusion B.symm := by
  apply ContinuousMap.ext
  intro x
  exact productCover_zero_apply m B hB x

private abbrev MappingTorusHomology.Covering.productCoverHomology {X : Type} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) (n : ℕ) :
    SingularMayerVietoris.SingularHomology (MappingTorus.Circle × X) n →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (MappingTorus.Torus B.symm) n :=
  SingularMayerVietoris.singularHomologyMap (productCover m B hB) n

private theorem MappingTorusHomology.Covering.productCoverHomology_comp_circleSection {X : Type}
    [TopologicalSpace X] [CompactSpace X] [T2Space X] (m : ℕ) [NeZero m] (B : X ≃ₜ X)
    (hB : B ^ m = 1) (n : ℕ) :
    (productCoverHomology m B hB n).comp (PeriodTorusHigherHomology.circleSectionHomology X n) =
      MappingTorusHomology.fibreHomologyMap B.symm n := by
  change
    (SingularMayerVietoris.singularHomologyMap (productCover m B hB) n).comp
        (SingularMayerVietoris.singularHomologyMap
          (PeriodTorusHigherHomology.CircleTopology.productSection X) n) =
      _
  rw [← PeriodTorusHigherHomology.singularHomologyMap_comp, productCover_comp_productSection]

@[simp]
private theorem MappingTorusHomology.Covering.productCoverHomology_circleSection_apply {X : Type}
    [TopologicalSpace X] [CompactSpace X] [T2Space X] (m : ℕ) [NeZero m] (B : X ≃ₜ X)
    (hB : B ^ m = 1) (n : ℕ) (a : SingularMayerVietoris.SingularHomology X n) :
    productCoverHomology m B hB n (PeriodTorusHigherHomology.circleSectionHomology X n a) =
      MappingTorusHomology.fibreHomologyMap B.symm n a :=
  LinearMap.congr_fun (productCoverHomology_comp_circleSection m B hB n) a

private theorem MappingTorusHomology.Covering.wangBoundary_productCover_circleSection {X : Type}
    [TopologicalSpace X] [CompactSpace X] [T2Space X] (m : ℕ) [NeZero m] (B : X ≃ₜ X)
    (hB : B ^ m = 1) (n : ℕ) :
    ((MappingTorusHomology.wangBoundary B.symm n).comp (productCoverHomology m B hB (n + 1))).comp
        (PeriodTorusHigherHomology.circleSectionHomology X (n + 1)) =
      0 := by
  ext a
  change
    MappingTorusHomology.wangBoundary B.symm n
        (productCoverHomology m B hB (n + 1)
          (PeriodTorusHigherHomology.circleSectionHomology X (n + 1) a)) =
      0
  rw [productCoverHomology_circleSection_apply]
  have ha :
    MappingTorusHomology.fibreHomologyMap B.symm (n + 1) a ∈
      LinearMap.range (MappingTorusHomology.fibreHomologyMap B.symm (n + 1)) :=
    ⟨a, rfl⟩
  rw [MappingTorusHomology.wang_exact_at_mappingTorus] at ha
  exact ha

private theorem
    MappingTorusHomology.Covering.wangBoundary_productCover_circleSection_apply {X : Type}
    [TopologicalSpace X] [CompactSpace X] [T2Space X] (m : ℕ) [NeZero m] (B : X ≃ₜ X)
    (hB : B ^ m = 1) (n : ℕ) (a : SingularMayerVietoris.SingularHomology X (n + 1)) :
    MappingTorusHomology.wangBoundary B.symm n
        (productCoverHomology m B hB (n + 1)
          (PeriodTorusHigherHomology.circleSectionHomology X (n + 1) a)) =
      0 :=
  LinearMap.congr_fun (wangBoundary_productCover_circleSection m B hB n) a

private def MappingTorusHomology.Covering.affineRealArc (a b : ℝ) : Path a b
    where
  toFun t := a + (b - a) * (t : ℝ)
  continuous_toFun := continuous_const.add (continuous_const.mul continuous_subtype_val)
  source' := by simp
  target' := by simp

private def MappingTorusHomology.Covering.affineCircleArc (a b : ℝ) :
    Path (a : (PeriodTorusHigherHomology.CircleTopology.Circle))
      (b : (PeriodTorusHigherHomology.CircleTopology.Circle)) :=
  (affineRealArc a b).map (AddCircle.continuous_mk' (1 : ℝ))

@[simp]
private theorem MappingTorusHomology.Covering.affineCircleArc_apply (a b : ℝ) (t : unitInterval) :
    affineCircleArc a b t =
      ((a + (b - a) * (t : ℝ) : ℝ) : (PeriodTorusHigherHomology.CircleTopology.Circle)) :=
  rfl

@[simp]
private theorem MappingTorusHomology.Covering.affineCircleArc_self (a : ℝ) :
    affineCircleArc a a = Path.refl (a : (PeriodTorusHigherHomology.CircleTopology.Circle)) := by
  apply Path.ext
  funext t
  simp

private theorem MappingTorusHomology.Covering.affineCircleArc_trans_homotopic (a b c : ℝ) :
    ((affineCircleArc a b).trans (affineCircleArc b c)).Homotopic (affineCircleArc a c) := by
  have h :=
    SimplyConnectedSpace.paths_homotopic ((affineRealArc a b).trans (affineRealArc b c))
      (affineRealArc a c)
  have hmap :=
    h.map
      (⟨fun x : ℝ => (x : (PeriodTorusHigherHomology.CircleTopology.Circle)),
          AddCircle.continuous_mk' (1 : ℝ)⟩ :
        C(ℝ, (PeriodTorusHigherHomology.CircleTopology.Circle)))
  rw [Path.map_trans] at hmap
  exact hmap

private theorem MappingTorusHomology.Covering.pathClass_affineCircleArc_add (a b c : ℝ) :
    FirstHurewicz.pathClass (affineCircleArc a b) +
        FirstHurewicz.pathClass (affineCircleArc b c) =
      FirstHurewicz.pathClass (affineCircleArc a c) := by
  rw [← FirstHurewicz.pathClass_trans]
  exact FirstHurewicz.pathClass_homotopic (affineCircleArc_trans_homotopic a b c)

private def MappingTorusHomology.Covering.quarterLift (m k : ℕ) : ℝ :=
  ((k : ℝ) + 1 / 4) / m

private def MappingTorusHomology.Covering.threeQuarterLift (m k : ℕ) : ℝ :=
  ((k : ℝ) + 3 / 4) / m

private def MappingTorusHomology.Covering.uPath (m k : ℕ) :
    Path (quarterLift m k : (PeriodTorusHigherHomology.CircleTopology.Circle))
      (threeQuarterLift m k : (PeriodTorusHigherHomology.CircleTopology.Circle)) :=
  affineCircleArc (quarterLift m k) (threeQuarterLift m k)

private def MappingTorusHomology.Covering.vPath (m k : ℕ) :
    Path (threeQuarterLift m k : (PeriodTorusHigherHomology.CircleTopology.Circle))
      (quarterLift m (k + 1) : (PeriodTorusHigherHomology.CircleTopology.Circle)) :=
  affineCircleArc (threeQuarterLift m k) (quarterLift m (k + 1))

@[simp]
private theorem MappingTorusHomology.Covering.uPath_apply (m k : ℕ) (t : unitInterval) :
    uPath m k t =
      ((((k : ℝ) + 1 / 4 + (t : ℝ) / 2) / m : ℝ) :
        (PeriodTorusHigherHomology.CircleTopology.Circle)) := by
  change
    (((quarterLift m k + (threeQuarterLift m k - quarterLift m k) * (t : ℝ)) : ℝ) :
        (PeriodTorusHigherHomology.CircleTopology.Circle)) =
      _
  congr 1
  unfold quarterLift threeQuarterLift
  ring

@[simp]
private theorem MappingTorusHomology.Covering.vPath_apply (m k : ℕ) (t : unitInterval) :
    vPath m k t =
      ((((k : ℝ) + 3 / 4 + (t : ℝ) / 2) / m : ℝ) :
        (PeriodTorusHigherHomology.CircleTopology.Circle)) := by
  change
    (((threeQuarterLift m k + (quarterLift m (k + 1) - threeQuarterLift m k) * (t : ℝ)) : ℝ) :
        (PeriodTorusHigherHomology.CircleTopology.Circle)) =
      _
  congr 1
  unfold quarterLift threeQuarterLift
  push_cast
  ring

private theorem MappingTorusHomology.Covering.pathClass_uPath_add_vPath (m k : ℕ) :
    FirstHurewicz.pathClass (uPath m k) + FirstHurewicz.pathClass (vPath m k) =
      FirstHurewicz.pathClass (affineCircleArc (quarterLift m k) (quarterLift m (k + 1))) :=
  pathClass_affineCircleArc_add _ _ _

private theorem MappingTorusHomology.Covering.quarterLift_period (m : ℕ) [NeZero m] :
    quarterLift m m = quarterLift m 0 + 1 := by
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  simp only [quarterLift, Nat.cast_zero, zero_add]
  field_simp
  ring

private theorem MappingTorusHomology.Covering.quarterLift_circle_period (m : ℕ) [NeZero m] :
    (quarterLift m m : (PeriodTorusHigherHomology.CircleTopology.Circle)) =
      (quarterLift m 0 : (PeriodTorusHigherHomology.CircleTopology.Circle)) := by
  rw [quarterLift_period]
  exact AddCircle.coe_add_period (1 : ℝ) _

private theorem MappingTorusHomology.Covering.boundaryOne_arcPrefix (m n : ℕ) :
    FirstHurewicz.boundaryOne (PeriodTorusHigherHomology.CircleTopology.Circle)
        (∑ k ∈ Finset.range n,
          (FirstHurewicz.pathChain (uPath m k) + FirstHurewicz.pathChain (vPath m k))) =
      FirstHurewicz.pointChain
          (quarterLift m n : (PeriodTorusHigherHomology.CircleTopology.Circle)) -
        FirstHurewicz.pointChain
          (quarterLift m 0 : (PeriodTorusHigherHomology.CircleTopology.Circle)) := by
  induction n with
  | zero => simp
  | succ n
    ih =>
    rw [Finset.sum_range_succ, map_add, ih, map_add, FirstHurewicz.boundaryOne_pathChain,
      FirstHurewicz.boundaryOne_pathChain]
    abel

private theorem MappingTorusHomology.Covering.chainClass_arcPrefix (m n : ℕ) :
    FirstHurewicz.chainClass (PeriodTorusHigherHomology.CircleTopology.Circle)
        (∑ k ∈ Finset.range n,
          (FirstHurewicz.pathChain (uPath m k) + FirstHurewicz.pathChain (vPath m k))) =
      FirstHurewicz.pathClass (affineCircleArc (quarterLift m 0) (quarterLift m n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, map_add, ih, map_add]
    change
      FirstHurewicz.pathClass (affineCircleArc (quarterLift m 0) (quarterLift m n)) +
          (FirstHurewicz.pathClass (uPath m n) + FirstHurewicz.pathClass (vPath m n)) =
        _
    rw [pathClass_uPath_add_vPath, pathClass_affineCircleArc_add]

private def MappingTorusHomology.Covering.arcSumChain (m : ℕ) :
    FirstHurewicz.Chains (PeriodTorusHigherHomology.CircleTopology.Circle) 1 :=
  ∑ k ∈ Finset.range m,
    (FirstHurewicz.pathChain (uPath m k) + FirstHurewicz.pathChain (vPath m k))

private theorem MappingTorusHomology.Covering.boundaryOne_arcSumChain (m : ℕ) [NeZero m] :
    FirstHurewicz.boundaryOne (PeriodTorusHigherHomology.CircleTopology.Circle) (arcSumChain m) =
      0 := by rw [arcSumChain, boundaryOne_arcPrefix, quarterLift_circle_period, sub_self]

private def MappingTorusHomology.Covering.arcSumCycle (m : ℕ) [NeZero m] :
    FirstHurewicz.Cycles1 (PeriodTorusHigherHomology.CircleTopology.Circle) :=
  FirstHurewicz.mkCycle1 (PeriodTorusHigherHomology.CircleTopology.Circle) (arcSumChain m)
    (boundaryOne_arcSumChain m)

@[simp]
private theorem MappingTorusHomology.Covering.arcSumCycle_val (m : ℕ) [NeZero m] :
    (arcSumCycle m).1 = arcSumChain m :=
  rfl

private theorem MappingTorusHomology.Covering.chainClass_arcSumChain (m : ℕ) :
    FirstHurewicz.chainClass (PeriodTorusHigherHomology.CircleTopology.Circle) (arcSumChain m) =
      FirstHurewicz.pathClass (affineCircleArc (quarterLift m 0) (quarterLift m m)) :=
  chainClass_arcPrefix m m

private def MappingTorusHomology.Covering.translatedPositiveLoop (a : ℝ) :
    Path (a : (PeriodTorusHigherHomology.CircleTopology.Circle))
      (a : (PeriodTorusHigherHomology.CircleTopology.Circle)) :=
  ((PeriodTorusHigherHomology.CirclePaths.positiveLoop.map
        (PeriodTorusHigherHomology.CirclePaths.circleTranslation a).continuous).cast
    (by simp) (by simp))

@[simp]
private theorem
    MappingTorusHomology.Covering.translatedPositiveLoop_apply (a : ℝ) (t : unitInterval) :
    translatedPositiveLoop a t =
      ((a + (t : ℝ) : ℝ) : (PeriodTorusHigherHomology.CircleTopology.Circle)) := by
  change
    (a : (PeriodTorusHigherHomology.CircleTopology.Circle)) +
        ((t : ℝ) : (PeriodTorusHigherHomology.CircleTopology.Circle)) =
      ((a + (t : ℝ) : ℝ) : (PeriodTorusHigherHomology.CircleTopology.Circle))
  exact (AddCircle.coe_add (1 : ℝ) a (t : ℝ)).symm

private theorem MappingTorusHomology.Covering.pathClass_affineCircleArc_period (a : ℝ) :
    FirstHurewicz.pathClass (affineCircleArc a (a + 1)) =
      FirstHurewicz.pathClass (translatedPositiveLoop a) := by
  have hp :
    (affineCircleArc a (a + 1)).cast rfl (AddCircle.coe_add_period (1 : ℝ) a).symm =
      translatedPositiveLoop a := by
    apply Path.ext
    funext t
    simp only [Path.cast_coe, affineCircleArc_apply, translatedPositiveLoop_apply]
    congr 1
    ring
  rw [← hp, FirstHurewicz.pathClass_cast]

private theorem MappingTorusHomology.Covering.translatedPositiveLoop_class (a : ℝ) :
    FirstHurewicz.loopHomologyClass (translatedPositiveLoop a) =
      FirstHurewicz.loopHomologyClass PeriodTorusHigherHomology.CirclePaths.positiveLoop := by
  have hc :
    FirstHurewicz.loopHomologyClass (translatedPositiveLoop a) =
      FirstHurewicz.loopHomologyClass
        (PeriodTorusHigherHomology.CirclePaths.positiveLoop.map
          (PeriodTorusHigherHomology.CirclePaths.circleTranslation a).continuous) := by
    apply
      FirstHurewicz.homologyToChainClass_injective
        (PeriodTorusHigherHomology.CircleTopology.Circle)
    rw [FirstHurewicz.homologyToChainClass_loopHomologyClass,
      FirstHurewicz.homologyToChainClass_loopHomologyClass]
    rfl
  exact
    hc.trans (PeriodTorusHigherHomology.CirclePaths.loopHomologyClass_map_circleTranslation a _)

private theorem MappingTorusHomology.Covering.arcSumCycle_positiveLoop_class (m : ℕ) [NeZero m] :
    FirstHurewicz.cycleClass (PeriodTorusHigherHomology.CircleTopology.Circle) (arcSumCycle m) =
      FirstHurewicz.loopHomologyClass PeriodTorusHigherHomology.CirclePaths.positiveLoop := by
  rw [← translatedPositiveLoop_class (quarterLift m 0)]
  apply
    FirstHurewicz.homologyToChainClass_injective (PeriodTorusHigherHomology.CircleTopology.Circle)
  rw [FirstHurewicz.homologyToChainClass_cycleClass,
    FirstHurewicz.homologyToChainClass_loopHomologyClass, arcSumCycle_val, chainClass_arcSumChain,
    quarterLift_period, pathClass_affineCircleArc_period]

private def
    MappingTorusHomology.Covering.uCircleMap (m k : ℕ) : C(unitInterval, (MappingTorus.Circle)) :=
  ⟨uPath m k, (uPath m k).continuous⟩

private def
    MappingTorusHomology.Covering.vCircleMap (m k : ℕ) : C(unitInterval, (MappingTorus.Circle)) :=
  ⟨vPath m k, (vPath m k).continuous⟩

private theorem MappingTorusHomology.Covering.uCircleMap_pathChain (m k : ℕ) :
    FirstHurewicz.inducedChain (uCircleMap m k) 1 (FirstHurewicz.pathChain Path.id) =
      FirstHurewicz.pathChain (uPath m k) := by
  rw [FirstHurewicz.inducedChain_pathChain]
  rfl

private theorem MappingTorusHomology.Covering.vCircleMap_pathChain (m k : ℕ) :
    FirstHurewicz.inducedChain (vCircleMap m k) 1 (FirstHurewicz.pathChain Path.id) =
      FirstHurewicz.pathChain (vPath m k) := by
  rw [FirstHurewicz.inducedChain_pathChain]
  rfl

private theorem
    MappingTorusHomology.Covering.productCover_uCircleMap {X : Type} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) (k : ℕ) :
    (productCover m B hB).comp ((uCircleMap m k).prodMap (ContinuousMap.id X)) =
      (MappingTorus.HomologyCover.inclusionU B.symm).comp (uStrip B.symm k) := by
  apply ContinuousMap.ext
  intro p
  change
    productCover m B hB (uPath m k p.1, p.2) = (uStrip B.symm k p : MappingTorus.Torus B.symm)
  rw [uPath_apply, productCover_real_apply, uStrip_val]
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  rw [div_mul_cancel₀ _ hm]
  have ht : (k : ℝ) + 1 / 4 + (p.1 : ℝ) / 2 = (1 / 4 : ℝ) + (p.1 : ℝ) / 2 + ((k : ℤ) : ℝ) := by
    push_cast
    ring
  rw [ht, mk_add_int]
  simp only [zpow_natCast]

private theorem
    MappingTorusHomology.Covering.productCover_vCircleMap {X : Type} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) (k : ℕ) :
    (productCover m B hB).comp ((vCircleMap m k).prodMap (ContinuousMap.id X)) =
      (MappingTorus.HomologyCover.inclusionV B.symm).comp (vStrip B.symm k) := by
  apply ContinuousMap.ext
  intro p
  change
    productCover m B hB (vPath m k p.1, p.2) = (vStrip B.symm k p : MappingTorus.Torus B.symm)
  rw [vPath_apply, productCover_real_apply, vStrip_val]
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  rw [div_mul_cancel₀ _ hm]
  have ht :
    (k : ℝ) + 3 / 4 + (p.1 : ℝ) / 2 = -(1 / 4 : ℝ) + (p.1 : ℝ) / 2 + (((k + 1 : ℕ) : ℤ) : ℝ) := by
    push_cast
    ring
  rw [ht, mk_add_int]
  simp only [zpow_natCast]

private theorem MappingTorusHomology.Covering.uStrip_inclusion_crossProduct {X : Type}
    [TopologicalSpace X] [CompactSpace X] [T2Space X] (m : ℕ) [NeZero m] (B : X ≃ₜ X)
    (hB : B ^ m = 1) (k n : ℕ) (b : FirstHurewicz.Chains X n) :
    FirstHurewicz.inducedChain (MappingTorus.HomologyCover.inclusionU B.symm) (n + 1)
        (FirstHurewicz.inducedChain (uStrip B.symm k) (n + 1)
          (PeriodTorusHigherHomology.crossProductEdge unitInterval X n
            (FirstHurewicz.pathChain Path.id) b)) =
      FirstHurewicz.inducedChain (productCover m B hB) (n + 1)
        (PeriodTorusHigherHomology.crossProductEdge (MappingTorus.Circle) X n
          (FirstHurewicz.pathChain (uPath m k)) b) := by
  have h :=
    congrArg
      (fun F =>
        FirstHurewicz.inducedChain F (n + 1)
          (PeriodTorusHigherHomology.crossProductEdge unitInterval X n
            (FirstHurewicz.pathChain Path.id) b))
      (productCover_uCircleMap m B hB k)
  simp only [FirstHurewicz.inducedChain_comp, LinearMap.comp_apply,
    PeriodTorusHigherHomology.crossProductEdge_natural, FirstHurewicz.inducedChain_id,
    LinearMap.id_apply, uCircleMap_pathChain] at h
  exact h.symm

private theorem MappingTorusHomology.Covering.vStrip_inclusion_crossProduct {X : Type}
    [TopologicalSpace X] [CompactSpace X] [T2Space X] (m : ℕ) [NeZero m] (B : X ≃ₜ X)
    (hB : B ^ m = 1) (k n : ℕ) (b : FirstHurewicz.Chains X n) :
    FirstHurewicz.inducedChain (MappingTorus.HomologyCover.inclusionV B.symm) (n + 1)
        (FirstHurewicz.inducedChain (vStrip B.symm k) (n + 1)
          (PeriodTorusHigherHomology.crossProductEdge unitInterval X n
            (FirstHurewicz.pathChain Path.id) b)) =
      FirstHurewicz.inducedChain (productCover m B hB) (n + 1)
        (PeriodTorusHigherHomology.crossProductEdge (MappingTorus.Circle) X n
          (FirstHurewicz.pathChain (vPath m k)) b) := by
  have h :=
    congrArg
      (fun F =>
        FirstHurewicz.inducedChain F (n + 1)
          (PeriodTorusHigherHomology.crossProductEdge unitInterval X n
            (FirstHurewicz.pathChain Path.id) b))
      (productCover_vCircleMap m B hB k)
  simp only [FirstHurewicz.inducedChain_comp, LinearMap.comp_apply,
    PeriodTorusHigherHomology.crossProductEdge_natural, FirstHurewicz.inducedChain_id,
    LinearMap.id_apply, vCircleMap_pathChain] at h
  exact h.symm

private theorem MappingTorusHomology.Covering.positiveCircleCross_subdivision_cycleClass {X : Type}
    [TopologicalSpace X] (m : ℕ) [NeZero m] (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    PeriodTorusHigherHomology.positiveCircleCross X n
        (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) n b) =
      SingularMayerVietoris.ModuleHomology.cycleClass
        (FirstHurewicz.singularComplex ((MappingTorus.Circle) × X)) (n + 1)
        (PeriodTorusHigherHomology.crossProductCycles (MappingTorus.Circle) X n (arcSumCycle m)
          b) := by
  have h :
    SingularMayerVietoris.ModuleHomology.cycleClass
        (FirstHurewicz.singularComplex (MappingTorus.Circle)) 1 (arcSumCycle m) =
      FirstHurewicz.loopHomologyClass PeriodTorusHigherHomology.CirclePaths.positiveLoop :=
    arcSumCycle_positiveLoop_class m
  change
    PeriodTorusHigherHomology.crossProductHomology (MappingTorus.Circle) X n
        (FirstHurewicz.loopHomologyClass PeriodTorusHigherHomology.CirclePaths.positiveLoop)
        (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) n b) =
      _
  rw [← h]
  exact
    PeriodTorusHigherHomology.crossProductHomology_cycleClass (MappingTorus.Circle) X n
      (arcSumCycle m) b

private def MappingTorusHomology.Covering.monodromyHomologyMonoidHom {X : Type} [TopologicalSpace X]
    (n : ℕ) : (X ≃ₜ X) →* Module.End ℤ (SingularMayerVietoris.SingularHomology X n)
    where
  toFun B := MappingTorusHomology.monodromyHomologyMap B n
  map_one' := PeriodTorusHigherHomology.singularHomologyMap_id X n
  map_mul' B D := PeriodTorusHigherHomology.singularHomologyMap_comp (D : C(X, X)) (B : C(X, X)) n

@[simp]
private theorem
    MappingTorusHomology.Covering.monodromyHomologyMap_pow {X : Type} [TopologicalSpace X]
    (B : X ≃ₜ X) (n k : ℕ) :
    MappingTorusHomology.monodromyHomologyMap (B ^ k) n =
      (MappingTorusHomology.monodromyHomologyMap B n) ^ k :=
  map_pow (monodromyHomologyMonoidHom (X := X) n) B k

private def MappingTorusHomology.Covering.homologyNorm {X : Type} [TopologicalSpace X] (m : ℕ)
    (B : X ≃ₜ X) (n : ℕ) :
    SingularMayerVietoris.SingularHomology X n →ₗ[ℤ] SingularMayerVietoris.SingularHomology X n :=
  ∑ k ∈ Finset.range m, SingularMayerVietoris.singularHomologyMap ((B ^ k : X ≃ₜ X) : C(X, X)) n

@[simp]
private theorem
    MappingTorusHomology.Covering.homologyNorm_apply {X : Type} [TopologicalSpace X] (m : ℕ)
    (B : X ≃ₜ X) (n : ℕ) (a : SingularMayerVietoris.SingularHomology X n) :
    homologyNorm m B n a =
      ∑ k ∈ Finset.range m,
        SingularMayerVietoris.singularHomologyMap ((B ^ k : X ≃ₜ X) : C(X, X)) n a := by
  simp only [homologyNorm, LinearMap.sum_apply]

private theorem
    MappingTorusHomology.Covering.homologyNorm_eq_sum_powers {X : Type} [TopologicalSpace X]
    (m : ℕ) (B : X ≃ₜ X) (n : ℕ) :
    homologyNorm m B n =
      ∑ k ∈ Finset.range m, (MappingTorusHomology.monodromyHomologyMap B n) ^ k := by
  apply Finset.sum_congr rfl
  intro k _
  exact monodromyHomologyMap_pow B n k

private theorem MappingTorusHomology.Covering.sum_range_shift_of_endpoints_mo1973_27356
    {A : Type*} [AddCommGroup A] (F : ℕ → A) (m : ℕ) (hF : F m = F 0) :
    ∑ k ∈ Finset.range m, F (k + 1) = ∑ k ∈ Finset.range m, F k := by
  apply add_right_cancel (b := F 0)
  calc
    (∑ k ∈ Finset.range m, F (k + 1)) + F 0 = ∑ k ∈ Finset.range (m + 1), F k :=
      (Finset.sum_range_succ' F m).symm
    _ = (∑ k ∈ Finset.range m, F k) + F 0 := by rw [Finset.sum_range_succ, hF]

private theorem MappingTorusHomology.Covering.homeomorph_symm_pow_eq {X : Type} [TopologicalSpace X]
    (m : ℕ) (B : X ≃ₜ X) (hB : B ^ m = 1) (k : ℕ) (hk : k ≤ m) : B.symm ^ k = B ^ (m - k) := by
  change B⁻¹ ^ k = B ^ (m - k)
  rw [pow_sub B hk, hB, one_mul, inv_pow]

private theorem
    MappingTorusHomology.Covering.homologyNorm_symm {X : Type} [TopologicalSpace X] (m : ℕ)
    (B : X ≃ₜ X) (n : ℕ) (hB : B ^ m = 1) : homologyNorm m B.symm n = homologyNorm m B n := by
  unfold homologyNorm
  calc
    (∑ k ∈ Finset.range m,
          SingularMayerVietoris.singularHomologyMap ((B.symm ^ k : X ≃ₜ X) : C(X, X)) n) =
        ∑ k ∈ Finset.range m,
          SingularMayerVietoris.singularHomologyMap ((B ^ (m - 1 - k + 1) : X ≃ₜ X) : C(X, X))
            n := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkm : k < m := Finset.mem_range.mp hk
      have hexp : m - k = m - 1 - k + 1 := by omega
      rw [homeomorph_symm_pow_eq m B hB k hkm.le, hexp]
    _ =
        ∑ k ∈ Finset.range m,
          SingularMayerVietoris.singularHomologyMap ((B ^ (k + 1) : X ≃ₜ X) : C(X, X)) n :=
      (Finset.sum_range_reflect
        (fun k => SingularMayerVietoris.singularHomologyMap ((B ^ (k + 1) : X ≃ₜ X) : C(X, X)) n)
        m)
    _ =
        ∑ k ∈ Finset.range m,
          SingularMayerVietoris.singularHomologyMap ((B ^ k : X ≃ₜ X) : C(X, X)) n := by
      apply
        sum_range_shift_of_endpoints_mo1973_27356
          (fun k => SingularMayerVietoris.singularHomologyMap ((B ^ k : X ≃ₜ X) : C(X, X)) n) m
      rw [hB, pow_zero]

private def MappingTorusHomology.Covering.uCrossChain {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (k n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    FirstHurewicz.Chains (MappingTorus.HomologyCover.U f) (n + 1) :=
  FirstHurewicz.inducedChain (uStrip f k) (n + 1)
    (PeriodTorusHigherHomology.crossProductEdge unitInterval X n (FirstHurewicz.pathChain Path.id)
      b.1)

private def MappingTorusHomology.Covering.vCrossChain {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (k n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    FirstHurewicz.Chains (MappingTorus.HomologyCover.V f) (n + 1) :=
  FirstHurewicz.inducedChain (vStrip f k) (n + 1)
    (PeriodTorusHigherHomology.crossProductEdge unitInterval X n (FirstHurewicz.pathChain Path.id)
      b.1)

private theorem MappingTorusHomology.Covering.uCrossChain_boundary {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (k n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    ((FirstHurewicz.singularComplex (MappingTorus.HomologyCover.U f)).d (n + 1) n).hom
        (uCrossChain f k n b) =
      FirstHurewicz.inducedChain (MappingTorus.HomologyCover.intersectionToU f) n
        (FirstHurewicz.inducedChain (upperSection f k) n b.1 -
          FirstHurewicz.inducedChain (lowerSection f k) n b.1) := by
  rw [uCrossChain, ← FirstHurewicz.inducedChain_boundary,
    PeriodTorusHigherHomology.crossProductEdge_path_boundary, map_sub, map_sub]
  congr 1
  · have h := congrArg (fun g => FirstHurewicz.inducedChain g n b.1) (uStrip_one f k)
    simpa only [FirstHurewicz.inducedChain_comp, LinearMap.comp_apply] using h
  · have h := congrArg (fun g => FirstHurewicz.inducedChain g n b.1) (uStrip_zero f k)
    simpa only [FirstHurewicz.inducedChain_comp, LinearMap.comp_apply] using h

private theorem MappingTorusHomology.Covering.vCrossChain_boundary {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (k n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    ((FirstHurewicz.singularComplex (MappingTorus.HomologyCover.V f)).d (n + 1) n).hom
        (vCrossChain f k n b) =
      FirstHurewicz.inducedChain (MappingTorus.HomologyCover.intersectionToV f) n
        (FirstHurewicz.inducedChain (lowerSection f (k + 1)) n b.1 -
          FirstHurewicz.inducedChain (upperSection f k) n b.1) := by
  rw [vCrossChain, ← FirstHurewicz.inducedChain_boundary,
    PeriodTorusHigherHomology.crossProductEdge_path_boundary, map_sub, map_sub]
  congr 1
  · have h := congrArg (fun g => FirstHurewicz.inducedChain g n b.1) (vStrip_one f k)
    simpa only [FirstHurewicz.inducedChain_comp, LinearMap.comp_apply] using h
  · have h := congrArg (fun g => FirstHurewicz.inducedChain g n b.1) (vStrip_zero f k)
    simpa only [FirstHurewicz.inducedChain_comp, LinearMap.comp_apply] using h

private def
    MappingTorusHomology.Covering.uCrossChainSum {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (m n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    FirstHurewicz.Chains (MappingTorus.HomologyCover.U f) (n + 1) :=
  ∑ k ∈ Finset.range m, uCrossChain f k n b

private def
    MappingTorusHomology.Covering.vCrossChainSum {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (m n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    FirstHurewicz.Chains (MappingTorus.HomologyCover.V f) (n + 1) :=
  ∑ k ∈ Finset.range m, vCrossChain f k n b

private def
    MappingTorusHomology.Covering.differenceCycle {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (m n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    SingularMayerVietoris.ModuleHomology.Cycle
      (FirstHurewicz.singularComplex
        (MappingTorus.HomologyCover.U f ∩ MappingTorus.HomologyCover.V f :
          Set (MappingTorus.Torus f)))
      n :=
  ∑ k ∈ Finset.range m,
    (SingularMayerVietoris.ModuleHomology.mapCycles
        (FirstHurewicz.singularChainMap (upperSection f k)) n b -
      SingularMayerVietoris.ModuleHomology.mapCycles
        (FirstHurewicz.singularChainMap (lowerSection f k)) n b)

@[simp]
private theorem MappingTorusHomology.Covering.differenceCycle_val {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (m n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    (differenceCycle f m n b).1 =
      ∑ k ∈ Finset.range m,
        (FirstHurewicz.inducedChain (upperSection f k) n b.1 -
          FirstHurewicz.inducedChain (lowerSection f k) n b.1) := by
  simp only [differenceCycle, Submodule.coe_sum, Submodule.coe_sub,
    SingularMayerVietoris.ModuleHomology.mapCycles_val]

private theorem
    MappingTorusHomology.Covering.lowerSection_chain_sum_shift {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (m : ℕ) (hf : f ^ m = 1) (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    (∑ k ∈ Finset.range m, FirstHurewicz.inducedChain (lowerSection f (k + 1)) n b.1) =
      ∑ k ∈ Finset.range m, FirstHurewicz.inducedChain (lowerSection f k) n b.1 := by
  apply add_right_cancel (b := FirstHurewicz.inducedChain (lowerSection f 0) n b.1)
  calc
    _ = ∑ k ∈ Finset.range (m + 1), FirstHurewicz.inducedChain (lowerSection f k) n b.1 :=
      (Finset.sum_range_succ' (fun k => FirstHurewicz.inducedChain (lowerSection f k) n b.1)
          m).symm
    _ = _ := by rw [Finset.sum_range_succ, lowerSection_period f m hf]

private theorem
    MappingTorusHomology.Covering.uCrossChainSum_boundary {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (m n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    ((FirstHurewicz.singularComplex (MappingTorus.HomologyCover.U f)).d (n + 1) n).hom
        (uCrossChainSum f m n b) =
      FirstHurewicz.inducedChain (MappingTorus.HomologyCover.intersectionToU f) n
        (differenceCycle f m n b).1 := by
  simp only [uCrossChainSum, differenceCycle_val, map_sum, uCrossChain_boundary]

private theorem
    MappingTorusHomology.Covering.vCrossChainSum_boundary {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (m : ℕ) (hf : f ^ m = 1) (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    ((FirstHurewicz.singularComplex (MappingTorus.HomologyCover.V f)).d (n + 1) n).hom
        (vCrossChainSum f m n b) =
      -FirstHurewicz.inducedChain (MappingTorus.HomologyCover.intersectionToV f) n
          (differenceCycle f m n b).1 := by
  calc
    _ =
        FirstHurewicz.inducedChain (MappingTorus.HomologyCover.intersectionToV f) n
          (∑ k ∈ Finset.range m,
            (FirstHurewicz.inducedChain (lowerSection f (k + 1)) n b.1 -
              FirstHurewicz.inducedChain (upperSection f k) n b.1)) := by
      simp only [vCrossChainSum, map_sum, vCrossChain_boundary]
    _ = _ := by
      rw [differenceCycle_val]
      simp only [Finset.sum_sub_distrib]
      rw [lowerSection_chain_sum_shift f m hf]
      simp only [map_sub]
      abel

private theorem MappingTorusHomology.Covering.differenceCycle_class {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (m n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    SingularMayerVietoris.ModuleHomology.cycleClass
        (FirstHurewicz.singularComplex
          (MappingTorus.HomologyCover.U f ∩ MappingTorus.HomologyCover.V f :
            Set (MappingTorus.Torus f)))
        n (differenceCycle f m n b) =
      ∑ k ∈ Finset.range m,
        (SingularMayerVietoris.singularHomologyMap (upperSection f k) n
            (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) n
              b) -
          SingularMayerVietoris.singularHomologyMap (lowerSection f k) n
            (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) n
              b)) := by
  simp only [differenceCycle, map_sum, map_sub,
    ← SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass]

private theorem MappingTorusHomology.Covering.differenceCycle_class_coordinates {X : Type}
    [TopologicalSpace X] (f : X ≃ₜ X) (m n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    MappingTorusHomology.intersectionHomologyEquiv f n
        (SingularMayerVietoris.ModuleHomology.cycleClass
          (FirstHurewicz.singularComplex
            (MappingTorus.HomologyCover.U f ∩ MappingTorus.HomologyCover.V f :
              Set (MappingTorus.Torus f)))
          n (differenceCycle f m n b)) =
      (-homologyNorm m f n
            (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) n
              b),
        homologyNorm m f n
          (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) n
            b)) := by
  rw [differenceCycle_class, map_sum]
  simp only [map_sub, upperSection_homology_coordinates, lowerSection_homology_coordinates,
    Prod.mk_sub_mk, zero_sub, sub_zero, ← prod_mk_sum, Finset.sum_neg_distrib, homologyNorm_apply]

private def
    MappingTorusHomology.Covering.coverSmallCycle {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (m : ℕ) (hf : f ^ m = 1) (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    SingularMayerVietoris.ModuleHomology.Cycle
      (SingularMayerVietoris.smallComplex (MappingTorus.HomologyCover.U f)
        (MappingTorus.HomologyCover.V f))
      (n + 1) :=
  PeriodTorusHigherHomology.twoChainSmallCycle (MappingTorus.HomologyCover.U f)
    (MappingTorus.HomologyCover.V f) n (uCrossChainSum f m n b) (vCrossChainSum f m n b)
    (differenceCycle f m n b) (uCrossChainSum_boundary f m n b)
    (vCrossChainSum_boundary f m hf n b)

private theorem
    MappingTorusHomology.Covering.coverSmallCycle_ambient_val {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (m : ℕ) (hf : f ^ m = 1) (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    (SingularMayerVietoris.ModuleHomology.mapCycles
          (SingularMayerVietoris.smallInclusion (MappingTorus.HomologyCover.U f)
            (MappingTorus.HomologyCover.V f))
          (n + 1) (coverSmallCycle f m hf n b)).1 =
      FirstHurewicz.inducedChain (MappingTorus.HomologyCover.inclusionU f) (n + 1)
          (uCrossChainSum f m n b) +
        FirstHurewicz.inducedChain (MappingTorus.HomologyCover.inclusionV f) (n + 1)
          (vCrossChainSum f m n b) :=
  PeriodTorusHigherHomology.twoChainSmallCycle_ambient_val (MappingTorus.HomologyCover.U f)
    (MappingTorus.HomologyCover.V f) n (uCrossChainSum f m n b) (vCrossChainSum f m n b)
    (differenceCycle f m n b) (uCrossChainSum_boundary f m n b)
    (vCrossChainSum_boundary f m hf n b)

private theorem MappingTorusHomology.Covering.coverSmallCycle_ambient_sum_val {X : Type}
    [TopologicalSpace X] (f : X ≃ₜ X) (m : ℕ) (hf : f ^ m = 1) (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    (SingularMayerVietoris.ModuleHomology.mapCycles
          (SingularMayerVietoris.smallInclusion (MappingTorus.HomologyCover.U f)
            (MappingTorus.HomologyCover.V f))
          (n + 1) (coverSmallCycle f m hf n b)).1 =
      ∑ k ∈ Finset.range m,
        (FirstHurewicz.inducedChain (MappingTorus.HomologyCover.inclusionU f) (n + 1)
            (uCrossChain f k n b) +
          FirstHurewicz.inducedChain (MappingTorus.HomologyCover.inclusionV f) (n + 1)
            (vCrossChain f k n b)) := by
  simp only [coverSmallCycle_ambient_val, uCrossChainSum, vCrossChainSum, map_sum,
    Finset.sum_add_distrib]

private theorem
    MappingTorusHomology.Covering.coverSmallCycle_connecting {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (m : ℕ) (hf : f ^ m = 1) (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    MappingTorusHomology.mayerVietorisConnecting f n
        (SingularMayerVietoris.ModuleHomology.cycleClass
          (FirstHurewicz.singularComplex (MappingTorus.Torus f)) (n + 1)
          (SingularMayerVietoris.ModuleHomology.mapCycles
            (SingularMayerVietoris.smallInclusion (MappingTorus.HomologyCover.U f)
              (MappingTorus.HomologyCover.V f))
            (n + 1) (coverSmallCycle f m hf n b))) =
      SingularMayerVietoris.ModuleHomology.cycleClass
        (FirstHurewicz.singularComplex
          (MappingTorus.HomologyCover.U f ∩ MappingTorus.HomologyCover.V f :
            Set (MappingTorus.Torus f)))
        n (differenceCycle f m n b) :=
  PeriodTorusHigherHomology.connectingHomomorphism_twoChain (MappingTorus.HomologyCover.U f)
    (MappingTorus.HomologyCover.V f) (MappingTorus.HomologyCover.U_open f)
    (MappingTorus.HomologyCover.V_open f) (MappingTorus.HomologyCover.cover f) n
    (uCrossChainSum f m n b) (vCrossChainSum f m n b) (differenceCycle f m n b)
    (uCrossChainSum_boundary f m n b) (vCrossChainSum_boundary f m hf n b)

private theorem MappingTorusHomology.Covering.coverSmallCycle_boundaryCoordinates {X : Type}
    [TopologicalSpace X] (f : X ≃ₜ X) (m : ℕ) (hf : f ^ m = 1) (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    MappingTorusHomology.boundaryCoordinates f n
        (SingularMayerVietoris.ModuleHomology.cycleClass
          (FirstHurewicz.singularComplex (MappingTorus.Torus f)) (n + 1)
          (SingularMayerVietoris.ModuleHomology.mapCycles
            (SingularMayerVietoris.smallInclusion (MappingTorus.HomologyCover.U f)
              (MappingTorus.HomologyCover.V f))
            (n + 1) (coverSmallCycle f m hf n b))) =
      (-homologyNorm m f n
            (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) n
              b),
        homologyNorm m f n
          (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) n
            b)) := by
  rw [MappingTorusHomology.boundaryCoordinates_apply, coverSmallCycle_connecting]
  exact differenceCycle_class_coordinates f m n b

private theorem MappingTorusHomology.Covering.sub_cross_boundary_mem_range_circleSection {X : Type}
    [TopologicalSpace X] (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        ((PeriodTorusHigherHomology.CircleTopology.Circle) × X) (n + 1)) :
    a -
        PeriodTorusHigherHomology.positiveCircleCross X n
          (PeriodTorusHigherHomology.circleBoundary X n a) ∈
      LinearMap.range (PeriodTorusHigherHomology.circleSectionHomology X (n + 1)) := by
  rw [PeriodTorusHigherHomology.circleBoundary_exact]
  change
    PeriodTorusHigherHomology.circleBoundary X n
        (a -
          PeriodTorusHigherHomology.positiveCircleCross X n
            (PeriodTorusHigherHomology.circleBoundary X n a)) =
      0
  rw [map_sub, PeriodTorusHigherHomology.circleBoundary_positiveCircleCross, sub_self]

private theorem
    MappingTorusHomology.Covering.eq_comp_circleBoundary_of_section_cross_apply {X : Type}
    [TopologicalSpace X] {A : Type*} [AddCommGroup A] [Module ℤ A] (n : ℕ)
    (L :
      SingularMayerVietoris.SingularHomology
          ((PeriodTorusHigherHomology.CircleTopology.Circle) × X) (n + 1) →ₗ[ℤ]
        A)
    (N : SingularMayerVietoris.SingularHomology X n →ₗ[ℤ] A)
    (hsec : ∀ b, L (PeriodTorusHigherHomology.circleSectionHomology X (n + 1) b) = 0)
    (hcross : ∀ b, L (PeriodTorusHigherHomology.positiveCircleCross X n b) = N b)
    (a :
      SingularMayerVietoris.SingularHomology
        ((PeriodTorusHigherHomology.CircleTopology.Circle) × X) (n + 1)) :
    L a = N (PeriodTorusHigherHomology.circleBoundary X n a) := by
  obtain ⟨b, hb⟩ := sub_cross_boundary_mem_range_circleSection n a
  have h := hsec b
  rw [hb, map_sub, hcross] at h
  exact sub_eq_zero.mp h

private theorem MappingTorusHomology.Covering.eq_comp_circleBoundary_of_section_cross {X : Type}
    [TopologicalSpace X] {A : Type*} [AddCommGroup A] [Module ℤ A] (n : ℕ)
    (L :
      SingularMayerVietoris.SingularHomology
          ((PeriodTorusHigherHomology.CircleTopology.Circle) × X) (n + 1) →ₗ[ℤ]
        A)
    (N : SingularMayerVietoris.SingularHomology X n →ₗ[ℤ] A)
    (hsec : ∀ b, L (PeriodTorusHigherHomology.circleSectionHomology X (n + 1) b) = 0)
    (hcross : ∀ b, L (PeriodTorusHigherHomology.positiveCircleCross X n b) = N b) :
    L = N.comp (PeriodTorusHigherHomology.circleBoundary X n) := by
  ext a
  exact eq_comp_circleBoundary_of_section_cross_apply n L N hsec hcross a

private theorem MappingTorusHomology.Covering.wangBoundary_productCover_eq_of_cross {X : Type}
    [TopologicalSpace X] [CompactSpace X] [T2Space X] (m : ℕ) [NeZero m] (B : X ≃ₜ X)
    (hB : B ^ m = 1) (n : ℕ)
    (N :
      SingularMayerVietoris.SingularHomology X n →ₗ[ℤ] SingularMayerVietoris.SingularHomology X n)
    (hcross :
      ∀ b,
        MappingTorusHomology.wangBoundary B.symm n
            (productCoverHomology m B hB (n + 1)
              (PeriodTorusHigherHomology.positiveCircleCross X n b)) =
          N b) :
    (MappingTorusHomology.wangBoundary B.symm n).comp (productCoverHomology m B hB (n + 1)) =
      N.comp (PeriodTorusHigherHomology.circleBoundary X n) := by
  apply eq_comp_circleBoundary_of_section_cross n
  · intro b
    exact wangBoundary_productCover_circleSection_apply m B hB n b
  · exact hcross

public
theorem MappingTorusHomology.Covering.inverseMonodromy_period_mo1973_27385 {X : Type}
    [TopologicalSpace X] (m : ℕ) (B : X ≃ₜ X) (h : B ^ m = 1) : B.symm ^ m = 1 := by
  rw [homeomorph_symm_pow_eq m B h m le_rfl, Nat.sub_self, pow_zero]

private theorem MappingTorusHomology.Covering.coverSmallCycle_productCover_eq {X : Type}
    [TopologicalSpace X] [CompactSpace X] [T2Space X] (m : ℕ) [NeZero m] (B : X ≃ₜ X)
    (hB : B ^ m = 1) (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    SingularMayerVietoris.ModuleHomology.mapCycles
        (SingularMayerVietoris.smallInclusion (MappingTorus.HomologyCover.U B.symm)
          (MappingTorus.HomologyCover.V B.symm))
        (n + 1) (coverSmallCycle B.symm m (inverseMonodromy_period_mo1973_27385 m B hB) n b) =
      SingularMayerVietoris.ModuleHomology.mapCycles
        (FirstHurewicz.singularChainMap (productCover m B hB)) (n + 1)
        (PeriodTorusHigherHomology.crossProductCycles (MappingTorus.Circle) X n (arcSumCycle m)
          b) := by
  apply Subtype.ext
  rw [coverSmallCycle_ambient_sum_val, SingularMayerVietoris.ModuleHomology.mapCycles_val]
  change
    (∑ k ∈ Finset.range m,
        (FirstHurewicz.inducedChain (MappingTorus.HomologyCover.inclusionU B.symm) (n + 1)
            (uCrossChain B.symm k n b) +
          FirstHurewicz.inducedChain (MappingTorus.HomologyCover.inclusionV B.symm) (n + 1)
            (vCrossChain B.symm k n b))) =
      FirstHurewicz.inducedChain (productCover m B hB) (n + 1)
        (PeriodTorusHigherHomology.crossProductEdge (MappingTorus.Circle) X n (arcSumChain m) b.1)
  simp only [arcSumChain, map_sum, LinearMap.sum_apply, map_add, LinearMap.add_apply]
  apply Finset.sum_congr rfl
  intro k _
  exact
    congrArg₂ (· + ·) (uStrip_inclusion_crossProduct m B hB k n b.1)
      (vStrip_inclusion_crossProduct m B hB k n b.1)

private theorem MappingTorusHomology.Covering.coverSmallCycle_productCover_class {X : Type}
    [TopologicalSpace X] [CompactSpace X] [T2Space X] (m : ℕ) [NeZero m] (B : X ≃ₜ X)
    (hB : B ^ m = 1) (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    SingularMayerVietoris.ModuleHomology.cycleClass
        (FirstHurewicz.singularComplex (MappingTorus.Torus B.symm)) (n + 1)
        (SingularMayerVietoris.ModuleHomology.mapCycles
          (SingularMayerVietoris.smallInclusion (MappingTorus.HomologyCover.U B.symm)
            (MappingTorus.HomologyCover.V B.symm))
          (n + 1) (coverSmallCycle B.symm m (inverseMonodromy_period_mo1973_27385 m B hB) n b)) =
      productCoverHomology m B hB (n + 1)
        (PeriodTorusHigherHomology.positiveCircleCross X n
          (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) n
            b)) := by
  rw [coverSmallCycle_productCover_eq, positiveCircleCross_subdivision_cycleClass m n b]
  exact
    (SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass
        (FirstHurewicz.singularChainMap (productCover m B hB)) (n + 1)
        (PeriodTorusHigherHomology.crossProductCycles (MappingTorus.Circle) X n (arcSumCycle m)
          b)).symm

private theorem
    MappingTorusHomology.Covering.boundaryCoordinates_productCover_cross_cycleClass {X : Type}
    [TopologicalSpace X] [CompactSpace X] [T2Space X] (m : ℕ) [NeZero m] (B : X ≃ₜ X)
    (hB : B ^ m = 1) (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    MappingTorusHomology.boundaryCoordinates B.symm n
        (productCoverHomology m B hB (n + 1)
          (PeriodTorusHigherHomology.positiveCircleCross X n
            (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) n
              b))) =
      (-homologyNorm m B.symm n
            (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) n
              b),
        homologyNorm m B.symm n
          (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) n
            b)) := by
  rw [← coverSmallCycle_productCover_class]
  exact
    coverSmallCycle_boundaryCoordinates B.symm m (inverseMonodromy_period_mo1973_27385 m B hB) n b

private theorem MappingTorusHomology.Covering.wangBoundary_productCover_cross_cycleClass {X : Type}
    [TopologicalSpace X] [CompactSpace X] [T2Space X] (m : ℕ) [NeZero m] (B : X ≃ₜ X)
    (hB : B ^ m = 1) (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    MappingTorusHomology.wangBoundary B.symm n
        (productCoverHomology m B hB (n + 1)
          (PeriodTorusHigherHomology.positiveCircleCross X n
            (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) n
              b))) =
      homologyNorm m B n
        (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) n b) :=
  by
  rw [MappingTorusHomology.wangBoundary_apply, boundaryCoordinates_productCover_cross_cycleClass]
  simp only [neg_neg]
  rw [homologyNorm_symm m B n hB]

private theorem
    MappingTorusHomology.Covering.wangBoundary_productCover_positiveCircleCross {X : Type}
    [TopologicalSpace X] [CompactSpace X] [T2Space X] (m : ℕ) [NeZero m] (B : X ≃ₜ X)
    (hB : B ^ m = 1) (n : ℕ) (b : SingularMayerVietoris.SingularHomology X n) :
    MappingTorusHomology.wangBoundary B.symm n
        (productCoverHomology m B hB (n + 1)
          (PeriodTorusHigherHomology.positiveCircleCross X n b)) =
      homologyNorm m B n b := by
  obtain ⟨c, rfl⟩ :=
    SingularMayerVietoris.ModuleHomology.cycleClass_surjective (FirstHurewicz.singularComplex X) n
      b
  exact wangBoundary_productCover_cross_cycleClass m B hB n c

private theorem
    MappingTorusHomology.Covering.wangBoundary_productCover {X : Type} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) (n : ℕ) :
    (MappingTorusHomology.wangBoundary B.symm n).comp (productCoverHomology m B hB (n + 1)) =
      (homologyNorm m B n).comp (PeriodTorusHigherHomology.circleBoundary X n) :=
  wangBoundary_productCover_eq_of_cross m B hB n (homologyNorm m B n)
    (wangBoundary_productCover_positiveCircleCross m B hB n)

private theorem MappingTorusHomology.Covering.wangBoundary_productCover_apply {X : Type}
    [TopologicalSpace X] [CompactSpace X] [T2Space X] (m : ℕ) [NeZero m] (B : X ≃ₜ X)
    (hB : B ^ m = 1) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology ((MappingTorus.Circle) × X) (n + 1)) :
    MappingTorusHomology.wangBoundary B.symm n (productCoverHomology m B hB (n + 1) a) =
      homologyNorm m B n (PeriodTorusHigherHomology.circleBoundary X n a) :=
  LinearMap.congr_fun (wangBoundary_productCover m B hB n) a

end Mathoverflow1973

end
