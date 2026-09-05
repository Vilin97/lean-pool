/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.MainTheorem.Core1
public import LeanPool.HopfProblem.Recognition.Smale10
import all LeanPool.HopfProblem.Foundations.Core1
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.Lattice.Core1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology1
import all LeanPool.HopfProblem.Foundations.TriangleRegularBaseFundamentalGroup
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.Toric.ToricSpace1
import all LeanPool.HopfProblem.PeriodFamily.PeriodPoint
import all LeanPool.HopfProblem.Uniformization.CuspUniformization1
import all LeanPool.HopfProblem.Foundations.Core3
import all LeanPool.HopfProblem.PeriodFamily.HolomorphicPeriodMap1
import all LeanPool.HopfProblem.HomologyTheory.FirstHurewicz3
import all LeanPool.HopfProblem.Lattice.Core2
import all LeanPool.HopfProblem.Elliptic.Core1
import all LeanPool.HopfProblem.PeriodFamily.PeriodDomain
import all LeanPool.HopfProblem.Threefold.SpecialPeriods1
import all LeanPool.HopfProblem.Uniformization.CuspUniformization2
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods1
import all LeanPool.HopfProblem.Elliptic.Core2
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods2
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods3
import all LeanPool.HopfProblem.Threefold.SpecialPeriods4
import all LeanPool.HopfProblem.PeriodFamily.Core1
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods6
import all LeanPool.HopfProblem.PeriodFamily.Core2
import all LeanPool.HopfProblem.Threefold.SpecialPeriods6
import all LeanPool.HopfProblem.Elliptic.Core3
import all LeanPool.HopfProblem.HomologyOfX.ThreefoldGluing1
import all LeanPool.HopfProblem.Uniformization.TriangleUniformizationGluing
import all LeanPool.HopfProblem.Threefold.SpecialPeriods7
import all LeanPool.HopfProblem.Elliptic.Core4
import all LeanPool.HopfProblem.HomologyOfX.ThreefoldGluing2
import all LeanPool.HopfProblem.PeriodFamily.HolomorphicPeriodMap2
import all LeanPool.HopfProblem.Threefold.SpecialPeriods8
import all LeanPool.HopfProblem.Elliptic.Core5
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods8
import all LeanPool.HopfProblem.Threefold.SpecialPeriods9
import all LeanPool.HopfProblem.Foundations.SplitGroupExtension
import all LeanPool.HopfProblem.PeriodFamily.Core3
import all LeanPool.HopfProblem.Elliptic.Core6
import all LeanPool.HopfProblem.Threefold.SpecialPeriods10
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods9
import all LeanPool.HopfProblem.Pi1.TwistGroup
import all LeanPool.HopfProblem.PeriodFamily.Core5
import all LeanPool.HopfProblem.Recognition.Smale10
import all LeanPool.HopfProblem.Foundations.CanonicalProduct
import all LeanPool.HopfProblem.MainTheorem.Core1

/-!
# Hopf problem: threefold · special periods 11

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

private def SpecialPeriods.Threefold.EllipticGeometry.regularColumnLoop
    (b : SpecialPeriods.TriangleRegularPoint) (w : Lattice) :
    Path
      (((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁
            SpecialPeriods.specialPeriodMap_generator₂)).fundamentalGroupBasepoint
        b)
      (((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁
            SpecialPeriods.specialPeriodMap_generator₂)).fundamentalGroupBasepoint
        b) :=
  (PeriodFamily.FlatTorus.periodLoop w).map
    (((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁
          SpecialPeriods.specialPeriodMap_generator₂)).quotient_continuous.comp
      (continuous_const.prodMk continuous_id))

private theorem SpecialPeriods.Threefold.EllipticGeometry.regularColumnLoop_apply
    (b : SpecialPeriods.TriangleRegularPoint) (w : Lattice) (t : (unitInterval)) :
    regularColumnLoop b w t =
      ((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁
            SpecialPeriods.specialPeriodMap_generator₂)).quotient
        (b, standardLattice.mkQ ((t : ℝ) • Elliptic.realCast w)) := by
  change
    ((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁
            SpecialPeriods.specialPeriodMap_generator₂)).quotient
        (b, PeriodFamily.FlatTorus.periodLoop w t) =
      _
  rw [PeriodFamily.FlatTorus.periodLoop_apply]

private theorem SpecialPeriods.Threefold.EllipticGeometry.regularColumnLoop_class
    (b : SpecialPeriods.TriangleRegularPoint) (w : Lattice) :
    FundamentalGroup.fromPath ⟦regularColumnLoop b w⟧ =
      ((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁
            SpecialPeriods.specialPeriodMap_generator₂)).latticeFundamentalGroupHom
        b (Multiplicative.ofAdd w) :=
  (((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁
          SpecialPeriods.specialPeriodMap_generator₂)).latticeFundamentalGroupHom_periodLoop
      b w).symm

private def SpecialPeriods.Threefold.EllipticGeometry.globalColumnLoop
    (b : SpecialPeriods.TriangleRegularPoint) (w : Lattice) :
    Path
      (SpecialPeriods.Threefold.regularFamilyInclusionMap
        (((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
              SpecialPeriods.specialPeriodMap_generator₁
              SpecialPeriods.specialPeriodMap_generator₂)).fundamentalGroupBasepoint
          b))
      (SpecialPeriods.Threefold.regularFamilyInclusionMap
        (((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
              SpecialPeriods.specialPeriodMap_generator₁
              SpecialPeriods.specialPeriodMap_generator₂)).fundamentalGroupBasepoint
          b)) :=
  (regularColumnLoop b w).map SpecialPeriods.Threefold.regularFamilyInclusionMap.continuous

private theorem SpecialPeriods.Threefold.EllipticGeometry.globalColumnLoop_apply
    (b : SpecialPeriods.TriangleRegularPoint) (w : Lattice) (t : (unitInterval)) :
    globalColumnLoop b w t =
      SpecialPeriods.Threefold.regularFamilyInclusionMap
        (((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
              SpecialPeriods.specialPeriodMap_generator₁
              SpecialPeriods.specialPeriodMap_generator₂)).quotient
          (b, standardLattice.mkQ ((t : ℝ) • Elliptic.realCast w))) :=
  congrArg SpecialPeriods.Threefold.regularFamilyInclusionMap (regularColumnLoop_apply b w t)

private theorem SpecialPeriods.Threefold.EllipticGeometry.globalColumnLoop_class
    (b : SpecialPeriods.TriangleRegularPoint) (w : Lattice) :
    FundamentalGroup.fromPath ⟦globalColumnLoop b w⟧ =
      FundamentalGroup.map SpecialPeriods.Threefold.regularFamilyInclusionMap
        (((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
              SpecialPeriods.specialPeriodMap_generator₁
              SpecialPeriods.specialPeriodMap_generator₂)).fundamentalGroupBasepoint
          b)
        (((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
              SpecialPeriods.specialPeriodMap_generator₁
              SpecialPeriods.specialPeriodMap_generator₂)).latticeFundamentalGroupHom
          b (Multiplicative.ofAdd w)) :=
  congrArg
    (FundamentalGroup.map SpecialPeriods.Threefold.regularFamilyInclusionMap
      (((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁
            SpecialPeriods.specialPeriodMap_generator₂)).fundamentalGroupBasepoint
        b))
    (regularColumnLoop_class b w)

private def SpecialPeriods.Threefold.EllipticGeometry.upstairsPathGlobalTail
    {b : SpecialPeriods.TriangleRegularPoint}
    (p : Path (PeriodFamily.Meridians.normalizedRegularMeridianBasepoint) b) :
    Path SpecialPeriods.Threefold.PiOne.basepoint
      (SpecialPeriods.Threefold.regularFamilyInclusionMap
        (((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
              SpecialPeriods.specialPeriodMap_generator₁
              SpecialPeriods.specialPeriodMap_generator₂)).fundamentalGroupBasepoint
          b)) :=
  (((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁
            SpecialPeriods.specialPeriodMap_generator₂)).zeroSectionPath
        p).map
    SpecialPeriods.Threefold.regularFamilyInclusionMap.continuous

private theorem SpecialPeriods.Threefold.EllipticGeometry.upstairsPathGlobalTail_symm
    {b : SpecialPeriods.TriangleRegularPoint}
    (p : Path (PeriodFamily.Meridians.normalizedRegularMeridianBasepoint) b) :
    (upstairsPathGlobalTail p).symm =
      (((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
                SpecialPeriods.specialPeriodMap_generator₁
                SpecialPeriods.specialPeriodMap_generator₂)).zeroSectionPath
            p.symm).map
        SpecialPeriods.Threefold.regularFamilyInclusionMap.continuous := by
  ext t
  rfl

private theorem SpecialPeriods.Threefold.EllipticGeometry.transport_globalColumnLoop
    {b : SpecialPeriods.TriangleRegularPoint}
    (p : Path (PeriodFamily.Meridians.normalizedRegularMeridianBasepoint) b) (w : Lattice) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath (upstairsPathGlobalTail p).symm
        (FundamentalGroup.fromPath ⟦globalColumnLoop b w⟧) =
      SpecialPeriods.Threefold.PiOne.latticeHom (Multiplicative.ofAdd w) := by
  rw [upstairsPathGlobalTail_symm, globalColumnLoop_class]
  exact
    (fundamentalGroup_basepoint_naturality_apply
          SpecialPeriods.Threefold.regularFamilyInclusionMap
          (((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
                SpecialPeriods.specialPeriodMap_generator₁
                SpecialPeriods.specialPeriodMap_generator₂)).zeroSectionPath
            p.symm)
          (((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
                SpecialPeriods.specialPeriodMap_generator₁
                SpecialPeriods.specialPeriodMap_generator₂)).latticeFundamentalGroupHom
            b (Multiplicative.ofAdd w))).trans
      (congrArg
        (FundamentalGroup.map SpecialPeriods.Threefold.regularFamilyInclusionMap
          (((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
                SpecialPeriods.specialPeriodMap_generator₁
                SpecialPeriods.specialPeriodMap_generator₂)).fundamentalGroupBasepoint
            (PeriodFamily.Meridians.normalizedRegularMeridianBasepoint)))
        (((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
              SpecialPeriods.specialPeriodMap_generator₁
              SpecialPeriods.specialPeriodMap_generator₂)).latticeFundamentalGroupHom_baseChange
          p.symm (Multiplicative.ofAdd w)))

private theorem
    SpecialPeriods.Threefold.EllipticGeometry.attachingLoop_pow_order (j : Elliptic.Kind)
    (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j)) :
    (FundamentalGroup.fromPath ⟦attachingLoop j s₀ hs₀ hr⟧) ^ j.order =
      FundamentalGroup.fromPath ⟦attachingFibreLoop j s₀ hs₀ hr j.twist⟧ := by
  apply (attachingDeckEquiv j s₀ hs₀ hr).injective
  rw [map_pow, attachingDeckEquiv_attachingLoop, attachingDeckEquiv_attachingFibreLoop, inv_pow,
    Elliptic.deckGenerator_pow_order j j.twist (Elliptic.mainTwist_admissible j).1]
  exact (map_inv (Elliptic.deckTranslationHom j j.twist) (Multiplicative.ofAdd j.twist)).symm

private theorem SpecialPeriods.Threefold.EllipticGeometry.includedAttachingFibreLoop_eq_column
    (j : Elliptic.Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j))
    (w : Lattice) :
    includedAttachingFibreLoop j s₀ hs₀ hr w =
      globalColumnLoop (attachingUpstairsPoint j s₀ hs₀ 0) w := by
  ext t
  rw [globalColumnLoop_apply]
  exact
    (inclusion_eq_regular_overlap j (attachingFibreLoop j s₀ hs₀ hr w t)
          (attachingFibreLoop_mem_overlap j s₀ hs₀ hr w t)).trans
      (congrArg SpecialPeriods.Threefold.regularFamilyInclusionMap
        (specialEllipticOverlap_attachingFibreLoop j s₀ hs₀ hr w t))

private def
    SpecialPeriods.Threefold.EllipticGeometry.attachingUpstairsTail (j : Elliptic.Kind) (s₀ : ℂ)
    (hs₀ : 0 < s₀.im) :
    Path (PeriodFamily.Meridians.normalizedRegularMeridianBasepoint)
      (attachingUpstairsPoint j s₀ hs₀ 0) :=
  PathConnectedSpace.somePath _ _

private def SpecialPeriods.Threefold.EllipticGeometry.attachingBaseTail (j : Elliptic.Kind) (s₀ : ℂ)
    (hs₀ : 0 < s₀.im) :
    Path
      (SpecialPeriods.triangleRegularProject
        (PeriodFamily.Meridians.normalizedRegularMeridianBasepoint))
      (SpecialPeriods.triangleRegularProject (attachingUpstairsPoint j s₀ hs₀ 0)) :=
  (attachingUpstairsTail j s₀ hs₀).map SpecialPeriods.triangleRegularProject_covering.continuous

private def
    SpecialPeriods.Threefold.EllipticGeometry.attachingGlobalTail (j : Elliptic.Kind) (s₀ : ℂ)
    (hs₀ : 0 < s₀.im) :
    Path SpecialPeriods.Threefold.PiOne.basepoint
      (SpecialPeriods.Threefold.regularFamilyInclusionMap
        (((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
              SpecialPeriods.specialPeriodMap_generator₁
              SpecialPeriods.specialPeriodMap_generator₂)).fundamentalGroupBasepoint
          (attachingUpstairsPoint j s₀ hs₀ 0))) :=
  upstairsPathGlobalTail (attachingUpstairsTail j s₀ hs₀)

private theorem SpecialPeriods.Threefold.EllipticGeometry.attachingGlobalTail_eq_zeroSection
    (j : Elliptic.Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im) :
    attachingGlobalTail j s₀ hs₀ =
      ((attachingBaseTail j s₀ hs₀).map
            ((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
                SpecialPeriods.specialPeriodMap_generator₁
                SpecialPeriods.specialPeriodMap_generator₂)).zeroSection_continuous).map
        SpecialPeriods.Threefold.regularFamilyInclusionMap.continuous := by
  ext t
  rfl

private def
    SpecialPeriods.Threefold.EllipticGeometry.attachingTransportHom (j : Elliptic.Kind) (s₀ : ℂ)
    (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j)) :
    FundamentalGroup (LocalSpace j) (attachingBasepoint j s₀ hs₀ hr) →*
      SpecialPeriods.Threefold.PiOne.GlobalGroup :=
  (FundamentalGroup.fundamentalGroupMulEquivOfPath
        (attachingGlobalTail j s₀ hs₀).symm).toMonoidHom.comp
    ((MulEquiv.cast (M := FundamentalGroup SpecialPeriods.Threefold.Space)
          (attachingGlobalBasepoint_eq j s₀ hs₀ hr)).toMonoidHom.comp
      (FundamentalGroup.map (attachingPieceInclusionMap j) (attachingBasepoint j s₀ hs₀ hr)))

private theorem SpecialPeriods.Threefold.EllipticGeometry.attachingTransportHom_fromPath
    (j : Elliptic.Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j))
    (γ : Path (attachingBasepoint j s₀ hs₀ hr) (attachingBasepoint j s₀ hs₀ hr)) :
    attachingTransportHom j s₀ hs₀ hr (FundamentalGroup.fromPath ⟦γ⟧) =
      FundamentalGroup.fundamentalGroupMulEquivOfPath (attachingGlobalTail j s₀ hs₀).symm
        (FundamentalGroup.fromPath
          ⟦(γ.map (inclusion_continuous j)).cast (attachingGlobalBasepoint_eq j s₀ hs₀ hr).symm
              (attachingGlobalBasepoint_eq j s₀ hs₀ hr).symm⟧) := by
  change
    FundamentalGroup.fundamentalGroupMulEquivOfPath (attachingGlobalTail j s₀ hs₀).symm
        (MulEquiv.cast (M := FundamentalGroup SpecialPeriods.Threefold.Space)
          (attachingGlobalBasepoint_eq j s₀ hs₀ hr)
          (FundamentalGroup.fromPath ⟦γ.map (inclusion_continuous j)⟧)) =
      _
  rw [Elliptic.LogGauge.fundamentalGroup_cast_loop]

private theorem SpecialPeriods.Threefold.EllipticGeometry.attachingTransportHom_fibreLoop
    (j : Elliptic.Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j))
    (w : Lattice) :
    attachingTransportHom j s₀ hs₀ hr
        (FundamentalGroup.fromPath ⟦attachingFibreLoop j s₀ hs₀ hr w⟧) =
      SpecialPeriods.Threefold.PiOne.latticeHom (Multiplicative.ofAdd w) := by
  rw [attachingTransportHom_fromPath]
  change
    FundamentalGroup.fundamentalGroupMulEquivOfPath (attachingGlobalTail j s₀ hs₀).symm
        (FundamentalGroup.fromPath ⟦includedAttachingFibreLoop j s₀ hs₀ hr w⟧) =
      _
  rw [includedAttachingFibreLoop_eq_column]
  exact transport_globalColumnLoop (attachingUpstairsTail j s₀ hs₀) w

private def SpecialPeriods.Threefold.EllipticGeometry.transportedAttachingLoop (j : Elliptic.Kind)
    (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j)) :
    Path SpecialPeriods.Threefold.PiOne.basepoint SpecialPeriods.Threefold.PiOne.basepoint :=
  (attachingGlobalTail j s₀ hs₀).trans
    ((includedAttachingLoop j s₀ hs₀ hr).trans (attachingGlobalTail j s₀ hs₀).symm)

private def SpecialPeriods.Threefold.EllipticGeometry.transportedAttachingClass (j : Elliptic.Kind)
    (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j)) :
    SpecialPeriods.Threefold.PiOne.GlobalGroup :=
  attachingTransportHom j s₀ hs₀ hr (FundamentalGroup.fromPath ⟦attachingLoop j s₀ hs₀ hr⟧)

private theorem SpecialPeriods.Threefold.EllipticGeometry.transportedAttachingClass_fromPath
    (j : Elliptic.Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j)) :
    transportedAttachingClass j s₀ hs₀ hr =
      FundamentalGroup.fromPath ⟦transportedAttachingLoop j s₀ hs₀ hr⟧ := by
  rw [transportedAttachingClass, attachingTransportHom_fromPath]
  change
    FundamentalGroup.fundamentalGroupMulEquivOfPath (attachingGlobalTail j s₀ hs₀).symm
        (Path.Homotopic.Quotient.mk (includedAttachingLoop j s₀ hs₀ hr)) =
      _
  rw [fundamentalGroup_basepoint_change_mk, Path.symm_symm]
  rfl

private def
    SpecialPeriods.Threefold.EllipticGeometry.transportedAttachingBaseLoop (j : Elliptic.Kind)
    (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j)) :
    Path
      (SpecialPeriods.triangleRegularProject
        (PeriodFamily.Meridians.normalizedRegularMeridianBasepoint))
      (SpecialPeriods.triangleRegularProject
        (PeriodFamily.Meridians.normalizedRegularMeridianBasepoint)) :=
  (attachingBaseTail j s₀ hs₀).trans
    ((attachingRegularBaseLoop j s₀ hs₀ hr).trans (attachingBaseTail j s₀ hs₀).symm)

private theorem SpecialPeriods.Threefold.EllipticGeometry.map_twice_tail_mo1973_26156
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {a b : X}
    (p : Path a b) (q : Path b b) {f : X → Y} {g : Y → Z} (hf : Continuous f)
    (hg : Continuous g) :
    ((p.trans (q.trans p.symm)).map hf).map hg =
      ((p.map hf).map hg).trans (((q.map hf).map hg).trans ((p.map hf).map hg).symm) := by
  simp only [Path.map_trans, Path.map_symm]

private theorem SpecialPeriods.Threefold.EllipticGeometry.transportedAttachingLoop_eq_zeroSection
    (j : Elliptic.Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j)) :
    transportedAttachingLoop j s₀ hs₀ hr =
      ((transportedAttachingBaseLoop j s₀ hs₀ hr).map
            ((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
                SpecialPeriods.specialPeriodMap_generator₁
                SpecialPeriods.specialPeriodMap_generator₂)).zeroSection_continuous).map
        SpecialPeriods.Threefold.regularFamilyInclusionMap.continuous := by
  simp only [transportedAttachingLoop, transportedAttachingBaseLoop]
  rw [attachingGlobalTail_eq_zeroSection, includedAttachingLoop_eq_regular,
    attachingRegularLoop_eq_zeroSection]
  exact
    (map_twice_tail_mo1973_26156 (attachingBaseTail j s₀ hs₀)
        (attachingRegularBaseLoop j s₀ hs₀ hr)
        ((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁
            SpecialPeriods.specialPeriodMap_generator₂)).zeroSection_continuous
        SpecialPeriods.Threefold.regularFamilyInclusionMap.continuous).symm

private def SpecialPeriods.Threefold.EllipticGeometry.attachingBaseSectionHom :
    FundamentalGroup SpecialPeriods.TriangleRegularQuotient
        (SpecialPeriods.triangleRegularProject
          (PeriodFamily.Meridians.normalizedRegularMeridianBasepoint)) →*
      SpecialPeriods.Threefold.PiOne.GlobalGroup :=
  SpecialPeriods.Threefold.PiOne.regularHom.comp
    (((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁
          SpecialPeriods.specialPeriodMap_generator₂)).sectionFundamentalGroupHom
      (PeriodFamily.Meridians.normalizedRegularMeridianBasepoint))

private theorem SpecialPeriods.Threefold.EllipticGeometry.transportedAttachingClass_eq_baseImage
    (j : Elliptic.Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j)) :
    transportedAttachingClass j s₀ hs₀ hr =
      attachingBaseSectionHom
        (FundamentalGroup.fromPath ⟦transportedAttachingBaseLoop j s₀ hs₀ hr⟧) := by
  rw [transportedAttachingClass_fromPath, transportedAttachingLoop_eq_zeroSection]
  rfl

private theorem SpecialPeriods.Threefold.EllipticGeometry.transportedAttachingClass_pow_order
    (j : Elliptic.Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j)) :
    transportedAttachingClass j s₀ hs₀ hr ^ j.order =
      SpecialPeriods.Threefold.PiOne.latticeHom (Multiplicative.ofAdd j.twist) := by
  change
    (attachingTransportHom j s₀ hs₀ hr (FundamentalGroup.fromPath ⟦attachingLoop j s₀ hs₀ hr⟧)) ^
        j.order =
      _
  rw [← map_pow, attachingLoop_pow_order, attachingTransportHom_fibreLoop]

private abbrev SpecialPeriods.Threefold.CuspAttaching.cuspLift
    (s : SpecialPeriods.CuspFamily.LogBase radius) : SpecialPeriods.TriangleRegularPoint :=
  SpecialPeriods.CuspFamily.logBaseToRegular radius radius_le_cuspChart s

private theorem SpecialPeriods.Threefold.CuspAttaching.cuspParameter_norm_lt
    (s : SpecialPeriods.CuspFamily.LogBase radius) :
    ‖CuspUniformization.exponential s‖ < radius :=
  (SpecialPeriods.CuspFamily.mem_logBase radius s).mp s.property

private theorem SpecialPeriods.Threefold.CuspAttaching.cuspParameter_log_neg
    (s : SpecialPeriods.CuspFamily.LogBase radius) :
    Real.log ‖CuspUniformization.exponential s‖ < 0 :=
  Real.log_neg (norm_pos_iff.mpr (CuspUniformization.exponential_ne_zero s))
    ((cuspParameter_norm_lt s).trans data.radius_lt_one)

private theorem SpecialPeriods.Threefold.CuspAttaching.cuspParameter_drift_bound
    (s : SpecialPeriods.CuspFamily.LogBase radius) :
    ToricSpace.entryNorm
        (ToricSpace.driftMatrix data.correction (CuspUniformization.exponential s)) ≤
      -Real.log ‖CuspUniformization.exponential s‖ / 4 :=
  data.smallDrift _ (norm_pos_iff.mpr (CuspUniformization.exponential_ne_zero s))
    (cuspParameter_norm_lt s)

private abbrev SpecialPeriods.Threefold.CuspAttaching.nativePeriodData
    (s : SpecialPeriods.CuspFamily.LogBase radius) : FullPeriodMatrix :=
  CuspUniformization.periodData data.correction s (cuspParameter_log_neg s)
    (cuspParameter_drift_bound s)

private def SpecialPeriods.Threefold.CuspAttaching.nativeFibreMap
    (s : SpecialPeriods.CuspFamily.LogBase radius) :
    (nativePeriodData s).Torus → SpecialPeriods.Threefold.SpecialCuspPiece :=
  CuspUniformization.fibreMap data.correction radius s (cuspParameter_norm_lt s)
    (cuspParameter_log_neg s) (cuspParameter_drift_bound s)

private theorem SpecialPeriods.Threefold.CuspAttaching.nativeFibreMap_continuous
    (s : SpecialPeriods.CuspFamily.LogBase radius) : Continuous (nativeFibreMap s) :=
  CuspUniformization.fibreMap_continuous data.correction radius s (cuspParameter_norm_lt s)
    (cuspParameter_log_neg s) (cuspParameter_drift_bound s)

private theorem SpecialPeriods.Threefold.CuspAttaching.nativeFibreMap_mkQ
    (s : SpecialPeriods.CuspFamily.LogBase radius) (z : ComplexPlane₂) :
    nativeFibreMap s ((nativePeriodData s).lattice.mkQ z) =
      CuspUniformization.fibreCover data.correction radius s (cuspParameter_norm_lt s) z :=
  rfl

private def SpecialPeriods.Threefold.CuspAttaching.logVector
    (s : SpecialPeriods.CuspFamily.LogBase radius) (z : ComplexPlane₂) :
    CuspUniformization.LogCover radius :=
  ⟨((s : ℂ), z), s.property⟩

private def SpecialPeriods.Threefold.CuspAttaching.regularFamilyInclusionMap :
    C(SpecialPeriods.Threefold.SpecialRegularFamily, SpecialPeriods.Threefold.Space) :=
  ⟨SpecialPeriods.Threefold.inclusion Option.none,
    (SpecialPeriods.Threefold.inclusion_openEmbedding Option.none).continuous⟩

private def SpecialPeriods.Threefold.CuspAttaching.globalLatticeHom
    (b : SpecialPeriods.TriangleRegularPoint) :
    Multiplicative Lattice →*
      FundamentalGroup SpecialPeriods.Threefold.Space
        (SpecialPeriods.Threefold.inclusion Option.none
          (regularData.fundamentalGroupBasepoint b)) :=
  (FundamentalGroup.map regularFamilyInclusionMap (regularData.fundamentalGroupBasepoint b)).comp
    (regularData.latticeFundamentalGroupHom b)

private def SpecialPeriods.Threefold.CuspAttaching.regularFibreMap
    (b : SpecialPeriods.TriangleRegularPoint) :
    C(RealTorus₄, SpecialPeriods.Threefold.SpecialRegularFamily) :=
  ⟨fun x => regularData.quotient (b, x),
    regularData.quotient_continuous.comp (continuous_const.prodMk continuous_id)⟩

private def SpecialPeriods.Threefold.CuspAttaching.regularLatticeLoop
    (b : SpecialPeriods.TriangleRegularPoint) (v : Lattice) :
    Path (regularData.fundamentalGroupBasepoint b) (regularData.fundamentalGroupBasepoint b) :=
  (PeriodFamily.FlatTorus.periodLoop v).map (regularFibreMap b).continuous

private def SpecialPeriods.Threefold.CuspAttaching.globalLatticeLoop
    (b : SpecialPeriods.TriangleRegularPoint) (v : Lattice) :
    Path
      (SpecialPeriods.Threefold.inclusion Option.none (regularData.fundamentalGroupBasepoint b))
      (SpecialPeriods.Threefold.inclusion Option.none
        (regularData.fundamentalGroupBasepoint b)) :=
  (regularLatticeLoop b v).map regularFamilyInclusionMap.continuous

private theorem SpecialPeriods.Threefold.CuspAttaching.globalLatticeLoop_apply
    (b : SpecialPeriods.TriangleRegularPoint) (v : Lattice) (t : (unitInterval)) :
    globalLatticeLoop b v t =
      SpecialPeriods.Threefold.inclusion Option.none
        (regularData.quotient (b, standardLattice.mkQ ((t : ℝ) • Elliptic.realCast v))) :=
  congrArg
    (fun x : RealTorus₄ =>
      SpecialPeriods.Threefold.inclusion Option.none (regularData.quotient (b, x)))
    (PeriodFamily.FlatTorus.periodLoop_apply v t)

private theorem SpecialPeriods.Threefold.CuspAttaching.globalLatticeHom_periodLoop
    (b : SpecialPeriods.TriangleRegularPoint) (v : Lattice) :
    globalLatticeHom b (Multiplicative.ofAdd v) =
      Path.Homotopic.Quotient.mk (globalLatticeLoop b v) := by
  change
    FundamentalGroup.map regularFamilyInclusionMap (regularData.fundamentalGroupBasepoint b)
        (regularData.latticeFundamentalGroupHom b (Multiplicative.ofAdd v)) =
      _
  rw [regularData.latticeFundamentalGroupHom_periodLoop]
  rfl

private def SpecialPeriods.Threefold.CuspAttaching.nativeGlobalPeriodLoop
    (s : SpecialPeriods.CuspFamily.LogBase radius) (v : Lattice) :
    Path (SpecialPeriods.Threefold.inclusion (Option.some Option.none) (nativeFibreMap s 0))
      (SpecialPeriods.Threefold.inclusion (Option.some Option.none) (nativeFibreMap s 0)) :=
  (((nativePeriodData s).periodLoop (CuspUniformization.sourcePeriodCoordinates v)).map
        (nativeFibreMap_continuous s)).map
    (SpecialPeriods.Threefold.inclusion_openEmbedding (Option.some Option.none)).continuous

private theorem SpecialPeriods.Threefold.CuspAttaching.nativePeriodData_matrix_eq_regular_leftBlock
    (s : SpecialPeriods.CuspFamily.LogBase radius) :
    (nativePeriodData s).matrix = (regularData.periods.point (cuspLift s)).val.leftBlock := by
  exact
    ((congrArg (fun p : PeriodDomain => p.val.leftBlock) (period_agreement s)).trans
        (data.point_leftBlock s)).symm

private theorem SpecialPeriods.Threefold.CuspAttaching.native_periodVector_sourceCoordinates
    (s : SpecialPeriods.CuspFamily.LogBase radius) (v : Lattice) :
    (nativePeriodData s).periodVector (CuspUniformization.sourcePeriodCoordinates v) =
      regularData.periods.periodEquiv (cuspLift s) (Elliptic.realCast v) := by
  calc
    _ = (regularData.periods.point (cuspLift s)).periodVector v :=
      (regularData.periods.point (cuspLift s)).fullPeriod_periodVector (nativePeriodData s)
        (nativePeriodData_matrix_eq_regular_leftBlock s) v
    _ = _ := (regularData.periodEquiv_realCast (cuspLift s) v).symm

private theorem
  SpecialPeriods.Threefold.CuspAttaching.sourcePeriodCoordinates_eq_integer_of_projection_zero
    (v : Lattice) (hv : CuspUniformization.cuspLatticeProjection v = 0) :
    CuspUniformization.sourcePeriodCoordinates v = (![v 2, v 3], 0) := by
  change (![v 2, v 3], CuspUniformization.cuspLatticeProjection v) = _
  rw [hv]

private theorem
  SpecialPeriods.Threefold.CuspAttaching.nativeFibre_periodLoop_nullhomotopic_of_projection_zero
    (s : SpecialPeriods.CuspFamily.LogBase radius) (v : Lattice)
    (hv : CuspUniformization.cuspLatticeProjection v = 0) :
    Path.Homotopic
      (((nativePeriodData s).periodLoop (CuspUniformization.sourcePeriodCoordinates v)).map
        (nativeFibreMap_continuous s))
      (Path.refl (nativeFibreMap s 0)) := by
  rw [sourcePeriodCoordinates_eq_integer_of_projection_zero v hv]
  exact
    CuspUniformization.fibre_integerPeriod_loop_nullhomotopic data.correction radius s
      (cuspParameter_norm_lt s) (cuspParameter_log_neg s) (cuspParameter_drift_bound s)
      data.radius_pos data.radius_lt_one data.holomorphic data.smallDrift ![v 2, v 3]

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.Threefold.specialRegularFamilyChartedSpace
    SpecialPeriods.Threefold.specialCuspPieceChartedSpace in
private theorem SpecialPeriods.Threefold.CuspAttaching.familyMap_iteratedCover_logVector
    (s : SpecialPeriods.CuspFamily.LogBase radius) (z : ComplexPlane₂) :
    SpecialPeriods.CuspGlobalOverlap.familyMap data regularData radius_le_cuspChart
        (data.iteratedCover (logVector s z)) =
      regularData.quotient (regularData.periods.quotientMap (cuspLift s, z)) := by
  change
    regularData.quotient
        (HolomorphicPeriodMap.periodPullbackMap data.periods regularData.periods
          (SpecialPeriods.CuspFamily.logBaseToRegular radius radius_le_cuspChart)
          (data.periods.quotientMap (s, z))) =
      _
  apply congrArg regularData.quotient
  exact
    HolomorphicPeriodMap.periodPullbackMap_quotientMap data.periods regularData.periods
      (SpecialPeriods.CuspFamily.logBaseToRegular radius radius_le_cuspChart) period_agreement
      (s, z)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.Threefold.specialRegularFamilyChartedSpace
    SpecialPeriods.Threefold.specialCuspPieceChartedSpace in
private theorem SpecialPeriods.Threefold.CuspAttaching.fibreCover_mem_overlap
    (s : SpecialPeriods.CuspFamily.LogBase radius) (z : ComplexPlane₂) :
    CuspUniformization.fibreCover data.correction radius s (cuspParameter_norm_lt s) z ∈
      SpecialPeriods.Threefold.specialCuspOverlap.source := by
  rw [SpecialPeriods.Threefold.specialCuspOverlap_source]
  change
    SpecialPeriods.Threefold.CuspPiece.projectionToBase SpecialPeriods.specialCuspData
        SpecialPeriods.Threefold.specialBaseCover
        (CuspUniformization.fibreCover data.correction radius s (cuspParameter_norm_lt s) z) ∈
      SpecialPeriods.Threefold.regularPatch
  apply
    (SpecialPeriods.Threefold.CuspPiece.projectionToBase_mem_regular_iff
        SpecialPeriods.specialCuspData SpecialPeriods.Threefold.specialBaseCover _).mpr
  exact
    (CuspUniformization.projection_fibreCover data.correction radius s (cuspParameter_norm_lt s)
          z).trans_ne
      (CuspUniformization.exponential_ne_zero s)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.Threefold.specialRegularFamilyChartedSpace
    SpecialPeriods.Threefold.specialCuspPieceChartedSpace in
private theorem SpecialPeriods.Threefold.CuspAttaching.overlap_fibreCover
    (s : SpecialPeriods.CuspFamily.LogBase radius) (z : ComplexPlane₂) :
    SpecialPeriods.Threefold.specialCuspOverlap
        (CuspUniformization.fibreCover data.correction radius s (cuspParameter_norm_lt s) z) =
      regularData.quotient (regularData.periods.quotientMap (cuspLift s, z)) := by
  let :=
    CuspQuotient.chartedSpace data.correction radius data.radius_pos data.radius_lt_one
      data.holomorphic data.smallDrift
  let := regularData.chartedSpace (SpecialPeriods.CuspGlobalOverlap.familyCovering regularData)
  have hx :
    CuspUniformization.fibreCover data.correction radius s (cuspParameter_norm_lt s) z ∈
      CuspUniformization.puncturedQuotientOpen data.correction radius := by
    change
      CuspQuotient.projection data.correction radius
          (CuspUniformization.fibreCover data.correction radius s (cuspParameter_norm_lt s) z) ≠
        0
    rw [CuspUniformization.projection_fibreCover]
    exact CuspUniformization.exponential_ne_zero s
  have he :
    (⟨CuspUniformization.fibreCover data.correction radius s (cuspParameter_norm_lt s) z, hx⟩ :
        CuspUniformization.PuncturedQuotient data.correction radius) =
      CuspUniformization.puncturedCuspCover data.correction radius (logVector s z) := by
    apply Subtype.ext
    rfl
  have h :=
    SpecialPeriods.CuspGlobalOverlap.cuspToRegularPartial_apply data regularData
      radius_le_cuspChart period_agreement
      (CuspUniformization.fibreCover data.correction radius s (cuspParameter_norm_lt s) z) hx
  have hrepresentative :=
    congrArg
      (fun x : CuspUniformization.PuncturedQuotient data.correction radius =>
        (SpecialPeriods.CuspGlobalOverlap.puncturedBiholomorph data regularData
            radius_le_cuspChart period_agreement x :
          regularData.Space))
      he
  have hcover :=
    SpecialPeriods.CuspGlobalOverlap.puncturedBiholomorph_cover data regularData
      radius_le_cuspChart period_agreement (logVector s z)
  change
    SpecialPeriods.Threefold.specialCuspOverlap
        (CuspUniformization.fibreCover data.correction radius s (cuspParameter_norm_lt s) z) =
      _ at h
  exact h.trans (hrepresentative.trans (hcover.trans (familyMap_iteratedCover_logVector s z)))

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.Threefold.specialRegularFamilyChartedSpace
    SpecialPeriods.Threefold.specialCuspPieceChartedSpace in
private theorem SpecialPeriods.Threefold.CuspAttaching.inclusion_fibreCover
    (s : SpecialPeriods.CuspFamily.LogBase radius) (z : ComplexPlane₂) :
    SpecialPeriods.Threefold.inclusion (Option.some Option.none)
        (CuspUniformization.fibreCover data.correction radius s (cuspParameter_norm_lt s) z) =
      SpecialPeriods.Threefold.inclusion Option.none
        (regularData.quotient (regularData.periods.quotientMap (cuspLift s, z))) := by
  apply
    (SpecialPeriods.Threefold.gluingData.inclusion_eq_iff (Option.some Option.none) Option.none _
        _).mpr
  exact ⟨fibreCover_mem_overlap s z, overlap_fibreCover s z⟩

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.Threefold.specialRegularFamilyChartedSpace
    SpecialPeriods.Threefold.specialCuspPieceChartedSpace in
private theorem SpecialPeriods.Threefold.CuspAttaching.inclusion_nativeFibreMap_zero
    (s : SpecialPeriods.CuspFamily.LogBase radius) :
    SpecialPeriods.Threefold.inclusion (Option.some Option.none) (nativeFibreMap s 0) =
      SpecialPeriods.Threefold.inclusion Option.none
        (regularData.fundamentalGroupBasepoint (cuspLift s)) := by
  have hz :
    nativeFibreMap s 0 =
      CuspUniformization.fibreCover data.correction radius s (cuspParameter_norm_lt s) 0 := by
    simpa only [map_zero] using nativeFibreMap_mkQ s 0
  rw [hz, inclusion_fibreCover]
  change
    SpecialPeriods.Threefold.inclusion Option.none
        (regularData.quotient (regularData.periods.quotientMap (cuspLift s, 0))) =
      SpecialPeriods.Threefold.inclusion Option.none (regularData.quotient (cuspLift s, 0))
  simp only [HolomorphicPeriodMap.quotientMap, map_zero]

private theorem SpecialPeriods.Threefold.CuspAttaching.nativeGlobalPeriodLoop_apply
    (s : SpecialPeriods.CuspFamily.LogBase radius) (v : Lattice) (t : (unitInterval)) :
    nativeGlobalPeriodLoop s v t =
      SpecialPeriods.Threefold.inclusion (Option.some Option.none)
        (CuspUniformization.fibreCover data.correction radius s (cuspParameter_norm_lt s)
          ((t : ℝ) •
            (nativePeriodData s).periodVector (CuspUniformization.sourcePeriodCoordinates v))) := by
  exact
    (congrArg
          (fun x : (nativePeriodData s).Torus =>
            SpecialPeriods.Threefold.inclusion (Option.some Option.none) (nativeFibreMap s x))
          ((nativePeriodData s).periodLoop_apply (CuspUniformization.sourcePeriodCoordinates v)
            t)).trans
      (congrArg (SpecialPeriods.Threefold.inclusion (Option.some Option.none))
        (nativeFibreMap_mkQ s _))

private theorem SpecialPeriods.Threefold.CuspAttaching.quotientMap_nativePeriodVector
    (s : SpecialPeriods.CuspFamily.LogBase radius) (v : Lattice) (t : (unitInterval)) :
    regularData.periods.quotientMap
        (cuspLift s,
          (t : ℝ) •
            (nativePeriodData s).periodVector (CuspUniformization.sourcePeriodCoordinates v)) =
      (cuspLift s, standardLattice.mkQ ((t : ℝ) • Elliptic.realCast v)) := by
  have hs :
    (t : ℝ) • (nativePeriodData s).periodVector (CuspUniformization.sourcePeriodCoordinates v) =
      regularData.periods.periodEquiv (cuspLift s) ((t : ℝ) • Elliptic.realCast v) :=
    (congrArg (fun z : ComplexPlane₂ => (t : ℝ) • z)
          (native_periodVector_sourceCoordinates s v)).trans
      ((regularData.periods.periodEquiv (cuspLift s)).map_smul (t : ℝ) (Elliptic.realCast v)).symm
  change
    (cuspLift s,
        standardLattice.mkQ
          ((regularData.periods.periodEquiv (cuspLift s)).symm
            ((t : ℝ) •
              (nativePeriodData s).periodVector
                (CuspUniformization.sourcePeriodCoordinates v)))) =
      _
  apply congrArg (fun x : RealTorus₄ => (cuspLift s, x))
  apply congrArg standardLattice.mkQ
  exact
    (congrArg (regularData.periods.periodEquiv (cuspLift s)).symm hs).trans
      ((regularData.periods.periodEquiv (cuspLift s)).symm_apply_apply _)

private theorem SpecialPeriods.Threefold.CuspAttaching.nativeGlobalPeriodLoop_cast
    (s : SpecialPeriods.CuspFamily.LogBase radius) (v : Lattice) :
    (nativeGlobalPeriodLoop s v).cast (inclusion_nativeFibreMap_zero s).symm
        (inclusion_nativeFibreMap_zero s).symm =
      globalLatticeLoop (cuspLift s) v := by
  apply Path.ext
  funext t
  change nativeGlobalPeriodLoop s v t = globalLatticeLoop (cuspLift s) v t
  exact
    (nativeGlobalPeriodLoop_apply s v t).trans
      ((inclusion_fibreCover s _).trans
        ((congrArg
              (fun x => SpecialPeriods.Threefold.inclusion Option.none (regularData.quotient x))
              (quotientMap_nativePeriodVector s v t)).trans
          (globalLatticeLoop_apply (cuspLift s) v t).symm))

private theorem SpecialPeriods.Threefold.CuspAttaching.globalLatticeLoop_nullhomotopic_at_cusp
    (s : SpecialPeriods.CuspFamily.LogBase radius) (v : Lattice)
    (hv : CuspUniformization.cuspLatticeProjection v = 0) :
    Path.Homotopic (globalLatticeLoop (cuspLift s) v)
      (Path.refl
        (SpecialPeriods.Threefold.inclusion Option.none
          (regularData.fundamentalGroupBasepoint (cuspLift s)))) := by
  have h :=
    (nativeFibre_periodLoop_nullhomotopic_of_projection_zero s v hv).map
      (⟨SpecialPeriods.Threefold.inclusion (Option.some Option.none),
          (SpecialPeriods.Threefold.inclusion_openEmbedding
              (Option.some Option.none)).continuous⟩ :
        C(SpecialPeriods.Threefold.SpecialCuspPiece, SpecialPeriods.Threefold.Space))
  change
    Path.Homotopic (nativeGlobalPeriodLoop s v)
      (Path.refl
        (SpecialPeriods.Threefold.inclusion (Option.some Option.none) (nativeFibreMap s 0))) at h
  have hc :=
    h.pathCast (inclusion_nativeFibreMap_zero s).symm (inclusion_nativeFibreMap_zero s).symm
  have hr :
    (Path.refl
            (SpecialPeriods.Threefold.inclusion (Option.some Option.none)
              (nativeFibreMap s 0))).cast
        (inclusion_nativeFibreMap_zero s).symm (inclusion_nativeFibreMap_zero s).symm =
      Path.refl
        (SpecialPeriods.Threefold.inclusion Option.none
          (regularData.fundamentalGroupBasepoint (cuspLift s))) := by
    apply Path.ext
    funext _
    exact inclusion_nativeFibreMap_zero s
  rw [nativeGlobalPeriodLoop_cast, hr] at hc
  exact hc

private theorem SpecialPeriods.Threefold.CuspAttaching.globalLatticeHom_eq_one_at_cusp
    (s : SpecialPeriods.CuspFamily.LogBase radius) (v : Lattice)
    (hv : CuspUniformization.cuspLatticeProjection v = 0) :
    globalLatticeHom (cuspLift s) (Multiplicative.ofAdd v) = 1 := by
  rw [globalLatticeHom_periodLoop]
  exact Quotient.sound (globalLatticeLoop_nullhomotopic_at_cusp s v hv)

private def SpecialPeriods.Threefold.CuspAttaching.globalZeroSectionPath
    {b₀ b₁ : SpecialPeriods.TriangleRegularPoint} (p : Path b₀ b₁) :
    Path
      (SpecialPeriods.Threefold.inclusion Option.none (regularData.fundamentalGroupBasepoint b₀))
      (SpecialPeriods.Threefold.inclusion Option.none
        (regularData.fundamentalGroupBasepoint b₁)) :=
  (regularData.zeroSectionPath p).map regularFamilyInclusionMap.continuous

private theorem SpecialPeriods.Threefold.CuspAttaching.globalLatticeHom_baseChange
    {b₀ b₁ : SpecialPeriods.TriangleRegularPoint} (p : Path b₀ b₁) (v : Multiplicative Lattice) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath (globalZeroSectionPath p)
        (globalLatticeHom b₀ v) =
      globalLatticeHom b₁ v := by
  exact
    (fundamentalGroup_basepoint_naturality_apply regularFamilyInclusionMap
          (regularData.zeroSectionPath p) (regularData.latticeFundamentalGroupHom b₀ v)).trans
      (congrArg
        (FundamentalGroup.map regularFamilyInclusionMap
          (regularData.fundamentalGroupBasepoint b₁))
        (regularData.latticeFundamentalGroupHom_baseChange p v))

private theorem SpecialPeriods.Threefold.CuspAttaching.globalLatticeHom_eq_one_of_projection_zero
    (b : SpecialPeriods.TriangleRegularPoint) (v : Lattice)
    (hv : CuspUniformization.cuspLatticeProjection v = 0) :
    globalLatticeHom b (Multiplicative.ofAdd v) = 1 := by
  obtain ⟨s, hs⟩ := exists_small_exponential
  let s' : SpecialPeriods.CuspFamily.LogBase radius :=
    ⟨s, (SpecialPeriods.CuspFamily.mem_logBase radius s).mpr hs⟩
  let p : Path (cuspLift s') b := PathConnectedSpace.somePath _ _
  calc
    globalLatticeHom b (Multiplicative.ofAdd v) =
        FundamentalGroup.fundamentalGroupMulEquivOfPath (globalZeroSectionPath p)
          (globalLatticeHom (cuspLift s') (Multiplicative.ofAdd v)) :=
      (globalLatticeHom_baseChange p (Multiplicative.ofAdd v)).symm
    _ = FundamentalGroup.fundamentalGroupMulEquivOfPath (globalZeroSectionPath p) 1 :=
      (congrArg (FundamentalGroup.fundamentalGroupMulEquivOfPath (globalZeroSectionPath p))
        (globalLatticeHom_eq_one_at_cusp s' v hv))
    _ = 1 := map_one _

private theorem
    SpecialPeriods.Threefold.PiOne.latticeHom_eq_one_of_cusp_projection_zero (v : Lattice)
    (hv : CuspUniformization.cuspLatticeProjection v = 0) :
    latticeHom (Multiplicative.ofAdd v) = 1 :=
  SpecialPeriods.Threefold.CuspAttaching.globalLatticeHom_eq_one_of_projection_zero
    PeriodFamily.Meridians.normalizedRegularMeridianBasepoint v hv

private theorem
    SpecialPeriods.Threefold.PiOne.latticeHom_eq_one_of_cusp_monodromy_kernel (v : Lattice)
    (hv : (M₀ - 1) *ᵥ v = 0) : latticeHom (Multiplicative.ofAdd v) = 1 :=
  latticeHom_eq_one_of_cusp_projection_zero v
    ((CuspUniformization.cuspLatticeProjection_eq_zero_iff v).mpr hv)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace in
private def SpecialPeriods.Threefold.CuspPeripheral.planeToRegularBase :
    SpecialPeriods.Triangle.TwicePuncturedPlane → SpecialPeriods.Threefold.regularPatch :=
  SpecialPeriods.Threefold.regularBiholomorph ∘
    SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph.symm

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace in
private theorem SpecialPeriods.Threefold.CuspPeripheral.planeToRegularBase_continuous :
    Continuous planeToRegularBase :=
  SpecialPeriods.Threefold.regularBiholomorph.continuous.comp
    SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph.symm.continuous

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace in
private theorem SpecialPeriods.Threefold.CuspPeripheral.planeToRegularBase_eq_finiteInverse
    (z : SpecialPeriods.Triangle.TwicePuncturedPlane) :
    (planeToRegularBase z : SpecialPeriods.TriangleCompactifiedOrbitSpace) =
      SpecialPeriods.MuTorsor.Cover.finiteInverse
        SpecialPeriods.Triangle.triangleSphereUniformization (z : ℂ) := by
  apply SpecialPeriods.Triangle.triangleSphereUniformization.injective
  have hfinite :
    SpecialPeriods.Triangle.triangleSphereUniformization
        (planeToRegularBase z : SpecialPeriods.TriangleCompactifiedOrbitSpace) =
      ((z : ℂ) : RiemannSphere) := by
    change
      ((SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph
              (SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph.symm z) :
            ℂ) :
          RiemannSphere) =
        ((z : ℂ) : RiemannSphere)
    rw [SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph.apply_symm_apply]
  exact
    hfinite.trans
      (SpecialPeriods.MuTorsor.Cover.apply_finiteInverse
          SpecialPeriods.Triangle.triangleSphereUniformization (z : ℂ)).symm

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace in
private theorem SpecialPeriods.Threefold.CuspPeripheral.exists_cusp_exterior_bound :
    ∃ A : ℝ,
      0 < A ∧
        ∀ z : SpecialPeriods.Triangle.TwicePuncturedPlane,
          A ≤ ‖(z : ℂ)‖ →
            (planeToRegularBase z : SpecialPeriods.TriangleCompactifiedOrbitSpace) ∈
              SpecialPeriods.Threefold.specialBaseCover.fillingPatch Option.none := by
  obtain ⟨A, hA, hmem⟩ :=
    SpecialPeriods.MuTorsor.Cover.finitePullback_contains_exterior
      SpecialPeriods.Triangle.triangleSphereUniformization
      SpecialPeriods.Triangle.triangleSphereUniformization_cusp
      (SpecialPeriods.Threefold.specialBaseCover.fillingPatch Option.none)
      (SpecialPeriods.Threefold.specialBaseCover.point_mem_fillingPatch Option.none)
  refine ⟨A, hA, fun z hz => ?_⟩
  rw [planeToRegularBase_eq_finiteInverse]
  apply hmem
  simpa only [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] using hz

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace in
private theorem SpecialPeriods.Threefold.CuspPeripheral.exists_outerCircle_in_cusp :
    ∃ R : ℝ,
      ∃ hR : 2 ≤ R,
        ∀ t : unitInterval,
          (planeToRegularBase (SpecialPeriods.Triangle.outerPositiveCircle R hR t) :
              SpecialPeriods.TriangleCompactifiedOrbitSpace) ∈
            SpecialPeriods.Threefold.specialBaseCover.fillingPatch Option.none := by
  obtain ⟨A, _, hA⟩ := exists_cusp_exterior_bound
  let R : ℝ := Max.max 2 (A + 1)
  have hR : 2 ≤ R := le_max_left _ _
  refine ⟨R, hR, fun t => hA _ ?_⟩
  have hnorm := SpecialPeriods.Triangle.outerPositiveCircle_norm_lower_bound R hR t
  have hlarge : A + 1 ≤ R := le_max_right _ _
  linarith

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace in
private def SpecialPeriods.Threefold.CuspPeripheral.outerRadius : ℝ :=
  exists_outerCircle_in_cusp.choose

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace in
private theorem SpecialPeriods.Threefold.CuspPeripheral.outerRadius_ge_two : 2 ≤ outerRadius :=
  exists_outerCircle_in_cusp.choose_spec.choose

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace in
private def SpecialPeriods.Threefold.CuspPeripheral.outerRegularCircle :
    Path
      (planeToRegularBase
        (SpecialPeriods.Triangle.outerCircleBasepoint outerRadius outerRadius_ge_two))
      (planeToRegularBase
        (SpecialPeriods.Triangle.outerCircleBasepoint outerRadius outerRadius_ge_two)) :=
  (SpecialPeriods.Triangle.outerPositiveCircle outerRadius outerRadius_ge_two).map
    planeToRegularBase_continuous

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace in
private theorem
    SpecialPeriods.Threefold.CuspPeripheral.outerRegularCircle_mem_cusp (t : unitInterval) :
    (outerRegularCircle t : SpecialPeriods.TriangleCompactifiedOrbitSpace) ∈
      SpecialPeriods.Threefold.specialBaseCover.fillingPatch Option.none :=
  exists_outerCircle_in_cusp.choose_spec.choose_spec t

private def SpecialPeriods.Threefold.CuspPeripheral.planeSection :
    SpecialPeriods.Triangle.TwicePuncturedPlane → SpecialPeriods.Threefold.Space :=
  SpecialPeriods.Threefold.CuspAttaching.regularSection ∘ planeToRegularBase

private theorem SpecialPeriods.Threefold.CuspPeripheral.planeSection_continuous :
    Continuous planeSection :=
  SpecialPeriods.Threefold.CuspAttaching.regularSection_continuous.comp
    planeToRegularBase_continuous

private def SpecialPeriods.Threefold.CuspPeripheral.planeSectionMap :
    C(SpecialPeriods.Triangle.TwicePuncturedPlane, SpecialPeriods.Threefold.Space) :=
  ⟨planeSection, planeSection_continuous⟩

private theorem SpecialPeriods.Threefold.CuspPeripheral.outerPositiveCircle_section_nullhomotopic :
    Path.Homotopic
      ((SpecialPeriods.Triangle.outerPositiveCircle outerRadius outerRadius_ge_two).map
        planeSection_continuous)
      (Path.refl
        (planeSection
          (SpecialPeriods.Triangle.outerCircleBasepoint outerRadius outerRadius_ge_two))) := by
  have h :=
    SpecialPeriods.Threefold.CuspAttaching.regularSection_loop_nullhomotopic_of_mem
      outerRegularCircle outerRegularCircle_mem_cusp
  have heq :
    outerRegularCircle.map SpecialPeriods.Threefold.CuspAttaching.regularSection_continuous =
      (SpecialPeriods.Triangle.outerPositiveCircle outerRadius outerRadius_ge_two).map
        planeSection_continuous := by
    ext t
    rfl
  exact heq ▸ h

private theorem
    SpecialPeriods.Threefold.CuspPeripheral.positiveOuterMeridian_section_nullhomotopic :
    Path.Homotopic
      ((SpecialPeriods.Triangle.positiveOuterMeridian outerRadius outerRadius_ge_two).map
        planeSection_continuous)
      (Path.refl (planeSection SpecialPeriods.Triangle.meridianBasepoint)) := by
  let a :=
    (SpecialPeriods.Triangle.outerMeridianTail outerRadius outerRadius_ge_two).map
      planeSection_continuous
  let b :=
    (SpecialPeriods.Triangle.outerPositiveCircle outerRadius outerRadius_ge_two).map
      planeSection_continuous
  have hb :
    b.Homotopic
      (Path.refl
        (planeSection
          (SpecialPeriods.Triangle.outerCircleBasepoint outerRadius outerRadius_ge_two))) :=
    outerPositiveCircle_section_nullhomotopic
  have h₁ := ((Path.Homotopic.refl a).hcomp hb).hcomp (Path.Homotopic.refl a.symm)
  have h₂ := (Path.Homotopic.trans_refl a).hcomp (Path.Homotopic.refl a.symm)
  have h := h₁.trans (h₂.trans (Path.Homotopic.trans_symm a))
  simpa only [SpecialPeriods.Triangle.positiveOuterMeridian_eq_tail_circle_tail, Path.map_trans,
    ← Path.map_symm] using h

private theorem SpecialPeriods.Threefold.CuspPeripheral.planeSection_positiveOuterMeridian_eq_one :
    FundamentalGroup.map planeSectionMap SpecialPeriods.Triangle.meridianBasepoint
        (Path.Homotopic.Quotient.mk
          (SpecialPeriods.Triangle.positiveOuterMeridian outerRadius outerRadius_ge_two)) =
      1 :=
  Path.Homotopic.Quotient.eq.mpr positiveOuterMeridian_section_nullhomotopic

private theorem SpecialPeriods.Threefold.CuspPeripheral.planeSection_meridian_product_eq_one :
    FundamentalGroup.map planeSectionMap SpecialPeriods.Triangle.meridianBasepoint
          (SpecialPeriods.Triangle.meridianClass Bool.false) *
        FundamentalGroup.map planeSectionMap SpecialPeriods.Triangle.meridianBasepoint
          (SpecialPeriods.Triangle.meridianClass Bool.true) =
      1 := by
  rw [← map_mul, ←
    SpecialPeriods.Triangle.positiveOuterMeridian_class_eq outerRadius outerRadius_ge_two]
  exact planeSection_positiveOuterMeridian_eq_one

private theorem
    SpecialPeriods.Threefold.CuspPeripheral.planeSection_oriented_meridian_product_eq_one
    (reverse : Bool) :
    FundamentalGroup.map planeSectionMap SpecialPeriods.Triangle.meridianBasepoint
          (FreeMeridianMarking.orientedClass reverse Bool.false) *
        FundamentalGroup.map planeSectionMap SpecialPeriods.Triangle.meridianBasepoint
          (FreeMeridianMarking.orientedClass reverse Bool.true) =
      1 := by
  cases reverse with
  | false => exact planeSection_meridian_product_eq_one
  | true =>
    simp only [FreeMeridianMarking.orientedClass_true, map_inv]
    have h := planeSection_meridian_product_eq_one
    have hx := eq_inv_of_mul_eq_one_left h
    rw [hx, inv_inv, mul_inv_cancel]

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace in
private theorem SpecialPeriods.Threefold.PiOne.planeSection_regularCoordinate
    (q : SpecialPeriods.TriangleRegularQuotient) :
    SpecialPeriods.Threefold.CuspPeripheral.planeSection
        (SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph q) =
      SpecialPeriods.Threefold.regularFamilyInclusionMap
        (((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
              SpecialPeriods.specialPeriodMap_generator₁
              SpecialPeriods.specialPeriodMap_generator₂)).zeroSection
          q) := by
  change
    SpecialPeriods.Threefold.inclusion Option.none
        (((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
              SpecialPeriods.specialPeriodMap_generator₁
              SpecialPeriods.specialPeriodMap_generator₂)).zeroSection
          (SpecialPeriods.Threefold.regularBiholomorph.symm
            (SpecialPeriods.Threefold.regularBiholomorph
              (SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph.symm
                (SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph q))))) =
      SpecialPeriods.Threefold.inclusion Option.none
        (((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
              SpecialPeriods.specialPeriodMap_generator₁
              SpecialPeriods.specialPeriodMap_generator₂)).zeroSection
          q)
  rw [SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph.symm_apply_apply,
    SpecialPeriods.Threefold.regularBiholomorph.symm_apply_apply]

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace in
private theorem SpecialPeriods.Threefold.PiOne.planeSection_basepoint :
    SpecialPeriods.Threefold.CuspPeripheral.planeSectionMap
        SpecialPeriods.Triangle.meridianBasepoint =
      basepoint := by
  have h :=
    planeSection_regularCoordinate
      (SpecialPeriods.triangleRegularProject
        PeriodFamily.Meridians.normalizedRegularMeridianBasepoint)
  rw [PeriodFamily.Meridians.normalizedRegularMeridianBasepoint_coordinate] at h
  exact h

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace in
private def SpecialPeriods.Threefold.PiOne.pointedPlaneHom :
    FundamentalGroup SpecialPeriods.Triangle.TwicePuncturedPlane
        SpecialPeriods.Triangle.meridianBasepoint →*
      GlobalGroup :=
  FundamentalGroup.mapOfEq SpecialPeriods.Threefold.CuspPeripheral.planeSectionMap
    planeSection_basepoint

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace in
public
theorem SpecialPeriods.Threefold.PiOne.mapOfEq_eq_one_of_map_eq_one_mo1973_26295
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) {x : X} {y : Y}
    (e : f x = y) (g : FundamentalGroup X x) (h : FundamentalGroup.map f x g = 1) :
    FundamentalGroup.mapOfEq f e g = 1 := by
  subst y
  simpa only [FundamentalGroup.mapOfEq, CategoryTheory.eqToIso_refl, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, CategoryTheory.Iso.refl_conj] using h

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace in
private theorem
    SpecialPeriods.Threefold.PiOne.pointedPlaneHom_oriented_product_eq_one (reverse : Bool) :
    pointedPlaneHom (FreeMeridianMarking.orientedClass reverse Bool.false) *
        pointedPlaneHom (FreeMeridianMarking.orientedClass reverse Bool.true) =
      1 := by
  rw [← map_mul]
  apply mapOfEq_eq_one_of_map_eq_one_mo1973_26295
  rw [map_mul]
  exact
    SpecialPeriods.Threefold.CuspPeripheral.planeSection_oriented_meridian_product_eq_one reverse

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace in
private theorem SpecialPeriods.Threefold.PiOne.regularHom_section_eq_plane
    (g :
      FundamentalGroup SpecialPeriods.TriangleRegularQuotient
        (SpecialPeriods.triangleRegularProject
          PeriodFamily.Meridians.normalizedRegularMeridianBasepoint)) :
    regularHom (SpecialPeriods.Threefold.specialRegularFamilyMarkedSectionHom g) =
      pointedPlaneHom (PeriodFamily.Meridians.compatibleBasePlaneEquiv g) := by
  unfold pointedPlaneHom
  rw [PeriodFamily.Meridians.compatibleBasePlaneEquiv_apply, FundamentalGroup.mapOfEq_apply,
    FundamentalGroup.mapOfEq_apply]
  obtain ⟨p⟩ := g
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  exact (planeSection_regularCoordinate (p t)).symm

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace in
private theorem SpecialPeriods.Threefold.PiOne.meridian_eq_pointedPlane (b : Bool) :
    meridian b =
      pointedPlaneHom
        (FreeMeridianMarking.orientedClass PeriodFamily.Meridians.normalizationReversesMeridians
          b) := by
  rw [meridian, SpecialPeriods.Threefold.specialRegularFamilyMarkedMeridianClass_eq_section,
    regularHom_section_eq_plane, PeriodFamily.Meridians.compatibleBasePlaneEquiv_meridianClass]

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace in
private theorem SpecialPeriods.Threefold.PiOne.meridian_product_eq_one :
    meridian Bool.false * meridian Bool.true = 1 := by
  rw [meridian_eq_pointedPlane, meridian_eq_pointedPlane]
  exact
    pointedPlaneHom_oriented_product_eq_one PeriodFamily.Meridians.normalizationReversesMeridians

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace in
private theorem SpecialPeriods.Threefold.PiOne.meridian_second_eq_first_inv :
    meridian Bool.true = (meridian Bool.false)⁻¹ :=
  eq_inv_of_mul_eq_one_right meridian_product_eq_one

private def SpecialPeriods.Threefold.PiOne.c : GlobalGroup :=
  latticeHom (Multiplicative.ofAdd ε)

private theorem SpecialPeriods.Threefold.PiOne.latticeHom_eq_one_of_first_two_coordinates_zero
    (v : Lattice) (h₀ : v 0 = 0) (h₁ : v 1 = 0) : latticeHom (Multiplicative.ofAdd v) = 1 :=
  latticeHom_eq_one_of_cusp_monodromy_kernel v ((M₀_sub_one_kernel v).mpr ⟨h₀, h₁⟩)

private theorem SpecialPeriods.Threefold.PiOne.latticeHom_eq_c_zpow (v : Lattice) :
    latticeHom (Multiplicative.ofAdd v) = c ^ γ v :=
  LatticeCuspNormalClosure.image_eq_zpow_gamma latticeHom (meridian Bool.false)
    meridian_first_conjugation latticeHom_eq_one_of_first_two_coordinates_zero v

private theorem SpecialPeriods.Threefold.PiOne.c_mem_center : c ∈ Subgroup.center GlobalGroup := by
  apply
    LatticeCuspNormalClosure.image_epsilon_mem_center_of_hom_ext latticeHom (meridian Bool.false)
      (meridian Bool.true) meridian_first_conjugation meridian_second_conjugation
      latticeHom_eq_one_of_first_two_coordinates_zero
  intro f g hL hx hy
  apply hom_ext f g hL
  intro b
  cases b
  · exact hx
  · exact hy

private theorem SpecialPeriods.Threefold.PiOne.c_commute (g : GlobalGroup) : Commute c g :=
  (Subgroup.mem_center_iff.mp c_mem_center g).symm

private theorem SpecialPeriods.Threefold.PiOne.commute_all_of_marked_mo1973_26322
    (g : GlobalGroup) (hL : ∀ v : Multiplicative Lattice, Commute g (latticeHom v))
    (hM : ∀ b : Bool, Commute g (meridian b)) : ∀ h : GlobalGroup, Commute g h := by
  have heq : (MulAut.conj g).toMonoidHom = MonoidHom.id GlobalGroup := by
    apply hom_ext
    · intro v
      change g * latticeHom v * g⁻¹ = latticeHom v
      rw [(hL v).eq, mul_inv_cancel_right]
    · intro b
      change g * meridian b * g⁻¹ = meridian b
      rw [(hM b).eq, mul_inv_cancel_right]
  intro h
  have hh : g * h * g⁻¹ = h := DFunLike.congr_fun heq h
  exact (mul_inv_eq_iff_eq_mul).mp hh

private theorem SpecialPeriods.Threefold.PiOne.meridian_first_commute (g : GlobalGroup) :
    Commute (meridian Bool.false) g := by
  apply commute_all_of_marked_mo1973_26322 (meridian Bool.false)
  · intro v
    change Commute (meridian Bool.false) (latticeHom (Multiplicative.ofAdd v.toAdd))
    rw [latticeHom_eq_c_zpow]
    exact (c_commute (meridian Bool.false)).symm.zpow_right _
  · intro b
    cases b
    · exact Commute.refl _
    · rw [meridian_second_eq_first_inv]
      exact (Commute.refl (meridian Bool.false)).inv_right

private theorem SpecialPeriods.Threefold.PiOne.all_commute (g h : GlobalGroup) : Commute g h := by
  apply commute_all_of_marked_mo1973_26322 g
  · intro v
    change Commute g (latticeHom (Multiplicative.ofAdd v.toAdd))
    rw [latticeHom_eq_c_zpow]
    exact (c_commute g).symm.zpow_right _
  · intro b
    cases b
    · exact (meridian_first_commute g).symm
    · rw [meridian_second_eq_first_inv]
      exact (meridian_first_commute g).symm.inv_right

@[simp]
private theorem SpecialPeriods.Threefold.EllipticGeometry.attachingBaseSectionHom_compatibleMeridian
    (b : Bool) :
    attachingBaseSectionHom (PeriodFamily.Meridians.compatibleRegularMeridianClass b) =
      SpecialPeriods.Threefold.PiOne.meridian b :=
  rfl

private theorem
    SpecialPeriods.Threefold.EllipticGeometry.transportedAttachingClass_eq_oriented_meridian
    (j : Elliptic.Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr :
      ‖CuspUniformization.exponential s₀‖ ^ j.order <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j))
    (hsmall : ‖CuspUniformization.exponential s₀‖ ^ j.order < attachingMeridianRadius j) :
    transportedAttachingClass j s₀ hs₀ hr =
      if PeriodFamily.Meridians.normalizationReversesMeridians then
        SpecialPeriods.Threefold.PiOne.meridian (attachingMeridianIndex j)
      else (SpecialPeriods.Threefold.PiOne.meridian (attachingMeridianIndex j))⁻¹ := by
  rw [transportedAttachingClass_eq_baseImage]
  have h :=
    attachingMeridian_map_whisker j s₀ hs₀ hr hsmall (attachingBaseTail j s₀ hs₀)
      attachingBaseSectionHom SpecialPeriods.Threefold.PiOne.all_commute
  simpa only [transportedAttachingBaseLoop, attachingBaseSectionHom_compatibleMeridian] using! h

private theorem
  SpecialPeriods.Threefold.EllipticGeometry.chosenTransportedAttachingClass_eq_oriented_meridian
    (j : Elliptic.Kind) :
    transportedAttachingClass j (chosenAttachingParameter j) (chosenAttachingParameter_im_pos j)
        (chosenAttachingParameter_filling_bound j) =
      if PeriodFamily.Meridians.normalizationReversesMeridians then
        SpecialPeriods.Threefold.PiOne.meridian (attachingMeridianIndex j)
      else (SpecialPeriods.Threefold.PiOne.meridian (attachingMeridianIndex j))⁻¹ :=
  transportedAttachingClass_eq_oriented_meridian j (chosenAttachingParameter j)
    (chosenAttachingParameter_im_pos j) (chosenAttachingParameter_filling_bound j)
    (chosenAttachingParameter_bound j)

private theorem SpecialPeriods.Threefold.EllipticGeometry.clockwise_meridian_pow_order
    (j : Elliptic.Kind) :
    (if PeriodFamily.Meridians.normalizationReversesMeridians then
          SpecialPeriods.Threefold.PiOne.meridian (attachingMeridianIndex j)
        else (SpecialPeriods.Threefold.PiOne.meridian (attachingMeridianIndex j))⁻¹) ^
        j.order =
      SpecialPeriods.Threefold.PiOne.latticeHom (Multiplicative.ofAdd j.twist) := by
  have h :=
    transportedAttachingClass_pow_order j (chosenAttachingParameter j)
      (chosenAttachingParameter_im_pos j) (chosenAttachingParameter_filling_bound j)
  rwa [chosenTransportedAttachingClass_eq_oriented_meridian] at h

private def SpecialPeriods.Threefold.PiOne.orientedCentral (reverse : Bool) : GlobalGroup :=
  if reverse then c else c⁻¹

private theorem SpecialPeriods.Threefold.PiOne.orientedCentral_commute (reverse : Bool)
    (g : GlobalGroup) : Commute (orientedCentral reverse) g :=
  all_commute _ _

private theorem SpecialPeriods.Threefold.PiOne.c_eq_one_of_orientedCentral_eq_one (reverse : Bool)
    (h : orientedCentral reverse = 1) : c = 1 := by
  cases reverse with
  | false => exact inv_eq_one.mp h
  | true => exact h

private theorem SpecialPeriods.Threefold.PiOne.trivial_of_oriented_elliptic_power_relations
    (reverse : Bool) (h₃ : meridian Bool.false ^ 3 = orientedCentral reverse)
    (h₄ : meridian Bool.true ^ 4 = (orientedCentral reverse)⁻¹) : ∀ g : GlobalGroup, g = 1 := by
  have hgen :=
    TwistGroup.main_realization_generators_eq_one (orientedCentral reverse) (meridian Bool.false)
      (meridian Bool.true) (orientedCentral_commute reverse _) (orientedCentral_commute reverse _)
      meridian_product_eq_one h₃ h₄
  have hc : c = 1 := c_eq_one_of_orientedCentral_eq_one reverse hgen.1
  have hid : MonoidHom.id GlobalGroup = 1 := by
    apply hom_eq_one
    · intro v
      change latticeHom (Multiplicative.ofAdd v.toAdd) = 1
      rw [latticeHom_eq_c_zpow, hc, one_zpow]
    · intro b
      cases b
      · exact hgen.2.1
      · exact hgen.2.2
  intro g
  exact DFunLike.congr_fun hid g

private theorem SpecialPeriods.Threefold.PiOne.meridian_pow_order (j : Elliptic.Kind) :
    meridian (SpecialPeriods.Threefold.EllipticGeometry.attachingMeridianIndex j) ^ j.order =
      orientedCentral PeriodFamily.Meridians.normalizationReversesMeridians ^ γ j.twist := by
  have h := SpecialPeriods.Threefold.EllipticGeometry.clockwise_meridian_pow_order j
  rw [latticeHom_eq_c_zpow] at h
  cases hreverse : PeriodFamily.Meridians.normalizationReversesMeridians with
  |
    false =>
    have hinv :
      meridian (SpecialPeriods.Threefold.EllipticGeometry.attachingMeridianIndex j) ^ j.order =
        (c ^ γ j.twist)⁻¹ := by
      simpa only [hreverse, Bool.false_eq_true, ↓reduceIte, inv_pow, inv_inv] using
        congrArg (fun g : GlobalGroup => g⁻¹) h
    simpa only [orientedCentral, hreverse, Bool.false_eq_true, ↓reduceIte, inv_zpow] using hinv
  | true => simpa only [orientedCentral, hreverse, ↓reduceIte] using h

private theorem SpecialPeriods.Threefold.PiOne.meridian_first_cube :
    meridian Bool.false ^ 3 =
      orientedCentral PeriodFamily.Meridians.normalizationReversesMeridians := by
  have h := meridian_pow_order Elliptic.Kind.three
  change
    meridian Bool.false ^ 3 =
      orientedCentral PeriodFamily.Meridians.normalizationReversesMeridians ^ (1 : ℤ) at h
  simpa only [zpow_one] using h

private theorem SpecialPeriods.Threefold.PiOne.meridian_second_fourth :
    meridian Bool.true ^ 4 =
      (orientedCentral PeriodFamily.Meridians.normalizationReversesMeridians)⁻¹ := by
  have h := meridian_pow_order Elliptic.Kind.four
  change
    meridian Bool.true ^ 4 =
      orientedCentral PeriodFamily.Meridians.normalizationReversesMeridians ^ (-1 : ℤ) at h
  simpa only [zpow_neg_one] using h

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.space_isManifold SpecialPeriods.Threefold.space_connected in
private theorem SpecialPeriods.Threefold.space_isRealAnalyticManifold :
    IsManifold 𝓘(ℝ, ℂ × ComplexPlane₂) ω Space :=
  complexManifold_isRealManifold Space ω

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.space_isManifold SpecialPeriods.Threefold.space_connected in
private theorem SpecialPeriods.Threefold.space_isSmoothRealManifold :
    IsManifold 𝓘(ℝ, ℂ × ComplexPlane₂) ∞ Space := by
  let := space_isRealAnalyticManifold
  infer_instance

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.space_isManifold SpecialPeriods.Threefold.space_connected in
private theorem
    SpecialPeriods.Threefold.real_dimension : Module.finrank ℝ (ℂ × ComplexPlane₂) = 6 := by
  simp [ComplexPlane₂, Module.finrank_prod, Module.finrank_pi_fintype]

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.space_isManifold SpecialPeriods.Threefold.space_connected in
private theorem
    SpecialPeriods.Threefold.space_locallyPathConnected : LocallyPathConnectedSpace Space :=
  ChartedSpace.locallyPathConnectedSpace (ℂ × ComplexPlane₂) Space

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.space_isManifold SpecialPeriods.Threefold.space_connected in
private theorem SpecialPeriods.Threefold.space_pathConnected : PathConnectedSpace Space := by
  let := space_locallyPathConnected
  exact pathConnectedSpace_iff_connectedSpace.mpr space_connected

private theorem SpecialPeriods.Threefold.PiOne.trivial (g : GlobalGroup) : g = 1 :=
  trivial_of_oriented_elliptic_power_relations
    PeriodFamily.Meridians.normalizationReversesMeridians meridian_first_cube
    meridian_second_fourth g

private theorem SpecialPeriods.Threefold.space_simplyConnected : SimplyConnectedSpace Space := by
  have := space_pathConnected
  exact simplyConnectedSpace_of_fundamentalGroup_eq_one PiOne.basepoint PiOne.trivial

private theorem SpecialPeriods.Threefold.space_paths_homotopic {x y : Space} (p q : Path x y) :
    Path.Homotopic p q := by
  have := space_simplyConnected
  exact SimplyConnectedSpace.paths_homotopic p q

private theorem SpecialPeriods.Threefold.space_loops_nullhomotopic {x : Space} (p : Path x x) :
    Path.Homotopic p (Path.refl x) :=
  space_paths_homotopic p (Path.refl x)

private def SpecialPeriods.Threefold.LowDegrees.singularH0Equiv :
    SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 0 ≃ₗ[ℤ] ℤ := by
  have := SpecialPeriods.Threefold.space_pathConnected
  exact PeriodTorusHigherHomology.connectedHomologyZeroEquiv SpecialPeriods.Threefold.Space

private theorem SpecialPeriods.Threefold.LowDegrees.singularH1_eq_zero
    (a : SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 1) : a = 0 := by
  have := SpecialPeriods.Threefold.space_pathConnected
  obtain ⟨p, hp⟩ :=
    FirstHurewicz.loopHomologyClass_surjective SpecialPeriods.Threefold.PiOne.basepoint a
  exact
    hp.symm.trans
      ((FirstHurewicz.loopHomologyClass_homotopic
            (SpecialPeriods.Threefold.space_loops_nullhomotopic p)).trans
        (FirstHurewicz.loopHomologyClass_refl SpecialPeriods.Threefold.PiOne.basepoint))

private theorem SpecialPeriods.Threefold.LowDegrees.singularH1_subsingleton :
    Subsingleton (SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 1) :=
  ⟨fun a b => (singularH1_eq_zero a).trans (singularH1_eq_zero b).symm⟩

attribute [local instance] SpecialPeriods.Threefold.localPieceChartedSpace in
private theorem SpecialPeriods.Threefold.VerticalAction.Gluing.localFlow_mem_overlap
    (F :
      ∀ i : SpecialPeriods.Threefold.Index,
        ℂ → SpecialPeriods.Threefold.localPiece i → SpecialPeriods.Threefold.localPiece i)
    (hbase :
      ∀ i s x,
        SpecialPeriods.Threefold.localProjectionToBase i (F i s x) =
          SpecialPeriods.Threefold.localProjectionToBase i x)
    (i : SpecialPeriods.Threefold.Puncture) (s : ℂ)
    (x : SpecialPeriods.Threefold.localPiece (Option.some i))
    (hx : x ∈ (SpecialPeriods.Threefold.localOverlap i).source) :
    F (Option.some i) s x ∈ (SpecialPeriods.Threefold.localOverlap i).source := by
  rw [SpecialPeriods.Threefold.localOverlap_source] at hx ⊢
  change
    SpecialPeriods.Threefold.localProjectionToBase (Option.some i) (F (Option.some i) s x) ∈
      SpecialPeriods.Threefold.specialBaseCover.patch Option.none
  rw [hbase]
  exact hx

attribute [local instance] SpecialPeriods.Threefold.localPieceChartedSpace in
private theorem SpecialPeriods.Threefold.VerticalAction.Gluing.inclusion_localOverlap
    (i : SpecialPeriods.Threefold.Puncture)
    (x : SpecialPeriods.Threefold.localPiece (Option.some i))
    (hx : x ∈ (SpecialPeriods.Threefold.localOverlap i).source) :
    SpecialPeriods.Threefold.inclusion Option.none (SpecialPeriods.Threefold.localOverlap i x) =
      SpecialPeriods.Threefold.inclusion (Option.some i) x :=
  ((SpecialPeriods.Threefold.gluingData.inclusion_eq_iff (Option.some i) Option.none x
          (SpecialPeriods.Threefold.localOverlap i x)).mpr
      ⟨hx, rfl⟩).symm

attribute [local instance] SpecialPeriods.Threefold.localPieceChartedSpace in
private theorem SpecialPeriods.Threefold.VerticalAction.Gluing.compatible
    (F :
      ∀ i : SpecialPeriods.Threefold.Index,
        ℂ → SpecialPeriods.Threefold.localPiece i → SpecialPeriods.Threefold.localPiece i)
    (hbase :
      ∀ i s x,
        SpecialPeriods.Threefold.localProjectionToBase i (F i s x) =
          SpecialPeriods.Threefold.localProjectionToBase i x)
    (hoverlap :
      ∀ i s x,
        x ∈ (SpecialPeriods.Threefold.localOverlap i).source →
          SpecialPeriods.Threefold.localOverlap i (F (Option.some i) s x) =
            F Option.none s (SpecialPeriods.Threefold.localOverlap i x))
    (s : ℂ) :
    SpecialPeriods.Threefold.gluingData.Compatible
      (fun i x => SpecialPeriods.Threefold.inclusion i (F i s x)) := by
  intro i j x hx
  by_cases hij : i = j
  · subst j
    change
      SpecialPeriods.Threefold.inclusion i
          (F i s (SpecialPeriods.Threefold.gluingData.transition i i x)) =
        SpecialPeriods.Threefold.inclusion i (F i s x)
    rw [SpecialPeriods.Threefold.gluingData.self_eq]
    rfl
  · cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j =>
        change x ∈ (SpecialPeriods.Threefold.localOverlap j).target at hx
        change
          SpecialPeriods.Threefold.inclusion (Option.some j)
              (F (Option.some j) s ((SpecialPeriods.Threefold.localOverlap j).symm x)) =
            SpecialPeriods.Threefold.inclusion Option.none (F Option.none s x)
        have hy := (SpecialPeriods.Threefold.localOverlap j).map_target hx
        calc
          SpecialPeriods.Threefold.inclusion (Option.some j)
                (F (Option.some j) s ((SpecialPeriods.Threefold.localOverlap j).symm x)) =
              SpecialPeriods.Threefold.inclusion Option.none
                (SpecialPeriods.Threefold.localOverlap j
                  (F (Option.some j) s ((SpecialPeriods.Threefold.localOverlap j).symm x))) :=
            (inclusion_localOverlap j _ (localFlow_mem_overlap F hbase j s _ hy)).symm
          _ =
              SpecialPeriods.Threefold.inclusion Option.none
                (F Option.none s
                  (SpecialPeriods.Threefold.localOverlap j
                    ((SpecialPeriods.Threefold.localOverlap j).symm x))) :=
            (congrArg (SpecialPeriods.Threefold.inclusion Option.none) (hoverlap j s _ hy))
          _ = SpecialPeriods.Threefold.inclusion Option.none (F Option.none s x) :=
            congrArg (fun y => SpecialPeriods.Threefold.inclusion Option.none (F Option.none s y))
              ((SpecialPeriods.Threefold.localOverlap j).right_inv hx)
    | some i =>
      cases j with
      | none =>
        change x ∈ (SpecialPeriods.Threefold.localOverlap i).source at hx
        change
          SpecialPeriods.Threefold.inclusion Option.none
              (F Option.none s (SpecialPeriods.Threefold.localOverlap i x)) =
            SpecialPeriods.Threefold.inclusion (Option.some i) (F (Option.some i) s x)
        rw [← hoverlap i s x hx]
        exact inclusion_localOverlap i _ (localFlow_mem_overlap F hbase i s x hx)
      | some j =>
        have hij' : i ≠ j := fun h => hij (congrArg Option.some h)
        change
          x ∈
            (SpecialPeriods.Threefold.gluingStar.transition (Option.some i)
                (Option.some j)).source at hx
        rw [SpecialPeriods.Threefold.gluingStar.transition_some_some_source_eq_empty hij'] at hx
        exact hx.elim

attribute [local instance] SpecialPeriods.Threefold.localPieceChartedSpace in
private def SpecialPeriods.Threefold.VerticalAction.Gluing.glue
    (F :
      ∀ i : SpecialPeriods.Threefold.Index,
        ℂ → SpecialPeriods.Threefold.localPiece i → SpecialPeriods.Threefold.localPiece i)
    (hbase :
      ∀ i s x,
        SpecialPeriods.Threefold.localProjectionToBase i (F i s x) =
          SpecialPeriods.Threefold.localProjectionToBase i x)
    (hoverlap :
      ∀ i s x,
        x ∈ (SpecialPeriods.Threefold.localOverlap i).source →
          SpecialPeriods.Threefold.localOverlap i (F (Option.some i) s x) =
            F Option.none s (SpecialPeriods.Threefold.localOverlap i x))
    (s : ℂ) : SpecialPeriods.Threefold.Space → SpecialPeriods.Threefold.Space :=
  SpecialPeriods.Threefold.gluingData.descend
    (fun i x => SpecialPeriods.Threefold.inclusion i (F i s x)) (compatible F hbase hoverlap s)

attribute [local instance] SpecialPeriods.Threefold.localPieceChartedSpace in
@[simp]
private theorem SpecialPeriods.Threefold.VerticalAction.Gluing.glue_inclusion
    (F :
      ∀ i : SpecialPeriods.Threefold.Index,
        ℂ → SpecialPeriods.Threefold.localPiece i → SpecialPeriods.Threefold.localPiece i)
    (hbase :
      ∀ i s x,
        SpecialPeriods.Threefold.localProjectionToBase i (F i s x) =
          SpecialPeriods.Threefold.localProjectionToBase i x)
    (hoverlap :
      ∀ i s x,
        x ∈ (SpecialPeriods.Threefold.localOverlap i).source →
          SpecialPeriods.Threefold.localOverlap i (F (Option.some i) s x) =
            F Option.none s (SpecialPeriods.Threefold.localOverlap i x))
    (s : ℂ) (i : SpecialPeriods.Threefold.Index) (x : SpecialPeriods.Threefold.localPiece i) :
    glue F hbase hoverlap s (SpecialPeriods.Threefold.inclusion i x) =
      SpecialPeriods.Threefold.inclusion i (F i s x) :=
  SpecialPeriods.Threefold.gluingData.descend_inclusion _ (compatible F hbase hoverlap s) i x

attribute [local instance] SpecialPeriods.Threefold.localPieceChartedSpace in
private theorem SpecialPeriods.Threefold.VerticalAction.Gluing.glue_projection
    (F :
      ∀ i : SpecialPeriods.Threefold.Index,
        ℂ → SpecialPeriods.Threefold.localPiece i → SpecialPeriods.Threefold.localPiece i)
    (hbase :
      ∀ i s x,
        SpecialPeriods.Threefold.localProjectionToBase i (F i s x) =
          SpecialPeriods.Threefold.localProjectionToBase i x)
    (hoverlap :
      ∀ i s x,
        x ∈ (SpecialPeriods.Threefold.localOverlap i).source →
          SpecialPeriods.Threefold.localOverlap i (F (Option.some i) s x) =
            F Option.none s (SpecialPeriods.Threefold.localOverlap i x))
    (s : ℂ) (x : SpecialPeriods.Threefold.Space) :
    SpecialPeriods.Threefold.projection (glue F hbase hoverlap s x) =
      SpecialPeriods.Threefold.projection x := by
  obtain ⟨i, x, rfl⟩ := SpecialPeriods.Threefold.gluingData.inclusion_jointly_surjective x
  rw [glue_inclusion, SpecialPeriods.Threefold.projection_inclusion,
    SpecialPeriods.Threefold.projection_inclusion, hbase]

attribute [local instance] SpecialPeriods.Threefold.localPieceChartedSpace in
private theorem SpecialPeriods.Threefold.VerticalAction.Gluing.glue_zero
    (F :
      ∀ i : SpecialPeriods.Threefold.Index,
        ℂ → SpecialPeriods.Threefold.localPiece i → SpecialPeriods.Threefold.localPiece i)
    (hbase :
      ∀ i s x,
        SpecialPeriods.Threefold.localProjectionToBase i (F i s x) =
          SpecialPeriods.Threefold.localProjectionToBase i x)
    (hoverlap :
      ∀ i s x,
        x ∈ (SpecialPeriods.Threefold.localOverlap i).source →
          SpecialPeriods.Threefold.localOverlap i (F (Option.some i) s x) =
            F Option.none s (SpecialPeriods.Threefold.localOverlap i x))
    (hzero : ∀ i x, F i 0 x = x) (x : SpecialPeriods.Threefold.Space) :
    glue F hbase hoverlap 0 x = x := by
  obtain ⟨i, x, rfl⟩ := SpecialPeriods.Threefold.gluingData.inclusion_jointly_surjective x
  rw [glue_inclusion, hzero]

attribute [local instance] SpecialPeriods.Threefold.localPieceChartedSpace in
private theorem SpecialPeriods.Threefold.VerticalAction.Gluing.glue_add
    (F :
      ∀ i : SpecialPeriods.Threefold.Index,
        ℂ → SpecialPeriods.Threefold.localPiece i → SpecialPeriods.Threefold.localPiece i)
    (hbase :
      ∀ i s x,
        SpecialPeriods.Threefold.localProjectionToBase i (F i s x) =
          SpecialPeriods.Threefold.localProjectionToBase i x)
    (hoverlap :
      ∀ i s x,
        x ∈ (SpecialPeriods.Threefold.localOverlap i).source →
          SpecialPeriods.Threefold.localOverlap i (F (Option.some i) s x) =
            F Option.none s (SpecialPeriods.Threefold.localOverlap i x))
    (hadd : ∀ i s t x, F i (s + t) x = F i s (F i t x)) (s t : ℂ)
    (x : SpecialPeriods.Threefold.Space) :
    glue F hbase hoverlap (s + t) x = glue F hbase hoverlap s (glue F hbase hoverlap t x) := by
  obtain ⟨i, x, rfl⟩ := SpecialPeriods.Threefold.gluingData.inclusion_jointly_surjective x
  rw [glue_inclusion, glue_inclusion, glue_inclusion, hadd]

attribute [local instance] SpecialPeriods.Threefold.localPieceChartedSpace in
private theorem SpecialPeriods.Threefold.VerticalAction.Gluing.glue_int_cast
    (F :
      ∀ i : SpecialPeriods.Threefold.Index,
        ℂ → SpecialPeriods.Threefold.localPiece i → SpecialPeriods.Threefold.localPiece i)
    (hbase :
      ∀ i s x,
        SpecialPeriods.Threefold.localProjectionToBase i (F i s x) =
          SpecialPeriods.Threefold.localProjectionToBase i x)
    (hoverlap :
      ∀ i s x,
        x ∈ (SpecialPeriods.Threefold.localOverlap i).source →
          SpecialPeriods.Threefold.localOverlap i (F (Option.some i) s x) =
            F Option.none s (SpecialPeriods.Threefold.localOverlap i x))
    (hint : ∀ i (n : ℤ) x, F i (n : ℂ) x = x) (n : ℤ) (x : SpecialPeriods.Threefold.Space) :
    glue F hbase hoverlap (n : ℂ) x = x := by
  obtain ⟨i, x, rfl⟩ := SpecialPeriods.Threefold.gluingData.inclusion_jointly_surjective x
  rw [glue_inclusion, hint]

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace in
private theorem SpecialPeriods.Threefold.VerticalAction.Gluing.inclusion_isLocalDiffeomorph
    (i : SpecialPeriods.Threefold.Index) :
    IsLocalDiffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (SpecialPeriods.Threefold.inclusion i) := by
  intro x
  exact
    ((SpecialPeriods.Threefold.patchBiholomorph i).isLocalDiffeomorph x).comp (K :=
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))) (P := SpecialPeriods.Threefold.Space)
      (isLocalDiffeomorph_subtypeVal (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
        (SpecialPeriods.Threefold.liftedPatch i) (SpecialPeriods.Threefold.patchBiholomorph i x))

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace in
private theorem SpecialPeriods.Threefold.VerticalAction.Gluing.holomorphic_of_comp_patchLine
    (f : SpecialPeriods.Threefold.Space × ℂ → SpecialPeriods.Threefold.Space)
    (hf :
      ∀ i,
        ContMDiff (((modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))).prod (modelWithCornersSelf ℂ ℂ))
          (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω
          (fun p : SpecialPeriods.Threefold.localPiece i × ℂ =>
            f (SpecialPeriods.Threefold.inclusion i p.1, p.2))) :
    ContMDiff (((modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))).prod (modelWithCornersSelf ℂ ℂ))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω f := by
  rintro ⟨y, s⟩
  obtain ⟨i, x, rfl⟩ := SpecialPeriods.Threefold.gluingData.inclusion_jointly_surjective y
  let q : SpecialPeriods.Threefold.localPiece i × ℂ → SpecialPeriods.Threefold.Space × ℂ :=
    fun p => (SpecialPeriods.Threefold.inclusion i p.1, p.2)
  have hq :
    IsLocalDiffeomorphAt
      (((modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))).prod (modelWithCornersSelf ℂ ℂ))
      (((modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))).prod (modelWithCornersSelf ℂ ℂ)) ω q
      (x, s) :=
    CanonicalProduct.isLocalDiffeomorphAt_prodLine (inclusion_isLocalDiffeomorph i x)
  have hc :
    ContMDiff (((modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))).prod (modelWithCornersSelf ℂ ℂ))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (f ∘ q) :=
    hf i
  have hh := hc.contMDiffAt.comp (q (x, s)) hq.localInverse_contMDiffAt
  apply hh.congr_of_eventuallyEq
  filter_upwards [hq.localInverse_eventuallyEq_right] with z hz
  change f z = f (q (hq.localInverse z))
  exact (congrArg f hz).symm

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace in
private theorem SpecialPeriods.Threefold.VerticalAction.Gluing.glue_joint_holomorphic
    (F :
      ∀ i : SpecialPeriods.Threefold.Index,
        ℂ → SpecialPeriods.Threefold.localPiece i → SpecialPeriods.Threefold.localPiece i)
    (hbase :
      ∀ i s x,
        SpecialPeriods.Threefold.localProjectionToBase i (F i s x) =
          SpecialPeriods.Threefold.localProjectionToBase i x)
    (hoverlap :
      ∀ i s x,
        x ∈ (SpecialPeriods.Threefold.localOverlap i).source →
          SpecialPeriods.Threefold.localOverlap i (F (Option.some i) s x) =
            F Option.none s (SpecialPeriods.Threefold.localOverlap i x))
    (hF :
      ∀ i,
        ContMDiff (((modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))).prod (modelWithCornersSelf ℂ ℂ))
          (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω
          (fun p : SpecialPeriods.Threefold.localPiece i × ℂ => F i p.2 p.1)) :
    ContMDiff (((modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))).prod (modelWithCornersSelf ℂ ℂ))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω
      (fun p : SpecialPeriods.Threefold.Space × ℂ => glue F hbase hoverlap p.2 p.1) := by
  apply holomorphic_of_comp_patchLine
  intro i
  simp_rw [glue_inclusion]
  exact (SpecialPeriods.Threefold.inclusion_holomorphic i).comp (hF i)

private def
    SpecialPeriods.Threefold.VerticalAction.Cusp.multiplier (s : ℂ) : ToricSpace.ActingTorus :=
  ToricSpace.fibreMultiplier
    ![1, Units.mk0 (Complex.exp (2 * Real.pi * Complex.I * s)) (Complex.exp_ne_zero _)]

@[simp]
private theorem
    SpecialPeriods.Threefold.VerticalAction.Cusp.multiplier_zero : multiplier 0 = 1 := by
  ext i
  fin_cases i <;> simp [multiplier, ToricSpace.fibreMultiplier]

private theorem SpecialPeriods.Threefold.VerticalAction.Cusp.multiplier_add (s t : ℂ) :
    multiplier (s + t) = multiplier s * multiplier t := by
  ext i
  fin_cases i <;> simp [multiplier, ToricSpace.fibreMultiplier, mul_add, Complex.exp_add]

@[simp]
private theorem SpecialPeriods.Threefold.VerticalAction.Cusp.multiplier_int_cast (n : ℤ) :
    multiplier (n : ℂ) = 1 := by
  have he : Complex.exp (2 * Real.pi * Complex.I * (n : ℂ)) = 1 := by
    simpa only [mul_comm] using Complex.exp_int_mul_two_pi_mul_I n
  ext i
  fin_cases i <;> simp [multiplier, ToricSpace.fibreMultiplier, he]

private def SpecialPeriods.Threefold.VerticalAction.Cusp.toricFlow (s : ℂ) :
    ToricSpace.Space → ToricSpace.Space :=
  ToricSpace.torusAction (multiplier s)

@[simp]
private theorem SpecialPeriods.Threefold.VerticalAction.Cusp.toricFlow_zero (x : ToricSpace.Space) :
    toricFlow 0 x = x := by simp [toricFlow]

private theorem SpecialPeriods.Threefold.VerticalAction.Cusp.toricFlow_add (s t : ℂ)
    (x : ToricSpace.Space) : toricFlow (s + t) x = toricFlow s (toricFlow t x) := by
  simp only [toricFlow, multiplier_add, ToricSpace.torusAction_mul]

@[simp]
private theorem SpecialPeriods.Threefold.VerticalAction.Cusp.toricFlow_int_cast (n : ℤ)
    (x : ToricSpace.Space) : toricFlow (n : ℂ) x = x := by simp [toricFlow]

@[simp]
private theorem SpecialPeriods.Threefold.VerticalAction.Cusp.toricFlow_time (s : ℂ)
    (x : ToricSpace.Space) : ToricSpace.time (toricFlow s x) = ToricSpace.time x := by
  exact ToricSpace.time_fibreMultiplier _ x

@[simp]
private theorem SpecialPeriods.Threefold.VerticalAction.Cusp.toricFlow_inclusion (s : ℂ)
    (a : ToricFan.Triangle) (z : ToricCharts.CoordinateSpace 3) :
    toricFlow s (ToricSpace.inclusion a z) =
      ToricSpace.inclusion a (ToricSpace.scale a (multiplier s) z) :=
  ToricSpace.torusAction_inclusion _ _ _

private theorem SpecialPeriods.Threefold.VerticalAction.Cusp.multiplier_holomorphic :
    ContDiff ℂ ω (fun s : ℂ => fun i => (multiplier s i : ℂ)) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_const
  · exact (contDiff_const.mul contDiff_id).cexp
  · exact contDiff_const

private theorem SpecialPeriods.Threefold.VerticalAction.Cusp.multiplier_factors_holomorphic
    (a : ToricFan.Triangle) : ContDiff ℂ ω (fun s => ToricSpace.factors a (multiplier s)) := by
  apply contDiffOn_univ.mp
  exact
    (ToricCharts.monomial_contDiffOn a.dual ω).comp multiplier_holomorphic.contDiffOn
      (fun s _ => ToricCharts.torus_subset_domain _ (fun i => (multiplier s i).ne_zero))

private theorem SpecialPeriods.Threefold.VerticalAction.Cusp.toricFlow_scale_joint_holomorphic
    (a : ToricFan.Triangle) :
    ContDiff ℂ ω
      (fun p : ℂ × ToricCharts.CoordinateSpace 3 => ToricSpace.scale a (multiplier p.1) p.2) :=
  ((multiplier_factors_holomorphic a).comp contDiff_fst).mul contDiff_snd

private theorem
  SpecialPeriods.Threefold.VerticalAction.Cusp.toricFlow_scale_joint_contMDiff_mo1973_28674
    (a : ToricFan.Triangle) :
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω
      (fun q : ℂ × ToricCharts.CoordinateSpace 3 => ToricSpace.scale a (multiplier q.1) q.2) :=
  (toricFlow_scale_joint_holomorphic a).contMDiff

private theorem
  SpecialPeriods.Threefold.VerticalAction.Cusp.toricChartInverse_holomorphic_mo1973_28675
    (a : ToricFan.Triangle) (x : ToricSpace.Space)
    (hx : x ∈ (ToricSpace.parametrization a).target) :
    ContMDiffAt (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω
      (ToricSpace.parametrization a).symm x := by
  have he :
    (ToricSpace.parametrization a).symm ∈
      IsManifold.maximalAtlas (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω
        ToricSpace.Space :=
    IsManifold.subset_maximalAtlas (Set.mem_range_self a)
  exact contMDiffAt_of_mem_maximalAtlas he hx

private theorem
  SpecialPeriods.Threefold.VerticalAction.Cusp.toricFlow_local_coordinates_holomorphic_mo1973_28676
    (a : ToricFan.Triangle) (p : ℂ × ToricSpace.Space)
    (hp : p.2 ∈ (ToricSpace.parametrization a).target) :
    ContMDiffAt
      (((modelWithCornersSelf ℂ ℂ)).prod (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)))
      (modelWithCornersSelf ℂ (ℂ × ToricCharts.CoordinateSpace 3)) ω
      (fun q : ℂ × ToricSpace.Space => (q.1, (ToricSpace.parametrization a).symm q.2)) p := by
  have hinv := toricChartInverse_holomorphic_mo1973_28675 a p.2 hp
  have hfirst :
    ContMDiffAt
      (((modelWithCornersSelf ℂ ℂ)).prod (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)))
      (modelWithCornersSelf ℂ ℂ) ω (Prod.fst : ℂ × ToricSpace.Space → ℂ) p :=
    contMDiffAt_fst
  have hsecond :
    ContMDiffAt
      (((modelWithCornersSelf ℂ ℂ)).prod (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω
      (fun q : ℂ × ToricSpace.Space => (ToricSpace.parametrization a).symm q.2) p :=
    hinv.comp p contMDiffAt_snd
  exact hfirst.prodMk_space hsecond

private theorem
  SpecialPeriods.Threefold.VerticalAction.Cusp.toricFlow_local_scaled_holomorphic_mo1973_28677
    (a : ToricFan.Triangle) (p : ℂ × ToricSpace.Space)
    (hp : p.2 ∈ (ToricSpace.parametrization a).target) :
    ContMDiffAt
      (((modelWithCornersSelf ℂ ℂ)).prod (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω
      (fun q : ℂ × ToricSpace.Space =>
        ToricSpace.scale a (multiplier q.1) ((ToricSpace.parametrization a).symm q.2))
      p := by
  exact
    ContMDiffAt.comp (I :=
      ((modelWithCornersSelf ℂ ℂ)).prod (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)))
      (I' := modelWithCornersSelf ℂ (ℂ × ToricCharts.CoordinateSpace 3)) (I'' :=
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))) (f :=
      fun q : ℂ × ToricSpace.Space => (q.1, (ToricSpace.parametrization a).symm q.2)) (g :=
      fun q : ℂ × ToricCharts.CoordinateSpace 3 => ToricSpace.scale a (multiplier q.1) q.2) p
      (toricFlow_scale_joint_contMDiff_mo1973_28674 a
        (p.1, (ToricSpace.parametrization a).symm p.2))
      (toricFlow_local_coordinates_holomorphic_mo1973_28676 a p hp)

private theorem
  SpecialPeriods.Threefold.VerticalAction.Cusp.toricFlow_local_holomorphic_mo1973_28678
    (a : ToricFan.Triangle) (p : ℂ × ToricSpace.Space)
    (hp : p.2 ∈ (ToricSpace.parametrization a).target) :
    ContMDiffAt
      (((modelWithCornersSelf ℂ ℂ)).prod (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω
      (fun q : ℂ × ToricSpace.Space =>
        ToricSpace.inclusion a
          (ToricSpace.scale a (multiplier q.1) ((ToricSpace.parametrization a).symm q.2)))
      p :=
  (ToricSpace.inclusion_holomorphic a).contMDiffAt.comp p
    (toricFlow_local_scaled_holomorphic_mo1973_28677 a p hp)

private theorem SpecialPeriods.Threefold.VerticalAction.Cusp.toricFlow_joint_holomorphic :
    ContMDiff
      (((modelWithCornersSelf ℂ ℂ)).prod (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω
      (fun p : ℂ × ToricSpace.Space => toricFlow p.1 p.2) := by
  intro p
  let a := ToricSpace.preferredTriangle p.2
  have hp : p.2 ∈ (ToricSpace.parametrization a).target := by
    rw [ToricSpace.parametrization_target]
    exact ToricSpace.preferred_mem p.2
  apply (toricFlow_local_holomorphic_mo1973_28678 a p hp).congr_of_eventuallyEq
  filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
      ((ToricSpace.parametrization a).open_target.mem_nhds hp)] with
    q hq
  calc
    toricFlow q.1 q.2 =
        toricFlow q.1 (ToricSpace.inclusion a ((ToricSpace.parametrization a).symm q.2)) :=
      congrArg (toricFlow q.1) ((ToricSpace.parametrization a).right_inv hq).symm
    _ = _ := toricFlow_inclusion q.1 a _

private theorem
    SpecialPeriods.Threefold.VerticalAction.Cusp.fibreMultiplier_variableMultiplier_commute
    (u : Fin 2 → ℂˣ) (v : ℂ → Fin 2 → ℂˣ) (x : ToricSpace.Space) :
    ToricSpace.torusAction (ToricSpace.fibreMultiplier u) (ToricSpace.variableMultiplier v x) =
      ToricSpace.variableMultiplier v (ToricSpace.torusAction (ToricSpace.fibreMultiplier u) x) :=
  by
  simp only [ToricSpace.variableMultiplier, ToricSpace.time_fibreMultiplier,
    ToricSpace.torusAction_mul]
  rw [mul_comm]

private theorem
    SpecialPeriods.Threefold.VerticalAction.Cusp.fibreMultiplier_twistedTranslate_commute
    (u : Fin 2 → ℂˣ) (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) (x : ToricSpace.Space) :
    ToricSpace.torusAction (ToricSpace.fibreMultiplier u) (ToricSpace.twistedTranslate C v x) =
      ToricSpace.twistedTranslate C v (ToricSpace.torusAction (ToricSpace.fibreMultiplier u) x) :=
  by
  unfold ToricSpace.twistedTranslate
  rw [fibreMultiplier_variableMultiplier_commute, ToricSpace.fibreMultiplier_translate]

private theorem SpecialPeriods.Threefold.VerticalAction.Cusp.toricFlow_twistedTranslate
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (s : ℂ) (v : Fin 2 → ℤ) (x : ToricSpace.Space) :
    toricFlow s (ToricSpace.twistedTranslate C v x) =
      ToricSpace.twistedTranslate C v (toricFlow s x) :=
  fibreMultiplier_twistedTranslate_commute _ C v x

private def
    SpecialPeriods.Threefold.VerticalAction.Cusp.tubeFlow (D : TopologicalSpace.Opens ℂ) (s : ℂ)
    (x : ToricSpace.Tube D) : ToricSpace.Tube D :=
  ⟨toricFlow s x, by
    change ToricSpace.time (toricFlow s x) ∈ D
    rw [toricFlow_time]
    exact x.property⟩

@[simp]
private theorem
    SpecialPeriods.Threefold.VerticalAction.Cusp.tubeFlow_zero (D : TopologicalSpace.Opens ℂ)
    (x : ToricSpace.Tube D) : tubeFlow D 0 x = x :=
  Subtype.ext (toricFlow_zero x)

private theorem
    SpecialPeriods.Threefold.VerticalAction.Cusp.tubeFlow_add (D : TopologicalSpace.Opens ℂ)
    (s t : ℂ) (x : ToricSpace.Tube D) : tubeFlow D (s + t) x = tubeFlow D s (tubeFlow D t x) :=
  Subtype.ext (toricFlow_add s t x)

@[simp]
private theorem SpecialPeriods.Threefold.VerticalAction.Cusp.tubeFlow_int_cast
    (D : TopologicalSpace.Opens ℂ) (n : ℤ) (x : ToricSpace.Tube D) : tubeFlow D (n : ℂ) x = x :=
  Subtype.ext (toricFlow_int_cast n x)

private theorem SpecialPeriods.Threefold.VerticalAction.Cusp.tubeFlow_translate
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (D : TopologicalSpace.Opens ℂ) (s : ℂ) (v : Fin 2 → ℤ)
    (x : ToricSpace.Tube D) :
    tubeFlow D s (ToricSpace.tubeTranslate C D v x) =
      ToricSpace.tubeTranslate C D v (tubeFlow D s x) :=
  Subtype.ext (toricFlow_twistedTranslate C s v x)

private theorem SpecialPeriods.Threefold.VerticalAction.Cusp.tubeFlow_joint_holomorphic
    (D : TopologicalSpace.Opens ℂ) :
    ContMDiff
      (((modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))).prod (modelWithCornersSelf ℂ ℂ))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω
      (fun p : ToricSpace.Tube D × ℂ => tubeFlow D p.2 p.1) := by
  intro p
  have he :
    ContMDiffAt
        (((modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))).prod
          (modelWithCornersSelf ℂ ℂ))
        (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω
        (fun q : ToricSpace.Tube D × ℂ => (tubeFlow D q.2 q.1 : ToricSpace.Space)) p ↔
      ContMDiffAt
        (((modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))).prod
          (modelWithCornersSelf ℂ ℂ))
        (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω
        (fun q : ToricSpace.Tube D × ℂ => tubeFlow D q.2 q.1) p :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact
    he.mp
      (toricFlow_joint_holomorphic.comp
        (contMDiff_snd.prodMk (contMDiff_subtype_val.comp contMDiff_fst)) p)

private def
    SpecialPeriods.Threefold.VerticalAction.Cusp.flow (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (s : ℂ) : CuspQuotient.QuotientSpace C ε → CuspQuotient.QuotientSpace C ε :=
  Quotient.lift (fun x => CuspQuotient.quotientMap C ε (tubeFlow (CuspQuotient.disc ε) s x))
    (by
      let := ToricSpace.tubeAction C (CuspQuotient.disc ε)
      intro x y hxy
      change x ∈ MulAction.orbit CuspQuotient.LatticeGroup y at hxy
      obtain ⟨g, rfl⟩ := hxy
      change
        CuspQuotient.quotientMap C ε
            (tubeFlow (CuspQuotient.disc ε) s
              (ToricSpace.tubeTranslate C (CuspQuotient.disc ε) g.toAdd y)) =
          _
      rw [tubeFlow_translate, CuspQuotient.quotientMap_translate])

@[simp]
private theorem
    SpecialPeriods.Threefold.VerticalAction.Cusp.flow_zero (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (x : CuspQuotient.QuotientSpace C ε) : flow C ε 0 x = x := by
  induction x using Quotient.inductionOn with
  | h x => exact congrArg (CuspQuotient.quotientMap C ε) (tubeFlow_zero _ x)

private theorem
    SpecialPeriods.Threefold.VerticalAction.Cusp.flow_add (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (s t : ℂ) (x : CuspQuotient.QuotientSpace C ε) :
    flow C ε (s + t) x = flow C ε s (flow C ε t x) := by
  induction x using Quotient.inductionOn with
  | h x => exact congrArg (CuspQuotient.quotientMap C ε) (tubeFlow_add _ s t x)

@[simp]
private theorem SpecialPeriods.Threefold.VerticalAction.Cusp.flow_int_cast
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (n : ℤ) (x : CuspQuotient.QuotientSpace C ε) :
    flow C ε (n : ℂ) x = x := by
  induction x using Quotient.inductionOn with
  | h x => exact congrArg (CuspQuotient.quotientMap C ε) (tubeFlow_int_cast _ n x)

@[simp]
private theorem SpecialPeriods.Threefold.VerticalAction.Cusp.projection_flow
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (s : ℂ) (x : CuspQuotient.QuotientSpace C ε) :
    CuspQuotient.projection C ε (flow C ε s x) = CuspQuotient.projection C ε x := by
  induction x using Quotient.inductionOn with
  | h x => exact toricFlow_time s x

private theorem SpecialPeriods.Threefold.VerticalAction.Cusp.quotientMap_isLocalDiffeomorph
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    IsLocalDiffeomorph (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (CuspQuotient.quotientMap C ε) :=
  by
  let := ToricSpace.tubeAction C (CuspQuotient.disc ε)
  exact
    CoveringQuotient.project_isLocalDiffeomorph
      (CuspQuotient.quotientMap_covering C ε hε hε1 hC hR)
      (fun v => ToricSpace.tubeTranslate_holomorphic C (CuspQuotient.disc ε) v.toAdd hC)

private theorem SpecialPeriods.Threefold.VerticalAction.Cusp.flow_joint_holomorphic
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    ContMDiff
      (((modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))).prod (modelWithCornersSelf ℂ ℂ))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω
      (fun p : CuspQuotient.QuotientSpace C ε × ℂ => flow C ε p.2 p.1) := by
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  have hq :=
    CanonicalProduct.isLocalDiffeomorph_prodLine (quotientMap_isLocalDiffeomorph C ε hε hε1 hC hR)
  have hs :
    Function.Surjective
      (fun p : ToricSpace.Tube (CuspQuotient.disc ε) × ℂ =>
        (CuspQuotient.quotientMap C ε p.1, p.2)) := by
    rintro ⟨q, s⟩
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    exact ⟨(x, s), rfl⟩
  apply
    contMDiff_of_comp_localDiffeomorph
      (((modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))).prod (modelWithCornersSelf ℂ ℂ))
      (((modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))).prod (modelWithCornersSelf ℂ ℂ))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) hq hs
  exact
    (CuspQuotient.quotientMap_holomorphic C ε hε hε1 hC hR).comp
      (tubeFlow_joint_holomorphic (CuspQuotient.disc ε))

private theorem SpecialPeriods.Threefold.VerticalAction.Cusp.torusAction_torusPoint
    (u : ToricSpace.ActingTorus) (w : ToricCharts.CoordinateSpace 3) :
    ToricSpace.torusAction u (CuspUniformization.torusPoint w) =
      CuspUniformization.torusPoint (fun j => (u j : ℂ) * w j) := by
  change
    ToricSpace.torusAction u
        (ToricSpace.inclusion ToricSpace.referenceTriangle
          (ToricCharts.monomial ToricSpace.referenceTriangle.dual w)) =
      ToricSpace.inclusion ToricSpace.referenceTriangle
        (ToricCharts.monomial ToricSpace.referenceTriangle.dual ((fun j => (u j : ℂ)) * w))
  rw [ToricSpace.torusAction_inclusion, ToricCharts.monomial_mul]
  rfl

private theorem SpecialPeriods.Threefold.VerticalAction.Cusp.toricFlow_torusPoint (s : ℂ)
    (w : ToricCharts.CoordinateSpace 3) :
    toricFlow s (CuspUniformization.torusPoint w) =
      CuspUniformization.torusPoint ![w 0, CuspUniformization.exponential s * w 1, w 2] := by
  rw [toricFlow, torusAction_torusPoint]
  apply congrArg CuspUniformization.torusPoint
  ext i
  fin_cases i <;> simp [multiplier, ToricSpace.fibreMultiplier, CuspUniformization.exponential]

private theorem SpecialPeriods.Threefold.VerticalAction.Cusp.toricFlow_exponentialPoint (s t : ℂ)
    (z : ComplexPlane₂) :
    toricFlow s (CuspUniformization.exponentialPoint t z) =
      CuspUniformization.exponentialPoint t (z + s • (![0, 1] : ComplexPlane₂)) := by
  change
    toricFlow s (CuspUniformization.torusPoint (CuspUniformization.exponentialCoordinates t z)) =
      CuspUniformization.torusPoint
        (CuspUniformization.exponentialCoordinates t (z + s • (![0, 1] : ComplexPlane₂)))
  rw [toricFlow_torusPoint]
  apply congrArg CuspUniformization.torusPoint
  ext i
  fin_cases i <;>
    simp [CuspUniformization.exponentialCoordinates, CuspUniformization.exponential_add, mul_comm]

private def SpecialPeriods.Threefold.VerticalAction.Cusp.logFlow (ε : ℝ) (s : ℂ)
    (p : CuspUniformization.LogCover ε) : CuspUniformization.LogCover ε :=
  ⟨(p.val.1, p.val.2 + s • (![0, 1] : ComplexPlane₂)), p.property⟩

private theorem SpecialPeriods.Threefold.VerticalAction.Cusp.toricFlow_totalExponentialPoint (s : ℂ)
    (p : ℂ × ComplexPlane₂) :
    toricFlow s (CuspUniformization.totalExponentialPoint p) =
      CuspUniformization.totalExponentialPoint (p.1, p.2 + s • (![0, 1] : ComplexPlane₂)) :=
  toricFlow_exponentialPoint s (CuspUniformization.exponential p.1) p.2

private theorem
    SpecialPeriods.Threefold.VerticalAction.Cusp.tubeFlow_totalExponentialLift (ε : ℝ) (s : ℂ)
    (p : CuspUniformization.LogCover ε) :
    tubeFlow (CuspQuotient.disc ε) s (CuspUniformization.totalExponentialLift ε p) =
      CuspUniformization.totalExponentialLift ε (logFlow ε s p) :=
  Subtype.ext (toricFlow_totalExponentialPoint s p)

private theorem SpecialPeriods.Threefold.VerticalAction.Cusp.flow_totalCuspCover
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (s : ℂ) (p : CuspUniformization.LogCover ε) :
    flow C ε s (CuspUniformization.totalCuspCover C ε p) =
      CuspUniformization.totalCuspCover C ε (logFlow ε s p) := by
  change
    CuspQuotient.quotientMap C ε
        (tubeFlow (CuspQuotient.disc ε) s (CuspUniformization.totalExponentialLift ε p)) =
      _
  rw [tubeFlow_totalExponentialLift]
  rfl

private def SpecialPeriods.Threefold.VerticalAction.Period.vector (s : ℂ) : ComplexPlane₂ :=
  ![0, s]

@[simp]
private theorem SpecialPeriods.Threefold.VerticalAction.Period.vector_zero : vector 0 = 0 := by
  ext i
  fin_cases i <;> rfl

private theorem SpecialPeriods.Threefold.VerticalAction.Period.vector_add (s t : ℂ) :
    vector (s + t) = vector s + vector t := by
  ext i
  fin_cases i <;> simp [vector]

private theorem SpecialPeriods.Threefold.VerticalAction.Period.vector_eq_smul (s : ℂ) :
    vector s = s • (![0, 1] : ComplexPlane₂) := by
  ext i
  fin_cases i <;> simp [vector]

private def SpecialPeriods.Threefold.VerticalAction.Period.vectorFlow {B : Type*} (s : ℂ)
    (x : B × ComplexPlane₂) : B × ComplexPlane₂ :=
  (x.1, x.2 + vector s)

private def SpecialPeriods.Threefold.VerticalAction.Period.flow {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B)
    (s : ℂ) (x : P.TotalSpace) : P.TotalSpace :=
  (x.1, x.2 + standardLattice.mkQ ((P.periodEquiv x.1).symm (vector s)))

@[simp]
private theorem SpecialPeriods.Threefold.VerticalAction.Period.flow_quotientMap {V B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    (P : HolomorphicPeriodMap V B) (s : ℂ) (x : B × ComplexPlane₂) :
    flow P s (P.quotientMap x) = P.quotientMap (vectorFlow s x) := by
  simp only [flow, HolomorphicPeriodMap.quotientMap, vectorFlow, map_add]

@[simp]
private theorem SpecialPeriods.Threefold.VerticalAction.Period.flow_projection {V B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    (P : HolomorphicPeriodMap V B) (s : ℂ) (x : P.TotalSpace) :
    P.projection (flow P s x) = P.projection x :=
  rfl

@[simp]
private theorem SpecialPeriods.Threefold.VerticalAction.Period.flow_zero {V B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    (P : HolomorphicPeriodMap V B) (x : P.TotalSpace) : flow P 0 x = x := by simp [flow]

private theorem SpecialPeriods.Threefold.VerticalAction.Period.flow_add {V B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    (P : HolomorphicPeriodMap V B) (s t : ℂ) (x : P.TotalSpace) :
    flow P (s + t) x = flow P s (flow P t x) := by
  simp only [flow, vector_add, map_add]
  congr 1
  abel

private theorem SpecialPeriods.Threefold.VerticalAction.Period.periodEquiv_delta {V B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    (P : HolomorphicPeriodMap V B) (b : B) :
    P.periodEquiv b (Pi.basisFun ℝ (Fin 4) 3) = (![0, 1] : ComplexPlane₂) := by
  rw [P.periodEquiv_coordinates]
  ext i
  fin_cases i <;> simp

private theorem SpecialPeriods.Threefold.VerticalAction.Period.inverse_vector_int_mem {V B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    (P : HolomorphicPeriodMap V B) (b : B) (n : ℤ) :
    (P.periodEquiv b).symm (vector (n : ℂ)) ∈ standardLattice := by
  have he : P.periodEquiv b (n • Pi.basisFun ℝ (Fin 4) 3) = vector (n : ℂ) := by
    rw [map_zsmul, periodEquiv_delta]
    ext i
    fin_cases i <;> simp [vector]
  rw [← he, LinearEquiv.symm_apply_apply]
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨3, rfl⟩

@[simp]
private theorem SpecialPeriods.Threefold.VerticalAction.Period.flow_int_cast {V B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    (P : HolomorphicPeriodMap V B) (n : ℤ) (x : P.TotalSpace) : flow P (n : ℂ) x = x := by
  have hz : standardLattice.mkQ ((P.periodEquiv x.1).symm (vector (n : ℂ))) = 0 :=
    (Submodule.Quotient.mk_eq_zero standardLattice).mpr (inverse_vector_int_mem P x.1 n)
  simp [flow, hz]

private theorem SpecialPeriods.Threefold.VerticalAction.Triangle.rightBlock_vector {V B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (g : SpecialPeriods.TriangleGroup) (b : B) (s : ℂ) :
    D.rightBlock g b *ᵥ SpecialPeriods.Threefold.VerticalAction.Period.vector s =
      SpecialPeriods.Threefold.VerticalAction.Period.vector s := by
  rw [SpecialPeriods.Threefold.VerticalAction.Period.vector_eq_smul, Matrix.mulVec_smul,
    D.rightBlock_fixes_second]

private theorem
    SpecialPeriods.Threefold.VerticalAction.Triangle.vectorFlow_complexLift {V B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B) (s : ℂ)
    (g : SpecialPeriods.TriangleGroup) (x : B × ComplexPlane₂) :
    SpecialPeriods.Threefold.VerticalAction.Period.vectorFlow s (D.complexLift g x) =
      D.complexLift g (SpecialPeriods.Threefold.VerticalAction.Period.vectorFlow s x) := by
  simp only [SpecialPeriods.Threefold.VerticalAction.Period.vectorFlow,
    PeriodFamily.Data.complexLift, Matrix.mulVec_add, rightBlock_vector]

private theorem SpecialPeriods.Threefold.VerticalAction.Triangle.periodFlow_smul {V B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B) (s : ℂ)
    (g : SpecialPeriods.TriangleGroup) (x : D.TotalSpace) :
    letI := D.totalAction
    SpecialPeriods.Threefold.VerticalAction.Period.flow D.periods s (g • x) =
      g • SpecialPeriods.Threefold.VerticalAction.Period.flow D.periods s x := by
  let := D.totalAction
  obtain ⟨w, rfl⟩ := D.periods.quotientMap_surjective x
  rw [← D.complexLift_quotientMap,
    SpecialPeriods.Threefold.VerticalAction.Period.flow_quotientMap, vectorFlow_complexLift,
    D.complexLift_quotientMap, SpecialPeriods.Threefold.VerticalAction.Period.flow_quotientMap]

private def
    SpecialPeriods.Threefold.VerticalAction.Triangle.flow {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B) (s : ℂ) :
    D.Space → D.Space := by
  let := D.totalAction
  exact
    Quotient.lift
      (fun x => D.quotient (SpecialPeriods.Threefold.VerticalAction.Period.flow D.periods s x))
      (by
        intro x y hxy
        have he : D.quotient x = D.quotient y := Quotient.sound hxy
        obtain ⟨g, hg⟩ := (D.quotient_eq_iff x y).mp he
        rw [← hg, periodFlow_smul, D.quotient_smul])

@[simp]
private theorem SpecialPeriods.Threefold.VerticalAction.Triangle.flow_quotient {V B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B) (s : ℂ)
    (x : D.TotalSpace) :
    flow D s (D.quotient x) =
      D.quotient (SpecialPeriods.Threefold.VerticalAction.Period.flow D.periods s x) :=
  rfl

@[simp]
private theorem SpecialPeriods.Threefold.VerticalAction.Triangle.flow_projection {V B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B) (s : ℂ) (x : D.Space) :
    D.projection (flow D s x) = D.projection x := by
  obtain ⟨x, rfl⟩ := D.quotient_surjective x
  rw [flow_quotient, D.projection_quotient, D.projection_quotient,
    SpecialPeriods.Threefold.VerticalAction.Period.flow_projection]

@[simp]
private theorem SpecialPeriods.Threefold.VerticalAction.Triangle.flow_zero {V B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B) (x : D.Space) :
    flow D 0 x = x := by
  obtain ⟨x, rfl⟩ := D.quotient_surjective x
  rw [flow_quotient, SpecialPeriods.Threefold.VerticalAction.Period.flow_zero]

private theorem SpecialPeriods.Threefold.VerticalAction.Triangle.flow_add {V B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B) (s t : ℂ)
    (x : D.Space) : flow D (s + t) x = flow D s (flow D t x) := by
  obtain ⟨x, rfl⟩ := D.quotient_surjective x
  simp only [flow_quotient, SpecialPeriods.Threefold.VerticalAction.Period.flow_add]

@[simp]
private theorem SpecialPeriods.Threefold.VerticalAction.Triangle.flow_int_cast {V B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B) (n : ℤ) (x : D.Space) :
    flow D (n : ℂ) x = x := by
  obtain ⟨x, rfl⟩ := D.quotient_surjective x
  rw [flow_quotient, SpecialPeriods.Threefold.VerticalAction.Period.flow_int_cast]

private theorem
    SpecialPeriods.Threefold.VerticalAction.Period.vector_holomorphic : ContDiff ℂ ω vector :=
  by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_const
  · exact contDiff_id

@[instance_reducible]
private def SpecialPeriods.Threefold.VerticalAction.Period.vectorChartedSpace {V B : Type*}
    [NormedAddCommGroup V] [TopologicalSpace B] [ChartedSpace V B] :
    ChartedSpace (V × ComplexPlane₂) (B × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd V ComplexPlane₂) (B × ComplexPlane₂))

attribute [local instance] SpecialPeriods.Threefold.VerticalAction.Period.vectorChartedSpace in
private theorem
    SpecialPeriods.Threefold.VerticalAction.Period.jointVectorFlow_holomorphic {V B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] :
    ContMDiff (((modelWithCornersSelf ℂ (V × ComplexPlane₂))).prod (modelWithCornersSelf ℂ ℂ))
      (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω
      (fun x : (B × ComplexPlane₂) × ℂ => vectorFlow x.2 x.1) := by
  rw [modelWithCornersSelf_prod]
  exact
    (contMDiff_fst.comp contMDiff_fst).prodMk
      ((contMDiff_snd.comp contMDiff_fst).add (vector_holomorphic.contMDiff.comp contMDiff_snd))

attribute [local instance] SpecialPeriods.Threefold.VerticalAction.Period.vectorChartedSpace in
private theorem SpecialPeriods.Threefold.VerticalAction.Period.jointFlow_holomorphic {V B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    (P : HolomorphicPeriodMap V B) [IsManifold (modelWithCornersSelf ℂ V) ω B] :
    letI := P.totalChartedSpace
    ContMDiff (((modelWithCornersSelf ℂ (V × ComplexPlane₂))).prod (modelWithCornersSelf ℂ ℂ))
      (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω
      (fun x : P.TotalSpace × ℂ => flow P x.2 x.1) := by
  let := P.totalChartedSpace
  have hq := CanonicalProduct.isLocalDiffeomorph_prodLine P.quotientMap_isLocalDiffeomorph
  have hs : Function.Surjective (fun x : (B × ComplexPlane₂) × ℂ => (P.quotientMap x.1, x.2)) := by
    rintro ⟨y, s⟩
    obtain ⟨x, rfl⟩ := P.quotientMap_surjective y
    exact ⟨(x, s), rfl⟩
  apply
    contMDiff_of_comp_localDiffeomorph
      (((modelWithCornersSelf ℂ (V × ComplexPlane₂))).prod (modelWithCornersSelf ℂ ℂ))
      (((modelWithCornersSelf ℂ (V × ComplexPlane₂))).prod (modelWithCornersSelf ℂ ℂ))
      (modelWithCornersSelf ℂ (V × ComplexPlane₂)) hq hs
  change
    ContMDiff (((modelWithCornersSelf ℂ (V × ComplexPlane₂))).prod (modelWithCornersSelf ℂ ℂ))
      (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω
      (fun x : (B × ComplexPlane₂) × ℂ => flow P x.2 (P.quotientMap x.1))
  simp_rw [flow_quotientMap]
  exact P.quotientMap_holomorphic.comp jointVectorFlow_holomorphic

private theorem SpecialPeriods.Threefold.VerticalAction.Triangle.jointFlow_holomorphic {V B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient SpecialPeriods.TriangleGroup)
    [IsManifold (modelWithCornersSelf ℂ V) ω B] :
    letI := D.chartedSpace hq
    ContMDiff (((modelWithCornersSelf ℂ (V × ComplexPlane₂))).prod (modelWithCornersSelf ℂ ℂ))
      (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω (fun x : D.Space × ℂ => flow D x.2 x.1) := by
  let := D.periods.totalChartedSpace
  let := D.chartedSpace hq
  have hl := CanonicalProduct.isLocalDiffeomorph_prodLine (D.quotient_isLocalDiffeomorph hq)
  have hs : Function.Surjective (fun x : D.TotalSpace × ℂ => (D.quotient x.1, x.2)) := by
    rintro ⟨y, s⟩
    obtain ⟨x, rfl⟩ := D.quotient_surjective y
    exact ⟨(x, s), rfl⟩
  apply
    contMDiff_of_comp_localDiffeomorph
      (((modelWithCornersSelf ℂ (V × ComplexPlane₂))).prod (modelWithCornersSelf ℂ ℂ))
      (((modelWithCornersSelf ℂ (V × ComplexPlane₂))).prod (modelWithCornersSelf ℂ ℂ))
      (modelWithCornersSelf ℂ (V × ComplexPlane₂)) hl hs
  change
    ContMDiff (((modelWithCornersSelf ℂ (V × ComplexPlane₂))).prod (modelWithCornersSelf ℂ ℂ))
      (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω
      (fun x : D.TotalSpace × ℂ => flow D x.2 (D.quotient x.1))
  simp_rw [flow_quotient]
  exact
    (D.quotient_holomorphic hq).comp
      (SpecialPeriods.Threefold.VerticalAction.Period.jointFlow_holomorphic D.periods)

private def SpecialPeriods.Threefold.VerticalAction.Cusp.overlapVectorCover
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (p : CuspUniformization.LogCover C.radius) : D.Space :=
  D.quotient
    (D.periods.quotientMap
      (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap ⟨p.val.1, p.property⟩, p.val.2))

private theorem SpecialPeriods.Threefold.VerticalAction.Cusp.overlapVectorCover_logFlow
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width) (s : ℂ)
    (p : CuspUniformization.LogCover C.radius) :
    overlapVectorCover C D hrcap (logFlow C.radius s p) =
      SpecialPeriods.Threefold.VerticalAction.Triangle.flow D s
        (overlapVectorCover C D hrcap p) := by
  unfold overlapVectorCover
  rw [SpecialPeriods.Threefold.VerticalAction.Triangle.flow_quotient,
    SpecialPeriods.Threefold.VerticalAction.Period.flow_quotientMap]
  apply congrArg D.quotient
  apply congrArg D.periods.quotientMap
  change
    (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap ⟨p.val.1, p.property⟩,
        p.val.2 + s • (![0, 1] : ComplexPlane₂)) =
      (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap ⟨p.val.1, p.property⟩,
        p.val.2 + SpecialPeriods.Threefold.VerticalAction.Period.vector s)
  rw [SpecialPeriods.Threefold.VerticalAction.Period.vector_eq_smul]

private theorem SpecialPeriods.Threefold.VerticalAction.Cusp.familyMap_iteratedCover_eq_vectorCover
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (hperiod :
      ∀ s : SpecialPeriods.CuspFamily.LogBase C.radius,
        D.periods.point (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap s) =
          C.periods.point s)
    (p : CuspUniformization.LogCover C.radius) :
    SpecialPeriods.CuspGlobalOverlap.familyMap C D hrcap (C.iteratedCover p) =
      overlapVectorCover C D hrcap p := by
  change
    D.quotient
        (HolomorphicPeriodMap.periodPullbackMap C.periods D.periods
          (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap)
          (C.periods.quotientMap (⟨p.val.1, p.property⟩, p.val.2))) =
      _
  exact
    congrArg D.quotient
      (HolomorphicPeriodMap.periodPullbackMap_quotientMap C.periods D.periods
        (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap) hperiod
        (⟨p.val.1, p.property⟩, p.val.2))

private theorem SpecialPeriods.Threefold.VerticalAction.Cusp.cuspToRegularPartial_totalCuspCover
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (hperiod :
      ∀ s : SpecialPeriods.CuspFamily.LogBase C.radius,
        D.periods.point (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap s) =
          C.periods.point s)
    (p : CuspUniformization.LogCover C.radius) :
    letI :=
      CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
        C.smallDrift
    letI := D.chartedSpace (SpecialPeriods.CuspGlobalOverlap.familyCovering D)
    SpecialPeriods.CuspGlobalOverlap.cuspToRegularPartial C D hrcap hperiod
        (CuspUniformization.totalCuspCover C.correction C.radius p) =
      overlapVectorCover C D hrcap p := by
  let :=
    CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
      C.smallDrift
  let := D.chartedSpace (SpecialPeriods.CuspGlobalOverlap.familyCovering D)
  exact
    (SpecialPeriods.CuspGlobalOverlap.cuspToRegularPartial_apply C D hrcap hperiod
          (CuspUniformization.totalCuspCover C.correction C.radius p)
          (CuspUniformization.puncturedCuspCover C.correction C.radius p).property).trans
      ((SpecialPeriods.CuspGlobalOverlap.puncturedBiholomorph_cover C D hrcap hperiod p).trans
        (familyMap_iteratedCover_eq_vectorCover C D hrcap hperiod p))

private theorem SpecialPeriods.Threefold.VerticalAction.Cusp.cuspToRegularPartial_flow
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (hperiod :
      ∀ s : SpecialPeriods.CuspFamily.LogBase C.radius,
        D.periods.point (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap s) =
          C.periods.point s)
    (s : ℂ) (x : CuspQuotient.QuotientSpace C.correction C.radius)
    (hx : CuspQuotient.projection C.correction C.radius x ≠ 0) :
    letI :=
      CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
        C.smallDrift
    letI := D.chartedSpace (SpecialPeriods.CuspGlobalOverlap.familyCovering D)
    SpecialPeriods.CuspGlobalOverlap.cuspToRegularPartial C D hrcap hperiod
        (flow C.correction C.radius s x) =
      SpecialPeriods.Threefold.VerticalAction.Triangle.flow D s
        (SpecialPeriods.CuspGlobalOverlap.cuspToRegularPartial C D hrcap hperiod x) := by
  let :=
    CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
      C.smallDrift
  let := D.chartedSpace (SpecialPeriods.CuspGlobalOverlap.familyCovering D)
  obtain ⟨p, hp⟩ := CuspUniformization.puncturedCuspCover_surjective C.correction C.radius ⟨x, hx⟩
  have he : CuspUniformization.totalCuspCover C.correction C.radius p = x :=
    congrArg Subtype.val hp
  rw [← he, flow_totalCuspCover, cuspToRegularPartial_totalCuspCover C D hrcap hperiod,
    cuspToRegularPartial_totalCuspCover C D hrcap hperiod]
  exact overlapVectorCover_logFlow C D hrcap s p

private abbrev SpecialPeriods.Threefold.CuspGeometry.data : SpecialPeriods.CuspFamily.Data :=
  SpecialPeriods.Threefold.CuspPiece.restrictedData SpecialPeriods.specialCuspData
    SpecialPeriods.Threefold.specialBaseCover SpecialPeriods.Threefold.specialCuspRadius_le

private abbrev SpecialPeriods.Threefold.CuspGeometry.LocalSpace :=
  SpecialPeriods.Threefold.SpecialCuspPiece

@[instance_reducible]
private def SpecialPeriods.Threefold.CuspGeometry.nativeChartedSpace :
    ChartedSpace (ToricCharts.CoordinateSpace 3) LocalSpace :=
  SpecialPeriods.Threefold.CuspPiece.nativeChartedSpace SpecialPeriods.specialCuspData
    SpecialPeriods.Threefold.specialBaseCover SpecialPeriods.Threefold.specialCuspRadius_le

attribute [local instance] SpecialPeriods.Threefold.CuspGeometry.nativeChartedSpace
    SpecialPeriods.Threefold.chartedSpace SpecialPeriods.Threefold.specialCuspPieceChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.Threefold.CuspGeometry.parameter : LocalSpace → ℂ :=
  CuspQuotient.projection data.correction data.radius

attribute [local instance] SpecialPeriods.Threefold.CuspGeometry.nativeChartedSpace
    SpecialPeriods.Threefold.specialCuspPieceChartedSpace SpecialPeriods.Threefold.chartedSpace in
private def SpecialPeriods.Threefold.VerticalAction.Cusp.specialFlow (s : ℂ) :
    SpecialPeriods.Threefold.CuspGeometry.LocalSpace →
      SpecialPeriods.Threefold.CuspGeometry.LocalSpace :=
  flow ((SpecialPeriods.Threefold.CuspGeometry.data)).correction
    ((SpecialPeriods.Threefold.CuspGeometry.data)).radius s

attribute [local instance] SpecialPeriods.Threefold.CuspGeometry.nativeChartedSpace
    SpecialPeriods.Threefold.specialCuspPieceChartedSpace SpecialPeriods.Threefold.chartedSpace in
@[simp]
private theorem SpecialPeriods.Threefold.VerticalAction.Cusp.specialFlow_zero
    (x : SpecialPeriods.Threefold.CuspGeometry.LocalSpace) : specialFlow 0 x = x :=
  flow_zero ((SpecialPeriods.Threefold.CuspGeometry.data)).correction
    ((SpecialPeriods.Threefold.CuspGeometry.data)).radius x

attribute [local instance] SpecialPeriods.Threefold.CuspGeometry.nativeChartedSpace
    SpecialPeriods.Threefold.specialCuspPieceChartedSpace SpecialPeriods.Threefold.chartedSpace in
private theorem SpecialPeriods.Threefold.VerticalAction.Cusp.specialFlow_add (s t : ℂ)
    (x : SpecialPeriods.Threefold.CuspGeometry.LocalSpace) :
    specialFlow (s + t) x = specialFlow s (specialFlow t x) :=
  flow_add ((SpecialPeriods.Threefold.CuspGeometry.data)).correction
    ((SpecialPeriods.Threefold.CuspGeometry.data)).radius s t x

attribute [local instance] SpecialPeriods.Threefold.CuspGeometry.nativeChartedSpace
    SpecialPeriods.Threefold.specialCuspPieceChartedSpace SpecialPeriods.Threefold.chartedSpace in
@[simp]
private theorem SpecialPeriods.Threefold.VerticalAction.Cusp.specialFlow_int_cast (n : ℤ)
    (x : SpecialPeriods.Threefold.CuspGeometry.LocalSpace) : specialFlow (n : ℂ) x = x :=
  flow_int_cast ((SpecialPeriods.Threefold.CuspGeometry.data)).correction
    ((SpecialPeriods.Threefold.CuspGeometry.data)).radius n x

attribute [local instance] SpecialPeriods.Threefold.CuspGeometry.nativeChartedSpace
    SpecialPeriods.Threefold.specialCuspPieceChartedSpace SpecialPeriods.Threefold.chartedSpace in
@[simp]
private theorem SpecialPeriods.Threefold.VerticalAction.Cusp.parameter_specialFlow (s : ℂ)
    (x : SpecialPeriods.Threefold.CuspGeometry.LocalSpace) :
    SpecialPeriods.Threefold.CuspGeometry.parameter (specialFlow s x) =
      SpecialPeriods.Threefold.CuspGeometry.parameter x :=
  projection_flow ((SpecialPeriods.Threefold.CuspGeometry.data)).correction
    ((SpecialPeriods.Threefold.CuspGeometry.data)).radius s x

attribute [local instance] SpecialPeriods.Threefold.CuspGeometry.nativeChartedSpace
    SpecialPeriods.Threefold.specialCuspPieceChartedSpace SpecialPeriods.Threefold.chartedSpace in
private theorem SpecialPeriods.Threefold.VerticalAction.Cusp.specialFlow_joint_holomorphic :
    ContMDiff
      (((modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))).prod (modelWithCornersSelf ℂ ℂ))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω
      (fun p : SpecialPeriods.Threefold.CuspGeometry.LocalSpace × ℂ => specialFlow p.2 p.1) :=
  flow_joint_holomorphic ((SpecialPeriods.Threefold.CuspGeometry.data)).correction
    ((SpecialPeriods.Threefold.CuspGeometry.data)).radius
    ((SpecialPeriods.Threefold.CuspGeometry.data)).radius_pos
    ((SpecialPeriods.Threefold.CuspGeometry.data)).radius_lt_one
    ((SpecialPeriods.Threefold.CuspGeometry.data)).holomorphic
    ((SpecialPeriods.Threefold.CuspGeometry.data)).smallDrift

attribute [local instance] SpecialPeriods.Threefold.CuspGeometry.nativeChartedSpace
    SpecialPeriods.Threefold.specialCuspPieceChartedSpace SpecialPeriods.Threefold.chartedSpace in
private theorem SpecialPeriods.Threefold.VerticalAction.Cusp.specialFlow_joint_common_holomorphic :
    ContMDiff (((modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))).prod (modelWithCornersSelf ℂ ℂ))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω
      (fun p : SpecialPeriods.Threefold.CuspGeometry.LocalSpace × ℂ => specialFlow p.2 p.1) := by
  let e :
    Diffeomorph (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      SpecialPeriods.Threefold.CuspGeometry.LocalSpace
      SpecialPeriods.Threefold.CuspGeometry.LocalSpace ω :=
    SpecialPeriods.Threefold.CuspPiece.nativeToCommon SpecialPeriods.specialCuspData
      SpecialPeriods.Threefold.specialBaseCover SpecialPeriods.Threefold.specialCuspRadius_le
  have he :
    ContMDiff (((modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))).prod (modelWithCornersSelf ℂ ℂ))
      (((modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))).prod (modelWithCornersSelf ℂ ℂ))
      ω (fun p : SpecialPeriods.Threefold.CuspGeometry.LocalSpace × ℂ => (e.symm p.1, p.2)) :=
    (e.symm.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd
  exact e.contMDiff.comp (specialFlow_joint_holomorphic.comp he)

attribute [local instance] SpecialPeriods.Threefold.CuspGeometry.nativeChartedSpace
    SpecialPeriods.Threefold.specialCuspPieceChartedSpace SpecialPeriods.Threefold.chartedSpace in
private theorem
    SpecialPeriods.Threefold.VerticalAction.Cusp.specialCuspPieceProjectionToBase_specialFlow
    (s : ℂ) (x : SpecialPeriods.Threefold.CuspGeometry.LocalSpace) :
    SpecialPeriods.Threefold.specialCuspPieceProjectionToBase (specialFlow s x) =
      SpecialPeriods.Threefold.specialCuspPieceProjectionToBase x := by
  change
    SpecialPeriods.Threefold.CuspPiece.projectionToBase SpecialPeriods.specialCuspData
        SpecialPeriods.Threefold.specialBaseCover (specialFlow s x) =
      SpecialPeriods.Threefold.CuspPiece.projectionToBase SpecialPeriods.specialCuspData
        SpecialPeriods.Threefold.specialBaseCover x
  rw [SpecialPeriods.Threefold.CuspPiece.projectionToBase_apply,
    SpecialPeriods.Threefold.CuspPiece.projectionToBase_apply]
  exact congrArg _ (parameter_specialFlow s x)

private abbrev SpecialPeriods.Threefold.VerticalAction.Regular.data :
    PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint :=
  PeriodFamily.regularData SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂

private theorem SpecialPeriods.Threefold.VerticalAction.Regular.baseCovering :
    IsQuotientCoveringMap data.baseQuotient SpecialPeriods.TriangleGroup :=
  PeriodFamily.regularCovering SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂

private def SpecialPeriods.Threefold.VerticalAction.Regular.flow (s : ℂ) :
    SpecialPeriods.Threefold.SpecialRegularFamily →
      SpecialPeriods.Threefold.SpecialRegularFamily :=
  SpecialPeriods.Threefold.VerticalAction.Triangle.flow data s

@[simp]
private theorem SpecialPeriods.Threefold.VerticalAction.Regular.flow_projection (s : ℂ)
    (x : SpecialPeriods.Threefold.SpecialRegularFamily) :
    SpecialPeriods.Threefold.specialRegularFamilyProjectionToBase (flow s x) =
      SpecialPeriods.Threefold.specialRegularFamilyProjectionToBase x := by
  change
    SpecialPeriods.Threefold.regularInclusion
        (data.projection (SpecialPeriods.Threefold.VerticalAction.Triangle.flow data s x)) =
      SpecialPeriods.Threefold.regularInclusion (data.projection x)
  rw [SpecialPeriods.Threefold.VerticalAction.Triangle.flow_projection]

@[simp]
private theorem SpecialPeriods.Threefold.VerticalAction.Regular.flow_zero
    (x : SpecialPeriods.Threefold.SpecialRegularFamily) : flow 0 x = x :=
  SpecialPeriods.Threefold.VerticalAction.Triangle.flow_zero data x

private theorem SpecialPeriods.Threefold.VerticalAction.Regular.flow_add (s t : ℂ)
    (x : SpecialPeriods.Threefold.SpecialRegularFamily) : flow (s + t) x = flow s (flow t x) :=
  SpecialPeriods.Threefold.VerticalAction.Triangle.flow_add data s t x

@[simp]
private theorem SpecialPeriods.Threefold.VerticalAction.Regular.flow_int_cast (n : ℤ)
    (x : SpecialPeriods.Threefold.SpecialRegularFamily) : flow (n : ℂ) x = x :=
  SpecialPeriods.Threefold.VerticalAction.Triangle.flow_int_cast data n x

attribute [local instance] SpecialPeriods.Threefold.specialRegularFamilyChartedSpace in
private theorem SpecialPeriods.Threefold.VerticalAction.Regular.jointFlow_holomorphic :
    ContMDiff (((modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))).prod (modelWithCornersSelf ℂ ℂ))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω
      (fun x : SpecialPeriods.Threefold.SpecialRegularFamily × ℂ => flow x.2 x.1) :=
  SpecialPeriods.Threefold.VerticalAction.Triangle.jointFlow_holomorphic data baseCovering

attribute [local instance] SpecialPeriods.Threefold.specialCuspPieceChartedSpace
    SpecialPeriods.Threefold.specialRegularFamilyChartedSpace in
private theorem SpecialPeriods.Threefold.VerticalAction.Cusp.specialCuspOverlap_specialFlow (s : ℂ)
    (x : SpecialPeriods.Threefold.SpecialCuspPiece)
    (hx : x ∈ SpecialPeriods.Threefold.specialCuspOverlap.source) :
    SpecialPeriods.Threefold.specialCuspOverlap (specialFlow s x) =
      SpecialPeriods.Threefold.VerticalAction.Regular.flow s
        (SpecialPeriods.Threefold.specialCuspOverlap x) := by
  have hp :=
    SpecialPeriods.CuspGlobalOverlap.spherePeriod_agreement
      SpecialPeriods.Triangle.triangleSphereUniformization
      SpecialPeriods.Triangle.triangleSphereUniformization_cusp
      SpecialPeriods.Triangle.triangleSphereUniformization_centerOne
      SpecialPeriods.Triangle.triangleSphereUniformization_centerTwo
      (SpecialPeriods.Threefold.specialBaseCover.radius Option.none)
      (SpecialPeriods.Threefold.specialBaseCover.radius_pos Option.none)
      SpecialPeriods.Threefold.specialCuspRadius_le
      SpecialPeriods.Threefold.specialBaseCover_cusp_radius_bounds.2.2.le
  have hn := (SpecialPeriods.Threefold.specialCuspNativeOverlap_source_iff x).mp hx.2
  exact
    cuspToRegularPartial_flow SpecialPeriods.Threefold.CuspGeometry.data
      SpecialPeriods.Threefold.VerticalAction.Regular.data
      SpecialPeriods.Threefold.specialBaseCover_cusp_radius_bounds.2.2.le hp s x hn

private theorem
    SpecialPeriods.Threefold.VerticalAction.Elliptic.linearMatrix_vector (j : Elliptic.Kind)
    (p : PeriodDomain) (s : ℂ) :
    Elliptic.linearMatrix j p *ᵥ SpecialPeriods.Threefold.VerticalAction.Period.vector s =
      SpecialPeriods.Threefold.VerticalAction.Period.vector s := by
  cases j <;> ext i <;> fin_cases i <;>
    simp [Elliptic.linearMatrix, PeriodPoint.R₁, PeriodPoint.R₂,
      SpecialPeriods.Threefold.VerticalAction.Period.vector, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]

private theorem SpecialPeriods.Threefold.VerticalAction.Elliptic.complexLift_vectorFlow
    {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j) (v : Lattice) (s : ℂ)
    (x : SpecialPeriods.Disc × ComplexPlane₂) :
    D.complexLift v (SpecialPeriods.Threefold.VerticalAction.Period.vectorFlow s x) =
      SpecialPeriods.Threefold.VerticalAction.Period.vectorFlow s (D.complexLift v x) := by
  apply Prod.ext
  · rfl
  · change
      Elliptic.linearMatrix j (D.periods.point x.1) *ᵥ
            (x.2 + SpecialPeriods.Threefold.VerticalAction.Period.vector s) +
          _ =
        (Elliptic.linearMatrix j (D.periods.point x.1) *ᵥ x.2 + _) +
          SpecialPeriods.Threefold.VerticalAction.Period.vector s
    rw [Matrix.mulVec_add, linearMatrix_vector]
    abel

private theorem SpecialPeriods.Threefold.VerticalAction.Elliptic.periodFlow_permutation
    {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j) (v : Lattice) (s : ℂ)
    (x : D.TotalSpace) :
    SpecialPeriods.Threefold.VerticalAction.Period.flow D.periods s (D.permutation v x) =
      D.permutation v (SpecialPeriods.Threefold.VerticalAction.Period.flow D.periods s x) := by
  obtain ⟨z, rfl⟩ := D.periods.quotientMap_surjective x
  rw [← D.complexLift_quotientMap,
    SpecialPeriods.Threefold.VerticalAction.Period.flow_quotientMap,
    SpecialPeriods.Threefold.VerticalAction.Period.flow_quotientMap, ← D.complexLift_quotientMap,
    complexLift_vectorFlow]

private theorem
    SpecialPeriods.Threefold.VerticalAction.Elliptic.periodFlow_action {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : j.matrix *ᵥ v = v) (s : ℂ)
    (g : Elliptic.CyclicGroup j) (x : D.TotalSpace) :
    letI := D.action v hv
    SpecialPeriods.Threefold.VerticalAction.Period.flow D.periods s (g • x) =
      g • SpecialPeriods.Threefold.VerticalAction.Period.flow D.periods s x := by
  let := D.action v hv
  have h :
    Function.Semiconj (SpecialPeriods.Threefold.VerticalAction.Period.flow D.periods s)
      (D.permutation v) (D.permutation v) :=
    periodFlow_permutation D v s
  change
    SpecialPeriods.Threefold.VerticalAction.Period.flow D.periods s
        ((D.permutation v ^ g.toAdd.val) x) =
      (D.permutation v ^ g.toAdd.val)
        (SpecialPeriods.Threefold.VerticalAction.Period.flow D.periods s x)
  simp only [Equiv.Perm.coe_pow]
  exact h.iterate_right g.toAdd.val x

private def SpecialPeriods.Threefold.VerticalAction.Elliptic.flow {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) (s : ℂ) :
    D.Space v hv → D.Space v hv := by
  let := D.action v hv.1
  exact
    Elliptic.FiniteQuotient.descend
      (fun x =>
        D.quotient v hv (SpecialPeriods.Threefold.VerticalAction.Period.flow D.periods s x))
      (by
        intro g x
        rw [periodFlow_action D v hv.1 s g x, D.quotient_smul])

@[simp]
private theorem SpecialPeriods.Threefold.VerticalAction.Elliptic.flow_quotient {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) (s : ℂ)
    (x : D.TotalSpace) :
    flow D v hv s (D.quotient v hv x) =
      D.quotient v hv (SpecialPeriods.Threefold.VerticalAction.Period.flow D.periods s x) :=
  rfl

@[simp]
private theorem SpecialPeriods.Threefold.VerticalAction.Elliptic.flow_projection {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) (s : ℂ)
    (x : D.Space v hv) : D.projection v hv (flow D v hv s x) = D.projection v hv x := by
  obtain ⟨y, rfl⟩ := D.quotient_surjective v hv x
  rw [flow_quotient, D.projection_quotient, D.projection_quotient]
  rfl

@[simp]
private theorem SpecialPeriods.Threefold.VerticalAction.Elliptic.flow_zero {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v)
    (x : D.Space v hv) : flow D v hv 0 x = x := by
  obtain ⟨y, rfl⟩ := D.quotient_surjective v hv x
  rw [flow_quotient, SpecialPeriods.Threefold.VerticalAction.Period.flow_zero]

private theorem SpecialPeriods.Threefold.VerticalAction.Elliptic.flow_add {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) (s t : ℂ)
    (x : D.Space v hv) : flow D v hv (s + t) x = flow D v hv s (flow D v hv t x) := by
  obtain ⟨y, rfl⟩ := D.quotient_surjective v hv x
  rw [flow_quotient, flow_quotient, flow_quotient,
    SpecialPeriods.Threefold.VerticalAction.Period.flow_add]

@[simp]
private theorem SpecialPeriods.Threefold.VerticalAction.Elliptic.flow_int_cast {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) (n : ℤ)
    (x : D.Space v hv) : flow D v hv (n : ℂ) x = x := by
  obtain ⟨y, rfl⟩ := D.quotient_surjective v hv x
  rw [flow_quotient, SpecialPeriods.Threefold.VerticalAction.Period.flow_int_cast]

private theorem SpecialPeriods.Threefold.VerticalAction.Elliptic.quotient_isLocalDiffeomorph
    {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j) (v : Lattice)
    (hv : Elliptic.AdmissibleTwist j v) :
    letI := D.periods.totalChartedSpace
    letI := D.chartedSpace v hv
    IsLocalDiffeomorph (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω (D.quotient v hv) := by
  let := D.periods.totalChartedSpace
  let := D.periods.totalSpace_isManifold
  let := D.action v hv.1
  exact
    CoveringQuotient.project_isLocalDiffeomorph (D.quotientCoveringMap v hv)
      (D.action_holomorphic v hv.1)

private theorem
    SpecialPeriods.Threefold.VerticalAction.Elliptic.jointFlow_holomorphic {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    letI := D.chartedSpace v hv
    ContMDiff (((modelWithCornersSelf ℂ Elliptic.FamilyModel)).prod (modelWithCornersSelf ℂ ℂ))
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω
      (fun x : D.Space v hv × ℂ => flow D v hv x.2 x.1) := by
  let := D.periods.totalChartedSpace
  let := D.chartedSpace v hv
  have hq := CanonicalProduct.isLocalDiffeomorph_prodLine (quotient_isLocalDiffeomorph D v hv)
  have hs : Function.Surjective (fun x : D.TotalSpace × ℂ => (D.quotient v hv x.1, x.2)) := by
    rintro ⟨y, s⟩
    obtain ⟨x, rfl⟩ := D.quotient_surjective v hv y
    exact ⟨(x, s), rfl⟩
  apply
    contMDiff_of_comp_localDiffeomorph
      (((modelWithCornersSelf ℂ Elliptic.FamilyModel)).prod (modelWithCornersSelf ℂ ℂ))
      (((modelWithCornersSelf ℂ Elliptic.FamilyModel)).prod (modelWithCornersSelf ℂ ℂ))
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) hq hs
  change
    ContMDiff (((modelWithCornersSelf ℂ Elliptic.FamilyModel)).prod (modelWithCornersSelf ℂ ℂ))
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω
      (fun x : D.TotalSpace × ℂ => flow D v hv x.2 (D.quotient v hv x.1))
  simp_rw [flow_quotient]
  exact
    (D.quotient_holomorphic v hv).comp
      (SpecialPeriods.Threefold.VerticalAction.Period.jointFlow_holomorphic D.periods)

attribute [local instance] SpecialPeriods.EllipticFilling.specialFullFillingChartedSpace
    SpecialPeriods.Threefold.specialEllipticPieceChartedSpace
    SpecialPeriods.Threefold.chartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.Threefold.HolomorphicForms.EllipticCover.rootDomain (j : Elliptic.Kind) :
    TopologicalSpace.Opens SpecialPeriods.Disc :=
  ⟨{z | ‖(z : ℂ) ^ j.order‖ < SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j)},
    isOpen_lt (continuous_subtype_val.pow j.order).norm continuous_const⟩

attribute [local instance] SpecialPeriods.EllipticFilling.specialFullFillingChartedSpace
    SpecialPeriods.Threefold.specialEllipticPieceChartedSpace
    SpecialPeriods.Threefold.chartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
private abbrev SpecialPeriods.Threefold.HolomorphicForms.EllipticCover.Root (j : Elliptic.Kind) :=
  rootDomain j

attribute [local instance] SpecialPeriods.EllipticFilling.specialFullFillingChartedSpace
    SpecialPeriods.Threefold.specialEllipticPieceChartedSpace
    SpecialPeriods.Threefold.chartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
private abbrev SpecialPeriods.Threefold.HolomorphicForms.EllipticCover.Cover (j : Elliptic.Kind) :=
  Root j × ComplexPlane₂

attribute [local instance] SpecialPeriods.EllipticFilling.specialFullFillingChartedSpace
    SpecialPeriods.Threefold.specialEllipticPieceChartedSpace
    SpecialPeriods.Threefold.chartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
@[instance_reducible]
private def SpecialPeriods.Threefold.HolomorphicForms.EllipticCover.coverChartedSpace
    (j : Elliptic.Kind) : ChartedSpace Elliptic.FamilyModel (Cover j) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (Root j × ComplexPlane₂))

attribute [local instance] SpecialPeriods.EllipticFilling.specialFullFillingChartedSpace
    SpecialPeriods.Threefold.specialEllipticPieceChartedSpace in
private def
    SpecialPeriods.Threefold.VerticalAction.Elliptic.specialFullFlow (j : Elliptic.Kind) (s : ℂ) :
    SpecialPeriods.EllipticFilling.SpecialFullFilling j →
      SpecialPeriods.EllipticFilling.SpecialFullFilling j :=
  flow (SpecialPeriods.EllipticFilling.specialLocalData j) j.twist
    (Elliptic.mainTwist_admissible j) s

attribute [local instance] SpecialPeriods.EllipticFilling.specialFullFillingChartedSpace
    SpecialPeriods.Threefold.specialEllipticPieceChartedSpace in
@[simp]
private theorem SpecialPeriods.Threefold.VerticalAction.Elliptic.specialFullFlow_quotient
    (j : Elliptic.Kind) (s : ℂ)
    (x : (SpecialPeriods.EllipticFilling.specialLocalData j).TotalSpace) :
    specialFullFlow j s
        ((SpecialPeriods.EllipticFilling.specialLocalData j).quotient j.twist
          (Elliptic.mainTwist_admissible j) x) =
      (SpecialPeriods.EllipticFilling.specialLocalData j).quotient j.twist
        (Elliptic.mainTwist_admissible j)
        (SpecialPeriods.Threefold.VerticalAction.Period.flow
          (SpecialPeriods.EllipticFilling.specialLocalData j).periods s x) :=
  rfl

attribute [local instance] SpecialPeriods.EllipticFilling.specialFullFillingChartedSpace
    SpecialPeriods.Threefold.specialEllipticPieceChartedSpace in
@[simp]
private theorem SpecialPeriods.Threefold.VerticalAction.Elliptic.specialFullFlow_projection
    (j : Elliptic.Kind) (s : ℂ) (x : SpecialPeriods.EllipticFilling.SpecialFullFilling j) :
    SpecialPeriods.EllipticFilling.specialFullFillingProjection j (specialFullFlow j s x) =
      SpecialPeriods.EllipticFilling.specialFullFillingProjection j x :=
  flow_projection (SpecialPeriods.EllipticFilling.specialLocalData j) j.twist
    (Elliptic.mainTwist_admissible j) s x

attribute [local instance] SpecialPeriods.EllipticFilling.specialFullFillingChartedSpace
    SpecialPeriods.Threefold.specialEllipticPieceChartedSpace in
private theorem SpecialPeriods.Threefold.VerticalAction.Elliptic.specialFullFlow_joint_holomorphic
    (j : Elliptic.Kind) :
    ContMDiff (((modelWithCornersSelf ℂ Elliptic.FamilyModel)).prod (modelWithCornersSelf ℂ ℂ))
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω
      (fun x : SpecialPeriods.EllipticFilling.SpecialFullFilling j × ℂ =>
        specialFullFlow j x.2 x.1) :=
  jointFlow_holomorphic (SpecialPeriods.EllipticFilling.specialLocalData j) j.twist
    (Elliptic.mainTwist_admissible j)

attribute [local instance] SpecialPeriods.EllipticFilling.specialFullFillingChartedSpace
    SpecialPeriods.Threefold.specialEllipticPieceChartedSpace in
private def SpecialPeriods.Threefold.VerticalAction.Elliptic.specialFlow (j : Elliptic.Kind) (s : ℂ)
    (x : SpecialPeriods.Threefold.EllipticGeometry.LocalSpace j) :
    SpecialPeriods.Threefold.EllipticGeometry.LocalSpace j :=
  ⟨specialFullFlow j s x.val,
    by
    change
      ‖(SpecialPeriods.EllipticFilling.specialFullFillingProjection j
              (specialFullFlow j s x.val) :
            ℂ)‖ <
        SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j)
    rw [specialFullFlow_projection]
    exact x.property⟩

attribute [local instance] SpecialPeriods.EllipticFilling.specialFullFillingChartedSpace
    SpecialPeriods.Threefold.specialEllipticPieceChartedSpace in
@[simp]
private theorem SpecialPeriods.Threefold.VerticalAction.Elliptic.specialFlow_coe (j : Elliptic.Kind)
    (s : ℂ) (x : SpecialPeriods.Threefold.EllipticGeometry.LocalSpace j) :
    (specialFlow j s x : SpecialPeriods.EllipticFilling.SpecialFullFilling j) =
      specialFullFlow j s x.val :=
  rfl

attribute [local instance] SpecialPeriods.EllipticFilling.specialFullFillingChartedSpace
    SpecialPeriods.Threefold.specialEllipticPieceChartedSpace in
@[simp]
private theorem
    SpecialPeriods.Threefold.VerticalAction.Elliptic.specialFlow_parameter (j : Elliptic.Kind)
    (s : ℂ) (x : SpecialPeriods.Threefold.EllipticGeometry.LocalSpace j) :
    SpecialPeriods.Threefold.EllipticGeometry.parameter j (specialFlow j s x) =
      SpecialPeriods.Threefold.EllipticGeometry.parameter j x :=
  congrArg (Subtype.val : SpecialPeriods.Disc → ℂ) (specialFullFlow_projection j s x.val)

attribute [local instance] SpecialPeriods.EllipticFilling.specialFullFillingChartedSpace
    SpecialPeriods.Threefold.specialEllipticPieceChartedSpace in
@[simp]
private theorem SpecialPeriods.Threefold.VerticalAction.Elliptic.specialFlow_projectionToBase
    (j : Elliptic.Kind) (s : ℂ) (x : SpecialPeriods.Threefold.EllipticGeometry.LocalSpace j) :
    SpecialPeriods.Threefold.specialEllipticPieceProjectionToBase j (specialFlow j s x) =
      SpecialPeriods.Threefold.specialEllipticPieceProjectionToBase j x := by
  change
    (SpecialPeriods.Threefold.punctureChart (Option.some j)).symm
        (SpecialPeriods.Threefold.EllipticGeometry.parameter j (specialFlow j s x)) =
      (SpecialPeriods.Threefold.punctureChart (Option.some j)).symm
        (SpecialPeriods.Threefold.EllipticGeometry.parameter j x)
  rw [specialFlow_parameter]

attribute [local instance] SpecialPeriods.EllipticFilling.specialFullFillingChartedSpace
    SpecialPeriods.Threefold.specialEllipticPieceChartedSpace in
private theorem SpecialPeriods.Threefold.VerticalAction.Elliptic.specialFlow_joint_holomorphic
    (j : Elliptic.Kind) :
    ContMDiff (((modelWithCornersSelf ℂ Elliptic.FamilyModel)).prod (modelWithCornersSelf ℂ ℂ))
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω
      (fun x : SpecialPeriods.Threefold.EllipticGeometry.LocalSpace j × ℂ =>
        specialFlow j x.2 x.1) := by
  have hi :
    ContMDiff (((modelWithCornersSelf ℂ Elliptic.FamilyModel)).prod (modelWithCornersSelf ℂ ℂ))
      (((modelWithCornersSelf ℂ Elliptic.FamilyModel)).prod (modelWithCornersSelf ℂ ℂ)) ω
      (fun x : SpecialPeriods.Threefold.EllipticGeometry.LocalSpace j × ℂ =>
        ((x.1 : SpecialPeriods.EllipticFilling.SpecialFullFilling j), x.2)) :=
    (contMDiff_subtype_val.comp contMDiff_fst).prodMk contMDiff_snd
  have h := (specialFullFlow_joint_holomorphic j).comp hi
  intro x
  have he :
    ContMDiffAt (((modelWithCornersSelf ℂ Elliptic.FamilyModel)).prod (modelWithCornersSelf ℂ ℂ))
        (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω
        (fun y : SpecialPeriods.Threefold.EllipticGeometry.LocalSpace j × ℂ =>
          (specialFlow j y.2 y.1 : SpecialPeriods.EllipticFilling.SpecialFullFilling j))
        x ↔
      ContMDiffAt
        (((modelWithCornersSelf ℂ Elliptic.FamilyModel)).prod (modelWithCornersSelf ℂ ℂ))
        (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω
        (fun y : SpecialPeriods.Threefold.EllipticGeometry.LocalSpace j × ℂ =>
          specialFlow j y.2 y.1)
        x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (h x)

attribute [local instance] SpecialPeriods.EllipticFilling.specialFullFillingChartedSpace
    SpecialPeriods.Threefold.specialEllipticPieceChartedSpace in
@[simp]
private theorem
    SpecialPeriods.Threefold.VerticalAction.Elliptic.specialFlow_zero (j : Elliptic.Kind)
    (x : SpecialPeriods.Threefold.EllipticGeometry.LocalSpace j) : specialFlow j 0 x = x :=
  Subtype.ext
    (flow_zero (SpecialPeriods.EllipticFilling.specialLocalData j) j.twist
      (Elliptic.mainTwist_admissible j) x.val)

attribute [local instance] SpecialPeriods.EllipticFilling.specialFullFillingChartedSpace
    SpecialPeriods.Threefold.specialEllipticPieceChartedSpace in
private theorem SpecialPeriods.Threefold.VerticalAction.Elliptic.specialFlow_add (j : Elliptic.Kind)
    (s t : ℂ) (x : SpecialPeriods.Threefold.EllipticGeometry.LocalSpace j) :
    specialFlow j (s + t) x = specialFlow j s (specialFlow j t x) :=
  Subtype.ext
    (flow_add (SpecialPeriods.EllipticFilling.specialLocalData j) j.twist
      (Elliptic.mainTwist_admissible j) s t x.val)

attribute [local instance] SpecialPeriods.EllipticFilling.specialFullFillingChartedSpace
    SpecialPeriods.Threefold.specialEllipticPieceChartedSpace in
@[simp]
private theorem
    SpecialPeriods.Threefold.VerticalAction.Elliptic.specialFlow_int_cast (j : Elliptic.Kind)
    (n : ℤ) (x : SpecialPeriods.Threefold.EllipticGeometry.LocalSpace j) :
    specialFlow j (n : ℂ) x = x :=
  Subtype.ext
    (flow_int_cast (SpecialPeriods.EllipticFilling.specialLocalData j) j.twist
      (Elliptic.mainTwist_admissible j) n x.val)

private def SpecialPeriods.Threefold.VerticalAction.Elliptic.Gauge.familyFlow
    (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc) (s : ℂ)
    (x : Elliptic.LogGauge.FamilyStar P) : Elliptic.LogGauge.FamilyStar P :=
  ⟨SpecialPeriods.Threefold.VerticalAction.Period.flow P s x.val, x.property⟩

private def SpecialPeriods.Threefold.VerticalAction.Elliptic.Gauge.coverFlow (s : ℂ)
    (x : Elliptic.LogGauge.CoverStar) : Elliptic.LogGauge.CoverStar :=
  ⟨SpecialPeriods.Threefold.VerticalAction.Period.vectorFlow s x.val, x.property⟩

@[simp]
private theorem SpecialPeriods.Threefold.VerticalAction.Elliptic.Gauge.familyFlow_project
    (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc) (s : ℂ) (x : Elliptic.LogGauge.CoverStar) :
    familyFlow P s (Elliptic.LogGauge.project P x) =
      Elliptic.LogGauge.project P (coverFlow s x) :=
  Subtype.ext (SpecialPeriods.Threefold.VerticalAction.Period.flow_quotientMap P s x.val)

private theorem SpecialPeriods.Threefold.VerticalAction.Elliptic.Gauge.gaugeLift_coverFlow
    (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc) (v : Lattice) (a : ℂ → ℂ) (s : ℂ)
    (x : Elliptic.LogGauge.CoverStar) :
    Elliptic.LogGauge.gaugeLift P v a (coverFlow s x) =
      coverFlow s (Elliptic.LogGauge.gaugeLift P v a x) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change
      (x.val.2 + SpecialPeriods.Threefold.VerticalAction.Period.vector s) +
          a x.val.1 • Elliptic.LogGauge.periodVector P v x.val.1 =
        (x.val.2 + a x.val.1 • Elliptic.LogGauge.periodVector P v x.val.1) +
          SpecialPeriods.Threefold.VerticalAction.Period.vector s
    exact add_right_comm _ _ _

private theorem SpecialPeriods.Threefold.VerticalAction.Elliptic.Gauge.gaugeMap_familyFlow
    (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc) (v : Lattice) (s : ℂ)
    (x : Elliptic.LogGauge.FamilyStar P) :
    Elliptic.LogGauge.gaugeMap P v (familyFlow P s x) =
      familyFlow P s (Elliptic.LogGauge.gaugeMap P v x) := by
  obtain ⟨y, rfl⟩ := Elliptic.LogGauge.project_surjective P x
  rw [familyFlow_project, Elliptic.LogGauge.gaugeMap_project, Elliptic.LogGauge.gaugeMap_project,
    familyFlow_project, gaugeLift_coverFlow]

private def
    SpecialPeriods.Threefold.VerticalAction.Elliptic.Gauge.fillingStarFlow {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) (s : ℂ)
    (x : Elliptic.LogGauge.FillingStar D v hv) : Elliptic.LogGauge.FillingStar D v hv :=
  ⟨SpecialPeriods.Threefold.VerticalAction.Elliptic.flow D v hv s x.val,
    by
    change
      (D.projection v hv (SpecialPeriods.Threefold.VerticalAction.Elliptic.flow D v hv s x.val) :
          ℂ) ≠
        0
    rw [SpecialPeriods.Threefold.VerticalAction.Elliptic.flow_projection]
    exact x.property⟩

@[simp]
private theorem SpecialPeriods.Threefold.VerticalAction.Elliptic.Gauge.fillingStarFlow_project
    {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j) (v : Lattice)
    (hv : Elliptic.AdmissibleTwist j v) (s : ℂ) (x : Elliptic.LogGauge.FamilyStar D.periods) :
    fillingStarFlow D v hv s (Elliptic.LogGauge.fillingStarProject D v hv x) =
      Elliptic.LogGauge.fillingStarProject D v hv (familyFlow D.periods s x) :=
  Subtype.ext (SpecialPeriods.Threefold.VerticalAction.Elliptic.flow_quotient D v hv s x.val)

private theorem SpecialPeriods.Threefold.VerticalAction.Elliptic.Gauge.localTotalMap_familyFlow
    (P : HolomorphicPeriodMap ℂ ℍ) (j : Elliptic.Kind) (s : ℂ)
    (x : Elliptic.LogGauge.FamilyStar (SpecialPeriods.EllipticFilling.localPeriods P j)) :
    SpecialPeriods.EllipticFilling.localTotalMap P j
        (familyFlow (SpecialPeriods.EllipticFilling.localPeriods P j) s x) =
      SpecialPeriods.Threefold.VerticalAction.Period.flow (PeriodFamily.regularPeriods P) s
        (SpecialPeriods.EllipticFilling.localTotalMap P j x) := by rfl

private theorem SpecialPeriods.Threefold.VerticalAction.Elliptic.Gauge.regularMap_familyFlow
    (P : HolomorphicPeriodMap ℂ ℍ) (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (s : ℂ) (x : Elliptic.LogGauge.FamilyStar (SpecialPeriods.EllipticFilling.localPeriods P j)) :
    SpecialPeriods.EllipticFilling.regularMap P j h₁ h₂
        (familyFlow (SpecialPeriods.EllipticFilling.localPeriods P j) s x) =
      SpecialPeriods.Threefold.VerticalAction.Triangle.flow (PeriodFamily.regularData P h₁ h₂) s
        (SpecialPeriods.EllipticFilling.regularMap P j h₁ h₂ x) := by
  change
    (PeriodFamily.regularData P h₁ h₂).quotient
        (SpecialPeriods.EllipticFilling.localTotalMap P j
          (familyFlow (SpecialPeriods.EllipticFilling.localPeriods P j) s x)) =
      SpecialPeriods.Threefold.VerticalAction.Triangle.flow (PeriodFamily.regularData P h₁ h₂) s
        ((PeriodFamily.regularData P h₁ h₂).quotient
          (SpecialPeriods.EllipticFilling.localTotalMap P j x))
  rw [SpecialPeriods.Threefold.VerticalAction.Triangle.flow_quotient, localTotalMap_familyFlow]
  rfl

private theorem
    SpecialPeriods.Threefold.VerticalAction.Elliptic.Gauge.puncturedFillingBiholomorph_project
    (P : HolomorphicPeriodMap ℂ ℍ) (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (x : Elliptic.LogGauge.FamilyStar (SpecialPeriods.EllipticFilling.localPeriods P j)) :
    (SpecialPeriods.EllipticFilling.puncturedFillingBiholomorph P j h₁ h₂
          (Elliptic.LogGauge.fillingStarProject
            (SpecialPeriods.EllipticFilling.localData P h₁ h₂ j) j.twist
            (Elliptic.mainTwist_admissible j) x)).val =
      SpecialPeriods.EllipticFilling.regularMap P j h₁ h₂
        (Elliptic.LogGauge.gaugeMap (SpecialPeriods.EllipticFilling.localPeriods P j) j.twist
          x) := by
  change
    (SpecialPeriods.EllipticFilling.tautologicalOverlapBiholomorph P j h₁ h₂
          (Elliptic.LogGauge.fillingToTautologicalBiholomorph
            (SpecialPeriods.EllipticFilling.localData P h₁ h₂ j) j.twist
            (Elliptic.mainTwist_admissible j)
            (Elliptic.LogGauge.fillingStarProject
              (SpecialPeriods.EllipticFilling.localData P h₁ h₂ j) j.twist
              (Elliptic.mainTwist_admissible j) x))).val =
      _
  rw [Elliptic.LogGauge.fillingToTautologicalBiholomorph_project]
  exact
    congrArg Subtype.val
      (SpecialPeriods.EllipticFilling.tautologicalOverlapBiholomorph_project P j h₁ h₂
        (Elliptic.LogGauge.gaugeMap (SpecialPeriods.EllipticFilling.localPeriods P j) j.twist x))

private theorem
  SpecialPeriods.Threefold.VerticalAction.Elliptic.Gauge.puncturedFillingBiholomorph_fillingStarFlow
    (P : HolomorphicPeriodMap ℂ ℍ) (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (s : ℂ) (x : SpecialPeriods.EllipticFilling.MainFillingStar P j h₁ h₂) :
    (SpecialPeriods.EllipticFilling.puncturedFillingBiholomorph P j h₁ h₂
          (fillingStarFlow (SpecialPeriods.EllipticFilling.localData P h₁ h₂ j) j.twist
            (Elliptic.mainTwist_admissible j) s x)).val =
      SpecialPeriods.Threefold.VerticalAction.Triangle.flow (PeriodFamily.regularData P h₁ h₂) s
        (SpecialPeriods.EllipticFilling.puncturedFillingBiholomorph P j h₁ h₂ x).val := by
  obtain ⟨y, rfl⟩ :=
    Elliptic.LogGauge.fillingStarProject_surjective
      (SpecialPeriods.EllipticFilling.localData P h₁ h₂ j) j.twist
      (Elliptic.mainTwist_admissible j) x
  rw [fillingStarFlow_project, puncturedFillingBiholomorph_project,
    puncturedFillingBiholomorph_project, SpecialPeriods.EllipticFilling.localData_periods,
    gaugeMap_familyFlow, regularMap_familyFlow]

attribute [local instance] SpecialPeriods.EllipticFilling.specialFullFillingChartedSpace
    SpecialPeriods.Threefold.specialEllipticPieceChartedSpace
    SpecialPeriods.Threefold.specialRegularFamilyChartedSpace in
private theorem SpecialPeriods.Threefold.VerticalAction.Elliptic.specialEllipticOverlap_specialFlow
    (j : Elliptic.Kind) (s : ℂ) (x : SpecialPeriods.Threefold.EllipticGeometry.LocalSpace j)
    (hx : x ∈ (SpecialPeriods.Threefold.specialEllipticOverlap j).source) :
    SpecialPeriods.Threefold.specialEllipticOverlap j (specialFlow j s x) =
      SpecialPeriods.Threefold.VerticalAction.Regular.flow s
        (SpecialPeriods.Threefold.specialEllipticOverlap j x) := by
  have hx0 : (SpecialPeriods.EllipticFilling.specialFullFillingProjection j x.val : ℂ) ≠ 0 :=
    (SpecialPeriods.EllipticFilling.smallOverlap_mem_source SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
          SpecialPeriods.Threefold.specialBaseCover j x).mp
      hx
  have hs0 :
    (SpecialPeriods.EllipticFilling.specialFullFillingProjection j (specialFlow j s x).val : ℂ) ≠
      0 := by
    rw [specialFlow_coe, specialFullFlow_projection]
    exact hx0
  change
    SpecialPeriods.EllipticFilling.smallOverlap SpecialPeriods.specialPeriodMap
        SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
        SpecialPeriods.Threefold.specialBaseCover j (specialFlow j s x) =
      SpecialPeriods.Threefold.VerticalAction.Regular.flow s
        (SpecialPeriods.EllipticFilling.smallOverlap SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
          SpecialPeriods.Threefold.specialBaseCover j x)
  rw [SpecialPeriods.EllipticFilling.smallOverlap_apply_mainStar SpecialPeriods.specialPeriodMap
      SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
      SpecialPeriods.Threefold.specialBaseCover j (specialFlow j s x) hs0,
    SpecialPeriods.EllipticFilling.smallOverlap_apply_mainStar SpecialPeriods.specialPeriodMap
      SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
      SpecialPeriods.Threefold.specialBaseCover j x hx0]
  exact
    Gauge.puncturedFillingBiholomorph_fillingStarFlow SpecialPeriods.specialPeriodMap j
      SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂ s
      ⟨x.val, hx0⟩

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace in
private def SpecialPeriods.Threefold.VerticalAction.localFlow :
    (i : SpecialPeriods.Threefold.Index) →
      ℂ → SpecialPeriods.Threefold.localPiece i → SpecialPeriods.Threefold.localPiece i
  | none => Regular.flow
  | some Option.none => Cusp.specialFlow
  | some (Option.some j) => Elliptic.specialFlow j

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace in
private theorem SpecialPeriods.Threefold.VerticalAction.localFlow_projection
    (i : SpecialPeriods.Threefold.Index) (s : ℂ) (x : SpecialPeriods.Threefold.localPiece i) :
    SpecialPeriods.Threefold.localProjectionToBase i (localFlow i s x) =
      SpecialPeriods.Threefold.localProjectionToBase i x := by
  cases i with
  | none => exact Regular.flow_projection s x
  | some i =>
    cases i with
    | none => exact Cusp.specialCuspPieceProjectionToBase_specialFlow s x
    | some j => exact Elliptic.specialFlow_projectionToBase j s x

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace in
private theorem SpecialPeriods.Threefold.VerticalAction.localFlow_overlap
    (i : SpecialPeriods.Threefold.Puncture) (s : ℂ)
    (x : SpecialPeriods.Threefold.localPiece (Option.some i))
    (hx : x ∈ (SpecialPeriods.Threefold.localOverlap i).source) :
    SpecialPeriods.Threefold.localOverlap i (localFlow (Option.some i) s x) =
      localFlow Option.none s (SpecialPeriods.Threefold.localOverlap i x) := by
  cases i with
  | none => exact Cusp.specialCuspOverlap_specialFlow s x hx
  | some j => exact Elliptic.specialEllipticOverlap_specialFlow j s x hx

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace in
private theorem SpecialPeriods.Threefold.VerticalAction.localFlow_zero
    (i : SpecialPeriods.Threefold.Index) (x : SpecialPeriods.Threefold.localPiece i) :
    localFlow i 0 x = x := by
  cases i with
  | none => exact Regular.flow_zero x
  | some i =>
    cases i with
    | none => exact Cusp.specialFlow_zero x
    | some j => exact Elliptic.specialFlow_zero j x

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace in
private theorem
    SpecialPeriods.Threefold.VerticalAction.localFlow_add (i : SpecialPeriods.Threefold.Index)
    (s t : ℂ) (x : SpecialPeriods.Threefold.localPiece i) :
    localFlow i (s + t) x = localFlow i s (localFlow i t x) := by
  cases i with
  | none => exact Regular.flow_add s t x
  | some i =>
    cases i with
    | none => exact Cusp.specialFlow_add s t x
    | some j => exact Elliptic.specialFlow_add j s t x

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace in
private theorem SpecialPeriods.Threefold.VerticalAction.localFlow_int_cast
    (i : SpecialPeriods.Threefold.Index) (n : ℤ) (x : SpecialPeriods.Threefold.localPiece i) :
    localFlow i (n : ℂ) x = x := by
  cases i with
  | none => exact Regular.flow_int_cast n x
  | some i =>
    cases i with
    | none => exact Cusp.specialFlow_int_cast n x
    | some j => exact Elliptic.specialFlow_int_cast j n x

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace in
private theorem SpecialPeriods.Threefold.VerticalAction.localFlow_joint_holomorphic
    (i : SpecialPeriods.Threefold.Index) :
    ContMDiff (((modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))).prod (modelWithCornersSelf ℂ ℂ))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω
      (fun p : SpecialPeriods.Threefold.localPiece i × ℂ => localFlow i p.2 p.1) := by
  cases i with
  | none => exact Regular.jointFlow_holomorphic
  | some i =>
    cases i with
    | none => exact Cusp.specialFlow_joint_common_holomorphic
    | some j => exact Elliptic.specialFlow_joint_holomorphic j

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace in
private def SpecialPeriods.Threefold.VerticalAction.flow (s : ℂ) :
    SpecialPeriods.Threefold.Space → SpecialPeriods.Threefold.Space :=
  Gluing.glue localFlow localFlow_projection localFlow_overlap s

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace in
@[simp]
private theorem SpecialPeriods.Threefold.VerticalAction.flow_inclusion (s : ℂ)
    (i : SpecialPeriods.Threefold.Index) (x : SpecialPeriods.Threefold.localPiece i) :
    flow s (SpecialPeriods.Threefold.inclusion i x) =
      SpecialPeriods.Threefold.inclusion i (localFlow i s x) :=
  Gluing.glue_inclusion localFlow localFlow_projection localFlow_overlap s i x

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace in
@[simp]
private theorem SpecialPeriods.Threefold.VerticalAction.flow_elliptic (j : Elliptic.Kind) (s : ℂ)
    (x : SpecialPeriods.Threefold.EllipticGeometry.LocalSpace j) :
    flow s (SpecialPeriods.Threefold.EllipticGeometry.inclusion j x) =
      SpecialPeriods.Threefold.EllipticGeometry.inclusion j (Elliptic.specialFlow j s x) :=
  flow_inclusion s (Option.some (Option.some j)) x

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace in
@[simp]
private theorem
    SpecialPeriods.Threefold.VerticalAction.flow_zero (x : SpecialPeriods.Threefold.Space) :
    flow 0 x = x :=
  Gluing.glue_zero localFlow localFlow_projection localFlow_overlap localFlow_zero x

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace in
private theorem SpecialPeriods.Threefold.VerticalAction.flow_add (s t : ℂ)
    (x : SpecialPeriods.Threefold.Space) : flow (s + t) x = flow s (flow t x) :=
  Gluing.glue_add localFlow localFlow_projection localFlow_overlap localFlow_add s t x

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace in
@[simp]
private theorem SpecialPeriods.Threefold.VerticalAction.flow_int_cast (n : ℤ)
    (x : SpecialPeriods.Threefold.Space) : flow (n : ℂ) x = x :=
  Gluing.glue_int_cast localFlow localFlow_projection localFlow_overlap localFlow_int_cast n x

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace in
@[simp]
private theorem SpecialPeriods.Threefold.VerticalAction.projection_flow (s : ℂ)
    (x : SpecialPeriods.Threefold.Space) :
    SpecialPeriods.Threefold.projection (flow s x) = SpecialPeriods.Threefold.projection x :=
  Gluing.glue_projection localFlow localFlow_projection localFlow_overlap s x

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace in
@[simp]
private theorem SpecialPeriods.Threefold.VerticalAction.projectionSphere_flow (s : ℂ)
    (x : SpecialPeriods.Threefold.Space) :
    SpecialPeriods.Threefold.projectionSphere (flow s x) =
      SpecialPeriods.Threefold.projectionSphere x := by
  simp only [SpecialPeriods.Threefold.projectionSphere, Function.comp_def, projection_flow]

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace in
private theorem SpecialPeriods.Threefold.VerticalAction.jointFlow_holomorphic :
    ContMDiff (((modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))).prod (modelWithCornersSelf ℂ ℂ))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω
      (fun p : SpecialPeriods.Threefold.Space × ℂ => flow p.2 p.1) :=
  Gluing.glue_joint_holomorphic localFlow localFlow_projection localFlow_overlap
    localFlow_joint_holomorphic

private def
    SpecialPeriods.Threefold.VerticalAction.Exponential.normalizedExponential (s : ℂ) : ℂˣ :=
  Units.mk0 (CuspUniformization.exponential s) (CuspUniformization.exponential_ne_zero s)

@[simp]
private theorem
    SpecialPeriods.Threefold.VerticalAction.Exponential.normalizedExponential_coe (s : ℂ) :
    (normalizedExponential s : ℂ) = CuspUniformization.exponential s :=
  rfl

@[simp]
private theorem SpecialPeriods.Threefold.VerticalAction.Exponential.normalizedExponential_zero :
    normalizedExponential 0 = 1 := by
  apply Units.ext
  exact CuspUniformization.exponential_zero

private theorem
    SpecialPeriods.Threefold.VerticalAction.Exponential.normalizedExponential_add (s t : ℂ) :
    normalizedExponential (s + t) = normalizedExponential s * normalizedExponential t := by
  apply Units.ext
  exact CuspUniformization.exponential_add s t

@[simp]
private theorem
    SpecialPeriods.Threefold.VerticalAction.Exponential.normalizedExponential_int (n : ℤ) :
    normalizedExponential (n : ℂ) = 1 := by
  apply Units.ext
  exact CuspUniformization.exponential_int n

private theorem SpecialPeriods.Threefold.VerticalAction.Exponential.normalizedExponential_eq_iff
    (s t : ℂ) : normalizedExponential s = normalizedExponential t ↔ ∃ n : ℤ, s = t + n := by
  rw [← Units.val_inj, normalizedExponential_coe, normalizedExponential_coe]
  exact CuspUniformization.exponential_eq_iff s t

private theorem SpecialPeriods.Threefold.VerticalAction.Exponential.normalizedExponential_eq_one_iff
    (s : ℂ) : normalizedExponential s = 1 ↔ ∃ n : ℤ, s = (n : ℂ) := by
  simpa using normalizedExponential_eq_iff s 0

private theorem
    SpecialPeriods.Threefold.VerticalAction.Exponential.normalizedExponential_surjective :
    Function.Surjective normalizedExponential := by
  intro u
  refine ⟨CuspUniformization.logarithm (u : ℂ), ?_⟩
  apply Units.ext
  exact CuspUniformization.exponential_logarithm u.ne_zero

private def SpecialPeriods.Threefold.VerticalAction.Exponential.integerPeriods : AddSubgroup ℂ :=
  AddSubgroup.zmultiples (1 : ℂ)

private theorem SpecialPeriods.Threefold.VerticalAction.Exponential.mem_integerPeriods_iff (s : ℂ) :
    s ∈ integerPeriods ↔ ∃ n : ℤ, s = (n : ℂ) := by
  simp only [integerPeriods, AddSubgroup.mem_zmultiples_iff, zsmul_one, eq_comm]

private def SpecialPeriods.Threefold.VerticalAction.Exponential.Parameter :=
  ℂ ⧸ integerPeriods

private instance SpecialPeriods.Threefold.VerticalAction.Exponential.instLocal1 :
    AddCommGroup Parameter :=
  inferInstanceAs (AddCommGroup (ℂ ⧸ integerPeriods))

private def
    SpecialPeriods.Threefold.VerticalAction.Exponential.parameterProjection : ℂ →+ Parameter :=
  QuotientAddGroup.mk' integerPeriods

private theorem SpecialPeriods.Threefold.VerticalAction.Exponential.parameterProjection_surjective :
    Function.Surjective parameterProjection :=
  QuotientAddGroup.mk'_surjective integerPeriods

private theorem
    SpecialPeriods.Threefold.VerticalAction.Exponential.parameterProjection_eq_iff (s t : ℂ) :
    parameterProjection s = parameterProjection t ↔ ∃ n : ℤ, s - t = (n : ℂ) :=
  QuotientAddGroup.eq_iff_sub_mem.trans (mem_integerPeriods_iff (s - t))

private def SpecialPeriods.Threefold.VerticalAction.Exponential.normalizedExponentialAddHom :
    ℂ →+ Additive ℂˣ
    where
  toFun s := Additive.ofMul (normalizedExponential s)
  map_zero' := normalizedExponential_zero
  map_add' := normalizedExponential_add

private def SpecialPeriods.Threefold.VerticalAction.Exponential.parameterExponentialAddHom :
    Parameter →+ Additive ℂˣ :=
  QuotientAddGroup.lift integerPeriods normalizedExponentialAddHom
    (by
      intro s hs
      change normalizedExponential s = 1
      exact (normalizedExponential_eq_one_iff s).mpr ((mem_integerPeriods_iff s).mp hs))

private def
    SpecialPeriods.Threefold.VerticalAction.Exponential.parameterExponential (p : Parameter) :
    ℂˣ :=
  Additive.toMul (parameterExponentialAddHom p)

@[simp]
private theorem SpecialPeriods.Threefold.VerticalAction.Exponential.parameterExponential_projection
    (s : ℂ) : parameterExponential (parameterProjection s) = normalizedExponential s :=
  rfl

private theorem SpecialPeriods.Threefold.VerticalAction.Exponential.parameterExponential_injective :
    Function.Injective parameterExponential := by
  intro p q h
  obtain ⟨s, rfl⟩ := parameterProjection_surjective p
  obtain ⟨t, rfl⟩ := parameterProjection_surjective q
  rw [parameterExponential_projection, parameterExponential_projection] at h
  obtain ⟨n, hn⟩ := (normalizedExponential_eq_iff s t).mp h
  apply (parameterProjection_eq_iff s t).mpr
  exact ⟨n, by simp [hn]⟩

private theorem
    SpecialPeriods.Threefold.VerticalAction.Exponential.parameterExponential_surjective :
    Function.Surjective parameterExponential := by
  intro u
  obtain ⟨s, hs⟩ := normalizedExponential_surjective u
  exact ⟨parameterProjection s, hs⟩

private theorem SpecialPeriods.Threefold.VerticalAction.Exponential.parameterExponential_bijective :
    Function.Bijective parameterExponential :=
  ⟨parameterExponential_injective, parameterExponential_surjective⟩

private def SpecialPeriods.Threefold.VerticalAction.Exponential.parameterMulEquiv :
    Multiplicative Parameter ≃* ℂˣ :=
  MulEquiv.ofBijective parameterExponentialAddHom.toMultiplicativeLeft
    parameterExponential_bijective

@[simp]
private theorem
    SpecialPeriods.Threefold.VerticalAction.Exponential.parameterMulEquiv_projection (s : ℂ) :
    parameterMulEquiv (Multiplicative.ofAdd (parameterProjection s)) = normalizedExponential s :=
  rfl

private theorem
    SpecialPeriods.Threefold.VerticalAction.Exponential.normalizedExponential_holomorphic :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω normalizedExponential := by
  apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
  exact CuspUniformization.exponential_holomorphic.contMDiff

private def SpecialPeriods.Threefold.VerticalAction.Exponential.unitsExponentialChart (s : ℂ) :
    PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ℂ ℂˣ ω
    where
  toFun := normalizedExponential
  invFun := (SpecialPeriods.CuspFamily.scalarExponentialChart s).symm ∘ Units.val
  source := (SpecialPeriods.CuspFamily.scalarExponentialChart s).source
  target := Units.val ⁻¹' (SpecialPeriods.CuspFamily.scalarExponentialChart s).target
  map_source' := by
    intro t ht
    exact (SpecialPeriods.CuspFamily.scalarExponentialChart s).map_source ht
  map_target' := by
    intro t ht
    exact (SpecialPeriods.CuspFamily.scalarExponentialChart s).map_target ht
  left_inv' := by
    intro t ht
    exact (SpecialPeriods.CuspFamily.scalarExponentialChart s).left_inv ht
  right_inv' := by
    intro t ht
    apply Units.ext
    exact (SpecialPeriods.CuspFamily.scalarExponentialChart s).right_inv ht
  open_source := (SpecialPeriods.CuspFamily.scalarExponentialChart s).open_source
  open_target :=
    (SpecialPeriods.CuspFamily.scalarExponentialChart s).open_target.preimage Units.continuous_val
  contMDiffOn_toFun := normalizedExponential_holomorphic.contMDiffOn
  contMDiffOn_invFun :=
    (SpecialPeriods.CuspFamily.scalarExponentialChart_symm_holomorphic s).contMDiffOn.comp
      Units.contMDiff_val.contMDiffOn (fun _ ht => ht)

private theorem
  SpecialPeriods.Threefold.VerticalAction.Exponential.normalizedExponential_isLocalDiffeomorph :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω normalizedExponential := by
  intro s
  exact
    ⟨unitsExponentialChart s, SpecialPeriods.CuspFamily.scalarExponentialChart_mem_source s,
      fun _ _ => rfl⟩

private theorem
    SpecialPeriods.Threefold.VerticalAction.Exponential.normalizedExponential_continuous :
    Continuous normalizedExponential :=
  normalizedExponential_holomorphic.continuous

private structure SpecialPeriods.Threefold.VerticalAction.Factor.AdditiveFlow (M : Type*) where
  toFun : ℂ → M → M
  zero_apply : ∀ x, toFun 0 x = x
  add_apply : ∀ s t x, toFun (s + t) x = toFun s (toFun t x)
  int_apply : ∀ (n : ℤ) x, toFun (n : ℂ) x = x

private instance SpecialPeriods.Threefold.VerticalAction.Factor.instCoeFun1 {M : Type*} :
    CoeFun (AdditiveFlow M) (fun _ => ℂ → M → M) :=
  ⟨AdditiveFlow.toFun⟩

private theorem
  SpecialPeriods.Threefold.VerticalAction.Factor.AdditiveFlow.apply_eq_of_parameterProjection_eq
    {M : Type*} (F : SpecialPeriods.Threefold.VerticalAction.Factor.AdditiveFlow M) {s t : ℂ}
    (h :
      SpecialPeriods.Threefold.VerticalAction.Exponential.parameterProjection s =
        SpecialPeriods.Threefold.VerticalAction.Exponential.parameterProjection t)
    (x : M) : F s x = F t x := by
  obtain ⟨n, hn⟩ :=
    (SpecialPeriods.Threefold.VerticalAction.Exponential.parameterProjection_eq_iff s t).mp h
  have hs : s = t + (n : ℂ) := by linear_combination hn
  rw [hs, F.add_apply, F.int_apply]

private def SpecialPeriods.Threefold.VerticalAction.Factor.AdditiveFlow.parameterAct {M : Type*}
    (F : SpecialPeriods.Threefold.VerticalAction.Factor.AdditiveFlow M)
    (p : SpecialPeriods.Threefold.VerticalAction.Exponential.Parameter) (x : M) : M :=
  Quotient.lift (fun s : ℂ => F s x)
    (fun _ _ h => F.apply_eq_of_parameterProjection_eq (Quotient.sound h) x) p

@[simp]
private theorem SpecialPeriods.Threefold.VerticalAction.Factor.AdditiveFlow.parameterAct_projection
    {M : Type*} (F : SpecialPeriods.Threefold.VerticalAction.Factor.AdditiveFlow M) (s : ℂ)
    (x : M) :
    F.parameterAct (SpecialPeriods.Threefold.VerticalAction.Exponential.parameterProjection s) x =
      F s x :=
  rfl

private def SpecialPeriods.Threefold.VerticalAction.Factor.AdditiveFlow.act {M : Type*}
    (F : SpecialPeriods.Threefold.VerticalAction.Factor.AdditiveFlow M) (u : ℂˣ) (x : M) : M :=
  F.parameterAct
    (SpecialPeriods.Threefold.VerticalAction.Exponential.parameterMulEquiv.symm u).toAdd x

@[simp]
private theorem
    SpecialPeriods.Threefold.VerticalAction.Factor.AdditiveFlow.act_normalizedExponential
    {M : Type*} (F : SpecialPeriods.Threefold.VerticalAction.Factor.AdditiveFlow M) (s : ℂ)
    (x : M) :
    F.act (SpecialPeriods.Threefold.VerticalAction.Exponential.normalizedExponential s) x =
      F s x := by
  have he :
    SpecialPeriods.Threefold.VerticalAction.Exponential.parameterMulEquiv.symm
        (SpecialPeriods.Threefold.VerticalAction.Exponential.normalizedExponential s) =
      Multiplicative.ofAdd
        (SpecialPeriods.Threefold.VerticalAction.Exponential.parameterProjection s) := by
    apply SpecialPeriods.Threefold.VerticalAction.Exponential.parameterMulEquiv.injective
    rw [SpecialPeriods.Threefold.VerticalAction.Exponential.parameterMulEquiv.apply_symm_apply,
      SpecialPeriods.Threefold.VerticalAction.Exponential.parameterMulEquiv_projection]
  rw [act, he]
  exact F.parameterAct_projection s x

@[simp]
private theorem SpecialPeriods.Threefold.VerticalAction.Factor.AdditiveFlow.act_one {M : Type*}
    (F : SpecialPeriods.Threefold.VerticalAction.Factor.AdditiveFlow M) (x : M) : F.act 1 x = x :=
  by
  simpa only [SpecialPeriods.Threefold.VerticalAction.Exponential.normalizedExponential_zero,
    F.zero_apply] using F.act_normalizedExponential 0 x

private theorem SpecialPeriods.Threefold.VerticalAction.Factor.AdditiveFlow.act_mul {M : Type*}
    (F : SpecialPeriods.Threefold.VerticalAction.Factor.AdditiveFlow M) (u v : ℂˣ) (x : M) :
    F.act (u * v) x = F.act u (F.act v x) := by
  obtain ⟨s, rfl⟩ :=
    SpecialPeriods.Threefold.VerticalAction.Exponential.normalizedExponential_surjective u
  obtain ⟨t, rfl⟩ :=
    SpecialPeriods.Threefold.VerticalAction.Exponential.normalizedExponential_surjective v
  rw [← SpecialPeriods.Threefold.VerticalAction.Exponential.normalizedExponential_add,
    F.act_normalizedExponential, F.act_normalizedExponential, F.act_normalizedExponential,
    F.add_apply]

@[instance_reducible]
private def SpecialPeriods.Threefold.VerticalAction.Factor.AdditiveFlow.action {M : Type*}
    (F : SpecialPeriods.Threefold.VerticalAction.Factor.AdditiveFlow M) : MulAction ℂˣ M
    where
  smul := F.act
  one_smul := F.act_one
  mul_smul := F.act_mul

@[simp]
private theorem
    SpecialPeriods.Threefold.VerticalAction.Factor.AdditiveFlow.action_normalizedExponential
    {M : Type*} (F : SpecialPeriods.Threefold.VerticalAction.Factor.AdditiveFlow M) (s : ℂ)
    (x : M) :
    letI := F.action
    SpecialPeriods.Threefold.VerticalAction.Exponential.normalizedExponential s • x = F s x :=
  F.act_normalizedExponential s x

@[simp]
private theorem SpecialPeriods.Threefold.VerticalAction.Factor.AdditiveFlow.act_inv_act {M : Type*}
    (F : SpecialPeriods.Threefold.VerticalAction.Factor.AdditiveFlow M) (u : ℂˣ) (x : M) :
    F.act u⁻¹ (F.act u x) = x := by rw [← F.act_mul, inv_mul_cancel, F.act_one]

@[simp]
private theorem SpecialPeriods.Threefold.VerticalAction.Factor.AdditiveFlow.act_act_inv {M : Type*}
    (F : SpecialPeriods.Threefold.VerticalAction.Factor.AdditiveFlow M) (u : ℂˣ) (x : M) :
    F.act u (F.act u⁻¹ x) = x := by rw [← F.act_mul, mul_inv_cancel, F.act_one]

private def SpecialPeriods.Threefold.VerticalAction.Factor.AdditiveFlow.equiv {M : Type*}
    (F : SpecialPeriods.Threefold.VerticalAction.Factor.AdditiveFlow M) (u : ℂˣ) : M ≃ M
    where
  toFun := F.act u
  invFun := F.act u⁻¹
  left_inv := F.act_inv_act u
  right_inv := F.act_act_inv u

private theorem SpecialPeriods.Threefold.VerticalAction.Factor.AdditiveFlow.act_holomorphic
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
    [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℂ E H}
    (F : SpecialPeriods.Threefold.VerticalAction.Factor.AdditiveFlow M)
    (hF : ContMDiff (I.prod 𝓘(ℂ)) I ω (fun p : M × ℂ => F p.2 p.1)) :
    ContMDiff (I.prod 𝓘(ℂ)) I ω (fun p : M × ℂˣ => F.act p.2 p.1) := by
  intro p
  obtain ⟨s, hs⟩ :=
    SpecialPeriods.Threefold.VerticalAction.Exponential.normalizedExponential_surjective p.2
  let e :=
    SpecialPeriods.Threefold.VerticalAction.Exponential.normalizedExponential_isLocalDiffeomorph s
  have hlog : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω e.localInverse p.2 := by
    simpa only [hs] using e.localInverse_contMDiffAt
  have hpair :
    ContMDiffAt (I.prod 𝓘(ℂ)) (I.prod 𝓘(ℂ)) ω (fun q : M × ℂˣ => (q.1, e.localInverse q.2)) p :=
    contMDiffAt_fst.prodMk (hlog.comp p contMDiffAt_snd)
  have hcomp : ContMDiffAt (I.prod 𝓘(ℂ)) I ω (fun q : M × ℂˣ => F (e.localInverse q.2) q.1) p :=
    hF.contMDiffAt.comp p hpair
  apply hcomp.congr_of_eventuallyEq
  have he := e.localInverse_eventuallyEq_right
  rw [hs] at he
  filter_upwards [(continuous_snd.tendsto p).eventually he] with q hq
  change
    SpecialPeriods.Threefold.VerticalAction.Exponential.normalizedExponential
        (e.localInverse q.2) =
      q.2 at hq
  exact
    (congrArg (fun u => F.act u q.1) hq).symm.trans
      (F.act_normalizedExponential (e.localInverse q.2) q.1)

private theorem SpecialPeriods.Threefold.VerticalAction.Factor.AdditiveFlow.act_holomorphic_const
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
    [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℂ E H}
    (F : SpecialPeriods.Threefold.VerticalAction.Factor.AdditiveFlow M)
    (hF : ContMDiff (I.prod 𝓘(ℂ)) I ω (fun p : M × ℂ => F p.2 p.1)) (u : ℂˣ) :
    ContMDiff I I ω (F.act u) :=
  (F.act_holomorphic hF).comp (contMDiff_id.prodMk contMDiff_const)

private theorem SpecialPeriods.Threefold.VerticalAction.Factor.AdditiveFlow.action_holomorphic
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
    [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℂ E H}
    (F : SpecialPeriods.Threefold.VerticalAction.Factor.AdditiveFlow M)
    (hF : ContMDiff (I.prod 𝓘(ℂ)) I ω (fun p : M × ℂ => F p.2 p.1)) :
    letI := F.action
    ContMDiff (I.prod 𝓘(ℂ)) I ω (fun p : M × ℂˣ => p.2 • p.1) :=
  F.act_holomorphic hF

private def SpecialPeriods.Threefold.VerticalAction.Factor.AdditiveFlow.biholomorph {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H] [TopologicalSpace M]
    [ChartedSpace H M] (I : ModelWithCorners ℂ E H)
    (F : SpecialPeriods.Threefold.VerticalAction.Factor.AdditiveFlow M)
    (hF : ContMDiff (I.prod 𝓘(ℂ)) I ω (fun p : M × ℂ => F p.2 p.1)) (u : ℂˣ) :
    Diffeomorph I I M M ω where
  toEquiv := F.equiv u
  contMDiff_toFun := F.act_holomorphic_const hF u
  contMDiff_invFun := F.act_holomorphic_const hF u⁻¹

private theorem
  SpecialPeriods.Threefold.VerticalAction.Factor.AdditiveFlow.biholomorph_normalizedExponential
    {M : Type*} (F : SpecialPeriods.Threefold.VerticalAction.Factor.AdditiveFlow M) {E H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H] [TopologicalSpace M]
    [ChartedSpace H M] {I : ModelWithCorners ℂ E H}
    (hF : ContMDiff (I.prod 𝓘(ℂ)) I ω (fun p : M × ℂ => F p.2 p.1)) (s : ℂ) (x : M) :
    F.biholomorph I hF
        (SpecialPeriods.Threefold.VerticalAction.Exponential.normalizedExponential s) x =
      F s x :=
  F.act_normalizedExponential s x

attribute [local instance] SpecialPeriods.Threefold.chartedSpace in
private def SpecialPeriods.Threefold.VerticalAction.additiveFlow :
    Factor.AdditiveFlow SpecialPeriods.Threefold.Space
    where
  toFun := flow
  zero_apply := flow_zero
  add_apply := flow_add
  int_apply := flow_int_cast

attribute [local instance] SpecialPeriods.Threefold.chartedSpace in
@[instance_reducible]
private def SpecialPeriods.Threefold.VerticalAction.action :
    MulAction ℂˣ SpecialPeriods.Threefold.Space :=
  additiveFlow.action

attribute [local instance] SpecialPeriods.Threefold.chartedSpace in
private theorem SpecialPeriods.Threefold.VerticalAction.action_normalizedExponential (s : ℂ)
    (x : SpecialPeriods.Threefold.Space) :
    letI := action
    Exponential.normalizedExponential s • x = flow s x :=
  additiveFlow.action_normalizedExponential s x

attribute [local instance] SpecialPeriods.Threefold.chartedSpace in
private theorem SpecialPeriods.Threefold.VerticalAction.action_joint_holomorphic :
    letI := action
    ContMDiff (((modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))).prod (modelWithCornersSelf ℂ ℂ))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω
      (fun p : SpecialPeriods.Threefold.Space × ℂˣ => p.2 • p.1) :=
  additiveFlow.action_holomorphic jointFlow_holomorphic

attribute [local instance] SpecialPeriods.Threefold.chartedSpace in
private theorem SpecialPeriods.Threefold.VerticalAction.action_holomorphic :
    letI := action
    ContMDiff (((modelWithCornersSelf ℂ ℂ)).prod (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω
      (fun p : ℂˣ × SpecialPeriods.Threefold.Space => p.1 • p.2) := by
  let := action
  have hs :
    ContMDiff (((modelWithCornersSelf ℂ ℂ)).prod (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)))
      (((modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))).prod (modelWithCornersSelf ℂ ℂ)) ω
      (fun p : ℂˣ × SpecialPeriods.Threefold.Space => (p.2, p.1)) :=
    contMDiff_snd.prodMk contMDiff_fst
  have hh := action_joint_holomorphic.comp hs
  simpa only [Function.comp_def] using hh

attribute [local instance] SpecialPeriods.Threefold.chartedSpace in
@[simp]
private theorem SpecialPeriods.Threefold.VerticalAction.projectionSphere_action (u : ℂˣ)
    (x : SpecialPeriods.Threefold.Space) :
    letI := action
    SpecialPeriods.Threefold.projectionSphere (u • x) =
      SpecialPeriods.Threefold.projectionSphere x := by
  let := action
  obtain ⟨s, rfl⟩ := Exponential.normalizedExponential_surjective u
  rw [action_normalizedExponential, projectionSphere_flow]

attribute [local instance] SpecialPeriods.Threefold.chartedSpace in
private def SpecialPeriods.Threefold.VerticalAction.actionBiholomorph (u : ℂˣ) :
    Diffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) SpecialPeriods.Threefold.Space
      SpecialPeriods.Threefold.Space ω :=
  additiveFlow.biholomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) jointFlow_holomorphic u

attribute [local instance] SpecialPeriods.Threefold.chartedSpace in
@[simp]
private theorem SpecialPeriods.Threefold.VerticalAction.actionBiholomorph_exponential (s : ℂ)
    (x : SpecialPeriods.Threefold.Space) :
    actionBiholomorph (Exponential.normalizedExponential s) x = flow s x :=
  additiveFlow.biholomorph_normalizedExponential jointFlow_holomorphic s x

private theorem SpecialPeriods.Threefold.FiniteActionFixed.Period.inverse_vector_real {V B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    (P : HolomorphicPeriodMap V B) (b : B) (s : ℝ) :
    (P.periodEquiv b).symm (SpecialPeriods.Threefold.VerticalAction.Period.vector (s : ℂ)) =
      s • Pi.basisFun ℝ (Fin 4) 3 := by
  apply (P.periodEquiv b).injective
  rw [LinearEquiv.apply_symm_apply, map_smul,
    SpecialPeriods.Threefold.VerticalAction.Period.periodEquiv_delta]
  ext i
  fin_cases i <;> simp [SpecialPeriods.Threefold.VerticalAction.Period.vector]

end Mathoverflow1973

end
