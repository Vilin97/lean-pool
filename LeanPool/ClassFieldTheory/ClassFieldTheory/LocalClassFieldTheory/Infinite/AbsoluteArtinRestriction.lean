/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Infinite.ProfiniteLocalReciprocity
/-!
# Actual finite values of the absolute local Artin map

Projecting the absolute Artin map to a finite abelian subextension recovers
its canonical finite Artin map, not merely the same norm kernel.
-/

@[expose] public section

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open LocalClassFieldTheory

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem absoluteAbelianRestriction_finiteProjection
    (N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K))
    (x : localAbsoluteAbelianProfinite K) :
    absoluteAbelianRestriction K (absoluteFiniteQuotientField K N) x =
      absoluteFiniteQuotientEquiv K N (QuotientGroup.mk x) := by
  refine QuotientGroup.induction_on x fun sigma ↦ ?_
  rw [absoluteAbelianRestriction_mk, absoluteFiniteQuotientEquiv_mk_mk]

private theorem separableAbsoluteLocalArtinMap_finiteQuotientRestriction
    (N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K)) (a : Kˣ) :
    absoluteAbelianRestriction K (absoluteFiniteQuotientField K N)
        (separableAbsoluteLocalArtinMap K a) =
      abelianLocalArtinMap K (absoluteFiniteQuotientField K N) a := by
  rw [absoluteAbelianRestriction_finiteProjection]
  change absoluteFiniteQuotientEquiv K N
    (QuotientGroup.mk' N.toSubgroup (separableAbsoluteLocalArtinMap K a)) = _
  rw [separableAbsoluteLocalArtinMap_finiteProjection]
  exact (absoluteFiniteQuotientEquiv K N).apply_symm_apply _

/-- The actual absolute Artin value restricts to the actual finite abelian
local Artin value. -/
theorem separableAbsoluteLocalArtinMap_restriction
    (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [IsAbelianGalois K E] (a : Kˣ) :
    absoluteAbelianRestriction K E (separableAbsoluteLocalArtinMap K a) =
      abelianLocalArtinMap K E a := by
  generalize hN : absoluteAbelianRestrictionKernel K E = N
  have hfield : absoluteFiniteQuotientField K N = E := by
    rw [← hN, absoluteFiniteQuotientField_restrictionKernel]
  subst E
  exact separableAbsoluteLocalArtinMap_finiteQuotientRestriction K N a

/-- The same finite-value comparison for the usual algebraic-closure
absolute Artin map. -/
theorem absoluteLocalArtinMap_restriction
    (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [IsAbelianGalois K E] (a : Kˣ) :
    absoluteAbelianRestriction K E
        ((separableToStandardAbsoluteAbelianizationEquiv K).symm
          (absoluteLocalArtinMap K a)) =
      abelianLocalArtinMap K E a := by
  rw [separableToStandardAbsoluteAbelianizationEquiv_symm_artinMap]
  exact separableAbsoluteLocalArtinMap_restriction K E a

end ClassFieldTower.Martinet.Shafarevich
