/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-

Concrete normalized-Haar actions and the Zhou fiber-shear equivalence for the
crossed-product model. Paper: §3.
-/
import LeanPool.ConnesRigidity.Paper.Section3.CrossedAction
import LeanPool.ConnesRigidity.Paper.Section3.DualActionConjugacy
import LeanPool.ConnesRigidity.Foundation.OperatorAlgebra.CrossedProductFactorTransport

/-!
The crossed haar component of the Connes rigidity formalization.
-/

namespace Connes
namespace PaperCrossedHaar

open MeasureTheory
open Construction
open Construction.PaperKernel
open PaperDualActions
open PaperDualTopology
open PaperFactorIsomorphism
open PaperDualShearMeasure
open PaperCrossedAction
open CrossedProduct

noncomputable section

/--
The `H` construction used in the Connes rigidity formalization.
-/
abbrev H := Construction.H
/--
The `Coordinates` construction used in the Connes rigidity formalization.
-/
abbrev Coordinates := PaperFactorIsomorphism.DualCoordinates

/- The inverse of each coordinate action is the action of the inverse group
element. Paper: §3. -/
theorem paperCoordinateActionOne_symm (h : H) :
    (paperCoordinateActionOne h).symm = paperCoordinateActionOne h⁻¹ := by
  apply AddEquiv.ext
  intro p
  apply (paperCoordinateActionOne h).injective
  simp

/- The second coordinate action has the same inverse formula. Paper: §3. -/
theorem paperCoordinateActionTwo_symm (h : H) :
    (paperCoordinateActionTwo h).symm = paperCoordinateActionTwo h⁻¹ := by
  apply AddEquiv.ext
  intro p
  apply (paperCoordinateActionTwo h).injective
  simp

/- The first concrete action preserves Zhou's normalized coordinate Haar
measure. Paper: §3. -/
theorem paperCoordinateActionOne_measurePreserving (h : H) :
    MeasurePreserving (paperCoordinateActionOne h : Coordinates → Coordinates)
      coordinatesHaar coordinatesHaar := by
  unfold coordinatesHaar
  exact NormalizedHaar.normalizedAddHaar_preserving_addEquiv
    Coordinates (paperCoordinateActionOne h)
    (continuous_paperCoordinateActionOne h) (by
      rw [paperCoordinateActionOne_symm]
      exact continuous_paperCoordinateActionOne h⁻¹)

/- The second concrete action preserves Zhou's normalized coordinate Haar
measure. Paper: §3. -/
theorem paperCoordinateActionTwo_measurePreserving (h : H) :
    MeasurePreserving (paperCoordinateActionTwo h : Coordinates → Coordinates)
      coordinatesHaar coordinatesHaar := by
  unfold coordinatesHaar
  exact NormalizedHaar.normalizedAddHaar_preserving_addEquiv
    Coordinates (paperCoordinateActionTwo h)
    (continuous_paperCoordinateActionTwo h) (by
      rw [paperCoordinateActionTwo_symm]
      exact continuous_paperCoordinateActionTwo h⁻¹)

/- The first Zhou action packaged as a probability Haar action. Paper: §3.
-/
/--
The `paperHaarActionOne` construction used in the Connes rigidity formalization.
-/
def paperHaarActionOne : HaarProbabilityAction H Coordinates where
  measure := coordinatesHaar
  haar := by
    unfold coordinatesHaar
    infer_instance
  probability := by
    unfold coordinatesHaar
    infer_instance
  action := paperCoordinatePermActionOne
  action_add := by
    intro h z z'
    change paperCoordinateActionOne h (z + z') =
      paperCoordinateActionOne h z + paperCoordinateActionOne h z'
    exact (paperCoordinateActionOne h).map_add z z'
  action_preserves_measure := paperCoordinateActionOne_measurePreserving

/-- The second Zhou action packaged as a probability Haar action. Paper: §3.
-/
def paperHaarActionTwo : HaarProbabilityAction H Coordinates where
  measure := coordinatesHaar
  haar := by
    unfold coordinatesHaar
    infer_instance
  probability := by
    unfold coordinatesHaar
    infer_instance
  action := paperCoordinatePermActionTwo
  action_add := by
    intro h z z'
    change paperCoordinateActionTwo h (z + z') =
      paperCoordinateActionTwo h z + paperCoordinateActionTwo h z'
    exact (paperCoordinateActionTwo h).map_add z z'
  action_preserves_measure := paperCoordinateActionTwo_measurePreserving

/-- The quadratic fiber shear as a homeomorphism. Its inverse is the same
quadratic shear, but it need not preserve the compact-group law. Paper: §3.
-/
def paperFiberShearHomeomorph : Coordinates ≃ₜ Coordinates where
  toEquiv :=
    { toFun := fiberShear
      invFun := fiberShear
      left_inv := fiberShear_involutive
      right_inv := fiberShear_involutive }
  continuous_toFun := continuous_fiberShear
  continuous_invFun := continuous_fiberShear

/-- The measurable equivalence underlying the quadratic fiber shear.
Paper: §3.
-/
def paperFiberShearMeasurableEquiv : Coordinates ≃ᵐ Coordinates :=
  paperFiberShearHomeomorph.toMeasurableEquiv

/-- Zhou's fiber shear as an equivariant measure-preserving homeomorphism of
the two crossed-product bases. Paper: §3.
-/
def paperHaarHomeomorph :
    EquivariantHaarHomeomorph paperHaarActionOne paperHaarActionTwo where
  toHomeomorph := paperFiberShearHomeomorph
  measure_preserving := fiberShear_measurePreserving
  equivariant := by
    intro h p
    -- Expose the actions and the underlying map through their bundled coercions.
    change fiberShear (paperCoordinateActionOne h p) =
      paperCoordinateActionTwo h (fiberShear p)
    exact PaperDualActionConjugacy.paperFiberShear_conjugates_paperActions h p

/-- Zhou's fiber shear is an equivariant Haar equivalence between the two
crossed-product bases. Paper: §3.
-/
def paperHaarEquiv :
    EquivariantHaarEquiv paperHaarActionOne paperHaarActionTwo :=
  paperHaarHomeomorph.toEquivariantHaarEquiv

end
end PaperCrossedHaar
end Connes
