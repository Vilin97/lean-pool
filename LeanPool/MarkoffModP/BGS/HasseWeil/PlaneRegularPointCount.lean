/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.AffinePointPlace
public import LeanPool.MarkoffModP.BGS.HasseWeil.PlaneSingularPointBound
public import Mathlib.Tactic

/-!
# Regular affine points in the second-coordinate direction

The Stepanov argument is applied only at affine points where the second
partial derivative is nonzero.  At those points the affine local ring agrees
with the normalization local ring, so the selected normalization place has
residue degree one.  The complementary critical points are kept explicit and
are bounded by `affineSecondCoordinateCriticalPoints_card_le`.

This file contains only the finite-set bookkeeping.  The local normalization
statement and the Stepanov zero count are proved in separate modules.
-/

@[expose] public section

namespace BGS.HasseWeil

open BGS.CorvajaZannier

noncomputable section

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- Affine points where differentiation in the second coordinate is regular. -/
abbrev AffineSecondCoordinateRegularPoint
    (f : MvPolynomial (Fin 2) K) :=
  {z : AffinePlaneCurvePoint f //
    MvPolynomial.eval ![z.1.1, z.1.2] (MvPolynomial.pderiv 1 f) ≠ 0}

/-- The complement of the regular-point subtype is the finite critical locus. -/
def affineSecondCoordinateNonregularEquivCritical
    (f : MvPolynomial (Fin 2) K) :
    {z : AffinePlaneCurvePoint f //
        ¬ MvPolynomial.eval ![z.1.1, z.1.2]
          (MvPolynomial.pderiv 1 f) ≠ 0} ≃
      {z : K × K // z ∈ affineSecondCoordinateCriticalPoints K f} where
  toFun z := ⟨z.1.1, by
    rw [mem_affineSecondCoordinateCriticalPoints_iff]
    exact ⟨z.1.2, not_ne_iff.mp z.2⟩⟩
  invFun z := ⟨⟨z.1, (mem_affineSecondCoordinateCriticalPoints_iff.mp z.2).1⟩,
    not_ne_iff.mpr
      (mem_affineSecondCoordinateCriticalPoints_iff.mp z.2).2⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv z := by
    apply Subtype.ext
    rfl

/-- Every affine point is either regular in the second-coordinate direction
or belongs to the explicitly defined critical locus. -/
theorem affinePlaneCurvePoint_card_eq_regular_add_critical
    (f : MvPolynomial (Fin 2) K) :
    Fintype.card (AffinePlaneCurvePoint f) =
      Fintype.card (AffineSecondCoordinateRegularPoint f) +
        (affineSecondCoordinateCriticalPoints K f).card := by
  classical
  let regular : AffinePlaneCurvePoint f → Prop := fun z =>
    MvPolynomial.eval ![z.1.1, z.1.2]
      (MvPolynomial.pderiv 1 f) ≠ 0
  have hcompl :
      Fintype.card {z : AffinePlaneCurvePoint f // ¬ regular z} =
        (affineSecondCoordinateCriticalPoints K f).card := by
    calc
      Fintype.card {z : AffinePlaneCurvePoint f // ¬ regular z} =
          Fintype.card
            {z : K × K // z ∈ affineSecondCoordinateCriticalPoints K f} :=
        Fintype.card_congr
          (affineSecondCoordinateNonregularEquivCritical f)
      _ = (affineSecondCoordinateCriticalPoints K f).card := by
        exact Fintype.card_coe _
  have hregularLe :
      Fintype.card {z : AffinePlaneCurvePoint f // regular z} ≤
        Fintype.card (AffinePlaneCurvePoint f) :=
    Fintype.card_subtype_le regular
  have hpartition := Fintype.card_subtype_compl regular
  change Fintype.card (AffinePlaneCurvePoint f) =
    Fintype.card {z : AffinePlaneCurvePoint f // regular z} +
      (affineSecondCoordinateCriticalPoints K f).card
  rw [← hcompl, hpartition]
  omega

/-- Removing one chosen regular point lowers the regular-point cardinality by
exactly one.  This is the form needed when that point supplies the unique
allowed pole of the Stepanov auxiliary. -/
theorem regularPoint_card_eq_punctured_add_one
    {f : MvPolynomial (Fin 2) K}
    (z₀ : AffineSecondCoordinateRegularPoint f) :
    Fintype.card (AffineSecondCoordinateRegularPoint f) =
      Fintype.card {z : AffineSecondCoordinateRegularPoint f // z ≠ z₀} + 1 := by
  classical
  have h := Fintype.card_subtype_compl
    (fun z : AffineSecondCoordinateRegularPoint f => z = z₀)
  have hpositive : 0 < Fintype.card (AffineSecondCoordinateRegularPoint f) :=
    Fintype.card_pos_iff.mpr ⟨z₀⟩
  have hpunctured :
      Fintype.card {z : AffineSecondCoordinateRegularPoint f // z ≠ z₀} =
        Fintype.card (AffineSecondCoordinateRegularPoint f) - 1 := by
    simpa only [Fintype.card_subtype_eq] using h
  rw [hpunctured]
  omega

end

end BGS.HasseWeil
