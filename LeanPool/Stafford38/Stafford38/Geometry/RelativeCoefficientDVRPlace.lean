/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Geometry.RetainedDVRPlace
import Mathlib.FieldTheory.Separable

/-!
# Relative coefficients in a retained DVR place

For the source DVR `E[X]_(X)`, the retained local factor contains the
coefficient field `E`.  This file constructs that coefficient map, checks its
compatibility with the ambient-field embedding, and proves that the resulting
residue extension is finite and separable in characteristic zero.

No inverse limit, completion, or power-series chart is constructed here.
-/

namespace Stafford38.Geometry.RelativeCoefficientDVR

open IsLocalRing
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.RetainedDVR

noncomputable section


universe u v

private abbrev SourceDVR (E : Type u) [Field E] :=
  CoordinateZeroLocalRing E

/-- Evaluation at zero on the source coordinate DVR. -/
def coordinateConstantTerm
    (E : Type u) [Field E] : SourceDVR E →+* E :=
  IsLocalization.lift (S := SourceDVR E)
    (M := (coordinateZeroPrime E).primeCompl)
    (g := Polynomial.evalRingHom (0 : E)) fun y ↦ by
      rw [isUnit_iff_ne_zero]
      intro hy
      apply y.2
      have hker :
          RingHom.ker (Polynomial.evalRingHom (0 : E)) =
            coordinateZeroPrime E := by
        rw [Polynomial.ker_evalRingHom, coordinateZeroPrime]
        have hCzero : Polynomial.C (0 : E) = 0 :=
          map_zero Polynomial.C
        rw [hCzero, sub_zero]
      exact hker.le (RingHom.mem_ker.mpr hy)

/-- Evaluation at zero is onto because constant polynomials survive the
localization. -/
theorem coordinateConstantTerm_surjective
    (E : Type u) [Field E] :
    Function.Surjective (coordinateConstantTerm E) := by
  intro e
  refine ⟨algebraMap (Polynomial E) (SourceDVR E) (Polynomial.C e), ?_⟩
  rw [coordinateConstantTerm, IsLocalization.lift_eq]
  exact Polynomial.eval_C

/-- The residue field of `E[X]_(X)` is canonically `E`. -/
noncomputable def coordinateResidueEquiv
    (E : Type u) [Field E] :
    ResidueField (SourceDVR E) ≃+* E := by
  let f := coordinateConstantTerm E
  letI : IsLocalHom f := (coordinateConstantTerm_surjective E).isLocalHom
  let g : ResidueField (SourceDVR E) →+* E := ResidueField.lift f
  apply RingEquiv.ofBijective g
  refine ⟨g.injective, ?_⟩
  intro e
  obtain ⟨a, rfl⟩ := coordinateConstantTerm_surjective E e
  exact ⟨residue (SourceDVR E) a, ResidueField.lift_residue_apply f a⟩

@[simp]
theorem coordinateResidueEquiv_algebraMap
    (E : Type u) [Field E] (e : E) :
    coordinateResidueEquiv E
        (algebraMap E (ResidueField (SourceDVR E)) e) = e := by
  letI : IsLocalHom (coordinateConstantTerm E) :=
    (coordinateConstantTerm_surjective E).isLocalHom
  change ResidueField.lift (coordinateConstantTerm E)
      (residue (SourceDVR E)
        (algebraMap E (SourceDVR E) e)) = e
  rw [ResidueField.lift_residue_apply]
  change coordinateConstantTerm E
      (algebraMap (Polynomial E) (SourceDVR E) (Polynomial.C e)) = e
  rw [coordinateConstantTerm, IsLocalization.lift_eq]
  exact Polynomial.eval_C

/-- The retained local factor restricted to constant coefficients. -/
def relativeCoefficientMap
    (E : Type u) [Field E]
    {L : Type v} [Field L] [Algebra (SourceDVR E) L]
    {a : SourceDVR E}
    (D : RetainedDVRPlace (SourceDVR E) (L := L) a) :
    E →+* D.valuation.toSubring :=
  D.factor.comp (algebraMap E (SourceDVR E))

/-- The coefficient map retained in the valuation subring is the original
ambient embedding of `E`. -/
theorem relativeCoefficientMap_commutes
    (E : Type u) [Field E]
    {L : Type v} [Field L] [Algebra E L]
    [Algebra (SourceDVR E) L] [IsScalarTower E (SourceDVR E) L]
    {a : SourceDVR E}
    (D : RetainedDVRPlace (SourceDVR E) (L := L) a) :
    D.valuation.toSubring.subtype.comp (relativeCoefficientMap E D) =
      algebraMap E L := by
  ext e
  change (D.factor (algebraMap E (SourceDVR E) e) : L) =
    algebraMap E L e
  calc
    (D.factor (algebraMap E (SourceDVR E) e) : L) =
        algebraMap (SourceDVR E) L
          (algebraMap E (SourceDVR E) e) :=
      DFunLike.congr_fun D.factor_commutes
        (algebraMap E (SourceDVR E) e)
    _ = algebraMap E L e :=
      (IsScalarTower.algebraMap_apply E (SourceDVR E) L e).symm

/-- The finite residue extension retained from the source DVR remains finite
over its coefficient field. -/
theorem relativeResidue_finite
    (E : Type u) [Field E]
    {L : Type v} [Field L] [Algebra (SourceDVR E) L]
    {a : SourceDVR E}
    (D : RetainedDVRPlace (SourceDVR E) (L := L) a) :
    letI : IsDiscreteValuationRing D.valuation.toSubring := D.isDiscrete
    letI : Algebra E D.valuation.toSubring :=
      (relativeCoefficientMap E D).toAlgebra
    Module.Finite E (ResidueField D.valuation.toSubring) := by
  let A := SourceDVR E
  let V := D.valuation.toSubring
  letI : IsDiscreteValuationRing V := D.isDiscrete
  letI : Algebra A V := D.factor.toAlgebra
  letI : IsLocalHom (algebraMap A V) := D.factor_isLocal
  letI : Algebra E V := (relativeCoefficientMap E D).toAlgebra
  letI : IsScalarTower E A V :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hsourceSurjective :
      Function.Surjective (algebraMap E (ResidueField A)) := by
    intro z
    refine ⟨coordinateResidueEquiv E z, ?_⟩
    apply (coordinateResidueEquiv E).injective
    exact coordinateResidueEquiv_algebraMap E
      (coordinateResidueEquiv E z)
  have hsourceFinite : Module.Finite E (ResidueField A) :=
    Module.Finite.of_surjective
      (Algebra.linearMap E (ResidueField A)) hsourceSurjective
  letI : Module.Finite E (ResidueField A) := hsourceFinite
  have htargetFinite :
      Module.Finite (ResidueField A) (ResidueField V) := by
    exact D.residue_finite
  letI : Module.Finite (ResidueField A) (ResidueField V) := htargetFinite
  letI : IsScalarTower E (ResidueField A) (ResidueField V) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact Module.Finite.trans (ResidueField A) (ResidueField V)

/-- In characteristic zero, the finite residue extension induced by the
retained coefficient map is separable. -/
theorem relativeResidue_isSeparable
    (E : Type u) [Field E] [CharZero E]
    {L : Type v} [Field L] [Algebra (SourceDVR E) L]
    {a : SourceDVR E}
    (D : RetainedDVRPlace (SourceDVR E) (L := L) a) :
    letI : IsDiscreteValuationRing D.valuation.toSubring := D.isDiscrete
    letI : Algebra E D.valuation.toSubring :=
      (relativeCoefficientMap E D).toAlgebra
    Algebra.IsSeparable E (ResidueField D.valuation.toSubring) := by
  letI : IsDiscreteValuationRing D.valuation.toSubring := D.isDiscrete
  letI : Algebra E D.valuation.toSubring :=
    (relativeCoefficientMap E D).toAlgebra
  letI : Module.Finite E (ResidueField D.valuation.toSubring) :=
    relativeResidue_finite E D
  letI : Algebra.IsIntegral E (ResidueField D.valuation.toSubring) :=
    ⟨fun y ↦ (IsAlgebraic.of_finite E y).isIntegral⟩
  exact Algebra.IsSeparable.of_integral E
    (ResidueField D.valuation.toSubring)


end

end Stafford38.Geometry.RelativeCoefficientDVR
