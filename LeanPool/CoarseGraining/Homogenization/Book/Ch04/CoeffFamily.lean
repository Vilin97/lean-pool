/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Law

/-! # Coeff Family -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch04

open MeasureTheory

/-!
# Dependent coefficient-family bridge

The reboot avoids the old totalized coefficient-field bridge.  To build Chapter
2 objects from a Chapter 4 coefficient field, callers provide the actual
`AELocallyUniformlyEllipticField` witness.  This keeps support assumptions
explicit and prevents hidden identity-totalization wrappers from leaking into
Chapter 5.
-/

/-- The Chapter 2 coefficient object on one triadic cube obtained from a
Chapter 4 a.e. ellipticity witness. -/
noncomputable def coeffOnOfAEEllipticOn {d : ℕ} (a : RegCoeffField d)
    (Q : TriadicCube d)
    (hQ : ∃ lam Lam : ℝ,
      0 < lam ∧ lam ≤ Lam ∧
        AEEllipticOn lam Lam (openCubeSet Q) a) :
    Ch02.CoeffOn (Ch02.cubeDomain Q) :=
  let lam := Classical.choose hQ
  let hLam := Classical.choose_spec hQ
  let Lam := Classical.choose hLam
  let hData := Classical.choose_spec hLam
  { toCoeffField := a.toFun
    lam := lam
    Lam := Lam
    lam_pos := hData.1
    lam_le_Lam := hData.2.1
    aeStronglyMeasurable := by
      intro i j
      have hEll :
          IsAEEllipticFieldOn lam Lam (openCubeSet Q) a.toFun := hData.2.2
      simpa [Ch02.cubeDomain_coe] using
        IsAEEllipticFieldOn.aestronglyMeasurable_restrictCoeffField_apply hEll i j
    aeElliptic := by
      have hEll :
          IsAEEllipticFieldOn lam Lam (openCubeSet Q) a.toFun := hData.2.2
      simpa [Ch02.cubeDomain_coe] using
        IsAEEllipticFieldOn.ae_isEllipticMatrix hEll }

@[simp] theorem coeffOnOfAEEllipticOn_toCoeffField {d : ℕ}
    (a : RegCoeffField d) (Q : TriadicCube d)
    (hQ : ∃ lam Lam : ℝ,
      0 < lam ∧ lam ≤ Lam ∧
        AEEllipticOn lam Lam (openCubeSet Q) a) :
    (coeffOnOfAEEllipticOn a Q hQ).toCoeffField = a.toFun :=
  rfl

/-- The Chapter 2 triadic coefficient family associated to a Chapter 4
a.e.-locally elliptic coefficient field. -/
noncomputable def triadicCoeffFamilyOfAELocallyUniformlyEllipticField {d : ℕ}
    (a : RegCoeffField d) (h : AELocallyUniformlyEllipticField a) :
    Ch02.TriadicCoeffFamily d where
  coeffOn := fun Q => coeffOnOfAEEllipticOn a Q (h Q)
  restrictsTo_of_subset := by
    intro Q R _hsub
    change a.toFun =ᵐ[volumeMeasureOn (Ch02.cubeDomain R : Set (Vec d))] a.toFun
    exact Filter.EventuallyEq.rfl

@[simp]
theorem triadicCoeffFamilyOfAELocallyUniformlyEllipticField_coeffOn_toCoeffField
    {d : ℕ} (a : RegCoeffField d) (h : AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) :
    ((triadicCoeffFamilyOfAELocallyUniformlyEllipticField a h).coeffOn Q).toCoeffField =
      a.toFun :=
  rfl

/-- Changing only ellipticity witnesses does not change the associated triadic
family modulo Chapter 2 a.e. equality. -/
theorem triadicCoeffFamilyOfAELocallyUniformlyEllipticField_aeeq {d : ℕ}
    {a : RegCoeffField d} (h₁ h₂ : AELocallyUniformlyEllipticField a) :
    Ch02.TriadicCoeffFamily.AEEq
      (triadicCoeffFamilyOfAELocallyUniformlyEllipticField a h₁)
      (triadicCoeffFamilyOfAELocallyUniformlyEllipticField a h₂) := by
  intro Q
  change a.toFun =ᵐ[volumeMeasureOn (Ch02.cubeDomain Q : Set (Vec d))] a.toFun
  exact Filter.EventuallyEq.rfl

/-- If two fields agree a.e. on every triadic cube, their dependent Chapter 2
triadic coefficient families agree a.e. on every cube. -/
theorem triadicCoeffFamilyOfAELocallyUniformlyEllipticField_aeeq_of_forall_ae_eq
    {d : ℕ} {a b : RegCoeffField d}
    (ha : AELocallyUniformlyEllipticField a)
    (hb : AELocallyUniformlyEllipticField b)
    (hab : ∀ Q : TriadicCube d,
      a.toFun =ᵐ[volumeMeasureOn (openCubeSet Q)] b.toFun) :
    Ch02.TriadicCoeffFamily.AEEq
      (triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
      (triadicCoeffFamilyOfAELocallyUniformlyEllipticField b hb) := by
  intro Q
  change a.toFun =ᵐ[volumeMeasureOn (Ch02.cubeDomain Q : Set (Vec d))] b.toFun
  simpa [Ch02.cubeDomain_coe] using hab Q

/-- A one-cube a.e. equality of ambient fields gives a.e. equality of the
corresponding Chapter 2 coefficient objects on that cube. -/
theorem coeffOnOfAELocallyUniformlyEllipticField_aeeq_of_ae_eq_on_openCubeSet
    {d : ℕ} {a b : RegCoeffField d}
    (ha : AELocallyUniformlyEllipticField a)
    (hb : AELocallyUniformlyEllipticField b)
    (Q : TriadicCube d)
    (hab : a.toFun =ᵐ[volumeMeasureOn (openCubeSet Q)] b.toFun) :
    Ch02.CoeffOn.AEEq
      ((triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
      ((triadicCoeffFamilyOfAELocallyUniformlyEllipticField b hb).coeffOn Q) := by
  change a.toFun =ᵐ[volumeMeasureOn (Ch02.cubeDomain Q : Set (Vec d))] b.toFun
  simpa [Ch02.cubeDomain_coe] using hab

namespace RestrictionLawCarrier

/-- A Chapter 4 law carrier supplies, almost surely, the dependent Chapter 2
triadic coefficient family associated to the sampled coefficient field. -/
theorem ae_coeffFamily_exists {d : ℕ} {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P) :
    ∀ᵐ a ∂P,
      ∃ h : AELocallyUniformlyEllipticField a,
        ∃ F : Ch02.TriadicCoeffFamily d,
          F = triadicCoeffFamilyOfAELocallyUniformlyEllipticField a h := by
  filter_upwards [hP.ae_locally_uniformly_elliptic] with a ha
  exact ⟨ha, triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha, rfl⟩

end RestrictionLawCarrier

end Ch04
end Book
end Homogenization
