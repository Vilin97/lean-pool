/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Geometry.ComponentProjectiveClosureNormalization

/-!
# Finite retained component equations

A finite generating family of an affine ideal contained in a prime component
is homogenized over the ground field and then transported through the explicit
retained Laurent coefficient map.  The resulting homogeneous equations vanish
on every retained common-scale completion, and their zeroth-chart
dehomogenizations generate exactly the scalar-extended affine ideal.

No ambient algebra structure on the residue field is used, and no tangent data
are constructed here.
-/

namespace Stafford38.Geometry.RetainedComponentEquationPackage

open IsLocalRing
open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ComponentProjectiveClosureNormalization
open Stafford38.Geometry.LocalizedProjectiveChartTransition
open Stafford38.Geometry.ProjectiveEquationFormalChart
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.RelativeRetainedBoundaryPlace
open Stafford38.Geometry.RetainedProjectiveCompletion

noncomputable section

universe u

variable {k : Type u} [Field k] {m : ℕ}

/-- Mapping coefficients commutes with zeroth-chart dehomogenization. -/
theorem projectiveDehomogenize_map
    {S : Type u} [Field S] (coeff : k →+* S)
    (H : MvPolynomial (Fin (m + 1)) k) :
    projectiveDehomogenize (n := m)
        (MvPolynomial.map coeff H) =
      MvPolynomial.map coeff (projectiveDehomogenize H) := by
  change MvPolynomial.bind₁ (Fin.cases 1 fun j ↦ MvPolynomial.X j)
      (MvPolynomial.map coeff H) =
    MvPolynomial.map coeff
      (MvPolynomial.bind₁ (Fin.cases 1 fun j ↦ MvPolynomial.X j) H)
  rw [MvPolynomial.map_bind₁]
  apply congrArg (fun g ↦
    MvPolynomial.bind₁ g (MvPolynomial.map coeff H))
  funext a
  refine Fin.cases ?_ (fun j ↦ ?_) a <;> simp

/-- Mapping coefficients therefore commutes with dehomogenizing the standard
ground-field homogenization. -/
theorem projectiveDehomogenize_map_homogenizeAtZero
    {S : Type u} [Field S] (coeff : k →+* S)
    (f : MvPolynomial (Fin m) k) :
    projectiveDehomogenize (n := m)
        (MvPolynomial.map coeff (homogenizeAtZero f)) =
      MvPolynomial.map coeff f := by
  rw [projectiveDehomogenize_map,
    projectiveDehomogenize_homogenizeAtZero]

/-- The mapped homogenizations of a finite family dehomogenize to precisely
the mapped ideal spanned by that family. -/
theorem dehomogenizedEquationIdeal_mapped_homogenizations
    {S : Type u} [Field S] (coeff : k →+* S) {r : ℕ}
    (generators : Fin r → MvPolynomial (Fin m) k) :
    dehomogenizedEquationIdeal
        (fun j ↦ MvPolynomial.map coeff
          (homogenizeAtZero (generators j))) =
      (Ideal.span (Set.range generators)).map (MvPolynomial.map coeff) := by
  rw [dehomogenizedEquationIdeal]
  simp_rw [projectiveDehomogenize_map_homogenizeAtZero coeff]
  rw [Ideal.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨generators j, ⟨j, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
    exact ⟨j, rfl⟩

/-- A finite homogeneous equation package over a displayed coefficient map.
Its last field records exact generation, not merely containment. -/
structure EquationPackage
    {S : Type u} [Field S]
    (I : Ideal (MvPolynomial (Fin m) k)) (coeff : k →+* S)
    (q : Fin (m + 1) → S) where
  /-- The size of the finite homogeneous equation family. -/
  equationCount : ℕ
  /-- Homogeneous equations vanishing at the point and generating the extended affine ideal
  after dehomogenization. -/
  equations : Fin equationCount → MvPolynomial (Fin (m + 1)) S
  /-- The homogeneous degree assigned to each retained component equation. -/
  degree : Fin equationCount → ℕ
  homogeneous : ∀ j, (equations j).IsHomogeneous (degree j)
  equations_vanish : ∀ j, MvPolynomial.eval q (equations j) = 0
  dehomogenizedEquationIdeal_eq :
    dehomogenizedEquationIdeal equations =
      I.map (MvPolynomial.map coeff)

private theorem equationPackage_of_vanishing {S : Type u} [Field S]
    (I : Ideal (MvPolynomial (Fin m) k)) (coeff : k →+* S) (q : Fin (m + 1) → S)
    (hvanish : ∀ f ∈ I, MvPolynomial.eval q
      (MvPolynomial.map coeff (homogenizeAtZero f)) = 0) :
    Nonempty (EquationPackage I coeff q) := by
  obtain ⟨r, generators, hgenerators⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp
      (IsNoetherian.noetherian (I : Submodule _ _))
  have hgenerator_mem : ∀ j, generators j ∈ I := by
    intro j
    rw [← hgenerators]
    exact Submodule.subset_span (Set.mem_range_self j)
  refine ⟨{
    equationCount := r
    equations := fun j ↦ MvPolynomial.map coeff (homogenizeAtZero (generators j))
    degree := fun j ↦ (generators j).totalDegree
    homogeneous := fun j ↦ (homogenizeAtZero_isHomogeneous (generators j)).map coeff
    equations_vanish := fun j ↦ hvanish (generators j) (hgenerator_mem j)
    dehomogenizedEquationIdeal_eq := ?_ }⟩
  rw [dehomogenizedEquationIdeal_mapped_homogenizations]
  change Ideal.map (MvPolynomial.map coeff)
      (Submodule.span _ (Set.range generators)) = I.map (MvPolynomial.map coeff)
  rw [hgenerators]

/-- Exact finite equation package obtained from ground-field generators of
`I`.  The coefficient map in both the equations and the ideal equality is the
displayed retained Laurent coefficient map. -/
theorem retainedComponentEquationPackage
    [CharZero k]
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (I : Ideal (MvPolynomial (Fin m) k)) (hIP : I ≤ P.asIdeal)
    (i : Fin m)
    (W : Data k (ComponentFractionField P) (componentCoordinate P i)) :
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
        (ComponentFractionField P) := W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : IsDiscreteValuationRing V := W.place.isDiscrete
    letI : Algebra W.coefficientField V :=
      (relativeCoefficientMap W.coefficientField W.place).toAlgebra
    ∀ (q : Fin (m + 1) → V) (scale : ComponentFractionField P),
      (∀ a, (q a : ComponentFractionField P) =
        scale * componentProjectivePoint P a) →
      Nonempty (EquationPackage (S := LaurentSeries (ResidueField V)) I
        (retainedLaurentCoefficientMap P i W)
        (fun a ↦ algebraMap (PowerSeries (ResidueField V))
          (LaurentSeries (ResidueField V))
            (retainedToCompletedPowerSeries W (q a)))) := by
  let : Algebra (CoordinateZeroLocalRing W.coefficientField)
      (ComponentFractionField P) := W.ambientAlgebra
  let V := W.place.valuation.toSubring
  let : IsDiscreteValuationRing V := W.place.isDiscrete
  let : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  dsimp only
  intro q scale hq
  let coeff : k →+* LaurentSeries (ResidueField V) := retainedLaurentCoefficientMap P i W
  let point : Fin (m + 1) → LaurentSeries (ResidueField V) := fun a ↦
    algebraMap (PowerSeries (ResidueField V)) (LaurentSeries (ResidueField V))
      (retainedToCompletedPowerSeries W (q a))
  have hvanish : ∀ f ∈ I,
      MvPolynomial.eval point (MvPolynomial.map coeff (homogenizeAtZero f)) = 0 := by
    intro f hf
    rw [MvPolynomial.eval_map]
    have h := retainedLaurent_eval₂_eq_zero_of_commonScale P i W
      (homogenizeAtZero_isHomogeneous f)
      (homogenizeAtZero_mem_componentProjectiveClosureIdeal P (hIP hf)) q scale hq
    exact h
  have package := equationPackage_of_vanishing I coeff point hvanish
  exact package


end

end Stafford38.Geometry.RetainedComponentEquationPackage
