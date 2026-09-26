/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Geometry.GeneralConormalAxis
public import LeanPool.Stafford38.Stafford38.Geometry.GeneralConstantCoordinateAxis
public import LeanPool.Stafford38.Stafford38.Geometry.GeneralCoordinateAvoidance
public import LeanPool.Stafford38.Stafford38.Geometry.CanonicalConstantCoordinateBranch


/-!
# Laurent conormal axes for coordinate-avoiding prime varieties

This combines the constant-coordinate and divisorial cases for an arbitrary
prime affine ideal. The conclusion is a residue-extension Laurent witness;
its comparison with ground-field projective directions is separate.
-/

@[expose] public section

namespace Stafford38.Geometry.GeneralAsymptoticLaurentAxis

open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.GeneralConormalAxis
open Stafford38.Geometry.GeneralConstantCoordinateAxis
open Stafford38.Geometry.GeneralCoordinateAvoidance
open Stafford38.Geometry.CanonicalConstantCoordinateBranch
open Stafford38.Geometry.LaurentConormalResidueExtension
open Stafford38.GeometryRetractionSpecialization

noncomputable section

universe u

theorem exists_groundConormalAxis_of_prime_coordinate_avoidance
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (havoid : ∀ y ∈ MvPolynomial.zeroLocus k P.asIdeal, y ⟨0, hm⟩ ≠ 0) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K)
      (y : Fin m → LaurentSeries K) (xi : Fin m → PowerSeries K),
      Sum.elim y
          (fun i ↦ algebraMap (PowerSeries K) (LaurentSeries K) (xi i)) ∈
        groundEquationConormalLocus (k := k) (K := K) P.asIdeal ∧
      residueColumn xi =
        (fun i : Fin m ↦ if i = ⟨0, hm⟩ then 1 else 0) := by
  by_cases halg : IsAlgebraic k (componentCoordinate P ⟨0, hm⟩)
  · obtain ⟨c, y, hc, hy, _⟩ :=
      exists_constant_coordinate_equation_and_pure_axis hm P halg
    exact exists_residueExtensionConormalAxis_of_ambientCoordinate_constant
      hm P.asIdeal ⟨y, hy⟩ ⟨c, hc⟩
  · apply exists_groundConormalAxis_of_minimalPrime_unit_transcendental
      hm P.asIdeal P.isPrime.isRadical P
    · simp [Ideal.minimalPrimes_eq_subsingleton_self]
    · exact exists_coordinate_inverse_of_avoidance P.asIdeal ⟨0, hm⟩ havoid
    · exact halg


end
end Stafford38.Geometry.GeneralAsymptoticLaurentAxis
