/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Geometry.GeneralAsymptoticLaurentAxis
import LeanPool.Stafford38.Stafford38.Geometry.SmoothConormalFibreVanishing
import LeanPool.Stafford38.Stafford38.Geometry.ConormalScalarExtensionVanishing

/-!
# Asymptotic conormal directions of coordinate-avoiding varieties

The boundary witness specializes only in the fibre coordinates. Its base
coordinates may have poles. Smooth-locus density and scalar-extension
vanishing relate that witness to the ground-field projective direction set.
-/

namespace Stafford38.Geometry.GeneralAsymptoticConormal

open Stafford38.Geometry.GeneralAsymptoticLaurentAxis
open Stafford38.Geometry.SmoothConormalFibreVanishing
open Stafford38.Geometry.ProjectiveConormalDirections
open Stafford38.Geometry.ConormalScalarExtensionVanishing
open Stafford38.Geometry.LaurentConormalDirection
open Stafford38.Geometry.LaurentConormalResidueExtension
open Stafford38.Geometry.ScalarExtensionPoints
open Stafford38.GeometryRetractionSpecialization

noncomputable section

universe u

theorem coordinate_axis_mem_smooth_fibre_closure
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (I : PrimeSpectrum (MvPolynomial (Fin m) k))
    (havoid : ∀ y ∈ MvPolynomial.zeroLocus k I.asIdeal, y ⟨0, hm⟩ ≠ 0) :
    (fun i : Fin m => if i = ⟨0, hm⟩ then (1 : k) else 0) ∈
      MvPolynomial.zeroLocus k
        (MvPolynomial.vanishingIdeal k (smoothConormalFibreProjection I.asIdeal)) := by
  obtain ⟨K, hK, hAlg, y, xi, hgeneric, hres⟩ :=
    exists_groundConormalAxis_of_prime_coordinate_avoidance hm I havoid
  let := hK
  let := hAlg
  intro P hP
  have hfull := fibreLift_mem_vanishingIdeal_equationConormal I.asIdeal I.isPrime P hP
  have hvan : ∀ q ∈ groundEquationConormalLocus (k := k) (K := K) I.asIdeal,
      MvPolynomial.eval₂ (groundLaurentMap (k := k) (K := K)) q (fibreLift P) = 0 := by
    let : Algebra k (LaurentSeries K) :=
      (groundLaurentMap (k := k) (K := K)).toAlgebra
    intro q hq
    exact scalarExtension_vanishing I.asIdeal (fibreLift P) hfull q hq
  have hpoly := residueFibreLift_mem_extensionValuedVanishingIdeal_of_ground_vanishing
    I.asIdeal P hvan
  have hclosure := residue_mem_residueExtensionFibreClosure_of_laurent_generic
    (K := K) (groundEquationConormalLocus (k := k) (K := K) I.asIdeal) y xi hgeneric
  have hzero := hclosure _ hpoly
  have hzero' : MvPolynomial.eval₂ (algebraMap k K) (residueColumn xi) P = 0 := by
    simpa [residuePolynomialMap] using hzero
  rw [hres] at hzero'
  apply (FaithfulSMul.algebraMap_injective k K)
  rw [map_zero]
  change (algebraMap k K) (MvPolynomial.eval
    (fun i : Fin m => if i = ⟨0, hm⟩ then (1 : k) else 0) P) = 0
  rw [MvPolynomial.eval₂_comp]
  simpa [Function.comp_def] using hzero'

theorem coordinate_axis_mem_projective_conormal_directions
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (I : PrimeSpectrum (MvPolynomial (Fin m) k))
    (havoid : ∀ y ∈ MvPolynomial.zeroLocus k I.asIdeal, y ⟨0, hm⟩ ≠ 0) :
    Projectivization.mk k
        (fun i : Fin m => if i = ⟨0, hm⟩ then (1 : k) else 0)
        (by intro h; have := congrFun h ⟨0, hm⟩; simp at this) ∈
      projectiveHomogeneousClosure
        (projectivizedDirectionSet (smoothConormalDirectionSet I.asIdeal)) := by
  exact mk_mem_projectiveHomogeneousClosure_of_fibre_zeroLocus I.asIdeal _ _
    (coordinate_axis_mem_smooth_fibre_closure hm I havoid)


end
end Stafford38.Geometry.GeneralAsymptoticConormal
