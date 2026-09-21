/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Geometry.CanonicalAsymptoticLaurentProducer

/-!
# A finite-gradient boundary producer

The completed-boundary consumer does not need a comparison of the entire
Zariski tangent space with a chosen matrix of tangent columns.  It needs only
one conormal covector.  This file replaces that global comparison by an
explicit finite expression of the required covector as a linear combination
of differentials of equations in the scalar-extended affine ideal.

This is the algebraic certificate naturally supplied at a smooth generic
point by a Jacobian/conormal calculation.  It is strictly local to the one
annihilating row and is independently checkable coordinate by coordinate.
No normalization, projective closure, boundary divisor, or existence of such
a certificate is asserted here.
-/

namespace Stafford38.Geometry.FiniteGradientBoundaryProducer

open Stafford38
open Stafford38.CanonicalSupportVanishingReduction
open Stafford38.Characteristic
open Stafford38.Characteristic.ReducedSupportIdeal
open Stafford38.CharacteristicInitialIdeal
open Stafford38.Geometry.AffineConormalClosure
open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.CanonicalAsymptoticLaurentProducer
open Stafford38.Geometry.CoisotropicTranslation
open Stafford38.Geometry.FormalDivisorLaurentConormal
open Stafford38.Geometry.ProjectiveConormalDehomogenization
open Stafford38.Geometry.ScalarExtensionPoints
open Stafford38.Geometry.PointwiseConormalContainment
open Stafford38.GeometryRetractionSpecialization
open Stafford38.WeylEulerResidue
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylPBWMonicBridge

noncomputable section

universe u

variable {K : Type u} [Field K]

/-! ## The finite-gradient bridge -/

/-- A coordinate covector is conormal when its coordinates are an explicit
finite linear combination of gradients of equations in the ideal.  This
avoids any equality or inclusion assertion about the whole tangent space. -/
theorem coordinateCovector_mem_affineConormalSpace_of_finite_gradient
    {m r : ℕ}
    (I : Ideal (MvPolynomial (Fin m) K))
    (y xi : Fin m → K)
    (equations : Fin r → I)
    (coefficients : Fin r → K)
    (hgradient : ∀ i,
      xi i = ∑ j, coefficients j * differentialAt y (equations j).1 i) :
    coordinateCovector xi ∈ affineConormalSpace y I := by
  classical
  rw [affineConormalSpace_eq_equationCovectorSpan]
  let g := baseLinearCombination coefficients (fun j ↦ (equations j).1)
  have hg : g ∈ I := by
    dsimp only [g, baseLinearCombination]
    apply Ideal.sum_mem
    intro j hj
    exact I.mul_mem_left (MvPolynomial.C (coefficients j)) (equations j).2
  let gI : I := ⟨g, hg⟩
  have hxi : xi = fun i ↦ differentialAt y g i := by
    funext i
    rw [hgradient, differentialAt_baseLinearCombination]
  have heq : coordinateCovector xi = differentialCovector y g := by
    apply LinearMap.ext
    intro v
    simp only [coordinateCovector_apply, differentialCovector_apply, hxi]
  rw [heq]
  apply Submodule.subset_span
  refine ⟨gI, ?_⟩
  rfl

/-! ## Corrected local boundary interface -/

/-- A completed projective arc together with the one finite Jacobian
certificate actually consumed downstream.

The base coordinates are represented by a projective power-series column;
after dehomogenization they may be Laurent series.  The tail of `ell` is the
regular fibre covector.  `gradient_identity` certifies conormality directly
using equations of the scalar-extended target ideal.  The projective Euler
relation is retained as a check that `ell` is genuinely a projective
annihilating row, although the affine conormal adapter needs only its tail.
-/
structure FiniteGradientBoundaryCertificate
    (k : Type u) [Field k]
    (m : ℕ) (hm : 0 < m)
    (I : Ideal (MvPolynomial (Fin m) k)) where
  equationCount : ℕ
  q : Fin (m + 1) → PowerSeries k
  ell : Fin (m + 1) → PowerSeries k
  q_origin_ne : q 0 ≠ 0
  projective_annihilation :
    ∑ i, laurentColumn ell i * laurentColumn q i = 0
  base_vanish :
    ∀ f ∈ I.map
        (scalarPolynomialMap (k := k) (K := LaurentSeries k) (Fin m)),
      MvPolynomial.eval (dehomogenizedPoint (laurentColumn q)) f = 0
  equations : Fin equationCount →
    I.map (scalarPolynomialMap
      (k := k) (K := LaurentSeries k) (Fin m))
  coefficients : Fin equationCount → LaurentSeries k
  gradient_identity : ∀ i : Fin m,
    laurentColumn ell i.succ =
      ∑ j, coefficients j *
        differentialAt (dehomogenizedPoint (laurentColumn q))
          (equations j).1 i
  residue_axis :
    residueColumn (fun i : Fin m ↦ ell i.succ) =
      (fun i : Fin m ↦ if i = ⟨0, hm⟩ then 1 else 0)

/-- The corrected finite-gradient certificate produces exactly the Laurent
conormal witness required by the canonical asymptotic step. -/
theorem exists_conormalAxis_of_finiteGradientBoundaryCertificate
    {k : Type u} [Field k]
    {m : ℕ} (hm : 0 < m)
    (I : Ideal (MvPolynomial (Fin m) k))
    (W : FiniteGradientBoundaryCertificate k m hm I) :
    ∃ (y : Fin m → LaurentSeries k)
      (xi : Fin m → PowerSeries k),
      Sum.elim y
          (fun i ↦ algebraMap (PowerSeries k) (LaurentSeries k) (xi i)) ∈
        equationConormalLocus
          (I.map (scalarPolynomialMap
            (k := k) (K := LaurentSeries k) (Fin m))) ∧
      residueColumn xi =
        (fun i : Fin m ↦ if i = ⟨0, hm⟩ then 1 else 0) := by
  let Iext := I.map
    (scalarPolynomialMap (k := k) (K := LaurentSeries k) (Fin m))
  let y := dehomogenizedPoint (laurentColumn W.q)
  let xi : Fin m → PowerSeries k := fun i ↦ W.ell i.succ
  have hconormal :
      coordinateCovector (fun i ↦ laurentColumn W.ell i.succ) ∈
        affineConormalSpace y Iext := by
    exact coordinateCovector_mem_affineConormalSpace_of_finite_gradient
      Iext y (fun i ↦ laurentColumn W.ell i.succ)
        W.equations W.coefficients W.gradient_identity
  refine ⟨y, xi, ?_, W.residue_axis⟩
  refine ⟨?_, ?_⟩
  · simpa [Iext, y] using W.base_vanish
  · simpa [xi, laurentColumn, y, Iext] using hconormal

/-! ## Pointwise handoff to the canonical producer -/

/-- For fixed canonical data, a finite-gradient boundary certificate has
exactly the existential conclusion demanded by
`CanonicalAsymptoticLaurentProducer`.  Thus the remaining nonconstant
geometric producer may target this certificate instead of the stronger
all-tangent-space interface. -/
theorem canonicalAsymptoticLaurentWitness_of_finiteGradientBoundaryCertificate
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    (n N : ℕ) (d : PresentedWeyl k (n + 1))
    (W : FiniteGradientBoundaryCertificate k (n + 1)
      (Nat.zero_lt_succ n)
      (reducedOrderBaseIdeal k
        (canonicalRightIdeal (presentedCoordinate k n) d N))) :
    ∃ (y : Fin (n + 1) → LaurentSeries k)
      (xi : Fin (n + 1) → PowerSeries k),
      Sum.elim y
          (fun i ↦ algebraMap (PowerSeries k) (LaurentSeries k) (xi i)) ∈
        equationConormalLocus
          ((reducedOrderBaseIdeal k
            (canonicalRightIdeal (presentedCoordinate k n) d N)).map
              (scalarPolynomialMap
                (k := k) (K := LaurentSeries k) (Fin (n + 1)))) ∧
      residueColumn xi = pureMomentumFibreAxis k n := by
  obtain ⟨y, xi, hmem, haxis⟩ :=
    exists_conormalAxis_of_finiteGradientBoundaryCertificate
      (k := k) (m := n + 1) (Nat.zero_lt_succ n)
      (reducedOrderBaseIdeal k
        (canonicalRightIdeal (presentedCoordinate k n) d N)) W
  exact ⟨y, xi, hmem, haxis⟩


end

end Stafford38.Geometry.FiniteGradientBoundaryProducer
