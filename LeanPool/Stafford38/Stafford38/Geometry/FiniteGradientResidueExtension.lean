/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Geometry.FiniteGradientBoundaryProducer
import LeanPool.Stafford38.Stafford38.Geometry.LaurentConormalResidueExtension

/-!
# Finite-gradient certificates over a boundary residue field

A boundary divisor can have residue field `K` strictly larger than the ground
field `k`.  The completed arc and its conormal covector then naturally have
coefficients in `PowerSeries K`, while the affine ideal and the fibre symbol
remain defined over `k`.

This file gives the finite-gradient certificate in that coefficient tower and
connects it directly to the residue-extension fibre-symbol contradiction.  No
map `K → k`, algebraic-closedness of `K`, normalization, boundary divisor, or
global certificate construction is assumed.
-/

namespace Stafford38.Geometry.FiniteGradientResidueExtension

open Stafford38.Characteristic
open Stafford38.Geometry.AffineConormalClosure
open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.CoisotropicTranslation
open Stafford38.Geometry.FiniteGradientBoundaryProducer
open Stafford38.Geometry.FormalDivisorLaurentConormal
open Stafford38.Geometry.LaurentConormalDirection
open Stafford38.Geometry.LaurentConormalResidueExtension
open Stafford38.Geometry.ProjectiveConormalDehomogenization
open Stafford38.GeometryRetractionSpecialization

noncomputable section

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- A completed projective arc and one finite gradient identity over the
natural boundary residue field `K`, for an affine ideal defined over `k`. -/
structure FiniteGradientBoundaryCertificateOver
    (m : ℕ) (hm : 0 < m)
    (I : Ideal (MvPolynomial (Fin m) k)) where
  /-- The number of equations in the residue-extension gradient certificate. -/
  equationCount : ℕ
  /-- The formal projective arc over the residue coefficient field. -/
  q : Fin (m + 1) → PowerSeries K
  /-- The formal conormal row over the residue coefficient field. -/
  ell : Fin (m + 1) → PowerSeries K
  q_origin_ne : q 0 ≠ 0
  projective_annihilation :
    ∑ i, laurentColumn ell i * laurentColumn q i = 0
  base_vanish :
    ∀ f ∈ I.map (groundPolynomialMap (k := k) (K := K) (Fin m)),
      MvPolynomial.eval (dehomogenizedPoint (laurentColumn q)) f = 0
  /-- Ground-ideal equations after coefficient extension used to express the conormal row. -/
  equations : Fin equationCount →
    I.map (groundPolynomialMap (k := k) (K := K) (Fin m))
  /-- The Laurent-series coefficients of the finite gradient representation over the residue
  field. -/
  coefficients : Fin equationCount → LaurentSeries K
  gradient_identity : ∀ i : Fin m,
    laurentColumn ell i.succ =
      ∑ j, coefficients j *
        differentialAt (dehomogenizedPoint (laurentColumn q))
          (equations j).1 i
  residue_axis :
    residueColumn (fun i : Fin m ↦ ell i.succ) =
      (fun i : Fin m ↦ if i = ⟨0, hm⟩ then 1 else 0)

/-- A residue-field finite-gradient certificate gives exactly the
`K((t))`-valued equation-conormal point needed by residue specialization. -/
theorem exists_groundConormalAxis_of_finiteGradientBoundaryCertificateOver
    {m : ℕ} (hm : 0 < m)
    (I : Ideal (MvPolynomial (Fin m) k))
    (W : FiniteGradientBoundaryCertificateOver
      (k := k) (K := K) m hm I) :
    ∃ (y : Fin m → LaurentSeries K)
      (xi : Fin m → PowerSeries K),
      Sum.elim y
          (fun i ↦ algebraMap (PowerSeries K) (LaurentSeries K) (xi i)) ∈
        groundEquationConormalLocus (k := k) (K := K) I ∧
      residueColumn xi =
        (fun i : Fin m ↦ if i = ⟨0, hm⟩ then 1 else 0) := by
  let Iext := I.map (groundPolynomialMap (k := k) (K := K) (Fin m))
  let y := dehomogenizedPoint (laurentColumn W.q)
  let xi : Fin m → PowerSeries K := fun i ↦ W.ell i.succ
  have hconormal :
      coordinateCovector (fun i ↦ laurentColumn W.ell i.succ) ∈
        affineConormalSpace y Iext := by
    exact coordinateCovector_mem_affineConormalSpace_of_finite_gradient
      Iext y (fun i ↦ laurentColumn W.ell i.succ)
        W.equations W.coefficients W.gradient_identity
  refine ⟨y, xi, ?_, W.residue_axis⟩
  refine ⟨?_, ?_⟩
  · simpa [Iext, y, groundEquationConormalLocus] using W.base_vanish
  · simpa [xi, laurentColumn, y, Iext] using hconormal

/-- Evaluation on the coordinate axis commutes with extension from `k` to
`K`.  This is the only scalar-extension fact needed for the terminal value
`P(axis)=1`. -/
theorem eval₂_extensionAxis_eq_algebraMap_eval_axis
    {m : ℕ} (hm : 0 < m) (P : MvPolynomial (Fin m) k) :
    MvPolynomial.eval₂ (algebraMap k K)
        (fun i : Fin m ↦ if i = ⟨0, hm⟩ then 1 else 0) P =
      algebraMap k K
        (MvPolynomial.eval
          (fun i : Fin m ↦ if i = ⟨0, hm⟩ then 1 else 0) P) := by
  have hpoint :
      (fun i : Fin m ↦ if i = ⟨0, hm⟩ then (1 : K) else 0) =
        fun i ↦ algebraMap k K
          (if i = ⟨0, hm⟩ then (1 : k) else 0) := by
    funext i
    split <;> simp_all
  rw [hpoint]
  exact (MvPolynomial.map_eval₂Hom
    (RingHom.id k)
    (fun i : Fin m ↦ if i = ⟨0, hm⟩ then (1 : k) else 0)
    (algebraMap k K) P).symm

/-- Direct terminal contradiction from a residue-field finite-gradient
certificate.  The symbol and its axis value stay over `k`; the completed arc
and all gradient coefficients may live over an arbitrary extension `K/k`. -/
theorem false_of_finiteGradientBoundaryCertificateOver
    {m : ℕ} (hm : 0 < m)
    (I : Ideal (MvPolynomial (Fin m) k))
    (P : MvPolynomial (Fin m) k)
    (W : FiniteGradientBoundaryCertificateOver
      (k := k) (K := K) m hm I)
    (hvanishes :
      ∀ q ∈ groundEquationConormalLocus (k := k) (K := K) I,
        MvPolynomial.eval₂ (groundLaurentMap (k := k) (K := K)) q
          (fibreLift P) = 0)
    (haxis : MvPolynomial.eval
      (fun i : Fin m ↦ if i = ⟨0, hm⟩ then 1 else 0) P = 1) : False := by
  obtain ⟨y, xi, hgeneric, hresidue⟩ :=
    exists_groundConormalAxis_of_finiteGradientBoundaryCertificateOver
      (k := k) (K := K) hm I W
  apply false_of_ground_fibreOnly_symbol_one_on_residue_and_vanishing
    (k := k) (K := K) I P
      (fun i : Fin m ↦ if i = ⟨0, hm⟩ then 1 else 0)
      y xi hgeneric hresidue hvanishes
  rw [eval₂_extensionAxis_eq_algebraMap_eval_axis (K := K) hm P, haxis]
  exact map_one (algebraMap k K)


end

end Stafford38.Geometry.FiniteGradientResidueExtension
