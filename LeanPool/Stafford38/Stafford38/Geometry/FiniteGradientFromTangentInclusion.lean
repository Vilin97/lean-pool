/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Geometry.FiniteGradientBoundaryProducer
import LeanPool.Stafford38.Stafford38.Geometry.ProjectiveTangentInclusion

/-!
# Extracting a finite gradient certificate from tangent inclusion

The formal-divisor construction already produces a projective power-series
arc and a row annihilating its explicit tangent columns.  The remaining local
commutative-algebra condition is that the equation-defined Zariski tangent
space at the dehomogenized Laurent point be contained in the span of those
columns.  Under exactly that condition, finite-dimensional annihilator
duality places the affine tail of the row in the span of equation
differentials.  A finitely supported expansion can then be reindexed by a
finite type, producing the finite-gradient boundary certificate used by the
canonical asymptotic consumer.

Thus no separate finite-generation theorem for the ideal is needed.  The
global normalization argument has only to establish the displayed tangent
inclusion for the completed boundary chart (and separately handle any
residue-field transport).
-/

namespace Stafford38.Geometry.FiniteGradientFromTangentInclusion

open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.CoisotropicTranslation
open Stafford38.Geometry.FiniteGradientBoundaryProducer
open Stafford38.Geometry.FormalDivisorLaurentConormal
open Stafford38.Geometry.ProjectiveConormalDehomogenization
open Stafford38.Geometry.ProjectiveTangentInclusion
open Stafford38.Geometry.ScalarExtensionPoints
open Stafford38.GeometryFormalDivisorTangent
open Stafford38.GeometryRetractionSpecialization

noncomputable section

universe u

variable {k : Type u} [Field k]

/-! ## Finite reindexing of an equation-differential expansion -/

/-- Membership of a coordinate covector in the equation conormal space gives
an honest `Fin r`-indexed gradient identity.  This is the finite-support
content of `Submodule.span`; it does not require the whole ideal to be
finitely generated. -/
theorem exists_fin_gradient_identity_of_mem_affineConormalSpace
    {m : ℕ}
    (I : Ideal (MvPolynomial (Fin m) k))
    (y xi : Fin m → k)
    (hxi : coordinateCovector xi ∈ affineConormalSpace y I) :
    ∃ (r : ℕ) (equations : Fin r → I) (coefficients : Fin r → k),
      ∀ i, xi i = ∑ j, coefficients j * differentialAt y (equations j).1 i := by
  classical
  obtain ⟨c, hc⟩ :=
    coordinate_mem_affineConormalSpace_exists_finsupp y xi I hxi
  let ι := {f : I // f ∈ c.support}
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let equations : Fin (Fintype.card ι) → I := fun j ↦ (e.symm j).1
  let coefficients : Fin (Fintype.card ι) → k := fun j ↦ c (e.symm j).1
  refine ⟨Fintype.card ι, equations, coefficients, fun i ↦ ?_⟩
  rw [hc i]
  calc
    ∑ f ∈ c.support, c f * differentialAt y f.1 i =
        ∑ f : ι, c f.1 * differentialAt y f.1.1 i := by
          exact Finset.sum_subtype c.support (by simp)
            (fun f ↦ c f * differentialAt y f.1 i)
    _ = ∑ j : Fin (Fintype.card ι),
        coefficients j * differentialAt y (equations j).1 i := by
          exact Fintype.sum_equiv e _ _ (fun f ↦ by
            simp [coefficients, equations])

/-! ## Completed formal chart to finite-gradient certificate -/

/-- A formal projective row plus the standard tangent-inclusion condition
constructs the complete finite-gradient boundary certificate.

This theorem identifies the exact higher-dimensional local bridge left to
the normalization argument: prove the Zariski tangent space of the
scalar-extended ambient ideal is contained in the dehomogenized span of the
formal divisor and normalized transverse columns.  Once that inclusion is
available, Mathlib's finite-dimensional annihilator and finite-support span
machinery supplies the finite equations and coefficients automatically. -/
theorem exists_finiteGradientBoundaryCertificate_of_zariski_le_formalSpan
    {m : ℕ} (hm : 0 < m)
    (I : Ideal (MvPolynomial (Fin m) k))
    {κ : Type*} [Fintype κ]
    (q ell : Fin (m + 1) → PowerSeries k)
    (Z : Matrix (Fin (m + 1)) κ (PowerSeries k))
    (tau : Fin (m + 1) → PowerSeries k)
    (hq0 : q 0 ≠ 0)
    (hrow : rowMul ell (formalTangentMatrix q Z tau) = 0)
    (hbase : ∀ f ∈
        I.map (scalarPolynomialMap
          (k := k) (K := LaurentSeries k) (Fin m)),
      MvPolynomial.eval (dehomogenizedPoint (laurentColumn q)) f = 0)
    (htangent :
      zariskiTangentSpace (dehomogenizedPoint (laurentColumn q))
          (I.map (scalarPolynomialMap
            (k := k) (K := LaurentSeries k) (Fin m))) ≤
        dehomogenizedTangentSpan (laurentColumn q)
          (laurentNonpositionTangentMatrix Z tau))
    (hresidue :
      residueColumn (fun i : Fin m ↦ ell i.succ) =
        (fun i : Fin m ↦ if i = ⟨0, hm⟩ then 1 else 0)) :
    Nonempty (FiniteGradientBoundaryCertificate k m hm I) := by
  let Iext := I.map
    (scalarPolynomialMap (k := k) (K := LaurentSeries k) (Fin m))
  let y := dehomogenizedPoint (laurentColumn q)
  let xi : Fin m → LaurentSeries k := fun i ↦ laurentColumn ell i.succ
  have hconormal : coordinateCovector xi ∈ affineConormalSpace y Iext := by
    exact coordinateCovector_mem_affineConormalSpace_of_zariski_le_span
      Iext (laurentColumn q) (laurentColumn ell)
        (laurentNonpositionTangentMatrix Z tau)
        (laurentColumn_ne_zero_of_ne_zero q hq0)
        (laurentColumn_dot_eq_zero_of_formalTangent_rowMul q ell Z tau hrow)
        (laurentNonposition_rowMul_eq_zero_of_formalTangent_rowMul
          q ell Z tau hrow)
        htangent
  obtain ⟨r, equations, coefficients, hgradient⟩ :=
    exists_fin_gradient_identity_of_mem_affineConormalSpace
      Iext y xi hconormal
  exact ⟨{
    equationCount := r
    q := q
    ell := ell
    q_origin_ne := hq0
    projective_annihilation :=
      laurentColumn_dot_eq_zero_of_formalTangent_rowMul q ell Z tau hrow
    base_vanish := hbase
    equations := equations
    coefficients := coefficients
    gradient_identity := hgradient
    residue_axis := hresidue
  }⟩


end

end Stafford38.Geometry.FiniteGradientFromTangentInclusion
