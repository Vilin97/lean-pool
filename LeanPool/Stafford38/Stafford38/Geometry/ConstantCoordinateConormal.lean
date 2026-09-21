/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Geometry.AffineConormalClosure
import LeanPool.Stafford38.Stafford38.Geometry.LaurentConormalDirection
import LeanPool.Stafford38.Stafford38.Geometry.ScalarExtensionPoints

/-!
# Constant-coordinate conormal directions

The boundary-divisor argument is needed only when the distinguished affine
coordinate is nonconstant on the relevant base component.  If
`X_i - c` already belongs to the reduced base ideal, its differential is the
pure `i`-th coordinate covector at every base point.  The desired conormal
axis is then present at a constant point, with no projective boundary or
completion.
-/

namespace Stafford38.Geometry.ConstantCoordinateConormal

open Stafford38.Geometry.AffineConormalClosure
open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.CoisotropicTranslation
open Stafford38.Geometry.ScalarExtensionPoints
open Stafford38.GeometryRetractionSpecialization

noncomputable section

universe u

variable {k : Type u} [Field k] {m : ℕ}

/-- The differential of `X_i - c` is the pure `i`-th coordinate covector. -/
theorem differentialCovector_coordinate_sub_constant
    (y : Fin m → k) (i : Fin m) (c : k) :
    differentialCovector y (MvPolynomial.X i - MvPolynomial.C c) =
      coordinateCovector (fun j ↦ if j = i then 1 else 0) := by
  ext v
  simp [differentialCovector, coordinateCovector, differentialAt,
    Pi.single_apply]

/-- A constant-coordinate equation places the corresponding pure axis in the
equation-defined affine conormal space. -/
theorem pureCoordinate_mem_affineConormalSpace_of_sub_constant_mem
    (I : Ideal (MvPolynomial (Fin m) k))
    (y : Fin m → k) (i : Fin m) (c : k)
    (hcoordinate : MvPolynomial.X i - MvPolynomial.C c ∈ I) :
    coordinateCovector (fun j ↦ if j = i then 1 else 0) ∈
      affineConormalSpace y I := by
  rw [affineConormalSpace_eq_equationCovectorSpan]
  rw [← differentialCovector_coordinate_sub_constant y i c]
  apply Submodule.subset_span
  exact ⟨⟨MvPolynomial.X i - MvPolynomial.C c, hcoordinate⟩, rfl⟩

/-- The constant-coordinate branch produces an actual equation-conormal
point over every common zero of the base ideal. -/
theorem constantCoordinate_phasePoint_mem_equationConormalLocus
    (I : Ideal (MvPolynomial (Fin m) k))
    (y : Fin m → k)
    (hy : ∀ f ∈ I, MvPolynomial.eval y f = 0)
    (i : Fin m) (c : k)
    (hcoordinate : MvPolynomial.X i - MvPolynomial.C c ∈ I) :
    Sum.elim y (fun j ↦ if j = i then 1 else 0) ∈
      equationConormalLocus I := by
  refine ⟨?_, ?_⟩
  · intro f hf
    exact hy f hf
  · exact pureCoordinate_mem_affineConormalSpace_of_sub_constant_mem
      I y i c hcoordinate

/-- The same constant-coordinate branch gives the exact Laurent-series point
used by the terminal asymptotic consumer.  All coordinates are constant
series; no boundary valuation is involved. -/
theorem exists_laurentConormalAxis_of_coordinate_sub_constant_mem
    (I : Ideal (MvPolynomial (Fin m) k))
    (y : Fin m → k)
    (hy : ∀ f ∈ I, MvPolynomial.eval y f = 0)
    (i : Fin m) (c : k)
    (hcoordinate : MvPolynomial.X i - MvPolynomial.C c ∈ I) :
    ∃ (yL : Fin m → LaurentSeries k)
      (xi : Fin m → PowerSeries k),
      Sum.elim yL
          (fun j ↦ algebraMap (PowerSeries k) (LaurentSeries k) (xi j)) ∈
        equationConormalLocus
          (I.map (scalarPolynomialMap
            (k := k) (K := LaurentSeries k) (Fin m))) ∧
      residueColumn xi = (fun j ↦ if j = i then 1 else 0) := by
  let yL : Fin m → LaurentSeries k := fun j ↦ algebraMap k (LaurentSeries k) (y j)
  let xi : Fin m → PowerSeries k := fun j ↦
    PowerSeries.C (if j = i then 1 else 0)
  let IL := I.map
    (scalarPolynomialMap (k := k) (K := LaurentSeries k) (Fin m))
  have hyL : ∀ f ∈ IL, MvPolynomial.eval yL f = 0 := by
    rw [show (∀ f ∈ IL, MvPolynomial.eval yL f = 0) ↔
        yL ∈ MvPolynomial.zeroLocus (LaurentSeries k) IL by rfl]
    rw [mem_zeroLocus_map_iff]
    intro f hf
    change MvPolynomial.eval₂ (algebraMap k (LaurentSeries k))
      ((algebraMap k (LaurentSeries k)) ∘ y) f = 0
    rw [← MvPolynomial.eval₂_comp, hy f hf, map_zero]
  have hcoordinateL :
      MvPolynomial.X i -
          MvPolynomial.C (algebraMap k (LaurentSeries k) c) ∈ IL := by
    have hmapped := Ideal.mem_map_of_mem
      (scalarPolynomialMap (k := k) (K := LaurentSeries k) (Fin m))
      hcoordinate
    change (scalarPolynomialMap
      (k := k) (K := LaurentSeries k) (Fin m))
        (MvPolynomial.X i - MvPolynomial.C c) ∈ IL at hmapped
    rw [(scalarPolynomialMap
      (k := k) (K := LaurentSeries k) (Fin m)).map_sub] at hmapped
    simpa [scalarPolynomialMap] using hmapped
  have hphase := constantCoordinate_phasePoint_mem_equationConormalLocus
    IL yL hyL i (algebraMap k (LaurentSeries k) c) hcoordinateL
  refine ⟨yL, xi, ?_, ?_⟩
  · convert hphase using 1
    funext q
    rcases q with j | j
    · rfl
    · simp [xi]
  · funext j
    simp [xi, residueColumn]


end

end Stafford38.Geometry.ConstantCoordinateConormal
