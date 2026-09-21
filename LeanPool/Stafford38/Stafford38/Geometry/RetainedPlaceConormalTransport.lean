/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Geometry.CanonicalNonconstantFiniteGradientProductionProof
import LeanPool.Stafford38.Stafford38.Geometry.DivisorTangentLattice
import LeanPool.Stafford38.Stafford38.Geometry.RetainedGroundMapIdentification

/-!
# Transport of a divisor-tangent conormal row to the completed chart

Let `P` be a prime component of affine `m`-space, `F` its function field,
`W` a retained boundary place for a transcendental component coordinate,
`V` its valuation ring and `Kres` its residue field.  Given

* normalized projective coordinates `q : Fin (m + 1) → V` of the generic
  point (the output of
  `exists_normalizedProjectivePoint_relativeRetainedBoundaryPlace`),
* a visible divisor frame `D` on those coordinates (the input of the
  divisor-tangent lattice lemma), and
* the generic-point Kähler bridge `hbridge` (a relation in `Ω[F⁄k]` among
  the differentials of the coordinates yields an equation-defined conormal
  covector over `F`; proved in a sibling file and taken here as an explicit
  hypothesis),

this file produces the `RegularizedOneRowConormalData` consumed by
`CanonicalNonconstantFiniteGradientProductionProof`, with the residue field
carrying the residue-induced ground structure
`retainedResidueGroundAlgebra`.

What is proved (all trust-zero, no axioms beyond the standard three):

1. `divisorFrame_kaehler_relation`: the lattice lemma gives a covector
   `xi = e₀ - ∑ c_j e_j` with `c_j ∈ V` and `∑ xi_i • d y_i = 0`.
2. `coordinateCovector_map_mem_affineConormalSpace`: equation-defined
   conormal membership transports along any ring homomorphism of fields.
3. `retainedLaurentLift`: the ring homomorphism `F →+* LaurentSeries Kres`
   extending the retained completion, with its ground identification
   `retainedLaurentLift_algebraMap_ground`.
4. `retainedLaurentLift_componentCoordinate`: the transported generic point
   is the dehomogenized completed projective column.
5. `annihilation_identity`: the exact `V`-identity giving the projective
   annihilation row.
6. `regularizedOneRowConormalData_of_transport`: the assembly over an
   abstract local ring `V ⊆ F` with an injective completion map killing the
   residue of nonunits and a compatible Laurent lift of `F`.
7. `exists_regularizedOneRowConormalData`: the instantiation at a retained
   boundary place; the residue field carries `retainedResidueGroundAlgebra`.

What is not proved here: the existence of a visible divisor frame `D`, and
the bridge `hbridge`; both are explicit hypotheses.
-/

namespace Stafford38.Geometry.RetainedPlaceConormalTransport

open IsLocalRing
open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.CanonicalNonconstantFiniteGradientProductionProof
open Stafford38.Geometry.CoisotropicTranslation
open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ComponentProjectiveClosureNormalization
open Stafford38.Geometry.DivisorTangentLattice
open Stafford38.Geometry.FiniteGradientFromTangentInclusion
open Stafford38.Geometry.FormalDivisorLaurentConormal
open Stafford38.Geometry.LaurentConormalResidueExtension
open Stafford38.Geometry.ProjectiveConormalDehomogenization
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.RelativeRetainedBoundaryPlace
open Stafford38.Geometry.RetainedGroundMapIdentification
open Stafford38.Geometry.RetainedProjectiveCompletion
open Stafford38.GeometryRetractionSpecialization

noncomputable section


universe u v

/-! ## Generic algebra: covector transport along a ring homomorphism -/

section CovectorTransport

variable {F L : Type*} [Field F] [Field L] {n : ℕ}

/-- `differentialAt` commutes with coefficient transport. -/
theorem differentialAt_map (ℓ : F →+* L) (y : Fin n → F)
    (f : MvPolynomial (Fin n) F) (i : Fin n) :
    ℓ (differentialAt y f i) =
      differentialAt (ℓ ∘ y) (MvPolynomial.map ℓ f) i := by
  unfold differentialAt
  rw [MvPolynomial.pderiv_map, MvPolynomial.eval_map, MvPolynomial.eval,
    MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left]
  rfl

/-- A coordinate covector given by a finite gradient identity lies in the
equation-defined conormal space. -/
theorem coordinateCovector_mem_of_gradient_identity
    (I : Ideal (MvPolynomial (Fin n) F)) (y xi : Fin n → F)
    {r : ℕ} (equations : Fin r → MvPolynomial (Fin n) F)
    (hmem : ∀ j, equations j ∈ I) (coefficients : Fin r → F)
    (hxi : ∀ i, xi i = ∑ j, coefficients j * differentialAt y (equations j) i) :
    coordinateCovector xi ∈ affineConormalSpace y I := by
  rw [affineConormalSpace_eq_equationCovectorSpan]
  have hcov : coordinateCovector xi =
      ∑ j, coefficients j • differentialCovector y (equations j) := by
    apply LinearMap.ext
    intro v
    simp only [coordinateCovector_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      differentialCovector_apply, smul_eq_mul, Finset.mul_sum, hxi, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  rw [hcov]
  refine Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span ⟨⟨equations j, hmem j⟩, rfl⟩

/-- Equation-defined conormal membership transports along a ring
homomorphism of fields, with the ideal mapped along the same homomorphism. -/
theorem coordinateCovector_map_mem_affineConormalSpace
    (ℓ : F →+* L) (I : Ideal (MvPolynomial (Fin n) F)) (y xi : Fin n → F)
    (hxi : coordinateCovector xi ∈ affineConormalSpace y I) :
    coordinateCovector (ℓ ∘ xi) ∈
      affineConormalSpace (ℓ ∘ y) (I.map (MvPolynomial.map ℓ)) := by
  obtain ⟨r, equations, coefficients, hgradient⟩ :=
    exists_fin_gradient_identity_of_mem_affineConormalSpace I y xi hxi
  refine coordinateCovector_mem_of_gradient_identity _ (ℓ ∘ y) (ℓ ∘ xi)
    (fun j ↦ MvPolynomial.map ℓ (equations j).1)
    (fun j ↦ Ideal.mem_map_of_mem _ (equations j).2)
    (fun j ↦ ℓ (coefficients j)) fun i ↦ ?_
  simp only [Function.comp_apply, hgradient i, map_sum, map_mul, differentialAt_map]

end CovectorTransport

/-! ## Generic algebra: the Kähler relation from the lattice lemma -/

section KaehlerRelation

variable {k V F Ω : Type*}
variable [CommRing k] [CommRing V] [IsLocalRing V] [Field F]
variable [Algebra k F] [Algebra V F]
variable [AddCommGroup Ω] [Module k Ω] [Module F Ω] [Module V Ω]
variable [IsScalarTower V F Ω]
variable {d : Derivation k F Ω} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The lattice lemma, rewritten as a single vanishing relation for the
covector `e_{j₀'} - ∑ c_j e_j` where `c_j = t^(a+e-1) b_j ∈ V`. -/
theorem divisorFrame_kaehler_relation
    (D : VisibleDivisorFrame (V := V) d ι)
    (hinj : Function.Injective (algebraMap V F))
    (y : ι → F) (i₀ : ι)
    (hy : ∀ j, algebraMap V F (D.Q j) / algebraMap V F D.Q₀ = y j)
    (hy₁ : algebraMap V F D.Q₁ / algebraMap V F D.Q₀ = y i₀) :
    ∃ b : ι → V,
      ∑ j, ((if j = i₀ then 1 else 0) -
        algebraMap V F (D.t ^ (D.a + D.e - 1) * b j)) • d (y j) = 0 := by
  obtain ⟨b, hb⟩ := D.exists_coefficients hinj
  refine ⟨b, ?_⟩
  simp only [hy, hy₁] at hb
  simp only [sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, algebraMap_smul]
  rw [← hb, sub_self]

end KaehlerRelation

/-! ## Generic algebra: the annihilation identity in the valuation ring -/

section Annihilation

variable {V : Type*} [CommRing V] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The row `(ell₀, xi_j)` annihilates the projective column `(q₀, q_j)`.
Here `q₀ = t^a u`, `q_{i₀} = q₀ p`, `u uinv = 1`, `c_j = t^(a+e-1) b_j`,
`xi_j = δ_{j i₀} - c_j`, and `ell₀ = ∑ t^(e-1) b_j q_j uinv - p`. -/
theorem annihilation_identity
    (t u uinv p : V) (a e : ℕ) (he : 1 ≤ e) (hu : u * uinv = 1)
    (q₀ : V) (qs : ι → V) (i₀ : ι) (b : ι → V)
    (hq₀ : q₀ = t ^ a * u) (hq₁ : qs i₀ = q₀ * p) :
    ((∑ j, t ^ (e - 1) * b j * qs j * uinv) - p) * q₀ +
      ∑ j, ((if j = i₀ then 1 else 0) - t ^ (a + e - 1) * b j) * qs j = 0 := by
  obtain ⟨e', rfl⟩ := Nat.exists_eq_add_of_le' he
  simp only [Nat.add_sub_cancel, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, hq₁, Finset.sum_mul]
  have hpow : ∀ j, t ^ (a + (e' + 1) - 1) * b j * qs j =
      t ^ e' * b j * qs j * uinv * q₀ := by
    intro j
    rw [show a + (e' + 1) - 1 = e' + a by omega, pow_add, hq₀]
    linear_combination (-(t ^ e' * b j * qs j * t ^ a)) * hu
  simp only [hpow]
  ring

end Annihilation


/-! ## The generic point as a ratio of normalized projective coordinates -/

section GenericPoint

variable {k : Type u} [Field k] {m : ℕ}

/-- A common-scale lift of the projective generic point dehomogenizes to the
component coordinates. -/
theorem componentCoordinate_eq_div
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (qF : Fin (m + 1) → ComponentFractionField P)
    (scale : ComponentFractionField P)
    (hq : ∀ a, qF a = scale * componentProjectivePoint P a)
    (hq0 : qF 0 ≠ 0) (j : Fin m) :
    qF j.succ / qF 0 = componentCoordinate P j := by
  have hscale : scale ≠ 0 := by
    intro h
    apply hq0
    rw [hq 0, h, zero_mul]
  rw [hq, hq]
  simp only [componentProjectivePoint, Fin.cases_zero, Fin.cases_succ, mul_one]
  field_simp

/-- Every equation of the affine component vanishes at the transported
generic point, for any ring homomorphism out of the function field. -/
theorem eval_map_componentCoordinate_eq_zero
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    {L : Type*} [Field L] (ℓ : ComponentFractionField P →+* L)
    {g : MvPolynomial (Fin m) k} (hg : g ∈ P.asIdeal) :
    MvPolynomial.eval (ℓ ∘ componentCoordinate P)
      (MvPolynomial.map (ℓ.comp (algebraMap k (ComponentFractionField P))) g) = 0 := by
  rw [MvPolynomial.eval_map, ← MvPolynomial.eval₂_comp_left,
    ← componentAffineGenericPointMap_eq_eval₂,
    componentAffineGenericPointMap_eq_zero_of_mem P hg, map_zero]

end GenericPoint

/-! ## The Laurent lift of the retained completion -/

section RetainedLift

variable {k : Type u} [Field k] [CharZero k] {m : ℕ}

/-- The retained completion followed by the Laurent embedding. -/
def retainedLaurentBase
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (i : Fin m)
    (W : Data k (ComponentFractionField P) (componentCoordinate P i)) :
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
        (ComponentFractionField P) := W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : IsDiscreteValuationRing V := W.place.isDiscrete
    letI : Algebra W.coefficientField V :=
      (relativeCoefficientMap W.coefficientField W.place).toAlgebra
    V →+* LaurentSeries (ResidueField V) := by
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
      (ComponentFractionField P) := W.ambientAlgebra
  let V := W.place.valuation.toSubring
  letI : IsDiscreteValuationRing V := W.place.isDiscrete
  letI : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  exact (algebraMap (PowerSeries (ResidueField V))
    (LaurentSeries (ResidueField V))).comp (retainedToCompletedPowerSeries W)

theorem retainedLaurentBase_injective
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (i : Fin m)
    (W : Data k (ComponentFractionField P) (componentCoordinate P i)) :
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
        (ComponentFractionField P) := W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : IsDiscreteValuationRing V := W.place.isDiscrete
    letI : Algebra W.coefficientField V :=
      (relativeCoefficientMap W.coefficientField W.place).toAlgebra
    Function.Injective (retainedLaurentBase P i W) := by
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
      (ComponentFractionField P) := W.ambientAlgebra
  let V := W.place.valuation.toSubring
  letI : IsDiscreteValuationRing V := W.place.isDiscrete
  letI : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  exact (IsFractionRing.injective (PowerSeries (ResidueField V))
    (LaurentSeries (ResidueField V))).comp
    (retainedToCompletedPowerSeries_injective W)

/-- The retained completion `V →+* PowerSeries Kres`, followed by the Laurent
embedding, extends uniquely to the component function field. -/
def retainedLaurentLift
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (i : Fin m)
    (W : Data k (ComponentFractionField P) (componentCoordinate P i)) :
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
        (ComponentFractionField P) := W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : IsDiscreteValuationRing V := W.place.isDiscrete
    letI : Algebra W.coefficientField V :=
      (relativeCoefficientMap W.coefficientField W.place).toAlgebra
    ComponentFractionField P →+* LaurentSeries (ResidueField V) := by
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
      (ComponentFractionField P) := W.ambientAlgebra
  let V := W.place.valuation.toSubring
  letI : IsDiscreteValuationRing V := W.place.isDiscrete
  letI : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  letI : IsFractionRing V (ComponentFractionField P) :=
    (inferInstance : IsFractionRing (↥W.place.valuation) (ComponentFractionField P))
  exact IsFractionRing.lift (A := V) (K := ComponentFractionField P)
    (retainedLaurentBase_injective P i W)

/-- The Laurent lift restricts to the retained completion on `V`. -/
theorem retainedLaurentLift_algebraMap
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (i : Fin m)
    (W : Data k (ComponentFractionField P) (componentCoordinate P i)) :
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
        (ComponentFractionField P) := W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : IsDiscreteValuationRing V := W.place.isDiscrete
    letI : Algebra W.coefficientField V :=
      (relativeCoefficientMap W.coefficientField W.place).toAlgebra
    ∀ v : ↥V, retainedLaurentLift P i W (algebraMap V (ComponentFractionField P) v) =
      algebraMap (PowerSeries (ResidueField V)) (LaurentSeries (ResidueField V))
        (retainedToCompletedPowerSeries W v) := by
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
      (ComponentFractionField P) := W.ambientAlgebra
  let V := W.place.valuation.toSubring
  letI : IsDiscreteValuationRing V := W.place.isDiscrete
  letI : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  letI : IsFractionRing V (ComponentFractionField P) :=
    (inferInstance : IsFractionRing (↥W.place.valuation) (ComponentFractionField P))
  dsimp only
  intro v
  exact IsFractionRing.lift_algebraMap (A := V) (K := ComponentFractionField P)
    (retainedLaurentBase_injective P i W) v

/-- With the residue-induced ground structure, the Laurent lift restricts to
the terminal consumer's ground map on `k`. -/
theorem retainedLaurentLift_comp_algebraMap
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (i : Fin m)
    (W : Data k (ComponentFractionField P) (componentCoordinate P i)) :
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
        (ComponentFractionField P) := W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : IsDiscreteValuationRing V := W.place.isDiscrete
    letI : Algebra W.coefficientField V :=
      (relativeCoefficientMap W.coefficientField W.place).toAlgebra
    letI : Algebra k (ResidueField V) :=
      retainedResidueGroundAlgebra P i W
    (retainedLaurentLift P i W).comp (algebraMap k (ComponentFractionField P)) =
      groundLaurentMap (k := k) (K := ResidueField V) := by
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
      (ComponentFractionField P) := W.ambientAlgebra
  let V := W.place.valuation.toSubring
  letI : IsDiscreteValuationRing V := W.place.isDiscrete
  letI : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  letI : Algebra k (ResidueField V) :=
    retainedResidueGroundAlgebra P i W
  letI : SMul W.coefficientField (CoordinateZeroLocalRing W.coefficientField) := Algebra.toSMul
  letI : SMul (CoordinateZeroLocalRing W.coefficientField) (ComponentFractionField P) := Algebra.toSMul
  letI : SMul W.coefficientField (ComponentFractionField P) := Algebra.toSMul
  letI : IsScalarTower W.coefficientField
      (CoordinateZeroLocalRing W.coefficientField)
      (ComponentFractionField P) := W.coefficientTower
  have hcoeff : ∀ c : k, algebraMap k (ComponentFractionField P) c =
      algebraMap V (ComponentFractionField P)
        (retainedComponentCoefficientMap P i W c) := by
    intro c
    change algebraMap k (ComponentFractionField P) c =
      ((relativeCoefficientMap W.coefficientField W.place
        (algebraMap k W.coefficientField c) : V) : ComponentFractionField P)
    calc
      algebraMap k (ComponentFractionField P) c =
          algebraMap W.coefficientField (ComponentFractionField P)
            (algebraMap k W.coefficientField c) :=
        IsScalarTower.algebraMap_apply k W.coefficientField
          (ComponentFractionField P) c
      _ = ((relativeCoefficientMap W.coefficientField W.place
          (algebraMap k W.coefficientField c) : V) :
          ComponentFractionField P) :=
        (DFunLike.congr_fun
          (relativeCoefficientMap_commutes W.coefficientField W.place)
          (algebraMap k W.coefficientField c)).symm
  have hlift : (retainedLaurentLift P i W).comp
      (algebraMap k (ComponentFractionField P)) =
      retainedLaurentCoefficientMap P i W := by
    refine RingHom.ext fun c ↦ ?_
    change retainedLaurentLift P i W (algebraMap k (ComponentFractionField P) c) = _
    have h := retainedLaurentLift_algebraMap P i W (retainedComponentCoefficientMap P i W c)
    have result := (congrArg (retainedLaurentLift P i W) (hcoeff c)).trans h
    exact result
  exact hlift.trans (retainedLaurentCoefficientMap_eq_groundLaurentMap P i W)

/-- The transported generic point is the dehomogenized completed projective
column. -/
theorem retainedLaurentLift_componentCoordinate
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (i : Fin m)
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
      q 0 ≠ 0 →
      retainedLaurentLift P i W ∘ componentCoordinate P =
        dehomogenizedPoint
          (laurentColumn fun a ↦ retainedToCompletedPowerSeries W (q a)) := by
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
      (ComponentFractionField P) := W.ambientAlgebra
  let V := W.place.valuation.toSubring
  letI : IsDiscreteValuationRing V := W.place.isDiscrete
  letI : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  dsimp only
  intro q scale hq hq0
  have hq0F : (q 0 : ComponentFractionField P) ≠ 0 := fun h ↦ hq0 (Subtype.ext h)
  have hlift : ∀ v : V, retainedLaurentLift P i W (algebraMap V (ComponentFractionField P) v) =
      algebraMap (PowerSeries (ResidueField V)) (LaurentSeries (ResidueField V))
        (retainedToCompletedPowerSeries W v) := retainedLaurentLift_algebraMap P i W
  have hdiv : ∀ j : Fin m, componentCoordinate P j =
      algebraMap V (ComponentFractionField P) (q j.succ) /
        algebraMap V (ComponentFractionField P) (q 0) := fun j ↦
    (componentCoordinate_eq_div P (fun a ↦ (q a : ComponentFractionField P))
      scale hq hq0F j).symm
  funext j
  simp only [Function.comp_apply, dehomogenizedPoint, laurentColumn, hdiv, map_div₀, hlift]
  rfl

end RetainedLift
/-! ## Abstract assembly -/

section AbstractAssembly

variable {k F Kres V : Type u} [Field k] [Field F] [Algebra k F] [Field Kres] [Algebra k Kres]
variable [CommRing V] [IsLocalRing V] [Algebra V F]
variable [SMulCommClass k V F]
variable {m : ℕ}

/-- Abstract assembly of the one-row datum.  `φ` is the completion of `V`
(injective, killing the residue of nonunits), `ℓ` the compatible extension
to `F` with the ground identification, `q` the normalized projective
coordinates of the generic point `y`, `D` the divisor frame on `q`, and
`hbridge` the generic-point Kähler bridge. -/
theorem regularizedOneRowConormalData_of_transport
    (hm : 0 < m) (I : Ideal (MvPolynomial (Fin m) k)) (y : Fin m → F)
    (hIy : ∀ g ∈ I, MvPolynomial.eval₂ (algebraMap k F) y g = 0)
    (hinj : Function.Injective (algebraMap V F))
    (φ : V →+* PowerSeries Kres) (hφinj : Function.Injective φ)
    (hφconst : ∀ v : V, ¬IsUnit v → PowerSeries.constantCoeff (R := Kres) (φ v) = 0)
    (ℓ : F →+* LaurentSeries Kres)
    (hℓ : ∀ v : V, ℓ (algebraMap V F v) =
      algebraMap (PowerSeries Kres) (LaurentSeries Kres) (φ v))
    (hground : ℓ.comp (algebraMap k F) = groundLaurentMap (k := k) (K := Kres))
    (q : Fin (m + 1) → V) (hq0 : q 0 ≠ 0)
    (hdiv : ∀ j, algebraMap V F (q j.succ) / algebraMap V F (q 0) = y j)
    (p : V) (hratio : q (Fin.succ ⟨0, hm⟩) = q 0 * p)
    (D : VisibleDivisorFrame (V := V) (KaehlerDifferential.D k F) (Fin m))
    (hQ₀ : D.Q₀ = q 0) (hQ₁ : D.Q₁ = q (Fin.succ ⟨0, hm⟩))
    (hQ : ∀ j, D.Q j = q (Fin.succ j))
    (hbridge : ∀ xi : Fin m → F,
      ∑ j, xi j • KaehlerDifferential.D k F (y j) = 0 →
      coordinateCovector xi ∈ affineConormalSpace y
        (I.map (MvPolynomial.map (algebraMap k F)))) :
    Nonempty (RegularizedOneRowConormalData (k := k) (K := Kres) hm I
      (fun a ↦ φ (q a))) := by
  let i₀ : Fin m := ⟨0, hm⟩
  let ψ : PowerSeries Kres →+* LaurentSeries Kres :=
    algebraMap (PowerSeries Kres) (LaurentSeries Kres)
  have hpoint : ℓ ∘ y = dehomogenizedPoint (laurentColumn fun a ↦ φ (q a)) := by
    funext j
    simp only [Function.comp_apply, dehomogenizedPoint, laurentColumn, ← hdiv, map_div₀, hℓ]
  obtain ⟨b, hb⟩ := divisorFrame_kaehler_relation D hinj y i₀
    (fun j ↦ by rw [hQ j, hQ₀]; exact hdiv j) (by rw [hQ₁, hQ₀]; exact hdiv i₀)
  let c : Fin m → V := fun j ↦ D.t ^ (D.a + D.e - 1) * b j
  let xiV : Fin m → V := fun j ↦ (if j = i₀ then 1 else 0) - c j
  let xi : Fin m → F := fun j ↦ (if j = i₀ then 1 else 0) - algebraMap V F (c j)
  have hxi : ∀ j, algebraMap V F (xiV j) = xi j := by
    intro j
    simp only [xiV, xi, map_sub]
    split_ifs <;> simp
  have hconormalF : coordinateCovector xi ∈ affineConormalSpace y
      (I.map (MvPolynomial.map (algebraMap k F))) := hbridge xi hb
  have hcnonunit : ∀ j, ¬IsUnit (c j) := by
    intro j
    have hpos : 0 < D.a + D.e - 1 := by
      have := D.one_le_a; have := D.one_le_e; omega
    have hmem : c j ∈ maximalIdeal V :=
      Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ D.t_mem _ hpos)
    exact mem_nonunits_iff.1 ((mem_maximalIdeal _).1 hmem)
  let uinv : V := ↑D.u_unit.unit⁻¹
  have hu : D.u * uinv = 1 := D.u_unit.mul_val_inv
  let ell₀ : V := (∑ j, D.t ^ (D.e - 1) * b j * q j.succ * uinv) - p
  have hann : ell₀ * q 0 + ∑ j, xiV j * q j.succ = 0 :=
    annihilation_identity D.t D.u uinv p D.a D.e D.one_le_e hu
      (q 0) (fun j ↦ q j.succ) i₀ b (hQ₀.symm.trans D.Q₀_eq) hratio
  let ell : Fin (m + 1) → PowerSeries Kres :=
    Fin.cases (φ ell₀) (fun j ↦ φ (xiV j))
  have hcol : (fun i ↦ laurentColumn ell i.succ) = ℓ ∘ xi := by
    funext i
    simp only [laurentColumn, ell, Fin.cases_succ, Function.comp_apply, ← hxi, hℓ]
  have hideal : (I.map (MvPolynomial.map (algebraMap k F))).map (MvPolynomial.map ℓ) =
      I.map (groundPolynomialMap (k := k) (K := Kres) (Fin m)) := by
    rw [Ideal.map_map]
    congr 1
    refine RingHom.ext fun f ↦ ?_
    simp only [RingHom.comp_apply, MvPolynomial.map_map, groundPolynomialMap, hground]
  refine ⟨{
    ell := ell
    q_origin_ne := ?_
    projective_annihilation := ?_
    base_vanish := ?_
    conormal := ?_
    residue_axis := ?_ }⟩
  · intro h
    exact hq0 (hφinj (h.trans (map_zero _).symm))
  · have h := congrArg (ψ.comp φ) hann
    simp only [RingHom.comp_apply, map_add, map_mul, map_sum, map_zero] at h
    simpa only [laurentColumn, Fin.sum_univ_succ, ell, Fin.cases_zero, Fin.cases_succ]
      using h
  · intro f hf
    rw [← hpoint]
    have hle : I.map (groundPolynomialMap (k := k) (K := Kres) (Fin m)) ≤
        RingHom.ker (MvPolynomial.eval (ℓ ∘ y)) := by
      refine Ideal.map_le_iff_le_comap.mpr fun g hg ↦ ?_
      rw [Ideal.mem_comap, RingHom.mem_ker, groundPolynomialMap, ← hground,
        MvPolynomial.eval_map, ← MvPolynomial.eval₂_comp_left, hIy g hg, map_zero]
    exact hle hf
  · rw [hcol, ← hpoint, ← hideal]
    exact coordinateCovector_map_mem_affineConormalSpace ℓ _ _ xi hconormalF
  · funext j
    simp only [residueColumn, ell, Fin.cases_succ, xiV, map_sub, hφconst (c j) (hcnonunit j),
      sub_zero]
    split_ifs <;> simp

end AbstractAssembly


/-! ## The concrete transport theorem -/

section Assembly

variable {k : Type u} [Field k] [CharZero k] {m : ℕ}

/-- The transport theorem at a retained boundary place.  Explicit inputs:
normalized projective coordinates `q` of the generic point in the retained
valuation ring (as produced by
`exists_normalizedProjectivePoint_relativeRetainedBoundaryPlace`), a visible
divisor frame `D` on them, and the generic-point Kähler bridge `hbridge`. -/
theorem exists_regularizedOneRowConormalData
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (hm : 0 < m)
    (W : Data k (ComponentFractionField P) (componentCoordinate P ⟨0, hm⟩)) :
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
        (ComponentFractionField P) := W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : IsDiscreteValuationRing V := W.place.isDiscrete
    letI : Algebra W.coefficientField V :=
      (relativeCoefficientMap W.coefficientField W.place).toAlgebra
    letI : Algebra k (ResidueField V) :=
      retainedResidueGroundAlgebra P ⟨0, hm⟩ W
    ∀ (q : Fin (m + 1) → V) (scale : ComponentFractionField P),
      q 0 ≠ 0 →
      (∀ a, (q a : ComponentFractionField P) =
        scale * componentProjectivePoint P a) →
      q (Fin.succ ⟨0, hm⟩) = q 0 * W.place.parameter →
      ∀ D : VisibleDivisorFrame (V := V)
        (KaehlerDifferential.D k (ComponentFractionField P)) (Fin m),
      D.Q₀ = q 0 → D.Q₁ = q (Fin.succ ⟨0, hm⟩) → (∀ j, D.Q j = q (Fin.succ j)) →
      (∀ xi : Fin m → ComponentFractionField P,
        ∑ j, xi j • KaehlerDifferential.D k (ComponentFractionField P)
          (componentCoordinate P j) = 0 →
        coordinateCovector xi ∈ affineConormalSpace (componentCoordinate P)
          (P.asIdeal.map (MvPolynomial.map
            (algebraMap k (ComponentFractionField P))))) →
      Nonempty (RegularizedOneRowConormalData (k := k) (K := ResidueField V)
        hm P.asIdeal (fun a ↦ retainedToCompletedPowerSeries W (q a))) := by
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
      (ComponentFractionField P) := W.ambientAlgebra
  let V := W.place.valuation.toSubring
  letI : IsDiscreteValuationRing V := W.place.isDiscrete
  letI : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  letI : Algebra k (ResidueField V) :=
    retainedResidueGroundAlgebra P ⟨0, hm⟩ W
  dsimp only
  intro q scale hq0 hq hratio D hQ₀ hQ₁ hQ hbridge
  have hq0F : (q 0 : ComponentFractionField P) ≠ 0 := fun h ↦ hq0 (Subtype.ext h)
  have hIy : ∀ g ∈ P.asIdeal,
      MvPolynomial.eval₂ (algebraMap k (ComponentFractionField P))
        (componentCoordinate P) g = 0 := by
    intro g hg
    rw [← componentAffineGenericPointMap_eq_eval₂]
    exact componentAffineGenericPointMap_eq_zero_of_mem P hg
  exact regularizedOneRowConormalData_of_transport hm P.asIdeal (componentCoordinate P)
    hIy Subtype.val_injective (retainedToCompletedPowerSeries W)
    (retainedToCompletedPowerSeries_injective W)
    (retainedToCompletedPowerSeries_constantCoeff_eq_zero_of_nonunit W)
    (retainedLaurentLift P ⟨0, hm⟩ W)
    (retainedLaurentLift_algebraMap P ⟨0, hm⟩ W)
    (retainedLaurentLift_comp_algebraMap P ⟨0, hm⟩ W)
    q hq0 (componentCoordinate_eq_div P (fun a ↦ (q a : ComponentFractionField P))
      scale hq hq0F)
    W.place.parameter hratio D hQ₀ hQ₁ hQ hbridge

end Assembly


end

end Stafford38.Geometry.RetainedPlaceConormalTransport
