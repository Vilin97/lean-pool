/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import Mathlib.Algebra.MvPolynomial.Derivation
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Module
public import LeanPool.Stafford38.Stafford38.Geometry.AffineConormalSpan


/-!
# Kähler relations at the generic point are affine conormal covectors

Let `A = k[X_1, …, X_m] ⧸ I` be a prime affine component with fraction
field `F`, and let `y_i ∈ F` be the images of the coordinates (the generic
point of the component).  If a coefficient vector `ξ ∈ F^m` satisfies the
Kähler relation `∑ ξ_i d y_i = 0` in `Ω[F⁄k]`, then the coordinate covector
`v ↦ ∑ ξ_i v_i` lies in the equation-defined affine conormal space of the
extended ideal `I·F[X]` at `y`.

The proof turns a tangent vector `v` into a derivation `k[X] → F`, descends
it to `A`, extends it through `Ω[A⁄k] → Ω[F⁄k]` (which is a localization of
modules), and evaluates the resulting `F`-linear functional on the relation.

Not proved here: nothing about places, residue fields, boundary charts,
smoothness, or geometric conormal bundles.  Only linear algebra of Kähler
differentials and derivations over the fraction field of a quotient ring.
-/

@[expose] public section

namespace Stafford38.Geometry.GenericPointKaehlerConormal

open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.CoisotropicTranslation
open MvPolynomial

noncomputable section

universe u


variable {k : Type u} [Field k] {m : ℕ}

section Descent

variable {P : Type*} [CommRing P] [Algebra k P] {I : Ideal P}
  {F : Type*} [CommRing F] [Algebra k F] [Algebra (P ⧸ I) F]
  [IsScalarTower k (P ⧸ I) F] [Module P F]

/-- The underlying linear map of a derivation vanishing on `I`, descended to
the quotient `P ⧸ I`. -/
def quotientDerivationLinear (D : Derivation k P F) (hD : ∀ f ∈ I, D f = 0) :
    (P ⧸ I) →ₗ[k] F :=
  (Submodule.liftQ (I.restrictScalars k) D.toLinearMap (by
      intro f hf
      exact hD f hf)).comp
    (Submodule.Quotient.restrictScalarsEquiv k I).symm.toLinearMap

omit [IsScalarTower k (P ⧸ I) F] in
omit [Algebra (P ⧸ I) F] in
theorem quotientDerivationLinear_mk (D : Derivation k P F) (hD : ∀ f ∈ I, D f = 0)
    (f : P) :
    quotientDerivationLinear D hD (Ideal.Quotient.mk I f) = D f :=
  rfl

/-- A derivation `P → F` vanishing on `I` descends to a derivation `P ⧸ I → F`,
provided the `P`-action on `F` factors through `P ⧸ I`. -/
def quotientDerivation [IsScalarTower P (P ⧸ I) F]
    (D : Derivation k P F) (hD : ∀ f ∈ I, D f = 0) :
    Derivation k (P ⧸ I) F where
  toLinearMap := quotientDerivationLinear D hD
  map_one_eq_zero' := by
    have h1 : (1 : P ⧸ I) = Ideal.Quotient.mk I 1 := by simp
    rw [h1]
    change quotientDerivationLinear D hD (Ideal.Quotient.mk I 1) = 0
    rw [quotientDerivationLinear_mk, Derivation.map_one_eq_zero]
  leibniz' a b := by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective b
    change quotientDerivationLinear D hD (Ideal.Quotient.mk I p * Ideal.Quotient.mk I q) =
      Ideal.Quotient.mk I p • quotientDerivationLinear D hD (Ideal.Quotient.mk I q) +
        Ideal.Quotient.mk I q • quotientDerivationLinear D hD (Ideal.Quotient.mk I p)
    rw [← map_mul, quotientDerivationLinear_mk, quotientDerivationLinear_mk,
      quotientDerivationLinear_mk, Derivation.leibniz]
    rw [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_smul (P ⧸ I) p,
      ← IsScalarTower.algebraMap_smul (P ⧸ I) q]

omit [IsScalarTower k (P ⧸ I) F] in
theorem quotientDerivation_mk [IsScalarTower P (P ⧸ I) F]
    (D : Derivation k P F) (hD : ∀ f ∈ I, D f = 0) (f : P) :
    quotientDerivation D hD (Ideal.Quotient.mk I f) = D f :=
  quotientDerivationLinear_mk D hD f

end Descent

section Main

variable {F : Type*} [Field F] [Algebra k F]
  {I : Ideal (MvPolynomial (Fin m) k)} [I.IsPrime]
  [Algebra (MvPolynomial (Fin m) k ⧸ I) F]
  [IsScalarTower k (MvPolynomial (Fin m) k ⧸ I) F]
  [IsFractionRing (MvPolynomial (Fin m) k ⧸ I) F]

/-- The generic point of the component: images of the coordinates in `F`. -/
def genericPoint (I : Ideal (MvPolynomial (Fin m) k)) (F : Type*) [Field F]
    [Algebra (MvPolynomial (Fin m) k ⧸ I) F] : Fin m → F :=
  fun i ↦ algebraMap (MvPolynomial (Fin m) k ⧸ I) F (Ideal.Quotient.mk I (X i))

/-- The equation ideal extended to `F[X]`. -/
def extendedIdeal (I : Ideal (MvPolynomial (Fin m) k)) (F : Type*) [Field F]
    [Algebra k F] : Ideal (MvPolynomial (Fin m) F) :=
  I.map (MvPolynomial.map (algebraMap k F))

/-- Evaluation of `MvPolynomial.mkDerivation` through partial derivatives,
when the polynomial ring acts on `F` through evaluation at `y`. -/
theorem mkDerivation_eq_sum_pderiv [Algebra (MvPolynomial (Fin m) k) F]
    [IsScalarTower k (MvPolynomial (Fin m) k) F]
    (y v : Fin m → F)
    (halg : ∀ p : MvPolynomial (Fin m) k, algebraMap (MvPolynomial (Fin m) k) F p = aeval y p)
    (f : MvPolynomial (Fin m) k) :
    mkDerivation k v f = ∑ i, aeval y (pderiv i f) * v i := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [← MvPolynomial.algebraMap_eq, Derivation.map_algebraMap]
    simp
  | add p q hp hq =>
    simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p n hp =>
    have h1 : ∑ i, aeval y (pderiv i (p * X n)) * v i =
        aeval y p * v n + y n * ∑ i, aeval y (pderiv i p) * v i := by
      have h2 : ∀ i, aeval y (pderiv i (p * X n)) * v i =
          aeval y p * (if n = i then v i else 0) + y n * (aeval y (pderiv i p) * v i) := by
        intro i
        simp only [pderiv_mul, map_add, map_mul, aeval_X, pderiv_X, Pi.single_apply]
        split_ifs <;> simp <;> ring
      simp only [h2, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true]
    rw [h1, Derivation.leibniz, mkDerivation_X, hp, Algebra.smul_def, Algebra.smul_def, halg, halg,
      aeval_X]

omit [I.IsPrime] [IsScalarTower k (MvPolynomial (Fin m) k ⧸ I) F] in
omit [Algebra k F] in
/-- Nonzero-divisors of `A` act invertibly on the fraction field `F`. -/
theorem isUnit_algebraMap_end
    (s : nonZeroDivisors (MvPolynomial (Fin m) k ⧸ I)) :
    IsUnit (algebraMap (MvPolynomial (Fin m) k ⧸ I)
      (Module.End (MvPolynomial (Fin m) k ⧸ I) F) s) := by
  rw [Module.End.isUnit_iff]
  have hfun : ⇑(algebraMap (MvPolynomial (Fin m) k ⧸ I)
      (Module.End (MvPolynomial (Fin m) k ⧸ I) F) s) = fun x ↦ (s : MvPolynomial (Fin m) k ⧸ I)
        • x :=
    funext fun _ ↦ rfl
  rw [hfun]
  have := IsLocalization.smul_bijective (M := nonZeroDivisors (MvPolynomial (Fin m) k ⧸ I)) F s
  simpa [Submonoid.smul_def] using this

omit [I.IsPrime] in
/-- **Main theorem.**  A Kähler relation among the generic-point coordinates
places the corresponding coordinate covector in the affine conormal space of
the extended ideal at the generic point. -/
theorem coordinateCovector_mem_affineConormalSpace_of_kaehler_sum_eq_zero
    (xi : Fin m → F)
    (h : ∑ i, xi i • KaehlerDifferential.D k F (genericPoint I F i) = 0) :
    coordinateCovector xi ∈ affineConormalSpace (genericPoint I F) (extendedIdeal I F) := by
  classical
  set A := MvPolynomial (Fin m) k ⧸ I
  set y := genericPoint I F
  rw [affineConormalSpace, Submodule.mem_dualAnnihilator]
  intro v hv
  rw [zariskiTangentSpace, Submodule.mem_dualCoannihilator] at hv
  have htan : ∀ f ∈ extendedIdeal I F, ∑ i, differentialAt y f i * v i = 0 := by
    intro f hf
    have := hv (differentialCovector y f) (Submodule.subset_span ⟨⟨f, hf⟩, rfl⟩)
    simpa using this
  -- `P`-algebra structure on `F` through the quotient and the fraction field.
  let _ : Algebra (MvPolynomial (Fin m) k) F :=
    ((algebraMap A F).comp (algebraMap (MvPolynomial (Fin m) k) A)).toAlgebra
  have : IsScalarTower (MvPolynomial (Fin m) k) A F := by
    refine ⟨fun p a x ↦ ?_⟩
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul, Ideal.Quotient.mk_eq_mk,
      smul_eq_mul, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul, map_mul,
      mul_assoc]
    rfl
  have : IsScalarTower k (MvPolynomial (Fin m) k) F :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      change algebraMap k F a = algebraMap A F (algebraMap (MvPolynomial (Fin m) k) A
        (algebraMap k _ a))
      rw [← IsScalarTower.algebraMap_apply k (MvPolynomial (Fin m) k) A,
        ← IsScalarTower.algebraMap_apply k A F]
  have halg : ∀ p : MvPolynomial (Fin m) k, algebraMap (MvPolynomial (Fin m) k) F p = aeval y p
    := by
    intro p
    have : (IsScalarTower.toAlgHom k (MvPolynomial (Fin m) k) F) = aeval y := by
      apply MvPolynomial.algHom_ext
      intro i
      rw [IsScalarTower.coe_toAlgHom', aeval_X]
      rfl
    exact (AlgHom.congr_fun this p)
  -- The tangent vector as a derivation `P → F`.
  let DP : Derivation k (MvPolynomial (Fin m) k) F := mkDerivation k v
  have hDP : ∀ f, DP f = ∑ i, aeval y (pderiv i f) * v i :=
    mkDerivation_eq_sum_pderiv y v halg
  have hDPI : ∀ f ∈ I, DP f = 0 := by
    intro f hf
    rw [hDP]
    have hmem : MvPolynomial.map (algebraMap k F) f ∈ extendedIdeal I F :=
      Ideal.mem_map_of_mem _ hf
    have := htan _ hmem
    convert this using 2 with i
    rw [differentialAt, pderiv_map, eval_map, aeval_def]
  -- Descend to `A`.
  let DA : Derivation k A F := quotientDerivation DP hDPI
  have hDA : ∀ i, DA (Ideal.Quotient.mk I (X i)) = v i := by
    intro i
    rw [quotientDerivation_mk]
    exact mkDerivation_X k v i
  -- Lift through Kähler differentials of `A`.
  let ψ : Ω[A⁄k] →ₗ[A] F := DA.liftKaehlerDifferential
  -- Extend through the localization `Ω[A⁄k] → Ω[F⁄k]`.
  let φ : Ω[F⁄k] →ₗ[A] F :=
    IsLocalizedModule.lift (nonZeroDivisors A) (KaehlerDifferential.map k k A F) ψ
      isUnit_algebraMap_end
  have hφ : ∀ i, φ (KaehlerDifferential.D k F (y i)) = v i := by
    intro i
    have hyi : y i = algebraMap A F (Ideal.Quotient.mk I (X i)) := rfl
    rw [hyi, ← KaehlerDifferential.map_D k k A F, IsLocalizedModule.lift_apply]
    change DA.liftKaehlerDifferential (KaehlerDifferential.D k A _) = _
    rw [Derivation.liftKaehlerDifferential_comp_D, hDA]
  let Φ : Ω[F⁄k] →ₗ[F] F := LinearMap.extendScalarsOfIsLocalization (nonZeroDivisors A) F φ
  have hΦ := congrArg Φ h
  rw [map_sum, map_zero] at hΦ
  simp only [map_smul, LinearMap.extendScalarsOfIsLocalization_apply', Φ, hφ, smul_eq_mul] at hΦ
  simpa using hΦ

end Main

end

end Stafford38.Geometry.GenericPointKaehlerConormal
