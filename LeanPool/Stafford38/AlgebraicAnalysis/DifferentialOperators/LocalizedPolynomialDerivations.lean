/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Derivation.Basic

/-!
# Derivations through localizations

The differentials of a localization are obtained by formally-etale base
change.  This file records the resulting extension operation and its
specialization to the partial derivations of a polynomial ring.
-/

namespace AlgebraicAnalysis.DifferentialOperators.LocalizedPolynomialDerivations

open TensorProduct

noncomputable section

universe u

variable (k A B : Type u)
variable [CommRing k] [CommRing A] [CommRing B]
variable [Algebra k A] [Algebra k B] [Algebra A B]
variable [IsScalarTower k A B]

/-- Extend a `k`-derivation through a localization `A → B`, by the
formally-etale base-change equivalence for Kähler differentials. -/
noncomputable def extendDerivation
    (S : Submonoid A) [IsLocalization S B]
    (D : Derivation k A B) : Derivation k B B := by
  letI : Algebra.FormallyEtale A B :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := B) S
  let base : B ⊗[A] KaehlerDifferential k A →ₗ[B] B :=
    D.liftKaehlerDifferential.liftBaseChange B
  let pull : KaehlerDifferential k B →ₗ[B] B :=
    base.comp
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale
        k A B).symm.toLinearMap
  exact KaehlerDifferential.linearMapEquivDerivation k B pull

@[simp]
theorem extendDerivation_compAlgebraMap
    (S : Submonoid A) [IsLocalization S B]
    (D : Derivation k A B) :
    (extendDerivation k A B S D).compAlgebraMap A = D := by
  let : Algebra.FormallyEtale A B :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := B) S
  apply Derivation.ext
  intro a
  simp [extendDerivation,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    Derivation.liftKaehlerDifferential_comp_D]

/-- A derivation of a localization is uniquely determined by its restriction
to the original algebra. -/
theorem derivation_ext_of_compAlgebraMap_eq
    (S : Submonoid A) [IsLocalization S B]
    {D₁ D₂ : Derivation k B B}
    (h : D₁.compAlgebraMap A = D₂.compAlgebraMap A) :
    D₁ = D₂ := by
  let : Algebra.FormallyEtale A B :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := B) S
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k A B
  have hbase :
      (D₁.liftKaehlerDifferential.restrictScalars A).comp
          (KaehlerDifferential.map k k A B) =
        (D₂.liftKaehlerDifferential.restrictScalars A).comp
          (KaehlerDifferential.map k k A B) := by
    apply Derivation.liftKaehlerDifferential_unique
    apply Derivation.ext
    intro x
    simpa [KaehlerDifferential.map_D,
      Derivation.liftKaehlerDifferential_comp_D] using
      Derivation.congr_fun h x
  have hpull :
      D₁.liftKaehlerDifferential.comp e.toLinearMap =
        D₂.liftKaehlerDifferential.comp e.toLinearMap := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a x =>
        simp only [e,
          KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
          KaehlerDifferential.mapBaseChange_tmul,
          LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.map_smul]
        exact congrArg (a • ·) (LinearMap.congr_fun hbase x)
  apply Derivation.ext
  intro x
  have hmaps : D₁.liftKaehlerDifferential = D₂.liftKaehlerDifferential := by
    apply LinearMap.ext
    intro w
    obtain ⟨z, rfl⟩ := e.surjective w
    exact LinearMap.congr_fun hpull z
  simpa [Derivation.liftKaehlerDifferential_comp_D] using
    LinearMap.congr_fun hmaps (KaehlerDifferential.D k B x)

/-- The commutator is constructed directly because the localization argument only needs
its derivation rule, not the surrounding Lie-algebra structure. -/
private def derivationCommutator (D E : Derivation k B B) : Derivation k B B :=
  Derivation.mk' (D.toLinearMap.comp E.toLinearMap - E.toLinearMap.comp D.toLinearMap)
    fun a b ↦ by
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, Derivation.coeFn_coe,
        Derivation.leibniz, map_add, smul_eq_mul]
      ring

section Polynomial

variable {k : Type u} {n : ℕ} [Field k]

/-- The polynomial ring in `n` coordinate variables over `k`. -/
abbrev PolynomialRing := MvPolynomial (Fin n) k

private theorem pderiv_comm (i j : Fin n) (f : MvPolynomial (Fin n) k) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j f) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p l hp =>
      by_cases hij : i = j
      · subst j
        simp [ mul_comm]
      · by_cases hil : i = l
        · subst l
          by_cases hjl : j = i
          · exact False.elim (hij hjl.symm)
          · simp [hp, hij, mul_comm]; ring
        · by_cases hjl : j = l
          · subst l
            simp [hp, hil, mul_comm]; ring
          · simp [hp, hil, hjl, mul_comm]

/-- The `i`th polynomial partial derivative, transported to a localization. -/
noncomputable def localizedPderiv
    (S : Submonoid (PolynomialRing (k := k) (n := n)))
    (B : Type u) [CommRing B]
    [Algebra (PolynomialRing (k := k) (n := n)) B]
    [Algebra k B]
    [IsScalarTower k (PolynomialRing (k := k) (n := n)) B]
    [IsLocalization S B] (i : Fin n) : Derivation k B B :=
  extendDerivation k _ B S
    ((Algebra.linearMap _ B).compDer (MvPolynomial.pderiv i))

@[simp]
theorem localizedPderiv_compAlgebraMap
    (S : Submonoid (PolynomialRing (k := k) (n := n)))
    (B : Type u) [CommRing B]
    [Algebra (PolynomialRing (k := k) (n := n)) B]
    [Algebra k B]
    [IsScalarTower k (PolynomialRing (k := k) (n := n)) B]
    [IsLocalization S B] (i : Fin n) :
    (localizedPderiv S B i).compAlgebraMap _ =
      (Algebra.linearMap _ B).compDer (MvPolynomial.pderiv i) := by
  exact extendDerivation_compAlgebraMap k _ B S _

theorem localizedPderiv_apply_algebraMap_X
    (S : Submonoid (PolynomialRing (k := k) (n := n)))
    (B : Type u) [CommRing B]
    [Algebra (PolynomialRing (k := k) (n := n)) B]
    [Algebra k B]
    [IsScalarTower k (PolynomialRing (k := k) (n := n)) B]
    [IsLocalization S B] (i j : Fin n) :
    localizedPderiv S B i
        (algebraMap (PolynomialRing (k := k) (n := n)) B
          (MvPolynomial.X j : PolynomialRing (k := k) (n := n))) =
      if i = j then 1 else 0 := by
  rw [show algebraMap _ B (MvPolynomial.X j) =
      (IsScalarTower.toAlgHom k _ B) (MvPolynomial.X j) by rfl]
  have h := Derivation.congr_fun
    (localizedPderiv_compAlgebraMap (k := k) S B i)
    (MvPolynomial.X j)
  change localizedPderiv S B i (algebraMap _ B (MvPolynomial.X j)) = _ at h
  simpa [MvPolynomial.pderiv_X, Pi.single_apply, eq_comm] using h

theorem localizedPderiv_comm
    (S : Submonoid (PolynomialRing (k := k) (n := n)))
    (B : Type u) [CommRing B]
    [Algebra (PolynomialRing (k := k) (n := n)) B]
    [Algebra k B]
    [IsScalarTower k (PolynomialRing (k := k) (n := n)) B]
    [IsLocalization S B] (i j : Fin n) :
    (localizedPderiv S B i).toLinearMap.comp
        (localizedPderiv S B j).toLinearMap =
      (localizedPderiv S B j).toLinearMap.comp
        (localizedPderiv S B i).toLinearMap := by
  have hcomm : derivationCommutator k B (localizedPderiv S B i) (localizedPderiv S B j) = 0 := by
    apply derivation_ext_of_compAlgebraMap_eq k _ B S
    apply Derivation.ext
    intro f
    change localizedPderiv S B i (localizedPderiv S B j
      (algebraMap _ B f)) - localizedPderiv S B j (localizedPderiv S B i
      (algebraMap _ B f)) = 0
    have hi := Derivation.congr_fun
      (localizedPderiv_compAlgebraMap (k := k) S B i) f
    have hj := Derivation.congr_fun
      (localizedPderiv_compAlgebraMap (k := k) S B j) f
    change localizedPderiv S B i (algebraMap _ B f) = _ at hi
    change localizedPderiv S B j (algebraMap _ B f) = _ at hj
    change localizedPderiv S B i (algebraMap _ B f) =
      algebraMap _ B (MvPolynomial.pderiv i f) at hi
    change localizedPderiv S B j (algebraMap _ B f) =
      algebraMap _ B (MvPolynomial.pderiv j f) at hj
    rw [hj, hi]
    have hij := Derivation.congr_fun
      (localizedPderiv_compAlgebraMap (k := k) S B i)
      (MvPolynomial.pderiv j f)
    have hji := Derivation.congr_fun
      (localizedPderiv_compAlgebraMap (k := k) S B j)
      (MvPolynomial.pderiv i f)
    change localizedPderiv S B i
      (algebraMap _ B (MvPolynomial.pderiv j f)) = _ at hij
    change localizedPderiv S B j
      (algebraMap _ B (MvPolynomial.pderiv i f)) = _ at hji
    change localizedPderiv S B i
      (algebraMap _ B (MvPolynomial.pderiv j f)) =
        algebraMap _ B (MvPolynomial.pderiv i (MvPolynomial.pderiv j f)) at hij
    change localizedPderiv S B j
      (algebraMap _ B (MvPolynomial.pderiv i f)) =
        algebraMap _ B (MvPolynomial.pderiv j (MvPolynomial.pderiv i f)) at hji
    rw [hij, hji]
    rw [pderiv_comm i j f]
    simp
  apply LinearMap.ext
  intro x
  have hx := congrArg (fun d : Derivation k B B => d x) hcomm
  exact sub_eq_zero.mp (by simpa [derivationCommutator, LinearMap.comp_apply] using hx)

end Polynomial

end
end AlgebraicAnalysis.DifferentialOperators.LocalizedPolynomialDerivations
