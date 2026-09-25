/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Henselian -/

@[expose] public section
namespace ValuationTheory

/-!
# Henselian discretely valued fields

This file contains the lightweight package for a discretely valued field whose
valuation ring is Henselian at its maximal ideal.
-/

noncomputable section

universe u v

namespace DiscreteValuationField

/-- The idempotent polynomial `X^2 - X` is monic in every nontrivial
coefficient ring. -/
theorem idempotentPolynomial_monic
    {R : Type*} [CommRing R] [Nontrivial R] :
    (Polynomial.X ^ 2 - Polynomial.X : Polynomial R).Monic := by
  exact Polynomial.monic_X_pow_sub (by
    rw [Polynomial.degree_X]
    norm_num)

/-- A quotient idempotent is an approximate root of `X^2 - X`. -/
theorem idempotentPolynomial_eval_mem_of_quotient_idempotent
    {R : Type*} [CommRing R] {I : Ideal R} (a0 : R)
    (ha0 : IsIdempotentElem (Ideal.Quotient.mk I a0)) :
    (Polynomial.X ^ 2 - Polynomial.X : Polynomial R).eval a0 ∈ I := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change
    Ideal.Quotient.mk I
      ((Polynomial.X ^ 2 - Polynomial.X : Polynomial R).eval a0) = 0
  simpa [pow_two] using sub_eq_zero.mpr ha0.eq

/-- At a quotient idempotent, the derivative of `X^2 - X` is a unit in the
quotient. -/
theorem idempotentPolynomial_derivative_eval_isUnit_of_quotient_idempotent
    {R : Type*} [CommRing R] {I : Ideal R} (a0 : R)
    (ha0 : IsIdempotentElem (Ideal.Quotient.mk I a0)) :
    IsUnit
      (Ideal.Quotient.mk I
        ((Polynomial.X ^ 2 - Polynomial.X : Polynomial R).derivative.eval a0)) := by
  rw [isUnit_iff_exists]
  refine
    ⟨Ideal.Quotient.mk I
      ((Polynomial.X ^ 2 - Polynomial.X : Polynomial R).derivative.eval a0),
      ?_, ?_⟩
  · simp only [pow_two, Polynomial.derivative_mul, Polynomial.derivative_X, one_mul, mul_one,
      Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one, map_sub,
      map_add, map_one]
    calc
      (Ideal.Quotient.mk I a0 + Ideal.Quotient.mk I a0 - 1) *
          (Ideal.Quotient.mk I a0 + Ideal.Quotient.mk I a0 - 1) =
        1 + (4 * (Ideal.Quotient.mk I a0 * Ideal.Quotient.mk I a0) -
          4 * Ideal.Quotient.mk I a0) := by
          ring
      _ = 1 := by
          rw [ha0.eq]
          ring
  · simp only [pow_two, Polynomial.derivative_mul, Polynomial.derivative_X, one_mul, mul_one,
      Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one, map_sub,
      map_add, map_one]
    calc
      (Ideal.Quotient.mk I a0 + Ideal.Quotient.mk I a0 - 1) *
          (Ideal.Quotient.mk I a0 + Ideal.Quotient.mk I a0 - 1) =
        1 + (4 * (Ideal.Quotient.mk I a0 * Ideal.Quotient.mk I a0) -
          4 * Ideal.Quotient.mk I a0) := by
          ring
      _ = 1 := by
          rw [ha0.eq]
          ring

/-- Idempotents lift along a surjective ring map whose kernel is a Henselian
ideal.

This is the `X^2 - X` simple-root form of Hensel's lemma.  At an idempotent,
the derivative `2X - 1` is a unit because its square is `1`. -/
theorem exists_idempotent_lift_of_surjective_henselianRing_ker
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f)
    [HenselianRing R (RingHom.ker f)]
    (e : S) (he : IsIdempotentElem e) :
    ∃ e' : R, IsIdempotentElem e' ∧ f e' = e := by
  cases subsingleton_or_nontrivial R with
  | inl hR =>
      have hS : Subsingleton S := by
        constructor
        intro x y
        rcases hf x with ⟨a, rfl⟩
        rcases hf y with ⟨b, rfl⟩
        exact congrArg f (Subsingleton.elim a b)
      exact ⟨0, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  | inr hR =>
      let : Nontrivial R := hR
      rcases hf e with ⟨a0, ha0⟩
      let p : Polynomial R := Polynomial.X ^ 2 - Polynomial.X
      have hpmonic : p.Monic := by
        dsimp [p]
        exact idempotentPolynomial_monic
      have ha0_quotient :
          IsIdempotentElem
            (Ideal.Quotient.mk (RingHom.ker f) a0) := by
        rw [IsIdempotentElem]
        rw [← map_mul, Ideal.Quotient.eq]
        rw [RingHom.mem_ker]
        simp [ha0, he.eq]
      have hroot : p.eval a0 ∈ RingHom.ker f := by
        simpa [p] using
          idempotentPolynomial_eval_mem_of_quotient_idempotent
            (I := RingHom.ker f) a0 ha0_quotient
      have hsimple :
          IsUnit
            (Ideal.Quotient.mk (RingHom.ker f) (p.derivative.eval a0)) := by
        simpa [p] using
          idempotentPolynomial_derivative_eval_isUnit_of_quotient_idempotent
            (I := RingHom.ker f) a0 ha0_quotient
      rcases HenselianRing.is_henselian p hpmonic a0 hroot hsimple with
        ⟨a, haroot, hacongr⟩
      refine ⟨a, ?_, ?_⟩
      · change a * a = a
        exact sub_eq_zero.mp (by simpa [p, pow_two] using haroot)
      · have hsub : f (a - a0) = 0 := RingHom.mem_ker.mp hacongr
        rw [map_sub, ha0, sub_eq_zero] at hsub
        exact hsub

/-- Chosen-representative form of idempotent lifting for Henselian pairs. -/
theorem exists_idempotent_lift_of_henselianRing_mk
    {R : Type*} [CommRing R] {I : Ideal R} [HenselianRing R I]
    (a0 : R) (ha0 : IsIdempotentElem (Ideal.Quotient.mk I a0)) :
    ∃ e : R,
      IsIdempotentElem e ∧
        Ideal.Quotient.mk I e = Ideal.Quotient.mk I a0 ∧
        e - a0 ∈ I := by
  cases subsingleton_or_nontrivial R with
  | inl hR =>
      have ha0zero : a0 = 0 := Subsingleton.elim _ _
      refine ⟨0, ?_, ?_, ?_⟩
      · rw [IsIdempotentElem]
        simp
      · simp [ha0zero]
      · simp [ha0zero]
  | inr hR =>
      let : Nontrivial R := hR
      let p : Polynomial R := Polynomial.X ^ 2 - Polynomial.X
      have hpmonic : p.Monic := by
        dsimp [p]
        exact idempotentPolynomial_monic
      have hroot : p.eval a0 ∈ I := by
        simpa [p] using
          idempotentPolynomial_eval_mem_of_quotient_idempotent
            (I := I) a0 ha0
      have hsimple :
          IsUnit
            (Ideal.Quotient.mk I (p.derivative.eval a0)) := by
        simpa [p] using
          idempotentPolynomial_derivative_eval_isUnit_of_quotient_idempotent
            (I := I) a0 ha0
      rcases HenselianRing.is_henselian p hpmonic a0 hroot hsimple with
        ⟨e, heroot, hecongr⟩
      refine ⟨e, ?_, ?_, hecongr⟩
      · change e * e = e
        exact sub_eq_zero.mp (by simpa [p, pow_two] using heroot)
      · rw [Ideal.Quotient.eq]
        exact hecongr

/-- Quotient form of idempotent lifting for Henselian pairs: every idempotent
modulo the Henselian ideal has an idempotent representative. -/
theorem exists_idempotent_lift_of_henselianRing
    {R : Type*} [CommRing R] {I : Ideal R} [HenselianRing R I]
    (e : R ⧸ I) (he : IsIdempotentElem e) :
    ∃ e' : R, IsIdempotentElem e' ∧ Ideal.Quotient.mk I e' = e := by
  rcases Ideal.Quotient.mk_surjective e with ⟨a0, rfl⟩
  rcases exists_idempotent_lift_of_henselianRing_mk
      (I := I) a0 he with
    ⟨e', he', hqe', _⟩
  exact ⟨e', he', hqe'⟩

/-- A Henselian discretely valued field. -/
structure HenselianDVF (K : Type u) [Field K] extends DVF.{u, v} K where
  /-- The valuation ring is Henselian along its maximal ideal. -/
  [instHenselian : HenselianRing toDVF.valuationSubring toDVF.maximalIdeal]

attribute [instance] HenselianDVF.instHenselian

namespace HenselianDVF

variable {K : Type u} [Field K]

/-- Introduces the abbreviation `valuationSubring`. -/
abbrev valuationSubring (F : HenselianDVF.{u, v} K) : Type u :=
  F.toDVF.valuationSubring

/-- Introduces the abbreviation `maximalIdeal`. -/
abbrev maximalIdeal (F : HenselianDVF.{u, v} K) : Ideal F.valuationSubring :=
  F.toDVF.maximalIdeal

/-- Introduces the abbreviation `residueField`. -/
abbrev residueField (F : HenselianDVF.{u, v} K) : Type u :=
  F.toDVF.residueField

/-- Introduces the abbreviation `residueMap`. -/
abbrev residueMap (F : HenselianDVF.{u, v} K) :
    RingHom F.valuationSubring F.residueField :=
  F.toDVF.residueMap

/-- Every residue-field polynomial admits a coefficientwise lift to the
valuation ring. -/
theorem exists_polynomial_lift_residue (F : HenselianDVF.{u, v} K)
    (fbar : Polynomial F.residueField) :
    ∃ f : Polynomial F.valuationSubring, f.map F.residueMap = fbar := by
  classical
  choose c hc using fun n : ℕ => F.toDVF.residue_surjective (fbar.coeff n)
  let f : Polynomial F.valuationSubring :=
    fbar.support.sum fun n => Polynomial.monomial n (c n)
  refine ⟨f, ?_⟩
  ext n
  by_cases hn : n ∈ fbar.support
  · simp only [Polynomial.coeff_map, Polynomial.finsetSum_coeff, map_sum, f]
    rw [Finset.sum_eq_single n]
    · simp [hc]
    · intro b hb hbn
      simp [Polynomial.coeff_monomial, hbn]
    · intro hnot
      exact False.elim (hnot hn)
  · have hcoeff : fbar.coeff n = 0 := by
      simpa [Polynomial.mem_support_iff] using hn
    simp only [Polynomial.coeff_map, Polynomial.finsetSum_coeff, map_sum, hcoeff, f]
    refine Finset.sum_eq_zero ?_
    intro b hb
    have hbn : n ≠ b := by
      intro h
      exact hn (by simpa [h] using hb)
    simp [Polynomial.coeff_monomial, hbn.symm]

/-- The valuation subring of the henselian model is a discrete valuation ring. -/
theorem valuationSubring_isDiscreteValuationRing (F : HenselianDVF.{u, v} K) :
    IsDiscreteValuationRing F.valuationSubring :=
  F.toDVF.valuationSubring_isDiscreteValuationRing

/-- The valuation subring of the henselian discrete valuation field is henselian. -/
theorem henselianRing (F : HenselianDVF.{u, v} K) :
    HenselianRing F.valuationSubring F.maximalIdeal := by
  change HenselianRing F.toDVF.valuationSubring F.toDVF.maximalIdeal
  infer_instance

/-- The maximal ideal of a Henselian DVF valuation ring is nonzero. -/
theorem maximalIdeal_ne_bot (F : HenselianDVF.{u, v} K) :
    F.maximalIdeal ≠ ⊥ :=
  F.toDVF.maximalIdeal_ne_bot

/-- Hensel's lemma in the simple-root form used by mathlib. -/
theorem exists_lift_root_simple (F : HenselianDVF.{u, v} K)
    (f : Polynomial F.valuationSubring) (hf : f.Monic) (a0 : F.valuationSubring)
    (hroot : f.eval a0 ∈ F.maximalIdeal)
    (hsimple : IsUnit (Ideal.Quotient.mk F.maximalIdeal (f.derivative.eval a0))) :
    ∃ a : F.valuationSubring, f.IsRoot a ∧ a - a0 ∈ F.maximalIdeal :=
  HenselianRing.is_henselian f hf a0 hroot hsimple

end HenselianDVF

end DiscreteValuationField

end

end ValuationTheory
