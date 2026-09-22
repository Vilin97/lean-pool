/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.TraceCurve.Localization

/-!
# Normal forms in the split trace-cover Kummer tower

The full kernel calculation for the Laurent trace-cover map requires reducing arbitrary Laurent
polynomials to a bounded monomial normal form.  This file proves the risky uniqueness half of that
calculation: the bounded `eta`--`xi` monomials are linearly independent over the quadratic base
function ring, so no nontrivial reduced normal form can vanish in the iterated Kummer algebra.

This basis statement only uses that the two defining binomials are monic.  Irreducibility, proved
in `TraceCurveKummer`, is needed later to regard the same rings as fields, but is not smuggled into
the normal-form interface.
-/

namespace BGS.Markoff

open Polynomial

noncomputable section

/-- Iterating two monic `AdjoinRoot` constructions gives a linearly independent rectangular
family of powers.  This generic lemma keeps the typeclass structures fixed before the concrete
Kummer polynomials are substituted. -/
theorem adjoinRootTower_normalMonomials_linearIndependent
    {R : Type*} [CommRing R] (f : R[X]) (hf : f.Monic)
    (g : Polynomial (AdjoinRoot f)) (hg : g.Monic) :
    @LinearIndependent (Fin f.natDegree × Fin g.natDegree) R (AdjoinRoot g)
      (fun ji : Fin f.natDegree × Fin g.natDegree ↦
        algebraMap (AdjoinRoot f) (AdjoinRoot g)
            (AdjoinRoot.root f ^ (ji.1 : ℕ)) *
          AdjoinRoot.root g ^ (ji.2 : ℕ))
      _ (AdjoinRoot.instCommRing g).toAddCommMonoid _ := by
  have hFirst := (AdjoinRoot.powerBasis' hf).basis.linearIndependent
  have hSecond := (AdjoinRoot.powerBasis' hg).basis.linearIndependent
  have hProduct := linearIndependent_smul hFirst hSecond
  change LinearIndependent R
    (fun p : Fin f.natDegree × Fin g.natDegree ↦
      (AdjoinRoot.powerBasis' hf).basis p.1 •
        (AdjoinRoot.powerBasis' hg).basis p.2) at hProduct
  simpa [PowerBasis.basis_eq_pow, Algebra.smul_def] using hProduct

variable {K : Type*} [Field K]

lemma splitTraceEtaKummerPolynomial_monic
    (sigma : K) (e : ℕ) (he : e ≠ 0) :
    (splitTraceEtaKummerPolynomial sigma e).Monic := by
  rw [splitTraceEtaKummerPolynomial]
  exact monic_X_pow_sub_C _ he

lemma splitTraceXiKummerPolynomial_monic
    (sigma : K) (e d : ℕ) (hd : d ≠ 0) :
    (splitTraceXiKummerPolynomial sigma e d).Monic := by
  rw [splitTraceXiKummerPolynomial]
  exact monic_X_pow_sub_C _ hd

/-- A bounded `eta`--`xi` normal form has unique coefficients over the base function ring.
Equivalently, its linear-combination evaluation map into the Kummer top algebra is injective. -/
theorem splitTraceEtaXiNormalMonomials_linearIndependent
    (sigma : K) (e d : ℕ) (he : e ≠ 0) (hd : d ≠ 0) :
    letI : CommRing (AdjoinRoot (splitTraceBaseKummerPolynomial sigma)) :=
      AdjoinRoot.instCommRing _
    letI : CommRing (AdjoinRoot (splitTraceEtaKummerPolynomial sigma e)) :=
      AdjoinRoot.instCommRing _
    letI : CommRing (AdjoinRoot (splitTraceXiKummerPolynomial sigma e d)) :=
      AdjoinRoot.instCommRing _
    LinearIndependent (AdjoinRoot (splitTraceBaseKummerPolynomial sigma))
      (fun ji : Fin (splitTraceEtaKummerPolynomial sigma e).natDegree ×
          Fin (splitTraceXiKummerPolynomial sigma e d).natDegree ↦
        splitTraceEtaRootInXiField sigma e d ^ (ji.1 : ℕ) *
          splitTraceXiRoot sigma e d ^ (ji.2 : ℕ)) := by
  let : CommRing (AdjoinRoot (splitTraceBaseKummerPolynomial sigma)) :=
    AdjoinRoot.instCommRing _
  let : CommRing (AdjoinRoot (splitTraceEtaKummerPolynomial sigma e)) :=
    AdjoinRoot.instCommRing _
  let : CommRing (AdjoinRoot (splitTraceXiKummerPolynomial sigma e d)) :=
    AdjoinRoot.instCommRing _
  simpa [splitTraceEtaRootInXiField, splitTraceXiRoot] using
    adjoinRootTower_normalMonomials_linearIndependent
      (splitTraceEtaKummerPolynomial sigma e)
      (splitTraceEtaKummerPolynomial_monic sigma e he)
      (splitTraceXiKummerPolynomial sigma e d)
      (splitTraceXiKummerPolynomial_monic sigma e d hd)

/-- In the odd-coprime situation used by the endgame, oddness supplies the required positive
exponents for the bounded normal-form theorem. -/
theorem splitTraceEtaXiNormalMonomials_linearIndependent_of_oddCoprime
    (sigma : K) (e d : ℕ) (heOdd : Odd e) (hdOdd : Odd d) (_hde : d.Coprime e) :
    letI : CommRing (AdjoinRoot (splitTraceBaseKummerPolynomial sigma)) :=
      AdjoinRoot.instCommRing _
    letI : CommRing (AdjoinRoot (splitTraceEtaKummerPolynomial sigma e)) :=
      AdjoinRoot.instCommRing _
    letI : CommRing (AdjoinRoot (splitTraceXiKummerPolynomial sigma e d)) :=
      AdjoinRoot.instCommRing _
    LinearIndependent (AdjoinRoot (splitTraceBaseKummerPolynomial sigma))
      (fun ji : Fin (splitTraceEtaKummerPolynomial sigma e).natDegree ×
          Fin (splitTraceXiKummerPolynomial sigma e d).natDegree ↦
        splitTraceEtaRootInXiField sigma e d ^ (ji.1 : ℕ) *
          splitTraceXiRoot sigma e d ^ (ji.2 : ℕ)) := by
  let : CommRing (AdjoinRoot (splitTraceBaseKummerPolynomial sigma)) :=
    AdjoinRoot.instCommRing _
  let : CommRing (AdjoinRoot (splitTraceEtaKummerPolynomial sigma e)) :=
    AdjoinRoot.instCommRing _
  let : CommRing (AdjoinRoot (splitTraceXiKummerPolynomial sigma e d)) :=
    AdjoinRoot.instCommRing _
  have he : e ≠ 0 := by
    rintro rfl
    simp at heOdd
  have hd : d ≠ 0 := by
    rintro rfl
    simp at hdOdd
  exact splitTraceEtaXiNormalMonomials_linearIndependent sigma e d he hd

/-- In the odd-coprime endgame range, a reduced rectangular normal form evaluates to zero in the
Kummer top algebra exactly when every coefficient is zero.  This is the concrete kernel statement
available before the separate existence-of-normal-form reduction for Laurent polynomials. -/
theorem splitTraceEtaXiNormalForm_evaluation_eq_zero_iff
    (sigma : K) (e d : ℕ) (heOdd : Odd e) (hdOdd : Odd d) (hde : d.Coprime e)
    (c : (Fin (splitTraceEtaKummerPolynomial sigma e).natDegree ×
      Fin (splitTraceXiKummerPolynomial sigma e d).natDegree) →₀
        AdjoinRoot (splitTraceBaseKummerPolynomial sigma)) :
    letI : CommRing (AdjoinRoot (splitTraceBaseKummerPolynomial sigma)) :=
      AdjoinRoot.instCommRing _
    letI : CommRing (AdjoinRoot (splitTraceEtaKummerPolynomial sigma e)) :=
      AdjoinRoot.instCommRing _
    letI : CommRing (AdjoinRoot (splitTraceXiKummerPolynomial sigma e d)) :=
      AdjoinRoot.instCommRing _
    Finsupp.linearCombination (AdjoinRoot (splitTraceBaseKummerPolynomial sigma))
        (fun ji : Fin (splitTraceEtaKummerPolynomial sigma e).natDegree ×
            Fin (splitTraceXiKummerPolynomial sigma e d).natDegree ↦
          splitTraceEtaRootInXiField sigma e d ^ (ji.1 : ℕ) *
            splitTraceXiRoot sigma e d ^ (ji.2 : ℕ)) c = 0 ↔
      c = 0 := by
  let : CommRing (AdjoinRoot (splitTraceBaseKummerPolynomial sigma)) :=
    AdjoinRoot.instCommRing _
  let : CommRing (AdjoinRoot (splitTraceEtaKummerPolynomial sigma e)) :=
    AdjoinRoot.instCommRing _
  let : CommRing (AdjoinRoot (splitTraceXiKummerPolynomial sigma e d)) :=
    AdjoinRoot.instCommRing _
  constructor
  · intro hc
    apply splitTraceEtaXiNormalMonomials_linearIndependent_of_oddCoprime
      sigma e d heOdd hdOdd hde
    simpa using hc
  · rintro rfl
    simp

end

end BGS.Markoff
