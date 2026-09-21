/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module


import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.OmnificInteger.Primality.IrreducibleOmnificIntegers
public import LeanPool.ConwayRefinement.ConwayRefinement.Examples.OmnificInteger.DegreeTwoNormalForm

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.DegreeTwo.DegreeTwoExample
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.CharZero
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.NonpositiveCoefficientMap
import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.Degree
import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.ArchimedeanAssumptions
import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.HahnSeries.DegreeTransfer
import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.HahnSeries.IntegerPart
import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.HahnSeries.RealLeadingSplit

/-!
# An explicit degree-two prime in the omnific integers

The PS06 construction supplies a generalised power series of support order type `ω ^ 2 + 1`
whose three independent translated-truncation classes modulo `J + K` prevent a nontrivial
factorisation,
over every field of characteristic zero. The omnific integer `ofRealSeries` of its real form has
this series as its signed Conway normal form. Irreducibility over the infinitesimal Hahn field
transfers to the omnific integer by the residue-one case of LM24, Proposition 8.3.6(5).
Every irreducible series and every irreducible omnific integer is prime. Everything is proved in
the model of Conway's `Oz` inside the surreal numbers of an arbitrary universe `u`.

## References

* J. Pommersheim, S. Shahriari, *Unique factorization in generalized power series rings*,
Proc. Amer. Math. Soc. 134 (2006), 1277–1287, cited as [PS06].
* S. L'Innocente, V. Mantova, *A factorisation theory for generalised power series and omnific
  integers*, Adv. Math. 442 (2024) 109513, cited as [LM24].
-/

open scoped HahnSeries

universe u

noncomputable section

namespace Surreal.OmnificInteger.DegreeTwoExample

open HahnSeries.Nonpositive PommersheimShahriari.DegreeTwoExample

private theorem degreeTwoWithConstant_ne_zero : degreeTwoWithConstant (K := ℝ) ≠ 0 := by
  intro hzero
  have hcoeff := degreeTwoWithConstant_coeff_zero (K := ℝ)
  rw [hzero] at hcoeff
  norm_num at hcoeff

private theorem degreeTwoWithConstant_constantCoeff_mem :
    constantCoeff (degreeTwoWithConstant (K := ℝ)) ∈ Surreal.realIntegerSubring := by
  rw [degreeTwoWithConstant_constantCoeff]
  exact Surreal.realIntegerSubring.one_mem

/-- The signed degree-two series has negative order: its exponent `q₀,₀` carries coefficient one
and is negative. -/
theorem signedDegreeTwo_order_neg :
    (mapRealDomainToSurreal (degreeTwoWithConstant (K := ℝ)) : ℝ⟦Surreal.{u}⟧).order < 0 := by
  have hcoeff : (mapRealDomainToSurreal (degreeTwoWithConstant (K := ℝ)) :
      ℝ⟦Surreal.{u}⟧).coeff ((degreeTwoExponentPair (0, 0) : ℝ) : Surreal) ≠ 0 := by
    have h := degreeTwoWithConstant_coeff_embedding (K := ℝ) 0 0
    rw [degreeTwoExponentEmbedding_apply] at h
    rw [mapRealDomainToSurreal_coeff_real, h]
    exact one_ne_zero
  refine (HahnSeries.order_le_of_coeff_ne_zero hcoeff).trans_lt ?_
  norm_num [degreeTwoExponentPair_apply]

theorem signedDegreeTwo_order_ne_zero :
    (mapRealDomainToSurreal (degreeTwoWithConstant (K := ℝ)) : ℝ⟦Surreal.{u}⟧).order ≠ 0 :=
  signedDegreeTwo_order_neg.ne

private theorem degreeTwoExponentPair_eq_neg_exponent (m n : ℕ) :
    degreeTwoExponentPair (m, n) =
      -DegreeTwoExample.exponent m n := by
  rw [degreeTwoExponentPair_apply,
    DegreeTwoExample.exponent_apply]
  ring

public section

/-- The explicit PS06 series is prime over every characteristic-zero coefficient field. -/
@[blueprint "thm:degree-two-series-prime"
  (phase := "Surreal numbers and omnific integers")
  (title := "Primality of an explicit degree-two series")
  (statement := /--
    Let $K$ be a field of characteristic $0$.  The series
    \[
      1+\sum_{m,n\in\mathbb N}
      t^{-\frac{1}{m+1}-\frac{1}{(m+1)(m+2)(n+1)}}
    \]
    is prime in $K((\mathbb R^{\le 0}))$.
  -/)
  (proof := /--
  The nonconstant support consists of $\omega$ successive blocks of order type
  $\omega$ and accumulates at $0$; adjoining the constant term gives support
  order type $\omega^2+1$.  Three translated-truncation classes from distinct
  blocks are linearly independent modulo $J+K$, so their span has dimension
  greater than $2$.  Hence \ref{fact:ps06-irreducibility} makes the displayed
  series irreducible.  It is prime by
  \ref{cor:hahn-series-irreducible-is-prime}.
  -/)]
theorem degreeTwoWithConstant_prime {K : Type*} [Field K] [CharZero K] :
    Prime (degreeTwoWithConstant (K := K)) :=
  Berarducci.prime_of_irreducible degreeTwoWithConstant_irreducible

/-- The explicit degree-two omnific integer obtained from the PS06 series with three independent
classes modulo `J`. -/
def degreeTwoOz : Surreal.OmnificInteger.{u} :=
  ofRealSeries (degreeTwoWithConstant (K := ℝ)) degreeTwoWithConstant_constantCoeff_mem

private theorem degreeTwoOz_signed :
    degreeTwoOz.{u}.1.toSignedFullHahnSeries =
      mapRealDomainToSurreal (degreeTwoWithConstant (K := ℝ)) :=
  toSignedFullHahnSeries_ofRealSeries _ _

/-- The explicit PS06 omnific integer is irreducible. -/
theorem degreeTwoOz_irreducible : Irreducible degreeTwoOz.{u} := by
  apply irreducible_ofRealSeries
  apply irreducible_mapRealDomainToSurrealIntegerPart Surreal.archimedeanStrata
    Surreal.realIntegerSubring (degreeTwoWithConstant (K := ℝ)) degreeTwoWithConstant_ne_zero
    signedDegreeTwo_order_ne_zero degreeTwoWithConstant_constantCoeff
  rw [nonpositiveCoefficientMap_degreeTwoWithConstant]
  exact degreeTwoWithConstant_irreducible
    (K := ℝ⟦FiniteArchimedeanClass.ball ℝ Surreal.realFiniteClass⟧)

/-- The explicit construction has the prescribed Conway normal form. -/
theorem degreeTwoOz_toHahnSeries : degreeTwoOz.{u}.1.toHahnSeries =
    DegreeTwoExample.normalForm := by
  apply Surreal.toHahnSeries_eq_of_toSignedFullHahnSeries_eq degreeTwoOz_signed
  · intro r
    by_cases hr : r ∈ Set.range degreeTwoExponentEmbedding
    · obtain ⟨p, rfl⟩ := hr
      rcases p with ⟨m, n⟩
      have hcoeff := degreeTwoWithConstant_coeff_embedding (K := ℝ) m n
      rw [degreeTwoExponentEmbedding_apply] at hcoeff
      change DegreeTwoExample.normalForm.coeff
          (-((degreeTwoExponentEmbedding (toLex (m, n)) : ℝ) : Surreal)) =
        ((degreeTwoWithConstant (K := ℝ) : Berarducci.Series ℝ) : ℝ⟦ℝ⟧).coeff
          (degreeTwoExponentEmbedding (toLex (m, n)))
      rw [degreeTwoExponentEmbedding_apply, hcoeff, degreeTwoExponentPair_eq_neg_exponent,
        Real.toSurreal_neg, neg_neg,
        DegreeTwoExample.normalForm_coeff_exponent]
    · by_cases hr0 : r = 0
      · subst hr0
        rw [degreeTwoWithConstant_coeff_zero]
        simpa using DegreeTwoExample.normalForm_coeff_zero
      · rw [degreeTwoWithConstant_coeff_eq_zero hr hr0, ← not_ne_iff,
          ← SurrealHahnSeries.mem_support_iff,
          DegreeTwoExample.normalForm_support]
        rintro ⟨p, hp⟩
        induction p using WithTop.recTopCoe with
        | top =>
            apply hr0
            have h0 : (0 : Surreal) = -(r : Surreal) := hp
            exact_mod_cast (neg_eq_zero.mp h0.symm)
        | coe q =>
            rcases q with ⟨m, n⟩
            apply hr
            refine ⟨toLex (m, n), ?_⟩
            have hmn :
                ((DegreeTwoExample.exponent m n : ℝ) : Surreal) =
                  -(r : Surreal) := hp
            rw [← Real.toSurreal_neg, Real.toSurreal_inj] at hmn
            rw [degreeTwoExponentEmbedding_apply, degreeTwoExponentPair_eq_neg_exponent, hmn,
              neg_neg]
  · rw [DegreeTwoExample.normalForm_support]
    rintro _ ⟨p, rfl⟩
    induction p using WithTop.recTopCoe with
    | top =>
        refine ⟨0, ?_⟩
        change -((0 : ℝ) : Surreal) = (0 : Surreal)
        simp
    | coe q =>
        rcases q with ⟨m, n⟩
        refine ⟨-DegreeTwoExample.exponent m n, ?_⟩
        change -((-DegreeTwoExample.exponent m n : ℝ) : Surreal) =
          ((DegreeTwoExample.exponent m n : ℝ) : Surreal)
        rw [Real.toSurreal_neg, neg_neg]

/-- The Conway support of the explicit omnific integer is the displayed two-dimensional exponent
sequence followed by exponent zero. -/
theorem degreeTwoOz_support : degreeTwoOz.{u}.1.support =
    Set.range DegreeTwoExample.exponentAtIndex := by
  rw [← Surreal.support_toHahnSeries, degreeTwoOz_toHahnSeries,
    DegreeTwoExample.normalForm_support]

/-- The Conway normal form of the explicit omnific integer has exact support order type
`ω ^ 2 + 1`. -/
theorem degreeTwoOz_length : degreeTwoOz.{u}.1.length =
    Ordinal.omega0 ^ (2 : Ordinal) + 1 := by
  have hlift := Ordinal.lift_omega0_opow_natCast.{u, 0} 2
  simp only [Nat.cast_ofNat] at hlift
  rw [degreeTwoOz, length_ofRealSeries, degreeTwoWithConstant_supportOrderType, Ordinal.lift_add,
    Ordinal.lift_one, hlift]

/-- The explicit PS06 omnific integer is reduced: its Hahn exponents lie in one nonzero
Archimedean class. -/
theorem degreeTwoOz_isReduced : degreeTwoOz.{u}.toSignedNonpositiveHahn.IsReduced :=
  isReduced_ofRealSeries _ _ signedDegreeTwo_order_ne_zero
    degreeTwoWithConstant_constantCoeff

/-- The omnific integer obtained from the explicit PS06 series is prime. -/
@[blueprint "thm:explicit-omnific-prime"
  (phase := "Surreal numbers and omnific integers")
  (title := "Primality of an explicit degree-two omnific integer")
  (statement := /--
    The omnific integer
    \[
      1+\sum_{m,n\in\mathbb N}
      \omega^{\frac{1}{m+1}+\frac{1}{(m+1)(m+2)(n+1)}}
    \]
    is prime in $\mathbf{Oz}$.
  -/)
  (proof := /--
  In the signed orientation $t=\omega^{-1}$, the nonconstant part is the
  real-exponent series above, now over the coefficient field of the leading
  Archimedean class. By \ref{fact:ps06-irreducibility}, that series is
  irreducible. Coefficient
  transport and the residue-one irreducibility transfer then make the displayed
  omnific integer irreducible.  It is prime by
  \ref{thm:omnific-factorisation}.
  -/)
  (highlight)]
theorem degreeTwoOz_prime : Prime degreeTwoOz.{u} :=
  Surreal.OmnificInteger.prime_of_irreducible _ degreeTwoOz_irreducible

end

end Surreal.OmnificInteger.DegreeTwoExample
