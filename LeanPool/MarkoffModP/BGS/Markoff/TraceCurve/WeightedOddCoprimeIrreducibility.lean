/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.TraceCurve.CommonPrimeKummerTower
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Absolute irreducibility of weighted odd-coprime split trace covers

The residue-block proof gives irreducibility first for the normalized coefficients `(1, sigma)`.
This file connects that result to the paper's actual weights `(alpha, beta)`.  Over the algebraic
closure choose `c` with `c ^ e = alpha`; the reversible coordinate scaling `y ↦ c * y` carries the
normalized cover with `sigma = alpha * beta` to `alpha` times the weighted cover.  Thus no new
irreducibility assumption is introduced at the normalization step.
-/

namespace BGS.Markoff

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

/-- Scaling the second variable of a two-variable polynomial by a unit. -/
noncomputable def finTwoSecondVariableScaleEquiv (c : Kˣ) :
    MvPolynomial (Fin 2) K ≃ₐ[K] MvPolynomial (Fin 2) K := by
  let forward : MvPolynomial (Fin 2) K →ₐ[K] MvPolynomial (Fin 2) K :=
    MvPolynomial.aeval ![MvPolynomial.X 0, MvPolynomial.C (c : K) * MvPolynomial.X 1]
  let backward : MvPolynomial (Fin 2) K →ₐ[K] MvPolynomial (Fin 2) K :=
    MvPolynomial.aeval
      ![MvPolynomial.X 0, MvPolynomial.C ((c⁻¹ : Kˣ) : K) * MvPolynomial.X 1]
  refine AlgEquiv.ofAlgHom forward backward ?_ ?_
  · apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · simp [forward, backward]
    · simp [forward, backward, ← mul_assoc]
      rw [← map_mul]
      simp
  · apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · simp [forward, backward]
    · simp [forward, backward, ← mul_assoc]
      rw [← map_mul]
      simp

@[simp]
theorem finTwoSecondVariableScaleEquiv_X_zero (c : Kˣ) :
    finTwoSecondVariableScaleEquiv c (MvPolynomial.X 0) = MvPolynomial.X 0 := by
  simp [finTwoSecondVariableScaleEquiv]

@[simp]
theorem finTwoSecondVariableScaleEquiv_X_one (c : Kˣ) :
    finTwoSecondVariableScaleEquiv c (MvPolynomial.X 1) =
      MvPolynomial.C (c : K) * MvPolynomial.X 1 := by
  simp [finTwoSecondVariableScaleEquiv]

@[simp]
theorem finTwoSecondVariableScaleEquiv_C (c : Kˣ) (a : K) :
    finTwoSecondVariableScaleEquiv c (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [finTwoSecondVariableScaleEquiv]

/-- Exact scaling identity between the normalized and weighted covers. -/
theorem finTwoSecondVariableScaleEquiv_normalizedCover
    (alpha beta : K) (e d : ℕ) (c : Kˣ) (hc : (c : K) ^ e = alpha) :
    finTwoSecondVariableScaleEquiv c
        (splitTraceCoverPolynomial (1 : K) (alpha * beta) d e) =
      MvPolynomial.C alpha * splitTraceCoverPolynomial alpha beta d e := by
  simp only [splitTraceCoverPolynomial, map_add, map_sub, map_mul, map_pow,
    finTwoSecondVariableScaleEquiv_C, finTwoSecondVariableScaleEquiv_X_zero,
    finTwoSecondVariableScaleEquiv_X_one, map_one]
  simp only [mul_pow, ← map_pow]
  rw [Nat.mul_comm 2 e, pow_mul, hc]
  rw [map_pow]
  ring

/-- The cleared split trace-cover polynomial commutes with scalar extension. -/
theorem map_splitTraceCoverPolynomial
    {L : Type*} [Field L] (phi : K →+* L) (alpha beta : K) (d e : ℕ) :
    MvPolynomial.map phi (splitTraceCoverPolynomial alpha beta d e) =
      splitTraceCoverPolynomial (phi alpha) (phi beta) d e := by
  simp [splitTraceCoverPolynomial]

/-- The paper's weighted split trace cover is absolutely irreducible for arbitrary positive
covering exponents when the first-stage exponent is nonzero in the ground field.  This is the
characteristic condition satisfied by the endgame exponents dividing `p - 1` or `p + 1`. -/
theorem splitTraceCoverPolynomial_absolutelyIrreducible_of_positiveExponents
    (alpha beta : K) (halpha : alpha ≠ 0) (hbeta : beta ≠ 0)
    (hnondegenerate : alpha * beta ≠ 1)
    (e d : ℕ) (he : 0 < e) (hd : 0 < d) (heChar : (e : K) ≠ 0) :
    Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K))
        (splitTraceCoverPolynomial alpha beta d e)) := by
  let phi : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  rw [map_splitTraceCoverPolynomial phi alpha beta d e]
  have halphaL : phi alpha ≠ 0 := (map_ne_zero_iff phi phi.injective).mpr halpha
  have hbetaL : phi beta ≠ 0 := (map_ne_zero_iff phi phi.injective).mpr hbeta
  have hproductL : phi alpha * phi beta ≠ 1 := by
    intro h
    apply hnondegenerate
    apply phi.injective
    simpa [phi] using h
  have heCharL : (e : AlgebraicClosure K) ≠ 0 := by
    change phi (e : K) ≠ 0
    exact (map_ne_zero_iff phi phi.injective).mpr heChar
  letI : NeZero e := ⟨he.ne'⟩
  letI : NeZero (e : AlgebraicClosure K) := ⟨heCharL⟩
  obtain ⟨zeta, hzeta⟩ :=
    HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) e
  obtain ⟨sqrtNegOne, hsqrtNegOne⟩ :=
    IsAlgClosed.exists_pow_nat_eq (-1 : AlgebraicClosure K) zero_lt_two
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (phi alpha) he
  have hcne : c ≠ 0 := by
    intro hc0
    apply halphaL
    rw [← hc]
    simp [hc0, Nat.ne_of_gt he]
  let cUnit : (AlgebraicClosure K)ˣ := Units.mk0 c hcne
  have hnormalized : Irreducible
      (splitTraceCoverPolynomial (1 : AlgebraicClosure K) (phi alpha * phi beta) d e) :=
    splitTraceCoverPolynomial_irreducible_of_primitiveRoot
      (phi alpha * phi beta) (mul_ne_zero halphaL hbetaL) hproductL
      sqrtNegOne hsqrtNegOne e d he hd zeta hzeta
  have hscaled := hnormalized.map (finTwoSecondVariableScaleEquiv cUnit)
  have hscaleIdentity :
      finTwoSecondVariableScaleEquiv cUnit
          (splitTraceCoverPolynomial (1 : AlgebraicClosure K) (phi alpha * phi beta) d e) =
        MvPolynomial.C (phi alpha) *
          splitTraceCoverPolynomial (phi alpha) (phi beta) d e := by
    apply finTwoSecondVariableScaleEquiv_normalizedCover
    simpa [cUnit] using hc
  rw [hscaleIdentity] at hscaled
  exact (irreducible_isUnit_mul
    (halphaL.isUnit.map (MvPolynomial.C : AlgebraicClosure K →+*
      MvPolynomial (Fin 2) (AlgebraicClosure K)))).mp hscaled

/-- The paper's weighted split trace cover is absolutely irreducible for nonzero weights with
nondegenerate product and arbitrary positive coprime covering exponents.  Passing to the
algebraic closure supplies both the required square root of `-1` and the root used to normalize
the first weight. -/
theorem splitTraceCoverPolynomial_absolutelyIrreducible_of_coprime
    (alpha beta : K) (halpha : alpha ≠ 0) (hbeta : beta ≠ 0)
    (hnondegenerate : alpha * beta ≠ 1)
    (e d : ℕ) (he : 0 < e) (hd : 0 < d) (hde : d.Coprime e) :
    Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K))
        (splitTraceCoverPolynomial alpha beta d e)) := by
  let phi : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  rw [map_splitTraceCoverPolynomial phi alpha beta d e]
  have halphaL : phi alpha ≠ 0 := (map_ne_zero_iff phi phi.injective).mpr halpha
  have hbetaL : phi beta ≠ 0 := (map_ne_zero_iff phi phi.injective).mpr hbeta
  have hproductL : phi alpha * phi beta ≠ 1 := by
    intro h
    apply hnondegenerate
    apply phi.injective
    simpa [phi] using h
  obtain ⟨sqrtNegOne, hsqrtNegOne⟩ :=
    IsAlgClosed.exists_pow_nat_eq (-1 : AlgebraicClosure K) zero_lt_two
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (phi alpha) he
  have hcne : c ≠ 0 := by
    intro hc0
    apply halphaL
    rw [← hc]
    simp [hc0, Nat.ne_of_gt he]
  let cUnit : (AlgebraicClosure K)ˣ := Units.mk0 c hcne
  have hnormalized : Irreducible
      (splitTraceCoverPolynomial (1 : AlgebraicClosure K) (phi alpha * phi beta) d e) :=
    splitTraceCoverPolynomial_irreducible_of_sqrt_neg_one_coprime
      (phi alpha * phi beta) (mul_ne_zero halphaL hbetaL)
      sqrtNegOne hsqrtNegOne e d he hd hde hproductL
  have hscaled := hnormalized.map (finTwoSecondVariableScaleEquiv cUnit)
  have hscaleIdentity :
      finTwoSecondVariableScaleEquiv cUnit
          (splitTraceCoverPolynomial (1 : AlgebraicClosure K) (phi alpha * phi beta) d e) =
        MvPolynomial.C (phi alpha) *
          splitTraceCoverPolynomial (phi alpha) (phi beta) d e := by
    apply finTwoSecondVariableScaleEquiv_normalizedCover
    simpa [cUnit] using hc
  rw [hscaleIdentity] at hscaled
  exact (irreducible_isUnit_mul
    (halphaL.isUnit.map (MvPolynomial.C : AlgebraicClosure K →+*
      MvPolynomial (Fin 2) (AlgebraicClosure K)))).mp hscaled

/-- Backwards-compatible odd-coprime specialization of the positive-coprime theorem. -/
theorem splitTraceCoverPolynomial_absolutelyIrreducible_of_oddCoprime
    (alpha beta : K) (halpha : alpha ≠ 0) (hbeta : beta ≠ 0)
    (hnondegenerate : alpha * beta ≠ 1)
    (e d : ℕ) (heOdd : Odd e) (hdOdd : Odd d) (hde : d.Coprime e) :
    Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K))
        (splitTraceCoverPolynomial alpha beta d e)) :=
  splitTraceCoverPolynomial_absolutelyIrreducible_of_coprime
    alpha beta halpha hbeta hnondegenerate e d heOdd.pos hdOdd.pos hde

end

end BGS.Markoff
