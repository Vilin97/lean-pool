/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PadicField
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.Cyclotomic.Discriminant
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.RingTheory.IsAdjoinRoot
/-!
# The Eisenstein polynomial of the `p`-power cyclotomic extension

For a primitive `p ^ m`-th root of unity `ζ`, with `m > 0`, the local
cyclotomic calculation proves that `ℚ_[p](ζ) / ℚ_[p]` is totally ramified of degree
`φ (p ^ m)`, identifies its Galois group with `(ZMod (p ^ m))ˣ`, identifies
its valuation ring with `ℤ_[p][ζ]`, and shows that `1 - ζ` is a prime
element of norm `p`.

The source is the translated cyclotomic Eisenstein polynomial
`Φ_{p^(k+1)}(X + 1)`.  We first transport its integral Eisenstein criterion
to the actual p-adic integer ring; no irreducibility or ramification
conclusion is assumed.
-/

noncomputable section

namespace AlgebraicNumberTheory
namespace Valuations

open Polynomial
open scoped Polynomial

universe u

theorem padicCyclotomicTotallyRamified_norm_isUnit_iff
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Module.Free R A] (x : A) :
    IsUnit (Algebra.norm R x) ↔ IsUnit x := by
  rw [Algebra.norm_apply, ← LinearMap.isUnit_iff_isUnit_det,
    Algebra.lmul_isUnit_iff]

/-- The translated prime-power cyclotomic polynomial over the actual p-adic
integer ring. -/
def padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt
    (p k : ℕ) [Fact p.Prime] : ℤ_[p][X] :=
  (cyclotomic (p ^ (k + 1)) ℤ_[p]).comp (X + 1)

theorem padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt_eq_map
    (p k : ℕ) [Fact p.Prime] :
    padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt p k =
      (((cyclotomic (p ^ (k + 1)) ℤ).comp (X + 1)).map
        (algebraMap ℤ ℤ_[p])) := by
  simp [padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt, Polynomial.map_comp]

/-- The translated cyclotomic polynomial remains Eisenstein after
completion from `ℤ` to `ℤ_[p]`. -/
theorem padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt_isEisensteinAt
    (p k : ℕ) [Fact p.Prime] :
    (padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt p k).IsEisensteinAt
      (Ideal.span ({(p : ℤ_[p])} : Set ℤ_[p])) := by
  let F : ℤ[X] := (cyclotomic (p ^ (k + 1)) ℤ).comp (X + 1)
  let G : ℤ_[p][X] := padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt p k
  have hF : F.IsEisensteinAt (Ideal.span ({(p : ℤ)} : Set ℤ)) := by
    simpa [F] using cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt p k
  have hGmonic : G.Monic := by
    dsimp [G, padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt]
    exact (cyclotomic.monic _ ℤ_[p]).comp_X_add_C 1
  refine hGmonic.isEisensteinAt_of_mem_of_notMem
    (Ideal.IsPrime.ne_top ((Ideal.span_singleton_prime PadicInt.prime_p.ne_zero).2
      PadicInt.prime_p)) ?_ ?_
  · intro i hi
    have hdeg : G.natDegree = F.natDegree := by
      change (padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt p k).natDegree = F.natDegree
      rw [padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt_eq_map]
      exact Polynomial.Monic.natDegree_map
        ((cyclotomic.monic (p ^ (k + 1)) ℤ).comp_X_add_C 1)
        (algebraMap ℤ ℤ_[p])
    have hmemF : F.coeff i ∈ Ideal.span ({(p : ℤ)} : Set ℤ) :=
      hF.mem (hdeg ▸ hi)
    rw [Ideal.mem_span_singleton] at hmemF ⊢
    change (p : ℤ_[p]) ∣ (padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt p k).coeff i
    rw [padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt_eq_map, coeff_map]
    obtain ⟨a, ha⟩ := hmemF
    refine ⟨(a : ℤ_[p]), ?_⟩
    simpa [F] using congrArg (algebraMap ℤ ℤ_[p]) ha
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    intro hdiv
    change (p : ℤ_[p]) ^ 2 ∣
      (padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt p k).coeff 0 at hdiv
    rw [padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt_eq_map, coeff_map] at hdiv
    have hdivZ : (p : ℤ) ^ 2 ∣ F.coeff 0 :=
      (PadicInt.pow_p_dvd_int_iff 2 (F.coeff 0)).mp hdiv
    exact hF.notMem (by
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact hdivZ)

/-- The translated polynomial is irreducible over `ℤ_[p]` by Eisenstein. -/
theorem padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt_irreducible
    (p k : ℕ) [Fact p.Prime] :
    Irreducible (padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt p k) := by
  have hei := padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt_isEisensteinAt p k
  have hprime :
      (Ideal.span ({(p : ℤ_[p])} : Set ℤ_[p])).IsPrime :=
    (Ideal.span_singleton_prime PadicInt.prime_p.ne_zero).2 PadicInt.prime_p
  have hmonic : (padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt p k).Monic :=
    (cyclotomic.monic _ ℤ_[p]).comp_X_add_C 1
  apply hei.irreducible hprime hmonic.isPrimitive
  rw [padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt, natDegree_comp,
    show (X + 1 : ℤ_[p][X]) = X + C 1 by simp,
    natDegree_X_add_C, mul_one, natDegree_cyclotomic]
  exact (Nat.totient_pos.mpr (pow_pos (Fact.out : Nat.Prime p).pos _))

/-- The translated polynomial is irreducible over the p-adic field. -/
theorem padicCyclotomicTotallyRamifiedShiftedCyclotomicPadic_irreducible
    (p k : ℕ) [Fact p.Prime] :
    Irreducible
      ((cyclotomic (p ^ (k + 1)) ℚ_[p]).comp (X + 1)) := by
  let G := padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt p k
  have hG : Irreducible G :=
    padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt_irreducible p k
  have hGmonic : G.Monic := (cyclotomic.monic _ ℤ_[p]).comp_X_add_C 1
  have hmap : Irreducible (G.map (algebraMap ℤ_[p] ℚ_[p])) :=
    hGmonic.irreducible_iff_irreducible_map_fraction_map.mp hG
  simpa [G, padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt,
    Polynomial.map_comp] using hmap

/-- The prime-power cyclotomic polynomial is irreducible over `ℚ_[p]`.
This supplies the local irreducibility input for the ramification analysis. -/
theorem padicCyclotomicPolynomial_irreducible_prime_pow_succ
    (p k : ℕ) [Fact p.Prime] :
    Irreducible (cyclotomic (p ^ (k + 1)) ℚ_[p]) := by
  let F : ℚ_[p][X] := cyclotomic (p ^ (k + 1)) ℚ_[p]
  have hs : Irreducible (F.comp (X + 1)) := by
    simpa [F] using padicCyclotomicTotallyRamifiedShiftedCyclotomicPadic_irreducible p k
  have hb := hs.map (Polynomial.algEquivAevalXAddC (-1 : ℚ_[p]))
  rw [Polynomial.algEquivAevalXAddC_apply, ← comp_eq_aeval] at hb
  simpa [F, comp_assoc] using hb

section CyclotomicExtension

variable {p k : ℕ} [Fact p.Prime]
variable {L : Type u} [Field L] [Algebra ℚ_[p] L]

local instance padicCyclotomicTotallyRamifiedAlgebraPadicInt : Algebra ℤ_[p] L :=
  ((algebraMap ℚ_[p] L).comp (algebraMap ℤ_[p] ℚ_[p])).toAlgebra

local instance padicCyclotomicTotallyRamifiedScalarTowerPadicInt :
    IsScalarTower ℤ_[p] ℚ_[p] L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- A field generated over `ℚ_[p]` by the displayed primitive root is the
corresponding cyclotomic extension.  The generation hypothesis only spells
out the notation `ℚ_[p](ζ)`; none of the totally ramified cyclotomic theorem's conclusions is
assumed. -/
theorem padic_isCyclotomicExtension_of_primitiveRoot_adjoin_eq_top
    (ζ : L) (hζ : IsPrimitiveRoot ζ (p ^ (k + 1)))
    (hgen : Algebra.adjoin ℚ_[p] ({ζ} : Set L) = ⊤) :
    IsCyclotomicExtension {p ^ (k + 1)} ℚ_[p] L := by
  let A := Algebra.adjoin ℚ_[p] ({ζ} : Set L)
  let : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ (Fact.out : Nat.Prime p).ne_zero⟩
  let hA : IsCyclotomicExtension {p ^ (k + 1)} ℚ_[p] A :=
    hζ.adjoin_isCyclotomicExtension ℚ_[p]
  let e : A ≃ₐ[ℚ_[p]] L :=
    (Subalgebra.equivOfEq A ⊤ hgen).trans Subalgebra.topEquiv
  exact IsCyclotomicExtension.equiv {p ^ (k + 1)} ℚ_[p] A e

/-- the totally ramified cyclotomic theorem(i), degree in Euler-totient form. -/
theorem padicCyclotomicTotallyRamified_finrank_eq_totient
    (ζ : L) (hζ : IsPrimitiveRoot ζ (p ^ (k + 1)))
    (hgen : Algebra.adjoin ℚ_[p] ({ζ} : Set L) = ⊤) :
    Module.finrank ℚ_[p] L = Nat.totient (p ^ (k + 1)) := by
  let : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ (Fact.out : Nat.Prime p).ne_zero⟩
  let : IsCyclotomicExtension {p ^ (k + 1)} ℚ_[p] L :=
    padic_isCyclotomicExtension_of_primitiveRoot_adjoin_eq_top ζ hζ hgen
  exact IsCyclotomicExtension.finrank L
    (padicCyclotomicPolynomial_irreducible_prime_pow_succ p k)

/-- The explicit degree of the totally ramified cyclotomic extension
`(p - 1) * p ^ k`. -/
theorem padicCyclotomic_finrank_eq_prime_sub_one_mul_pow
    (ζ : L) (hζ : IsPrimitiveRoot ζ (p ^ (k + 1)))
    (hgen : Algebra.adjoin ℚ_[p] ({ζ} : Set L) = ⊤) :
    Module.finrank ℚ_[p] L = (p - 1) * p ^ k := by
  rw [padicCyclotomicTotallyRamified_finrank_eq_totient ζ hζ hgen,
    Nat.totient_prime_pow (Fact.out : Nat.Prime p) (Nat.succ_pos k)]
  simp [Nat.mul_comm]

/-- the totally ramified cyclotomic theorem(ii): the full Galois group is the unit group modulo
`p ^ (k + 1)`. -/
noncomputable def padicCyclotomicTotallyRamified_galoisGroupEquivUnits
    (ζ : L) (hζ : IsPrimitiveRoot ζ (p ^ (k + 1)))
    (hgen : Algebra.adjoin ℚ_[p] ({ζ} : Set L) = ⊤) :
    (L ≃ₐ[ℚ_[p]] L) ≃* (ZMod (p ^ (k + 1)))ˣ := by
  letI : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ (Fact.out : Nat.Prime p).ne_zero⟩
  letI : IsCyclotomicExtension {p ^ (k + 1)} ℚ_[p] L :=
    padic_isCyclotomicExtension_of_primitiveRoot_adjoin_eq_top ζ hζ hgen
  exact IsCyclotomicExtension.autEquivPow L
    (padicCyclotomicPolynomial_irreducible_prime_pow_succ p k)

/-- the totally ramified cyclotomic theorem(iv), including the exceptional order-two case:
the field norm of `1 - ζ` is exactly the rational prime `p`. -/
theorem padicCyclotomic_norm_one_sub_primitiveRoot_eq_prime
    (ζ : L) (hζ : IsPrimitiveRoot ζ (p ^ (k + 1)))
    (hgen : Algebra.adjoin ℚ_[p] ({ζ} : Set L) = ⊤) :
    Algebra.norm ℚ_[p] (1 - ζ) = (p : ℚ_[p]) := by
  let n := p ^ (k + 1)
  let : NeZero n := ⟨pow_ne_zero _ (Fact.out : Nat.Prime p).ne_zero⟩
  let : IsCyclotomicExtension {n} ℚ_[p] L := by
    simpa [n] using padic_isCyclotomicExtension_of_primitiveRoot_adjoin_eq_top ζ hζ hgen
  let : FiniteDimensional ℚ_[p] L :=
    IsCyclotomicExtension.finiteDimensional {n} ℚ_[p] L
  have hirr : Irreducible (cyclotomic n ℚ_[p]) := by
    simpa [n] using padicCyclotomicPolynomial_irreducible_prime_pow_succ p k
  by_cases hn : n = 2
  · have hp_dvd_two : p ∣ 2 := by
      rw [← hn]
      exact dvd_pow_self p (Nat.succ_ne_zero k)
    have hp2 : p = 2 :=
      ((Nat.dvd_prime Nat.prime_two).mp hp_dvd_two).resolve_left
        (Fact.out : Nat.Prime p).ne_one
    have hζ2 : IsPrimitiveRoot ζ 2 := by simpa [n, hn] using hζ
    have hfinrank : Module.finrank ℚ_[p] L = 1 := by
      calc
        Module.finrank ℚ_[p] L = Nat.totient (p ^ (k + 1)) :=
          padicCyclotomicTotallyRamified_finrank_eq_totient ζ hζ hgen
        _ = Nat.totient n := by rfl
        _ = 1 := by rw [hn]; norm_num
    rw [hζ2.eq_neg_one_of_two_right]
    rw [show (1 - (-1 : L)) = algebraMap ℚ_[p] L (2 : ℚ_[p]) by
        calc
          1 - (-1 : L) = (2 : L) := by norm_num
          _ = algebraMap ℚ_[p] L (2 : ℚ_[p]) := by
            simpa using (map_natCast (algebraMap ℚ_[p] L) 2).symm,
      Algebra.norm_algebraMap, hfinrank, pow_one]
    exact_mod_cast hp2.symm
  · have hprimePow : IsPrimePow n := by
      simpa [n] using
        (show IsPrimePow (p ^ (k + 1)) from
          (show IsPrimePow p from (Fact.out : Nat.Prime p).isPrimePow).pow
            (Nat.succ_ne_zero k))
    have hsub : Algebra.norm ℚ_[p] (ζ - 1) = (p : ℚ_[p]) := by
      rw [hζ.sub_one_norm_isPrimePow hprimePow hirr hn,
        show n.minFac = p by
          simpa [n] using
            (Fact.out : Nat.Prime p).pow_minFac (Nat.succ_ne_zero k)]
    have hn_ge_two : 2 ≤ n := by
      exact le_trans (Fact.out : Nat.Prime p).two_le
        (by simpa [n] using Nat.le_pow (a := p) (Nat.succ_pos k))
    have hn_gt_two : 2 < n := lt_of_le_of_ne hn_ge_two (Ne.symm hn)
    have heven : Even (Module.finrank ℚ_[p] L) := by
      rw [padicCyclotomicTotallyRamified_finrank_eq_totient ζ hζ hgen]
      change Even (Nat.totient n)
      exact Nat.totient_even hn_gt_two
    rw [show 1 - ζ = -(ζ - 1) by ring,
      show -(ζ - 1) = algebraMap ℚ_[p] L (-1) * (ζ - 1) by simp,
      map_mul, Algebra.norm_algebraMap, hsub, heven.neg_one_pow, one_mul]

/-- The primitive root is integral over the actual p-adic integer ring. -/
theorem padicCyclotomicTotallyRamified_primitiveRoot_isIntegral_padicInt
    (ζ : L) (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) :
    IsIntegral ℤ_[p] ζ := by
  refine ⟨X ^ (p ^ (k + 1)) - 1,
    monic_X_pow_sub_C 1 (pow_ne_zero _ (Fact.out : Nat.Prime p).ne_zero), ?_⟩
  simp [hζ.pow_eq_one]

/-- The p-adic-integer minimal polynomial of `ζ - 1` is the Eisenstein
translate `Φ_{p^(k+1)}(X+1)`. -/
theorem padicCyclotomicTotallyRamified_minpoly_sub_one_padicInt
    (ζ : L) (hζ : IsPrimitiveRoot ζ (p ^ (k + 1)))
    (hgen : Algebra.adjoin ℚ_[p] ({ζ} : Set L) = ⊤) :
    minpoly ℤ_[p] (ζ - 1) =
      padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt p k := by
  let n := p ^ (k + 1)
  let : NeZero n := ⟨pow_ne_zero _ (Fact.out : Nat.Prime p).ne_zero⟩
  let : IsCyclotomicExtension {n} ℚ_[p] L := by
    simpa [n] using padic_isCyclotomicExtension_of_primitiveRoot_adjoin_eq_top ζ hζ hgen
  have hirr : Irreducible (cyclotomic n ℚ_[p]) := by
    simpa [n] using padicCyclotomicPolynomial_irreducible_prime_pow_succ p k
  have hint : IsIntegral ℤ_[p] (ζ - 1) :=
    (padicCyclotomicTotallyRamified_primitiveRoot_isIntegral_padicInt ζ hζ).sub isIntegral_one
  apply Polynomial.map_injective (algebraMap ℤ_[p] ℚ_[p])
    (FaithfulSMul.algebraMap_injective ℤ_[p] ℚ_[p])
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[p] hint,
    hζ.minpoly_sub_one_eq_cyclotomic_comp hirr]
  simp [padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt, Polynomial.map_comp]

end CyclotomicExtension

end Valuations
end AlgebraicNumberTheory

end
