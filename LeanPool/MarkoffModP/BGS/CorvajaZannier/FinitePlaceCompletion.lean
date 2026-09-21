/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# Finite places and their adic completions

Let `R` be a Dedekind domain with fraction field `L`.  Mathlib supplies both
the exponent `FractionalIdeal.count L v I` of a height-one prime `v` in a
fractional ideal `I` and the `v`-adic completion of `L`.  This file connects
those two interfaces for principal fractional ideals.

For a nonzero global function `x`, the valuation of its image in the actual
adic completion is `exp (-ord_v(x))`, where `ord_v(x)` is the exponent of `v`
in `(x)`.  The orders at all finite places are also packaged as a genuine
finitely supported divisor.  This is the finite-place part of the global
divisor infrastructure needed in the Corvaja--Zannier Wronskian argument.

It does not add the places above infinity, a degree map on divisors, or the
canonical-divisor degree formula.
-/

open scoped nonZeroDivisors
open IsDedekindDomain Multiplicative WithZero

namespace BGS.CorvajaZannier

noncomputable section

variable {R L : Type*} [CommRing R] [IsDedekindDomain R]
  [Field L] [Algebra R L] [IsFractionRing R L]

/-- The additive order of `x` at the finite place `v`, defined as the
exponent of `v` in the principal fractional ideal `(x)`. -/
def finitePlaceOrder (v : HeightOneSpectrum R) (x : L) : ℤ :=
  FractionalIdeal.count L v (FractionalIdeal.spanSingleton R⁰ x)

/-- The multiplicative `v`-adic valuation is the exponential of minus the
additive order defined by principal fractional-ideal factorization. -/
theorem valuation_eq_exp_neg_finitePlaceOrder
    (v : HeightOneSpectrum R) (x : L) (hx : x ≠ 0) :
    v.valuation L x = exp (-finitePlaceOrder v x) := by
  obtain ⟨⟨n, d, hd⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors R) x
  obtain rfl : x = IsLocalization.mk' L n ⟨d, hd⟩ :=
    IsLocalization.eq_mk'_iff_mul_eq.mpr hnd
  have hn : n ≠ 0 := by
    intro hn
    apply hx
    simp [hn]
  have hd' : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hprincipal :
      FractionalIdeal.spanSingleton R⁰ (IsLocalization.mk' L n ⟨d, hd⟩) =
        FractionalIdeal.spanSingleton R⁰ ((algebraMap R L d)⁻¹) *
          (↑(Ideal.span {n}) : FractionalIdeal R⁰ L) := by
    rw [FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton]
    apply congrArg (FractionalIdeal.spanSingleton R⁰)
    rw [IsFractionRing.mk'_eq_div, div_eq_mul_inv, mul_comm]
  have hspan :
      FractionalIdeal.spanSingleton R⁰ (IsLocalization.mk' L n ⟨d, hd⟩) ≠ 0 := by
    rw [FractionalIdeal.spanSingleton_ne_zero_iff]
    exact hx
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_mk',
    IsDedekindDomain.HeightOneSpectrum.intValuation_if_neg v hn,
    IsDedekindDomain.HeightOneSpectrum.intValuation_if_neg v hd',
    finitePlaceOrder,
    FractionalIdeal.count_well_defined L v hspan hprincipal]
  rw [← exp_sub]
  congr 1
  ring

/-- The canonical embedding of the global fraction field into the actual
adic completion attached to a finite place. -/
def finitePlaceCompletionEmbedding (v : HeightOneSpectrum R) :
    L →+* v.adicCompletion L :=
  algebraMap L (v.adicCompletion L)

theorem finitePlaceCompletionEmbedding_injective (v : HeightOneSpectrum R) :
    Function.Injective (finitePlaceCompletionEmbedding (R := R) (L := L) v) :=
  (finitePlaceCompletionEmbedding (R := R) (L := L) v).injective

/-- After the canonical completion embedding, the completed-field valuation
still records the exponent of `v` in the global principal fractional ideal. -/
theorem valued_finitePlaceCompletionEmbedding_eq_exp_neg_order
    (v : HeightOneSpectrum R) (x : L) (hx : x ≠ 0) :
    Valued.v (finitePlaceCompletionEmbedding (R := R) (L := L) v x) =
      exp (-finitePlaceOrder v x) := by
  calc
    Valued.v (finitePlaceCompletionEmbedding (R := R) (L := L) v x) =
        v.valuation L x := by
      simp [finitePlaceCompletionEmbedding,
        IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
    _ = exp (-finitePlaceOrder v x) :=
      valuation_eq_exp_neg_finitePlaceOrder v x hx

/-- The finite-place part of the principal divisor of `x`.  Finiteness is
provided by unique factorization of nonzero fractional ideals in a Dedekind
domain (and is harmlessly true for `x = 0` under Mathlib's `count 0 = 0`
convention). -/
def finitePrincipalDivisor (x : L) : HeightOneSpectrum R →₀ ℤ :=
  let h := FractionalIdeal.finite_factors
    (FractionalIdeal.spanSingleton R⁰ x)
  Finsupp.mk h.toFinset (fun v ↦ finitePlaceOrder v x)
    (fun _ ↦ h.mem_toFinset)

@[simp]
theorem finitePrincipalDivisor_apply (x : L) (v : HeightOneSpectrum R) :
    finitePrincipalDivisor x v = finitePlaceOrder v x := rfl

/-- The finite principal divisor of a nonzero product is the sum of the two
finite principal divisors. -/
theorem finitePrincipalDivisor_mul
    (x y : L) (hx : x ≠ 0) (hy : y ≠ 0) :
    finitePrincipalDivisor (R := R) (x * y) =
      finitePrincipalDivisor (R := R) x + finitePrincipalDivisor (R := R) y := by
  ext v
  simp only [finitePrincipalDivisor_apply, Finsupp.add_apply, finitePlaceOrder]
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.count_mul L v]
  · exact FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx
  · exact FractionalIdeal.spanSingleton_ne_zero_iff.mpr hy

end

end BGS.CorvajaZannier
