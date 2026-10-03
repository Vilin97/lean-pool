/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.FinitePrimeFractionalIdeal
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.NumberFieldFractionalIdealGroup
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.RingTheory.DedekindDomain.Factorization
/-!
# Prime factorization of nonzero fractional ideals

Mathlib's `FractionalIdeal.count` and unique-factorization theorems identify
the multiplicative group of nonzero fractional ideals with the finitely
supported integer exponents of finite primes. This equivalence is formulated
entirely in Mathlib and public Definitions vocabulary.
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable
section

namespace ClassFieldTheory

universe u

namespace NumberFieldFractionalIdealGroup

variable {K : Type u} [Field K] [NumberField K]

open scoped Classical in
/-- The integer exponent of one finite prime, viewed multiplicatively. -/
def primePowerHom (v : HeightOneSpectrum (𝓞 K)) :
    Multiplicative ℤ →* NumberFieldFractionalIdealGroup K :=
  MonoidHom.mk'
    (fun n => finitePrimeFractionalIdeal v ^ n.toAdd)
    (fun m n => by simp only [toAdd_mul, zpow_add])

open scoped Classical in
/-- Reconstruct a nonzero fractional ideal from finitely many prime
exponents. -/
def factorization :
    Multiplicative (HeightOneSpectrum (𝓞 K) →₀ ℤ) →*
      NumberFieldFractionalIdealGroup K :=
  MonoidHom.mk'
    (fun exps =>
      exps.toAdd.prod fun v n => primePowerHom v (Multiplicative.ofAdd n))
    (fun a b => by
      exact Finsupp.prod_hom_add_index (fun v => primePowerHom v))

open scoped Classical in
@[simp]
theorem factorization_val
    (exps : Multiplicative (HeightOneSpectrum (𝓞 K) →₀ ℤ)) :
    ((factorization exps : NumberFieldFractionalIdealGroup K) :
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      exps.toAdd.prod fun v n =>
        (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ n := by
  classical
  simp [factorization, primePowerHom, finitePrimeFractionalIdeal, Finsupp.prod]

open scoped Classical in
/-- Only finitely many finite primes occur with nonzero exponent in a
nonzero fractional ideal. -/
theorem finite_count_support (I : NumberFieldFractionalIdealGroup K) :
    {v : HeightOneSpectrum (𝓞 K) |
      FractionalIdeal.count K v
        (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0}.Finite :=
  Filter.eventually_cofinite.mp
    (FractionalIdeal.finite_factors
      (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K))

open scoped Classical in
/-- The finitely supported prime-exponent vector of a nonzero fractional
ideal. -/
def countVector (I : NumberFieldFractionalIdealGroup K) :
    HeightOneSpectrum (𝓞 K) →₀ ℤ :=
  Finsupp.onFinset (finite_count_support I).toFinset
    (fun v => FractionalIdeal.count K v
      (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K))
    (fun v hv => by
      rw [Set.Finite.mem_toFinset]
      exact hv)

open scoped Classical in
@[simp]
theorem countVector_apply (I : NumberFieldFractionalIdealGroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    countVector I v =
      FractionalIdeal.count K v
        (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :=
  rfl

open scoped Classical in
theorem count_factorization
    (exps : Multiplicative (HeightOneSpectrum (𝓞 K) →₀ ℤ))
    (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v
      ((factorization exps : NumberFieldFractionalIdealGroup K) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      exps.toAdd v := by
  rw [factorization_val]
  exact FractionalIdeal.count_finsuppProd K v exps.toAdd

open scoped Classical in
theorem ext_count {I J : NumberFieldFractionalIdealGroup K}
    (h : ∀ v : HeightOneSpectrum (𝓞 K),
      FractionalIdeal.count K v
        (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      FractionalIdeal.count K v
        (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) :
    I = J := by
  apply Units.ext
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization'
      K (Units.ne_zero I),
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization'
      K (Units.ne_zero J)]
  exact finprod_congr fun v => congrArg
    (fun n : ℤ =>
      (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ n) (h v)

open scoped Classical in
theorem factorization_injective :
    Function.Injective (factorization (K := K)) := by
  intro a b hab
  apply Multiplicative.ext
  ext v
  rw [← count_factorization a v, ← count_factorization b v, hab]

open scoped Classical in
theorem factorization_surjective :
    Function.Surjective (factorization (K := K)) := by
  intro I
  refine ⟨Multiplicative.ofAdd (countVector I), ?_⟩
  apply ext_count
  intro v
  rw [count_factorization]
  change countVector I v =
    FractionalIdeal.count K v
      (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
  exact countVector_apply I v

open scoped Classical in
/-- Multiplicative prime factorization of nonzero fractional ideals. -/
def factorizationEquiv :
    Multiplicative (HeightOneSpectrum (𝓞 K) →₀ ℤ) ≃*
      NumberFieldFractionalIdealGroup K :=
  MulEquiv.ofBijective (factorization (K := K))
    ⟨factorization_injective, factorization_surjective⟩

end NumberFieldFractionalIdealGroup

end ClassFieldTheory
