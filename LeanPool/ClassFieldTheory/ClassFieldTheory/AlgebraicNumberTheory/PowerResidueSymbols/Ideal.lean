/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.PowerResidueSymbols.FiniteField
public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import Mathlib.RingTheory.DedekindDomain.Factorization
/-!
# Power-residue symbols at prime ideals and integral ideals

Let `K` contain the `n`-th roots of unity and let `P` be a prime ideal
whose absolute norm is coprime to `n`.  Reduction identifies
`μₙ(𝓞 K)` with `μₙ(𝓞 K / P)`.  Pulling the finite-field symbol back along
this identification gives `(a/P)`.

For a nonzero integral ideal `I`, `(a/I)` is the finite product of
`(a/P)` raised to the multiplicity of `P` in `I`.
-/

@[expose] public section

open scoped NumberField BigOperators
open NumberField IsDedekindDomain

noncomputable
section

namespace AlgebraicNumberTheory
namespace PowerResidueSymbols

attribute [local instance] Ideal.Quotient.field

variable (K : Type*) [Field K] [NumberField K]

open scoped Classical in
/-- The residue field at a nonzero prime ideal of a number field has a finite enumeration. -/
noncomputable local instance primeIdealResidueFintype
    (P : HeightOneSpectrum (𝓞 K)) :
    Fintype (𝓞 K ⧸ P.asIdeal) :=
  Fintype.ofFinite _

attribute [local instance] primeIdealResidueFintype

open scoped Classical in
/-- Reduction of `n`-th roots of unity modulo an integral prime ideal. -/
def rootsOfUnityReduction
    (P : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    rootsOfUnity n (𝓞 K) →*
      rootsOfUnity n (𝓞 K ⧸ P.asIdeal) where
  toFun z :=
    ⟨Ideal.rootsOfUnityMapQuot P.asIdeal n z, by
      change Ideal.rootsOfUnityMapQuot P.asIdeal n (z ^ n) = 1
      rw [show z ^ n = 1 by exact Subtype.ext z.2, map_one]⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (Ideal.rootsOfUnityMapQuot P.asIdeal n)
  map_mul' z w := by
    apply Subtype.ext
    exact map_mul (Ideal.rootsOfUnityMapQuot P.asIdeal n) z w

open scoped Classical in
/-- Reduction on `μₙ` is injective away from `n`. -/
theorem rootsOfUnityReduction_injective
    (P : HeightOneSpectrum (𝓞 K)) (n : ℕ+)
    (hcoprime : (Ideal.absNorm P.asIdeal).Coprime (n : ℕ)) :
    Function.Injective (rootsOfUnityReduction K P (n : ℕ)) := by
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  intro z w hzw
  exact
    Ideal.rootsOfUnityMapQuot_injective
      (I := P.asIdeal) (n : ℕ)
      (Ideal.absNorm_eq_one_iff.not.mpr P.isPrime.ne_top)
      hcoprime
      (congrArg Subtype.val hzw)

open scoped Classical in
/-- If `K` contains `μₙ`, then `n` divides `N(P)-1` at every prime
`P ∤ n`. -/
theorem dvd_absNorm_sub_one_of_primitiveRoots
    (P : HeightOneSpectrum (𝓞 K)) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hcoprime : (Ideal.absNorm P.asIdeal).Coprime (n : ℕ)) :
    (n : ℕ) ∣ Ideal.absNorm P.asIdeal - 1 := by
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  obtain ⟨zeta, hzeta⟩ := hmu
  have hzetaK : IsPrimitiveRoot zeta (n : ℕ) :=
    (mem_primitiveRoots n.pos).1 hzeta
  have hcard :
      Nat.card (rootsOfUnity (n : ℕ) (𝓞 K)) = (n : ℕ) :=
    hzetaK.toInteger_isPrimitiveRoot.card_rootsOfUnity
  have hinjective :
      Function.Injective
        (Ideal.rootsOfUnityMapQuot P.asIdeal (n : ℕ)) :=
    Ideal.rootsOfUnityMapQuot_injective
      (I := P.asIdeal) (n : ℕ)
      (Ideal.absNorm_eq_one_iff.not.mpr P.isPrime.ne_top)
      hcoprime
  have hdvd :=
    Subgroup.card_dvd_of_injective
      (Ideal.rootsOfUnityMapQuot P.asIdeal (n : ℕ)) hinjective
  rw [hcard, Nat.card_units] at hdvd
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact hdvd

open scoped Classical in
/-- Away from `n`, reduction identifies the global integral `n`-th roots
of unity with the residue-field `n`-th roots of unity. -/
noncomputable def rootsOfUnityReductionEquiv
    (P : HeightOneSpectrum (𝓞 K)) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hcoprime : (Ideal.absNorm P.asIdeal).Coprime (n : ℕ)) :
    rootsOfUnity (n : ℕ) (𝓞 K) ≃*
      rootsOfUnity (n : ℕ) (𝓞 K ⧸ P.asIdeal) := by
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  letI : Fintype (rootsOfUnity (n : ℕ) (𝓞 K)) :=
    Fintype.ofFinite _
  let f := rootsOfUnityReduction K P (n : ℕ)
  have hinjective : Function.Injective f :=
    rootsOfUnityReduction_injective K P n hcoprime
  let zeta := Classical.choose hmu
  have hzeta := Classical.choose_spec hmu
  have hzetaK : IsPrimitiveRoot zeta (n : ℕ) :=
    (mem_primitiveRoots n.pos).1 hzeta
  have hsource :
      Fintype.card (rootsOfUnity (n : ℕ) (𝓞 K)) = (n : ℕ) := by
    rw [← Nat.card_eq_fintype_card]
    exact hzetaK.toInteger_isPrimitiveRoot.card_rootsOfUnity
  have htarget_le :
      Fintype.card (rootsOfUnity (n : ℕ) (𝓞 K ⧸ P.asIdeal)) ≤
        (n : ℕ) := by
    rw [← Nat.card_eq_fintype_card]
    exact card_rootsOfUnity (𝓞 K ⧸ P.asIdeal) (n : ℕ)
  have hsource_le_target :
      Fintype.card (rootsOfUnity (n : ℕ) (𝓞 K)) ≤
        Fintype.card (rootsOfUnity (n : ℕ) (𝓞 K ⧸ P.asIdeal)) :=
    Fintype.card_le_of_injective f hinjective
  have htarget :
      Fintype.card (rootsOfUnity (n : ℕ) (𝓞 K ⧸ P.asIdeal)) =
        (n : ℕ) :=
    Nat.le_antisymm htarget_le (by simpa [hsource] using hsource_le_target)
  exact MulEquiv.ofBijective f
    ((Fintype.bijective_iff_injective_and_card f).2
      ⟨hinjective, hsource.trans htarget.symm⟩)

open scoped Classical in
/-- The reduction equivalence acts by the canonical reduction homomorphism. -/
@[simp]
theorem rootsOfUnityReductionEquiv_apply
    (P : HeightOneSpectrum (𝓞 K)) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hcoprime : (Ideal.absNorm P.asIdeal).Coprime (n : ℕ))
    (zeta : rootsOfUnity (n : ℕ) (𝓞 K)) :
    rootsOfUnityReductionEquiv K P n hmu hcoprime zeta =
      rootsOfUnityReduction K P (n : ℕ) zeta :=
  rfl

open scoped Classical in
/-- The cardinality of the residue field is the absolute norm of the
prime ideal. -/
theorem card_primeIdealResidueField
    (P : HeightOneSpectrum (𝓞 K)) :
    Fintype.card (𝓞 K ⧸ P.asIdeal) = Ideal.absNorm P.asIdeal := by
  rw [← Nat.card_eq_fintype_card, Ideal.absNorm_apply,
    Submodule.cardQuot_apply]

open scoped Classical in
/-- An algebraic integer prime to `P`, regarded as a unit of the residue
field. -/
def primeIdealResidueUnit
    (P : HeightOneSpectrum (𝓞 K))
    (a : 𝓞 K) (ha : a ∉ P.asIdeal) :
    (𝓞 K ⧸ P.asIdeal)ˣ :=
  Units.mk0 (Ideal.Quotient.mk P.asIdeal a)
    (by
      rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
      exact ha)

open scoped Classical in
@[simp]
theorem primeIdealResidueUnit_mul
    (P : HeightOneSpectrum (𝓞 K))
    (a b : 𝓞 K) (ha : a ∉ P.asIdeal) (hb : b ∉ P.asIdeal)
    (hab : a * b ∉ P.asIdeal) :
    primeIdealResidueUnit K P (a * b) hab =
      primeIdealResidueUnit K P a ha *
        primeIdealResidueUnit K P b hb := by
  apply Units.ext
  rfl

open scoped Classical in
/-- The `n`-th power-residue symbol `(a/P)`, valued in the common group
`μₙ(𝓞 K)`. -/
noncomputable def primeIdealPowerResidueSymbol
    (P : HeightOneSpectrum (𝓞 K)) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hcoprime : (Ideal.absNorm P.asIdeal).Coprime (n : ℕ))
    (a : 𝓞 K) (ha : a ∉ P.asIdeal) :
    rootsOfUnity (n : ℕ) (𝓞 K) :=
  let hn : (n : ℕ) ∣ Fintype.card (𝓞 K ⧸ P.asIdeal) - 1 := by
    rw [card_primeIdealResidueField K P]
    exact dvd_absNorm_sub_one_of_primitiveRoots K P n hmu hcoprime
  (rootsOfUnityReductionEquiv K P n hmu hcoprime).symm
    (finiteFieldPowerResidueSymbol
      (𝓞 K ⧸ P.asIdeal) n hn
      (primeIdealResidueUnit K P a ha))

open scoped Classical in
/-- Reduction sends `(a/P)` to the finite-field formula
`a^((N(P)-1)/n)`. -/
theorem rootsOfUnityReductionEquiv_primeIdealPowerResidueSymbol
    (P : HeightOneSpectrum (𝓞 K)) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hcoprime : (Ideal.absNorm P.asIdeal).Coprime (n : ℕ))
    (a : 𝓞 K) (ha : a ∉ P.asIdeal) :
    let hn : (n : ℕ) ∣ Fintype.card (𝓞 K ⧸ P.asIdeal) - 1 := by
      rw [card_primeIdealResidueField K P]
      exact dvd_absNorm_sub_one_of_primitiveRoots K P n hmu hcoprime
    rootsOfUnityReductionEquiv K P n hmu hcoprime
        (primeIdealPowerResidueSymbol K P n hmu hcoprime a ha) =
      finiteFieldPowerResidueSymbol
        (𝓞 K ⧸ P.asIdeal) n hn
        (primeIdealResidueUnit K P a ha) := by
  dsimp only [primeIdealPowerResidueSymbol]
  exact (rootsOfUnityReductionEquiv K P n hmu hcoprime).apply_symm_apply _

open scoped Classical in
/-- The prime-ideal symbol is one exactly when `a` is an `n`-th power
modulo `P`. -/
theorem primeIdealPowerResidueSymbol_eq_one_iff
    (P : HeightOneSpectrum (𝓞 K)) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hcoprime : (Ideal.absNorm P.asIdeal).Coprime (n : ℕ))
    (a : 𝓞 K) (ha : a ∉ P.asIdeal) :
    primeIdealPowerResidueSymbol K P n hmu hcoprime a ha = 1 ↔
      ∃ u : (𝓞 K ⧸ P.asIdeal)ˣ,
        u ^ (n : ℕ) = primeIdealResidueUnit K P a ha := by
  let hn : (n : ℕ) ∣ Fintype.card (𝓞 K ⧸ P.asIdeal) - 1 := by
    rw [card_primeIdealResidueField K P]
    exact dvd_absNorm_sub_one_of_primitiveRoots K P n hmu hcoprime
  constructor
  · intro h
    have hred := congrArg
      (rootsOfUnityReductionEquiv K P n hmu hcoprime) h
    rw [rootsOfUnityReductionEquiv_primeIdealPowerResidueSymbol,
      map_one] at hred
    exact
      (finiteFieldPowerResidueSymbol_eq_one_iff
        (𝓞 K ⧸ P.asIdeal) n hn
        (primeIdealResidueUnit K P a ha)).1 hred
  · intro h
    apply (rootsOfUnityReductionEquiv K P n hmu hcoprime).injective
    rw [rootsOfUnityReductionEquiv_primeIdealPowerResidueSymbol, map_one]
    exact
      (finiteFieldPowerResidueSymbol_eq_one_iff
        (𝓞 K ⧸ P.asIdeal) n hn
        (primeIdealResidueUnit K P a ha)).2 h

open scoped Classical in
/-- Multiplicativity of `(a/P)` in the numerator. -/
theorem primeIdealPowerResidueSymbol_mul
    (P : HeightOneSpectrum (𝓞 K)) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hcoprime : (Ideal.absNorm P.asIdeal).Coprime (n : ℕ))
    (a b : 𝓞 K) (ha : a ∉ P.asIdeal) (hb : b ∉ P.asIdeal) :
    primeIdealPowerResidueSymbol K P n hmu hcoprime (a * b)
        (by
          intro hab
          exact (P.isPrime.mem_or_mem hab).elim ha hb) =
      primeIdealPowerResidueSymbol K P n hmu hcoprime a ha *
        primeIdealPowerResidueSymbol K P n hmu hcoprime b hb := by
  let hab : a * b ∉ P.asIdeal := by
    intro h
    exact (P.isPrime.mem_or_mem h).elim ha hb
  let hn : (n : ℕ) ∣ Fintype.card (𝓞 K ⧸ P.asIdeal) - 1 := by
    rw [card_primeIdealResidueField K P]
    exact dvd_absNorm_sub_one_of_primitiveRoots K P n hmu hcoprime
  apply (rootsOfUnityReductionEquiv K P n hmu hcoprime).injective
  rw [map_mul]
  rw [rootsOfUnityReductionEquiv_primeIdealPowerResidueSymbol,
    rootsOfUnityReductionEquiv_primeIdealPowerResidueSymbol,
    rootsOfUnityReductionEquiv_primeIdealPowerResidueSymbol]
  rw [primeIdealResidueUnit_mul K P a b ha hb hab, map_mul]

open scoped Classical in
/-- Multiplicity of `P` in the prime factorization of a nonzero integral
ideal. -/
def idealPrimeMultiplicity
    (P : HeightOneSpectrum (𝓞 K)) (I : Ideal (𝓞 K)) : ℕ :=
  (Associates.mk P.asIdeal).count (Associates.mk I).factors

open scoped Classical in
/-- Prime-ideal multiplicities add under multiplication of nonzero
integral ideals. -/
theorem idealPrimeMultiplicity_mul
    (P : HeightOneSpectrum (𝓞 K))
    (I J : Ideal (𝓞 K)) (hI : I ≠ 0) (hJ : J ≠ 0) :
    idealPrimeMultiplicity K P (I * J) =
      idealPrimeMultiplicity K P I +
        idealPrimeMultiplicity K P J := by
  unfold idealPrimeMultiplicity
  rw [← Associates.mk_mul_mk]
  exact
    Associates.count_mul
      (Associates.mk_ne_zero.mpr hI)
      (Associates.mk_ne_zero.mpr hJ)
      P.associates_irreducible

open scoped Classical in
/-- A prime not dividing a nonzero ideal has multiplicity zero in its
factorization. -/
theorem idealPrimeMultiplicity_eq_zero_of_not_dvd
    (P : HeightOneSpectrum (𝓞 K))
    (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (hP : ¬ P.asIdeal ∣ I) :
    idealPrimeMultiplicity K P I = 0 := by
  by_contra hne
  exact hP
    ((Associates.count_ne_zero_iff_dvd hI P.irreducible).mp hne)

open scoped Classical in
/-- The finite set of height-one primes dividing a nonzero denominator ideal.

Naming this set keeps every finite-product presentation on the same subtype,
instead of asking typeclass inference to reconstruct definitionally equal
subtypes from separate predicate expressions. -/
def idealPrimeDivisors (I : Ideal (𝓞 K)) :
    Set (HeightOneSpectrum (𝓞 K)) :=
  {P | P.asIdeal ∣ I}

omit [NumberField K] in
open scoped Classical in
/-- Membership in the named prime-divisor set is ordinary ideal divisibility. -/
@[simp]
theorem mem_idealPrimeDivisors
    (I : Ideal (𝓞 K)) (P : HeightOneSpectrum (𝓞 K)) :
    P ∈ idealPrimeDivisors K I ↔ P.asIdeal ∣ I :=
  Iff.rfl

open scoped Classical in
/-- The prime divisors of a nonzero ideal form a finite set. -/
theorem idealPrimeDivisors_finite
    (I : Ideal (𝓞 K)) (hI : I ≠ 0) :
    (idealPrimeDivisors K I).Finite :=
  Ideal.finite_factors hI

open scoped Classical in
/-- **Ideal power residue symbol.**  For `I = ∏ P ^ v_P(I)`, define

`(a/I) = ∏ (a/P) ^ v_P(I)`.

The hypotheses only concern the finitely many primes dividing `I`. -/
noncomputable def idealPowerResidueSymbol
    (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a : 𝓞 K)
    (hcoprime :
      ∀ P : HeightOneSpectrum (𝓞 K),
        P.asIdeal ∣ I →
          (Ideal.absNorm P.asIdeal).Coprime (n : ℕ))
    (ha :
      ∀ P : HeightOneSpectrum (𝓞 K),
        P.asIdeal ∣ I → a ∉ P.asIdeal) :
    rootsOfUnity (n : ℕ) (𝓞 K) := by
  letI : Fintype
      (idealPrimeDivisors K I) :=
    (idealPrimeDivisors_finite K I hI).fintype
  exact
    ∏ P : idealPrimeDivisors K I,
      primeIdealPowerResidueSymbol K P.1 n hmu
          (hcoprime P.1 ((mem_idealPrimeDivisors K I P.1).mp P.2)) a
          (ha P.1 ((mem_idealPrimeDivisors K I P.1).mp P.2)) ^
        idealPrimeMultiplicity K P.1 I

open scoped Classical in
/-- The prime-by-prime factor of the ideal power-residue symbol, extended
by `1` away from the prime divisors of the denominator. -/
noncomputable def idealPowerResidueFactor
    (I : Ideal (𝓞 K))
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a : 𝓞 K)
    (hcoprime :
      ∀ P : HeightOneSpectrum (𝓞 K),
        P.asIdeal ∣ I →
          (Ideal.absNorm P.asIdeal).Coprime (n : ℕ))
    (ha :
      ∀ P : HeightOneSpectrum (𝓞 K),
        P.asIdeal ∣ I → a ∉ P.asIdeal)
    (P : HeightOneSpectrum (𝓞 K)) :
    rootsOfUnity (n : ℕ) (𝓞 K) :=
  if hP : P.asIdeal ∣ I then
    primeIdealPowerResidueSymbol K P n hmu
        (hcoprime P hP) a (ha P hP) ^
      idealPrimeMultiplicity K P I
  else
    1

open scoped Classical in
/-- Only prime divisors of the denominator can contribute a nontrivial
factor. -/
theorem idealPowerResidueFactor_hasFiniteMulSupport
    (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a : 𝓞 K)
    (hcoprime :
      ∀ P : HeightOneSpectrum (𝓞 K),
        P.asIdeal ∣ I →
          (Ideal.absNorm P.asIdeal).Coprime (n : ℕ))
    (ha :
      ∀ P : HeightOneSpectrum (𝓞 K),
        P.asIdeal ∣ I → a ∉ P.asIdeal) :
    Function.HasFiniteMulSupport
      (idealPowerResidueFactor K I n hmu a hcoprime ha) := by
  apply (Ideal.finite_factors hI).subset
  intro P hP
  by_contra hdiv
  have hnot : ¬ P.asIdeal ∣ I := by
    simpa using hdiv
  exact hP (by simp [idealPowerResidueFactor, hnot])

open scoped Classical in
/-- Prime-by-prime multiplicativity in the denominator. -/
theorem idealPowerResidueFactor_mul
    (I J : Ideal (𝓞 K)) (hI : I ≠ 0) (hJ : J ≠ 0)
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a : 𝓞 K)
    (hcoprime :
      ∀ P : HeightOneSpectrum (𝓞 K),
        P.asIdeal ∣ I ∨ P.asIdeal ∣ J →
          (Ideal.absNorm P.asIdeal).Coprime (n : ℕ))
    (ha :
      ∀ P : HeightOneSpectrum (𝓞 K),
        P.asIdeal ∣ I ∨ P.asIdeal ∣ J → a ∉ P.asIdeal)
    (P : HeightOneSpectrum (𝓞 K)) :
    let hcoprimeI :=
      fun P hP => hcoprime P (Or.inl hP)
    let hcoprimeJ :=
      fun P hP => hcoprime P (Or.inr hP)
    let hcoprimeIJ :=
      fun P hP => hcoprime P (P.prime.dvd_mul.mp hP)
    let haI :=
      fun P hP => ha P (Or.inl hP)
    let haJ :=
      fun P hP => ha P (Or.inr hP)
    let haIJ :=
      fun P hP => ha P (P.prime.dvd_mul.mp hP)
    idealPowerResidueFactor K (I * J) n hmu a
        hcoprimeIJ haIJ P =
      idealPowerResidueFactor K I n hmu a
          hcoprimeI haI P *
        idealPowerResidueFactor K J n hmu a
          hcoprimeJ haJ P := by
  dsimp only
  by_cases hPI : P.asIdeal ∣ I
  · have hPIJ : P.asIdeal ∣ I * J :=
      dvd_mul_of_dvd_left hPI J
    by_cases hPJ : P.asIdeal ∣ J
    · rw [idealPowerResidueFactor, dite_eq_left hPIJ,
        idealPowerResidueFactor, dite_eq_left hPI,
        idealPowerResidueFactor, dite_eq_left hPJ,
        idealPrimeMultiplicity_mul K P I J hI hJ,
        pow_add]
    · have hmJ :
          idealPrimeMultiplicity K P J = 0 :=
        idealPrimeMultiplicity_eq_zero_of_not_dvd
          K P J hJ hPJ
      rw [idealPowerResidueFactor, dite_eq_left hPIJ,
        idealPowerResidueFactor, dite_eq_left hPI,
        idealPowerResidueFactor, dite_eq_right hPJ,
        idealPrimeMultiplicity_mul K P I J hI hJ,
        hmJ, add_zero, mul_one]
  · by_cases hPJ : P.asIdeal ∣ J
    · have hPIJ : P.asIdeal ∣ I * J :=
        dvd_mul_of_dvd_right hPJ I
      have hmI :
          idealPrimeMultiplicity K P I = 0 :=
        idealPrimeMultiplicity_eq_zero_of_not_dvd
          K P I hI hPI
      rw [idealPowerResidueFactor, dite_eq_left hPIJ,
        idealPowerResidueFactor, dite_eq_right hPI,
        idealPowerResidueFactor, dite_eq_left hPJ,
        idealPrimeMultiplicity_mul K P I J hI hJ,
        hmI, zero_add, one_mul]
    · have hPIJ : ¬ P.asIdeal ∣ I * J := by
        intro h
        exact (P.prime.dvd_mul.mp h).elim hPI hPJ
      rw [idealPowerResidueFactor, dite_eq_right hPIJ,
        idealPowerResidueFactor, dite_eq_right hPI,
        idealPowerResidueFactor, dite_eq_right hPJ, one_mul]

open scoped Classical in
/-- The subtype product defining the ideal symbol is equivalently the finite product
over all finite primes, with factor `1` away from the denominator. -/
theorem idealPowerResidueSymbol_eq_finprod
    (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a : 𝓞 K)
    (hcoprime :
      ∀ P : HeightOneSpectrum (𝓞 K),
        P.asIdeal ∣ I →
          (Ideal.absNorm P.asIdeal).Coprime (n : ℕ))
    (ha :
      ∀ P : HeightOneSpectrum (𝓞 K),
        P.asIdeal ∣ I → a ∉ P.asIdeal) :
    idealPowerResidueSymbol K I hI n hmu a hcoprime ha =
      ∏ᶠ P : HeightOneSpectrum (𝓞 K),
        idealPowerResidueFactor K I n hmu a hcoprime ha P := by
  classical
  let : Fintype
      (idealPrimeDivisors K I) :=
    (idealPrimeDivisors_finite K I hI).fintype
  calc
    idealPowerResidueSymbol K I hI n hmu a hcoprime ha =
        ∏ P : idealPrimeDivisors K I,
          idealPowerResidueFactor K I n hmu a hcoprime ha P := by
            unfold idealPowerResidueSymbol
            apply Finset.prod_congr rfl
            intro P _
            have hP := (mem_idealPrimeDivisors K I P.1).mp P.2
            simp [idealPowerResidueFactor, hP]
    _ = ∏ᶠ P : idealPrimeDivisors K I,
          idealPowerResidueFactor K I n hmu a hcoprime ha P :=
      (finprod_eq_prod_of_fintype _).symm
    _ = ∏ᶠ (P : HeightOneSpectrum (𝓞 K))
          (_ : P.asIdeal ∣ I),
          idealPowerResidueFactor K I n hmu a hcoprime ha P :=
      finprod_subtype_eq_finprod_cond _
    _ = ∏ᶠ P : HeightOneSpectrum (𝓞 K),
          idealPowerResidueFactor K I n hmu a hcoprime ha P := by
      apply finprod_congr
      intro P
      by_cases hP : P.asIdeal ∣ I
      · simp [hP]
      · simp [idealPowerResidueFactor, hP]

open scoped Classical in
/-- Multiplicativity of the ideal power residue symbol in the denominator ideal. -/
theorem idealPowerResidueSymbol_mul_denominator
    (I J : Ideal (𝓞 K)) (hI : I ≠ 0) (hJ : J ≠ 0)
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a : 𝓞 K)
    (hcoprime :
      ∀ P : HeightOneSpectrum (𝓞 K),
        P.asIdeal ∣ I ∨ P.asIdeal ∣ J →
          (Ideal.absNorm P.asIdeal).Coprime (n : ℕ))
    (ha :
      ∀ P : HeightOneSpectrum (𝓞 K),
        P.asIdeal ∣ I ∨ P.asIdeal ∣ J → a ∉ P.asIdeal) :
    let hcoprimeI :=
      fun P hP => hcoprime P (Or.inl hP)
    let hcoprimeJ :=
      fun P hP => hcoprime P (Or.inr hP)
    let hcoprimeIJ :=
      fun P hP => hcoprime P (P.prime.dvd_mul.mp hP)
    let haI :=
      fun P hP => ha P (Or.inl hP)
    let haJ :=
      fun P hP => ha P (Or.inr hP)
    let haIJ :=
      fun P hP => ha P (P.prime.dvd_mul.mp hP)
    idealPowerResidueSymbol K (I * J) (mul_ne_zero hI hJ)
        n hmu a hcoprimeIJ haIJ =
      idealPowerResidueSymbol K I hI n hmu a hcoprimeI haI *
        idealPowerResidueSymbol K J hJ n hmu a hcoprimeJ haJ := by
  dsimp only
  rw [idealPowerResidueSymbol_eq_finprod,
    idealPowerResidueSymbol_eq_finprod,
    idealPowerResidueSymbol_eq_finprod]
  rw [← finprod_mul_distrib
    (idealPowerResidueFactor_hasFiniteMulSupport
      K I hI n hmu a _ _)
    (idealPowerResidueFactor_hasFiniteMulSupport
      K J hJ n hmu a _ _)]
  apply finprod_congr
  intro P
  exact idealPowerResidueFactor_mul
    K I J hI hJ n hmu a hcoprime ha P

open scoped Classical in
/-- Unfolded finite-product form of the ideal power residue symbol. -/
theorem idealPowerResidueSymbol_eq_prod
    (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a : 𝓞 K)
    (hcoprime :
      ∀ P : HeightOneSpectrum (𝓞 K),
        P.asIdeal ∣ I →
          (Ideal.absNorm P.asIdeal).Coprime (n : ℕ))
    (ha :
      ∀ P : HeightOneSpectrum (𝓞 K),
        P.asIdeal ∣ I → a ∉ P.asIdeal) :
    letI : Fintype
        (idealPrimeDivisors K I) :=
      (idealPrimeDivisors_finite K I hI).fintype
    idealPowerResidueSymbol K I hI n hmu a hcoprime ha =
      ∏ P : idealPrimeDivisors K I,
        primeIdealPowerResidueSymbol K P.1 n hmu
            (hcoprime P.1 ((mem_idealPrimeDivisors K I P.1).mp P.2)) a
            (ha P.1 ((mem_idealPrimeDivisors K I P.1).mp P.2)) ^
          idealPrimeMultiplicity K P.1 I :=
  rfl

open scoped Classical in
/-- Multiplicativity of the ideal power residue symbol in the numerator. -/
theorem idealPowerResidueSymbol_mul
    (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a b : 𝓞 K)
    (hcoprime :
      ∀ P : HeightOneSpectrum (𝓞 K),
        P.asIdeal ∣ I →
          (Ideal.absNorm P.asIdeal).Coprime (n : ℕ))
    (ha :
      ∀ P : HeightOneSpectrum (𝓞 K),
        P.asIdeal ∣ I → a ∉ P.asIdeal)
    (hb :
      ∀ P : HeightOneSpectrum (𝓞 K),
        P.asIdeal ∣ I → b ∉ P.asIdeal) :
    idealPowerResidueSymbol K I hI n hmu (a * b) hcoprime
        (fun P hP hab =>
          (P.isPrime.mem_or_mem hab).elim (ha P hP) (hb P hP)) =
      idealPowerResidueSymbol K I hI n hmu a hcoprime ha *
        idealPowerResidueSymbol K I hI n hmu b hcoprime hb := by
  classical
  let : Fintype
      (idealPrimeDivisors K I) :=
    (idealPrimeDivisors_finite K I hI).fintype
  unfold idealPowerResidueSymbol
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro P _
  rw [primeIdealPowerResidueSymbol_mul, mul_pow]

end PowerResidueSymbols
end AlgebraicNumberTheory
