/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.Localization.Cardinality

/-!
# N-subrings and A-extensions

An N-subring of a complete local domain (T, M) is a quasi-local
UFD subring satisfying a height condition on associated primes.
An A-extension preserves primality and cardinality bounds.

* Heitmann, "Characterization of completions of UFDs", 1993.
* Jensen, "Completions of UFDs with semi-local formal fibers", 2006.
-/

noncomputable section

open Cardinal Ideal

/-!
## N-subring definition

For T a complete local domain, the N-subring conditions simplify:
- Condition (2) (Q ∩ R = (0) for Q ∈ Ass(T)) is automatic since
  Ass(T) = {(0)} and R ⊆ T domain.
- Condition (3): for every regular t ∈ T and P ∈ Ass(T/tT), ht(P ∩ R) ≤ 1.
-/

variable {T : Type*} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsDomain T]

/-- An N-subring of a complete local domain (T, M).
This is a quasi-local UFD R ⊆ T with bounded cardinality and a height condition
on associated primes of principal ideals. -/
structure NSubring (T : Type*) [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsDomain T] where
  /-- The underlying subring of T -/
  carrier : Subring T
  /-- R is a UFD -/
  isUFD : UniqueFactorizationMonoid carrier
  /-- R is a local ring (quasi-local with M ∩ R as maximal ideal) -/
  isLocalRing : IsLocalRing carrier
  /-- |R| ≤ max(ℵ₀, |T/M|) -/
  card_le : Cardinal.mk carrier ≤ max Cardinal.aleph0 (Cardinal.mk (IsLocalRing.ResidueField T))
  /-- The maximal ideal of R equals the contraction of M to R.
  This ensures R is "centered on M" — prime elements of R land in M. -/
  maximal_ideal_eq : IsLocalRing.maximalIdeal carrier =
    (IsLocalRing.maximalIdeal T).comap carrier.subtype
  /-- For every nonzero t ∈ T and P ∈ Ass(T/tT), ht(P ∩ R) ≤ 1.
  This is the key condition ensuring that primes of T interact well with R. -/
  height_bound : ∀ (t : T), t ≠ 0 →
    ∀ P ∈ associatedPrimes T (T ⧸ Ideal.span {t}),
      Ideal.height (P.comap carrier.subtype) ≤ 1

namespace NSubring

instance (N : NSubring T) : UniqueFactorizationMonoid N.carrier := N.isUFD
instance (N : NSubring T) : IsLocalRing N.carrier := N.isLocalRing

/-- Coercion: an N-subring is a subring of T. -/
instance : CoeOut (NSubring T) (Subring T) := ⟨NSubring.carrier⟩

/-- An N-subring of a domain is itself a domain (as a subring of a domain). -/
instance isDomain (N : NSubring T) : IsDomain N.carrier := inferInstance

end NSubring

/-!
## A-extension

An A-extension S of an N-subring R is a larger N-subring where prime elements
of R remain prime in S, and |S| ≤ max(ℵ₀, |R|).
-/

/-- S is an A-extension of R if R ≤ S, primes of R remain prime in S,
and the cardinality of S is bounded by max(ℵ₀, |R|). -/
structure IsAExtension (R S : NSubring T) : Prop where
  /-- R is contained in S -/
  le : R.carrier ≤ S.carrier
  /-- Prime elements of R remain prime in S.
  Expressed via the canonical embedding: if r ∈ R is prime, then its image in S is prime. -/
  primes_preserved : ∀ (r : R.carrier), Prime r →
    Prime (⟨r.1, le r.2⟩ : S.carrier)
  /-- |S| ≤ max(ℵ₀, |R|) -/
  card_le : Cardinal.mk S.carrier ≤ max Cardinal.aleph0 (Cardinal.mk R.carrier)

/-!
## Initial N-subring

For T a complete local domain with depth ≥ 2, char 0, and no integer zero divisor,
the prime subring (image of ℤ) localized at M ∩ (prime subring) gives an N-subring.
In characteristic 0 over ℂ, this is essentially ℚ embedded in T.
-/

/-- The prime subring of T (image of ℤ → T), localized at its intersection with M,
is an N-subring when T has depth ≥ 2 and no integer is a zero divisor. -/
theorem initial_NSubring
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    (hchar : ∀ (n : ℤ), n ≠ 0 → (algebraMap ℤ T n) ≠ 0) :
    ∃ N : NSubring T, Cardinal.mk N.carrier ≤ Cardinal.aleph0 := by
  set p : Ideal ℤ := (IsLocalRing.maximalIdeal T).comap (algebraMap ℤ T) with hp_def
  have hp : p.IsPrime := (IsLocalRing.maximalIdeal.isMaximal T).isPrime.comap (algebraMap ℤ T)
  have hunits : ∀ (y : p.primeCompl), IsUnit ((algebraMap ℤ T) ↑y) := by
    intro ⟨y, hy⟩
    exact (IsLocalRing.notMem_maximalIdeal).mp (fun hmem => hy (Ideal.mem_comap.mpr hmem))
  let φ : Localization.AtPrime p →+* T := IsLocalization.lift hunits
  have hinj_T : Function.Injective (algebraMap ℤ T) := by
    intro a b hab
    by_contra hne
    exact hchar (a - b) (sub_ne_zero.mpr hne) (by rwa [map_sub, sub_eq_zero])
  have hφ_inj : Function.Injective φ := by
    rw [IsLocalization.lift_injective_iff]
    have hinj_loc : Function.Injective (algebraMap ℤ (Localization.AtPrime p)) :=
      IsLocalization.injective _ (Ideal.primeCompl_le_nonZeroDivisors p)
    exact fun x y => ⟨fun h => congrArg _ (hinj_loc h), fun h => congrArg _ (hinj_T h)⟩
  have _ : IsDomain (Localization.AtPrime p) :=
    IsLocalization.isDomain_of_atPrime (Localization.AtPrime p) p
  have _ : IsLocalRing (Localization.AtPrime p) :=
    IsLocalization.AtPrime.isLocalRing (Localization.AtPrime p) p
  have _ : IsDedekindDomain (Localization.AtPrime p) :=
    Localization.AtPrime.isDedekindDomain ℤ p
  have _ : IsPrincipalIdealRing (Localization.AtPrime p) :=
    IsDedekindDomain.isPrincipalIdealRing (Localization.AtPrime p)
  have _ : UniqueFactorizationMonoid (Localization.AtPrime p) :=
    PrincipalIdealRing.to_uniqueFactorizationMonoid
  have hequiv : Localization.AtPrime p ≃+* φ.range :=
    RingEquiv.ofLeftInverse (Function.leftInverse_invFun hφ_inj)
  have _ : UniqueFactorizationMonoid φ.range :=
    hequiv.toMulEquiv.uniqueFactorizationMonoid ‹_›
  have _ : IsLocalRing φ.range := hequiv.isLocalRing
  have _ : IsPrincipalIdealRing φ.range :=
    IsPrincipalIdealRing.of_surjective (R := Localization.AtPrime p) hequiv hequiv.surjective
  have _ : Countable (Localization.AtPrime p) := by
    rw [← Cardinal.mk_le_aleph0_iff]
    calc Cardinal.mk (Localization.AtPrime p)
        = Cardinal.mk ℤ := Localization.cardinalMk (Ideal.primeCompl_le_nonZeroDivisors p)
      _ ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0
  have _ : Countable φ.range := (Set.countable_range φ).to_subtype
  refine ⟨⟨φ.range, ‹UniqueFactorizationMonoid _›, ‹IsLocalRing _›, ?_, ?_, ?_⟩,
    Cardinal.mk_le_aleph0⟩
  · exact le_trans Cardinal.mk_le_aleph0 (le_max_left _ _)
  · ext x
    rw [Ideal.mem_comap]
    constructor
    · intro hx
      rw [IsLocalRing.mem_maximalIdeal] at hx
      rw [IsLocalRing.mem_maximalIdeal]
      intro hux
      apply hx
      obtain ⟨y, hy⟩ := x.2
      obtain ⟨a, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl y
      have ha : a ∈ p.primeCompl := by
        intro ha
        have : (φ.range.subtype x : T) ∈ IsLocalRing.maximalIdeal T := by
          change (x : T) ∈ _
          rw [show (x : T) = φ (IsLocalization.mk' _ a ⟨s, hs⟩) from hy.symm,
              IsLocalization.lift_mk' hunits a ⟨s, hs⟩]
          exact Ideal.mul_mem_right _ _ (Ideal.mem_comap.mp ha)
        exact absurd hux ((IsLocalRing.mem_maximalIdeal _).mp this)
      have hyu : IsUnit (IsLocalization.mk' (Localization.AtPrime p) a ⟨s, hs⟩) :=
        (IsLocalization.AtPrime.isUnit_mk'_iff _ p a ⟨s, hs⟩).mpr ha
      rw [show x = φ.rangeRestrict (IsLocalization.mk' _ a ⟨s, hs⟩) from Subtype.ext hy.symm]
      exact hyu.map φ.rangeRestrict
    · intro hx
      rw [IsLocalRing.mem_maximalIdeal] at hx ⊢
      intro hu
      exact hx (hu.map φ.range.subtype)
  · intro t ht P hP
    have hPprime : P.IsPrime := hP.isPrime
    have _ : (P.comap φ.range.subtype).IsPrime := hPprime.comap _
    have hkd : Ring.KrullDimLE 1 (φ.range : Type _) :=
      @IsPrincipalIdealRing.krullDimLE_one ↥φ.range _ ‹_›
    rw [Ring.krullDimLE_iff] at hkd
    have hht := (ringKrullDim_le_iff_height_le (↑(1 : ℕ))).mp hkd
      ‹(P.comap φ.range.subtype).IsPrime›
    exact_mod_cast hht

/-!
## Basic API
-/

/-- The inclusion map from an N-subring into T. -/
def NSubring.subtype (N : NSubring T) : N.carrier →+* T :=
  N.carrier.subtype

/-- Two N-subrings are equal if their carriers are equal. -/
theorem NSubring.ext {N₁ N₂ : NSubring T} (h : N₁.carrier = N₂.carrier) : N₁ = N₂ := by
  cases N₁
  cases N₂
  congr

end
