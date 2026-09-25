/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.Localization.AsSubring
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Ramification.RationalPrime
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.Basic
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.LocalizationRamificationGroups
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.PadicLocalization
/-!
# The global valuation/prime-ideal bridge in the global cyclotomic inertia argument

An extension `w` of the rational `p`-adic absolute value determines a
valuation subring of a number field `M`.  This file synchronizes that
valuation subring with a concrete prime ideal of `𝓞 M`, proves that the
prime lies over `(p)`, and identifies the valuation subring with the
localization of `𝓞 M` at that prime.

The final comparison sends ideal-theoretic inertia injectively to the
valuation-subring inertia group.  Thus the local cardinality bound furnished
by
  the localization and decomposition comparison applies to the chosen global prime without an
    extra compatibility
hypothesis.
-/

@[expose] public section

open _root_.ValuationTheory.DiscreteValuationField.Valuation renaming
  valuationSubring_eq_of_le_of_mem_maximalIdeal_iff →
    valuationSubring_eq_of_le_of_mem_maximalIdeal_iff


noncomputable
section

namespace HilbertRamification.Dedekind

open NumberField
open AlgebraicNumberTheory.Valuations
open AlgebraicNumberTheory.Ramification
open scoped NumberField

variable (p : ℕ) [Fact p.Prime]
variable (M : Type) [Field M] [NumberField M] [IsAbelianGalois ℚ M]

/-- The localization of a Dedekind domain at a nonzero prime, realized
inside its fraction field as a valuation subring.  This construction belongs
to the ideal/localization bridge; it is kept private here until that bridge
is factored into prime-decomposition theory. -/
def dedekindAtPrimeValuationSubring
    (B : Type*) [CommRing B] [IsDedekindDomain B]
    {L : Type*} [Field L] [Algebra B L] [IsFractionRing B L]
    (P : Ideal B) [P.IsPrime] (hP : P ≠ ⊥) :
    _root_.ValuationSubring L := by
  let S := Localization.subalgebra L P.primeCompl
    P.primeCompl_le_nonZeroDivisors
  letI : IsLocalization P.primeCompl S := by
    dsimp [S]
    infer_instance
  letI : IsDiscreteValuationRing S :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      B hP S
  refine _root_.ValuationSubring.ofSubring S.toSubring ?_
  intro x
  obtain ⟨a, ha | ha⟩ :=
    (ValuationRing.isFractionRing_iff.mp
      (inferInstance : IsFractionRing S L)).1 x
  · left
    rw [ha]
    exact a.property
  · right
    rw [ha]
    exact a.property

/-- The valuation-subring realization of a Dedekind localization carries its
canonical algebra structure over the original domain. -/
noncomputable instance dedekindAtPrimeValuationSubringAlgebra
    (B : Type*) [CommRing B] [IsDedekindDomain B]
    {L : Type*} [Field L] [Algebra B L] [IsFractionRing B L]
    (P : Ideal B) [P.IsPrime] (hP : P ≠ ⊥) :
    Algebra B (dedekindAtPrimeValuationSubring B (L := L) P hP) := by
  change Algebra B
    (Localization.subalgebra L P.primeCompl
      P.primeCompl_le_nonZeroDivisors)
  infer_instance

/-- The valuation-subring realization is the localization away from the
chosen prime. -/
instance dedekindAtPrimeValuationSubringIsLocalization
    (B : Type*) [CommRing B] [IsDedekindDomain B]
    {L : Type*} [Field L] [Algebra B L] [IsFractionRing B L]
    (P : Ideal B) [P.IsPrime] (hP : P ≠ ⊥) :
    IsLocalization P.primeCompl
      (dedekindAtPrimeValuationSubring B (L := L) P hP) := by
  change IsLocalization P.primeCompl
    (Localization.subalgebra L P.primeCompl
      P.primeCompl_le_nonZeroDivisors)
  infer_instance

/-- A Dedekind localization realized as a valuation subring is again a
Dedekind domain. -/
instance dedekindAtPrimeValuationSubringIsDedekindDomain
    (B : Type*) [CommRing B] [IsDedekindDomain B]
    {L : Type*} [Field L] [Algebra B L] [IsFractionRing B L]
    (P : Ideal B) [P.IsPrime] (hP : P ≠ ⊥) :
    IsDedekindDomain
      (dedekindAtPrimeValuationSubring B (L := L) P hP) :=
  IsLocalization.AtPrime.isDedekindDomain B P
    (dedekindAtPrimeValuationSubring B (L := L) P hP)

/-- The valuation-subring realization of a nonzero Dedekind localization has
Krull dimension at most one. -/
instance dedekindAtPrimeValuationSubringKrullDimLE
    (B : Type*) [CommRing B] [IsDedekindDomain B]
    {L : Type*} [Field L] [Algebra B L] [IsFractionRing B L]
    (P : Ideal B) [P.IsPrime] (hP : P ≠ ⊥) :
    Ring.KrullDimLE 1
      (dedekindAtPrimeValuationSubring B (L := L) P hP) :=
  Ring.KrullDimLE.mk₁' (fun _ a _ => IsPrime.to_maximal_ideal a)

/-- The nonarchimedean extension valuation ring attached to a global
extension of the rational `p`-adic absolute value. -/
abbrev globalPadicExtensionValuationSubring
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) M) :
    _root_.ValuationSubring M :=
  HilbertRamification.absoluteValueExtensionValuationSubring
    (Rat.AbsoluteValue.padic p) w
    (HilbertRamification.absoluteValueExtension_nonarchimedean_of_base
      (Rat.AbsoluteValue.padic p) w
      (rationalPadicAbsoluteValue_nonarchimedean p))

omit [IsAbelianGalois ℚ M] in
/-- Every algebraic integer belongs to the valuation ring defined by `w`.
This is the integrally-closed valuation-ring argument, rather than an
additional boundedness assumption on algebraic integers. -/
theorem ringOfIntegers_mem_globalPadicExtensionValuationSubring
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) M)
    (x : 𝓞 M) :
    (x : M) ∈ globalPadicExtensionValuationSubring p M w := by
  let A := globalPadicExtensionValuationSubring p M w
  change (x : M) ∈ A
  rw [← A.valuationSubring_valuation]
  exact Valuation.Integers.mem_of_integral
    (Valuation.valuationSubring.integers (v := A.valuation))
    (IsIntegral.tower_top
      (A := A.valuation.valuationSubring) x.property)

/-- The canonical inclusion `𝓞 M → A_w`. -/
def globalPadicRingOfIntegersToExtensionValuationSubring
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) M) :
    𝓞 M →+* globalPadicExtensionValuationSubring p M w :=
  RingHom.codRestrict (algebraMap (𝓞 M) M)
    (globalPadicExtensionValuationSubring p M w).toSubring
    (ringOfIntegers_mem_globalPadicExtensionValuationSubring p M w)

omit [IsAbelianGalois ℚ M] in
/-- The canonical map from `𝓞 M` to the extension valuation ring agrees with
the usual inclusion into `M`. -/
@[simp] theorem globalPadicRingOfIntegersToExtensionValuationSubring_coe
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) M)
    (x : 𝓞 M) :
    ((globalPadicRingOfIntegersToExtensionValuationSubring p M w x :
        globalPadicExtensionValuationSubring p M w) : M) = (x : M) :=
  rfl

/-- The prime ideal of `𝓞 M` which is the center of `w`. -/
def globalPadicPrimeIdeal
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) M) :
    Ideal (𝓞 M) :=
  (IsLocalRing.maximalIdeal
      (globalPadicExtensionValuationSubring p M w)).comap
    (globalPadicRingOfIntegersToExtensionValuationSubring p M w)

omit [IsAbelianGalois ℚ M] in
/-- Membership in the synchronized prime is the strict `w`-adic
inequality. -/
theorem mem_globalPadicPrimeIdeal_iff
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) M)
    (x : 𝓞 M) :
    x ∈ globalPadicPrimeIdeal p M w ↔ w.1 (x : M) < 1 := by
  let A := globalPadicExtensionValuationSubring p M w
  let f := globalPadicRingOfIntegersToExtensionValuationSubring p M w
  change f x ∈ IsLocalRing.maximalIdeal A ↔ w.1 (x : M) < 1
  simpa [A, f] using
    (absoluteValueValuationSubring_mem_maximalIdeal_iff_abs_lt_one
      w.1
      (HilbertRamification.absoluteValueExtension_nonarchimedean_of_base
        (Rat.AbsoluteValue.padic p) w
        (rationalPadicAbsoluteValue_nonarchimedean p))
      (f x))

omit [IsAbelianGalois ℚ M] in
/-- The center of a valuation ring is prime. -/
theorem globalPadicPrimeIdeal_isPrime
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) M) :
    (globalPadicPrimeIdeal p M w).IsPrime := by
  unfold globalPadicPrimeIdeal
  exact Ideal.comap_isPrime _ _

omit [IsAbelianGalois ℚ M] in
/-- On rational integers, membership in the center is divisibility by `p`. -/
theorem int_mem_globalPadicPrimeIdeal_under_iff
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) M)
    (z : ℤ) :
    algebraMap ℤ (𝓞 M) z ∈ globalPadicPrimeIdeal p M w ↔
      (p : ℤ) ∣ z := by
  rw [mem_globalPadicPrimeIdeal_iff]
  have hz :
      ((algebraMap ℤ (𝓞 M) z : 𝓞 M) : M) =
        algebraMap ℚ M (z : ℚ) := by
    simp
  rw [hz, w.2]
  change (((padicNorm p (z : ℚ) : ℚ) : ℝ) < 1) ↔ (p : ℤ) ∣ z
  exact_mod_cast padicNorm.int_lt_one_iff (p := p) z

omit [IsAbelianGalois ℚ M] in
/-- The contraction of the synchronized prime to `ℤ` is the usual
principal ideal `(p)`. -/
theorem globalPadicPrimeIdeal_under_eq_span
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) M) :
    (globalPadicPrimeIdeal p M w).under ℤ =
      Ideal.span ({(p : ℤ)} : Set ℤ) := by
  ext z
  change algebraMap ℤ (𝓞 M) z ∈ globalPadicPrimeIdeal p M w ↔ _
  rw [int_mem_globalPadicPrimeIdeal_under_iff, Ideal.mem_span_singleton]

omit [IsAbelianGalois ℚ M] in
/-- The synchronized prime lies over the rational height-one prime `p`. -/
theorem globalPadicPrimeIdeal_liesOver
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) M) :
    (globalPadicPrimeIdeal p M w).LiesOver
      (rationalPrimeIdeal (⟨p, Fact.out⟩ : Nat.Primes)) := by
  constructor
  exact
    (rationalPrimeIdeal_eq_span (⟨p, Fact.out⟩ : Nat.Primes)).trans
      (globalPadicPrimeIdeal_under_eq_span p M w).symm

omit [IsAbelianGalois ℚ M] in
/-- The synchronized prime is nonzero. -/
theorem globalPadicPrimeIdeal_ne_bot
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) M) :
    globalPadicPrimeIdeal p M w ≠ ⊥ := by
  let : (globalPadicPrimeIdeal p M w).LiesOver
      (rationalPrimeIdeal (⟨p, Fact.out⟩ : Nat.Primes)) :=
    globalPadicPrimeIdeal_liesOver p M w
  apply Ideal.ne_bot_of_liesOver_of_ne_bot
    (p := rationalPrimeIdeal (⟨p, Fact.out⟩ : Nat.Primes))
  exact (Rat.HeightOneSpectrum.primesEquiv.symm
    (⟨p, Fact.out⟩ : Nat.Primes)).ne_bot

omit [IsAbelianGalois ℚ M] in
/-- In the Dedekind ring `𝓞 M`, the synchronized nonzero prime is maximal. -/
theorem globalPadicPrimeIdeal_isMaximal
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) M) :
    (globalPadicPrimeIdeal p M w).IsMaximal :=
  (globalPadicPrimeIdeal_isPrime p M w).isMaximal
    (globalPadicPrimeIdeal_ne_bot p M w)

/-- The center of a global `p`-adic place is a prime ideal. -/
instance instIsPrimeGlobalPadicPrimeIdeal
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) M) :
    (globalPadicPrimeIdeal p M w).IsPrime :=
  globalPadicPrimeIdeal_isPrime p M w

/-- The center of a global `p`-adic place is a maximal ideal. -/
instance instIsMaximalGlobalPadicPrimeIdeal
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) M) :
    (globalPadicPrimeIdeal p M w).IsMaximal :=
  globalPadicPrimeIdeal_isMaximal p M w

/-- The center of a global `p`-adic place lies over the rational prime
ideal generated by `p`. -/
instance instLiesOverGlobalPadicPrimeIdeal
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) M) :
    (globalPadicPrimeIdeal p M w).LiesOver
      (rationalPrimeIdeal ⟨p, Fact.out⟩) :=
  globalPadicPrimeIdeal_liesOver p M w

/-- The height-one prime of `𝓞 M` centered at `w`. -/
def globalPadicPrimeHeightOneSpectrum
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) M) :
    IsDedekindDomain.HeightOneSpectrum (𝓞 M) :=
  ⟨globalPadicPrimeIdeal p M w,
    globalPadicPrimeIdeal_isPrime p M w,
    globalPadicPrimeIdeal_ne_bot p M w⟩

/-- The ordinary localization of `𝓞 M` at the prime centered at `w`, viewed
as a valuation subring of `M`. -/
abbrev globalPadicPrimeLocalizationValuationSubring
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) M) :
    _root_.ValuationSubring M :=
  dedekindAtPrimeValuationSubring (𝓞 M) (L := M)
    (globalPadicPrimeIdeal p M w)
    (globalPadicPrimeIdeal_ne_bot p M w)

omit [IsAbelianGalois ℚ M] in
/-- The valuation ring defined by the absolute value `w` is exactly the
ordinary localization of `𝓞 M` at its center. -/
theorem globalPadicPrime_localizationValuationSubring_eq
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) M) :
    globalPadicPrimeLocalizationValuationSubring p M w =
      globalPadicExtensionValuationSubring p M w := by
  let P := globalPadicPrimeIdeal p M w
  let V := dedekindAtPrimeValuationSubring (𝓞 M) (L := M) P
    (globalPadicPrimeIdeal_ne_bot p M w)
  let A := globalPadicExtensionValuationSubring p M w
  change V = A
  have hVA : V ≤ A := by
    rintro x ⟨a, s, hs, rfl⟩
    have hs0 : s ≠ 0 := by
      intro hsZero
      apply hs
      simp [hsZero]
    have hsM0 : (s : M) ≠ 0 := by
      simpa only [map_zero] using
        (IsFractionRing.injective (𝓞 M) M).ne hs0
    have hmk :
        IsLocalization.mk' M a
            ⟨s, P.primeCompl_le_nonZeroDivisors hs⟩ =
          (a : M) / (s : M) := by
      apply (mul_right_cancel₀ hsM0)
      rw [IsLocalization.mk'_spec]
      exact (div_mul_cancel₀ _ hsM0).symm
    have haA : (a : M) ∈ A :=
      ringOfIntegers_mem_globalPadicExtensionValuationSubring p M w a
    have hsA : (s : M) ∈ A :=
      ringOfIntegers_mem_globalPadicExtensionValuationSubring p M w s
    have haLe : w.1 (a : M) ≤ 1 :=
      (mem_absoluteValueValuationSubring_iff
        w.1
        (HilbertRamification.absoluteValueExtension_nonarchimedean_of_base
          (Rat.AbsoluteValue.padic p) w
          (rationalPadicAbsoluteValue_nonarchimedean p))
        (a : M)).mp haA
    have hsLe : w.1 (s : M) ≤ 1 :=
      (mem_absoluteValueValuationSubring_iff
        w.1
        (HilbertRamification.absoluteValueExtension_nonarchimedean_of_base
          (Rat.AbsoluteValue.padic p) w
          (rationalPadicAbsoluteValue_nonarchimedean p))
        (s : M)).mp hsA
    have hsNotLt : ¬w.1 (s : M) < 1 := by
      intro hlt
      apply hs
      exact (mem_globalPadicPrimeIdeal_iff p M w s).mpr hlt
    have hsEq : w.1 (s : M) = 1 :=
      le_antisymm hsLe (not_lt.mp hsNotLt)
    rw [mem_absoluteValueValuationSubring_iff]
    rw [hmk, map_div₀, hsEq, div_one]
    exact haLe
  apply
    (valuationSubring_eq_of_le_of_mem_maximalIdeal_iff
      V A hVA ?_).symm
  intro x
  rcases x.property with ⟨a, s, hs, hx⟩
  have hs0 : s ≠ 0 := by
    intro hsZero
    apply hs
    simp [hsZero]
  have hsM0 : (s : M) ≠ 0 := by
    simpa only [map_zero] using
      (IsFractionRing.injective (𝓞 M) M).ne hs0
  have hmk :
      IsLocalization.mk' M a
          ⟨s, P.primeCompl_le_nonZeroDivisors hs⟩ =
        (a : M) / (s : M) := by
    apply (mul_right_cancel₀ hsM0)
    rw [IsLocalization.mk'_spec]
    exact (div_mul_cancel₀ _ hsM0).symm
  have hsA : (s : M) ∈ A :=
    ringOfIntegers_mem_globalPadicExtensionValuationSubring p M w s
  have hsLe : w.1 (s : M) ≤ 1 :=
    (mem_absoluteValueValuationSubring_iff
      w.1
      (HilbertRamification.absoluteValueExtension_nonarchimedean_of_base
        (Rat.AbsoluteValue.padic p) w
        (rationalPadicAbsoluteValue_nonarchimedean p))
      (s : M)).mp hsA
  have hsNotLt : ¬w.1 (s : M) < 1 := by
    intro hlt
    apply hs
    exact (mem_globalPadicPrimeIdeal_iff p M w s).mpr hlt
  have hsEq : w.1 (s : M) = 1 :=
    le_antisymm hsLe (not_lt.mp hsNotLt)
  have hxmk : x = IsLocalization.mk' V a ⟨s, hs⟩ := by
    rw [IsLocalization.eq_mk'_iff_mul_eq]
    apply V.subtype_injective
    change (x : M) * (s : M) = (a : M)
    rw [hx]
    simp [hsM0]
  have hright :
      x ∈ IsLocalRing.maximalIdeal V ↔ a ∈ P := by
    rw [hxmk]
    exact IsLocalization.AtPrime.mk'_mem_maximal_iff V P a ⟨s, hs⟩
  rw [hright]
  have hleft :
      V.inclusion A hVA x ∈ IsLocalRing.maximalIdeal A ↔
        w.1 (x : M) < 1 := by
    have hcoe :
        ((V.inclusion A hVA x : A) : M) = (x : M) := rfl
    simpa [A, hcoe] using
      (absoluteValueValuationSubring_mem_maximalIdeal_iff_abs_lt_one
        w.1
        (HilbertRamification.absoluteValueExtension_nonarchimedean_of_base
          (Rat.AbsoluteValue.padic p) w
          (rationalPadicAbsoluteValue_nonarchimedean p))
        (V.inclusion A hVA x))
  rw [hleft, hx, hmk, map_div₀, hsEq, div_one]
  exact (mem_globalPadicPrimeIdeal_iff p M w a).symm

/-! ## Comparison of ideal inertia with valuation inertia -/

omit [IsAbelianGalois ℚ M] in
private theorem globalPadicPrimeCompl_smul_of_mem_inertia
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) M)
    (sigma : HilbertRamification.Dedekind.inertiaGroup
      (globalPadicPrimeIdeal p M w) (M ≃ₐ[ℚ] M))
    {s : 𝓞 M}
    (hs : s ∈ (globalPadicPrimeIdeal p M w).primeCompl) :
    (sigma : M ≃ₐ[ℚ] M) • s ∈
      (globalPadicPrimeIdeal p M w).primeCompl := by
  intro hsigma
  apply hs
  have hdiff :
      (sigma : M ≃ₐ[ℚ] M) • s - s ∈
        globalPadicPrimeIdeal p M w := sigma.property s
  have hmem :=
    (globalPadicPrimeIdeal p M w).sub_mem hsigma hdiff
  simpa using hmem

omit [IsAbelianGalois ℚ M] in
/-- An ideal-inertia automorphism preserves the localization of `𝓞 M` at
the synchronized prime. -/
private theorem globalPadicIdealInertia_maps_localization
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) M)
    (sigma : HilbertRamification.Dedekind.inertiaGroup
      (globalPadicPrimeIdeal p M w) (M ≃ₐ[ℚ] M))
    {x : M}
    (hx : x ∈
      globalPadicPrimeLocalizationValuationSubring p M w) :
    (sigma : M ≃ₐ[ℚ] M) x ∈
      globalPadicPrimeLocalizationValuationSubring p M w := by
  rcases hx with ⟨a, s, hs, rfl⟩
  have hs0 : s ≠ 0 := by
    intro hsZero
    apply hs
    simp [hsZero]
  have hsM0 : (s : M) ≠ 0 := by
    simpa only [map_zero] using
      (IsFractionRing.injective (𝓞 M) M).ne hs0
  have hsigmaM0 :
      (sigma : M ≃ₐ[ℚ] M) (s : M) ≠ 0 := by
    simpa only [map_zero] using
      (sigma : M ≃ₐ[ℚ] M).injective.ne hsM0
  refine ⟨(sigma : M ≃ₐ[ℚ] M) • a,
    (sigma : M ≃ₐ[ℚ] M) • s,
    globalPadicPrimeCompl_smul_of_mem_inertia p M w sigma hs, ?_⟩
  rw [IsLocalization.eq_mk'_iff_mul_eq]
  rw [IsFractionRing.mk'_eq_div, map_div₀]
  exact div_mul_cancel₀ _ hsigmaM0

omit [IsAbelianGalois ℚ M] in
/-- Ideal inertia at the synchronized prime maps to the decomposition group
of its localization. -/
def globalPadicIdealInertiaToLocalizationDecomposition
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) M) :
    HilbertRamification.Dedekind.inertiaGroup
        (globalPadicPrimeIdeal p M w) (M ≃ₐ[ℚ] M) →
      RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup ℚ
        (globalPadicPrimeLocalizationValuationSubring p M w) := by
  intro sigma
  let V := globalPadicPrimeLocalizationValuationSubring p M w
  exact ⟨(sigma : M ≃ₐ[ℚ] M), by
    ext x
    rw [_root_.ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    constructor
    · intro hx
      have h := globalPadicIdealInertia_maps_localization p M w sigma hx
      simpa [AlgEquiv.smul_def] using h
    · intro hx
      simpa [AlgEquiv.smul_def] using
        (globalPadicIdealInertia_maps_localization p M w sigma⁻¹ hx)⟩

omit [IsAbelianGalois ℚ M] in
private theorem
    globalPadicIdealInertiaToLocalizationDecomposition_mem_maximalIdealInertia
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) M)
    (sigma : HilbertRamification.Dedekind.inertiaGroup
      (globalPadicPrimeIdeal p M w) (M ≃ₐ[ℚ] M)) :
    globalPadicIdealInertiaToLocalizationDecomposition p M w sigma ∈
      (IsLocalRing.maximalIdeal
        (globalPadicPrimeLocalizationValuationSubring p M w)).toAddSubgroup.inertia
        (RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup ℚ
          (globalPadicPrimeLocalizationValuationSubring p M w)) := by
  let P := globalPadicPrimeIdeal p M w
  let V := globalPadicPrimeLocalizationValuationSubring p M w
  let delta : RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup ℚ V :=
    globalPadicIdealInertiaToLocalizationDecomposition p M w sigma
  intro x
  rcases x.property with ⟨a, s, hs, hx⟩
  have hs0 : s ≠ 0 := by
    intro hsZero
    apply hs
    simp [hsZero]
  have hdeltaA : (sigma : M ≃ₐ[ℚ] M) • a - a ∈ P :=
    sigma.property a
  have hdeltaS : (sigma : M ≃ₐ[ℚ] M) • s - s ∈ P :=
    sigma.property s
  have hsigma : (sigma : M ≃ₐ[ℚ] M) • s ∈ P.primeCompl :=
    globalPadicPrimeCompl_smul_of_mem_inertia p M w sigma hs
  have hsM0 : (s : M) ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective (𝓞 M) M).ne hs0
  have hsigmaM0 :
      (sigma : M ≃ₐ[ℚ] M) (s : M) ≠ 0 := by
    simpa only [map_zero] using
      (sigma : M ≃ₐ[ℚ] M).injective.ne hsM0
  have hxmk : x = IsLocalization.mk' V a ⟨s, hs⟩ := by
    rw [IsLocalization.eq_mk'_iff_mul_eq]
    apply V.subtype_injective
    change (x : M) * (s : M) = (a : M)
    rw [hx]
    simp [hsM0]
  have hdeltaxmk : delta • x =
      IsLocalization.mk' V ((sigma : M ≃ₐ[ℚ] M) • a)
        ⟨(sigma : M ≃ₐ[ℚ] M) • s, hsigma⟩ := by
    rw [IsLocalization.eq_mk'_iff_mul_eq]
    apply V.subtype_injective
    change
      (sigma : M ≃ₐ[ℚ] M) (x : M) *
          (((sigma : M ≃ₐ[ℚ] M) • s : 𝓞 M) : M) =
        (((sigma : M ≃ₐ[ℚ] M) • a : 𝓞 M) : M)
    rw [hx, IsFractionRing.mk'_eq_div, map_div₀]
    exact div_mul_cancel₀ _ hsigmaM0
  have hnum :
      (sigma : M ≃ₐ[ℚ] M) • a * s -
          a * ((sigma : M ≃ₐ[ℚ] M) • s) ∈ P := by
    have h := P.sub_mem
      (P.mul_mem_right s hdeltaA)
      (P.mul_mem_left a hdeltaS)
    convert h using 1; ring
  let den : P.primeCompl :=
    ⟨((sigma : M ≃ₐ[ℚ] M) • s) * s,
      P.primeCompl.mul_mem hsigma hs⟩
  have hfrac : IsLocalization.mk' V
        ((sigma : M ≃ₐ[ℚ] M) • a * s -
          a * ((sigma : M ≃ₐ[ℚ] M) • s)) den ∈
      IsLocalRing.maximalIdeal V :=
    (IsLocalization.AtPrime.mk'_mem_maximal_iff V P _ den).mpr hnum
  rw [hdeltaxmk, hxmk, ← IsLocalization.mk'_sub]
  exact hfrac

omit [IsAbelianGalois ℚ M] in
private theorem
    globalPadicIdealInertiaToLocalizationDecomposition_mem_inertia
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) M)
    (sigma : HilbertRamification.Dedekind.inertiaGroup
      (globalPadicPrimeIdeal p M w) (M ≃ₐ[ℚ] M)) :
    globalPadicIdealInertiaToLocalizationDecomposition p M w sigma ∈
      RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup ℚ
        (globalPadicPrimeLocalizationValuationSubring p M w) := by
  let V := globalPadicPrimeLocalizationValuationSubring p M w
  let delta : RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup ℚ V :=
    globalPadicIdealInertiaToLocalizationDecomposition p M w sigma
  rw [HilbertRamification.ValuationSubring.mem_inertiaGroup_iff_sub_mem_nonunits]
  intro x
  change (((delta • x - x : V) : M) ∈ V.nonunits)
  exact V.coe_mem_nonunits_iff.mpr
    (globalPadicIdealInertiaToLocalizationDecomposition_mem_maximalIdealInertia
      p M w sigma x)

omit [IsAbelianGalois ℚ M] in
/-- The canonical localization map from global ideal inertia to valuation
inertia. -/
def globalPadicIdealInertiaToLocalizationInertia
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) M) :
    HilbertRamification.Dedekind.inertiaGroup
        (globalPadicPrimeIdeal p M w) (M ≃ₐ[ℚ] M) →*
      RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup ℚ
        (globalPadicPrimeLocalizationValuationSubring p M w) where
  toFun sigma :=
    ⟨globalPadicIdealInertiaToLocalizationDecomposition p M w sigma,
      by exact globalPadicIdealInertiaToLocalizationDecomposition_mem_inertia p M w sigma⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_mul' _ _ := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

omit [IsAbelianGalois ℚ M] in
/-- The localization map is injective because it does not change the
underlying `ℚ`-automorphism of `M`. -/
theorem globalPadicIdealInertiaToLocalizationInertia_injective
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) M) :
    Function.Injective
      (globalPadicIdealInertiaToLocalizationInertia p M w) := by
  intro sigma tau h
  have h1 := congrArg Subtype.val h
  have h2 := congrArg Subtype.val h1
  apply Subtype.ext
  exact h2

omit [IsAbelianGalois ℚ M] in
/-- The exact cardinal comparison needed in the global cyclotomic inertia argument: the ideal
inertia group
at the synchronized prime is no larger than the localization and decomposition comparison
  valuation inertia
group attached to `w`. -/
theorem globalPadicPrimeIdeal_inertia_natCard_le_valuationInertia
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) M) :
    Nat.card
        (HilbertRamification.Dedekind.inertiaGroup
          (globalPadicPrimeIdeal p M w) (M ≃ₐ[ℚ] M)) ≤
      Nat.card
        (RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup ℚ
          (globalPadicExtensionValuationSubring p M w)) := by
  have h := Nat.card_le_card_of_injective
    (globalPadicIdealInertiaToLocalizationInertia p M w)
    (globalPadicIdealInertiaToLocalizationInertia_injective p M w)
  rw [globalPadicPrime_localizationValuationSubring_eq p M w] at h
  exact h

end HilbertRamification.Dedekind

end
