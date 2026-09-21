/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Geometry.NormalizationHeightOne
import Mathlib

/-!
# Divisorial visible-frame construction core

This file packages the already checked valuation, DVR, Kähler, and
transcendence stages and states the assembly interface used by the dedicated
normalization, residue-algebraicity, and coefficient-field modules.
-/

open IsLocalRing Polynomial
open Stafford38.Geometry.NormalizationHeightOne

noncomputable section

universe u v

namespace Stafford38.Geometry.LaneC

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

def coeffHom (E : IntermediateField k K) (V : ValuationSubring K)
    (hEV : ∀ z : E, (z : K) ∈ V.toSubring) : E →+* V.toSubring :=
  RingHom.codRestrict (IntermediateField.val E).toRingHom V.toSubring hEV

def groundHom (E : IntermediateField k K) (V : ValuationSubring K)
    (hEV : ∀ z : E, (z : K) ∈ V.toSubring) : k →+* V.toSubring :=
  (coeffHom E V hEV).comp (algebraMap k E)

def DivisorialVisibleFrameExistence : Prop :=
  ∀ (k K : Type u) [Field k] [CharZero k] [Field K] [Algebra k K]
    (r : ℕ) (y : Fin r → K) (i : Fin r),
    IntermediateField.adjoin k (Set.range y) = ⊤ →
    Transcendental k (y i) →
    ∃ (E : IntermediateField k K) (V : ValuationSubring K)
      (hEV : ∀ z : E, (z : K) ∈ V.toSubring)
      (hVdvr : IsDiscreteValuationRing V.toSubring)
      (hxV : y i ∈ V.toSubring),
      letI : IsLocalRing V.toSubring := hVdvr.toIsLocalRing
      letI : Algebra E V.toSubring := (coeffHom E V hEV).toAlgebra
      letI : Algebra k V.toSubring := (groundHom E V hEV).toAlgebra
      Transcendental E (y i) ∧
      (⟨y i, hxV⟩ : V.toSubring) ∈ maximalIdeal V.toSubring ∧
      Module.Finite E (ResidueField V.toSubring) ∧
      Module.Finite V.toSubring (Ω[V.toSubring⁄k]) ∧
      (∀ (s : K) (q : Fin (r + 1) → V.toSubring),
        (∀ a, (q a : K) = s * Fin.cases 1 y a) →
        (∃ j, q j = 1) → ¬ IsUnit (q 0) →
        Algebra.IsAlgebraic
          (IntermediateField.adjoin k
            (Set.range fun j : Fin r ↦ residue V.toSubring (q (Fin.succ j))) :
            IntermediateField k (ResidueField V.toSubring))
          (ResidueField V.toSubring))

/-! The concrete localization model used by the place stage. -/

def placeSubalgebra (A : Subalgebra k K) [IsFractionRing A K]
    (p : Ideal A) [p.IsPrime] : Subalgebra A K :=
  Localization.subalgebra.ofField K p.primeCompl p.primeCompl_le_nonZeroDivisors

def placeValuationSubring (A : Subalgebra k K) [IsFractionRing A K]
    (p : Ideal A) [p.IsPrime]
    (h : ∀ z : K, z ∈ (placeSubalgebra A p).toSubring ∨
      z⁻¹ ∈ (placeSubalgebra A p).toSubring) : ValuationSubring K :=
  ValuationSubring.ofSubring (placeSubalgebra A p).toSubring h

local instance valuationSubringToSubringIsLocal (V : ValuationSubring K) :
    IsLocalRing V.toSubring :=
  ValuationSubring.isLocalRing V

local instance placeSubalgebraAtPrime (A : Subalgebra k K) [IsFractionRing A K]
    (p : Ideal A) [p.IsPrime] :
    IsLocalization.AtPrime (placeSubalgebra A p) p := by
  unfold placeSubalgebra
  infer_instance

local instance placeSubalgebraIsLocal (A : Subalgebra k K) [IsFractionRing A K]
    (p : Ideal A) [p.IsPrime] : IsLocalRing (placeSubalgebra A p).toSubring := by
  change IsLocalRing (placeSubalgebra A p)
  exact IsLocalization.AtPrime.isLocalRing (placeSubalgebra A p) p

local instance placeSubalgebraIsLocal' (A : Subalgebra k K) [IsFractionRing A K]
    (p : Ideal A) [p.IsPrime] : IsLocalRing (placeSubalgebra A p) :=
  IsLocalization.AtPrime.isLocalRing (placeSubalgebra A p) p

theorem ofField_mem_algebraMap (A : Subalgebra k K) [IsFractionRing A K]
    (p : Ideal A) [p.IsPrime]
    (a : A) :
    (a : K) ∈ (placeSubalgebra A p).toSubring := by
  change (a : K) ∈ placeSubalgebra A p
  exact (placeSubalgebra A p).algebraMap_mem a

theorem ofField_mem_algebraMap_v (A : Subalgebra k K) [IsFractionRing A K]
    (p : Ideal A) [p.IsPrime]
    (h : ∀ z : K, z ∈ (placeSubalgebra A p).toSubring ∨
      z⁻¹ ∈ (placeSubalgebra A p).toSubring) (a : A) :
    (a : K) ∈ (placeValuationSubring A p h).toSubring := by
  exact ofField_mem_algebraMap A p a

theorem ofField_mem_maximalIdeal_iff (A : Subalgebra k K) [IsFractionRing A K]
    (p : Ideal A) [p.IsPrime]
    (a : A) :
    (⟨(a : K), ofField_mem_algebraMap A p a⟩ : (placeSubalgebra A p).toSubring) ∈
        maximalIdeal (placeSubalgebra A p).toSubring ↔ a ∈ p := by
  change algebraMap A (placeSubalgebra A p) a ∈
      maximalIdeal (placeSubalgebra A p) ↔ a ∈ p
  exact IsLocalization.AtPrime.to_map_mem_maximal_iff
    (placeSubalgebra A p) p a (h := placeSubalgebraIsLocal A p)

theorem ofField_mem_maximalIdeal_iff_v (A : Subalgebra k K) [IsFractionRing A K]
    (p : Ideal A) [p.IsPrime]
    (h : ∀ z : K, z ∈ (placeSubalgebra A p).toSubring ∨
      z⁻¹ ∈ (placeSubalgebra A p).toSubring) (a : A) :
    (⟨(a : K), ofField_mem_algebraMap_v A p h a⟩ :
      (placeValuationSubring A p h).toSubring) ∈
        maximalIdeal (placeValuationSubring A p h).toSubring ↔ a ∈ p := by
  change algebraMap A (placeSubalgebra A p) a ∈
      maximalIdeal (placeSubalgebra A p) ↔ a ∈ p
  exact IsLocalization.AtPrime.to_map_mem_maximal_iff
    (placeSubalgebra A p) p a (h := placeSubalgebraIsLocal A p)

theorem ofField_residue_surjective (A : Subalgebra k K) [IsFractionRing A K]
    (p : Ideal A) [p.IsPrime]
    (z : ResidueField (placeSubalgebra A p).toSubring) :
    ∃ (a b : A), b ∉ p ∧
      z = residue (placeSubalgebra A p).toSubring
        ⟨(a : K), ofField_mem_algebraMap A p a⟩ /
        residue (placeSubalgebra A p).toSubring
          ⟨(b : K), ofField_mem_algebraMap A p b⟩ := by
  obtain ⟨x, rfl⟩ := residue_surjective (R := (placeSubalgebra A p).toSubring) z
  change ∃ (a b : A), b ∉ p ∧
    residue (placeSubalgebra A p).toSubring x =
      residue (placeSubalgebra A p).toSubring
          ⟨(a : K), ofField_mem_algebraMap A p a⟩ /
        residue (placeSubalgebra A p).toSubring
          ⟨(b : K), ofField_mem_algebraMap A p b⟩
  have hx : (x : K) ∈ placeSubalgebra A p := x.property
  simp only [placeSubalgebra, Localization.subalgebra.ofField] at hx
  obtain ⟨a, b, hb, hab⟩ := hx
  refine ⟨a, b, ?_, ?_⟩
  · exact hb
  · have hbinv : (algebraMap A K b)⁻¹ ∈ placeSubalgebra A p := by
      simp only [placeSubalgebra, Localization.subalgebra.ofField]
      exact ⟨1, b, hb, by simp⟩
    let binv : (placeSubalgebra A p).toSubring :=
      ⟨(algebraMap A K b)⁻¹, hbinv⟩
    have hxb : x = algebraMap A (placeSubalgebra A p) a * binv := by
      apply Subtype.ext
      simpa [binv] using hab
    have hbA0 : b ≠ 0 := fun hbzero ↦ hb (hbzero ▸ p.zero_mem)
    have hb0 : algebraMap A K b ≠ 0 := by
      intro hbzero
      apply hbA0
      apply Subtype.ext
      exact hbzero
    have hbmul : binv * algebraMap A (placeSubalgebra A p) b = 1 := by
      apply Subtype.ext
      exact inv_mul_cancel₀ hb0
    have hresinv : residue (placeSubalgebra A p).toSubring binv =
        (residue (placeSubalgebra A p).toSubring
          (algebraMap A (placeSubalgebra A p) b))⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← map_mul, hbmul, map_one]
    calc
      residue (placeSubalgebra A p).toSubring x =
          residue (placeSubalgebra A p).toSubring
            (algebraMap A (placeSubalgebra A p) a * binv) := by rw [hxb]
      _ = residue (placeSubalgebra A p).toSubring
            ⟨(a : K), ofField_mem_algebraMap A p a⟩ /
          residue (placeSubalgebra A p).toSubring
            ⟨(b : K), ofField_mem_algebraMap A p b⟩ := by
        rw [map_mul, hresinv, div_eq_mul_inv]
        rfl

theorem ofField_residue_surjective_v (A : Subalgebra k K) [IsFractionRing A K]
    (p : Ideal A) [p.IsPrime]
    (h : ∀ z : K, z ∈ (placeSubalgebra A p).toSubring ∨
      z⁻¹ ∈ (placeSubalgebra A p).toSubring)
    (z : ResidueField (placeValuationSubring A p h).toSubring) :
    ∃ (a b : A), b ∉ p ∧
      z = residue (placeValuationSubring A p h).toSubring
        ⟨(a : K), ofField_mem_algebraMap_v A p h a⟩ /
        residue (placeValuationSubring A p h).toSubring
          ⟨(b : K), ofField_mem_algebraMap_v A p h b⟩ := by
  exact ofField_residue_surjective A p z

theorem ofField_glue (A : Subalgebra k K) [IsFractionRing A K]
    (p : Ideal A) [p.IsPrime]
    (h : ∀ z : K, z ∈ (placeSubalgebra A p).toSubring ∨
      z⁻¹ ∈ (placeSubalgebra A p).toSubring) :
    (∀ a : A, (a : K) ∈ (placeValuationSubring A p h).toSubring) ∧
    (∀ a : A, (⟨a, ofField_mem_algebraMap_v A p h a⟩ :
      (placeValuationSubring A p h).toSubring) ∈
        maximalIdeal (placeValuationSubring A p h).toSubring ↔ a ∈ p) ∧
    (∀ z : ResidueField (placeValuationSubring A p h).toSubring,
      ∃ (a b : A), b ∉ p ∧
        z = residue (placeValuationSubring A p h).toSubring
          ⟨(a : K), ofField_mem_algebraMap_v A p h a⟩ /
        residue (placeValuationSubring A p h).toSubring
          ⟨(b : K), ofField_mem_algebraMap_v A p h b⟩) := by
  refine ⟨fun a ↦ ofField_mem_algebraMap_v A p h a,
    fun a ↦ ofField_mem_maximalIdeal_iff_v A p h a,
    fun z ↦ ofField_residue_surjective_v A p h z⟩

/-! Explicitly named implementations of the five checked stages. -/

theorem isDiscreteValuationRing_of_isLocalization_atPrime
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (p : Ideal A) [p.IsPrime] (h : p.height = 1)
    (S : Type*) [CommRing S] [IsDomain S] [Algebra A S]
    [IsLocalization.AtPrime S p] : IsDiscreteValuationRing S := by
  have hpb : p ≠ ⊥ := Ideal.ne_bot_of_height_eq_one h
  letI : IsLocalRing S := IsLocalization.AtPrime.isLocalRing S p
  letI : IsNoetherianRing S := IsLocalization.isNoetherianRing p.primeCompl S inferInstance
  letI : IsIntegrallyClosed S :=
    isIntegrallyClosed_of_isLocalization S p.primeCompl p.primeCompl_le_nonZeroDivisors
  have hnf : ¬ IsField S := IsLocalization.AtPrime.not_isField A hpb S
  have hkd : Ring.KrullDimLE 1 S := by
    rw [Ring.krullDimLE_iff, IsLocalization.AtPrime.ringKrullDim_eq_height p S, h]
    norm_num
  have h3 : IsIntegrallyClosed S ∧ ∃! P : Ideal S, P ≠ ⊥ ∧ P.IsPrime := by
    refine ⟨inferInstance, IsLocalRing.maximalIdeal _,
      ⟨IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hnf, inferInstance⟩, ?_⟩
    rintro P ⟨hPb, hPp⟩
    exact IsLocalRing.eq_maximalIdeal (hPp.isMaximal_of_ne_bot hPb)
  exact ((IsDiscreteValuationRing.TFAE S hnf).out 3 0).mp h3

theorem stage1_exists_valuationSubring_of_transcendental
    {k K : Type*} [Field k] [Field K] [Algebra k K] (x : K)
    (hx : Transcendental k x) :
    ∃ W : ValuationSubring K, (∀ c : k, algebraMap k K c ∈ W) ∧ x ∈ W ∧ x⁻¹ ∉ W := by
  classical
  have hx0 : x ≠ 0 := fun h => hx (h ▸ isAlgebraic_zero)
  let A : Subring K := (Algebra.adjoin k ({x} : Set K)).toSubring
  have hxA : x ∈ A := Algebra.subset_adjoin (Set.mem_singleton x)
  let I : Ideal A := Ideal.span {⟨x, hxA⟩}
  have hI : I ≠ ⊤ := by
    intro htop
    have h1 : (1 : A) ∈ I := htop ▸ Submodule.mem_top
    rw [Ideal.mem_span_singleton'] at h1
    obtain ⟨g, hg⟩ := h1
    have hg' : (g : K) * x = 1 := by
      have := congrArg Subtype.val hg
      simpa using this
    obtain ⟨q, hq⟩ : ∃ q : Polynomial k, Polynomial.aeval x q = (g : K) := by
      have hmem : (g : K) ∈ Algebra.adjoin k ({x} : Set K) := g.2
      rw [Algebra.adjoin_singleton_eq_range_aeval] at hmem
      exact (AlgHom.mem_range _).1 hmem
    apply hx
    refine ⟨q * Polynomial.X - 1, ?_, ?_⟩
    · intro h0
      have hc := congrArg (fun p : Polynomial k => p.coeff 0) h0
      simp [Polynomial.mul_coeff_zero] at hc
    · simp [map_sub, map_mul, hq, hg']
  obtain ⟨W, hAW, hIW⟩ := Ideal.image_subset_nonunits_valuationSubring I hI
  have hxW : x ∈ W := hAW hxA
  refine ⟨W, fun c => hAW (Subalgebra.algebraMap_mem _ c), hxW, ?_⟩
  intro hinv
  have hxn : x ∈ W.nonunits := hIW
    ⟨⟨x, hxA⟩, Ideal.mem_span_singleton_self _, rfl⟩
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal] at hxn
  obtain ⟨hxW', hxm⟩ := hxn
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hxm
  exact hxm (isUnit_iff_exists_inv.2
    ⟨⟨x⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hx0)⟩)

theorem stage3_exists_height_one_prime_valuation
    {k K : Type*} [Field k] [Field K] [Algebra k K]
    (A : Subalgebra k K) [IsNoetherianRing A] [IsIntegrallyClosed A]
    [IsFractionRing A K] (x : A) (hx0 : x ≠ 0) (hxu : ¬ IsUnit x) :
    ∃ p : Ideal A, ∃ _ : p.IsPrime, p.height = 1 ∧ x ∈ p ∧
      ∀ z : K, z ∈ Localization.subalgebra.ofField K p.primeCompl
        p.primeCompl_le_nonZeroDivisors ∨ z⁻¹ ∈
        Localization.subalgebra.ofField K p.primeCompl
          p.primeCompl_le_nonZeroDivisors := by
  obtain ⟨p, hp, hp1⟩ := exists_height_one_minimal_prime hx0 hxu
  letI := hp.isPrime
  refine ⟨p, inferInstance, hp1, hp.1.2 (Ideal.mem_span_singleton_self x), ?_⟩
  set S := Localization.subalgebra.ofField K p.primeCompl
    p.primeCompl_le_nonZeroDivisors with hS
  letI : IsDiscreteValuationRing S :=
    isDiscreteValuationRing_of_isLocalization_atPrime p hp1 S
  intro z
  rcases ValuationRing.isInteger_or_isInteger S z with ⟨s, hs⟩ | ⟨s, hs⟩
  · left; rw [← hs]; exact s.2
  · right; rw [← hs]; exact s.2

theorem stage6_transcendental_of_mem_maximalIdeal
    {k K : Type*} [Field k] [Field K] [Algebra k K]
    (E : IntermediateField k K) (V : ValuationSubring K) [IsLocalRing V.toSubring]
    (hEV : ∀ z : E, (z : K) ∈ V.toSubring) (x : K) (hx0 : x ≠ 0)
    (hxV : x ∈ V.toSubring)
    (hxm : (⟨x, hxV⟩ : V.toSubring) ∈ maximalIdeal V.toSubring) :
    Transcendental E x := by
  intro halg
  have hint : IsIntegral E x := halg.isIntegral
  set a : E := (minpoly E x).coeff 0 with ha
  have ha0 : a ≠ 0 := minpoly.coeff_zero_ne_zero hint hx0
  obtain ⟨q, hq⟩ := X_dvd_sub_C (p := minpoly E x)
  have h1 : aeval x (minpoly E x - C a) = aeval x (X * q) := by rw [hq]
  rw [map_sub, minpoly.aeval, aeval_C, zero_sub, map_mul, aeval_X] at h1
  have hqV : aeval x q ∈ V.toSubring := by
    rw [aeval_eq_sum_range]
    refine Subring.sum_mem _ fun n _ ↦ ?_
    rw [Algebra.smul_def]
    exact Subring.mul_mem _ (hEV _) (Subring.pow_mem _ hxV n)
  have haV : algebraMap E K a ∈ V.toSubring := hEV _
  have hmem : (⟨algebraMap E K a, haV⟩ : V.toSubring) ∈ maximalIdeal V.toSubring := by
    have : (⟨algebraMap E K a, haV⟩ : V.toSubring) =
        -((⟨x, hxV⟩ : V.toSubring) * ⟨aeval x q, hqV⟩) := by
      apply Subtype.ext
      push_cast
      exact neg_eq_iff_eq_neg.1 h1
    rw [this]
    exact (Submodule.neg_mem_iff _).2 (Ideal.mul_mem_right _ _ hxm)
  have hu : IsUnit (⟨algebraMap E K a, haV⟩ : V.toSubring) := by
    refine isUnit_iff_exists_inv.2 ⟨⟨(algebraMap E K a)⁻¹, ?_⟩, Subtype.ext ?_⟩
    · have h : (algebraMap E K a)⁻¹ = ((a⁻¹ : E) : K) := by
        first | simp | (rw [IntermediateField.coe_inv]; rfl)
      rw [h]; exact hEV _
    · exact mul_inv_cancel₀ ((_root_.map_ne_zero _).2 ha0)
  exact (mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal _).1 hmem)) hu

theorem stage7_kaehler_finite_ofField
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (A : Subalgebra k K) [Algebra.FiniteType k A] [IsFractionRing A K]
    (p : Ideal A) [p.IsPrime]
    (hk : ∀ c : k, algebraMap k K c ∈
      (Localization.subalgebra.ofField K p.primeCompl p.primeCompl_le_nonZeroDivisors).toSubring) :
    letI : Algebra k
        (Localization.subalgebra.ofField K p.primeCompl p.primeCompl_le_nonZeroDivisors).toSubring :=
      ((algebraMap k K).codRestrict _ hk).toAlgebra
    Module.Finite
      (Localization.subalgebra.ofField K p.primeCompl p.primeCompl_le_nonZeroDivisors).toSubring
      (Ω[(Localization.subalgebra.ofField K p.primeCompl p.primeCompl_le_nonZeroDivisors).toSubring⁄k]) := by
  exact (by
    set S := Localization.subalgebra.ofField K p.primeCompl
      p.primeCompl_le_nonZeroDivisors with hS
    letI inst : Algebra k S.toSubring := ((algebraMap k K).codRestrict _ hk).toAlgebra
    haveI : Algebra.EssFiniteType A S := Algebra.EssFiniteType.of_isLocalization S p.primeCompl
    haveI : IsScalarTower k A S := IsScalarTower.of_algebraMap_eq fun c =>
      Subtype.ext (IsScalarTower.algebraMap_apply k A K c)
    haveI : Algebra.EssFiniteType k A := Algebra.EssFiniteType.of_finiteType k A
    haveI h1 : Algebra.EssFiniteType k S := Algebra.EssFiniteType.comp k A S
    have h2 : inst = (inferInstance : Algebra k S) := by
      apply Algebra.algebra_ext
      intro c
      rfl
    haveI h3 : Algebra.EssFiniteType k S.toSubring := by
      rw [h2]
      exact h1
    exact KaehlerDifferential.finite k S.toSubring)

/-! ## Assembly scaffold

The declarations below intentionally expose exactly the three unresolved
construction stages.  They are inputs, rather than axioms or placeholders, so a
future assembly proof can be checked by supplying S2, S4, and S5 separately.
The four other stage fields are already available as the theorems above. -/

def Stage2Obligation : Prop :=
  ∀ {k K : Type u} [Field k] [CharZero k] [Field K] [Algebra k K]
    {r : ℕ} (y : Fin r → K) (i : Fin r)
    (hgen : IntermediateField.adjoin k (Set.range y) = ⊤)
    (hx : Transcendental k (y i)),
    ∃ (j : Fin (r + 1)) (s : K) (A : Subalgebra k K),
      s ≠ 0 ∧ (Fin.cases 1 y j : K) * s = 1 ∧
      (∀ a, (Fin.cases 1 y a : K) * s ∈ A) ∧ y i ∈ A ∧
      Algebra.FiniteType k A ∧ IsIntegrallyClosedIn A K ∧ IsFractionRing A K ∧
      (∀ a : A, IsIntegral (Algebra.adjoin k
        (Set.range (fun a : Fin (r + 1) => (Fin.cases 1 y a : K) * s) ∪ {y i})) (a : K)) ∧
      (y i)⁻¹ ∉ A

def Stage4Obligation : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    (A : Subalgebra k K) (p : Ideal A) [p.IsPrime]
    (V : ValuationSubring K) [IsLocalRing V.toSubring]
    [Algebra k V.toSubring] [IsScalarTower k V.toSubring K]
    (hAV : ∀ a : A, (a : K) ∈ V.toSubring)
    (hp : ∀ a : A, (⟨a, hAV a⟩ : V.toSubring) ∈ maximalIdeal V.toSubring ↔ a ∈ p)
    (hsurj : ∀ z : ResidueField V.toSubring, ∃ (a b : A), b ∉ p ∧
      z = residue V.toSubring ⟨a, hAV a⟩ / residue V.toSubring ⟨b, hAV b⟩)
    {ι : Type v} (c : ι → K) (hc : ∀ i, c i ∈ A)
    (hint : ∀ a : A, IsIntegral (Algebra.adjoin k (Set.range c)) (a : K)),
    Algebra.IsAlgebraic
      (IntermediateField.adjoin k (Set.range fun i =>
        residue V.toSubring ⟨c i, hAV ⟨c i, hc i⟩⟩) :
        IntermediateField k (ResidueField V.toSubring))
      (ResidueField V.toSubring)

def Stage5Obligation : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    (A : Subalgebra k K) [Algebra.FiniteType k A] (p : Ideal A) [p.IsPrime]
    (V : ValuationSubring K) [IsLocalRing V.toSubring]
    (hAV : ∀ a : A, (a : K) ∈ V.toSubring)
    (hp : ∀ a : A, (⟨a, hAV a⟩ : V.toSubring) ∈ maximalIdeal V.toSubring ↔ a ∈ p)
    (hsurj : ∀ z : ResidueField V.toSubring, ∃ (a b : A), b ∉ p ∧
      z = residue V.toSubring ⟨a, hAV a⟩ / residue V.toSubring ⟨b, hAV b⟩),
    ∃ (E : IntermediateField k K) (hEV : ∀ z : E, (z : K) ∈ V.toSubring),
      letI : Algebra E V.toSubring := (coeffHom E V hEV).toAlgebra
      Module.Finite E (ResidueField V.toSubring)

structure AssemblyScaffold : Prop where
  stage2 : Stage2Obligation.{u}
  stage4 : Stage4Obligation.{u, v}
  stage5 : Stage5Obligation.{u}

theorem assembly_scaffold_of_obligations
    (stage2 : Stage2Obligation.{u}) (stage4 : Stage4Obligation.{u, v})
    (stage5 : Stage5Obligation.{u}) : AssemblyScaffold.{u, v} :=
  ⟨stage2, stage4, stage5⟩


end Stafford38.Geometry.LaneC

end
