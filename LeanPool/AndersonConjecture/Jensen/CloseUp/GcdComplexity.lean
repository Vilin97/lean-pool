/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import LeanPool.AndersonConjecture.Jensen.CloseUp.Base
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# GCD complexity measure

Defines the GCD complexity of a finite set of elements in a UFD:
the sum of the lengths of their factorisations. This serves as
the well-founded measure for the inductive step of the close-up
construction when n >= 3 generators. Dividing all generators by
a common prime strictly decreases the complexity.
-/

noncomputable section

open Cardinal Ideal

variable {T : Type*} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsDomain T]

/-- "GCD complexity" of a finite set `s` in a UFD subring `R`: the sum over `x ∈ s`
of the number of (normalized) irreducible factors of `x`. Used as a termination
measure in the close-up construction. -/
noncomputable def gcdComplexity {R : Subring T}
    [UniqueFactorizationMonoid R] (s : Finset R) : ℕ :=
  @Finset.sum _ _ _ s fun x =>
    @Multiset.card _
      (@UniqueFactorizationMonoid.normalizedFactors
        R _ UniqueFactorizationMonoid.normalizationMonoid _ x)

/-- `gcdComplexity` for a finite set in an N-subring, supplying the domain and
UFD instances from the N-subring structure. -/
noncomputable def gcdComplexityNsub (R : NSubring T) (s : Finset R.carrier) : ℕ :=
  haveI : IsDomain R.carrier := NSubring.isDomain R
  haveI : UniqueFactorizationMonoid R.carrier := R.isUFD
  gcdComplexity s

lemma normalizedFactors_card_inclusion
    (R S₁ : NSubring T) (hAext : IsAExtension R S₁)
    (hle : R.carrier ≤ S₁.carrier)
    (x : R.carrier) :
    letI : IsDomain R.carrier := NSubring.isDomain R
    letI : UniqueFactorizationMonoid R.carrier := R.isUFD
    letI : IsDomain S₁.carrier := NSubring.isDomain S₁
    letI : UniqueFactorizationMonoid S₁.carrier := S₁.isUFD
    letI : NormalizationMonoid R.carrier := UniqueFactorizationMonoid.normalizationMonoid
    letI : NormalizationMonoid S₁.carrier := UniqueFactorizationMonoid.normalizationMonoid
    (UniqueFactorizationMonoid.normalizedFactors
      (Subring.inclusion hle x)).card =
    (UniqueFactorizationMonoid.normalizedFactors x).card := by
  letI : IsDomain R.carrier := NSubring.isDomain R
  letI : UniqueFactorizationMonoid R.carrier := R.isUFD
  letI : IsDomain S₁.carrier := NSubring.isDomain S₁
  letI : UniqueFactorizationMonoid S₁.carrier := S₁.isUFD
  letI : NormalizationMonoid R.carrier := UniqueFactorizationMonoid.normalizationMonoid
  letI : NormalizationMonoid S₁.carrier := UniqueFactorizationMonoid.normalizationMonoid
  have h_inj : Function.Injective (Subring.inclusion hle) :=
    Subring.inclusion_injective hle
  change (UniqueFactorizationMonoid.normalizedFactors (Subring.inclusion hle x)).card =
      (UniqueFactorizationMonoid.normalizedFactors x).card
  exact WfDvdMonoid.induction_on_irreducible x
    (by simp [map_zero, UniqueFactorizationMonoid.normalizedFactors_zero])
    (fun u hu => by
      simp [UniqueFactorizationMonoid.normalizedFactors_of_isUnit hu,
          UniqueFactorizationMonoid.normalizedFactors_of_isUnit (hu.map _)])
    (fun a i ha hi ih_a => by
      have hi_prime : Prime i := UniqueFactorizationMonoid.irreducible_iff_prime.mp hi
      have hi_S₁ : Prime (Subring.inclusion hle i) := hAext.primes_preserved i hi_prime
      have ha_S₁ : Subring.inclusion hle a ≠ 0 :=
        fun h => ha (h_inj (h.trans (map_zero _).symm))
      have hi_S₁_ne : Subring.inclusion hle i ≠ 0 :=
        fun h => hi.ne_zero (h_inj (h.trans (map_zero _).symm))
      rw [map_mul, UniqueFactorizationMonoid.normalizedFactors_mul hi.ne_zero ha,
          UniqueFactorizationMonoid.normalizedFactors_mul hi_S₁_ne ha_S₁,
          Multiset.card_add, Multiset.card_add,
          UniqueFactorizationMonoid.normalizedFactors_irreducible hi,
          UniqueFactorizationMonoid.normalizedFactors_irreducible hi_S₁.irreducible,
          Multiset.card_singleton, Multiset.card_singleton, ih_a])

lemma span_eq_mul_span_image_div {R₀ : Type*} [CommRing R₀]
    [DecidableEq R₀]
    (p : R₀) (s : Finset R₀)
    (_hp_dvd : ∀ x ∈ s, p ∣ x)
    (div_f : R₀ → R₀)
    (hdiv_spec : ∀ x ∈ s, x = p * div_f x) :
    Ideal.span (↑s : Set R₀) =
      Ideal.span {p} * Ideal.span (↑(s.image div_f) : Set R₀) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro x hx
    rw [SetLike.mem_coe, hdiv_spec x (Finset.mem_coe.mp hx)]
    exact Ideal.mul_mem_mul (Ideal.subset_span rfl)
      (Ideal.subset_span (Finset.mem_coe.mpr
        (Finset.mem_image.mpr ⟨x, Finset.mem_coe.mp hx, rfl⟩)))
  · apply Ideal.mul_le.mpr
    intro a ha b hb
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp ha
    suffices hpb : p * b ∈ Ideal.span (↑s : Set R₀) by
      rw [mul_comm p r, mul_assoc]
      exact Ideal.mul_mem_left _ r hpb
    exact Submodule.span_induction
      (p := fun b _ => p * b ∈ Ideal.span (↑s : Set R₀))
      (fun z hz => by
        rw [Finset.mem_coe, Finset.mem_image] at hz
        obtain ⟨x, hx, rfl⟩ := hz
        rw [(hdiv_spec x hx).symm]
        exact Ideal.subset_span (Finset.mem_coe.mpr hx))
      (by
         rw [mul_zero]
         exact zero_mem _)
      (fun x y _ _ hx hy => by
        change p * (x + y) ∈ _
        rw [mul_add]
        exact add_mem hx hy)
      (fun r x _ hx => by
        change p * (r • x) ∈ _
        rw [smul_eq_mul, ← mul_assoc, mul_comm p r, mul_assoc]
        exact Ideal.mul_mem_left _ r hx)
      hb

lemma prime_mul_span_insert_le {R₀ : Type*} [CommRing R₀]
    [DecidableEq R₀]
    (q' a : R₀) (rest : Finset R₀)
    (div_f : R₀ → R₀)
    (hdiv : ∀ x ∈ rest, x = q' * div_f x) :
    Ideal.span {q'} * Ideal.span (↑(insert a (rest.image div_f)) : Set R₀) ≤
      Ideal.span (↑(insert a rest) : Set R₀) := by
  apply Ideal.mul_le.mpr
  intro x hx y hy
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hx
  suffices hq'y : q' * y ∈ Ideal.span (↑(insert a rest) : Set R₀) by
    rw [mul_comm q' r, mul_assoc]
    exact Ideal.mul_mem_left _ r hq'y
  exact Submodule.span_induction
    (p := fun y _ => q' * y ∈ Ideal.span (↑(insert a rest) : Set R₀))
    (fun z hz => by
      rw [Finset.coe_insert, Set.mem_insert_iff] at hz
      rcases hz with rfl | hz'
      · exact Ideal.mul_mem_left _ q' (Ideal.subset_span
          (Finset.mem_coe.mpr (Finset.mem_insert.mpr (Or.inl rfl))))
      · rw [Finset.mem_coe, Finset.mem_image] at hz'
        obtain ⟨xo, hxo, rfl⟩ := hz'
        rw [(hdiv xo hxo).symm]
        exact Ideal.subset_span (Finset.mem_coe.mpr
          (Finset.mem_insert_of_mem hxo)))
    (by
       rw [mul_zero]
       exact zero_mem _)
    (fun x y _ _ hx hy => by
      change q' * (x + y) ∈ _
      rw [mul_add]
      exact add_mem hx hy)
    (fun r x _ hx => by
      change q' * (r • x) ∈ _
      rw [smul_eq_mul, ← mul_assoc, mul_comm q' r, mul_assoc]
      exact Ideal.mul_mem_left _ r hx)
    hy

-- Regularity: q prime, q ∤ a implies a is regular on T/qT, so a*t ∈ span{q} forces t ∈ span{q}.
lemma nzd_element_in_span_prime
    (R : NSubring T)
    (q a : R.carrier)
    (hq_prime : Prime q) (hqa : ¬(q ∣ a))
    (_hM_not_assoc : ∀ (r : T), r ≠ 0 →
      IsLocalRing.maximalIdeal T ∉ associatedPrimes T (T ⧸ Ideal.span {r}))
    (t_val : T) (h_at_mem : (a : T) * t_val ∈ Ideal.span {(q : T)}) :
    ∃ t' : T, t_val = (q : T) * t' := by
  haveI : IsDomain R.carrier := NSubring.isDomain R
  have hq_ne : (q : T) ≠ 0 := fun h => hq_prime.ne_zero (Subtype.val_injective h)
  have hnt : Nontrivial (T ⧸ Ideal.span {(q : T)}) := by
    rw [Ideal.Quotient.nontrivial_iff, Ne, Ideal.eq_top_iff_one, Ideal.mem_span_singleton]
    intro ⟨c'', hc''⟩
    have hmem : q ∈ IsLocalRing.maximalIdeal R.carrier :=
      (IsLocalRing.mem_maximalIdeal _).mpr hq_prime.not_unit
    rw [R.maximal_ideal_eq, Ideal.mem_comap] at hmem
    exact (IsLocalRing.mem_maximalIdeal _).mp hmem (isUnit_of_dvd_one ⟨c'', hc''⟩)
  haveI := hnt
  have ha_not_in_P : ∀ P ∈ associatedPrimes T (T ⧸ Ideal.span {(q : T)}),
      (a : T) ∉ P := by
    intro P hP_mem ha_in_P
    have hq_in_P : (q : T) ∈ P := by
      have hP_assoc := (hP_mem : IsAssociatedPrime P _)
      have : Ideal.span {(q : T)} ≤ P :=
        Ideal.span_le.mpr (Set.singleton_subset_iff.mpr
          (hP_assoc.annihilator_le (by
            rw [Submodule.mem_annihilator]
            intro m _
            induction m using Quotient.inductionOn' with
            | h r => exact Ideal.Quotient.eq_zero_iff_mem.mpr
                       (Ideal.mul_mem_right r _
                         (Ideal.subset_span rfl)))))
      exact this (Ideal.subset_span rfl)
    have hht := R.height_bound (q : T) hq_ne P hP_mem
    have hspan_le : Ideal.span {q} ≤ P.comap R.carrier.subtype :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hq_in_P)
    have hspan_prime : (Ideal.span {q}).IsPrime :=
      (Ideal.span_singleton_prime (α := R.carrier) hq_prime.ne_zero).mpr hq_prime
    have hspan_ne_bot : Ideal.span {q} ≠ (⊥ : Ideal R.carrier) :=
      mt (Ideal.span_singleton_eq_bot (α := R.carrier)).mp hq_prime.ne_zero
    have hcomap_prime : (P.comap R.carrier.subtype).IsPrime :=
      hP_mem.isPrime.comap R.carrier.subtype
    have heq : Ideal.span {q} = P.comap R.carrier.subtype :=
      @eq_of_prime_le_prime_height_le_one R.carrier _ (NSubring.isDomain R) _ _
        hspan_prime hcomap_prime hspan_le hspan_ne_bot hht
    have ha_comap : a ∈ P.comap R.carrier.subtype := ha_in_P
    rw [← heq, Ideal.mem_span_singleton] at ha_comap
    exact hqa ha_comap
  have ha_reg : IsSMulRegular (T ⧸ Ideal.span {(q : T)}) (a : T) := by
    by_contra h_not_reg
    have hmem : (a : T) ∈ ⋃ p ∈ associatedPrimes T (T ⧸ Ideal.span {(q : T)}),
        (p : Set T) := by
      rw [biUnion_associatedPrimes_eq_compl_regular]
      simp only [Set.mem_compl_iff] at h_not_reg ⊢
      exact h_not_reg
    rw [Set.mem_iUnion₂] at hmem
    obtain ⟨P, hP, ha_P⟩ := hmem
    exact ha_not_in_P P hP ha_P
  have h_quot_zero : (a : T) • Ideal.Quotient.mk (Ideal.span {(q : T)}) t_val = 0 := by
    change Ideal.Quotient.mk _ ((a : T) * t_val) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr h_at_mem
  have h_t_zero : Ideal.Quotient.mk (Ideal.span {(q : T)}) t_val = 0 := by
    have h0 : (a : T) • (0 : T ⧸ Ideal.span {(q : T)}) = 0 := smul_zero _
    exact ha_reg (h_quot_zero.trans h0.symm)
  have h_t_mem : t_val ∈ Ideal.span {(q : T)} :=
    Ideal.Quotient.eq_zero_iff_mem.mp h_t_zero
  exact Ideal.mem_span_singleton.mp h_t_mem

omit [IsLocalRing T] [IsNoetherianRing T] in
lemma gcdComplexity_div_le {R₀ : Subring T}
    [UniqueFactorizationMonoid R₀]
    [DecidableEq R₀]
    (q : R₀) (hq : Prime q) (s : Finset R₀)
    (_hq_dvd : ∀ x ∈ s, q ∣ x)
    (div_f : R₀ → R₀)
    (hdiv : ∀ x ∈ s, x = q * div_f x)
    (hinj : Set.InjOn div_f ↑s) :
    gcdComplexity (s.image div_f) ≤ gcdComplexity s := by
  letI : NormalizationMonoid R₀ := UniqueFactorizationMonoid.normalizationMonoid
  unfold gcdComplexity
  rw [Finset.sum_image hinj]
  apply Finset.sum_le_sum
  intro x hx
  by_cases hx0 : x = 0
  · subst hx0
    have : div_f 0 = 0 := by
      have h := hdiv 0 hx
      exact (mul_eq_zero.mp h.symm).resolve_left hq.ne_zero
    simp [this]
  · have hdvd_x : div_f x ∣ x := ⟨q, (hdiv x hx).trans (mul_comm q (div_f x))⟩
    by_cases hfx : div_f x = 0
    · simp [hfx, UniqueFactorizationMonoid.normalizedFactors_zero]
    · open UniqueFactorizationMonoid in
      exact Multiset.card_le_card
        ((dvd_iff_normalizedFactors_le_normalizedFactors hfx hx0).mp hdvd_x)

end
