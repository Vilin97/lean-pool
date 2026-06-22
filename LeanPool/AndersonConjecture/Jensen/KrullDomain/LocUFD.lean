/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-!
# Localisation of a UFD at one element

If R is a UFD and y is a nonzero element, then R[y^{-1}] is
again a UFD. The prime factors of any numerator that are
associate to y become units in the localisation
the remaining
irreducibles stay prime.
-/

noncomputable section

open Cardinal Ideal Set Pointwise

section LocUFD

variable {R₀ : Type*} [CommRing R₀] [IsDomain R₀] [UniqueFactorizationMonoid R₀]

omit [UniqueFactorizationMonoid R₀] in
/-- A prime element p that doesn't divide any power of y stays prime in R[y⁻¹]. -/
lemma prime_algebraMap_of_not_dvd_pow (y p : R₀) (hp : Prime p)
    (hpy : ∀ n : ℕ, ¬ p ∣ y ^ n) :
    Prime (algebraMap R₀ (Localization.Away y) p) := by
  have hyne : y ≠ 0 := by
    intro h
    apply hpy 1
    rw [h, pow_one]
    exact dvd_zero p
  have hpow_ne : (0 : R₀) ∉ Submonoid.powers y := by
    rintro ⟨n, hn⟩
    exact pow_ne_zero n hyne hn
  have hinj := IsLocalization.injective (Localization.Away y)
    (le_nonZeroDivisors_of_noZeroDivisors hpow_ne)
  have hne : algebraMap R₀ (Localization.Away y) p ≠ 0 :=
    fun h => hp.ne_zero (hinj (by rw [h, map_zero]))
  -- Reduce primality of p in R[y⁻¹] to disjointness of (p) from powers of y
  rw [← Ideal.span_singleton_prime hne]
  rw [show Ideal.span {algebraMap R₀ (Localization.Away y) p} =
    Ideal.map (algebraMap R₀ (Localization.Away y)) (Ideal.span {p}) from
    by rw [Ideal.map_span, Set.image_singleton]]
  exact IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers y) _ _
    ((Ideal.span_singleton_prime hp.ne_zero).mpr hp) (by
      rw [Set.disjoint_iff]
      intro x ⟨hxM, hxI⟩
      rw [SetLike.mem_coe, Ideal.mem_span_singleton] at hxI
      obtain ⟨n, rfl⟩ := (hxM : x ∈ Submonoid.powers y)
      exact hpy n hxI)

/-- In a UFD, the localization away from a nonzero element is a UFD. -/
theorem localization_away_UFD (y : R₀) (hy : y ≠ 0) :
    UniqueFactorizationMonoid (Localization.Away y) := by
  open Classical in
  have hpow_ne : (0 : R₀) ∉ Submonoid.powers y := by
    rintro ⟨n, hn⟩
    exact pow_ne_zero n hy hn
  have hle : Submonoid.powers y ≤ nonZeroDivisors R₀ :=
    le_nonZeroDivisors_of_noZeroDivisors hpow_ne
  haveI : IsDomain (Localization.Away y) :=
    IsLocalization.isDomain_localization hle
  have hinj : Function.Injective (algebraMap R₀ (Localization.Away y)) :=
    IsLocalization.injective _ hle
  apply UniqueFactorizationMonoid.of_exists_prime_factors
  intro z hz
  -- Write z = a/s with s a power of y, then factor a in R
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers y) z
  change IsLocalization.mk' _ a s ≠ 0 at hz
  have ha : a ≠ 0 := by intro h
                        apply hz
                        simp [h]
  obtain ⟨f, hf_prime, hf_assoc⟩ := UniqueFactorizationMonoid.exists_prime_factors a ha
  -- Partition prime factors: g = primes not dividing y (stay prime),
  -- h = primes dividing y (become units)
  let g := f.filter (fun p => ¬ p ∣ y)
  let h := f.filter (fun p => p ∣ y)
  have hfgh : f = g + h := by
    have := Multiset.filter_add_not (· ∣ y) f
    rw [add_comm] at this
    exact this.symm
  refine ⟨g.map (algebraMap R₀ (Localization.Away y)), ?_, ?_⟩
  · intro b hb
    rw [Multiset.mem_map] at hb
    obtain ⟨p, hpg, rfl⟩ := hb
    have hp_prime := hf_prime p (Multiset.mem_of_mem_filter hpg)
    have hp_ndvd : ¬ p ∣ y := (Multiset.mem_filter.mp hpg).2
    have hne : algebraMap R₀ (Localization.Away y) p ≠ 0 :=
      fun heq => hp_prime.ne_zero (hinj (by simp [heq]))
    rw [← Ideal.span_singleton_prime hne,
      show Ideal.span {algebraMap R₀ (Localization.Away y) p} =
        Ideal.map (algebraMap R₀ (Localization.Away y)) (Ideal.span {p}) from
      by rw [Ideal.map_span, Set.image_singleton]]
    exact IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers y) _
      (Ideal.span {p}) ((Ideal.span_singleton_prime hp_prime.ne_zero).mpr hp_prime)
      (Set.disjoint_iff.mpr fun x ⟨hxM, hxI⟩ => by
        rw [SetLike.mem_coe, Ideal.mem_span_singleton] at hxI
        obtain ⟨n, rfl⟩ := (hxM : x ∈ Submonoid.powers y)
        exact hp_ndvd (hp_prime.dvd_of_dvd_pow hxI))
  · -- The product of mapped non-y-dividing primes is associated to mk' a s
    change Associated (g.map (algebraMap R₀ (Localization.Away y))).prod
        (IsLocalization.mk' (Localization.Away y) a s)
    -- The product of y-dividing primes becomes a unit in R[y⁻¹] since each divides the unit y
    have hunit : IsUnit ((h.map (algebraMap R₀ (Localization.Away y))).prod) := by
      apply Multiset.prod_induction IsUnit
      · exact fun a b => IsUnit.mul
      · exact isUnit_one
      · intro p hp
        rw [Multiset.mem_map] at hp
        obtain ⟨q, hq, rfl⟩ := hp
        exact isUnit_of_dvd_unit (map_dvd _ (Multiset.mem_filter.mp hq).2)
          (IsLocalization.map_units _ (⟨y, Submonoid.mem_powers y⟩ : Submonoid.powers y))
    have hmk1_unit : IsUnit (IsLocalization.mk' (Localization.Away y) (1 : R₀) s) :=
      IsUnit.of_mul_eq_one _ (by
        rw [mul_comm, ← IsLocalization.mk'_eq_mul_mk'_one, IsLocalization.mk'_self])
    -- Chain of associations: prod(g) ~ prod(f) ~ a ~ mk'(a,s) in R[y⁻¹]
    have step1 : Associated (g.map (algebraMap R₀ (Localization.Away y))).prod
        (f.map (algebraMap R₀ (Localization.Away y))).prod := by
      rw [hfgh, Multiset.map_add, Multiset.prod_add]
      exact associated_mul_unit_right _ _ hunit
    have step2 : Associated (f.map (algebraMap R₀ (Localization.Away y))).prod
        (algebraMap R₀ (Localization.Away y) a) := by
      rw [← map_multiset_prod]
      exact hf_assoc.map _
    have step3 : Associated (algebraMap R₀ (Localization.Away y) a)
        (IsLocalization.mk' (Localization.Away y) a s) := by
      rw [IsLocalization.mk'_eq_mul_mk'_one]
      exact associated_mul_unit_right _ _ hmk1_unit
    exact step1.trans (step2.trans step3)

/-- In a UFD, the localization at any submonoid of non-zero-divisors
is a UFD. Generalizes `localization_away_UFD` to an arbitrary
submonoid `M`. -/
theorem localization_submonoid_UFD {S : Type*} [CommRing S]
    [Algebra R₀ S] {M : Submonoid R₀} [IsLocalization M S]
    (hM : M ≤ nonZeroDivisors R₀) :
    UniqueFactorizationMonoid S := by
  open Classical in
  haveI : IsDomain S :=
    IsLocalization.isDomain_of_le_nonZeroDivisors _ hM
  have hinj : Function.Injective (algebraMap R₀ S) :=
    IsLocalization.injective _ hM
  apply UniqueFactorizationMonoid.of_exists_prime_factors
  intro z hz
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective M z
  change IsLocalization.mk' _ a s ≠ 0 at hz
  have ha : a ≠ 0 := by intro h
                        apply hz
                        simp [h]
  obtain ⟨f, hf_prime, hf_assoc⟩ :=
    UniqueFactorizationMonoid.exists_prime_factors a ha
  -- g = primes disjoint from M (stay prime in S), h = primes dividing some m ∈ M (become units)
  let g := f.filter (fun p => ∀ m ∈ M, ¬ p ∣ (m : R₀))
  let h := f.filter (fun p => ¬ ∀ m ∈ M, ¬ p ∣ (m : R₀))
  have hfgh : f = g + h := by
    change f = f.filter _ + f.filter _
    rw [Multiset.filter_add_not]
  refine ⟨g.map (algebraMap R₀ S), ?_, ?_⟩
  · intro b hb
    rw [Multiset.mem_map] at hb
    obtain ⟨p, hpg, rfl⟩ := hb
    have hp_prime :=
      hf_prime p (Multiset.mem_of_mem_filter hpg)
    have hp_ndvd : ∀ m ∈ M, ¬ p ∣ (m : R₀) :=
      (Multiset.mem_filter.mp hpg).2
    have hne : algebraMap R₀ S p ≠ 0 :=
      fun heq => hp_prime.ne_zero (hinj (by simp [heq]))
    rw [← Ideal.span_singleton_prime hne,
      show Ideal.span {algebraMap R₀ S p} =
        Ideal.map (algebraMap R₀ S) (Ideal.span {p}) from
        by rw [Ideal.map_span, Set.image_singleton]]
    exact IsLocalization.isPrime_of_isPrime_disjoint M _
      (Ideal.span {p})
      ((Ideal.span_singleton_prime hp_prime.ne_zero).mpr
        hp_prime)
      (Set.disjoint_iff.mpr fun x ⟨hxM, hxI⟩ => by
        rw [SetLike.mem_coe,
          Ideal.mem_span_singleton] at hxI
        exact hp_ndvd x hxM hxI)
  · change Associated
      (g.map (algebraMap R₀ S)).prod
      (IsLocalization.mk' S a s)
    -- Each prime in h divides some element of M, hence maps to a unit; their product is a unit
    have hunit :
        IsUnit ((h.map (algebraMap R₀ S)).prod) := by
      apply Multiset.prod_induction IsUnit
      · exact fun a b => IsUnit.mul
      · exact isUnit_one
      · intro p hp
        rw [Multiset.mem_map] at hp
        obtain ⟨q, hq, rfl⟩ := hp
        have hq_dvd :
            ¬ ∀ m ∈ M, ¬ q ∣ (m : R₀) :=
          (Multiset.mem_filter.mp hq).2
        push Not at hq_dvd
        obtain ⟨m, hm_M, hq_dvd_m⟩ := hq_dvd
        exact isUnit_of_dvd_unit (map_dvd _ hq_dvd_m)
          (IsLocalization.map_units _ ⟨m, hm_M⟩)
    have hmk1_unit :
        IsUnit (IsLocalization.mk' S (1 : R₀) s) :=
      IsUnit.of_mul_eq_one _ (by
        rw [mul_comm,
          ← IsLocalization.mk'_eq_mul_mk'_one,
          IsLocalization.mk'_self])
    -- Conclude: prod(g) ~ prod(f) ~ a ~ mk'(a,s) by transitivity of Associated
    exact (by
      rw [hfgh, Multiset.map_add, Multiset.prod_add]
      exact associated_mul_unit_right _ _ hunit
      : Associated (g.map (algebraMap R₀ S)).prod
          (f.map (algebraMap R₀ S)).prod).trans
      ((by rw [← map_multiset_prod]
           exact hf_assoc.map _
        : Associated (f.map (algebraMap R₀ S)).prod
            (algebraMap R₀ S a)).trans
        (by rw [IsLocalization.mk'_eq_mul_mk'_one]
            exact associated_mul_unit_right _ _ hmk1_unit))

end LocUFD

end
