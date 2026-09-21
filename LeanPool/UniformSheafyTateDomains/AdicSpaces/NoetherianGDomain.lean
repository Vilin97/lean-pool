/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Ideal

/-!
# Noetherian G-domains: one-dimensionality from a field localization

The **G-domain lemma** ([hrw-decomposition] "THE TATE LEAF DECOMPOSED", leaf 7;
classically part of the Goldman/Kaplansky G-domain theory): if `B` is a
noetherian integral domain, `π ≠ 0` is a non-unit, and `B[1/π]` is a field,
then every nonzero prime of `B` is a minimal prime of `(π)` and is maximal.
The chain: primes avoiding `π` collapse to `⊥` (they survive into the field);
Krull's principal ideal theorem bounds the height of minimal primes over a
nonzero element; the height pinch identifies every such prime with a minimal
prime of `(π)`; finite prime avoidance traps arbitrary nonzero primes.

This is the algebra input for zero-dimensionality of `T°/π` in the affinoid
Nullstellensatz (leaf 8); it is stated for an arbitrary commutative ring
localization `Localization.Away π`.
-/

@[expose] public section

open scoped Classical

section GDomain

variable {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B]
variable {π : B}

/-- Primes avoiding `π` collapse to `⊥` when `B[1/π]` is a field: a nonzero
element of such a prime becomes a unit in the field, so a power of `π` lands
in the prime. -/
theorem Ideal.eq_bot_of_isPrime_of_notMem_of_isField_away
    (hπ0 : π ≠ 0) (hfield : IsField (Localization.Away π))
    (𝔮 : Ideal B) (hq : 𝔮.IsPrime) (hπq : π ∉ 𝔮) : 𝔮 = ⊥ := by
  classical
  refine (Submodule.eq_bot_iff _).mpr fun x hx => ?_
  by_contra hx0
  -- the image of `x` is a nonzero element of the field, hence a unit
  have hinj : Function.Injective
      (algebraMap B (Localization.Away π)) :=
    IsLocalization.injective _
      (powers_le_nonZeroDivisors_of_noZeroDivisors hπ0)
  have himg0 : algebraMap B (Localization.Away π) x ≠ 0 := by
    intro h0
    exact hx0 (hinj (by rw [h0, map_zero]))
  obtain ⟨y, hy⟩ := hfield.mul_inv_cancel himg0
  -- clear the denominator of the inverse
  obtain ⟨⟨a, m⟩, hm⟩ := IsLocalization.surj (Submonoid.powers π) y
  obtain ⟨k, hk⟩ := m.2
  -- x * a and m have the same image up to a power of π
  have hxa : algebraMap B (Localization.Away π) (x * a) =
      algebraMap B (Localization.Away π) (m : B) := by
    rw [map_mul]
    calc algebraMap B (Localization.Away π) x * algebraMap B _ a
        = algebraMap B _ x * (y * algebraMap B _ (m : B)) := by rw [hm]
      _ = (algebraMap B _ x * y) * algebraMap B _ (m : B) := by ring
      _ = algebraMap B _ (m : B) := by rw [hy, one_mul]
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists
    (Submonoid.powers π) (Localization.Away π)).mp hxa
  obtain ⟨j, hj⟩ := c.2
  -- a power of π lies in 𝔮
  have hmem : π ^ (k + j) ∈ 𝔮 := by
    have h1 : (c : B) * (x * a) = (c : B) * (m : B) := hc
    have h2 : π ^ (k + j) = x * (a * c) := by
      have hk' : π ^ k = (m : B) := hk
      have hj' : π ^ j = (c : B) := hj
      rw [pow_add, hk', hj']
      calc (m : B) * (c : B) = (c : B) * (m : B) := by ring
        _ = (c : B) * (x * a) := h1.symm
        _ = x * (a * c) := by ring
    rw [h2]
    exact Ideal.mul_mem_right _ _ hx
  exact hπq (hq.mem_of_pow_mem _ hmem)

/-- **The G-domain lemma, minimal-prime form**: every nonzero prime of a
noetherian domain with field localization `B[1/π]` is a minimal prime of
`(π)` (Krull's principal ideal theorem + the height pinch + finite prime
avoidance). -/
theorem Ideal.mem_minimalPrimes_span_of_isPrime_of_ne_bot_of_isField_away
    (hπ0 : π ≠ 0) (hfield : IsField (Localization.Away π))
    (𝔭 : Ideal B) (hp : 𝔭.IsPrime) (hp0 : 𝔭 ≠ ⊥) :
    𝔭 ∈ (Ideal.span {π}).minimalPrimes := by
  classical
  -- every nonzero prime contains a minimal prime of (π), of height ≤ 1,
  -- with which any nonzero sub-prime coincides
  have hkey : ∀ (𝔯 : Ideal B), 𝔯.IsPrime → 𝔯 ≠ ⊥ → 𝔯.height ≤ 1 →
      𝔯 ∈ (Ideal.span {π}).minimalPrimes := by
    intro 𝔯 hr hr0 hht
    haveI := hr
    -- π ∈ 𝔯 by the collapse lemma
    have hπr : π ∈ 𝔯 := by
      by_contra hπr
      exact hr0 (Ideal.eq_bot_of_isPrime_of_notMem_of_isField_away
        hπ0 hfield 𝔯 hr hπr)
    -- a minimal prime of (π) inside 𝔯
    obtain ⟨𝔮, hq, hqr⟩ := Ideal.exists_minimalPrimes_le
      (I := Ideal.span {π}) (by rwa [Ideal.span_le, Set.singleton_subset_iff])
    haveI hqp : 𝔮.IsPrime := hq.1.1
    have hq0 : 𝔮 ≠ ⊥ := by
      intro h0
      refine hπ0 ?_
      have := hq.1.2
      rw [h0] at this
      simpa using this (Ideal.mem_span_singleton_self π)
    -- the pinch: 𝔮 = 𝔯
    rcases eq_or_lt_of_le hqr with rfl | hlt
    · exact hq
    · exfalso
      have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
      have h2 : 𝔮.height ≠ 0 :=
        fun h0 => hq0 (Ideal.height_eq_zero_iff_eq_bot.mp h0)
      have h3 : (1 : ℕ∞) ≤ 𝔮.height := by
        rwa [Order.one_le_iff_ne_zero]
      have h4 : (2 : ℕ∞) ≤ 𝔯.height := le_trans (by
        calc (2 : ℕ∞) = 1 + 1 := by norm_num
          _ ≤ 𝔮.height + 1 := by gcongr) h1
      have h5 : 𝔯.height ≤ 1 := hht
      have : (2 : ℕ∞) ≤ 1 := le_trans h4 h5
      norm_num at this
  -- trap 𝔭 by the finitely many minimal primes of (π)
  have hfin : (Ideal.span {π} : Ideal B).minimalPrimes.Finite :=
    Ideal.finite_minimalPrimes_of_isNoetherianRing (I := Ideal.span {π})
  -- each nonzero x ∈ 𝔭 lies in a minimal prime of (π) contained in 𝔭
  have hxmem : ∀ x ∈ 𝔭, x ≠ 0 → ∃ 𝔯 ∈ (Ideal.span {π}).minimalPrimes,
      x ∈ 𝔯 ∧ 𝔯 ≤ 𝔭 := by
    intro x hx hx0
    obtain ⟨𝔯, hr, hrp⟩ := Ideal.exists_minimalPrimes_le
      (I := Ideal.span {x}) (by rwa [Ideal.span_le, Set.singleton_subset_iff])
    haveI hrpr : 𝔯.IsPrime := hr.1.1
    have hxr : x ∈ 𝔯 := hr.1.2 (Ideal.mem_span_singleton_self x)
    have hr0 : 𝔯 ≠ ⊥ := by
      intro h0
      rw [h0] at hxr
      exact hx0 (by simpa using hxr)
    haveI : (Ideal.span {x} : Ideal B).IsPrincipal := ⟨x, rfl⟩
    have hht := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes
      (Ideal.span {x}) 𝔯 hr
    exact ⟨𝔯, hkey 𝔯 hrpr hr0 hht, hxr, hrp⟩
  -- 𝔭 is contained in the union; prime avoidance picks one
  obtain ⟨x₀, hx₀p, hx₀0⟩ : ∃ x ∈ 𝔭, x ≠ (0 : B) := by
    by_contra hall
    push_neg at hall
    exact hp0 ((Submodule.eq_bot_iff _).mpr hall)
  obtain ⟨𝔯₀, hr₀min, hx₀r, hr₀p⟩ := hxmem x₀ hx₀p hx₀0
  have hFprime : ∀ 𝔮 ∈ hfin.toFinset, 𝔮.IsPrime := by
    intro 𝔮 hq
    rw [Set.Finite.mem_toFinset] at hq
    exact hq.1.1
  have hsub : (𝔭 : Set B) ⊆
      ⋃ i ∈ ((hfin.toFinset : Finset (Ideal B)) : Set (Ideal B)),
        ((i : Ideal B) : Set B) := by
    intro x hx
    rcases eq_or_ne x 0 with rfl | hx0
    · refine Set.mem_biUnion (x := 𝔯₀) ?_ (Ideal.zero_mem 𝔯₀)
      rw [Finset.mem_coe, Set.Finite.mem_toFinset]
      exact hr₀min
    · obtain ⟨𝔯, hrmin, hxr, -⟩ := hxmem x hx hx0
      refine Set.mem_biUnion (x := 𝔯) ?_ hxr
      rw [Finset.mem_coe, Set.Finite.mem_toFinset]
      exact hrmin
  obtain ⟨𝔮m, hq_mF, hpq_m⟩ := (Ideal.subset_union_prime
    (s := hfin.toFinset) (f := fun q => q) 𝔯₀ 𝔯₀
    (fun i hi _ _ => hFprime i hi)).mp hsub
  have hq_min : 𝔮m ∈ (Ideal.span {π}).minimalPrimes := by
    rw [Set.Finite.mem_toFinset] at hq_mF
    exact hq_mF
  have h𝔯₀q : 𝔯₀ ≤ 𝔮m := le_trans hr₀p hpq_m
  have hq𝔯₀ : 𝔮m ≤ 𝔯₀ := hq_min.2 ⟨hr₀min.1.1, hr₀min.1.2⟩ h𝔯₀q
  have heq : 𝔭 = 𝔯₀ := le_antisymm (le_trans hpq_m hq𝔯₀) hr₀p
  rw [heq]
  exact hr₀min

/-- **The G-domain lemma, maximality form**: every nonzero prime is maximal
(minimal primes of `(π)` form an antichain containing every nonzero prime). -/
theorem Ideal.isMaximal_of_isPrime_of_ne_bot_of_isField_away
    (hπ0 : π ≠ 0) (hπu : ¬ IsUnit π)
    (hfield : IsField (Localization.Away π))
    (𝔭 : Ideal B) (hp : 𝔭.IsPrime) (hp0 : 𝔭 ≠ ⊥) : 𝔭.IsMaximal := by
  classical
  refine ⟨⟨hp.ne_top, fun J hJ => ?_⟩⟩
  by_contra hJtop
  obtain ⟨𝔪, hm, hJm⟩ := Ideal.exists_le_maximal J hJtop
  have hm0 : 𝔪 ≠ ⊥ := by
    intro h0
    rw [h0, le_bot_iff] at hJm
    rw [hJm] at hJ
    exact not_lt_bot hJ
  have hpmin := Ideal.mem_minimalPrimes_span_of_isPrime_of_ne_bot_of_isField_away
    hπ0 hfield 𝔭 hp hp0
  have hmmin := Ideal.mem_minimalPrimes_span_of_isPrime_of_ne_bot_of_isField_away
    hπ0 hfield 𝔪 hm.isPrime hm0
  have hle : 𝔭 ≤ 𝔪 := le_trans (le_of_lt hJ) hJm
  have := hmmin.2 ⟨hpmin.1.1, hpmin.1.2⟩ hle
  exact (lt_irrefl 𝔭 (lt_of_lt_of_le hJ (le_trans hJm this)))

end GDomain
