/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs

import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-!
# Localizations of unique factorisation domains

A localization of a unique factorisation domain at a submonoid of nonzerodivisors is again one.
A prime of the base either becomes a unit or stays prime, so a factorisation of a numerator
becomes one after the primes that turned into units are dropped.

Mathlib has the corresponding statements for polynomial rings and for principal ideal rings, but
none for localizations. The Laurent polynomial ring is a localization of the polynomial ring, so
this is what carries unique factorisation along the tower of Laurent extensions reaching the group
ring of a finitely generated free abelian group.
-/

universe u v

public noncomputable section

namespace IsLocalization

variable {A : Type u} [CommRing A] [IsDomain A]
variable {B : Type v} [CommRing B] [IsDomain B] [Algebra A B]
variable (S : Submonoid A) [IsLocalization S B]

omit [IsDomain A] [IsDomain B] in
/-- Divisibility after localization comes from divisibility up to a denominator. -/
theorem exists_dvd_mul_of_dvd_algebraMap {p a : A}
    (h : algebraMap A B p ∣ algebraMap A B a) : ∃ s ∈ S, p ∣ a * s := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨⟨c₁, v⟩, hv⟩ := IsLocalization.surj (M := S) c
  have hmap : algebraMap A B (a * v) = algebraMap A B (p * c₁) := by
    rw [map_mul, map_mul, hc, mul_assoc, hv]
  obtain ⟨w, hw⟩ := IsLocalization.exists_of_eq (M := S) hmap
  refine ⟨(v : A) * (w : A), mul_mem v.2 w.2, ⟨c₁ * (w : A), ?_⟩⟩
  calc a * ((v : A) * (w : A)) = (w : A) * (a * (v : A)) := by ring
    _ = (w : A) * (p * c₁) := hw
    _ = p * (c₁ * (w : A)) := by ring

omit [IsDomain A] [IsDomain B] in
/-- A prime of the base ring stays prime after localization unless it becomes a unit. -/
theorem prime_algebraMap_of_prime (hS : S ≤ nonZeroDivisors A) {p : A} (hp : Prime p)
    (hnu : ¬ IsUnit (algebraMap A B p)) : Prime (algebraMap A B p) := by
  refine ⟨fun h ↦ hp.ne_zero (IsLocalization.injective B hS (by simpa using h)), hnu, ?_⟩
  intro y z hyz
  obtain ⟨⟨y₁, t⟩, ht⟩ := IsLocalization.surj (M := S) y
  obtain ⟨⟨z₁, u⟩, hu⟩ := IsLocalization.surj (M := S) z
  have hdvd : algebraMap A B p ∣ algebraMap A B (y₁ * z₁) := by
    have hrw : algebraMap A B (y₁ * z₁)
        = (y * z) * (algebraMap A B (t : A) * algebraMap A B (u : A)) := by
      rw [map_mul, ← ht, ← hu]
      ring
    rw [hrw]
    exact hyz.mul_right _
  obtain ⟨s, hs, hps⟩ := exists_dvd_mul_of_dvd_algebraMap S hdvd
  have hpns : ¬ p ∣ s := fun hd ↦
    hnu (isUnit_of_dvd_unit (map_dvd (algebraMap A B) hd)
      (IsLocalization.map_units B ⟨s, hs⟩))
  rcases hp.dvd_mul.mp hps with hprod | hcon
  · rcases hp.dvd_mul.mp hprod with hy | hz
    · refine Or.inl ((IsUnit.dvd_mul_right (IsLocalization.map_units B t)).mp ?_)
      rw [ht]
      exact map_dvd _ hy
    · refine Or.inr ((IsUnit.dvd_mul_right (IsLocalization.map_units B u)).mp ?_)
      rw [hu]
      exact map_dvd _ hz
  · exact absurd hcon hpns

omit [IsDomain A] [IsDomain B] in
/-- Mapping a list of primes into the localization and dropping those that become units leaves a
prime factorisation of the image. -/
private theorem exists_prime_factors_algebraMap [UniqueFactorizationMonoid A]
    (hS : S ≤ nonZeroDivisors A) (f : Multiset A) (hf : ∀ p ∈ f, Prime p) :
    ∃ g : Multiset B, (∀ q ∈ g, Prime q) ∧ Associated g.prod (algebraMap A B f.prod) := by
  induction f using Multiset.induction with
  | empty => exact ⟨0, by simp, by simp⟩
  | cons p f ih =>
    obtain ⟨g, hgp, hga⟩ := ih fun q hq ↦ hf q (Multiset.mem_cons_of_mem hq)
    have hp : Prime p := hf p (Multiset.mem_cons_self p f)
    by_cases hu : IsUnit (algebraMap A B p)
    · refine ⟨g, hgp, hga.trans ⟨hu.unit, ?_⟩⟩
      rw [Multiset.prod_cons, map_mul, IsUnit.unit_spec]
      ring
    · refine ⟨algebraMap A B p ::ₘ g, ?_, ?_⟩
      · intro q hq
        rcases Multiset.mem_cons.mp hq with rfl | hq
        · exact prime_algebraMap_of_prime S hS hp hu
        · exact hgp q hq
      · rw [Multiset.prod_cons, Multiset.prod_cons, map_mul]
        exact hga.mul_left _

omit [IsDomain A] in
/-- A localization of a unique factorisation domain at a submonoid of nonzerodivisors is again a
unique factorisation domain. -/
theorem uniqueFactorizationMonoid [UniqueFactorizationMonoid A]
    (hS : S ≤ nonZeroDivisors A) : UniqueFactorizationMonoid B := by
  refine UniqueFactorizationMonoid.of_exists_prime_factors (α := B) fun b hb ↦ ?_
  obtain ⟨⟨x, s⟩, hs⟩ := IsLocalization.surj (M := S) b
  have hunit : IsUnit (algebraMap A B (s : A)) := IsLocalization.map_units B s
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, map_zero] at hs
    rcases mul_eq_zero.mp hs with h' | h'
    · exact hb h'
    · exact hunit.ne_zero h'
  obtain ⟨f, hfp, hfa⟩ := UniqueFactorizationMonoid.exists_prime_factors x hx0
  obtain ⟨g, hgp, hga⟩ := exists_prime_factors_algebraMap (B := B) S hS f hfp
  refine ⟨g, hgp, hga.trans ?_⟩
  refine (hfa.map (algebraMap A B)).trans (Associated.symm ⟨hunit.unit, ?_⟩)
  rw [IsUnit.unit_spec]
  exact hs

end IsLocalization
