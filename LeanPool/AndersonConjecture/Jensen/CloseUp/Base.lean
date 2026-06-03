/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import LeanPool.AndersonConjecture.Jensen.NSubring

/-!
# Close-up: base case

Base cases of the close-up construction (Heitmann, Lemma 4).
For a principal ideal (a) in a Noetherian local domain T with
an A-extension R, one produces a new A-extension containing
a/p for suitable primes p. The divisibility case follows by
induction on the UFD factorisation in R.
-/

noncomputable section

open Cardinal Ideal

variable {T : Type*} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsDomain T]

/-!
## Base case: principal ideals (n = 1)

If I = yR for y prime in R, and c ∈ yT ∩ R, then c ∈ yR already.
This follows from the N-subring height condition.
-/

/-- Close-up for principal prime ideals: if y is prime in R
and c ∈ yT ∩ R, then c ∈ yR.
Uses N-subring condition (3): for P ∈ Ass(T/yT),
ht(P ∩ R) ≤ 1, forcing P ∩ R = yR. -/
lemma eq_of_prime_le_prime_height_le_one
    {S : Type*} [CommRing S] [IsDomain S]
    {P Q : Ideal S} [hP_prime : P.IsPrime] [hQ_prime : Q.IsPrime]
    (hPQ : P ≤ Q) (hP_ne_bot : P ≠ ⊥) (hht : Q.height ≤ 1) : P = Q := by
  by_contra hne
  have hPQ_strict : P < Q := lt_of_le_of_ne hPQ hne
  have hht' : Q.height ≤ ↑(1 : ℕ) := hht
  rw [Ideal.height_le_iff] at hht'
  have hP_height : P.height < ↑(1 : ℕ) := hht' P hP_prime hPQ_strict
  have hbot_lt_P : (⊥ : Ideal S) < P := bot_lt_iff_ne_bot.mpr hP_ne_bot
  have hbot_fin : (⊥ : Ideal S).FiniteHeight :=
    ⟨Or.inr (by simp [Ideal.height_bot])⟩
  have h0 : (⊥ : Ideal S).height < P.height :=
    @Ideal.height_strict_mono_of_isPrime S _ (⊥ : Ideal S) P Ideal.isPrime_bot
      hbot_lt_P hbot_fin
  rw [Ideal.height_bot] at h0
  rw [show (↑(1 : ℕ) : ℕ∞) = 1 from rfl, Order.lt_one_iff] at hP_height
  rw [hP_height] at h0
  exact lt_irrefl _ h0

theorem close_up_principal
    (R : NSubring T) (y : R.carrier) (hy : Prime y) (c : R.carrier)
    (hc : (c : T) ∈ Ideal.span {(y : T)}) : c ∈ Ideal.span {y} := by
  rw [Ideal.mem_span_singleton] at hc ⊢
  have hy_ne_zero : (y : T) ≠ 0 :=
    fun h => hy.ne_zero (Subtype.val_injective h)
  have hnt : Nontrivial (T ⧸ Ideal.span {(y : T)}) := by
    rw [Ideal.Quotient.nontrivial_iff, Ne, Ideal.eq_top_iff_one, Ideal.mem_span_singleton]
    intro ⟨c', hc'⟩
    have hmem : y ∈ IsLocalRing.maximalIdeal R.carrier :=
      (IsLocalRing.mem_maximalIdeal _).mpr hy.not_unit
    rw [R.maximal_ideal_eq, Ideal.mem_comap] at hmem
    exact (IsLocalRing.mem_maximalIdeal _).mp hmem (isUnit_of_dvd_one ⟨c', hc'⟩)
  haveI := hnt
  obtain ⟨P, hP_mem⟩ :=
    associatedPrimes.nonempty (R := T) (M := T ⧸ Ideal.span {(y : T)})
  have hy_in_P : (y : T) ∈ P := by
    have hP_assoc := (hP_mem : IsAssociatedPrime P _)
    have : Ideal.span {(y : T)} ≤ P := by
      intro x hx
      apply hP_assoc.annihilator_le
      rw [Submodule.mem_annihilator]
      intro m _
      induction m using Quotient.inductionOn' with
      | h a =>
        change Ideal.Quotient.mk _ (x * a) = 0
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right a _ hx)
    exact this (Ideal.subset_span rfl)
  have hht := R.height_bound (y : T) hy_ne_zero P hP_mem
  have hspan_le : Ideal.span {y} ≤ P.comap R.carrier.subtype :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hy_in_P)
  have hspan_prime : (Ideal.span {y}).IsPrime :=
    (Ideal.span_singleton_prime (α := R.carrier) hy.ne_zero).mpr hy
  have hspan_ne_bot : Ideal.span {y} ≠ (⊥ : Ideal R.carrier) :=
    mt (Ideal.span_singleton_eq_bot (α := R.carrier)).mp hy.ne_zero
  have hcomap_prime : (P.comap R.carrier.subtype).IsPrime :=
    hP_mem.isPrime.comap R.carrier.subtype
  have heq : Ideal.span {y} = P.comap R.carrier.subtype :=
    @eq_of_prime_le_prime_height_le_one R.carrier _ (NSubring.isDomain R) _ _
      hspan_prime hcomap_prime hspan_le hspan_ne_bot hht
  have hc_in_P : (c : T) ∈ P := by
    obtain ⟨t, ht⟩ := hc
    rw [ht]
    exact P.mul_mem_right _ hy_in_P
  rw [← Ideal.mem_span_singleton, heq]
  exact hc_in_P

/-!
## Generalized close-up for arbitrary elements

In a UFD N-subring R, if y ∈ R and c ∈ yT ∩ R, then c ∈ yR.
Proved by well-founded induction on divisibility, reducing to
close_up_principal.
-/

/-- Generalized close-up for arbitrary elements: if y ∈ R
(NSubring, UFD) and c ∈ yT ∩ R, then c ∈ yR.
Proved by induction on prime factorization. -/
theorem close_up_dvd
    (R : NSubring T) (y c : R.carrier)
    (hc : (c : T) ∈ Ideal.span {(y : T)}) : c ∈ Ideal.span {y} := by
  haveI : UniqueFactorizationMonoid R.carrier := R.isUFD
  haveI : IsDomain R.carrier := NSubring.isDomain R
  revert c
  refine UniqueFactorizationMonoid.induction_on_prime y ?_ ?_ ?_
  · intro c hc
    simp only [ZeroMemClass.coe_zero] at hc
    rw [Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot] at hc
    rw [Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot]
    exact Subtype.val_injective hc
  · intro y hu c _
    rw [Ideal.span_singleton_eq_top.mpr hu]
    exact Submodule.mem_top
  · intro a p ha_ne hp ih c hc
    have hc_p : (c : T) ∈ Ideal.span {(p : T)} := by
      rw [Ideal.mem_span_singleton] at hc ⊢
      obtain ⟨t, ht⟩ := hc
      exact ⟨(a : T) * t, by
        rw [show ((p * a : R.carrier) : T) = (p : T) * (a : T) from
          map_mul R.carrier.subtype p a] at ht
        rw [← mul_assoc]
        exact ht⟩
    have hc_pR : c ∈ Ideal.span {p} := close_up_principal R p hp c hc_p
    rw [Ideal.mem_span_singleton] at hc_pR
    obtain ⟨c', hcc'⟩ := hc_pR
    have hc'_a : (c' : T) ∈ Ideal.span {(a : T)} := by
      rw [Ideal.mem_span_singleton] at hc ⊢
      obtain ⟨t, ht⟩ := hc
      have hp_ne : (p : T) ≠ 0 := fun h => hp.ne_zero (Subtype.val_injective h)
      have hpc : (c : T) = (p : T) * (c' : T) := by
        have := congr_arg R.carrier.subtype hcc'
        simp only [map_mul] at this
        exact this
      have hpa : (c : T) = (p : T) * (a : T) * t := by
        rw [show ((p * a : R.carrier) : T) = (p : T) * (a : T) from
          map_mul R.carrier.subtype p a] at ht
        exact ht
      have : (p : T) * (c' : T) = (p : T) * ((a : T) * t) := by
        rw [← hpc, hpa, mul_assoc]
      exact ⟨t, mul_left_cancel₀ hp_ne this⟩
    have hc'R : c' ∈ Ideal.span {a} := ih c' hc'_a
    rw [Ideal.mem_span_singleton] at hc'R ⊢
    obtain ⟨b, hb⟩ := hc'R
    exact ⟨b, by rw [hcc', hb, mul_assoc]⟩

end
