/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import LeanPool.AndersonConjecture.Jensen.KrullDomain.AdjoinLocSet
import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# Primality in R[x, y^{-1}] and coprime height bound

If x is transcendental over R and r is prime in R with r not
dividing y, then r remains prime in R[x, y^{-1}]. As a
consequence, if y_1 and y_2 are coprime in R, no height-one
prime of T contracting to a nonzero ideal of R can contain
both y_1 and y_2.
-/

noncomputable section

open Cardinal Ideal Polynomial Set Pointwise

variable {T : Type*} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsDomain T]

section AdjoinLocPrime

/-- If r is prime in NSubring R and r ∤ y, then y ∉ P for any P ∈ Ass(T/(r·T)).
Uses the NSubring height bound: ht(P∩R) ≤ 1 forces P∩R = (r), so y ∈ P → r | y. -/
lemma not_mem_associatedPrime_of_ndvd
    (R : NSubring T) (r y : R.carrier) (hr : Prime r) (hry : ¬ r ∣ y)
    (P : Ideal T) (hP : P ∈ associatedPrimes T (T ⧸ Ideal.span {(↑r : T)})) :
    (↑y : T) ∉ P := by
  haveI : IsDomain R.carrier := NSubring.isDomain R
  haveI : UniqueFactorizationMonoid R.carrier := R.isUFD
  intro hy_P
  have hr_ne : (↑r : T) ≠ 0 := fun h => hr.ne_zero (R.carrier.subtype_injective h)
  have hI_le_P : Ideal.span {(↑r : T)} ≤ P := by
    have h := hP.annihilator_le
    rwa [Submodule.annihilator_top, Ideal.annihilator_quotient] at h
  have hr_P : (↑r : T) ∈ P := hI_le_P (Ideal.mem_span_singleton_self _)
  have hht := R.height_bound (↑r : T) hr_ne P hP
  haveI : P.IsPrime := hP.isPrime
  haveI : (P.comap R.carrier.subtype).IsPrime := Ideal.comap_isPrime _ _
  have hspan_le : Ideal.span {r} ≤ P.comap R.carrier.subtype :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (show (↑r : T) ∈ P from hr_P))
  have hspan_ne : Ideal.span {r} ≠ ⊥ :=
    Ideal.span_singleton_eq_bot.not.mpr hr.ne_zero
  haveI : (Ideal.span {r}).IsPrime := (Ideal.span_singleton_prime hr.ne_zero).mpr hr
  -- Height argument: P ∩ R = Ideal.span{r}
  have hspan_eq : Ideal.span {r} = P.comap R.carrier.subtype := by
    by_contra hne
    have hstrict := lt_of_le_of_ne hspan_le hne
    rw [show (1 : ℕ∞) = ↑(1 : ℕ) from rfl] at hht
    rw [Ideal.height_le_iff] at hht
    have hspan_ht := hht (Ideal.span {r}) inferInstance hstrict
    have hbot_lt := bot_lt_iff_ne_bot.mpr hspan_ne
    have hbot_fin : (⊥ : Ideal R.carrier).FiniteHeight :=
      ⟨Or.inr (by simp [Ideal.height_bot])⟩
    have h0 := @Ideal.height_strict_mono_of_isPrime R.carrier _
      (⊥ : Ideal R.carrier) (Ideal.span {r}) Ideal.isPrime_bot hbot_lt hbot_fin
    rw [Ideal.height_bot] at h0
    rw [show (↑(1 : ℕ) : ℕ∞) = 1 from rfl, Order.lt_one_iff] at hspan_ht
    rw [hspan_ht] at h0
    exact lt_irrefl _ h0
  have hy_comap : y ∈ P.comap R.carrier.subtype := hy_P
  rw [← hspan_eq] at hy_comap
  exact hry (Ideal.mem_span_singleton.mp hy_comap)

/-- y is a non-zero-divisor on T/(r·T) when r is prime in NSubring R and r ∤ y. -/
lemma isSMulRegular_of_ndvd
    (R : NSubring T) (r y : R.carrier) (hr : Prime r) (hry : ¬ r ∣ y) :
    IsSMulRegular (T ⧸ Ideal.span {(↑r : T)}) (↑y : T) := by
  have key : (↑y : T) ∉ ⋃ p ∈ associatedPrimes T (T ⧸ Ideal.span {(↑r : T)}), (p : Set T) := by
    simp only [Set.mem_iUnion, not_exists]
    intro P hP
    exact not_mem_associatedPrime_of_ndvd R r y hr hry P hP
  rwa [biUnion_associatedPrimes_eq_compl_regular, Set.mem_compl_iff, not_not] at key

/-- A prime element r of R that doesn't divide y is "prime" in adjoinLocSetY R x y
when x is transcendental over R: if a₁ * b₁ = (r:T) * c in T with
a₁, b₁, c ∈ adjoinLocSetY, then r divides a₁ or b₁ within adjoinLocSetY.

The proof has three key ingredients:
1. Polynomial factorization: from a₁*b₁ = r*c and transcendence, derive C(r)|f₁ or C(r)|f₂
   in R[X] (using C(r) prime and C(r) ∤ C(y)^n).
2. NSubring height bound: y is a non-zero-divisor in T/(r·T) because y ∉ P for every
   P ∈ Ass(T/rT). This uses: P∩R has height ≤ 1, r ∈ P∩R with ht((r))=1, so P∩R = (r),
   and y ∉ (r) since r ∤ y.
3. Divisibility transfer: from a₁*y^m = r*e and y regular mod r, conclude r|a₁ in T.
   Then d := a₁/r ∈ adjoinLocSetY with witness (h₁, m₁). -/
lemma prime_in_adjoinLocSet
    (R : NSubring T) (x : T) (y : R.carrier) (r : R.carrier)
    (hx_trans : Transcendental R.carrier x)
    (hr : Prime r) (hry : ¬ r ∣ y)
    (a₁ b₁ c : T) (ha₁ : a₁ ∈ adjoinLocSetY R x y) (hb₁ : b₁ ∈ adjoinLocSetY R x y)
    (hc : c ∈ adjoinLocSetY R x y) (heq : a₁ * b₁ = (r : T) * c) :
    (∃ d ∈ adjoinLocSetY R x y, a₁ = (r : T) * d) ∨
    (∃ d ∈ adjoinLocSetY R x y, b₁ = (r : T) * d) := by
  obtain ⟨f₁, n₁, hf₁⟩ := ha₁
  obtain ⟨f₂, n₂, hf₂⟩ := hb₁
  obtain ⟨f₃, n₃, hf₃⟩ := hc
  haveI : IsDomain R.carrier := NSubring.isDomain R
  haveI : UniqueFactorizationMonoid R.carrier := R.isUFD
  have hinj := transcendental_iff_injective.mp hx_trans
  have hpoly : f₁ * f₂ * C (y ^ n₃) = C r * f₃ * C (y ^ (n₁ + n₂)) := by
    apply hinj
    simp only [map_mul, aeval_C, show algebraMap R.carrier T = R.carrier.subtype from rfl,
      Subring.coe_subtype, map_pow]
    rw [← hf₁, ← hf₂, ← hf₃]
    have lhs_rw : a₁ * (↑y : T) ^ n₁ * (b₁ * (↑y : T) ^ n₂) * (↑y : T) ^ n₃ =
        a₁ * b₁ * ((↑y : T) ^ n₁ * (↑y : T) ^ n₂ * (↑y : T) ^ n₃) := by ring
    rw [lhs_rw, heq, pow_add]
    ring
  have hCr : Prime (C r : Polynomial R.carrier) := Polynomial.prime_C_iff.mpr hr
  have hCr_ndvd : ¬ (C r : Polynomial R.carrier) ∣ C (y ^ n₃) := by
    rw [map_pow]
    intro h
    have h1 := hCr.dvd_of_dvd_pow h
    rw [Polynomial.C_dvd_iff_dvd_coeff] at h1
    have h2 := h1 0
    rw [Polynomial.coeff_C_zero] at h2
    exact hry h2
  have hCr_dvd : (C r : Polynomial R.carrier) ∣ f₁ * f₂ := by
    have hdvd : (C r : Polynomial R.carrier) ∣ f₁ * f₂ * C (y ^ n₃) :=
      ⟨f₃ * C (y ^ (n₁ + n₂)), by rw [hpoly, mul_assoc]⟩
    exact (hCr.dvd_or_dvd hdvd).resolve_right hCr_ndvd
  have hr_ne : (↑r : T) ≠ 0 := fun h => hr.ne_zero (R.carrier.subtype_injective h)
  have hy_reg := isSMulRegular_of_ndvd R r y hr hry
  suffices aux : ∀ (t : T) (f : Polynomial R.carrier) (n : ℕ),
      t * (↑y : T) ^ n = aeval x f → (C r : Polynomial R.carrier) ∣ f →
      ∃ d ∈ adjoinLocSetY R x y, t = (↑r : T) * d by
    rcases hCr.dvd_or_dvd hCr_dvd with h | h
    · exact Or.inl (aux a₁ f₁ n₁ hf₁ h)
    · exact Or.inr (aux b₁ f₂ n₂ hf₂ h)
  intro t f n htf ⟨g, hfg⟩
  have ht_eq : t * (↑y : T) ^ n = (↑r : T) * aeval x g := by
    rw [htf, hfg, map_mul, aeval_C,
      show algebraMap R.carrier T = R.carrier.subtype from rfl]
    rfl
  have hyn_reg := hy_reg.pow n
  have ht_mem : t ∈ (Ideal.span {(↑r : T)} : Ideal T) :=
    mem_of_isSMulRegular_quotient_of_smul_mem hyn_reg (by
      rw [smul_eq_mul, mul_comm, ht_eq]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp ht_mem
  exact ⟨d, ⟨g, n, mul_left_cancel₀ hr_ne (by
                                             rw [← mul_assoc, hd.symm]
                                             exact ht_eq)⟩, hd⟩

end AdjoinLocPrime

/-!
## Coprime height bound

Key lemma: if y₁, y₂ ∈ R are coprime (no prime divides both), then no
height-1 prime P of T (that contracts to a nonzero ideal of R) can contain
both y₁ and y₂. This is what makes the intersection approach work.
-/

section CoprimeHeight

/-- In a UFD, every nonzero prime ideal contains a prime element. -/
lemma exists_prime_mem_of_ne_bot {S : Type*} [CommRing S] [IsDomain S]
    [UniqueFactorizationMonoid S]
    (Q : Ideal S) [hQ : Q.IsPrime] (hQ_ne_bot : Q ≠ ⊥) :
    ∃ q : S, Prime q ∧ q ∈ Q := by
  obtain ⟨a, haQ, ha_ne⟩ : ∃ a ∈ Q, a ≠ (0 : S) := by
    by_contra h
    push Not at h
    exact hQ_ne_bot (le_antisymm (fun x hx => (Submodule.mem_bot _).mpr (h x hx)) bot_le)
  have ha_nu : ¬IsUnit a := fun hu => hQ.ne_top (Ideal.eq_top_of_isUnit_mem Q haQ hu)
  suffices ∀ x : S, x ≠ 0 → ¬IsUnit x → x ∈ Q → ∃ q : S, Prime q ∧ q ∈ Q from
    this a ha_ne ha_nu haQ
  intro x
  apply wellFounded_dvdNotUnit.induction x
  intro x ih hx_ne hx_nu hxQ
  obtain ⟨p, hp_irr, hp_dvd⟩ := WfDvdMonoid.exists_irreducible_factor hx_nu hx_ne
  obtain ⟨b, hxpb⟩ := hp_dvd
  rcases hQ.mem_or_mem (show p * b ∈ Q from hxpb ▸ hxQ) with hp_Q | hb_Q
  · exact ⟨p, hp_irr.prime, hp_Q⟩
  · exact ih b ⟨right_ne_zero_of_mul (hxpb ▸ hx_ne), p, hp_irr.prime.not_unit,
      by rw [hxpb, mul_comm]⟩ (right_ne_zero_of_mul (hxpb ▸ hx_ne))
      (fun hu => hQ.ne_top (Ideal.eq_top_of_isUnit_mem Q hb_Q hu)) hb_Q

/-- If y₁, y₂ are coprime in R and P∩R has height ≤ 1 and is nonzero,
then y₁ ∉ P or y₂ ∉ P. -/
theorem coprime_not_both_in_prime (R : NSubring T)
    (y₁ y₂ : R.carrier)
    (hcoprime : ∀ p : R.carrier, Prime p → ¬(p ∣ y₁ ∧ p ∣ y₂))
    (P : Ideal T) [hP : P.IsPrime]
    (hPR_ht : (P.comap R.carrier.subtype).height ≤ 1)
    (hPR_ne : P.comap R.carrier.subtype ≠ ⊥) :
    (↑y₁ : T) ∉ P ∨ (↑y₂ : T) ∉ P := by
  haveI : IsDomain R.carrier := NSubring.isDomain R
  haveI : UniqueFactorizationMonoid R.carrier := R.isUFD
  by_contra h
  push Not at h
  obtain ⟨hy₁P, hy₂P⟩ := h
  have hy₁_comap : y₁ ∈ P.comap R.carrier.subtype := hy₁P
  have hy₂_comap : y₂ ∈ P.comap R.carrier.subtype := hy₂P
  haveI hPR_prime : (P.comap R.carrier.subtype).IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨q, hq_prime, hq_mem⟩ := exists_prime_mem_of_ne_bot (P.comap R.carrier.subtype) hPR_ne
  haveI : (Ideal.span {q}).IsPrime := Ideal.span_singleton_prime hq_prime.ne_zero |>.mpr hq_prime
  have hspan_le : Ideal.span {q} ≤ P.comap R.carrier.subtype :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hq_mem)
  have hspan_ne_bot : Ideal.span {q} ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact hq_prime.ne_zero
  -- Height argument: span{q} = P∩R since ht(P∩R) ≤ 1
  have hspan_eq : Ideal.span {q} = P.comap R.carrier.subtype := by
    by_contra hne
    have hstrict : Ideal.span {q} < P.comap R.carrier.subtype :=
      lt_of_le_of_ne hspan_le hne
    have hht' : (P.comap R.carrier.subtype).height ≤ ↑(1 : ℕ) := hPR_ht
    rw [Ideal.height_le_iff] at hht'
    have hspan_height : (Ideal.span {q}).height < ↑(1 : ℕ) :=
      hht' _ inferInstance hstrict
    have hbot_lt : (⊥ : Ideal R.carrier) < Ideal.span {q} :=
      bot_lt_iff_ne_bot.mpr hspan_ne_bot
    have hbot_fin : (⊥ : Ideal R.carrier).FiniteHeight :=
      ⟨Or.inr (by simp [Ideal.height_bot])⟩
    have h0 : (⊥ : Ideal R.carrier).height < (Ideal.span {q}).height :=
      @Ideal.height_strict_mono_of_isPrime R.carrier _ (⊥ : Ideal R.carrier)
        (Ideal.span {q}) Ideal.isPrime_bot hbot_lt hbot_fin
    rw [Ideal.height_bot] at h0
    rw [show (↑(1 : ℕ) : ℕ∞) = 1 from rfl, Order.lt_one_iff] at hspan_height
    rw [hspan_height] at h0
    exact lt_irrefl _ h0
  have hy₁_span : y₁ ∈ Ideal.span {q} := hspan_eq ▸ hy₁_comap
  have hy₂_span : y₂ ∈ Ideal.span {q} := hspan_eq ▸ hy₂_comap
  rw [Ideal.mem_span_singleton] at hy₁_span hy₂_span
  exact hcoprime q hq_prime ⟨hy₁_span, hy₂_span⟩

end CoprimeHeight

end
